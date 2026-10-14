-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3393
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:32:09.072062+00:00
-- url     : https://prove2.me/submissions/231b7c47-ed00-4698-828c-b626b50ad1b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 610071942 ≤ n < 610251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 610073192 1250 610071942 610071967
    0x8040b2406031e01080106090e150a05040f1202031b0c010f0f020a0f0b01050f180a092102070f090b01170c12090102030103030f0c2609120c03010b040b090c 69
    0x3403070404005101610f65a50f500301c40d406800d40344580ca000c0303464003051400111011407200300d19150010040495182c2da20f40308002d0400600960f006c0840c08688400211200d6a000100030305034004d60320b4260f6100d025000150603d010390260744100306a03049640c0255040c1c0340d0800c51700740440e0260701440140d041010945004102d041d80810150801168028080c103948040c0c813440700740c00904040c0700d6031048003c6103c0d240d42080300000c100700c0043c1c00c100c030f201d80710702600c07000b412003400030030340810030302442001580266000303000311055181402c0007491181018010100d120b80080d1410150f40c860040089a210001d6003281c040710842d01d000784040001041803070002d554034000d400a0104500048141c1000642203110b4406441100c1c0c100380d41c603074441c85400b01c225980b2003400e5074001401d014043c29038280d4607c0040c206182010307029105945008bc00c0500710b400079131103540b24918090314007110b80c4540f80055409542c45210958030680704002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 610074442 1250 610073192 610073221
    0x1080103030813023010050903040e060f040608030c011a012f0303100314070308030c030402030f0f0a0b061002210903010207030f0f0806150a031b08040b240603 71
    0x415030316488080d04a50a83e1005e0200ca08610016a101400c0300500130040d01c3e015070313450701d10780d00c00e00c01400034680c041527054102c140245182124480103000c24280c42495019481d290400308896a00361402e0141094044458002038582400d000001e0300b50724036603040400c001e0808000440c203070b8040c007100d40310070040c0085076240e1800b00c00b013003007100403800304480b4804100504120f000e000141c3c0701c103903580140d6403400c42e940c4100d515002e0700018001e03a41845680950300361104240481c0c11700581c082c000d080b1034005402c001d0350104024200390300070b924480b1b0f8041500e03404645400b9404000249009410700105c1c110144d02070702000d240d141d403000504204150b0008040c02a0f203040345c03980c0255441400c800e403030526046588540080c02d044180d2004890940205122041d500780000c40411550b0390b074242d0b480f6010f14901180c0800240300500c007454070032607800503102094405451580102c58510103480e001d450180700040b0110b200c40520140 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 610075692 1250 610074442 610074469
    0xf020304030b0903040303181211032a031e0a03110f06070804030e0907271205030408070506031e070c150510080304050a033804110108010303081302 66
    0xd12210a080c102c480c03580705e40c0144400c0b40461003d15070380085581c0c00700312004494040a12030038420b455181d001c106007000f445e00380d16004404058881d43d50480c0d80c2e110280c080d0801c40801d10120f001d00d07107002e054800030303005508250503440760341c64001400c4890a5151030682883e0342d007200e50742e141c00c0904070f4603030143c0607200410080c65404800320344618042e42e18041e010010205010003000b060f0742c1c0398001010000c0c54a01e900048254070b50001203440c0609102d580d5024000b800d0180e80000c0700c0d41c0c1c100180400001c20104104c001619080390520303e18203000c0340003c946070000528040012002c80051141d500694040354880d400202001c038004845110000400c412105038044e403412100104041100000740c0d400e42d40041c00d80300314241103803a801071301c2442c5031048118060907400c140700d0802d5000c2e05661507031401440907860030701d46040c1c01e014428195a44c10003070070000400110758802e036031a401001070342042064032054000318150011081c6c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 610076942 1250 610075692 610075703
    0x14130605030708030306030601060906081303090b0c03130f06080f1e070c1a01082a030f03070312020913020a0e030706110c120d12201c0b100f02030403 67
    0x5400043c201808801107104500c00c03015200ba0b40e883d20001d41e11001c450003181c4c006001080080c180394041540056401d0103800c20214550391070200c11995031100142201c150000b28075904a20a50400c21014225000c50b0703c0300c003802d0510003001114002c020302c003034882c00c0001c94100d1071205410030f0201140c1d800b131286c91802d00c0c8080c0a9690040301202c40208407807481c0f09060940c801d90303058130455800346c00b44016507a0a101c918206195001e03001c10010303000f55090b0f5040060505003c10340c0040c1d61500300605020307001d19260710300400c90030300421020b45203507290340e5410032510381d6020041c1c4409414804035403140680020b250144666a0040382003074104103000f41c1c100c110001c41d140c015034002800121403561401034105e40c40508050340881c022040110340303581b990400142c0806000c484401c401c80c402440a241d140000c02c4802249001084c001840c5055010f10900030148041040503c80210000801103045174160030f083c8280102c81c004c54020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 610078192 1250 610076942 610076953
    0x703030b0a0609050f090411010e0316170d180608130f0605010810020f03060f1f0e130e06011a0708030406050a140709030209040f06140a0f061413060503 68
    0x40c01c02910556403401400d1240340c4807425001c4600d00888007d1050743d0042000101600480043d90401c5c10070115581c5801040c0310a0346900300412107030000c1c400154103604a071100c01c2400d00700000059042c0400c07440590021480d01880701c04000c0b500c036403411524540c2c44596007048020007200003000212082406014001c00e0f8001d01e05071411441500e07400c00c0c988401000302d115682c0721380c0c03c0890a100090b000d250aa046002c1c814000c0c00a0300c0751803881140f00342c04004000c0a0020940c0ca00110f5150300341075041c6101240c0b490700070800903150004540ea9540148200322102c0d68110010700e1a0424509444119500880903500c0341007030301e42140a00700403542c01c0f046d58601011100003106207040c0714080d12840e1103032048c1c9400d40d003d01c990224010000d40704100101032480004100c1d00c1220407260854040803880e0500302c82d00c10075206120040c1c3c2c01701e410301406010022864903120002c0c20104c40c2040f074002c2c040405030150027640c2c0581d5260007407 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 610079442 1250 610078192 610078199
    0x3020109020f01020307020a051306080303100e0c0306210f330412030b060f030711070501081009150b030f0a0b090103030f0c03030f11040e090606090c0703030b0a 72
    0x150450340540d842110701e001c4000e140d100481c0d80b4040c6480c00780d44840c1d400340400c00e07802c0990305a6400001c0784008601a904d80440f00d255900a40300d1131009c0c81c0c2d0440401951101101098000c01c800d8510391860402c00c00040c010302805131807040e11107000c040070307800b400d08000c5042d40c040007100361014203c01d007102d00028480060725404981e007024003a10704070905402a441140e00c5508401d0100e42e450003180181941e480c40c940204003042805403903141440a180300d84450303583c09a0400f0903601142c00d01040d80d00050602c4075a40a0003807403a90980ea04064527552180000c0b00c41440038031440d022000d1f0301c4000803000000910548149001900f031040501940c28040b07039044001744810070009101c06000101503d2100c0d05851041d030980d103010707009180108012644e100c8000440d992004400f00070100041c041000340c0851100300c1d0b101c4d01000140600786800d00120f00d00c0c00008000080060002481d0b40816000307070321041c5807900c0a05159417554a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 610080692 1250 610079442 610079447
    0xa0f06030c09080105010605040b0309210a020d080402010504090c0c02090c1b0a170711030d0206061003020403051e070819060e0c031209310e0601060c030c0303140403 74
    0x1003000d007000a40b40b1a000c1090340301401003e0403a05035548091803d0300c1e0071503807041604023401e2240d25000c2c00243e070200e1218a24844609001c00503060b949104401d000303843c05a00920080a010460003040b01613a0800c1c1690125600c3c5c81020810006c504800c866109164a0081d400881a004d000030851a0405040d00d2000c5600c001d46a02c0038091a03562010708100c014201c2e141a0005441e808a0a000e010322512580071076940d4030a0b01c00103400c1580ca100c1200050340001b04112507440d04042400f140080381c2030462400d03045403a01e940b110000c086000c0c030720000b030445104071101080901c0081c030010b01070301d003902d403817a100101e41d9802d19410fa40d228209041e01d00d02300004140341031201802001003000b910075110841c580d400c1054503590040390f40845c1040c00070005184121022415041803036404109544011240b0805260340e8a52225005101880d0088003030b0303038105c0d010308004144200740d01e01103021f00f10032082012400c803000288000c140c4c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 610081942 1250 610080692 610080701
    0x9010b041a0301060b1204230d02010903121406040c1b0f1104050c0904110d0c03050a0e0d020d0311270108160912330c08010b0909060a0f0603 63
    0x20701c1100241301059543c1c00510880c01580202c080d4012804085000980162454092503003044202c19942920104503070508102041d0140542d444421950805600041810030069014010040c5446941014489840080c4000d0169640700c0304c1101e171500904040081c02c0d803120401014021601d031107440000028002c0b60700180b403464020791403506024040c41503103200f220505040d5420100009081524107420b0b10540c2007111506020f481d001e540440c03003094801052604040303500c4012651011007a40480d00300d41241c5149550100b0000c0034401d44c6d00c3c020600c000075413401c00b05889946a4080345142c0f840c0003415488001040c0103040c5c40076218010300340c0d50004070000361180d04040e000082c402c400c0034030160140d0600c0c41102801a52442407c9400d400c50036540c22210580e00810701c250f0400600500403070080d40c56440c13103440c00c0503ca515210268046010f00303c01907129801c079000240346900c0b107a072090000c000361500300812503a81c0c00082c0051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 610083192 1250 610081942 610081991
    0x4110909130b060f1818010c090e1515070309180614040b01020d0c17033c0a050a0905120306040f090c05041d0a03030c0e030a020d060509010b04 64
    0x698602e00060300e40c0c900b8113040080044060541080c00009442e55080b0300001090b04031007602d0140c0c00b981c1050b00340314203100d80b256901c94003203140c182002c4e4203801701c00801c0c20750302100c48400c108041d21140f20200ca1009500c20302030b210b08043c5001c1e01d07464506d070040b01110348d140d018600081a141c020f80c1c220b0702010807100706d19041034144002d890b0648403480c0568000d160b1070b0829442504001d000b1801395003066014107007104100d0325640291a202950001c84ea403403040312031442030080c1c6042100c43c40c4006012183c0c0142a8080e0040030603400942d00c0000402c0100540c211140d03199001c8203403503142c42d400ba90102103802c241c0c1c00c80d000300d10b0300840d406003a0740c62140c110f103143c01c01c551004c001c3c640720801014000038403844249200d04042000301c8542041400904e9110343c0740411301001b444001030524034440c2d0854844d602000364580980c0300c00007070080707a54002c00089026070b20010080c1c00f501211454603001707031518411141b4181d020100c02e000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 610084442 1250 610083192 610083203
    0x182802070213050421030e06010305160e0907050d030903050303090d0801120206071104021b0303010602010c0905010e46092903070308070803100b180411090913 71
    0x810088502d03800b00c56080307800070040f04000b209103040c803100035200010481c0500c0d012038074580c9844580d050400a0f0303c02c80e1558481649000c500341800014005800300c90203030342071460895501ca1b40c4000714400c80b030207085803101a03414548251180f401441d005006c4139680d00b00a161a61748000840c441000070ba0620000309820f452441400d0701250020a40e605041481d160342090441809800342d010740c2c20011070b4480d02d03541c4c0b402002c000d14100a1a16503242110103801e41e10304131801030400041003024052680c0002c0104090340c2c0503151842040c8240307040007485c0300f6501d201c0041040f42c0351700d8078003142000c1c002d1b00350781c49180d601808180c0d03442d078a10a5401c402e6a1461081100d03c41d503200c01040c10b01c650315503c2c01412100807035035a407030303100103580020001d89500300000100000c8004983c56107008040d420f003c03500e400e03d2798440041c28228552920700c169240c0c10300b1300c440b01011042e200d107060028404207076401c100d0301708046800e08407000c2303d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 610085692 1250 610084442 610084459
    0x12150901080d0e1002071413090305040305120a0c0b04021201020c1e0102070f171201030602030a0506010c030807051c0c0c03090b090604030b071b03020705010e0f1828020702 77
    0x207281011191000060304d0b5400500501d800c2c015480380c00da1600c000c140d01716510040b40000181c140c040c01c83c0c030340c2c06511b0700d80c1d035075096050a03420844901c2403001130b100200135294004c0e03801100c6010090b00000c03080459203440c400142030940001404040358004614240c00b21030115400903000c01c00112022544071a1211509038002c56038082c280152412200010481062250300c400032050207862a10300d000100901c202020303002650051b50200400981d03950328401c0c65003003042401c1c0000080e07885e0760300038011803000b8002400c0150109480b403040191424021410005520900044003045002840781281400c140e00007010003a00190382001c0004548512801030200c0e45080d0039600c801c41d240d00058054000c000f4851040d4072410400030b1821380b200e100c2c2d03026040c0070f403070b21000500c104034450f0709600c80e9003d00c040d808580d64541100e145c41c3c00c4011480d466a0b240c0702048000e5140b552a0a08200c42e04010300142d41c00b9802012054401c40e41c850 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 610086942 1250 610085692 610085717
    0x715050f01061116120201090e0106020304090e01151e0909080705070e1501180308160c05060f07120c02100207080106090513021e04020f0c07050f0612150901080d 72
    0x2a5104a800c3c80368000130207031001030041d01001504100703804c0c01818195581c40d5282c0380b00d0b01c2c45c2403d81c81840107801c0400c06021822031405140000f044140c020300c401e031034040c4103ca40d10304522407045001199443d118030440842c03000790050070300b080100491030340c80c145800250301040d401c4819008404003c039a005030900104e0080c0006000035034803c002ea40150b40c0c885824400700400801c1000002c0080c004c0c1c070040400c01084d10409050089514084142841c2c0390001c521601c000e10411755014004402c7d2028a40c014450b4440d04650f4442a180380d0081c0070041c0d08464640d00000381d042c4c00160312011116240001c1040940d0342e0345040407103070151003504a180c110400c00000d031514092100e00d2261800380701040e80d141c1d00004089038031548981c10010800300742020104c2060220000922069130001d09400c47d160016070b02c0d20603400300e05015004900412240c4408a262505802024040c03036580e5850b03000403a45c641007680c0344c0001446440003013 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 610088192 1250 610086942 610086977
    0x1140102060405190f0b01060203070606090501080a02191a130f1203081f140415120f080702061c0c02070303021e0a061d0d081603020715050f0106 65
    0x2502c80c5030042c0182c14a0300003000710014040761400180c03454581c0c10344039000300f8901c00c4000d000780215001103560340c25074903002040d10843d900400e1851300e0180104244840800d0000015904a40e8004040d20300d902c0b00881194917001100101e00550001d20300b0680e0300010311074940701c02c100c6118070341d8428000d001b080c024040c100c05030203c1001c0000003401200020b810031901c0d941c0e011004640b000e1401000003561295410040480305c50000381007921030362060b40707100e00345601e00c207007008001d03651054810002000b0220641da60b006000c85402070b5804254014000795880d0100341d8480d003c41c05034440c080c03a00c1e180c0407941d0b038541d00003d080b00460b540342d00a001c1d414902580d4080e17096071000503880c076026060320000042c02500c5108001a050038441503103046d0f45000a107007480505511081c0080c1100f4012906040141d640409002e885c0141e41d070451458406807502000c0c41c00e504403410281446610444007520750705a810036600c0704000703110724405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 610089442 1250 610088192 610088203
    0x10e09030a08062106011509080c0f060d140105041b080a0203070c0f080a0e010206150409020d140a02010e0402090a0e040c05090103120f05070b06040b01030e1501140102 75
    0x408195108001c002103590103101d0550380b10600504000c0c0b0754100084a0002041c1e04a00001542081d801400300651061144440d5800c91424003a504e0509a10564a034120140c1506c142c9000c0e088017500d6a807103048a1100703c501d00e050081201c0718501c07509006003806002d208078205284240030781140c0b1410150803955031344484c00d6481e02180c180c020351003e40b50788208842c001820020030981c0c60820009446602045d6481c601c0d400003c1c00c4800b41c20315a81150410f1040c0700b4196820344001075100030403640010780740a80d200090704400203100060404120034041d100810012642000d901c1c000c0c0c0b1003008001d000f1042004074804c7c000915400201c1c18000e1107415052000e4030380c040d2107410310030382d03068855001481d43e45c0b0991003110f400c07001202004140e503011041c07402c00d070501d06103d420f00c200b03a941c44690507001000c0c42d01132a0340d15912951070303110350065440c5406c203606489082c0150280c00c48202801d0055807917034010303108105081e5100284 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 610090692 1250 610089442 610089451
    0x31201180c0507032a0515010603060e070f17010b0c070807050a0e0406020702031e12040515090409060c05130f0509041e1e0209090105040b0a020c1906050609010e 72
    0x581603c0c103003040d54240d45e20502c50b1002c68149540c94a14803451010601080d85240518001c0221b06d161403009644880142c00000806080070703020011034010b01c03840340c1c000182e41044c40d03907922228002c855101c00306134074144d04511200002030300341ca614010400040240d056a001a44075201c40b551240d1610905412a00041007002058005401260000e210741c002600e8104c417900002e10740011008880d91800c040202c0d0344041004218122088000700e04450815141500044560700c025240a00400b800201880c6a60325170740712207091070380580b040080c0f1101c1140144039400c80c5410fa01d2103049000080351001075070b040c03c003c44038010454030040c1d40c1c60b6a83c50513145041941a51010714250010000b83c000564980d403601056886841589900402c1181900034000c40d038981d24103401c0c4004070f0102030480d54082480c401c05a911401b040e144e5190048140b52408000100744240040100c5600024000c00c012101d2800c580d0301c44082404d800c80966 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 610091942 1250 610090692 610090697
    0x1502120904020a030e12120f04031706040b1210290f01090e010e0a060e040f11030a0206031504110f031504020d020309060106141e031305031201180c 66
    0x100005140ca01a0010b01211403031349404246240009020744c502212100e03484080140803550030705004c25404403a038850100c2110741100e0800c6c2e1009041040c00a90803042c0b4542c2d00002091502c85801c400341c0761802410a420900d02e0301d45c20740d1107030b480d07031080711842d0300300b501040401000090200001080c54070030035559000b002041008130b81e00900c5414856403080000300310018040c41d60003000046102c0358280f6041d40000304590f0340360001e180326802201448041000b40440d030001680c40340c0f9244580114100082c0b0313101c0d0a06c1c0096006200000f0015070341c524034001000c0c0c0710295010b2101448415540c0c25034002e102c411140e06c0d1041c0001250000b000c2c613420408003001e44018500384081c0c020609a1340204c40001481d03001000402c807040c4d201aa0f641205544400e650030705060701c4c200742000e11000040c0907068404400700f116042d0f8200c0844190b54080100c0e503907500307885055031592000744240c50300003200081440d59200f1038004c019101501d517 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 610093192 1250 610091942 610091947
    0x5040210170a0207030e0604090c09090c2106080a080d050106050405011202160210020a11060f0d0207060b04060609080f1203060111100c02010603020f06040308070f05150f01150212 80
    0x82d202c44029000120260304000740102a41c4035170315a003000384094600ca40000c21070000340342002e0100b102c0750740031702d00c2070b1710b1700070b540328a50707030242d8209001612f40d43c1014122810b01d042c4009409035420980080c01115259000c10810b14010007066104010a005d22380c0e88190a4906010383d1085501262444140d0f072144d070041c0c0c2c01080b4001504043d00020100b540104615148180322300e40940c0c4100301c82002e02041c100c1050340d405003283e4841c40c2c8110241c006400380201010301101c990085191410004541c00241044002820070020703903648040091861806210b055000e010f1130704003040820300840e0482c0c1e240f5003a4a458036645a210044034148810038060302140128500380b5064600c03402070581c0070303685900220f610350030b50040040070352900712003602c215410070040000030640c0d41074038102d6070019070405a20b021402c10508040c1e0b00c900d10443c02404204002541c1c5e0400600c906940d030b180c0d420800d40d24591300a1b40c2c0d65504403007507440706500303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 610094442 1250 610093192 610093201
    0x705041415250b180105060904150e07051203120a05070804120c0506010b1902010b0a09150305010e0106060305132109091514060a1b020d0b0403030504021017 70
    0xd180040d010301c5400740a0a0110b0981d112494400310030b80d400c1000e00d0683c103450b01115001d004080c1c01001c129210b81d2641015512000754a6650320004070607520740707448200280701804541c00a013009000e1400d140c03000840903481c1da012610ba4008020f00c0300101e00d0800c020720030b95210349441c0d1a5a40c1c203860325100c80c2a40d5140304030b410304004400f03110a00154003440600d00a10300e00c4201d40d12041c1e0014014140202e6180800840e03160004503402581d4074801d402c12501501c43c00601031601d80e140d54410405074001400715804c0954280c030b42041580300000712600c2c4d94007045039880301c08010110803080760010382601c03800c08000c00e064070005148c204100780e03801c02160030341c0c0c0c50300042c00740c4510103104030141001762400c208842c0001d0182d5000801110030915101424402401c403c0c2150420241c080c41d48102c3c00c1103403261003225100b20f4201e0b9192005142070301d0001c006d0030782240c0490040d04030100f0b10381541d003e44490580b0844203c0d5011032941c8 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 610095692 1250 610094442 610094467
    0xe0a03050f07062c0601061103041701090f080909100302030d08151002010e0606120d050c03040b030a0510080309030d050c240406060609050105090f010e03060705041415 75
    0x4940b03820b0700d07003540e21000e10f01644100c902e49038003071450036003809003c1400c030070785410250168045010300c01030040e03072402d4090101c12281a140d0150815841d10400380700ca03030052280075401843d60f0440c5103610240503c1c840503010110741140c185000d50384203c40034070503420f00d00c002034142d4440c200440049020319a09507102d40c0135900240300c0b94070100081c42c841c242040700d20141c2d55849400300ea118081c000c40e940050152072070100e00c0c5100c4c04403591800310b501060200310f004101f00d010341c0d00c140708440007811545441a203034205800e0b01c0000341001d07558442a1190f404001030a40d00203c15614141c0e001005840800200b02080d21140d101d0900d00d1094000c0501d1112064074102261403100c40d8a010800d003450b0528004088544c982c00079003e000007144c040080340c2c3e008007210301241013900d540f15200c041d00d0068504103000285280e0502455040280c443c0d445005001210b03107580a11046150b100e06101072680040000410304c8002c00c20148080d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 610096942 1250 610095692 610095697
    0x141e0d020319030c0e091501110a3903080a11010b0f0103020d0f020c0a020913050703020f040207050d021609090b01060309050f0a050a0c0e1015121107060e0a03050f 73
    0x521414459048404080003440031b0104890452002c00c0848140205592004460070380d0340d6100000c040c44031a50f122240b600c80c070302100d1410303480d1b0385010826090510f04164030480c0c0d00c0c022401c695803203241810007504240c00036030000e40703141c0d0708100c854030500034004000d1003e0980c0010103982c10044000c0d62059031020301c119104d00800002205030b10080840210420180032106102c0c410041c501601411070f40740d0b03034803841500700801c5001c00d03803508503507045488241549012012030043d0060400142590149805c810842600400c1c0c4282094075130a00c0703201617807243d4640f42101c0008001030f00c07c490400040c8000f038080d501c03100d5840d008600301c5207605505005a464107808010440f5075401400b001070800c15034041c4c11014210309041e0901d589498010740040301341a12403c0c070480c4803a00480c513007a005542042101c40c1d020418000000440c1f00c54500d5808404200c3d101c91500490028040010841040c81941a035031546480349118a204054 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 610098192 1250 610096942 610096961
    0xb0a180b190b120c010f09030c150c06230a021c050c1215010e040c0f030b0103021b07030b0a020c030301140a09020d0b10020609030f07141e0d02031903 67
    0xc40e03941c03100c80510b0b034901400f06618005031004103a00600e2400060200002c51000410702c0002c0c10140005018a20384000361071410503605a02e00c541c0724102c40c180c0c414000071700300618010700002c206a241000c14004050340210410300d0f01c0b44102081244142000d040b5050440414007841d20442d40185411000100b038090400410001c1d0034140c640503500f080c050350840340d8000785544c0200c0003460501c0210380c02c00c0b154580b80d50140c040d0f00ea80c00704a041580ea4905044c59038041e07816030b205c92480352005408a803041880550300c5010740030946030301501c0c0c03000403c020341038001c6a0401000c1c402850860346007007030311901d2124800710554860760043c40450085554400b4000603e40e0101c00f1810745c840750184005155507403c3c00f02190850020044800800000c5415148181c2c1c0410368440303440c10085407400784000c4242c0e190040c0000c03407450207800c80004800c40c1e022000c1c0d603625041c084003680d0328880c40901c2d000f2500841d5204e442c060180d441001c0c4c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 610099442 1250 610098192 610098241
    0x60f021b0609090106320406081902040f0302090a06050a031b0b03070503011401090b27040603060e0d0e010f110c040903121406061b190b0a180b 64
    0x1e102400c000280f91031800d070451400516035207540c0d02402c4080801c00c3c084a508030381c042c44d200f412901a0054844d2307008900034058074030042401081c507044041c81000035801c01315119030300c0b200781130f841c0c1e021880183d1140421001003102051144140000c80b0070007050006900d01e1076541c6801c0100924181681f1a11114000f0b000349010b0011803003095036644042d0790791704000701261000d030400c060714100702d02a142803250758858012070351054840c1600c6481141d250420b42101805000700c10703002424000000204020ba40000b0351590740c1030140c9003802d04003502141c07001c40c610010740c0050003034044100f006008000718a904a170001c1640ca8030341c910b0f8045401e13145c0c141800c03000250840814901c0440c035100e0304c40d88510f02c030490507442c2402400644140102082c80313410380720580782030708181000c120300c84000c8100c1d64980b03003210f4a4204156619012590740321741900b0035035240c59009003503000343c0c2d0050b0b115480c21001d403200c00300301026040c2501240b01d03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 610100692 1250 610099442 610099447
    0x1305061206010312080a0c120209030a02030f01090b011710050a020c0d090f09020412080a021504060f050606120a0b01020c06040b0c0c04090201231c09020a060f021b06 74
    0x480c0c01800754501031030283d9040303219040a054024100b000c02003250000c0c0e445c100707101b18866400302058928203034506000da21690010b00203400e200200030300951511030040c100c00c4007041908240d901c14003071119029140c0c1d0b650450a01a09046607402032900940e803019060034254ec80f450f04001c242000506006a1002040c60300040c440140082040d9040802007542d00b03145100150814240950805207085580b01701c0b1840741c10010992040492092005842005040d8490280c1152014141410f0911600500190403121201030429000403030b1810308a044030b400710354110327030b6000654800b1032540060201c4e031404c80c114000d01011003c166210300140000d8041248100c1d5100500ca81043c54101c5038491030340030302d0412803800c0150fa0481503c00703030710340b8040440c0b0310041d20540b100c00c40d00c140700d10000e903040c0340803401c046c02082d0751090042c64420341c0c6040c00951110816544954008002d4006a2003004d44a04080d000384240407801e0003e01100d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 610101942 1250 610100692 610100719
    0x50a1b0b04030f02040b0609010212031305030a050703030e070f05130f0509100f2a030f110901121109040c020111030c0a1b080426120307030b0f130506 67
    0x2412684180e00a5803e81d14464125081d40707803138842c41b44282000c603100307480d01c10800c0c0040d4540503111101c18045401000144401854802065060341c0c80070a40790b580780342610150840e04032003001d03000640303440240c0451440002d445000d80e44600c501d4442e8034030f0901080340d859805109080c08945484000310465614014140640c990801400c082d5086040c1c00085030200300f40e65a0003410a00880e520700d48095030007688510320b083d07009031007900c150284c000d400744101e4a020507241801518010300031602416940b4000d9a51028200b000d1550409540c070900131a8000c01c0300704545c440a1800d44d02c11030901c00316000201c1d800000341030100484e0021200d2000f80c4900007101c510282c0d0006909071031018a04404158071141d80300c0e0030300d1340514010241c1c1c040c06101048210303695291403501001c400001c4444211100502e100c1c00d401c00e81d00e00c0042030a00b01b500509150581504200840280c2466900318024412401a1001520305600f054010035140d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 610103192 1250 610101942 610101959
    0x100e1009020306010203190e04111903050907120f06110c061f1a04140102210307030608030313031b03020a1223120705090d06090302100c0306090612050a1b 69
    0x111440c01170b10795a80230b08869044c4070a603240040c7c45c1c030380c95000b0082d9987c3c1040c2d1810750710007030f6000c0c40c00017085c1e640d541d007a030b20304804c81d08640404041031030020700b00300d0b19100c0c10720f40302c0c40303168140040903081181009a00600c803250005411101c00030341c04103060f0701a030300f001420500c00400380390b071680300c60f01652207910511520400001c0620003800d00741d03a040d081800030700c01841d12400000d00e5001091480d0030301c20341c01e480003000c1854203101350000c2c03014211940070b40360b503401e0618014086000301d103021000700340c050450801660000203800e900540503009062254001c0c1d84803044100320004403000e120108a400079a0300703107680d0410310f400745902c40c2039072007213464000f0700b1022005100d4030420104000101180d100c0380f1b0048581030b88041c003c50000558581a820454401c0c441d003506403800c440c24207150f038107800410440c0e42e200070400c07041d926007a280d505240c0322000904580d1102002200040c92501c0d0750801020001d03c2d004065224082c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 610104442 1250 610103192 610103227
    0x60f050421150f060306110715051b03130b0919080318030304030c0c0e240d0510020d151d22030809060609042117010806100e1009020306010203 64
    0x5070f090341d40c4440a1040211a01c81c20100c14a401550341c24403605036107100400c1100c0c07000207485a1618082054000007808150312074a030303205042d49a10300058041c103140380781c0d102503560b0043c0c2c2011540500e408204c40300031000001c540072000400e501e4030200d503400602480c4003640144550b1540b00004d001441c09107202c0d40d00d00e24140e1107420320001000454000c5c3c1480078801d03060111208800100a40001c00d001410350482c1104001584440521201824030300230341d100d40c40b401106500916a45111a104201d00e2003241c041842031269401051a000303e10200d50745200f00f800100307079002608150500c01c0b4218038054503103194410000b00c0100340c4640074043d05010510105030f0100060700e02195514058849031400d6940c1f441d20f0801101c0702e41282c024501c6506005200d5070441250440741d65214161039403104215150504490029008120448002100c0707000720500c0d46103441c0326092000a0000b90300180c0024151711081106483c503403802c494 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 610105692 1250 610104442 610104461
    0x5090307030204110a090806010b3403180801050f060f190929150f041e030b0601020f060f2d0a0606020a0b010909110303030c0301060f05042115 64
    0xa0030351145c0103054003501e900c0703898001901c581c100000500103285280156030641260031010018034061030401d601420002d03803641c1e075200240390083d0505401642c1e821100862881003044113a644003014220703501030700d6202190b0454004100303245003840140c2d200d008024140322500c42d070026880c11050240c0c0c0500500e03074441c44140c0183c2090104001081c0d45041c088540c5015100011115a8058071300b60b40c1c00b401140e60364a100001040d00c0181c0310040302c0d82102c1c0c9010394580c07010030491001700c90410780d010019025501c081090006820840700503c916119221300d2480356000504280101d000004d002d440858280203124030780b000820245004e0402d10081d6041d1445034001006651208403007030009240c2100c0c0301e04554820800282e45025840e102507a0040b400007070340e040c8804414484800201002103048900e69143c1d071020b045559020341e0b8078020b038402d0003c441c00c280c101c100317242c0c1c0c941c9401551310721900562086014145100c8103c528500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 610106942 1250 610105692 610105721
    0x518030301060305090601140f19170106050a060f05071101020c0418020102010c05030105010f11030d0c09060e0409080418090c08010608070f080d110f1207110a0602030a05090307030204 82
    0x42c8039501707606124407405042c441c00b0b651501c11148010a041d40310a140d01401140c0c03e1010002c2072030480c455070054503c013003043c510102d1034140305001e800700c0c1c001c89101d038014580026801c1e001e500c0c031407504541600e61a007000b500b91982c00001101c01c041360305500035407600f0741d501e58591240c00800b101c80c0c1030b4074402c50082c1c000242156100450342c42404000c03c014013041e80c100c41c4c02010000c46140410030b14021102c80c504501a05468034900d5081044600e501074101d4001000d4800382e96034030301c081039034108110560303580150103050060100001e1003c0140300200e84510500a007000c95000e289076540c00c158181a4401e110b180d654510501441c18103011403401084140e044240480c00c140d2510b031120401a170840905c400d05900d90702082c006d01800701c3c1c0101c18001e0301e510302807513612800241e0205004540780400d5210401c80c43c03821620380415141158011400c2c131280d60b0040d143e50f40007803140350b07140c89565400030060342c580c0030748000d110841 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 610108192 1250 610106942 610106951
    0x512040612142e0503060403051209010b1c1a1504060602060603030307181502010f3206010e030a230d1403250e100c0201080a05180303010603 63
    0x80030282242c419071110000c1c01402024080220000c581980810801d040110311403080d000d4408201842680020f4150080c6400c0100340760b001005020441c0980d8204541c45e40c54051107802c0703030303039429005510005c2c50945000400d40300d040e50106a101d0728200a1182c1911801a08080e044070810400a520004001349041a0295000411450008101038100003002075184c5c007008000310304003d460300300e071800c0041d8218990020902900c4c0c034820240e00340002070180411407003452201d41840b44100340c03060740d06085840c40185886016541044400107082c2c01409010306041115500780c0c151903a80c24031240c10204e11580c1000c90044483c14070303c2d8000100c5604490360342013519100d141d1500035840803803052111107244d030f480c1c0c0c480d00f0343c2d43c0c0805000c0b943d0180d0321190b1080703030903c1c0e00207280004038881160003151500714168102c4064107008002400604c0d030b100400c2d09040590803030b0b500480c00c04002950525502109450758100342d00000009495 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 610109442 1250 610108192 610108217
    0xc0106080d0518040218090702160e040506041101090801020c1501050103063606031118011805040c0b1306090b09180a0e0f2a010c020d05120406 64
    0x1040750744106800c03810410700300561816080405265415080e0160ba00019102d28000c0004844ca815500040140203d8104220000e503036a0040d03000c00034a034845200819801500d0340007501c603662010042c1250340d556035459106031143e0904506210380141c0c08102160280060101d1404620043c90341403048600c10842004c1a0b200505162405105010031114280c0340704201c51210b0f940294030b0350061250721b50020100300d440d0b80500d058000720070403c1a0082180e408412102102d108980c0c41c1010032041e820702c07a203503084030607950301c0e8100651038004540c440c0c014103804600e84c1c0d903a00c200440740c0c0103d020400d41014200280103881c0c0009448001c0d00c0040e008904041866020400840000d01760300040000f0400143c800c504a421811149504106a91034a00303e401c2440d5200000e00c0e20b0390121514050000075900d80b02030900c464901691503140040c401d4080c4070300c6900c401d1045d141401020300d141d5400002400500003880c06944011940f0003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 610110692 1250 610109442 610109459
    0x91703070f0905091b0a021f0506030114071e02030c1b0a06051204020d0816050d02010b0303090a1406070b0f06120f0a06180606080a0c050a0b07170f0c0106 69
    0x83c1c01c090311070103030f03107003400101007044200c03211601036218400c0c0d0ba440e141c1e00981c0f03400d0012000c2001801284d42c0341c400541d9641115000341021b9009105001e8460340007260550100c41480004599052400d10b024483e00c00d191041c9250042c0d900c1c000485420b54200350181524940454101c071030079840303040009a09005001c135180203810314075142d040d0f504624014201a10913100010024140490fa50860710b0000901010307c0e8106070314a00aa1a00d40706201c01000d0352030070074801940e00300170085822000c001024000118102260f0f101c05603414259250404024002000001c031022040e601403100c43e80000c04510307182040080c10412280440d425401900091089143c00038110482650041c00483c02280c00e6003180400700f10303c900580100e042032000542c100307001c1061860f007400781100c0d440241d114030900462282c10b22030266102d8040050b0f030041a022080c82074100040c11001345000e24a180010441d00421020440f40c0d5407040c08110694 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 610111942 1250 610110692 610110707
    0xc0d06230c090a0b0f0f181207090513020603192c061e06090703020906070c05210a03120213030311100c0203040302060906040302031e0c0303041503091703070f 71
    0x281c81d41a11300d411100c11017464603002c1d0128032040c03507101290400d6050203450700301d40300d00806499480c891001100c8596108001d12403441e499180c0700c00314903060610080100346c83d402900b06459501c6104c0c2408200301d0b161081c0c0714155407110710318281c40ca052840c54290142440f40b0b201e001c040745074203090040c0501340e0149508410000000c42e1194994a64802c004a4140304181d072807020a602034414541115804000000c004c000c111480d1120400c2e107600f61021848000c1203100031000200704411300c0c000f5844010b20600082c424400840304103150b13680035041c1b508010f241c602c4040303c0c1d0800c6020600200c6181035400c4104815400d060001805104686d820600039469106030f010290146c1000240700340c03140c0707c1314115401103034050102e03101c9589904000c0c0318500c40350806216402150300408807407400000703540507a41000c0c4030900d6075501e00e0301640200304100741110340c40d22284070340d01c2c02803440d8040d61141103203446480d40c044070584020140c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 610113192 1250 610111942 610111949
    0x3070b0618130b01152a1b0f1406031605040806010303050a02010e06040b070c020d0b01092004031518060e100c110d030504080c030a0903060506030c0d06230c090a 72
    0xc00c0ea000a001d03844d40200380200d41d06c60712040d0354444425001e0780311100c010081c00390200e444904440c64038180000640c0c110f0f0800a82ca04485495906440403154101c901c02d500c003000b403010407411104400e03030098640046c00c7c6549040d031396008442c2050f038260303c20390200390702080014a84d0340a0081c0a903200d400c0d80a00b0b2545043d9071003e54081d03018101c0c104005d050385a16045480c0c500240c000107401c10050031441da502d0309501c0180444111304445181d0745030490ba40b6408800c16202a01d51000319590070703149048000c80280f407400e0882006185103102e08000c43c0e031910a01a100d003441010f4403860760103500da04140ea00440c607200c1007141040c0161050100800c0304d40141d40300780741c0841c1c0f0f501d03541412040c60141e1400c00280d03010005031b00c08415040450340084900c100c44c1441107965482c1019107402844031003035007200ca0104514009440c40d07200003101c4e458040f6800c408051141c07200341180e4111b07101c0c65100400201e051042c074000740341c003009 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 610114442 1250 610113192 610113209
    0x18090c09021309050604020d1a01092903070c02060d0501060305010b07200301061a03011a0a05180a0f090b040b0f030a031107050d03080f011703070b0618130b01 71
    0x18580300200c9a120058144a14103c89a903100815a183c1c0ea580490780707a110004014030180780080580000c41c400c1401c810702181d00f00100050b135541080c6070002c2d00400d008000604400d2800000483d80010240c20802020007004401030b540c0c03602805141c9e03846000050158184440034086800c182c1000d03500b40701c107000310400580b44801c0c001c0200041114401e00d628040086070151007250401c83d4000b030309000d46045142e502010314121010354034488070040c610440c0c00540d225079015031002640c10440010418107002480130324010207402c0a28041e07844c0414181c4c201c00d5000050003540343c1c6442905d5280c030f401020030b0030f0011501c8201c42c801040c0020b6440101110080c203200e5500807003010b0010500c0b085008180140c1a2050048980390007040b01034121041010383d00f50400104160202c4d41d0816008010f210003986001c005885450300e18000174030413070f03008610203050f41c251002d111256000c0c6103001c2980d420b02806203002203200d00d058101c2d120 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 610115692 1250 610114442 610114447
    0x101e02030c13050307052202040302092a120606070c32040203060303121e041211010501081e070506041203020f060c27181027021318090c0902 63
    0x3c0366120b4822070400e24182101f050403107030000070507019001d2548080e60100c51401080703442682072101008a016440350160441d81040190829008d1580da0080d4010030701e000405a0911500170481c45014044c404041079440101e0000030710500a02c405107030742440d409443d40b910328031101c03040c041181c040d401c40c504a00030075528018081240744564669022803024002000f5640d5041c4036281c01c0c0e500307480e00c1c0c14914208040c080c0900000348480d201518161410702c5020b0607281100040c15080d41c5003c8203032884428104071010b180a41a400100e0365100030007000140340c40e44040c02d0451036820040d0601920301841611500300000300103a07442403904035000040f120000da01040c03107031740ca25402500c501c1b00c00b075042010050401003000d040240c2d2849424440741c4088116200c5103448940304005c5801d00100800e0800800c8001160f00502640b0702c9164902c0307120f41d070f43d80c000d005100441340e160190359500c04040040c481c0c8080c0000c00381c00d2914047d032 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 610116942 1250 610115692 610115699
    0x20403050606193b06090f0a151202031c020a02011d030102130e01090e190302010b060a0c03030b0a0602031207090f090b0a1403101e02030c13050307 66
    0x26110140142010300c1500a0610900c1100c810306124019204c50420741540c810755070000d0b600403120200d01007140041c19244403440b4030b9401001c0c400c0303201900350071550300e0b01040b05091201c080c04000c03945480e400002c5001014815540c01056440201c2c0640c9002e401130500709415110b11000d007071012903c5049080d00010083c14440d828a8011b500f0101c02c111500c1c0b050003003c3c956415400014000154614100b00b50181d5140c2c189a50003640e0324a140800c5400004a0140c00c5d0030001c040c2040a0b41e1084600792140030f400045200403802001030f20720b51203e24148085020500d03c001459414803406c0c0c078004041c0c03440d010741405c3c0760002e9a41d0280c0100541c904840c04000381100c0d10a14940004161040200030f00944a604c204081e00c8140c3c00180205101c000008051a07481304800c4a22400b80140c4040c014113440440031b08074280407020449528400c03620044180e10043d07104030101c40724552251400400c013150304600f540b03d42d20a6000ca6001c0c03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 610118192 1250 610116942 610116953
    0x2515021f0b01080c0904020d0c1116080a08090a120b070f08361c23042313060617040309060525060903080c070f0303020c0c0d061b03020403 62
    0x1150001c0750791081d151551714150010b4080e124110010b550030f428a080b2080080d0003900e2608040310300000d540301030321460009540015035105402c12541710000450106131144c00070140f0300701c00390811140e207486541000d001000003404585120f40700d010004010392164041c00020490f25140348181003c0d8a140c88800f0400740c03445141c4d440340003080300c0707581000070340e2850301819054030010302d0007030b80d16852400c100083c0c40104208192440071001c0c002c105000e542c605000741030420741030052001c1d1344000a44803500340c0c0b12040d80c5509a0382ca226511181456044002c900141080c000500c100100c1d00600d4000800b4030038040003d402104500940310245046611400701c010120070140e117008003c00403181150080301840f400c0d802c010f09144c025100c92805844652981c0800e200c0c019000d8003203200c1c20740382c40c0000e200390020003060a4900c03c0b1a4000c0c0c1d00e0000420254910313500b12001075460703003140b8840c41000701204422809040450416186413201d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 610119442 1250 610118192 610118207
    0x3090905010e070f180605030115080c0a180e0103150c030203040b0711120d0203040309051009090b012706031d060406091a0c0405030601172515021f0b01 68
    0x3c80003480745901c907119005102c0c6039543d1180250b0301000b00300b44d0b9203d0010b02642d01c2805070407802c441003125001d00e580aa10388500914010351410315240c1c4e040800c5403442003650300310707604400b018000201d100017081031502070343c0642c02520750035008102c24000c5865860460051500510811012960102c2c1942d031214503402c1034207408000203991800e0204100c00a4004207001c121415000529805980b0580c442d03210a0302c0c0c503881c1d07130030414400b42810001c030001c1c10601062004000f035400c101c9940c0010f040c00c0c0340400e180b0440c0d600c80980031460b103c82802c48001000210f515008003d16002041507901c9504041c0390856104c10005001402d41916400d1460800483c285440301108015200001d80e040044100c4030541c0b080c4100c9100f40f1032000003003913600540c0035104403a01c0d5100103100b481c0d4666003010001da00344551141d00b8400101c0003c0702030040200280101071039010f003080a03c1030454401940443c1c40c2401c40a02d844405403003660000b23032 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 610120692 1250 610119442 610119451
    0x60a0f0b010e061803162418061101021c020c0d0e010e040513060504150c050a050417010908040b0c070b031303111218180c0d0c030b0405010806010303090905010e 72
    0x20381544e1030340040c01281c80c2891100320225004580758000400d04600c3d0070040c860f6040352084076048400420441e054102c1a00c2040090512130040140c9401110f1200d0035502183c00542060011035403441a984044410100c0f160001121048a030b8280844484140d80d4100f10380c04501e90b4000031310000e03114415038056550b401c04590305000c48132000044a90040d0280b14900d000d1402103641210306204040903418541c0c01450319002d0026149003100039961242060700d0403030581c5414108200b0071015550b501000c4011815100c02003018080e198030180d42c6d050300c03600360b501c5c0c45500d522a502441d4144180103405e403d8a811101041d01840e2908019a511794a07a041c036003103408110201c1c800041c41c1484007103c03d0054000a001c03034640d81041e0341646400b00a0b0000c0f1100c9002c0c09080000d8a55000940d0001c0381e100302a240c00510320a410003c00d00700d900a801601e0310b5842000100105a440344210010745a4002c00788419450000020200720000e403 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 610121942 1250 610120692 610120717
    0x70306081903030e0d1106090a03120c0c2a050604050307031b0b030a05311e0206070c0509010b04031208040f0f210c17030c0c060a0f0b010e06 63
    0x220301c0e4060500c00d0704540010070a4034140c4411100b110809850a460082d4030f1a5500540b00019040440800c5808020780c04d0b8071070304030300c501c0c0244020082c0b0441641c070091100f0302c0c1c913110100d000d0040c0480c2039096803610040441d01060200a020b1f0140d21580c41201d04010600031303a1004614003048035441040780346860b20355140c89410f40d000b80c1144803615004003c10040c1c200980000703005544065540003041c09041d0381c241c0c0610007001d41074076040f0103e190000100b55515900c031000440c1c03418031080711548c1c00100203a00c580010744440141c05018001c43c40c2c40b43c0b4141c010700003448260302c1c0c6491580c94400f04180c4400705000c0c000600c1c0020705101412185c2500c9076404940f0700f03d10b1856191241c2e940d101404446c1e2001110502964003034002e100707008485d500081080144c4103d0120702c05554401003034110800c00038000051112010401c05025404000011681851034100e00c01203070010b601040c10446003250b0101a038031149c040f141c10714400c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 610123192 1250 610121942 610121983
    0x41107020420181503040218090712050321160e0f1c1203050c0d02090409050d2d120507021c050414090124021c0e010807030608 57
    0x198004210703000c03010301d1510112000802003c0c00749141000e00580600300da0400f280440300500c1c22140c00b00703d0f030094010411a50f1104200f01c016840c641c40300112003243c00642d16803c042810415103442240c190f800400c100580741c00d0030a042c2510840c12280a00c07900c2c00790005d01c0311940140c1c8402c00d02803144088145601c464a420400c1040984000c5841d1907001c00420072800c65502502d00e01c0710100ea14034070500c0f900515028003109a01c607418039689a003120001e5014020f1745074002e03070310500100040c1c030030300401d00e01b00901c3d16201603049440050441c0708111f24600c1e00c11100d80f105041c50b858101c1300710007980c81c4d2000002101c0d551184280c0c5000c405140280c02c2e00ba44a00040055520000420a492018100ea00913819082c28014912000c0c0948158413283c1507400c841c064402b69400b440070494812500d4038840380020030803c071109000a40041d120005144065820880302a040300c11442c04001045c40c0464203601c5680d4607070490a9240711 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 610124442 1250 610123192 610123211
    0x150304031116060c03020c0a06021e01021605010207031b0812130b04110a0911190c080c01060e2401050a03020d0213080f030a0503040201050319021c05060411070204 73
    0x4008040b8a94005904680c100d921080040d218070701a0004400510428800e9089404c2901d800004c44189400500e4003083c804c41000301410200b00d1002c2c1c43d0b60911614151180080ea4500b040380070f03000069507800726040051a02c01c54035400700004142540342400504c40c0c900b22045010401500090b40e260841c129420f01003034070001d4207034003000041c001071100014802d902c030341c1c0c00c035055100740d581c0350910415070f80c00b2860801e001a050140c103c2000300310783d81210000c124a000010101e0039514140c43c0d82001c1c2506806a40d609c07810700c41002010031981e0011841070302c1c40801c3d414400f0844600e441c070400d035030410001050080b455406501590505e0f803d03900e080d0740b1184030b0100140340d503000380b1405035940304414065490402c00700403251080401d5440d6441c55885030015201c6500103401524403c2e48035409144da410180b029115003003a08841c00751107421a80000b042d1840541503a2155280404100c00102554111380300b13564156030101300c1075003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 610125692 1250 610124442 610124477
    0x7060908070203100617070e0a0b0102030f0c060712020f03060103092d0b0c1306080903090603041b150f1d03010e060f09030a0903060b031c0509090615030403 70
    0x41d0380c00003500340c415614501c0c048103958114505482e0340380480041380110000b00c9648a60b6445007101680c2c800000c543c040120b508603a1380e041040c01144e2a000c0c111741070a000368020540781070141c0010042c00007441c6e0000c482242d40360500d10660070101c0082c2c0c411a00d1001400850500d13544140c20745c00c000115144104801440100080c0f15014002d501d140041d8030808488047c0403000040c1612821030546100222141c501d0f85030508145003690b000c1000703412007440703100038800035000e540e90304011441a0300c81c1c074a40c1c1808582c00180d0321481c10700d8111114a03e81494180384003030f400200144983c01d02e10f0a803025130010986aa2401c151449803034141d402c146881201101c0001c00501500342d480301c0820300da490b401080e8603070040052307800010b005440c0030804961039070044003007400010207032045800d140315003038004010700901d0000708102240415541c904003440682c40760041d80c121055404044070b0418511004000505000c0d010007120205503 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 610126942 1250 610125692 610125697
    0x115050616150911060a0519170103081c0c1e120c0206071e020a0305031e0f0601030b09220c1a1c0c0f0819050412030e0a0807060908 59
    0x2d82007000860b00d04042a11031000c0c0802c000c0c156814204d40c0c1c41d88405040440c1198000d000c40d41d206c03800c101c0c81401040160104400100c1001464401040350701c20741040325009510807010346030340c0d100c10482042c2c4800f1050b220704082c3e00d84950040b0480d009002c684100c5170003540f8140c4038a4548003030342c0205103a00d03040d40b05803428815011054001400034050441c90319801203086603024510907603614601c03807074016005800c1c604000ba0089000e550854103013100e90400903001020340c6170681d0f0880303a0f1082c00c081c00080c412156090710800d0a00d55080e217185510340b07040c0300c88400360840c0e14100e0718041b01e18103824041c00000b00598002e007000324040c090300c5242c04000c20040c0c10901c100782641e80741c1078202000310094460a110704c0c01580742c2911442c95004140e400210040480034103034580320ba405401081d82c400c0d0343c891071046c0d48100051108207002011101030700701c0804030b03520900038131002c01c1440c0c0030785000070b034002c4012400103502d1802050b5030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 610128192 1250 610126942 610126987
    0x50a090614010603050c030c0405042c0a030e0a080304180204030b070306230907030c02190516090e1e030403020604030308040605100b0a05250302070e070201150506 73
    0x2140340030054010080700d1994941260011340d0140600d41704d1a07804076451000303640091485030100820030aa040a40040082c1c1c03401c01c40700c07641c1c011413100d1b07881c12450116000d81035411480042c030805401600b65800c00b00c2c19103010f526141404a0281d0307070301c07850050342c2c01d0741e9008409540c1120140c0450303001e154000103490389410002c0014014222501400754070220401412800400c076508070034026500030700121041d241c007002540280303075080484d42140506900c0e0700c0d001c20b419241840d15442a0018081441d1406a0240026041e00203050745801d0000028003540e001403031070403000c2c41c2540c0044210720030340154a03500c103981c4000c1d0004000700e0008140b513041603809100302d00800e0140040c0e40e0b4041d200410540a0040210300d25003803103c9442207200354040c0a0211450b082040c550f16030309151148000914011801a030098105000c85103540400c16000311090000784880306c0910b603014002105070007503e0240c10f000ca04100d910000d08000880c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 610129442 1250 610128192 610128203
    0xf0c080a080a020c040207020d20030d020d030e010501080a0b0a150e04020102240a02090f030601030b061801031110030b1207170714060705030d0f0204030212030702090a050a09 78
    0x2480c09181070302668008035020005401520840320305820503000715030351190f005102d00603c0b40c96584102c0040103400441006011101c0200d040752010028030301c1800039600145400251030030018103445060104056503414400100b0194400142054100c0e5120401070990380e0759000400080030134a000b001850100500060132040c4200c4041c082c50007a400d403001114022800b0b0540035607004443c0600b8200000900000500e0b4049c1401d1140101103941e40040d500000b0f04d40b000c280c006446000b0300c1c100788a1503142c1011f51810903010314051088544c07443d1100b00c44403202d1039800e40200c000c400320303010141c404e500031850248018100340170081f520000c04c0d904ca13250300580c004411144070b004800d170740c0050405d00300d41290b014090180d2614040c0710f855001a5401c48403484140300400e10891030f4050381140f20910280140c840707145004104009039920050f00d040e4000304440000740c0c031a42e00440e4401c92007900031949403151403c00008141254004e040b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 610130692 1250 610129442 610129453
    0x201270b062701060f090608101e0305011e050f01030c150507050d0c0201110c09130f02030d080901110304020907032004030c1508190908130803120916030f0c08 71
    0x41c441d40129503a070359040c0340c0d40e86e81c80c0645c40b50320682c2c40b20001d1354000121380c0980c1080020400c006103003812041c5240f10b149200c2d580b50b940c203080d180c9400780c0e40d21441c15468913401d880168031445910a40021550302d1552568513141990001405010560700340060040041d5010b2003c0b01c081e6607002d002c03101211a06c58004100781000f446c200c2c00110b412590004001c80065805460341006080903800e031500c0321703000b6624004150446d4610710510850300540d5090000a10094203a1501601032038144a240d0848403441c0704403210310340c01d1040c032000d611100310300c03035128140c1c2c00e0008900da068110070002c01100e0002c090318078400a000700800c03d0018000c0c1c200ea4404e03442c59034445000c0b80980e025841102c40d4500d2030000d0850144809554000405441c003d40f0035038a09407121102030f280704855005024903900004104c00242c4480d5403095110188002038001c5540d4145250020b1011784009029421412a14401d0200251594000702880c2d0304455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 610131942 1250 610130692 610130699
    0x30b060714010b0402032707210c050a0e070315050907020a02010e0909030307050d0b060a030b0f03011a10030e010504060b01080f190f0b100201270b062701 69
    0x400c03032120a200c08594200f901012503410030b4000d8034040c0712500071440d5841d1600e50120b1040888251400c0248904e00001590880d040110074080c0070402c1024210050b50926881c3d0312600e42c8010b01691000713104010351046a00b02c160000043c0c540400c04800903000b080600d00c00350030a542c0038514a0070720420503000104600a10300c01c0e01c40d00310060646080040008003224070f00225002040094492071061005001902404100141c42c00008003c241d242d0004a805c8000c02c0c2e03500081919464180c49080301c0c92021802804101e1200521030034000072908102d0180c1000c8510b140040e000f500940d030a651520001c01191030241405000361086007505400710f000d52020031244520a15410b1040e80d1042d0490714100c0703c0202c0070020440d240030602815942c40f107071900343e6200b28005640ca035850f4004200c0601c4041c105c1030000d00081d0440c00e02d0702c4034070391800213000c90404980c003040441303017500d1b12200200000c4240302080c1c40160703003200803000070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 610133192 1250 610131942 610131953
    0x15010e121e010b0f010f17090a0b0903091003020c280c08030f0304030e0f060304050601170d0c06020c0a020a031209060c020f151c0209040b0a060c080a030b0607 71
    0x80c8001e400d0400410a801c1e12055a0b0882e0152142c50760014160340d03520240354058944c6224550641c0340c9285000004800004c0311038056415060782d40005006006100c0281e0780940c01602d058042d41c9402c030110006410f44490700000020325402280c0242c1c9003d0a003c0b070f41070110326145001d5001c06200000c41814a1198210fa046406241c08203020000109503092030a041140e40e10790b4072207440030f0b07418000d03614846502170090b16103002181c840c40d0241d4040c6104000074241541403800700581803010401d01007455000003054260140c0c06450600d5894102000580c1c406a12804504158100001a4202d1400d000c0081040710950385280703444195614002c0700c13515513600300d41507107200c500039510859030700c1000c03000e2800b048190049503408940e1861300c20000300f1156815410b1203000445039010901102e181000e01850010380d900300c4011035240e080100c0508640c08100b40580710200105050301540e0103a4400c01840000402c0340c1d80718201480c0c030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 610134442 1250 610133192 610133203
    0x20030d06030c0f05150304021903050309092a0d1517010506041e05060a090f060807140a0b0a02190b01030302011d100902040b0a0e01050916020615010e12 68
    0x2c54030034100c0301c800140e9100c524003000980c1c00013001a504128900548155908050303c207a83c403e04d0311000c45841c02d40d5051000056200d50040c503204d45a4408000e8400c0300281000c5644201c11a9500b14414076408283e0421100104680b0740420303611540c001c0c80e045001c204205460070340400e403030001541c101000001e101c028800f40e5194004c1c042a100780c0f81020482c03203010704178004844907903041075034000409006030b01c0240d0b503010f0310010b4580034039045010035903a0030284400b000602511025111141c00074494107680000b26001014520510841120100e080c1286502c01e0120098004146c00d82c510034030258140904040030030310044000d50f180050344000910004c4420700d40054142c00350240e88810b695007400f41c800d86804aa01658600502a45a4451883c038009d0081e5813542d401c0d42d8105000d0101010740a08420f003943c00715403141a00660018900f82d000800703030116000f0301d4004c030059501712000e603d07803a0b0110301e641c8100b5003100000ba0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 610135692 1250 610134442 610134449
    0x3050903010510051219020103020d140709051219020d0507080706020312011e0e130b04050604120c050303042004021c0507090b040902030618010807080c091620030d06 74
    0x8804105080e50140c40c2c2d601c141800740072844a1180301b80d50055800f07580940800509200041003214000705504135100c1c00b1126080400c2031080140a82c0c100040c40a03400190a070041030540c8101584550071004140000e1040902c1800b60081010500060b0010b000b00f8040314030403030311603130042c0d140e4000c10a8102d209020500014602d081c1210084202100901c95a0441d003000c1c540041c0c0600140f042c50180040540030300010100801d1501c00d6018401804d201e0501e80340c80311322041da03c070241c1c081101d02d01000700402e5010080b00d0300f15620080320042d50f0900400405c00f40c24803070885a0091000c5040403400b10701c544450b1860700450000c10550351407940503200054140500c800c041e80511003400704172050f034000e54200d180209501c04811007448010300402c400d800200490300070010402c00600104100009603008841c003003034515007460262444e4008907124401c0007004690884200b442d0703080c0daa020400c0100b0381c0d0742d500c41c1e03180c41e001410340c520 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 610136942 1250 610135692 610135699
    0x705071401030c0c110409060204051c050c2209030905090f10051203040b0306030109081605100b0d11120303150909010c0818010e0601030c050f0405010b0906070305090301051005 79
    0x21642d40d6014804c2c4c030600304690380000292400401e0106010050103241000c030341155013040007007141d94600401d20200200e4260f140700e051040d14000b8101040441d440740030300504100c180b1480e054043ca003220207500000000d103081e403814101c07042e00090b404103030000310700c1050080b00b40d03000908d180f1400403440344e82c08555464003401030b5032a0704103410280f500144000e00221b400340c070045410032030040012540032040d40310844940d0104c80502d8002060700d4444c0704100040c4182d02c00321390f0558040160343c2184000c41c10f04400107100405851042d1202c00e5686d40b040d80c5d40001c0046541203a803641340405094940724400c2a80e01d00c5143c6501c005100342c00140a240354002c2c2550f100d02031611182400d41d5901c00c00c10ac060b419540700c000c0305a0070f03201041b43c24002c6002d000c5c001c1c559440c107001d200d000c42c0d0100406000d00d00f480d0040c480c40c010b080465150300c0c019039541e55100554201190140540041a076155081a06104002410136404001d848088 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 610138192 1250 610136942 610136951
    0x11508120f13170f0706020c0622060305010e070509030d03090f1703180a2d0f030503070e06070c3605010504140702071e0b0c060103060f0e06060d08070507140103 72
    0x102055580d000340c4500e4006901c480c814560f1418260043d00d00550000d074403644452b0180c00400c40b1400c81d422201c0020b0317030361004100e0003c031142003a0b000085030610518120702c15010070303240c1c4030030103421003455110f916079020022840418090240c0141801c6003140320454000e115500a0703c80780040c0c800b071440c00c400420301052066000381c0c003038000d4042464004901d4030b0920721403406a0f5045080c07441a02082e03200c094900360500c00da603526640c0c0713400e00c0090500c1d020130f00a94010181489500001014924034405640360700301030f40a40700b22039010000305400c2100e0b030302130010782c002c0c440502d2045401c06410b0700d100311010f04c50b10064610030300c00717410202d62450042c0e004800c00c01942090522440b07000d0f109240384540c0036228450b0114070f602000341f04115510800c0100240401480f5890301c0b4420319405202c02e800c480c00e0301d41d43d91800f414544c070542da580401010012030308121100c0d150b00400340c8900e144c0c0c400c1d00e4808028131b01902c60100341070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 610139442 1250 610138192 610138213
    0x3070e0c190e0429040614090c0f0a0201060915080d03110c01060e220803010306020304111f1815030e07090c08041a22020307030b1305011508120f1317 67
    0x20b000380410747e00b144110582140d02030007004011507020303101c0407011000300710341c20212050340004d1501da18140c00228000c0c1c940841002255000110211503154051052040c68400300d01000008402c1c500851100148000141580b16a110045440d8605040014409a40e100302031190401c40c039001e400c100414941000d942c61500003c00b2a04104014400030300d8560245810a01030301d1104041c0d2843c0b00411135618003640030481c2c101038100341c64034495100320044030304c80394061070b0380b0802d1800782813524140215000c00c003030507215082001c0c1040200010030040480317902c1400030200c0380c0000b92030703845c06030b40a4a10790113401d000904038040740440d40c01030241c50703ca04800a50281300280301c6215003c00c03070b0315000c0c103400003001c105951922402600280707890440c040ca01d00d802070840d040703065903241d09004140708005490000c02c041143c050701c018119600c50305510710082f0f500c5200d010390801c4e01442e0300440e07000308110170800d1410082c0103c5250024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 610140692 1250 610139442 610139449
    0x703092729010c0305070b0a0605120c1003090525170102040e0f0703241701090b04030f1809020901030e0f100e1e06040203070e0c190e0429 62
    0x400e001400d080d0044860708a055481410001d4000c0c1c000e1401e01c0c28010507582c0c6da540b0321000e07680e10722003648402c002d0240785401c1c5020030458007400003c1c00288003000110f03840d4a0160503000616550340034010903c0b4044c09034101ca00c440307941c2c0400107105080e45c00c4000c41c1d0b074000c042f0307030103c010002c903003205051003100d055070181d81800fa46583c503d00702551481c002000381c820140c9a80d141591100b43e41104052048082049160241800c043c407110711518140c40409a0500551501082c6a240385540058040c50712407024601c416040e541d803a0211141406074494034000a4042c81c039601400b110f26091381d00341710280c0110314103a5541d411080e01200b680021008035003105d01540005450b19603101555018406c2c1040301059241c0b040c0c075a10b031500000100000c614040c040315010746071400001c50107043c0043c48100e41e005070f4004503240c840115120030f00c2c2c0d000d24002c4482c580001c0081c44804040d08a10381c200101e50404018a800d8041d83c000c680fa = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 610141942 1250 610140692 610140731
    0x108190c030803060a094101090c0516030c05150f07030e070504090303050f0a110708091f02030d0608031617090d0f050f1f0207030927 60
    0x54120030000600c0e07086071601c10300ea40c4040c21550303121401110002d02d40d941c500521a4100c5020030701c1c84d0070460755a42c40100022401c0e081803e90b140c0c0000c01c01034014440b99815208a40000200450200c07001d848900c904a60010003c24016544040591010b03540d22074602c1035080d47d8440a041e90b220b071004009462011002e401800000d0120344641c0c000d000906100b021102e11035601e001150445a081d038095001030384843c01c0103d0418070326070850300a910380c0000c2011319550514a42903004050009180d2280080d10700b0481d903852601c0d03054189052101f1403242008a4082d5495003c482d00c801954100040054000c03804003c0e6001c019002601c51585a00f99803440454111220703030f400d00c0e400501114056484200e400601603105000440c4c0c6582c03242031040c40c2034041c08650516a001007080040540b034107041d01c07031410600c0805a20f640e464a016203003450250050325a0214001c54261010724101c0075040712801e4076800c1000d2100d01110f2541403 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 610143192 1250 610141942 610141993
    0xe0a0b0d1407320a05061c0b060702030c0d060204080111070b1807051c081207120c0e01030f0b040f051509150105210403090518060f3102030108 64
    0x221021201100041403c403e800800074018980584203031900005074054015032a0711a0107550894480306541c000e100d031510a01d01220303c1c03428102c050340000e5649268400c0c40e4050f0b039650130b03000304002d0550103440280140e003000317015010403100c40101581000c4025076407540074101140c0c5007003410b841c1d80c101608480c0036210140c202030134042d45502e10400211120503540e802404145160042e100c050070000c420441420000b400820341d581495040d60740d645801d4218035010f030030414819102d0800c0c03c0c0440d09904151a403802080415942500503040c135680c41501030259022074880d104a000907600c040610081c4038100c1c0c0125142410b030846034032035088541c0201c001d030016080454981c0c20540510445051040c81510110b0100e48125420700583c90048ac1d030405144524400c0e60003440c2201c009004803801100381070180c00c80300d0540c0259013a004401008036032800d4160060725031060400d0007942b091085819500a05e1a400ca102008905001c0355 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 610144442 1250 610143192 610143239
    0x70804240302073201051302011103030f0a0b0103091a06090c07080f1b120304051005090c0f0402041d06090f01050d0b06030c0d080c011b0203040e0a0b0d1407 70
    0x5110800c40720010614030b400c1844e01001110502040b1000d00f409002d00c00c00d1260407003002c20000b4800500901c4a50340b0b1001e85420910400040020301108180e014100e050003213100001c0d000180c000b400311a001402504840c141c0000c0c8080707144200c2d018400503582c94003a41d5403040710b41164080ca01d4024034038407041007810300400071100903001000c001c032462003805030505801d42c0307407900c40e24000702d40d00000300c104001c1c80001e0204424101980c4814006841d22925103902c50211003c40c40c4500160542103a507911141d05a03405000c52140b004c0129001c102d0a00004c0c0045900c10710455400303001070080c090f40320903a4103c0740094280c040c1c1d028240d913100d04c070540052629416201e0601003138103d81d01c1c60b1001c90120301414510f40da07018640301580c01e41d01c1ea10981f0303100c1c1c8007091044181e9a070005c201da0403a00c886619042c070342c4454070801c6c05020813030005a480700340d9542034818800228507401082c0b003800e08a40c0482c0d80c0310b113a050010442c2416021 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 610145692 1250 610144442 610144463
    0x1a060a02030a0c021f091a07030e2205090304050f0d0206040302061e0a0503040515010b030c1e0c15010f050a0510030902150a02010b090f010b09010507080424030207 73
    0x155029002c0d4203c11032005200006520000010541440b1318420980c0020060601040012030710a212650386180320102072810300c681c0c402810043c006c1030007901582d40c40c103040c0080d1000c4402024460622002405141007020300c80390307290440c0c00f030507108042840b2014901d01d810f10480c5001170b03001c0c06041c10685142c007000400d82020040c071518016401030019250109030040c43c813170362180c8803e52203083c42e00708545030011450300e40d9180d0b41d5900060110301949070075603a00c1141142c0041e580c4022100045105402090317000d01040c001c55007040006002c42d0b0148114002014102c1d81c1e0b82e20712210700541281d204941e080790003004140007504290380484410b4116042c04a8080c69603804144803544c40e001201d0780e00e802040040d1560350a0080d4002c1d10340c2100c8409513410300780b0800724558010301c00c140c0c000d000000c004000e40d0258056920141d040134185840c1da965460b0b1400181c80d0004200c508000307007110100103402032007581c0105800000160 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 610146942 1250 610145692 610145707
    0x61b11060f07140c011406060a09090e0f06010b0703031103012102010e090712150501021b0423040b0109091505040204061a0c010b04090302100c09181a060a0203 71
    0x60600748003601080801ca440c191681840031010000d10b050b040a4000141101c030100000c03984003005016a44a0720080281142d5150311603004420b551522070001004a02d68140743d1a0101c0074103a141c1d07500030f00000107100789952001d0142c00b4020345080c801c1c28500c001f42c0c9914842400382081d10251003030030151003200068104a40c034418107011030040c11a5000548481c021181e550020b1062003148500c4105401391040d602c081c98140e0049904000010f51100e4144120045400b032284d0150551b42d07490f04000c6a5101880045170240204a80d101d8480c1c4212783c190360003c00200001075400040c0700e104000d03500711802e501d405070300038031410140901078003d03a40251141e40c0850712141c0703143c138280e1040b00844200d5958542014260035103084240061203985404410008650040f401c80da0007600f000b800100d0b13420424090f42d060304180c0145a460261201e010f000402d158400c802480740c5554600070140c40c07104103d0030344101000000145c000b444610f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 610148192 1250 610146942 610146961
    0x105030a0b13062a020105010b040b07110d050f060f0c0703080403020c0a0f0518150607050102040b0d02070506060306040302031909030f050304051005210601020f0703061b1106 78
    0x30741025204403040005401030b00e0b40f205696400601180140c404100c03100ca0601d60310303111030180040c3c0000d2182e90314041d1800683e02462181c0c480c1c0903070001c1d64004004488000c1e81d9151030007002c89201d0030090074081da95407200300083d20684506008582c02e42c0c81d0000c128402c0200e078030720900c1e00743c41e81c0c0c0c100c50140e8013174011810b610480c5040521a81d4a841c00c402030031a10008008241c0382c17804001e0301e600034038280340e44003d401042c091094032546020511140581d00159104400d10300a8020f124650100211070004503041860103d103400810205020f002254000c0d115142059141c1d24103440080240e03100304407035003080002070203030411101d25061456429a4a07250b041680081d40700403130b080e402c0010144400c0c60400ca00c820ba1220741c0c0782450820800e4140400303141d1001d04d0041944d507131040000e50b60b078420400b0300e40050807101520006a41c80c500a00900300c0c5031003400c0840300ca0090069220700c5a000c04864071540401000c1c1c50f183d40485c03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 610149442 1250 610148192 610148213
    0x9090f06010b2107020609150603100207020a0f0b07020405090f060403030c0903080c0601030507060c0314091309151a0a1a07230d03060b090931140102030105030a 72
    0x70810003424a003070b02607105041c0400603114030060f401a000c6441e10b1820123017403004140302c1d0b1800f0031b09101440950b850005000070101d002c50710040e620344490000440c2034025501004d42c00c0c50308040800d45018220107007043c0c52096030203100381d4407071f1101c041d102c0714011400c012030390024000030301080c03094010140d80449410b14080399922a121f800c856071101700c1c100d1440c3d020100400801000700308000041820746001c44040b110f43d80d000b8050542030340240c003000303070206061b4202d58481a141c0c10f007000c0000100102ca0041c41c00960b00f0074203030020003e9501d400c40b10311801c0700c0c1d5482c41c24048801060111494208030b103000043d10a8202461041410700028000950040100c14540b02d1210390090380128140c0862902840851050030903003854410000c069080c0f0a88229110480c3c240c0709035030f02e0000120340f00c0910511084081e00d01a5008880d00e150284541c0c514000c0108040caa0b826180690a038802885060b4040c3d10802d41c072740200390062807 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 610150692 1250 610149442 610149457
    0x9051023040b072d03020711121f18030309060606031a1309080703051206060f040b031b04170c18040227010603140a090309060507050f070f0509090f06010b 69
    0xd450000760a040d04604c03401c448101480440e5001a0304020700c24103007000600200b0484854074400408640e03640c60349140400d2884400340c603041120980e07129088180640e8000c1e15070350300c001190800402030801c41c0070980700240342110103da420f2203406000905904005140d00071200c8005010340d410041d604080385540d00c04822000402d02c0004200e1300b03000b9907400341c90390803503c00d48240e43c0e40038003620f100364805c0100f03548542e480000d642c1200d411400a80c0caa030307980f00c00581c04046800c0b604000d002d0024010500718461a20441054801801c41e0380c0b224600c0240702031184510f000441040c3c000d00054010320340005d000b407020300098980c225241c0e480d800e40074803641c01c2e0060f00102e51541d240181c81c81195210661000c0e00c02c00c00d01c04201c00f41c8004d0721000280c001c00f42000701c0083e0740c6060010400c090740e1400c09031022190a80d03510018010080707198001c040c465514900882c0d254180002c0b4000014120380c0030b80316a0746406a065410b60002c2da = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 610151942 1250 610150692 610150727
    0x14130c0305060c190806030a020603070c050d09060e03010501051f18030507090b03011802010f0c140105060910140609010c0204020a0818010c09030b0403020109051023040b07 77
    0x64010000400034002680070310901040c0a8991211a403207205504c40c1000c0241040fa416041040a541c00103c8445030b0f90181c1d11690b4130340f5411421140464a040090007038807034903409241c5135612940310011608190f4556100e5403988003098240e1b0300a12800307a009010070041d0742c04010a21405c000c1080d40e0a02d901d41c10300b0031b038071510340424070340c8195880d820003201001944c145000f00e03444501d00318001c00c0704044403007604846c03051b0700e075000e0304008081c034101c6145401f82c1201138850350041000403007020103208450281104070f603100d0184e2908800716079051041c3c1810707401c0c2c484045e1090810942041801925008094882d04116443d0652800341e143ea1009150050042e42d13450041d1501140e0084007115a4010302002c2c0c0c50252a0030301c0607407000141084e2580442c0c080c84549490400320301502c0c903c80003074003030700560f00000e90410041d801851500c440f14070044070000d034074540e4030107040d048601030403110365200041c2103d440394808118122000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 610153192 1250 610151942 610151963
    0x11e0e0705092e031118010509040f0f0b03030910110c2205071b031b05010501061125120c0b040f0f0504090c18020d0c050307030f1413 60
    0x1000010400140503d00c001d103510608801c1083c158803140c20751000705241024881004600780038030781482080101c0c00c903001808401071050707103e40d04890107190010400d015070709401090000410006403076400c0d640c82e00108036207504010041c2c62250714000c01000080e1441c00c002d40e5031444162012406024145401c0000d0b0745840b0b00c904c40c0c64040c0c680d00e01400c1e0703240004045070406801c070004e221030f0617901110300d800d14009081d07443c1e0625014502e00c80c1020205d00301d00e91040c0c014450350070f00001140c501c1e84100300b0004070480781c080f00c00d4014031802c0300a0f41d07003c50010241501c0d03040300501042100d0031080541c94800d50529420315528000105250000e4003d251303003036000340041056000b08815200503010403034003081011001d640d07009010006218029084203150401e13040000603038155a141c0f41004014000f040c03d280e401041c9910840703100740070038503100d200701c1c02c0542d5110b00302001201c8544441903880b030084000a08042c040200c9814000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 610154442 1250 610153192 610153207
    0x1a040e03120405010902061c0b01030e100e0703080705030a02070b03060105190c15150803090a14190b0a0f032f0408121312030801060e1206070c0308011e0e0705 71
    0x1501f004210030301d000c1100000400340306030403074207585040d4034440c109410400c0301189003501080300401c1c00403d107800503400312078074030301800d091465201506401c00803803074030203000001c8000c20250300303103900b980c140c0c0d510b840e80038401d03001c10b60f03000e40014024048200b00214000c4500301000d45400d00007a0000a2b9451040301e0000c0c0c52402100d40d1241c1ca1302e10030f2564401d1210240800101942c01e010402c40840c0442c4024070440340200913484025461751104088100104118405c2403800360700c0fa030b0a14080c0d400303804000000348500140340d0708a8441d00c2002e40100703500c0c0c562005a42103860000420100d010250030300d04007008006801d002c1007010041000300300310380980b2819034407074201c0d5a150551020089080c1c103106480000d5101c850307181590409c0c02d041e001c07c0003c1300420800c0100d80b8030710b01c80348221001e1014250708200c601800503c83c0e5100e149582e2030702080003400c0da00072800031007542c0078001401400200f12015500505610380141092136 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 610155692 1250 610154442 610154449
    0x130b19020a020d0207080c0306220c0602010c020d0516020f040e010911120304031205030a060e01060c0204110405030316020d0606031208090d211e1a040e03120405010902 75
    0x9507581102580c0105000003600d90148401d50050030030742c015001c80800d10000c6512050b0040c903007481640c5260f2440d002c0c0880c00502c0401d00c1c2c00854030712900c1c3d2900d074082d0003040306002c22409031040144c580f180798418401ca80c4011085045000d00414903402d01000d80b26401c00540d005441d18910164070740c007486904c6030a8021054001551020001d01c1568030b000e0400100c1c94008100a20125030a107680680d1102d05103402c035929a9008031840042166401c4403040360460000003c000d076002042c0960640201d804008a40311001c400c0721600c81c6100d6a600b540042c0050303100001c280d41911400c9001514102980442e50b80d11b404030354041d08202c4080b0403017414203011b260f101e42c1c103d6214181c4d000406200e80e254030302520729000c400210440c03811003046145504105d42000629030860b00b403a90b2654143c003410000b41141d4007030400c0d00d90412560050b00e1a0600550200d40314280c05140f81102d1070076080b13142c89005109560315901c5d1030740000180c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 610156942 1250 610155692 610155697
    0x414120c15040302040516230c0d1205100e22050a030c050d080108070302150d060b091002160e09031303030807110a03090902030912070501060509010e130b1902 71
    0x141d201030250750790341c110300c104401c0301d10140441c4064010a1490f05e41c1c01e4025522401c034a040385000e0b80b030080c0301c00f001c1d0828415210000c00310b00820f80307001c10054006032101e08035100440309105641e909001088c904103103204201800050b900490040c03518611540120031440c1038101e12a64981c4542c0d20b01406260100d0004148443c410103010050003210008809450f008005516101f0000d903a408540000b0384a422482548072410003004100c5280c03178400e404c103001d40740c3e48440620309604500350040c081c0c1450301041c04910710120b142c0b125040440d43c601e98060804800d08078200c4020038421040c4030402400011041c0f07100c1d04801544039039590202880c02d0403005081b040d070f00000403904da04c050b22400000782c00c46a0b503006d641d00e240005880b0741c0e490344d2992526040c00021028410001103403024041c040d001b01064800940744040189d07620101c2d081404411500d504a07404091020f90008403410045a000032040c600440c12030340b82500c46040307a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 610158192 1250 610156942 610156969
    0x1401060b2701050f031902090d0303050105010906030608120c0304050303030109090213050106080412260627012903150a150e0103230f18030414120c 66
    0x4004048424901c0e02100111002003002032a2090401a0320f9580b08000d000141000e0401c1c041c03048045412845c55068031042000180f11014001481c00d002d0000c06007809601e0005921160110303145000c2d0040c94100c505c55002001f50100ca4802c4011581101d4200159400304002c0000e40d9503040000d580030340021400081c54050700e104000e221100c1c00d5000d1011410100100300d40740d0003d1400740d016401550306800e0190918085071507001312143c1c0c4030803401c8a410001c032440144c4010b442958160b6042800b440d903a0350031032402d240c1030024204600030760018410045451421080f82003111050100105500403e60032604211181e072885c05041d40310f00f1032484c00c07013078260060101d081009800110003000034090300039081d542d810b15071683e000c1f550309040c0c92614820403c04140941140c01d2909180d451840151520b900b491140b404090607010040204c80495200c00e92071111441c03000240541130190030100803060050f4801d01c9150307251041d040d01030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 610159442 1250 610158192 610158217
    0xc01030522080d0b011404050607020109030c06172401050a03090b0a0902180f0114120d0507030908060c031b1b030408150c0d27050105100e04020a031401060b 70
    0x1c40743c216a07084100d0f629040c0282c10410b0b0480400c101d66a00000c55080c0c52080d110250349840317500041c1c843c8001741e40014210002800009041ea9100b00c0103900540b2040400307034191035241c2c0c000440152102d444500383c000800110b0a0340c000d200400010249050100341d480b9039850f804900d4804692040c030058a0f07046030411417070864440c06401545003d62595800c00000c0411034040500030f10307100c0050900201419176405288004144025080702e01501e10f400004210707404c420002c40200f09030090208102c3d001060952042409242e16421035940307509180410030203c584008509041041c81912000c1c2c0600b2509442e6803001540d5a600d0149603a1074075031682005544084100184212201c412044550150481401180c555000d510348d08252043d040c543c000c4c02c2858442004014064000501c0390f41c2d40c1d40c1040c24560764899480e1b021008a90080d44030070040d40c103200282d080000e0440130b000c0040000349881d241c0651441c1940008412001c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 610160692 1250 610159442 610159447
    0xe0117070e0f091603020f070b010f05090108060c090d0c08190215120103020f030f0a1a0a02090102033c070b01080304051f0315090e0c120c0103052208 67
    0x101d504050941d80001034007034031250b0251410514504403d99400300240800d84c0000c2d14049070480641a281043d03000206040656580c640b00842106284103d60180d11a140001400340300455100e11600c40e0304440c40c03812241000700300072600081c4007201c0307a015074100462010010003c2646c940a4004441d901e00c4140c01041007580d0822403080035190104000640420303000c0d00241140c1e03050320800c011502160009003400d00b03010031000d07944134200e140c80501003496516191224010132407186500d03032070a40010383c403c0d0024203015074000c02c001c06000311007420500c0300701c0304400581c07036620098100381c403040c00d8900e1022024102040784c00512001d11076480c010644040250320300352400010a4a1076500020801c14001400b00100d4044c0250088903004800c203c580ea078044d1101d840000034548000310030541c0c03050b0f03100304409060074080119007901d00d00003800700400050044025010091519110141060414401214810b0700704c100c684900111034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 610161942 1250 610160692 610160717
    0x60b120619050a27051003031106010312110f0d03020c06010905091e0f03030406020d0b010f09210206070b091b0603040605060103020c070e151e010e011707 69
    0x104240001081d03490a030400c1504202076a5032182d0342c0c1c11152032a8003c0d25105004a0001c0c6400d402d182041c03040342004200305201d0341280c1c2c500242d07403007904c400d0300a4609160b40303a40c40c0424000200360030522501102094022080c007061940706004940704603070b000481e64140200200c5060200b600410031352401101845498090076101c1c81c1000503103042c0894980e100c450060440850520340501d00440600b4803041103100102d0085079a2801c0900d0444029030050803020310b0241340c1040120f4562140c0c19605501585959190f80e0604200ca81c0c240c620301051048601b2400300c0d0200c0c0141c44200c09004040e0054802c44000d1a1454810f81030090500407107803620701408072084c02d65210030517030340c0080e0891400541a82c0b9440103900a00c1029030391003861107801c20004044180750b17001849600030034210740b8102d10302401d001c04404a01e1038100d8001e8030454484255100e6a42d1904a0708140340a424040301042c4020a00340c082d251100021410000760 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 610163192 1250 610161942 610161949
    0x90102190228200a0909260c06011a0c10060e071b0b0703090f120306090b0d06091a090106090c0e10230a0215070309030c060b04060b1206 61
    0x110403200c0d201c00400c1e1900065a8400c8201c3c10406980e403102d15107a141103954445840b00d402500a6140412118403039083c00d04c0040680c070343e8004401106200c14a0b140320741020307201444142801009583d082c200804070170190340348014074000080c8180c0b601d060041000c2480d16440c41e1002644505005281c501001c2c01441c40051150103541c4442d00e10b4261501103026401c103903146500e45074150304a01908444502900142c40c1000c0c210034070050482c0c4040a40550b2400c21010780d450251609640c40803a00c1c941c40140400307818089950ba80114801c00d10408114a004541c0c2490081001d02034a0441c40360390364007014400c1c1c0243d40b054004031800d81c1000820301000c180010750741c00c07010f5091b01c2002104100b68900c110002c4061069141c40800182c03a003541d5500296100d050488220710404002e000c240510700074450505240c0e095a10084000901d032622000340c0006001650000d503038900001c1c24610b5640500594540025106003d00313004040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 610164442 1250 610163192 610163233
    0x13c030b030c03010209030712060f020a0203132301140d020c0307110a0b0d02280c0204150312050a0926010f050f06010c0503130e10080304030314030901021902 71
    0x5074044c1c0e1040181e28440d58000036014122a8241841074140380c0616040c00039080880b0740c00581d0340007107511020746c1c0d00031000d080c03403c2010030781c14041b41e940c5c40318020f5124110b5107030140d02c80d40d54600c1140e520588a8561007918021080d2404484541c0380c0200d03070005a00d8a81e50300085100070170050b0000ba1907003444400c41e40c0100c11424188529454403445445410040d80041c01e0204a030000403507070b14001071083e86400300e46862001402c47d03c089002207101d14076000220409203410598202965008000c89a106416032019101c0b548600000323404d012a0403070000344881c145031809144c402d00304ca60300c00348082c02411401e49030040d0150207024101400c00c1101d840c80c102ea41d40c41082440c04603445e441604005045110301d04080c01101c0c55850003013140701c01c80f283e0760b0040300000702c0e9041c840d503160180c980300e020318000200054021081440382041c807001440c2c0082c410b034001840c244000b100c040c00007400781440d01c05038011004000c103a0b40384208 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 610165692 1250 610164442 610164463
    0x1505030f070908061305160320060301141009080708100e0d0c1b1a040e09120415050c01092003010606090b0f19030920013c030b03 58
    0x8022042c14144070f111521040004c00c00301840390b00210000c24084c0400c00c20300c1e0752040700340d0307003207001e0f05d9040030ba4080a00381100c1050300004000c030b0146040610449040f69441d00035107002c00b0303e500c20014480360302c0c1c2c40f03202000ba00b01c101143e540c0042c0022001401520020076080215641302000c1d030b6a42c0440020303a81042e01041051904128404150343c0c4c45140078803100b5003184400d807008030940041403110041051980c0d81100c000c010026200d05a050340b030303c0e03680c0166043c1c0d0707004885d6000312110014081002072454044910200320b0305c44c10441d04203210014850300b101d903441c1c4241e81d10002050718204e55400c403480c00d1010041a40280102410040041d0004c41a44036072240101c0008800c2c4141c0c0280c03064600407150000601da100c2c0b04908001c0185c0313072000d0b040c2d070b00b0800400070040c003008441e05010107560603112031000b000a04110004a14400742d4080700c0200d1040e070403d800c0c03e544610b03600c449240c5000503580e00c0300e000d0514000c25400d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 610166942 1250 610165692 610165697
    0x1090c0e040c0503040311030c0706020a05070f03031407030905060f0d200403140109020432040209011203021006120b09030c07120602040503120d0b0315130602041505030f07 77
    0xb400030302015800801c40c0c2d4820b4040c20107580d0415071a00da1407640c841c0c4284500fa6028605c00070515179030200b0325010542c091000c558a003900c0708010181c200c4a40b1000740419141c0c460b41e96001c0d0340a001d4204a402400c090b12416030b6640402d42d194003414120020301c2c00014030b0300010080c0d00c12a4104403402907201c004c441000031190b22407150313010281c8250481240e00c0b10160702500502c0c0c0300d0f40c1c00790040c0110b0508801500c1e60042041e20f4510171240e03a00214081c104031100c00b48107a030001c02800240c0d2801250807103480d041e0800303a04501807403c0c1f68411011a02800c030080c6036046809902e4159410040710450001d0321981e95504104480154030500050200075103403103041c01da040100600d8080000c0c0710319071010f40c040c01389140d07050000c001c0002a20802c51149000c4c01008448820140c50300c0180513200e54641010005c202d8080d0701406000c40745200301d600501c0e10b0703199400c0425503c8220030b0707840098000400c2108482150143c0c6821030182d0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 610168192 1250 610166942 610166951
    0x1b03031e07020901030f055b15080607020a0204110909100501090b07020901060e010c05071e091812030f0e010209120a030905011404091401140d021503091501090c0e04 74
    0x80b040c240148984050580340c100b014840c88042c925003940660743d005a0742c042c01c07031450a9125070001e02582400701c0c6649c01a1341001a52100204003a4815190381c1c0c041e00d220b414940c20840100904400d28408100a00c04402151180300001d8001c940c0b0107102c0d61034a141c40001841d8400130340002c40c1030082030140b0300c0140c650704540d505607441e90030094040780700c2c071004941c0c0e413141420240040c818424005440914000300844014000b04c9495050b61114120310503604140c503914110303c0101030314004100851003100d6110850700e0003051010035014034905135580507441d070713440781d41c0054400c11903d040d40b203c03408a0a142e02500c100c100c541c4010700b83e10910310031b080c144030382800600354650750142200d01800d5210020081c1032401880d0000b89502401a26541031a0f502d000390b441c03600203c2511200da001b041260394031010210320040c1e420241c1001082d22a07502001840c0c1501850640070306000a00040c441c032401030010888109121142e0103940381 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 610169442 1250 610168192 610168243
    0x50405100e040f1a040c020c060f07020a0614030403080703060504090602040509130503071707060f1e02042919080a050f0606040306050712060b0a021b03031e07020901030f05 77
    0x4020369049951308407800a40013500313020603030804030352030304850f40003000180501d220083c2c40e0191084c0f41c0240c81144104d5240c1800b6512000d03e04031380d0b840b80d5400e00c001800248901d103103940c480a00d160118040d0703940d070041000c2d41d010000c02c50707509030041000e10141c00c0002c60150b014450038007040403c25540c407040d07205e100740c03000038148030648030b000031b19084900c0403182199440341c400c0000c0303280300c1c0d881c0c8003d002d0400a01da5203003040b5040440e07d28203009540c00c6d1000007080021144403050f290215900c8008824041e910612200e46010020200c810612015494001a616080203610f085900c002e05003202e071075081c02846281c2d01c031141a101a03a5200c480021507448146081e220603205030b1400010034103290f40801c7e0480e6140c081c24020627107030210390007142a00c10081004c046900f225400d640184511141d80840c002544030340c20701c0e100c0700d61502c100f48d001b01310250000d81090740c0340482c06245000b0070070f04114010490885030108542c5060 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 610170692 1250 610169442 610169471
    0xd11030705070206070c0302060313050f0c10030b0a18150609060504030215070b0c040801180f0f14030d150803031b0306030111070f021014040b0a050405100e040f 72
    0x10b0500d010f401a640440c40c1c000b00408400136001864005098079282d14061188580380141c0324003c03991405030078080c040c0c61000113004e1480c0140200300492100805108034020641c1c511546e41c4049100d40000740d100000502c542e06448a00d80807a40790b075105154201c0503000d038800007c00c184044200405540001502d044c1c950484148115031407010070620b050044160242c030515842050010310a0500c00034012101e110f00240410400f020103048500207180002d841083d016514000023099a0500c2040b248554504200c101d81221740500d15003141400380c98a95682010512006400400b00010f184001c0118a142b800041d665825000030051112640c40440401d405540c00e400c8480c6a585050226844010f10300b42443c20780d09150040e4000c44103254100c0516201c0d6149031007549904024074641498240c40100c0c2d40d004100c81c800b0448280008205030762848414410340c415651000c41c0d0600400408c01240e0310306100c581139a2424108004422 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 610171942 1250 610170692 610170697
    0x2401140d0b010809150712060b0d05010905070e0a090c11070f050f100f03090507170304050f0321030c13120c0902091e06161401051b09040c02210d11030705 69
    0x1c07045c90074040b82c4009080c07c901414298100d2403418502040328101c80a0b254880b030b040321741d0f03d581170119441d51101628004800c402c801d0308140000010b001410040e00310f800141e4040c0381001011410b000c81500f810344a0308a4010381c070300b40c602042285407117400d8a42082007195014840c02c030a050207010707031058a1000341813544684501050002c1849408028070818540502d807001d03080c4c19030b4480e88503000f0300d4031a800c02500d968660800062641950104890005640c0c9000c0e14686e4a508014a10031147c0c3c02000b054034034031440103620009004034054601c41143e03519019801101c2030304251907003481800707001e505685045040807035400d40900c003404800b101007c01d41c10321500e0a40203001481c08555020400b2144e0710001c618403500c005c0110b0f40716022150890104d01c03000b0340118400340f0891005280c5640403030003991981c0101c3d56121121540c1402c0801600045464420046843e00c1036880c80d002d00c11030140515005d42c80d51030811006009030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 610173192 1250 610171942 610171951
    0x50a0b07050a122004180e120a050d2909070314061513080a120e0d03120e010c050310050306010e011a0c0604051f02032401140d0b01080915 62
    0x641c41303038034003900905442108610003001c000d14940d600d44595075080307810101500082d025180502042c1a0380d000700700f00301c10714100c4841c0c0e0301c0d00d900341e44115a41d80004142c0000e0700d40e14000d10103140c12180011845007551284001036041f0389003004900e0f50000e040c40d0501d17092441121081d414405c1340b69002d50304a8840c04491103480382c6841e140103d01003200344040f012004908024002050700a040c03040000c12a6184081c81c100c82c20071000000c16042140ba59180c03000074003c04c8103103e00e0b00c00200000c0d141100030310301420b4614070501342000c103000005001540752113401e40c3c1c0c05058250010056035241c001c0200c154007051246a0001c2e1816402204101001003203803e00380d03240d0b007143c40d075041c02c0c20015140d0755041c917402030711004040100a0341160780280ca1040c0350400c0d510344440c40c4400c049a90b01204607805040190100d54155002d013140054204100902000104280d40000242c0511005800340c90594806007501b41184a51008030780e11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 610174442 1250 610173192 610173227
    0x10150c12110705061c0f1406011d0f0d120c0312020708040e0606280810061b020307090c03060504061202090703091106040e070306150219050c060304050a0b07050a 72
    0x2d8204a00d942e001102d0101002c028443c01c0001b8612103e110b60000801c502d040d1002e00c2d02c135143c40005491800011103054120020b02643c05007601d89640d051050580160011082071310b26544d200c01440312042e00030110380c000a40c40181a40310702c2c3c45c01402443d240c00c6242c000030351504046800b0314407410403405181c0b8002021600e619003075a01c4220000c20b00c242d40380b04802803c03030010012840a00158020000414445160b01c1030000c442c0039440f200140600da501f84d400130030380924203903051310076114001140b50345032107400c20200c285e0b40e00107041820401080250380c1260700c4108004031441e01d500160b91515245a04080c81e82400250000945400002402881074159108101260000d000511a0a440d01c51040e40e5020030040c0c2d22081c441c07402289081c00307000164002c2da903600081c4c11000e9614152400741d0201e5401414803070008426920444040750745400040c00b140030440d80c8154560012442d003005810003038045002030828041d40e4031340c00c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 610175692 1250 610174442 610174447
    0x5010611120715020a0507050d0206010e1603140703090519030f080a140f06030d0903051c0504080a2102030403020f04020d020706090308070207140a0e10150c1211070506 75
    0x204081040e10070320710030303c2000a40d04c4180400d0b0280094020340c0040e681400340c0240a00468804201b0301d0580f54820540c418075114410700d410b5060382d00003850141075880c0020903c2202140070284600305a55010549642e40d01c6c0c8941040700c490710a42017080c80c26903e40c00a81c001ba50102001c400d460008101c0c1d540000307010140c40c40f000000c80c4442c000084c0302c40b511075a8081442107600303900300c030b40c0c04044040c1103499070040e100c05412078202120561140392004090141c0070320518119040a8844030581c1c10612880d004039854040c107019110300d2591106070444603a2980090f40c14240340d900486c00520002000a100315400286104064013aa041d02d860642000e4108070209040c0b50182410f5015101840584030384000014100e05d40c80303002c034400d000500111440d524040c40700d84020350141107482c000c403070510042800c5010052000c12003400e81c2c4c500c004a1414100001182c0c0440040801c0181d28a40054034480014140f41203c1c01640e0031503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 610176942 1250 610175692 610175707
    0x10e01060f02150420060a1d0111060925061b0317100810020a0e1912080d060902070f0f0203030d1401030b01060c020901060c08040b0c01020a030501061112 69
    0xa081808181c0c4aa001140c0f220604c0203115004074084610340c1ca1300c401c481400c51080800501e030040600c041e00056401c6881c0607002410b12800c0c8a00e001810118003110100c1081130030680c0445602030300c0c0e4400070b0718071480d0303032038204482884058a804070b01042c1001070044c048405910a05402444100c10404051041a107094221f8403000f42c01201c0c18070700002243c01c3c0f0a481040709920441d205024400018402c4451380d550381e84039086050b142c03109003c1100341480e031441c5a51031b8048005246005180d481e101107200314022a40c880319008164100c0391a41c101d400c94510500c00d0000007102100d040a900350001c0c0500221240c9100203440d500c6002400f050f400c1c1803210210740d40f1240404681079900c14201c00840d83e0300c541d821070f160a01d501c00a940b14038000010440c582c02a140c401180703010314401883c2030b4488204400da64400c50f12001a41c0d4000f91030000958948207003405000c0710300d40001c40d4111041040c1c1d0f168229130744024000d2000503100b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 610178192 1250 610176942 610176947
    0xb031606140a050f0412020f03010513060902030a050a0506071d010e0d06060519091b14030907030f080309250b090402090406060e09130203030406050703030f0e1e0105010e01060f 79
    0x1541c0355201c4e004510341d02d94a8600d41c00310400b4000e4220701070302949900c3c040c20700d41800b603d4407540c1c078040b000c60f100605840722405011600c0c020703030b014001c1c940c1d020081501400509400c6003d080202600d081c0000010840c03204c91081c0c1d031848170301840b40d082d0b40c2c0c0d01044911100c0c0049401c00101002c9003002001030035203903c4958015256003028840c61008800c500c21180b031060200422000c1c8503844548411401c0302c00e00080740b03403403104e40707d103a524040c0d50410000d07005c41d1807107602c83d901d400309850f00b05803d031800301d00802000b040c12385c2084035541d00301051805250480100181c0480000c05002d103040c01c4901017200c50841d1100e42c15504c40d00401482440519520311000c2c1400c039a52500c107020740e0b030700c41c00101c5030711564448000242c0d001c2c00031442d040c0b401408444130b4101d00c00c100c00305620751030342408100080c003d11107924503840251902c00e034643c6162080e01c154a261170300310f0f41820010460040d1000b241070456145040c40e00c4e411039905001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 610179442 1250 610178192 610178197
    0x12031209060105040606050f16030c0f030314010b0918090a02030303010f030b060303032a070614072307020f0a0503030d05330d11040e010b031606140a05 68
    0x85252006a41040044000000540d039040343e030140c0301005803640703d8a003111184902c54040401f007030304110000d01244070001822010b80246800342e40c09020b613075401c03080d810105003900000e84424018821079003031003183d4010301c01c94409901d465a0f420205103515a90010006000c141d00001420040148000300c00c0c550b006050300c0d40c0f903841d12a240b20841c0385000c250740e03064141c40041c0c51070900008a0340140880801c4101c0715050a000c204802454842c0780d41c0c41c081031028034001000d41c01003801140c040e00c1c40100a1a00c2c6034018200c1c02c814206422014403450031401007681c00086811154040d21a2000c2a12840200b46080758561006030035100018a045201301e03d41d0105000c0c3c06c190309510055584000329501d060b0003000c48980b103581403440b040b41c03480c2030000e040e006841100b00c00351384001040010304803416604104001d945400d00044a0300d000d1003594100d80f121400004154100030004010090350b6016600035140041c1801b16180a64107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 610180692 1250 610179442 610179457
    0x90102190203010209223b1002070f05151524070507060f08390f070303060e04051c0c150b01110f0d0509010e04020408011512030e1203 60
    0x81c6003070380f0000325200c030224441b0380501c01209240003d00030343d00d41210100300d500c01c3c4a80003002101760b1921100540d0100d090205c01c180700301c0240e135614030b585001500809009503034490000342c42d8200281842004411185072a8140302003004414090710100c0709094143c4100c0c0c0c00300c14115600740c0740f64103030504502410010440d030f0308101001034000290381c803d030f48114464120180a07a2149000c0c0e86142ea2449085142420210b5405c041e1107412030351030380d050300305031462410b52940e448650580d007400d40c0021404145601030140708000c10285040b11b0980c5060745030b00340c440d8036420186040b02d6412800200792403007105501103190300414001c0364200b19000b854000c0a00e442c00b81d000c2004822040c2c501000840d40c0ca900424500160095030a868421103d40d480190b09a0612803034060322030440d02c50344094000391a0318000001c0f241c0d15400c000d9100c050aa021508205c074010078000025440401d10086401c240c44500043d603150b440d09042d80190300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 610181942 1250 610180692 610180699
    0xb0903010216060204080f030301030209040204050a241a030c0412020a090608150c0c0d300527030406300b090a09020a030b04050a15090606060302090102190203010209 74
    0x70b0031400b40b03c0240e0050007200d240200326024400b54441c003540324002480060750101c0300c400014050300303080e044140c0c448124400043c40091010402d0070b00c001022183d0120310070814280035840303149a4001010100c0440181546002c014050b070602c40c9000350001000351144000441d2510502400980b030050002e0080f0790301c8020030b654403030000010100c001292400701e40030143c0c41d4115440090b03108060203141d03500f6903043c0c500329400081460035417035060de00c40700a45a100e614400c1c003412000454030f400c001d05c6c0c00121800d46155107191180c26012803811850001c229004c0b910300b41000d003203100c0c460544a030314440d034845515002c04189544d07c914480e503417007030144600480c1c00c1009901d42d19010403c40700a020025000340581e00140041010210180d501911500848804607100c0e6200b202820945418080785502c400c04402000340a00a5001800301c0c0d1404600b0141d8060000350f8898110030110122220b1525079825503c0a404441010340c014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 610183192 1250 610181942 610181977
    0x50304150e060d020d0510030206070b060609040c1709060c030a050a0f180c0b130e0604090c06020d0905151602010309120e01090510090509091518010c020f070b09030102 75
    0x11141400a0750000b4000450681b804001443e4184941f581606483d005441c090800042c0d6861141102d405440f0a610000c14004460706603590b0298102045003603072903e0b410300116180ea41c0c1c800d00582184490742292081040031503020054030752100821802040c15203d40076000c0042610000041001e8100b501c101c50072030b00586242d08191207441001d845940e0751942003418091480402c0d100250441c040040c00081100150021030003800080e4411069803002401000ba500c81409604940b4061906940003203100c0c0050600f601c08041044201000020761722410440990b9102d03551880c60959203c5d61001c40c1e11540820125603d120021010707040302510800140003c5005a0215180c2480b88659842025903100c0d0303840e81d400c00081007400709002740f14891034401e0020714101e04400818841c0610441040801428064418142910801d0401c40250350100c001e14800e0302000032450b08035000d104d0400d40b500c01540019019110301c1d159a1400042c2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 610184442 1250 610183192 610183207
    0xd050306010503100e2e06090b18040501030606061106060609010f020c10211401090c14040e0106031415010f031104080c1903030206040b043905030109050304150e06 73
    0x2280e42820100c0c400d9111b92900103040140c20741507900d81c0c000c0f1000510300000030041d010414000e0610392001141d0f10041c441540049801c17120264802d450740360b221041001010b401c90354100044007640042e2180f03103007800205855105131040b103410000c00d070f00e01e040d03a10f2080c0104405403000603d02012100700520061075102002022030f0b00c41e44403443c160f0101d44920605645c011582800783d0242e280c00d41c03000003045a81c5600040c49036041809007841d00981c003c0c1b0103046010013a18072135041640040444e4002d40340c070b11005030400d0030b0000a68a4503070613604100c091078103440385001c80c0d100310302410301031a00d0621104082070200d0201c82c04141030b0a04e607003d0b110300c800c101a404040c800b000c150f100150142c0c00c0306001c00e004c2048004c50b2a03025000c1c44800c044d0701c10207406500001613803540e0400342c0302c0c0d4100280d06240b80810001c002c0500f18020b00c204e05071138542c15200c1c031491082110031208003442e000c01078069070301680316003c010001c5484111 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 610185692 1250 610184442 610184461
    0x111f0e27070306060f0923030c0604030b04060b0f0904060906022101080c031212130213052401021002070c270e16150c060c18080d050306010503100e 66
    0x1000c2c040d02c008546a5451203810610500c01300041f00d901411701c590703d50a414201c1c0c5406e43c440142501402403042100c0551500b80040004500c6095044107078641814000d017210104000c40344a0450f1020004107a514004c603d600150410000a545c2c150341c80d003000248503000f00315000140c00d1040c843e2003d96840c1244c126192901a1412502420201a03d92804950442140a003400300e43c007800344d0704241c40d80c001038030080c411100c0c010f60006501610720410082c2c0581d140c10410100c50b131450f11000c51414503660300b08940400d00c001030345071400030725400c10499010a40c0303c184246000d4044c010316020500232a41e0f00e4421921000f620000120050681011070724542c1e01b90020350626000180801e80d407001303041c80c50070031500012080c42e800300048400c09401041c3c0f5849103000361941604c450454400e500742d9003140d070740039502c9100c0342d4000b142c4840f83c00d0f40220480741e005400b441c0c690b550b0342c0c4015030911003411f160000704400e8203160030070600b131a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 610186942 1250 610185692 610185701
    0x801060e0a020c06070c0305040305010212150a060e010f030b120309011706030a02060306041d0123060a031b12030f030b0316090507030b040207111f0e270703 70
    0x2104015103011075510303032071000300b42e00c52000c100f05158007600002e101c43c0d100700e0300404c00d42d1107440c111345000d40e00e845150030f80c0c11203550703101d00c2c0c42c010b410700000b903030001d540e640545400c0c2d52100b4a94030b441c5000e01304c0c095001c00581032140c0000d04000c020b109070322070103a00380c001705400349400d182d0b040580d50b40c01c030302c15440c003080c8010b6007950030001043c40240708400081c0188039881056003800590740000d08600d402030345404400740603550380d41081d40540703401c000010301c13000c00143c44583e50b0801d2030540142010750341030202c1a2070f0800701a00b5290080c0c041181001121403c18204015511448000b010802d1071420154049031003010040150f41c140061070015041646a040c0813041d08244510b01e20f0410251946400c01c80c0e12501600700004c003104440b02290680e0b01004d002c8405c0300d0200e81221907440c00c00d180d13000140c10810b5201c03500c1d81c07400000c2c0c2130240138071310310348141c085d8600b500c401d1001e040004002c8210003e03d5484c3d00300710901a0182 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 610188192 1250 610186942 610186949
    0xe1203130618120f081605010510121a070e030d02031c05060f09070915020604050f0708061f0b04030b0a110315190b040e040512031506090406030c080106 68
    0x10340c8002040181d00c810305100b00903104903030101c11640601d652420313050b11000718215034100c414003101d607880590318400404103001d100040340728a094141990640d000c0d80248a00507800a07000ac046100c41b502800c10903c2c400c4102d4803620b9100f0305407500e202040c019a41445856000941c5940c040090704074040320102e02d94031068108080d00c01d0b40e10488449820480c0d2520800341886c000c00d410340c0040d002d06203442015260208140513100b0401c3c69130150340100c09010400c00200090f2607108041405000c0307441c20090111b49a04014005030300501104608801c01c1e000c25100d03a0080618452131941d5591f2458001c0c00803408403203c2d1049441c1c107031960501c8a030141128424441c001a0060100c1801d00308a220000100c480090f410089804a10490b401700148090641c0000f44280c514062800030310300414080600c810210074400e10507001d00d88030041e86131100858205864030810404640240042d90002c1c1a6480600c4000b80441065010f4070a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 610189442 1250 610188192 610188197
    0x1c020105010b04030f060911100903020f06120c03041a01060804140d210e01060803070c1a030711100606050c010b0402120c0702030709021314030d020601060e12031306 74
    0x10380e80c0c2d010296414011480060146001c2c8468038000442c194404121a4452024405040c0c5d050001c111014264a0960082400c2003024002d40c90602c8410107280d9048a903545060700100c40b010b4414400b91060316656000b201103810400444101007100c03828107844e03907041da91804024451102514144c41c1212096111030f59400b000c2982440d1b0705950312503010842a0754110b0f0115000140a4040c02c1d68528801d001e0a00078010329004003662001181c98004c1802d28069196440d44400320030b215455203901d100300d040d416250b0264007420940d04c900c000703803010f5060801000d8050320803882d00c003002c1881500a4043d040e18500d190003001401c603803005010072403144c10001406400500c000500c00f42170300700145202413024007902d110640e11151002640c01c1804170b100d02d175000a4043c08040420140c050f00042d00301c0052001400d000c201035100d080c1809032408000d111040c3c0c40b4107407a4050540342040864086982e1444282103840161900b802a50300 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 610190692 1250 610189442 610189451
    0xa080c1b160e15011407080d02030a110301240e09090a0312110306040b0102071a0301031a01230f030307030908010e1f23151002030c030a0815031c0201 67
    0x18041c01034020b051150b0244403040c00c55007007100c0151451100160300d100000301c1040007100250507100178019100005002680303a00300029810159a412084c2c148290420300c010018074500c200041d41c41202d41c0c1c0d031040401800d80c4100c0c3e41d18000711003e90000d07000c200b803100f07030a00015181801400b03a80c0f59030588208201031401d940c0c142c0f03200d003690300b41400414042d2900da400003a540d00140100c0d80010383c2c80443d0462020080103a2000b203002000420921003480b40500f802c131441400c44d40b596060500503000090001860b28080c5241440082503031103881c0e140c19502d4000742100d489114a11b40140b50f18124040d400265080001503902050009011410224403941c800c1c921404070180c07000800740c004401d0130049030382c10031030b4591804560060091910000e03507100c20940c4c101707214004011100402c01c66000708107140307040c0c4001c41038928100c994541000b02e51603021014481c40448075907141d050150442000072160040340107401c14086070000d00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 610191942 1250 610190692 610190699
    0x30c0e0c070b0a1e0614210a080c01060e0c070302070501080f01060e150c03070606050f0303160606150f02010c020a080f09010309060e0a0506010602191e0f2a08030a080c1b16 77
    0xb901c0e528007c200d4443d6520011810b40000c00301c00250078010248000040c0056680c0c4034444900c41c02d941001d040705002492205050781801210f001e0142030034010514103100e040030300c2d042014445d010400054000300603081d03445200c0204030300f21181e005501c409841a05540ba540a180704440d428070700400003e4a041c480c45042d0f05000c020702640c00e1210170100745600c0d00c078804040701c0305562644003040352008000b0400c92921241e035400c03560234070a40701900b120902d40c0e110b025903100003142e42c000340e5540115000300c20144c0e0300c151100d02c4c0708c0045e40940030681f0000c11460900c01040414200040c041d95403502480c100c40c0e41c0c0c1d0f682c400503030b150b404c4501034941c21440f051000c0080b482c0d91108103a1203240c4000c00d00100d040d40c41c5c0c0601c02d820001c084801060580c4840810b454030050b0b9000403000e54144081d1501d000d00080d81d038410304030b00c9800e000251002420740f08581d07040c0c44078003906e05204001d154100004580f21480c5094a09012a00d8000403 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 610193192 1250 610191942 610191979
    0x30305150904110603040f0b04080702460b030a02070b2805180a03120b0f0105040510030b0d0501150e0f060411040807030c0e0c070b0a1e0614 63
    0x100d0049400480d004040100b0701c080c0151381d07000402c10b41d100d503010140140040c0c4040c08407072086002e0141e482e2509514410451181501004100a4003d44052401a02c0b281c00055141010010720301c8026482040403082683c042d4007010105030040100940020690010f015203885131403002255501d214450900005410320000981c00d1020424010705881e4040b80c0c00c050388803148291506150800d40c40c140e0795003400c0f400520384e0503030101100402d002d800100c4600b1607568a0036281c600c0000c009000741d1042d00e03c05c42201c02441c219501136072001d003964101402c3d0141c00c8849041c40e5018140d1800d030844052800d01000074402e8910786d01c07a00500d058240c820311919107404000c00341c074001500c152603032820000010032003410080d03c402184a01800c0c0328261a04503d04061440186040c0940350100540c00005004020b0f07160300c07007803100b0b0008195984100005080380c41100850050703150036404a41300281080c007660010048500b42607402d13901c0c90345d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 610194442 1250 610193192 610193209
    0x70b0a0203040e04230c010201140105060717160804031a0402090109020c122101080607020a03080702010e031206031b060313030e0a030f02280603020a1b03030515 72
    0x54401a08244018869542c0c00740c0003981141c054071000b0203c0c089002d9000c54603403251484021769000400003601035070280140b03090070820040300000d561508000c68098464120700901d4000c1c0c01c0b03014943c2c0c0758030b64281c070b11440c50728041007d204024544448141d00600064038021100c01040c0003100e003105c0700c180300c1c99002c0c200ca0603a134648602c05020b504400a40c0322580588440b103055079074550301401f012400c0400780302c048260322290141c12001a00000400d8000030704100c645a00002c50f40072250b810f03d843d0103265a11b1804034010490700c901c44c125800009000940361003024880c0740520b0084054510741a07411094180804008540c580c008109200044a2400d03100540609030300a0800c0c041c0b00c0072686c0080d80040c80c0350022078144502100040960800603800d682a06d4002841301c5c0700311541800340824405441190205600046d403040c0301031080c9180321210483e038080c2d1040240e18a4080d004c0c2c40211980f03c02400d800d07105142ca49024004c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 610195692 1250 610194442 610194457
    0x60708010e0f010f1205150c0d1808091c1e0308060d050718062c01050d03051207200606130c050418110a02060702061003030e0f01030f020d0608070b 66
    0xc061a19140c45e441e04081c1e16141c1045e2464001c69400821500a0041c09449002c10303040f410354558083d403d60040303902004201c08903030503143c0044002048002201c400050803904050341c923071010700c0c0407200700b60160010038612078242294071070400d108003021a1446a116040b581e6245014001e4807980d451000d091a40489020008046003038160448803000c408085141a02c440342c0b59203104050640b24448507880c440440711201036200c80c1c0c0501000c40301b13501016110f403001481c6001c0c01c000c0d034200200341004100e52901445c0c450b0740b004800f01b100c80007506004400e0781c407410111541409030110801c504d0110301e480c85289100102619030504290400c000f900354030b01800704a2203055944c0c1c07503040303a0303502901c0036003d510115030007441d00b450941c0c0024104600071701080a51800e5010034000681c001140c0060b68a050b59200501c224850048001d00015000c640b4160b03c001b6842004401c0c40e084501503840d8070049a4182b41c0c1c40f001c0c91968400c1d0b00 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 610196942 1250 610195692 610195709
    0x216120807140a030905030c072304090305041401091814070e1827060718030c03060e25050102150c0405010c050c0307120201261f08060708010e0f01 66
    0x41140d054041e520000040d4012407c44e424101032200507460b203e282d03042100003110b9080d03407200d0018050010b48810500365820f1010900564000d0400d002c3e80c020720380c98600300c10410080e1713489507107810000d00d1515403c16405200407000e0005100daa031401d24684c040c0000106502d000f0341c0760240d91480600a4180c5d84000310b02880e0040018003100421406010420b80c082c9228548564960304900a0003a0b8182881d001d855100b140340100070000c1d1140e010000b1a0022111720100e80e0800d07408901c840403041501c0c20845070b100d80016040303207405400706041c0b1442484042c1d80b820303002c5440e401c0b01485254040031040b21903e0140e80100010301c00380d44030380000c08429100702c00700c0b481010124002030401840390172a0030740603a0003210000359a4810030700ea00c0c00b07a840220110780c21109140c07080010700100490b0800510010940d406800b10500c0f900400c00b00303050b52043e0500340740040410740d0a01c28415822402e00201c1e00540449400c14101e40c0c581 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 610198192 1250 610196942 610196947
    0xe0d09050303030c0a090807030503031909021f020109200a0e13030e01050c060103083016180f03050f070e1501110f0105100b0702030a080706021612080714 69
    0x318a4035101da0320880c01715040080c040c40015540320200281805584558091604c92a04000c4a01d032102103194801c025030508101c0c40240e2207968850506600c1410070a100500450040e8003410320210010040b01c040c5034000c0c0080708400326020317809000ca1711540816174a868500da000b0080d02d044903250340e12f03180c10000078002c0c0301c035280384031040c1055800c0050314049241800700c00d07403058864450000f45601900d01d5515400c420000210b0800101c1d410710b0301904154500a2244100c807001001d02c1c00307254003e084410100344c2020914680a031911406842003c661108560300c0c4203210507101d04ae84086441c000360345509000b81c4155035692112008503422001441c1840340c6069040011032081c05901070440100c00003155130308004940094402141d0300411642c6e03424840f100050743c010501840385900010910b440e00081c0c1022002441010511031003140d40c0c10701d250802840c040902000341140d2211455aa104a02521a06c03415105500400400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 610199442 1250 610198192 610198201
    0x705181f030b0403080103021809060f0a0f0f15270506010507080703020a03020c12030a030f0b03031215091504090f0203070612110f0f0705010e010c030e0d0905030303 74
    0x6000c8903003862184040c004280341c1d5a844840d0b000100303640660000d001c00c0d006006606050340c690301c2040d40ca40c00780e034544c54411041a1501c070080c020307030089021034000c199868100e40040c5601c1030300100400c803003001128110014050402001c1e4045080c00b0300003007040014240c0c485950030640070042140c00071009000400004008505000061000c040030410600140c503c00d8480e40050140002d2401c01038645611101d9031841030110b02c40040344404044261030402d40c907400c010882c1d404412644000e84412001142c161101084261401c02420300302805501403110011111221070203201d40800c0864490005101d900d0200341c060130300c1e500091085004603402010861654002030500c2202c0c0e00640000b14000c07107220850000d403140458061810051529181314072150140c1d900840040000d500b40114004c42445003e402c43d41030b41d803a041c002c1080310821100680240700c44509880c0c03511070340d400d02c04114050500801645c400400840c1960344 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 610200692 1250 610199442 610199461
    0x807090209060f0a050d1b11010c050412030207350a030c0b0a15060905030d020303090a0209040312111e03060a03061109030a122d031d1b03070518 65
    0x14410904c2089002c000c6140c500c501c51041c200d080c0e2124408000e030000d00d55004004411140041a16900d09901c00325540c1d0414115803c85007101002034044401e41403d90400c3d0081d40300c4240001e0160740d80c08580c0c0c15400150020043e00c44102a10b40c2004020342e1300c2c01805c000a01003201ca034a00300210341400c002583c001d04030040801c400f1003000b032075000008039600c60008580082c005000034134040c4441c180c5072015100071811841c01d5084039a454400d00c1002e40a08400800b040c1898842c081400600350030354001c1c000c1d44034039011289542e01c8000d54155641200741c0c41c4c0000d40e0004122405403038001c0c60f09200340d04588510700244058684901c0e219010084035406440034840003141500034140303e246101c0303000000c0c2030202e0428400f50300c1e606401007c464407220100402c00a0441c3c5000103d8006000040700e542445000c2c0040c1031054090200c1d1290b500e0309110507889095042e65140d0750b40b031046c49070085d41c0d80710490000d615940020300000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 610201942 1250 610200692 610200697
    0xf132010180b090a050409142a090408070506010f1505030c0a2a1b090b090415060504090b0402040f0e03041217130f080c060714010e030309070807090209060f 70
    0x384002c0130025507994030f20010741102c1140700101da4524500d0309040805209001d503280c0000008240701e40040a070f05035840c0000201c500e1071045040b01c02050034070030418203031540c1d03a038840f00b01c95071075031200c0344240041901d101d00c21115409000b6800c00505c06c8040d41c0c040d10b0719211a5007085d5035400150385500028000504071068445102d10000e200c18180100a01030344000c41140340200314004596020b4100000d00c0d07003800155021521001d04080e4802d070004415014829550004406003000b907000d6507200e800c1032862803d0280b0071004034025407003240c2c104801c40700c03005040c06503544602000791941051100704801002d1460003034603e88908810f4071241882d07500d010071754011844040f2059180740040c84a5161801c1a101030805070340245042003403c000981c0c58440c1c410001e0501c1031782d4420740e0500c0c2003500080c0d2503000341420380791640b5002074a66650900d80c400c15049108011000900704181c2c821900e55070000351000340f601000e2072560b0502c0d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 610203192 1250 610201942 610201957
    0x4030806010c0602210603070f0510110615031006030b1902070602030c0a020d0504150e030f0703060506010e01110a03110709020a050414040209090f132010180b 71
    0x100184000003003c0303100410284041c0b0100701003407040820301079500c1400404560091388100070a10941c0c9210304640102c030021500c070141120038880407288106c5400c0d6203000741c8502414031030151034075489019850001c0d0212010404c1c000a140b094900d1381c07201402c5207a080c0c1c081260600e45200c003821101145c90007500d0140c00707640d140c0899000311a0840200ca0100302802002d6051100c401d400d4450f19025003030038201500010b07805514408041845000440c40050f61400e00149403021621800e03202d41c03507503908140c00900800c540b003a00140744207081d040e01c0d43c001e03071100d01052001c40042c510030324191f80543d500c0c02c0180d601c0c8100d11500e44001458500c1d40010002c00040d0742c0e5590700e640c40c100c61690f031b10b00c0d48044140f0850040c40781d140036440311901d16901c149070a51107042a10340c001c00c103503100c1809802514200381c1c800074481c2c1030860301045842200079221410700041c109001c803041407400201d60b400041c0080c0c1049540580c80160404 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 610204442 1250 610203192 610203197
    0x302090a06080a0b061306020618060c03040c051207050906030118060b06090a030302070302010801090e0a0318081e0c040e0a080d0b131401080714010809010b060301030804210b0403080601 83
    0x32044c0d031000075507603402c510040c441500b6503d006000080d8144039242e004034501b0403103056907404909031619564000d00707501e40d074000400003806001680700728000601d0702a114401c44a0b1070003050392200c0c0c05010703060050200304081469401d05120300f03076131a0410030b000c2d07031001019511400030f015440b44081d80180c0070f0020703c0090391032000d000001c601c40e0b0010601285144005400418140d002402e11868030301100c2d48024045503841600345c0c103140100550007220b0040b1000032094100c10300c0b521400c8019950450303000c000000c85017443c1d00b1616104000401c00080e603130b07080800c075410380200a001e40001d0b095000b03004000c000d00c1001c07a615040300013161141c0c2140300085511074950300140d07030142d0f07080313200c0b0b015060a80142000509200d007408000c006c0d0f8103881e040128400004485010230341c448007000c0e000030060b550307030750f50ba00b031075961900240504195551801c0d10380c0150310700a0b64403c030f407640c800c7c4001d5035681c0b640c400381e425034030040c4003905 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 610205692 1250 610204442 610204451
    0xf05060f2d040f1211010c05090a0b0304030908060c0a031a0a18020408030d02211006050a0908010501030f05120a0e090a0207020d0b1807030206190203041502030711010302090a06080a 81
    0x5000841d80c104049107176541d0340302c03210b045410142912841c0e10051b0a000e0100400c04568441d84000d4059815800d2171551f03a0311039107000c40d0304042a6024220f80e02501c014410450600340041032041c11681e0280800e0500d07481d501580c00e92800307000da012110600c200144d80702d0a080c2c40202d00d1f0642c006003016504d0250750b0641c5e00c191259a4480d9000950010509458024000301d500402102e4020311303003049604245d400780e009032014071402140400c0d60300d03c1000c082015004140081c4000d51707592030030107030807008400d0494040c041c0d507840c10312035035002d0f0503541380740502e50301d024408107034005002c003821015140d840c04a408010010150300d6031500c1100180c4102410300a0b4174009a110100f480c2e58901340c1119040803800300050fa54002c142d03a020200d044c006d00d00041100002d07450751285501420110028200c0c0a50194010000d0f010a600038858100d2002e01213004604a1140e06800d56002c1c0c91400141b040394421210181c1c0000500030024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 610206942 1250 610205692 610205723
    0xf231315060311070210030e010222060207060215010b0a050c1b0f03010204050114032d150a0302030307240e0303090c100c140a0f05060f2d04 63
    0x10192000403400d010006003260040100799414459040011904020740d828000140c0c0020a0526032203407003003c054960600308c514030001c0d8101d4845154841440d0440d100901e100428140a031068070302500a42c2c3c0009003c2d800400c50711601130300c6c4242e0f24402c1e070800c0c189000e0382c1c0090080008003c81801403c2c05440c0c100a2111690469400480d0680f02841005594201e0918080c0282d0041c042040aa60400c400002140d0040500f50301c9a4410404280510101e03c140c08024004094010b401100803150b42c041c1020300d07000720380d41c0300c4601400100c02c11444000c1d09a40108450b402240070380f00c0c1d0391500491aa000603240790568400815a001a5a081040d400000510420a10401c180701295006550f164049100d01001420425900601502c0807903003045041c0c1c0d11031b003800b082c110703036a0008440900d5003083c01e0050352220100c46540036503291602284035808500711045603a0302c801a58528400d81182d083c3e4840005401192188858071035130 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 610208192 1250 610206942 610206979
    0x14070c0f1e080408011b0e060414060c030307350703020310050a06020f0c0a05180a0b06030a06030209060d231009030507120302031b090f030a03030509070f23 70
    0x4100030441300c3c0010407602c0c08482800355103ca0314134900203002d155481c0c83c0454880d030f0151012079102c58940c0051031221030204455200d040b100103418040007082084241d00b00c40c1c0c3e07468580c41c41c0d66030420200100e0482c0d0540003103424a201160b40f4100003640b080c402d400540d03220760605000412281d40d40c0c04201c904900303800c1100544c00500c4480d40d001e00402c54114480c00c00ca5280f2034152030600400c0f0f141c645500004210810307000014502c2419800c8451014405440c0c1d564030718111031028014092030004034820709001d0003040103031038022002001b0b1500329466504c1504e980c103164100d03c5113440c041c8100d00481201540090b00c61040b00c000c00d00a8036029600c20840c58030141102400a4060605105006001038540c5941d0f440c00a010407010311903551701a800041e004242001025a01d842104401e06c1019403580181d4068a0143c04a031421500e461030b0310720061040c0174030715001c142c04041602c01d04601c2948981203a001c1d02c00490039a804199 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 610209442 1250 610208192 610208197
    0x60b01021e0f1216030507020a15180605030f0f06010e030f0a031103041d130206030a092102250f0b190c08090f0a050409050114070c0f1e08 62
    0x100c000710703000350304521040b4406000380d490412001110910f0688107441520494032082405002c012000c181041152201c50040000d007898041d5041c5160304000c00828192246000c035a005895120005035280506c05076405402583c0d10401d80e0750b100195545a030000070b01081c1001041c00303100020392020722415002c982d003c1c002c0e2001918074207003d05503802c030076010000c50740108420170200212240c014a480384041802003140c81d082c5c15100110120140030394042e6000042c04039050066010808051262640c0c0c02511000c04294000c200d1150002d009070b040000641c03010b0840c140c900e03801d141c0c1c1d01400780d1019110701c8011031840340d03a0070410070894001846240c01d0900e40550341c1070b188510f0200000d12803961919043d0140d440c0060252001c1c000451203a6a0090600c0140001803c20801c1c1c000324204580030304811190007111181c0034001c14401c5202d1035154006903001a2075841002c0030f96184001700e00707403004a0600482c80b08180c1b0004001800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 610210692 1250 610209442 610209493
    0xb07050115060c0b0f15060301090209031b010905040e0106081c03060e13030e0307210b0a060e04020909010f0603030f120e0606040e031909031b05010c060b0102 71
    0x10340700302018041010825140c1001c0103020012224400142004d00200d5008101e517503400d07010703107944080c0710303817841109101a400b240c0880003040c0c60187d64082c04035203804808440798a2081c1008082102c50300f03240c0d0340022900b5505001d1420650000ea03d45100000001102d5580f5001030381404201d20050090000c0c5840046055605005002c0903141d01400c11941d07041c000d80b111105008261b004050042041040e48aa54107002d405d0041c080d007130000d007107030000c02082c2c4141000e10b50112007140ca188003151105449129203000d07504017888075000d580b903503020400d04820042c6800019034845e8040b5007120094050301e4010740c4a602c4001a1304000701d005440000a03020094a00c0e14240b450074201c20300040c0c0c240c000030f00740c40000b030a040040b030540c1580704025201140101541003030041e154007841580850740611100c04c80408041c07401262801700340b14880c00200000c074808080307526a030200412443c14012180903219900d0700e000340402102 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 610211942 1250 610210692 610210703
    0x120914010501030b06120f100e0c100f0207090203040f1b03061505010908060906040b1f140108010b0408060408030a14040302010f050702010c020a080f040b0d050a1d0d12060b07 78
    0x82c107110359400c0c8116403090032107058000d401440c4007203080554070088c0314200c9612648440c00300e180001c0621280d50b82e031001030040c0b80080503103240a0f0108140c015844014411281c2c0056100390307070310959006030b500011500e80360407903071981c01003140600d0400020b0746000900200091540c8105045a401d221003604110700d810005810b5400329406050541c214508014034038401140d21944140c3c440c18903031031501e5110800c400c10345419042942100d8403400403030821030f80c1d041e00d58948401da07142c628a81e21a036088080d809103100d600403681c464800300b00000c040801071903100c07415480004480042e90310655010700306880540c00741c3d40d2928400d1140f0198001d03035600c100305000071b01918190240c000d6681004860107041c00c0b0000c07504140d80703d81c003821500108a0110400e0302c0341c8100c2001001130030151502054646051603100c80b0300040081440c41c400a100178241d40d030f00c4842c0a070344200f01d00c0305248156540750707004140a5080c0c405010060f00a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 610213192 1250 610211942 610211963
    0x30a06030302060604050f0f100b0f0c0d050f0301361b09050f1e0a081b1e060702010c3804020f01050d06050d080c01050709050112091401050103 64
    0x604010f4140350010f0042030007903081004020b00400051007558102440c040c19030003641d10001170404c03032a400d4100d00b8191000082d200000c1082d84c020b0050b4a4581c030540304a452140402d84441c46051003a04030180180010800300740c4d20864540c4d0b8500e00342c85401111880c401c02d126900d002c03c0074051070360391a5080301901782c2c20368503a403072482d1b2410300d600c4450804c0001807100d4a482c0300030b4864078812910205c00300134a1a88203102d04080c002c00086a00c504127262107400404100d980ca0980080d0b4018070319110740232142080701d0040c10300d0139001900174844658800503080c0d0501807141c8110b40011a4203580000000608440c45014554400176030850440940b440f06038440c4042484056030f14151044c00030803007400c0c966900c03084142c00d080034005070341c4101d500c140c0b8000c0b4481405507400080001800070b80003003081d0341d40c10b10b05071041c8a1074017039980000e04003c850854161143d105a4115005490641c0d41501c1101c080d800d46002342c00449408894 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 610214442 1250 610213192 610213199
    0x70807050d020c0a0b0a120e060403020615011b1a101a131215060605190503070c02062b0902031212041e0b090c010e0a03020f1014030a06 61
    0x107200041441005102030f180c103010000c0000c0050580c2d01600708006000155030780c10034040c2c20500074440c07400c50144031134034091024030303203031802214240c015028500005440d4510b01c0e4034a46c245c90141c46070309080c0319864556105840020046070100d840c140c00100c8900049100c92043d5002e123014000c50b8105072040c0c040c10200c02c0c00410310482480b040390f4488011107014181e608641c14106040b219042c0890004006480c400031a4070f0500040b51007030780a8020303c00880c40950801c900d161500040710791344011601600050b1156450000515140c1c000744614444022000c00c0424401190f0040b241c0001c1042086a600c1000f0411070070180801d001d2162481c4c5103908244800b81c032106031600c01071008202200c0c0b5500940070702c0c1401c3c107a8000c87d801c414030640d02e2900701c034595691104628074501186410046082d02d2521780c0e90141541d5003c0c001512105c0c104c000d00c0401684080c10790140311f400c44a4107100d00f850005584552444003021404918 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 610215692 1250 610214442 610214453
    0xa0b01030c0b07022d060d0605010e010c080703111e060405120a051219050f04020a0b0306130213051f26040312060e10030b090d0212030417070807 65
    0x1501d0b844124100c1c014030241c000340e6122064140300a40c141d01c40d840320b207501170101a0140500220a50052003c240841c00240076800340069640c02e0f00d60882c41d541c42c1d401941e4802200a004000314010054100000d120300541202095840120381c5011a4000d813180120005c0c40d100030103500400c1040705206042241000c03040c50014414030f40100803100900038864030100389040c40581d40460100d8040c0c980304070000c422120204100e007804150103007440d0048d03070305034410140c0c0312000c600d0101301011640106401403100b070001c8803011100c4081c0d0170506903201d012003c3c120015503510760605007900303100703040c81008902450b2003000d01111240c4a030203c699010100c0320b65100780600c0f501703801a4050411000d07120344030820340058066508440ca03880e05440070303c0350081908012400340c80c0f040039850120382c0d0f03a07040c85669544e07100401c40164054045441d50300504001035811a0107a110041d4141d03c030301c0902004d0303205400c111a0410005410410700c403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 610216942 1250 610215692 610215713
    0x150d0903020717030301030b07020a080304120e01020c030c010c020f0901030305190305070f0c0204091406061314010308090a030b010b250203152e090c090303050d0c050405030a0b0103 81
    0x41d01102d9001d1440f1000850741d40c9010501005205503c46004201110b00802c1403103c00c1d58060f0590b030342c07440d00b0329003441100426060340c0086050340c0f10b0a0819030020030a0048588064000e0401054210046500356030800e81a80c020b03c0011039002213880d01000d0070b020314000e0b00c13803a656001c07000940304080b09014105d810185400c00348910154840e807c25000710080c0b5003061005000c1c00010001c0038043d100038080d071030340c200c0d5414054000c152103204100071200b1100c0c0c20743e000f03000740513100308400d40c41e03044591500600000b40200054013172800013400c0c3c0301c0e2860700ca0380c94050078ae000fa088070080000c08907502c1d003001050600400c1041920356410444003459022a985007070045407946071503007410001c4e200300809823900050380510180e4040700f1041491050880c101802004c141c24180204007545602504090701200c1d07041d660346140c60301318081c1100500180d86824201f0404010016890341c0401042c8a42400349001c0d0b030182d4594509004042c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 610218192 1250 610216942 610216949
    0x7050708070b03090703080703030f1a03060709030c0b0f041505041a0405010c060908130605090909060c0d0902150f09030c040513030c1416060e040524150d09030207 73
    0xd50b08000300314041002003800402c8a5201410319110210340c82c0c02e6024280303002d00039041501d44140c1c00412911605132411000c4103400740d444503200c0e82400c4038141c030640805413540d164044100a4100740b0300082c80358030180403c2c1410035488500883c2079603038541400e00050070105c3c00780110420300d820842e00c905617a45181c9428a0040042e01010001801804075556820481c080c0920141103400d402d800d80c0c3d41604240c0c07183c1014206401203915030340070300504030010704810000140c882c050740944100d40d0a15248520502c05002103000403a0410041525000410452000791451504410600d0f449804030801d03d890540b8101141c0c1c03246003041c090003000040800508030705905850302501140b01ca0404100b02101800506600c0c860100c5c16214009100c3d121000d9850640d030f001e4025950804101c00c0d07520641d41c80c6608205581042c4840100c1c1c91640c416070f2001e09194806503201c52084019001500754600d020384036510b590416a045c88940043d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 610219442 1250 610218192 610218209
    0x60f090c0c030f030507030b10020304090510030f0f1502120105040b0108010303121109030f010c1101050103030219060f1d0c1801140109030b092428060b0705070807 73
    0x241c181c5004010641c44080c15040c540d4900100ea00782d4465000100c60300809014141502d11001c0000e549600c00e1080381c001916000110310b0141080205d41c045a40041d0600c1c114502d544501504203420b100032200b49109200c5000c0e103042d1030000d000484003034540c8404541c94a400c0c071003943c000d10300a0307041222100044c00000d42089441d98441d26651002170b89250040390048544280920545d05200b0080608081d002c1500400c100322225510003640d200c110300c0003800d03181c003808000c1c09030b0084840c2584038030040036000030a9000d00c80100b02c2080d060030500c210360b46c0c000c45a0700008000c0031110141e1040046200c404c3c01924503407624002c0c5c405806040606004001d4010741c81c21383c980303c0340c0c40b4480d05000b941c0c010907408080e061001101d580c98105550344800d072407139a115440002036100895200c3c4074400c40446200100100350401003410480a0005036905d080c04550425181b0151252501c5540180291703801c140c0e1192402e041680007072a03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 610220692 1250 610219442 610219457
    0x83a050d1a100201020c071e03060e0102030703060b04030c050103050601260708010f050303180a0f0b0910030203010305030711150d140114030d1d0607050a02040506030c0a210501060f090c 83
    0xb10384400a070f211f049a034007051448800d00c0c031403640400c000c100d500150419050120750041d5000c1940114050185a2820440503503100702854140c0560300c40944421780702542000300794000d42000e58000014034180d20066003c031004aa24144581c0d02030060030074800f080803944d00602c59501400480c5800f450305454640025600d10a1a074030b00181c0e00802c11200d26034481a02c003802414440c001c2508060315283d050006410124170180f01d012a141d00004090191089034140e0350010059850710000d520b0f03c6030106120080c8039086203c3d8910320b042554403101405008080b440301003440d211103045002458010703008910b10442100781001155000100d040c40c0c2c400703504014007495003034084107c1c07a000c0810800d8000a000a608003044000b0030483c0b821032003150108100d4403603100f8141c0e6085144e50094010300150024001144002c0003000c0310b00d8954510b102d81515565800e0a540c07840d84000c110b84c440010500004419010b10301c1c04070f985140144 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 610221942 1250 610220692 610220707
    0x301080a12052d040b0a1107090218010503061504060c03030b030f190302150a0c03140f0a20130609240305131704083a050d1a10020102 60
    0x30540018015610344107800421101181d461440c107940c01401d174000c090741c07201c1c1d1a902c0a0700c40c0b00400040049030281410205080c840380c400c0d41d0288013840e003001d02c00700f84080151807d41c80540b582e540001d404840b64075410740c40004101130b00e420740d200707075104000d85000b6059804105031a407003900000c6c0240c0308040c1c0011a120070030b00310141c803d0401c1c62030a00fa800d03c1c4c1700024403402da100300802c0005c02c080f03a0700000c4280d43c81ea0780401c62029419a0388900c01c209407500603a00602e40003244950480341c00035010070f40c0d40c0503d00c054110740140c0604580c41804010045a001c000410003281c01000c1003000700007485590700b1880c3c241c012000072010a01c40c2d001810365034004940c010921782881c14200c2d9010200500c407004448580c5502c2e08988207040d4644103881000791340c061850b4000da01410114032005151801d03024086036410511b80940800006001a40007056240030300303644428141c188042e0020001e091004118820324142c0079680104100e5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 610223192 1250 610221942 610221967
    0x12050901030b1e2206330e061b03031e10080a081818040b0106050703050d0b0103140c0c0106060509062208030c030903011d060106030209060409020301080a1205 71
    0x200410a000c644c241c0040c004184045985100c0328502984c0d14640b40002c00c200c0c155464000c89044814074400c40100c20b950100f00602c0f01c1038186d40000d8081044800c2c0d8100170000e0324403884251aa84a4a241c0300005455600b00300c0b00d003000340c1003c0422001c0d40b51a1611f07660416200503400305540d04000905582c2ea5010000070308100780050030600f60b80380000d03003000c904001001c0300c0c034035407114003032400c0d148040d50140c407030a490400000e0007502440031118083d034591102402c0030846070a2400410a02c0c81c41814103807100300441f1840c50003040300e4820401c0022181d290300903c241c041c01c550441c0c000c1824400d040200250940e200401e0f10100c2082800c0c035000340401050307070001242c2c1c60b488201c2c83e05c404604481e0032600403016110280068008210001d680b1080240015041c0d4225103250052001032120074400c6d00140072808020b0709252403d507a9084880483e403099000c0c1c825604010345101c02c01511107000008000d06140980c241841951903 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 610224442 1250 610223192 610223239
    0x90127020a3503040510020307110a06020c0108090c040219090f06050306040f0e0303151f270305030d060305010b040504110402090102100204060f020d0305010b03180a12050901030b 80
    0x30b581c2c003003409410181e0140d410002c42c0c02501024002c100d0480c09400040d599400c24041114034540080c0140b049090200b00041100c400398000c220070010980151415a07000d0803031082070180225185840d03d4a000502080c98440b2058403006081d010080490349030fa008550400500e003004c20105500030113681d00000304440000302c0070803154445000b008001044c407198000401085800308103030700714902641081c0e5162416080005800014802d05030b00c00c0049004448075001054520340030a411401c0c6441d5000e425460742c030ba0f20b03e180c21900040014a4a4490030b00401a0a002d580d0002c0f1040e1024492400e1030707a5190102c041840059004030f50224031865580e02c200f08410924000000071903465444010060005254425040140c45000c08000c0300d90f209101c0c8a0407240301e075140904580f502a42401c9140421045001b2032088030050404180f0080c5e01501e810540d03241d40e40e9400d40140003509940e009075102d1710174a6421009560406403010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 610225692 1250 610224442 610224509
    0x50309012a02130207050610140102070b12040c1d040618030c06020d0f14060a050d080703030903050910030f0606020c030c21060a05040b0a0b18090127020a 69
    0x1101c921500c0d002d0040d0f8001c0c052020081e102e44581424003030740210200740002900d4600520303407110f0345900010381e6500303528441c18004110801540c03407801c0110310035580081c410501c20340c0c0c144ea602c0148070016007030b1042d806025040c2c0c0c02d00c0100034071031080750b18218080310030000c2c00c072281e100a0000e8030081001341026800144a04503508164001981e00c20749840400c1602034581a040c0101c400315595401036500300c00214141c40e00c0c0c2000310742180e0091b100c6207044c075240da00b14003802507080c084007130200c02c2c003da14031983c0e0710080301240b402d299130004290b0f504c04414010794056074080425504084c824040381c2c2c90100e03e035400d000059030a02e0701c846000c89188800301e13030410013440f14041e203024049811070b07a400141c002c1c0d015018003800c9480d04440d00c0100d40c5200c1d5620750095009803480c0c50003141ea0f11103544032050314000a84803945196201c14441c23031100c800c03d40e408001300d0328214030709031000c00090310000d608201c0500130241c2002d85035079401c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 610226942 1250 610225692 610225699
    0x151c050c0907030e0d030f0c0824150c031e040503070902131e030309050105040b16031205090a0c3602040f0f030605090136050a050309012a02 63
    0x4001070b0031a802030f04640a5503400004540c403004000c0c500a0080917462600781d1803078100306550040703603c40c50344039006d106115100550b8410850035104242e5080780070540205102051000e00e0158502070594084020090b41e9070b01c00b102070354203803190b50a01e0140e00d00c5082c003051220b924001108415541e5001006075100c40c0d034101084078087c950b0007a40703603486002d6000b015080500b00039080324840d0b128448965150001560b036405240285a0b071000700340034158010b000034000159450007401d102c084ca113501840c240588404403030200099010050310b10400003007038101c00c028001d11044e01c1c41611100c0003020403418002484001c3d0030b041c0b8000f00611480c0d0b04070381c004c021600380300c5a02561402042019001031100342da52034a0000025003106044c01245881d07000424198440b0041a0030000341494a0749404002014400410006902002000c00c1980170707000071a00c0e15102e0300010005003d8548187d101d80b0300300142c48616949000c01c101c4140e048 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 610228192 1250 610226942 610226959
    0x1d0c0724090b1e130219120b1014090c0d1118010c050303040201080912030109060e13050606130603140604210f14070b10050f1c020904020604030209151c050c 70
    0x10300001d801b034009000e050119180896001601c10103200e0036019603445942d03d08a00d5a680201d01c2c1501f802d44038010a07030001e00e031a014035161580d80c03ea40142e40500031420b0070301c4000000c2c00c42d140b00380002603134900003404401c00b01504541d0303099803000b46020000b80c4559034806460380000f4000030306000081c008244648070520a4a28140040c08640e40300e694a03a16180a0820b502c9000321065a0101040c0310080511055555541000080041707881e00c005000d418108201e010341026070306d52000c000122121510200d4000d040000d000d40d041900f0300d103112064141080d039082404040c081300544d0003c6c01110314000504182c200c80c180041044503d00c550400100007100140c10041041700700394400080d910280c8004113a034426078180249481e540340c09040b10712491400714010318100c2140c40e4460320240ca000d00703041c2d490380851f0703902d481649c20303a007840c84e0540140c0d854103054055001e17901443c0103105c074040031911026216854040381c0c0b40294401e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 610229442 1250 610228192 610228231
    0x1060b07062f1e0c0a201e031b090a09030e090906070908160b070515040c0e0a020f09010f0201140c131d0c0724090b1e 53
    0x1e0b01c5500080300441010008040c02448040300e540c0c011446219201d03056101505051602c00a50300b40c52031981c010015000540c4400e01080d92010741d07144008100c0c14030b400103840e0b140402d02a14441c0711100b00e6112040201414205024041d0649103401c40345400c0699610038910b41000030020001003038a40342c201101c512020001c62a0410307414400d12070044d000280f0544604095992100d890ba00e0b80c0e281c60b1119054003084c3ca200d54000c4082c04440e004000514800d440303202150801d11a80c0300d0a081c900040320140e8100610980c104000c02000f00b0050b444014090111314000c2c0108203e40c1030300a1200e03060411030340084201500d070003580100407101d45001d08500e245003405243e04581e000c0d51602c0011100b0140000310242c0b519148580084c0c04616080d4950f14000b00302c181d074020900a03290400020b1364041c04100c110658040b5105545003c605900d05040c480c1c00314101070011848182a80c201c581c1000b20b0781181900000c1c40c4c0700e1100d80030907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 610230692 1250 610229442 610229471
    0x170702011710050402030f092401150207080d030507020f0102270d06050c0306011b020a0e0c041508160e011418041e0b0904050a061e0507090306060801060b0706 71
    0x240b40d00f00640242c03000040c064014080e01030319206070303040340440382206500707d014284a0841d01002c80418601d40c0140504c0c18402510440240c00344102c0e180d65949841040c07a01ca00c02c44c48030003180e521001c0c080d07483d0f810322500c0d50f02c1c1035040085d031030030064070501e40110a4024603042d0b5156040d1003448150341d04234035000c50796044002840760342403523440c00100740e20a49502c3d000c01e001211044501070443c00080600d9002405101e6152500429040c0c02c08001c015401c284400c00001c2110892a034000c0301c94006940d030000d07030380390500c0c41000e081114030124040c001c11080005491780c0c002429810789495117895511000741915105043d070546400701d510030304048101c0c2d92503c0941d00c08030140b44080c42802170311001d005012008070250b802410a422400c520780105465807c040c03011b05c0303690724110203503c001c0c080c102110025195000050404038080081c8081809504094102680200304440c42c041c000c201c0703403159240007481d040c2c81d8001d0008403030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 610231942 1250 610230692 610230721
    0x6160305070509060c01061814130f1b030c0b07050c0d020105090a06020318040b0105030714040f030b16180611030c01380d080d0e10091707020117 65
    0x2025004d181c507049000b8045011b81000e0154030000911800144010050760180b0b41c4402001e40d400b00860300c41041c00d0030320b0708034814103817808409440d000c40060700003a10805109050340c10048007038118034165555940a41c42900703000e200340003500110354042101c55542c82c0413103078181c00041610058529018003107246500000301c5c100081c4040d004002499403c4c02040c200d0745902000d01044102c980600d40b460000b0340a0001036615400340440c10303199070500c0b003400d050a03070750540c0e00c4068840d900201c400e040c0010a0003030303400c1d5021050050006e0f50620f1038030000d0f075923105e150380c040c1072094408003d12544c00160f001820b10455a0003c01540203210b00b0302c400d0000440d2050230900340303400f202c3c100c0002c011003840080070080c9640041034002034030b6050b200c2c203489030440410000000e988143e89103015808104d1810002c01200c40803c0f45030309410015207000e48041120302c08a0f080000b9030050781e018813401c04804020712054280c0d11203d120300f12a4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 610233192 1250 610231942 610231957
    0x290414011206090225050c09100503010f0906051522020403140c030709060b04060c021c05060601030e1204091d030f0405100c0309051201020c1603060e061603050705 73
    0x150700c1e12a000c80c001042e500281030170b4000c46098031321229180c0001d00c810300c42e440060a5a002100700840624001680c9604400c0740064852455110300000c0d0840b00c0512038400350a43c2d990801c81000700c00d0043c20740c4808100c111f43c1015403004c01041307003d08100018a8480f5800207410242d400e9941500c001d1500b1542c0d07104420f410240f4960b039564580d105920078440c4000000d0504801c0c05a2001e075050150024245460608103840d509a204012607102d013070004106e0702c1160084400e481140104000c2080f41041400902143d220101040240c0c110074000850654807004032400c03501e02100003d100480d60501e00480c01844c00c4444103404001200c0e80a0640b01e00034000303941007103540c000f04264041003910b060010200c0140816201c0c1800c0100b4a400b10450140703a0611001500c1c180f05d1809090810360700b82d41080070200d07140c400b4401d01417144030303603240a40c40c480200410b08014202610100070660024101615100064189032182c1d058a0341c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 610234442 1250 610233192 610233227
    0xc01020c160305121305060d0b0907020c09010b04060e060904060807080a20030a062004030b0a0b10021005040f0206040b0c0105060a0b070b0402030a080c0729041401 73
    0x15588465071404210703215101c00e80301c82c40f51202070380503041c00318201c40c81c2c40250031403925601c2c90407003480480d421000e0028401603882ca802034540c0c40345290b051188a981e0b0107410b44102d403104205038128180c12403215a60300b40800d00081c0c0c0c02502c040d8610500322001c07030b01d4803041c40001c0e0140082e034001040038001c10000044503640060320400083c0318010340710480c20b000a86094103620b2070002645a444041010007064099012400120900ba0f448114040720814403686a10035402101d095800204100c41c0c00c04a21600392582822200c0040c40b01e00c691000303599410501016003020340d52000b080801081103081440c0f07030750140c501a103440c0c0d01e580d40c034582d0f00086600801e81d42800c000450607c2c20701751010540c1c41450b5590b00308001c40e1940720a10400603c00ca81500c5031941d9080441e00c403501400481078014002c10746642003403040006d211409046510304418111000140384180c4140c600b43caa030058450090003005c40101c40c1240302c0c0060204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 610235692 1250 610234442 610234453
    0xb0a0506070c0b190e091312020f01050907090f0c2109150209010e03070b030711031204111201020a05040314030912250302150f042103081e0402060c01020c 69
    0x184d511a1000781d02011100d601c410030699441400d024020341c2c100d400c00d56440c0d0320050700b00091900c0500c3d612030f02481c030451310381071003041c070050840780709492516469200803402c000c406001e0143d5801100015404c0c44202c0741c03110040c062404030341005104038601086c40030444895800300076159040605002c07031100d50303c0f41d10006c0d8403090070076002402c150807085a80c2400600c0504803100d50319941d2550780e8681c4103e89a20f0398410905260000300402e038040124060550b01a6000e51084807034018600200400e00c3c5c1c04020101250340144003480c00660014242c400726900122949010000312107624114403402c59580d41c00f0301d00703442e00c0003402000a10b0003e4407200e624511666801d982001c04035a40c80c1c0b10083d40303c0011007510803101c0038000600b03698009629001e04058445442001450407404408103440368011460145a80714400d950802c41401c51080c0a0f80600440e50071003900034000381c0200c3e00002c0a1011410940c119140703142050165107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 610236942 1250 610235692 610235707
    0x50c0d060f09050a0212150d0605010f0806011a031b30070e0d060b030a05030304050a0507050f060d0509031303060e0705030d170601170106031e0b0a0506070c0b 71
    0x20350441c1c86000ea285814682800914000e000344203c070451814004001c6442d91901044c1905420711010590041905103500b07000503c24042c803406040201c0542580909002c60f0070302d0100b050b40072204083e0105542058602c0d460100c0350000003101d0b0142c0d4145104103201013611448a548901c1c0003001180900101c50803035413072113511511a428100d845078882211400d98504002d0b900004003000c120000d01181d1080303175101d101074191134629a030354071f0703040c1543c008890035107041e009007580504100040c0040d0b00039201c1210003150150340c80000c41e400340075010030007500594940210b20804000c10584520f0149012407810140c1c41c0c1ca040e201407c40141212050f12600c0c401050516003c1200041c0d12960340d10300303a54000c04049001c40c00c60152440b818011303100f420102c1d0134015079025000c0c0500c6d1710003242005030a05010740392403d480301140614949400c0c1c034074680e54091030b001122030440c2c045032190f116080650b0720b100a580050101d00000170303010f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 610238192 1250 610236942 610236959
    0x3070306030b13020a050a0f05011b0605010b0c1009031e020c12030c061e040b070306080a06020901020f06010608010902090604090c030b130501052103120f0610020307080904050c0d06 81
    0x43d82103602c2034808100d401d41d5442440030552030380c0501c40395106850428030035548602c1001b013140d4030b00d44415020ba811512801c08070348003a00310f10b20328140020b400004800810000440045500003040078030782c1510000c18045d00252b0130045010201008403410744200000107001c0305c014110b104030300d2100c1c40039680354410000d50704c4d40c0c003504000500c10104901e1106185d140500301e040075030b40703951b07c2c3c50030145c0041009040c140d480a003c00c22500c104405698640304020041c1e690301e03ca00064684200f0300943c0120350f001c0d40040c0f00c44c60b0b10100e141e04441c1c5031038001d615900d0710000201240210703000818414500082c1c80030b615416045261414000d5503c000401c032042498020380340c1c2401956044442c40b03800e40d8a07118100b00c10300d851815101501d041015200c41025500c20565810b003070410b00704240400e600d406c0d2200075039145140010351600c0300503138031074140d4001c1e2400070388126a5040040c020030600da00b259554040010100701c469180e0944 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 610239442 1250 610238192 610238221
    0x10e09030d05010e1f1802130914250e06091210060e0919030e21060105010f0309110907110708011a011d040906020f0d02040302040f02041a03070306030b 68
    0xd00302d0400280280515052407400b1445c2a900d2000300c0c44404000d00d007403031000e54007003040119451500c10001031414418420f40320403100781d2404800301d003800c1070406440030285070040e88110042c00c3c0c10000030382101c01001850710a840d4980c0358001e080005240424403000c1468501906c441c0003c1000a030703100700141d52600e034200b038603a110104c408d65600b0900d40c1d20030800c1ca950269a000c28018240c0c095459002440342001b003c501c07618074040741050344222460b41c04200140b00c2581c20203103c04c00c214851604114070342e1561900000c101d14880458000c2c0a08800b080032944600d50411190f050102241c80169440000c07034002c00300a1414070481070400400d102c0341d80300e4004001c52072014551031060b012450100001029022411038070b055080001c6249071550f903016000008014a00503201d51845c0188170079100225041465148104414000e0355414491a002d0301c00e40d0001c2c5031240d4801c502039000740101e80010b0440000704080005420050a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 610240692 1250 610239442 610239451
    0x151206040b0901090201120906060f081b0102010c0914150a020f0d050307270504181a04080a0f020c1c110306011a16020d0516120b010e09030d05010e 66
    0xd86280c00d41d580500b1508039007000000900298007001441684840c0d40c001e021118040d000001c0c1d010740d40c62610600700e80c6584030000303d070006c0300d6241980b48042d44902d0541c0d800e000a04c041e0044100041c421203c034025a5140c2c40b01008042c100d4446103c810701d6401403d030640e55401c5200f101a5440070707000d8100d00b6174441c00c07c15034241c0b07210710180c038042d80c0d07140c94400d958940001c00108031034020300c03000c03000e10507124000b910b951140551814046108109600140c40b42441c079000c0c6070a410440c41000c801d003c0c000007500181c1281c0c551422454480a0f10481013022420944050740c40f07035100107080b00d2402e81803420340c2a112500e03c900c07003000000040310245522450300b4446d00d45102c1107031680503456000040280320031701c801d021b00b07190100590300080790503d0651050303e55601840070280e061540c5a83c400240070390748520040726505545007402100140248040142c103000451200841041034039403612400301e0601003580c441c9845900281c00310b5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 610241942 1250 610240692 610240703
    0x2031015031802101b1b0801061d041502040b030a0f0e0d0305091608010501060318080702100e1201050601080a0c02060606070c0f060201060504140f0f15120604 71
    0x82540c4010340a4403a10200b038004081c0261841015000c10014114001c11002400a210080c10a407004100f8204960340300703205035401288450b11608889900f40c0280c007141e0715100003401480220070704450745260608520701642d940789490701d19000004101c032045400823601140303807001100510302c00e90f040d100c10070040c0e0410702c14900755100414003803901d03000281d42040c02d038440e42000c0c2d44200000119003d03045100c01810040e6010b51042c910382e55280c1c01404210380c18059030001c81c18141100428001319207035001103201e1080020300c0740102d0f003a0083d4245c02281140ca010314010710206414240513003103070290504032001400184c049000501e5040f642c818040e501070140d00826490f03a0305820f01040c0d51224900742c0b191926141d000403850036003004800a0b00840d40045886840c010a20080d210701c0d0141050a08882040000001140000340d900941c2c02e50340a0f07039038540100842140c22410943c5400040000003001a10000102c0f980914401c8 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 610243192 1250 610241942 610241969
    0x200f19021b0105030c16020604080a060504020906010c0c060509040b04090f110909150912070c030308092a010e040204080a0201140a0905271005030607091a1309020310 74
    0x119207610003100c0d0f020081c1740c01e11042120724880e00c41000d443c0e01c09400d10385481c0c1c03190003031850303c89280b10488201c2e13107030b20400003141003042d43d0541004081c24070119845055440185010450042c03004014010078650b12640d1950406103004602500c104150035003070803c000c001c54610390694030008800d0141c0c00c0380c00d01005140c4070342407403005012200b21040c1c2944000c0340c007622080c110701c42c0d04144c2c440c0025600007080842d01c40c409010290745180750240504000404d41c42c45600500f41c0f0440180c001550024001c8940c02440c1c0300d02d012800603118090f0b180c00300d0f5040707480410003182528001450005041c001d0301d40c5c2000c1c000c0340c180303000c2034404c40041d0740c00941d0710041048039081801441303075012002c09200024000100c051304980f50100d9600b0381c6a100103904100304d08061080c0ca8021845107003411103203040400c0d401c031009040c450402c0c04600020b20104480c0041c6501000d07081e03c2d10255940d05294804081c022039078000c00707140d10080d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 610244442 1250 610243192 610243243
    0x20d06020d151401050a020c04021204030f0206190902031515040b031209010c0f06050a0204090e010209030c090a060b030a15050303070b010608040602070501020319050109200f1902 80
    0x1803038000b808883c540906450346440000044526800015903981584202940300320f1507901d030700103000c1c503d002112100b080d240509000305403074821050002550800f409010050f5a83c501e80218180450b901042142032840400d2501e40b9a070120307400c000102060011280030710812126918046a00f440134030200f03400c060302c8020800002102000812804644e035006488035600307075008103c6010950001c1d04d0780c10640c0c1c0304660001d60294000b41c05c0c00080118480c80d103840c180800210304041805002c43c0d03072070254401681c801c41c0c40d14000784018095800078006028034262003902ca0401d070a800f40603010400c5200e40c411202e00001c030b00d03410000133031201240c03c44903425140e441e01c0e100b0380c0c1d2010701034001d5030b42903000c10907400890f2003400154000c5040c80170440c904141150140100d40060f00405130315400c110f450006100c0040410003110b031800c5640740c1e00c4c0070404105060b1720490202e14903414800780301c0d00b0100c0d00030856000c4c0c624400d0101d81b10284 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 610245692 1250 610244442 610244471
    0x100c051b040c0e2101090c060e13230c0c070e2205071a0d02041202040615020a0605060406120507060305010f050a06110106030215070507050d05030f03070309020d06020d 75
    0x100d40030550094000311800024072880e410b075220a070300c13400c000214020030b5158240f41407030540105000c215618581c01c1c40e418950342900113043c160741b041000708003401e03e100d05044208030f205000d03c24000464104001301044420303d0105208980c0d420365101c20510f191481144d172b2280040c103040c10f60341e0b800028804000219131007070150190301e040c02070154060440803850100c074031042c08403d40d101f0480c8000c1026021509400b824028540304000c180c03502908a00c595081410219108035000102030320515444803010609507a0f8401260041000d0b0740083e201551120181040c800f002c0b56100540e400c0d560180126070301c0301c60380141003041d0321403250044001401000441d11460820040b403940344e00200d6100c0d503a40004100000c2c58541414850740002c20f60700300002000aa40140415070344461080c10300d403251904c0b03000d5561440c0b805c000000028490502c69803250380820b90050051b04180c0407420240c00a4002d000412216031828000401c02007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 610246942 1250 610245692 610245707
    0x1701060b13170d0f0f0e0907080108010b030c0102060105010c1b03030915050301060f050901020f1b011701181d12030a3c110412060b01050304030509100c051b040c 72
    0x3c501d61140401901041c1040311413042600c0780008120b207009644a0300c1d5280354101740036607150758030340c9815414564020f08441030f58070f1441c460751051040c804243d80101d2030604440c0242004c82c3c0f41201400c1c0840d440d522a030b000c4601e488031a00100c05c141c0c2003070036281a5071035000c1460040500e030070143c40910007800b40c46c010403809903041180c0c03440b440003007400c0e12042c4191141081000f08062900a800030694a03100e0001400280c1d035034410044040d4800e20703640c10003039500d0718600c0780c420140842d1500c030340380d1109c55a814054510300185403003c404401c41c2c2981c41018404c07001d83d04141c4190203401e003006411100c0035802c90120580e02001c0480310b02c034021260002c800c0c1956410000c401c0c85c1c0ba00c18041c138464200c80508014907810185440842181c50070340708a98190000a040c443d0a006100110340e200041c2ca00031042a0ac0804c0c0720b051520003902c1c086600c0700001d01390310590750441c1e418080c08442c80c07000340042e10107200b4621520005d80e00c88 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 610248192 1250 610246942 610246963
    0x501020c06011a0412020f041d0c03070e180111030106020607030b121903030b0d050303040b0702060c0a050c0309130e0709051509150d0c1706010f1701060b1317 71
    0x4000c4c0400e10074900c0100990008500c01000181d00401440228064603481150100c084840b0711b518800b005080c0131015040900301c016042043c20301c0300420070280d015280d528104e1030a05c0ea6114001e003540035020500d00060070710740fa9a902c00c4000d6a545040300d01e080024203103441c0d05124100360445c02d00d00c07403492000e00800300a0861440710000c0807c4203808050f1100d081d0340040d101d940c2141d034139a0140004d50f58074609800c12880c0c11001400ba24119449841000403101c0d01c04103a07076140342c40d40b80c056900c2400428451541c0101441d03a640040e680d000d600803111154005580c4941c00ba041e9132105a6a001c0d0b4011150704880750740303510301c05941d580001c2c070701075480f25070044e65010b201104245140224030825441c0c0030448181c5240c41c0b0034040f100c06100c0110101142100034052581401c080846415140c4101c01c1c0c4004111100c0384280c6080d0413420240041070f0989840d0b400b00103000c180c1c000144181c884c50881c0398002c81070b01f40d0114000d20403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 610249442 1250 610248192 610248239
    0x1407020705150f030709091503050115080604150609060e06130c050a120219050a020f0613060207083a11030f10080f011d1920030a0501020c0601 64
    0xa001c0d10f00c5640f0341903400140820304100d11a0000b1800f003100e84101040500d801003010b00c080c0c11880d2840c00c650f99540039106264803003000700160307d0005a0a50300c9076100001d41c0c01c00a42c0342c40000900010340040451034101b0700040751036982c103042244142411141c0803010007903240e482003111410f10301c020020384202f1843c190f6a001e105141000205200d0040c60192003194590700301030111b0f01c180008400040740c02c1200d5040040400e000c1441000d495035003091203004041d8a200300f0b00801d0190045a160144a0030009681001811070088a0200c54089102908640035060403c480302001c5c02805542c0f054400c42803030a8104070610310b142c99603043d0003480d06e0024454004512076460110301100c062160400d0020300800201f200b01050803881e04945110021402a50129664208030040030496401c0789811440300942d0b0740841d92034102c2e844d110030740c094042c46000002070400c03c055001f082c06100340d106a980998984404043d0f284114500100c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 610250692 1250 610249442 610249447
    0x5130b13050d08090a08070c0e1803040618080d0f02070605090319021212090405010501050306030d0e0a080d0c0c0e0106021c0c0f0602090306010801021c09020a0801140702070515 79
    0x240140a8580560004010411141704117800c0d96401c0e80c07a449080c0440e43c201b5070309402c010b5900c0000340240c0018100c81d003c500480070704807250b9207000364070070f001c01c12040440507000030000c103541001521120b01036a80190355240060200c82c111441c03000107100300003001034002c2c8500142c1c0e0301103a0080c090021560b600c610512084840003003664001043c640305804240108100e4101c2c506200a550721095030000700012140c050f80b00d2410300a08200308001c0340d81c00b0130a04006100d0b8100080b40e01100130100d64a9050754000d02903520414110f03070303522a0802e072600100e45c03086500f0000310741c85000b1420070319828814440540c1c00510742c510f50701c00c0c4641d1241811514138101031a40d0454032540d19136001400192280c035400207809181e820144103c9014105900c000d614000149070345403000800d036440901c090350358841d10007c550301c0a10210050142d80000d01c400da418644a200303505040d0307006805881402400211800c0100342059a0b03020b051400c0d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 610251798 1106 610250692 610250713
    0x20a120b0a1805130b01080f07120c0608070e09010f05040c080105092a03160801080a08030106120b0301110d0f09050706031d0105130b1305 62
    0x80c0103020070803050202c0d200d0680c40080c054540e03000002c07983e4642c0c81d035680c141000e240050051207440700000e42e4a10004030258000f0412050312025595180340d41c520045c81000200b403918040c44c10001d4501034030085501141c9414010b11241d13a03280000d540c403600b40c0001e4404030b0405001d00950406e0b00c544040b17441c131410300c1705055060900054800d0401010003d41810421072080300c0c07c1c0e41c400656542850488050312402c051a0304041141c48600c000001042c001c000140032000050b070400c4180c001c0409407030360742001d8040756203141040503842455206c15000f0000c1c3ca0920440d199a07440d8031009480781050302910f02580c4c5c809c032668507860304005440d00444d0011a4160031500746080006500556001c3c40824440c221080341c640c1d440c01d400c00c0f403040030701003040d10403038490f9140c80c4090b81c40282c07003030804109136000380c4a58004035900 = true := by decide +kernel

theorem cover : BRFrame.Cov 610071942 610251798 := by
  have h0 := BRFrame.cov_init 610071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 610071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 610071942 ≤ n) (h2 : n < 610251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
