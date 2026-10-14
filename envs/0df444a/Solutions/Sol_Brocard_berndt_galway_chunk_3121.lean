-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3121
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:43:25.086346+00:00
-- url     : https://prove2.me/submissions/a6de918c-7086-4e1c-abd3-b9c357b388ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 561151079 ≤ n < 561330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 561152329 1250 561151079 561151093
    0x705150d0b090615070206040b0a03050403021e1018120807090f08150601050f0d05221109090309030114071103270409021f1404182f0705 61
    0xa0701d4860403281c492480100350601314194040214055040b254040380c0180c014400481c040c0c10303e00c0603003144640360b5400607460ae0701d8240245014a101c01c0d1510100444480450007400841c84041040801101054400c0c2c1d03c2040701842c150190040c000030012004001a998015007880c0908140e0740d8000445860380420500301c0c0b424070614805134420448020321303000d048185540000c3c1418168184048224804e00642c496041c110b60159500100600040c9481344482c800040003041b41030808256110200e09e0380100c503641c818a1210000749142c54104201d81540d03c024001f8003200300410306500d08084241c80c0f030000f0070310b45070b0020481140082a1800718610401c0303040c1d07002400b510347c035103281c80e003907600e410030344130b00803140962105600c1809201300000b9000c00f01944120085c4a011008260031500703104004c1046041c1201522402007824a14006540c0d107201c1092440840e1103814002a440058804243c86c1c001e85c1c082c124490140c1d0030b5980c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 561153579 1250 561152329 561152351
    0x5040506090d020309040908090a090608070e060f1909020c0304050307120807030e1809100f0203074e0b040605100e1305130218010302030613050705150d 68
    0x19201d0b141060720040c2c1c401d111213442880c1541100c07003044d00aa2010389861850b001080c1c0312110b5030049040c89858400400800750b042003180c1c010000703841400f002c1e0a01b400042c820b11480480c662007803c1c101090000950030034440e03001400c2415007156650800801c894a90b0006d2103414424021128000303070075449080d10801151307000c5202e07444c10580ea501a40d01480c8100303266000ac140c1c910a0482c0c5049203015409052004010640003190300850400d650301c0061300451107006206019060790800001da02c0c510360702482d00c2c068401840b807080b03d0200300c5400303251040c0c01d85031710100940640b041c00501c400b024062103861301c481c0500068900510445401000b800c10b007140c070300c0c4214031680010200805813825101c1001600703050340ca040c6c070101e640366003901c0140218541000388612112280c7c40c01c1d44e06600d590006601e07030340f005104200d448030700020442080750500128014100003009680760036004c81d008511604050300c0050a40c0ca4440400b05c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 561154829 1250 561153579 561153583
    0xe1c06050c0a0206041b031b090506151c0b0604120b071716020307120810080604081b190503031603021801050f0c010515100f02060f0402120a03030504050609 70
    0x1120100319002840030307031100d50f50003094411a00c00c100500b600c40b0004400546181401c03c0800380c01489103230031505251054085450280c179243c464140c5610003081000c8060503500f01c244400120442200d100039aa00980860100e1035880b1100080c0452110800300301c00500318041e00d00c108565460480688503901c01d00b541c00d42280c14040001ca141e00f61482071f01c014030f00761065134200102641c40c2e002c0d22443c018001e01240303440040244824580403a9001480314000a02c401d05180c1c4660100380308880342200c504c41c1d000c100e0561800101300f6440101e03081d0180f200841920b0410903140c3d00140c9981800a09110031200e00310321030700958070320205d1407031103407580c80200c030040d0b44c0c5a0007030341c3c10b00c8440c0d4180610310807080203100f81c9216940038150113440c07050303202c01c0000400c0d018402805002811401e00901d0340d00141003076005003407c03090840340d00d480c000507a0603003039540481442e00c44c00caa1002016450341140b401140300d0411500e150300c03101d00580e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 561156079 1250 561154829 561154837
    0x10b0d0f03020c15091507120215150105030408030606120f0106030b0103020a0e211f3b01060b0409020901111f09061508031209150f06010e1c06050c 66
    0x80d11036042803009005c0f0307241030920350341e422030700700b5645113030098a139a4490342204c665404005030700103804d00409034201d490b941da80300c0340d510360400c501c800c4200080c0590002401c081c0c141040880095a55250b090813110990546800c0d0700c1d041c0b0300311002000c0340c03400f4040d240010b4280380d4004415400b03030017070b5102c6010340e40f0780c494980b0914044c0649004000c0700304c0381000c407403205140c81c8003007400282c1440d40c3c50960034042060322040c030340070f6440c400c0301141c0b1400105140d5901449004007881031151082c8240740420200448901402658111486403180040c1c0055003a07003507801001c0b031200a80b11420f03c0254001901e031030710058088402c60703100c074220003500c034245544909221441807000080000076600c04c40c1e2a041d0913080460150b000040910b49010300381402948070003403900504403003545c504007400d0f220b00604100c5100c0841c0001c03a619030300840c082c1101c0039001c0c013481d504c803401ca81104200306d803850095030b800380b078000071442c1002d502d8115 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 561157329 1250 561156079 561156109
    0x180f04110316091a16020603071106010b03090705100c05030414190e160207031406061318120c05100204091523010c050d030c030509010507020c040c02010b0d0f03020c 74
    0x214a80c054000c1004045d40b0900401014515003034025005a40354005140110000d40d12400d845810690141ca0241c040c0c0000b0381c0300d07070f081c000c00022075400960f520541d03806690040208030301d403506031103c1ca003869000f01a40008540440c0807081c400c03075060a114100e650220070102140306401405041c0034101c1650320490000300130000c41c90014003c0510380c8112065103a9a407600310071041040c1145025412880606c0142d142c45180e6400022203040d04100c254003560344080c10301d0800e940141005284800302c4002400350a03650b40b42074000040d154840e42501c40180258032500840c007083d0703d0204040e00e20300e0100300351011303210616245070400610b003024500205082220034100280c0c00104030008400340f019402e02017181c7c802142d20440f151024003a00d600414607030041c1c1c58201000b141035030005039451400c0080d280060f01941280040303000d07100c80644290420b041900107004c0109a1400c0400c06020b40e0035101c070910f1900810500070319580e04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 561158579 1250 561157329 561157349
    0x1110313090b0109271113080303040201020c0102060106020604020108070c061d160602031206061b1b010309150e2812030b0603040b25030e07050a060203180f0411031609 75
    0xc29403444032030b900c041d01002c440343e5550308048108080604c0c20245c2d030008d00450700040180310465804000e0110300c000240044d01007581844030080d035855004001070704010f101800300c0c4203c0e01601114501e0390f0490018014071460102040c00124501181070341c5110303405d02c00c5019021900850705503052580610b03c0c041c003500c450320350080042c2c0829400030b030410085146984101d0a40c0c01c0d080910701a043d510303c0c01c811380a204a071910700506150411407020300143c00910003070340d40d0403148ed00050741c149000d1030318134081c460030b600b0884200c01070700c1c44005038a85521640c03940c070404a41d60500e04440e42107064501e90b034880e940200301400030900003149646000d40c000b0b411540c10746044e80e0290b003988207950361342d1560b02103070303403060094070101c01440b030b00015003000e5034101c01103450401c00a560344105050b980701180b000c612003403140e40780c01203e28003e030b00400034010b0701d100f020003803550f500035103406441f0144490100394050142a50f0400c451013085 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 561159829 1250 561158579 561158639
    0x218010309050717102003130309050a06020c03011505010801063501032102030a120e030703051306210e1e0105010f060203090f01110313090b0109 65
    0x640141c10031100032581c41c05102008101c0e890000c5003031485403004001890010b0900ca041000c40d448000c03110154040b004202c003441625078100d0380c00a240c186030440152181c201200d60f905590011035004000c180b001403910b0b8005072801c0441c4040b4020407c240155484e6062140b0074494580864950b40c0100f1103140540c0035071889105008140c2489076894041d4020305007100f002030740000e00000180244a0006200e0914064020400c003200c1d0300700304060341e01c1c05000010402c00208096040e80c40f45c05405c8190700262080c112611032401d450082c01c0c1d500080d0220544800c031500001e08588211150036003803501c01603d0700e43d02110384084d0054000c800d880c81c82c82c450311104004c2d1020b52800036110b142c00030000101941803030000d00028007a548241b0441d44140446c0c075040d80d84103054018580242049044954000d4141d400c5001d0001c81941030010a4030000354510310350888101d40c81c090b40c490b0748482d160076004007030311103408503000da40c0c2ca03d81e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 561161079 1250 561159829 561159877
    0x408150615030405030705030c030a0311091e03010603020604090c1115160509061309060603020a080a0513050d08010914040f1506090204030f200d11010507141c020102 74
    0x20000d641180c0913105592602d40140c4031546954011201c1038100d500001d45844c8080d07040c40341580848100b8880d038035000113607002034007219440103d2031b4031f18898603804000d07507000d61020380210707070140145887c0c0b507650240c413008280d041c4114000c6a11135403402a00e1402088968145209011030300c1952100e070000c03160200c0e24010201071020030420000256a80d0025054560070340220507107150400d0f0300c8030146d44c165400101403600500ca044c0c0300e50b8101d610554000140c1400041d141e652100b0508207002c6040e000c1c010b4007850b401511110ba110b504141a111252818003041480e03a0320360048a20031038001c0e003500c100c00721040c0014054480c00c06030078842903010914a4450341c40384102d9005600448175142c0741d074903e104111800749400c1454141d2540c00c40403200c0031010480003000302c0f8009000e030810441800c0568014801d91b420690060120010704803004400da584030b50441c450030344a21441440c06072175105000319140c941c40407107141c903410069 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 561162329 1250 561161079 561161119
    0xc110f030d050307170c07020118060903031101110403081801141917190b030102040501020c1201090606030b0103140d0915110607020601050a170a0f0609020405070504081506 77
    0x4e01101d082041c120700d038410104100f49070b64029090314425503503900607071001610188408000e180d86001e903040030851103400c104400101e030341600b40313203545521401d6410700612000c84141c148500205000c41031040090242041071140301110121465103401900d080700301000461020004200b84109020308040f519030300c070300601300740c106c071009000d54148241e0200c42c0704052240028190700155518015900740b404154001c40c0b40c1800c210000791200c10740a50103024511800385181485400d510004000c1c2d0041d01c200001900e0340f03090030000c4000c0c07100350b501d07500c012042c812074000401c10800c584081d4450b07024651500495200007201041041c041c800c100c0f14604c404103040c461188100d80c240d0280c051507061a04203c4aa0030b283c014614150342000c00314003e400000d80b110380c030380d0041c0002524071680d1034507401a0003a0180290058248820300c00f603e03402c18060000d07103120001b610ba44651032080341c1c24907032040300c2c005e510a003c502c05054080d68 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 561163579 1250 561162329 561162331
    0x1201020408030a21060801022106091b0f070c17011802040b030c0603041401050c04062a082805090d02041a0306011202090f091015150c110f030d0503 66
    0x150800000444005813905002c9510a520006859400055600390481300001c0348203000c84462070410700303080001c08241c1403d80104180b00725060400c1d034204040c00030090795412030094041c242c0d60340941c41c245103100700c01e11034543e4544244045140101043c019560405441c50303486900355140d808210140030f03010103094060180b00051752803900d48100951003a4064180070703980558a014460854030014201030810a0a100c1808510b9020030318507078031050355402007107024415150040e2000f1100b0001c141c420b00051069030701f1440c8924410140040c480b20581c2c080041d01075416200320000706902090b88030500c401458203612982042c1c4000f00c2e00011a010031021038a050800c0c1c000d810005145c021381400c41c503141d11240d921117107401c282e00990410703680d0f840e60307545c4180e14180003075207070002400051007000300840100240e10004102d8004a4405000d022030311383c05490840200c903800385541000c120401010001130024042c2d000c10070022a16500 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 561164829 1250 561163579 561163607
    0x30d080f280603210302030702060f0403030605130f05070207152a080d18020603010312230901030608010902060a050307051611040e0a0b1612050112021201020408030a 74
    0xc500c00304074920140703511030400038502ca64a09010100d5034000302c201108210000c10800d40100201321740e0540c00f042094004a5840c3c0155803901d0b140380503805001e55402c01608501c083d69003e1005110341c221080540d80b0040c1001580c81d480c408036215034290098003815682003545045561080c041030f5101418011410020241d4603103e01107040c002c0001c0e03178000c0c0082a040e501d451148201d00c0442101d20300c00c0d549011680c080746045c04148405071444050301c00d500038850103101c4035428400c5030003500c17010040d1040b4101c2103030000e070b101d540000e15100c0e000c6154241481480002e640042156081030020381084409610061600d0304000d8107110b2540d040829040c100380e030034840c2d40440300d066916001e1008440d140c24a000c141e40c094185407000c036000b8103c443e000905501c5c1d060610844036000d90303070800a03d01d42c814a92a080001070342009600d07040810324800c03a0020b45900191288a081c2d01845c0954219070f04108451074005008000e10281c0c28 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 561166079 1250 561164829 561164881
    0x1a0a05060f010c0809130618020c060903040f0b090f0d03020f0c0d0c0e1306090c09141005010302220824010b04060309060603080a171b1804060305061302030d080f 72
    0x40d108e015188083e004100b480c1d030015004101c2022050040c05902c2d44596188020342c245440c00c503a900d1280e0540c4980e0281e0500000d14006a46508450b01d1803048090000c0700854014a130007587c422140b0100d814600800e055050149040c2d04a41c903225008020381050a062000304013580c80041d280000e415980c0c416507001413954080c42042c1d43c0100300e10341000c2d1074080c0400641e84506920845022450100052940c00420300310640c3c60a180040e158204800003c0004189400c500c82c442281e42002483c8030001400f1026408000020700040f5005001403807011801e019031a000740713062100b803060b50b101c1d60000f25014000c1360080360301541c2e501c902e45241d10450304440080d03906041a54030700c11111049400814200c20480e4481c101c010007019802140c040840100344034034600081c0d03945400c030300080c60708002550700d241480200362460741501c1408a0003070180c410b241b08502d010304542846038000200b0301c09240da484060205074030412402c41841 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 561167329 1250 561166079 561166091
    0xd08040213090b010305010912110a260c030403060b010f0903061808120f010501090b0a030f060b1917011505130305061f0806040201020d0c1a0a05060f010c080913 72
    0x41583c0c01c0c0b51070300a60160000090325941414031603110025840384400b403010140c0f100c040d2040008007404095080041c4210440d062078071222105101c4e90490383c001400300d0301008200011000b802220301c191404c200020800005481d003804000f90040071034810390081002c207085810000e81038082d080c003001039a4440d907a40031349800012450300d12a041e48200004085503510b07090141001b42040086e11f80f070552031800c64490195114105078640003c01c81c42149508444040d0180260b12500c0319200038100e440f25a08461100000e40b90000b59005a0003595015069a03a00b00401c1e10080300300c08195144e500c1901c1d00303100c44001b1100040440c00500841740500860640c2003149442d8204525548425800a05498010360700340801030b0303000240d4440f10541c81c1000807651070a418280d4507586040440400400b0540401c205417050b0b03400644100c1e01240c0c3c4c11025001d203001158500f07240d15000b401240100404210362030f02581200c0d032030110b00408210 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 561168579 1250 561167329 561167333
    0x60f04060e180103230a030302040602251403070305012f0f0a050901021609061503111213140303040c120c180e070b030402010908120a120207060c11010507020d0804021309 76
    0xa80746c3c11000c143d00003a8041420300400d54180103410624030300ba00000100320f0a04d021011004151203030558001c0c1c01d8001e4902c1d510f05010160003160000000c0040d00782d0510340301104000e1000302d04a1210100342c1d010030341f4851080d00c003c1c00e50251418104480300c030050710654804403440341503114214918800c00803205007140502600000404c03864907000d8141114a00309900c08181420002d2a140c050b010b441a509803031501c0300d03082c256843e065119024140c004c00b000e41414a9001c0032040d402c80080210f0040c1d10901c0160302080d07540c0041e881100c0034000051031920045810070a003640402c4410f01c525640000145885102003524034109040d0711640142001001300015503801003103000c003e02107400030f402c488110700b0001c0c0d250f201d00c600f0072050010203820f406d480c3c400703581522505603000c0da081000c60003146000c2c01520075510542d64079801d20700000c079114404a40700c44d47e41c0f00c5880f030240d580c959908204140c20039400c0510340c15510041100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 561169829 1250 561168579 561168583
    0x3060b061c0e10090f02100917010e070b0412030c03030b030a0308010306150f0e090709020c01090204150f050103090503070b01150215060d1b05060f04060e18010323 73
    0x1018000d20001102910704002c40d0804410740c141c1181103141200c1100440c4580050703600b503036811680c14030540f82000054070040c40d690081d48901118010200c1d820317405600c0405074044c07180403511510398820045050b4401d50050900344500611418002030054904041041c403a09000c549070317251034003080c54400c0d001002d400207038484004005100042c49511201644081c00b464103e080002c941c012f040280309540c038905c000c10014a004d041800300c04054100c81009540c1c070601da1075054080c00700c02e00141c0c4150301e40861900c5801c03c134103250782121602c499100c80780d031400c401134000300b000403415203980c007081006070001142c10009502902c0501c004959005120500a1070200c40308466403409207050103100060b90341c0030145551951046c1c0d216610145014160100c51240d0f000d10b40000011604441000d007140180058406507560502123650340810089005c10090941c074210150500503c085620503117142404c241101e2002d10401c00900d03154 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 561171079 1250 561169829 561169867
    0xd030f051e0c0a060b0f21031201090902090a0c091a0909130c080f0c040504020105090306070503013f0c0e0429090d0e37150903060b06 60
    0x210840e0846402d842c04c002e00c900c03507544c400c00140c80e0060544113a10118620348400103007440514401c0da50308590300c0040044800c5042c2c032040e414204d51391881c903080641100e01040344258040c90000d1542a202d22820b00419200da072880300a81c13500c4048404058038100225542c1c40c01c11840d1055200d04180e0f0780100d100308458a80664542005c5804081507002480342c0d401c0030122803681040010810100360341103500003013a48403840140d9181c0315034000150103000380c000f00418036812101940c1221500199665660701c3c2c00d403149254500082500103d1419130b40c01209000d1140090724424481c2d880455150780b201214001c6400807203086a407264000e040342c100d1192000219590207209800180c03906280030788a8407500c40901c40006c02c01c0c0035504411580c0c0b04d6040d0184200340c64145090001c850342000d44a0015200d003085100d28060000b43c4000c034617204092102003550388100751420366680401800e85110484d51114041c803004958208100c211 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 561172329 1250 561171079 561171097
    0x11070807050c09100b0d0b040204080a060b10032a17181209030307020f030c130b0405150102030f1309050703020d060608010605091c060513110d030f051e 68
    0x5050810860b0100908550003c10000c121200c0544c01c020b444291020340b00742c00700c2044081840d0340050041070003801242e101111506c120b0401c0006d01c24180d0210780030040540d64480840d4013024141c0546200c40316001c10003441841403424003e181c2d40e0301451103000d1501c5502038908107442080c0707040540e0101403c3d10110b9000402000800290001c10500c02216082c40b10703400000f51a4020344001900443c5125075440d00d658080c02085000c6100404411504035441c0c825802001c4942720300b0b01551410700840c003680386481240a000d00141d0040d46805c410080203900c0d5080260044907800006e0710210300301c0c9080c01180e01c43c40441d41c0042e2101500c00360041901d4180d480f510a029600c001070220b1607111040720903107042030710b8046074010a584840c5450940c0e41c0045c0c203641c68101809010700107007000104090146943d24480710900e17040000c0106815002808141000c0100b01c40034082d802030700161a80c600101c0c1c0c1110582c00d00325080d03002c4052 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 561173579 1250 561172329 561172333
    0x90f03030f1005150301140a0e010609050f03070812070c121401140906060103021605030a0809060a02090906100e120708011d1002090307030f080d1109090a1107080705 74
    0x1000100042c01c0100c2e4010f003c2158450f1500041c030001c103c90344018012410303e404840c00e142e07403a0301c0e8014541c0040c900403403200629a03468800800b410514000c02d880b480311031012007202c0ca030000d01c1b6420354030f018002d03040c540c10b043d0740041a944a01c03003c58102012000c00038030701000028a2030749078000e00d006101219150460f50071903004400301a403202c0042c080c4404180c002500c070754010700a080069a07003510f040700719040d01c0001c100030803905c40010042c0e907044e8080003541c041c0301640c00b107030f00c1500c4003480c0c00180d008140f61030b50403000c00030001300c952800c2e000906994041e03040010740c180070000814034214014405d14a161301100c02041800800d2203080d01508108000340d00032018044129118011007416000e4a0340114007000305540070b1003140003c2d0b911030461600c04280e0304d02540b258010120705030003d481d09000c891080c6800003100c0140c1001000580d099441c085200014501091106028142409007000041c01d0100a111a03802040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 561174829 1250 561173579 561173581
    0x10504091e06022802120a03020c07120c06091406030a060305012c0703020d1b0b0408011406010309030509090c1b030403060b1909050901110703030c1701081203090f03030f 76
    0x480444040c04110883c04140110340d10084c08903404606040000c18102d01c196691680c40b404038060301400c20401c0e220f0041c8000024882d19814041004c18441d00c00040402c3d0340c3c01c0c3c15a01d500c1c407403094145243e00303c04121614075100c001182e12500301a40010465100c2d201e0a084035400e100d80600e04a88100b41c1a1903141a002c403030070000803070020503055080d03601044c03140c0c2c0181c000400d48021a281d00c1c07034116001d824071001c3c0c445102580d40342c5a0b1031030000c1c040c2c0a00e24460000e1380c3e140b804584a54400c0c0981324015030103440f160b141c481c1c00b10034030840c100010100914a1000d0020f000c103405422010000c580c0b0400041d0346030f50a50402d60f003203d15080300240f06100e0a804440788904402d10f800448441440004d015903c0416903405400300d0503020001e241c000400c1c40c00c0581550208081d959142d0300e410408182c9040e1203181902800b503801141e10109014030075001c003800031607000d08544151814200a4516245103400580c0c4e22109021400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 561176079 1250 561174829 561174847
    0x9251704031d030102090618040209120d080c0f031504111821120c0a02130911040b01090b160f1101080a020a2f07031202010b0414010504091e0602 65
    0x24000031100032080f03000b180341420703010000d0303002e2055040781d185506002203001003541d510350645603002005400ca103031052012040984510002c01c41601150745607012622030f00490042c4c80c40c1c0c01600c111303240b13103448125008501203599103601d50301070f0b1121aa03400e00d503426005005806002013000c0110b611100802009844e04c020701c4002d42c0f0901c00300b9a4444d800150b881c2c415000c070b40c00d260349511a0300030034101104000040d400141050710a4003036805035204800f0140035000041c0e410071204204001e88100340c0206000400f00070f401d03c0300300e46040080c18103010841c1d00d140c00004a079606000c28200840a4400d90304003090012103582000bc0c095001450403001c500d489404180941110040380c1d840c0c03044d01c0030081c011811070f0140c840b00000354100c011954015543d10345468290040c1d11150b0065003845c1202d42942010f00038018110320f60f50145034580c2c242003e00c001041d000c24141c91030715076074000d074400c00d5003003000040300d078016080560340f20801 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 561177329 1250 561176079 561176117
    0x60b090a0501210e0a0b070228051002030c0c19060b03190b150d0b010f050612010e0703090804150810120b0702030d0c0206090c0925170403 62
    0x1d0303000a041c803c0940001949401110120100203160040000c043c0101500545045a069001048500c0402c00e001141d500028008402c084a00240c100c4e00d415014043c4036a901c240700130079980c401c00f0303682440507203a000f45510003d000e55043c1049084a10a80b40a1156081003c15805212903000f405500d0040c5c01544a0990050500b030300740b500c0c1c0c000e85080c0740c0030240504441401082d8030aa0a000034102a140200314240f6520b160520004011082c480c40e200c0190031500011300341400c406035400a104002c0d06041a842c101d60031040000040c4180c0416a490081c00300059904002e0006050301c00040040300d966000090903040300500f0356800340e4206002009200e90040100141940c803101c101196250390800340e00c0c46c01071401484c051424916200c1c1250303400a54244115404d900b165441e440300014484000c005640c0c092090f1082100a03a419000001c04003664196290203003043c8403c048880d003aa80c180c400b1000542c0303140d1a01c0c084284 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 561178579 1250 561177329 561177349
    0x8030a110f030a090312020d05150103050114010809070b030f0901050903190e03070509090a060f092f101e0f020c0d06090b0705031806130b0c0d060b09 67
    0x540e00e01481c040034620118001e010060100840685606010003090300c14820703400c0c000507592055444901e150702d000c0142074115104070480b451410860020f40c40f034021b19040b00c20303841c205c24501605500456003644001d2000080f0b00c20300320009801403806008501c00c2a02005c03910507802c081d12410300391900649208000d41c000d0003201d0154400e0f00e90185001c2c0c0300d04000545c00402c00203c3e0902e0b0555000036402092030701041002400030440703001c1e15118400c10481c01c040c00751030000702c442002c005410203c401d444e070304925011540c52217840c404c40a03007090b2425044005100c4020104011000901c80c200d028039145141c0030741007550110342803000c5854101403000713640d810440d880341d03c2941035401c12000d000302e552000c0196a0800c0d002c86451070038110182c00c82d4000d54210104455074112601ca40101242c01e40c001c0300001c2400c3d92241058460743c00c080b80c05010703030341c03089410490f1403410300c254890100200403810710703643c070307000c040d82080140c0340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 561179829 1250 561178579 561178601
    0x304140102100903080112110a14121614180c1305011b080a09081b09060904080301030818030f011b05071a13020604060201061a07030203090d050c0d08030a 69
    0x42010300348070010b500040300c0d0f0b065841550b8032075054403131030420f0748c1d641d0843d8a8460300b09904031400310f002c4c401c1c0001405c0d507040565645505807040011680e1b1110a00b5005c180300400081c02d2103c290840c070143d43c03410008185642c0d070000c1c1c1040c034603540d20590300700c0102400064954018040709000c48c1c014002401c1c00d062500d40e84542d55814004014020103800c000a20071400e00e0288800b90040c05244007126010849030414001c650080b07003046100d2100310f00011001e1a2910507940320f20f42c0180c82c5030469185940b500c441da0840101e400d280071040c91603548035102003240706c06000c501800030403541c1c902d58042e5100005103110000b0010104603040104507400b00109020418041500e0304d0342d6400380c10303018034a040e030000758003440c0000c000500390742c1500300f402980e400e01c55015a04a643e40356204621a112004026800c02d1010f0340c8580b07012407142d0001c034010025103009210362000200d81c0070484808982e114000301c140074242e1828418088180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 561181079 1250 561179829 561179831
    0x12081501050702060304020907090803070c0905090c03030d0c1b060b1206100501080c070203160602010b010504060c26030907090e061b070302030c0601260c090718030203030414010210 81
    0x3902e6500030034440d201c000c0003e0701a505d9600490202c5200b0044000104401c6050300d031501032134504140380405900c202c070f00c45824840400c0b00c60344040741e80c1121030310003001103180444a41c1104041c24000140d41d05000d207000c04400c40b11082488221100d104080c0000c84c5100d560030403920400d01c100701c102950200b0304010b4680c48980389031013603c2090a0901e55995891f1428106110307410009400d4010740350302920003070054980300d0903034007150024032800c0d0328100110f849000d644141000035020017049404a0400d0a03640c44103601450340f51a031440c00c264204065000352801040d40c0e108200401a020389445088403042140e030141c15181000b040d0000c100320190000c820300100002c46004040c003c00440c1c0e0350300c84034415101c856954007117a6101064000c0f0741a207003021004981c0000d600882c0b00f011030040207000002ca0749485404880f101d0704a1b48400ea40450000d002c030159400b000540010243d07101c202e6588445440020300781044940c4410a107 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 561182329 1250 561181079 561181087
    0xc020606011b050c060f0a110d08041509021e030c150f0f0d0c0816050c06071d09010305030406090e0702060103021309121e1404090b0d1208150105 65
    0x9681c2c00001600040240d0680140080312401d0060400d07500075025940310100052441c2c01103002806015054196100c81c6420203c1142c00c98a9048001c07201e0000750b4020700203400905c14081c01000d101c407103000054800c940b90b0101e07105034100d001d07150490a0484013072916140c10040c1c2c1042c2841507821210004500c03400551500500000c0c1c44020800b1864140e0305080c842030704c0788161a0311040c07281c1404c00b0000381c01810255000076020300004a10303020b2074048c0d03080b2100c0c401c40030001c10f019540e9000483d4100e02c0c42c400c92000d4424a0507202c46a9101c1c90390034069402a8041c1d503440d407900c00e001d4900781048d404032084645500070003040701e030041506411640c041d02e040112449104c5018002c200301e0800034007d0100030104980c5641c003250140f1510b1200e420380c1501c100381c0c0d1090703c00514462410840d1001000309021015044c3c000321a52440501040b089045943d03030510120000007030100081c00134001c10850001510460039848402e00303040c0d1034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 561183579 1250 561182329 561182341
    0x60c010e0f0a030509060a18120c1505070f0804051201140703182913020405060307080a2405130c05010905090f2a0909060a080d180b0d020c010c0206 66
    0x50f4000e081700c5a2080001103032914000740942c1c00403e1200d01480304140c900e888888410141c43d503401c00b40d030803c0902d000400c0100e1800190790000c0c1c0030740c0360340b4108941641c0e00d5140e110810b0301112940800e01001501c1c1d00c600109000030b1010304008148503143d2409620301d004000c125404140c200342000721702d1496040006500c5812400c100360003003d0783c031500700105c00c180004038428529410807103980000008802c40c1482102c0520dc252a144c041603a100d17214010b50900e9008414000005241c2440d1446800012504d90008202009c5003104494040390400640c20301c1100503010010450110b1016010034202102058145404504414030003400000c0301a00d143c0850b102c0c7d15000417000b05400755500318401403481a00503410b40d0024842c00c0d025041d030201083d06031420b40b070020152080302e0018502c05011202c22141400300403280c100300482c081000c10060103001c020080303102000303805640e034140103c0711070854810308110b104540015042c088 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 561184829 1250 561183579 561183587
    0x1209031a04081210030f060f050f040c090f09050a03110d02061006030c1b060b0a0e16031d06010e0f01080c0102070b0901050903070e100806011a0711060c010e0f0a03 73
    0x143c81003240c0d02c440c52903446010403c0028950f030409007030b1052600d031110402901e038001c10960300340500c0911090303d450091801e0b504d0181c900411505188000788420a11179000da45c51032070500700440d0451554480c9400e01031000016000a004130f90882e40e000030400090f00c0300c1400d0303c02800c02d450301600001c083d80e00b60064030101a00c502c01200818803da60f00c4c0e158240700c80e004001c0c2d9a16103064001004d0041c030050040d08421800944a03250101c00c51248580c44807070802e0043c6000c4c01c0b070003440300d01c10440d50041c1e0018400d09201d010400380380a4640c207000c1e081c0d0b900704010b950180303038416806007116034031241a80c5143d0f42c2c086072203030807540e2114107a61221010b40c010380f06405000b1109805104d203110001d10002d0060700b10f8055a019a074002801d61103120176620703031000b4000c60042942c07600200da0443c02c458002c15940c2d0150082402000138003000840c19484184003409980d110103400040302414814800070103412001061400440e54000d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 561186079 1250 561184829 561184837
    0x11d0906010e060d05011d0616140d09050f0c040f0209030a1502191e0f14030405030f030f271005090f0a051b060304022107031209031a0408 62
    0x52a40e040b01001c64056151200a40e5203e030b0302c0402400303041e040d030b02c94a0103040c038040d400d1010300c0b400001c25000e185491580d41c5410a90ba40c0c03c0a211880754040001c4c1e004070b061002259030785d1440c6020820a00800300d244e417424028009400c0850200015501e00d05401841c20b4410070201846550004401e0041a44401c6c0b10401011001c4041d000b4050081c40d00400508116440c080e20340c4030420940d98a0700c0105011f40010b05903044484042140c4000301007841c0c046c0d5003048020540107103a01c28400c60880e03150488265100540d500142d580300e5120403000706001000c005030451814141141d044900000110050196250800d00005040c4c640d07401c041058500c040c04a035008110f41030449200c0c007641c1c1382060303503440382350198221500c5c2d084031214a89082002c6030701031034004003541140304200706c000100c6440c25403021246d11410100100246040c038400c8000c1c140b60f107500e0a04c80c55824000c584894035086e0402e58030300381c4100800160200156 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 561187329 1250 561186079 561186089
    0x240d02040903120609060608010801090c0b0c1f02070b060d050615011b050601050907050f041809020d030801090b120d030b030a0503191e140c2103011d090601 70
    0xc5441003450500343c0c0c1e0904528030321540142010004944055642c018800700c603004e0b030340d00213242e03642c10149089952881d4000d1040e00f000c4070801c05403110303001412110000e00262944c1a021031100803610003161006401d42d80c010410200b4042506502a031000c0152801c1140c5403556441070b86030f0800815260701f0782c100410780003c503441000040030b0b074060464010600740d0141800f86e5150001d1040c1840351100c4400508036510a4040e55800c460a048142c1414100103480342000007170764281c3d0916680302441005aa54a03503441100360290322007480035418295414240d52100c00128001c0d650101640c007411030000344070100880a14000680022503000641041901d000c058000e1201043d2110743c018020007400905500352101d0a445034284505c00785060f40d02e000700c0110f580c51200b698040003060007888000300f1074043d41c0d19180151103030f10021194001e05854910302200602410741190344800d49012080151003241c0b502420096440405001d4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 561188579 1250 561187329 561187331
    0x506041803031d0106091b0c1a04081207080403020106080c030a080708040e0103060c08160f0f030209100909140f1b120c07110609150906041a03240d0204 68
    0x1485003540e4443e9036124071620384900902005640711681005416141140d1030000030507145140040c0c01080c000f0a09640b14030020b0218401114079a8580380c000c000391150340d03040001000700c00c128100d0501c203070303440d071100025401c003410002d007100c955070400c12041d4081340054205584c0081c01d1080b156029898a60303422452801341414001c4e644402103450041001104100c1c01d40c200340824440c5940380c0405070f4815400901d03130400a400507005c01c0180e540d01d8a40e83c4500f2000305024503a090252034028a01c01143c050a00140c620000880044090103985441c0c00707a0030f6a50360030440200c003401e01140b0065143c41c086c0240740210b1103103c040d040d81d4140400eaa0140542c814600ca03503103012500451190f0215508559082c0720406200b207515200096888007800540808240310040400d06140c0d4091255654400e10600c0002401c8040c1d03548400c01c0d81c010040d01d9100c1c01e0800b020112034050100544181d500501c42c00340584520280c1706d4502d40480d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 561189829 1250 561188579 561188591
    0xa08180601081b0d0606030f200a030803090a3512070f02070302040507030b0f10051c0b062d04060e0d03200303070f020f060604050403050f0408060703050604180303 73
    0x100141e0860540c044c000c003500d04012001061117645140d89035068040c030355284a9948456440c64071105c1c80c03034825805000c22609001017031210b0041c1d58080c4a0000b1a5800f90b42a110340c00c80d80d03200410030a0b100607110031321000055503807900c8901c000b0122401d0501d060044031070071204004001c1f80800030f001035810001c5100300812002103402034420440e81c09d245400501400104100714014985401852030307e04043c5080380100c10075a0303455050001d0240c602000c004040b414401a5841e23020105403680c40344000c280320008051802d07030f607035042444c00c0241c401204403007020b007009010411206400c440714550000c0215101d640320022840e0542e4030400c0a80e0195028120b048400655200000110300038030241c0c8641c0c505039001c81013280c0d41c42c00d82c0c403190841d41004001c20345509040e0031494200b4030a0030b150f0708007024450745c0c5901c1d03001a4041c0000d45e0085040c490384a03010b01c00c881d0010401c3e2002e1100500800c061603135103450700c00080416642d18 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 561191079 1250 561189829 561189883
    0x20c0d050c0108060a090608010b01110a0201170c090616031b0804030f0c0b0d0608070807032f12010506100804081b070506070b01032d11150a0818060108 68
    0x500000043c2c6030300d0908118654440d54414003c10ad00c04015021a1034199101505a40050003404180d4142c0d120343d0080b0940b404100340003409401c4065004090200c038015640b24000350182042d490750b031031603058840c24010120005400002d011100c0d5480100c00306001600312000d4070b0b04110085032110682c6408001d403003441d4450024024042080800002960092402c40302c00104844400d502c92502d00d84511007403200030121030700014524400c01460012103600d181c580001c6504440000201d202040e0805c1400601e95542c5c041280350300e8014101d074001075072807800030300d146480ea407001d61501c1541c00e05c40300c104ca180d2428980050070011903010b010050555511440f103880c100c1800a000c0c0002c40700303c03400c0b402c40c010550142c1c44250b808514400020989103954481c01d0504c8651a40142c00150025102440c2c1100c04001d09400502e6074906145180203540c05c14002c1050604032140d410820040190300c60001d1485810b203040300440892000017 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 561192329 1250 561191079 561191089
    0x30316080721080c0a02030904150806070c0501110304020f040b041d1614030c10030207080f0d0f151a09090103120f030207081806120c0307020c0d050c010806 70
    0x40341c8018420814501115009001920004102c40280d241c8282c181c5070b0341003c6081e409070f50064001a4400c1c031402d042481c198002c8030606c013016a0110029807a07040c0c450070448100d40d0040070600010340c00c010070030b092007081d40000e008528141107040a030300061590180034240d91089031610b4404245503616030040d4002100c5d4144035041e01e28145c1c07040d4503901d04158069085c41840b1000403403040200d901c0740d8201e8020082c2510b1840002007024070b030590400d0304105503083c0001c80020b0305070346c0100400254a641140c07925000c0b40840165101610040001410455400310510b04121080c0a071000c0c4031406034065070301003000541d40910a641c5038880c1d0948000001e2180c581c0368180c4403881c43d914245544c000c8a0203405078802c1d0352008112500401c00302a040c040307503948400c0080010a03451a00c076a40100c6050550b060342d10110401c400001c1c44417241d010000c800d541c00d001e8800038034000180d1142611000042d42e00c80c18006450300007100c071380d10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 561193579 1250 561192329 561192337
    0x50f0406080a0f1d070609050906060307120204031b060f120e0a06050415050f010b030c13080307050d03150b030a02070201031d011a010306150c080c2a0901030203031608 75
    0x2030204104c4c080b8130b80ca0407000d45440e400480c0480c0518000070451798450b02009050715005003014030b0b6502c0c3c0303205005582c0c1c0000c02c40e204018003c5417015042c503040c0020001140a07000d0843c1203040315041c5000704071598882002d0229064450340010340100c00c02503102402c0c40c00003912440582e00c9402c040490300010b010b18941010041040901101c0b0812a20050790402ca030f5500c1c28170000d04e000080c01501851030051000400c0305980100400c268440740344002145030b51000c1c0765242d80c1101d441160300d40c10046940440c16410b105100c1030020360039862200314078001d189040f51001600d0781c0e41d65900000c5000c15640a600400007010405130100e41c0c4980c4941914024441030720020030440500c1c44955541d03100340102010303900c00b01d080035074a40c2d40040694101444407012565421700b07102c42d16031810144140080c0492801c04100d6080101118407411504103480a220740c00d900014000340c0c0f4000195a41009030060221419007a0304005550b405 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 561194829 1250 561193579 561193601
    0x70e060f070308040c090903050d0c1806120c0e100302031b1b07080109020f040c02160f0e0604090308070c030909090c141f14040b04060306080d050f0406080a 70
    0x1030002408010198440e000510941c0290041c50309140c0b01e14405094800c2e0503c003500040c0140700c4140c80714520b600071150b50300107041005c102d10301ca121140c0d449059600c05004681032100740c0080c0310b0701c2c1c060100180840e190501038038503883c000640c10040300c082c80041503400310001d0400480d01c042540d600e24501c00c00b50b209c80c08a005100c1900603141c40c10190b00441c1000600e60005000e05041c0c0c5a00510b0701082d0100101880010031301d26080c003086114480c01e20103900080060310010b13142100c290f102141c01c0078881003540703801514031406036290240b004040b031350000341a60002100d00c2c050101c043c00d428100d402203110780080070300c90f03e0908031108001180012400700c68a80100566040c500400c20090110001d9010342d8406e02c4030b550801c2600c500408203a01ca45c082c1c4003401d19442d44a6008660426000540400d503140000e00611004100e440421107040c540369103400f03c00405004640180d11600c02444441c0010820a103126004a0702d000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 561196079 1250 561194829 561194857
    0x1f0e0a0e01060f1511192f04020306010c020d0605180606030616091a19210e101406120a0809060f0909100302150c120304050102070b0106021023070e06 67
    0x58000042040c0c090f4400c0f007140c50f440741455468161780c0c00c0f813041f01c1c0f50804150014034140220148070203544000c10083c10400c202c141d820045e6210130112411a008107000035903490481d400542c005000182900325a10403010001985e50008006500080400a003841c00b58440c00c26a125103144d00100d000103000c00101c0d421420007009032600ca03000030382a0a080000e510280c44940f501c00b040035200705030801c410780c0c410407a040301c0c41d80e0b81c0032401c40342240c2c100906c1c44111589882c205100c03014074414400e091508141214101c1540005841041c4055840040038890261124001c250200e81d0750300c501c1856040c1c814405004d4080c113a0ba00d451440c00707601242c9030104070b10031a203100c1800c4103801d0b0501612542c81494005000040000a40189980000340708668540d0200703c42c1e0f00081845004500030a00f603001400c20403400640301c825507400815040f0280018003500c284a4605200030750009013601300700c4d481c2c0340110049039440c842c20984540d11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 561197329 1250 561196079 561196093
    0xb180a02090c03070f0f020a0b0910150807090b060a030504020607060c1e05091c0807170307120b0a030f1b120203120903151f0e0a0e01060f1511 64
    0x105060b0030085108155a64800d0418903207890180c079036140c0c50041c4001648110807490000302c2c4903507900d802518031011078509003800d000341c40c181c800f031080c0440b5501d0111010000590100050009001030207030034001c07405468049440c034020384070007004050301d550201e010354462000320f034007544c0c05c4281804440b00c1600013500c0e01d42c0c3c01001a20004851003584405403159007600e01c0c1000007020042e0498004009150344010404269071950080103014001100800504141d480007180360381c82e8505450098101c0b413a038081c0c01e55090510590b40c40303d80d100307c120020b0325841940c2c071141c0b034000e081c001440c0302d0041900750441d003050b5011441c010000700c032088a0748210100c0b0090788103c00b860610f8003a171500079405611050003240d001403485405603215a5003010f096a139000d1014003102c00d00254850203500014078140f10801d011402010301940d50b00300207020440c5000d01c1c00d640c1d204a48200020700004100c9a4455440761013840345000103001201c0c08 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 561198579 1250 561197329 561197341
    0x70515010501020d17070f0207051305010e01120f0305070515010306050610110c010c02060c0601090203150301150504020906071b1e06090b0f04050d0b01030506060d0b180a0209 78
    0x4558400e026940c0075114018507000d0341440303065100759040074040003100b00d032210300d0156100300340354810740107502801502080e10788809000300d070315007444400810607500d800e03003168030080181c1144022684410340100071030594510b00022540c107140083e82c4011604100d4240400c03a070401c81c1c114600b80c000824414a5045180141822110100c040b100c02d42d041c1c03034200c0c40d4941b4402c150403826030341e00190300803041d0b0520380b030010340145c0c9042c110540712410184241c006000444e40031050000f51b0704001003e13401c9001c140d008024800385003010030340d44203840c03280324801d0341c0004840310162900c00c107070341010390300640515a821040000c80803e101d28000d0207400d007407038040d401d0205903da112004450b0103488051026051041042250b4800401d1400c0b240c0d0400c40000d040c0c4440160b48003440c000d0058004650562038002d0a0510203081039100b00302120088010514114986030080b0380c00e00304030080c110001d40241804100c0360082d61200c540b00070401 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 561199829 1250 561198579 561198613
    0x80304051e0a0b060409080721080c07150c110f01090b09010209010f0e0a0b04060c030212030c1602150705030d06050901120b04061e060509090c240705 67
    0x20320010708904000000d1194080e0340d58040324001030040c0c00103c01003451410503074000100345009588052400000b500d40c860700070701941e00c028455100000307172820351f503000500540103040c1406e541e103080d180343c4502100b0840005000230150b690450040301c10700a00b840ea00d508054403d48140007100340d0f0050003021640010341d00200c1c00c00024034114010302c201c0b4081c640585554441805501003210750032403034011030303800803c00314001c0b95000c0501c0181004140d1030b507900c690704805140003801d1145941d59020300f0756041c400c0c00380d480071010642d91892002c2004066003182c0e4000070b11540c1c030316023100c0a003000c002015000e008000c4010010100103000500032156a4010320032614401d11600c0502074080600d0800903103403001094106006500c0450303c0350311603d10081c48070846082801080d0764050400944c10903041c1e259201644001501c41900002c0c04503501a03078401920118134148083c0d00380980082c411f48040c03d03005021590804122a9104 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 561201079 1250 561199829 561199843
    0x60213031e050c090402061c020d021b100c090b0901140403080909220215070605070503060a0611071406040305060406060906080309010f0e150f030a0c081e0c0708030405 75
    0x107940b600810801c04001c2c10101229400b80b540500120310304021013223002d00750425980e042142c41e07000c12181c00d01d030226001814900380740581103000111429001880c0c03d00061100010340c1c10802d01003503107a0085010341c11201c0d0000007a81c0c0e0180d0030012268408100280c410100780030802009200450000c0c10486400740d0300c0240715154821600e80d088141e2415400f0485504080c0c001420031301a184a000f21001d040790805080c1d13602c42c010341e4030440300000010404810045140782c12600400146004c2c142100e0a840074201c040d03e0300c05ca07028110651038031080c030205079142d141c1114011034010082e5402810103103400c0001d040c3e140f144810311030512901007800c80340170040720501c10050716541504069081d090703031600c1c051000290b00c00b841540c201000d0611400505a150000a140742e076450070f10024411940f606401d041042044001c0042e0800300d4041244414a01503038030066540e200203c0146c0c0c0701e40c1d44020150900401400100b140015142c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 561202329 1250 561201079 561201083
    0x60f060f0a11070e040807030c02130507020d0f020c1002150f0a0b01050c1b04060b040608040218040b04060921031a0f010e2b080a0f05040b030103060213031e 70
    0x401c0040b034404041ea9541034502424200141250202d00001c80c0c0d0002040600d1180c03c04130b084104540014006a42410f01c00740c6d000d40300e40030000001c0c5e05216282c041920380c180420f80411000b0025a90502c03400d03600c0c0101d49807943c2d0110a03000300b208101a07180340d0701d00392039407070108420307485110241d42114a10b4104448580998040c901b075072194910ba4004114183d00d10011a4231a2200021b45400994540307000c03444061590003400a0059620b8100b002c2c00d240c41400b5500b8984041c0300214034104040c003000611840c44c542e00070ba00007101081c0104e140c141607400001c4c03404c101c032180c003500c1c020400d80e1760035400c5039401c9868040811101c01400d0240280d41464200b03007030009400c410901068039214010280c12803c1c0c0141001c0520006161422001c00200c2a0f400850204160300ca080d4420303030340f415140321440c24605203850042144000d000600004044a402188410a40801c84040b4000310b4000d66001100300703000b0101c03004070444901c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 561203579 1250 561202329 561202337
    0x30c1609020a12020702130c02030a230306150405040911030d0201050c0d0911030105010f0f120f020d050a0c0e1816050418080c010b040609090209040605060f060f0a 73
    0x2800300359910036a102051a6100d01c24185003140e0018000e5011460480e0702400303040d1011400c40440c443d090140c1c04607001150341e010600c030003500400c13003215940c540c4407040a2a54003041580c080e00d402000c00d454002c26018207280400c042c1c01640c00003500145000d0a031810b2054400c1ea0381c1551106034155080407080d282c2c22400d1f55070894501c0003a1b4070800401742a00341952080c0c60f030034040d0105241c91035800300040d007034400a80c40402d61b0f40090505100c04080c28030000000c0c01d200103d0541030b82541e41b4050300b82080d03c00a13101d40d00b4840d03420b0601c2401c0c003410f100c09a100340b888003aa41c980f40342120528080d183d0000c0c0d44580c0d5843d0349005c1d00010800d0f540001c1c00581c10602e0b2502d010080030705550141c24200c06448240f00000481400140c403500f031001001060350746849081c0002c441c4158402d840807420601200d0140e169040080e81098000c68041459030783c10022448800441468030303000407000800300030380703000440a404819501c0c6c0e1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 561204829 1250 561203579 561203623
    0xd0f0302031b0313030b07021f0605010e090708010603180f0b0a0e0a05120c19080403111005031602071701020d11030402010210020a030f0606080a1415120f030c 71
    0x1045070f0fa2400350b80710345403040780d007a4424404200783d51861030340300f002e45c81181d0a01d03481640004480f060108160b13504ca445503000d101e250317001411400c942030300703481e0442d1900e00500010401a010310800d000c1c0f41d07840181d84802d410303172114030320180d40214150403190080e103898200300404583e00c561701d0380740c003814526060011900f00d802941200c020040c181c0c05804000c555030014580040d00e1060400c0303000c55007002502100400c0c0030b040c1d290b48452440c207107180c0ca032000351061403080ca150a4103450054000003501d42018544001c64046401942c003a450642d0940040091a650b100d0b800b4040005400415080341c405109011540c1d1100c1c110007a07000a480090141c3c0044a511b0401d20300f40d8054510071019150100f00c12880c0c10241082342c515420040004924404004280e00e03940208690007950303070b04180f810314016221091740c04c0c66800081c407581c9101c40c2c20744c03542e104006160b22842401c0640e69030303161180c88a0340c0c48411941e400d0f228220710b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 561206079 1250 561204829 561204877
    0x3050603061314100c09030b0106020303060109090b03010b031e120906031909150f05070207080c011d04020301090605012006040221060403030c031a0f010507020d0f030203 76
    0x42800740c040e6156902c115607020b403583d83d00c0d00040c00841c148440e4414040907070f520070464080d0104200c941c1d16a038203002d046003002c400d207500580081c0190360003001802016603022144000307c80116000054403160200081d0151408220450f4144074810448001080f420700f007005400106044814000548810990f103000380d8080302d9112400748002a1108000b0840c120300c00c0007210001501403582d0b0b181c1c1d40030102040d40e510b0307413035545c0c207150049080741c0304080c1c0050040c001440b145190803500ba035601c020954072810003000f4000c40480d000c044401e10070803080103000755117941e152402c5c90010031091254030700145040114440500e04903202015007407018000e055240e40307a40074080340403540007a82d090795070988150855200306003c3c490159100303580114030f0810304d20780102510452800b102d2100404c09140c503007035460b0300340b00b41d991800b802c065440e1110f9000003800200011030242401100d40c105c44205a40800181022034200002e424143d201c0303 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 561207329 1250 561206079 561206083
    0x50115171605032205032505060c220b070201090e011d04230c1e0102100c02010e121c0209031b12010609051608071b0c121203050603 59
    0x2603600507441e10118144140482c03140c1c0003141c1c03181c40101c0103c01000602062504041d54560580300c50f04081898105101e403419101c0001101e65256000045580c039203e40307a840280c403208030804000740c801c56510424a030000c021000036071050401ea620b1444d110940c0c010034040b400241040d40104070044022070060607501c40003212880f0001c201c90342e800c0d1441c090400e90f03c1e440004103d1f01488101c1c140d511000543c100507000344e13502801403041d54080903516a07003401481d00c14440f0346e68000b840030408500c40d40c02080d0040b118405074014038102c0b25082150082c418100c440c1035040c2c0c000c003413040100010889000303112040b10f00300d002c2c0001a50345600024108890134080440b072000068005101200c0580300c0705002d421240c50b580140d14242e110010008021903d000c500c4004803503080c2800c0e01d10300b40d41c004014000088240d000004c6240d080c40601c120800002d01400d0645052403848a95003042e2032888500d08442000070b0401000070300038200 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 561208579 1250 561207329 561207331
    0xf0905030d06081603120909090f020907020f190c080a080301031e030e010309061410080c0f030601050108180303010e160c0503040501050a0e0a12052505010c050f0105011517 77
    0x43e16100204985c10350707031051a1501c10000500402106220210304e018080c0f00702410240700c3d10310581040707120300c10321100c418000c240b00b041d5040106031808144d00450403002d007a10030080c41d0000c50243c0740c240400c12141e0480c04240c401d0441d1103081201840c02141a00d00659030209806104000218070690b1483c0050000d8482001c54400754080d07080b56a0302845613901154442c09840c0c1d00850020481e40745000300c202000070480d070041800050000f83c8203130385000d040c52001010942c0c841040c41501d04201d5241e00123000c000b900e0348012460400c4006403640ca50b906c180600b44544152100101902015403102110b4080c100841e481a4090061400d05181c04010b5803075400001028042c8003040394407504590303404c82450090641096000c0c405506820243e19002c15103070b920582c025040310300c0c1c030b0707240390481e00030100c48092030505145001460034900b045003800740b0340c5456007000300120781c200f40210141d040e120350360380301070000345501c0e418003103248 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 561209829 1250 561208579 561208603
    0x1103070510090c0e0403090504050705121618051507020616050307060b060307020a11040e101b080c030402040504030e03150708061519090b0a0c0209010506090f130f0905030d0608 79
    0x201c81f480c10040c1c0d00313054200650080d05800d046007000c4049c6a00e26043c1c02c115010007250170f00c030069250fa913400c00d8542049060b00c01d00d010b02d91b418480072804260080d0311a1501120100304441196503000c200c482150305190700a042c0c0800780392003545c98004202c00c6030110f080c00c421151508058056900c164000d50003050300c1d11503a00c5c2d0200801900070fa694101d0b0311010110b2218004010003458202030200000b440c410010310344040220032041d600401c450340041c400748504000641c2d811940444000540b42c5075441c00b9600560700c1e4034131940501400144102c0364060b0000284030344450b07100c606040d03a03502c01304030050090211801200304144a11140b00015000e40582c64041c1e06080345159198030308454190060001c1750001a1b4007401c0c6800c604045400b06d00420003650541c0c148200d400010b0003000c0c03014035032401100d10281a0742d46200f0354100c0100d280784142c04104181460420304d03241d60103400e0803015541450070016030320741e0000e2b62101030ba03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 561211079 1250 561209829 561209837
    0x12040f0e0910150f06120c080603071701091a0a05011a070b040812010b040609080c09010b030a090b01170c0d05061f0e0a0903030c0c0804061103070510090c0e0403 72
    0x10302105030712801001c10fa0b00038440f50103690008500f84904100f8980034140c180c4600182e4102c1d82401400c0d20700e0200104100501e91045c4a2036880c0018202c00360342c0390020000903803002420321801014803100281000780c01d03890f5286806280c91b640c5005101d5100140b00c260303200e000246402e1541d40701a4803400c2c042020f171001c159004443c940033440f0300c0001d4030700380b540c011040c206103007078001c000c2001001904000d080d4001c00c5000c020602440603181d54604400040c401440502c43c038000000004006840c00005130300070003140758841d440080719610f64400000a0450b01d004204c81d00c03503e03245220703610f0007110903070b1a079500c8401007141d680d40c02550868014103003040c0640c0703514200301084102041e02c54900c01c208186000401e5020f604004003075442c0c0303078540010f0100c0607142102291000f8211020340d03160f4184039100c01280c40d00d0510710320404d10060194091681c0f02c070300c1e50550360061904103005180e45c00819031102442c0c211510103540c024049 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 561212329 1250 561211079 561211093
    0x6240509010b091f050c16030210120f1401050a0504020304050705270a0516030c020601050420070b0105010305181507120c080402010f0f080402061b12040f0e09 71
    0x1180340c4000500c683c10001e015040203600003800010f54140340000200800c1001c513480d81925001c12000c0b07581e042011206080354a03540100e01c800703c011800004200807490701c46010365294121601042c80440c5c00c00841002c1c840141818500b030068620a1400c05c4d40000c0d24502402542e0041e40c0060103000d03410f24000c204044160060350052010940d0070501032500b90365001c59101d000c03801c001003210b00d0103550a14481541d04c00620a140c0b912001012056001580d01d040d60740c180d030700007410922602c06996080c030500060200d0007002403807030100306081494a0403901c007a01c05020b5511021035240108030b88000c0b04407140d001c4050601c3d1a400207114507041040e03400c1a2500c0100c041a21007a01c0c064095040070480010a202c210359000c000d21441007000e1900507841c0002c07590003001540c014102a02c42c800c04102c5000b00c0c00107010480b004142402150b8802c8081d400035041c54100d0300c10782080c8802d0300030000302c2203800d03402c1511499054dc041c01c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 561213579 1250 561212329 561212339
    0x160506090d021f03051605090906130c0e121f020a0e1302071a01050a03151b111009150504170f09120a05071802160624050901 56
    0x425084030314000d80c4050840040c1000d619100d9160a0b41070110030b0780407944500000c0581654800780c14090000700e002941e1014942c007101b52121120215503101c095100c56002030102c0d003000080d42c20303180ca08050112099001030700400030031750544100481c1d43c04440c1150711a90038105034202120700c1c10100c0700180b4594002c10391250b09041c0355413606a00d43c00701c0c807202c0f9107144039091181d00081c07000c184005a0805440c007951084601005d60604003c80e0034201340c0c1c400181400704410701c54804480070b4022010340395400c44064941c2c001110700034114150300420010714011080042c0e001402405460192504101d41030f081049810001000b4100240240d8403003003220b03040501020490300030008031041540e407644550103842000584011600c1c62030703642c1d106100030030000d50007140c01011201c500e44a40d032100c0c0c81c0e110308000381c4107041c80051260341c8110314804100c0381c0d07480300c05c5400720030b260803110005021500308608810b000c0c80b6070102940c001001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 561214829 1250 561213579 561213589
    0xc062d0c0a11090f0f07020f03040e0f0a090c062307060c0807050c03040509090f01110921060408091c030c03090b1e0c0109020307030b010905130f230609011b021605 73
    0x50000443d00c100c8c1d50b03a00f054404d840c00d54205400403400102d901f414850440752036121950417492421041080407281e17075401d403c80401b8842c01041c00a0841c80141d401c91441d0710011420403680155a07030152031800200034480c074005030700803401c0103000c40c581d00d1080050b241d81c0c0d24182c004520303090800040100310b803001840400c0d584a050a0064450700c01e0080c0e1140c5c0c90040020382d01d40d81c203030040040b4548001551503920218094407148007000007030180c0c200e170304038240955403411500403030311104050002880c1060220307001400c0681c001c0740c1d00c1c10389010b65911420700c0d4940021862034400c0c6501c2d1030210141e001c011799030009074001480600801e5000040784200c50380424207007011980140d42542c0300030300403c0203e4007400307440c0d03006000009075050210313a580c4040461207829806000090700114050b0307000e840d41c18816036204020110f62282c540101120301030607510030f400c0304121500500510890001030644000301c614990f2082e0b1900b070400303100f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 561216079 1250 561214829 561214831
    0x6010e1005012d02010c110f100b01050f0a090e162708070b0d06080307170306030709050c0c0c03071203030e1513030e030c062d0c0a11090f0f 63
    0x3035059520001c0703548040c01c0c00c3c0900310315070900703400200f0702a42201014018001e0305030480701c2a00700b980e9010441c0004540c2c50000d13001d800b000200540340c1401202c10380506112002210800624101219000a0101d0469201d40c64130011655100501c05409200314441000319110820100c03290440d440001d0090f03800f0039089044d15900d0704050f1800c00c1c2540280950040007440320440840340c0600b03c06001307160021442c121032581c80310702c01900e4203e40c0b81c804401001040d003aa8060001800414101d20144a01c1c00c110005180b10380c018101000c592040d0007000f2090f040215620045030484132071540309151917241a006000b150741000d02d01d02545560580c0240701107042d0740543d4900800c5902041c85113005809811b00200d0244a54002d1010303109545d10082240c0c0b01440e45811b40b0005416900780140b100302c2003003248034070800403402c400600000600326008500502801e0048044a4180a6038060640780813400d00f402d8000900301c07150030200c007 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 561217329 1250 561216079 561216107
    0x50d05040b120a0e010204120c0519150903050114010e130309120807050604080a0f0206060f0f0f0a14040606030203060d14070305071e0603230c0d06090204060206010e100501 77
    0x7044550300d190190b0b0880c0c1c4039403c42023100b0343c80400b400522654102c0340018010a462080c416503a80b500c0d0a038440f400e2284001c441070300c0b01d99400301482500060000c690005c028004428103000071a0352440074000c1c20503241c11400011842e02100c0342403004150151a2260b80b181031140b0400a44450841990302d20380400403103000400400403540705034010344000d925032042e81002084000462011421035025030180440ea80c1e43c1d2103120700f211012500980d240b2040d20226070840740c40350b030555100700d800f00c0005140c07081008a8040c00d900b11020030031140c40d040c05074101c0c0810340d016500864002010400150301c0c0d59032100038a040e800f03c0b1a019500c4c3e59192900099801c03030b80d41c0c011030030355002d0000350419024000d0441410244504c00e040300c4400140803461030644002804400401d584d00300c5c0e0811162409240c4000b0f22015848600e110041e502074454080140304500000900c0381d01907200c1b80c0a03210010201e140c140c5890011200307009804a4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 561218579 1250 561217329 561217331
    0x9050a09050303010314061027061d0103020f0406030b220f06020d1b0e09040311010204120b090703080706050606090d05060402030d050f0a03021605010c0c050d05040b120a 76
    0x5a000314800b00050f41c001c602ca0319245c2d04e004040500700e0300b80301c4041d11034030f4080d5000d1020300c181d082e0514092000e00c030000002c031510f0308508845024100c10b034000313940340801103218000c4040d849900c1c1d069900981d129129103801034144011100c09210103090400b9040c01700300341401007000ca014419004c0c1c990100303013010b5100c01102180e102021200300d64000340012030400300f4001e5246408070b0309420210a44c80f0103020389803501c1c0c4424944144440400541014056101c01400020b890000c5440d1921010100700d0b10017141000e850103491000014401d41c4000350aa09030b13079108034031a00382866030303444402901000e404164881400d10149020b62920101d12400303034091001803150303050600515080c911580060010000100306078803014542004549030141030307142c01a9103403a1254034003002c280c1c10f08000c0055081c000201e0030250b005401e464440c3c001c10588241e1280c800080d24244154403454039145024441c054510038002c40b0540d10094502d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 561219829 1250 561218579 561218591
    0x7180239030f0a1d03031204061401050609010e031608030903070b1305062115090f060f0f011809200406020a03030207151b030b15032a070501020315060703080109050a 74
    0xb0b400e603003120031047c402524540800050000c40c0c01500e8030340c0302203200c00c5269410701c0c011031403c0c402c020805051020841d080c0030141c41c01c00400c42111040640f0030f201070f07111405148c8035485408414800d106d40000841c0568503442201c0f80309074064050482e040c40c0400b0700181c0c1d0002d071000c0003228035000070968003c50090010303101c0c039848520b80515904280030003d0614000d030442040c01c96450410003140c90b1246810125541215010001140040100d4022003816a0042c2c00c000c1e10800183d00c0da010342154240e045070540c81001c0f442d141c40c1003092802584151401640078039840c1e804280607500604166000d8084612410720006201d01a00c0b02c0052981000c4041d02c060311041e5030520650103c10000c4407402400407040c2d01a60150001030282400001001103032410803843e000765054410700c001c11641c90f002c3c0c03400c02e14001e40080326816580d061940c0f21524615040c001c8481c41d541c161154100c0d43d0900030701c04001c3c00001d0025441566510b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 561221079 1250 561219829 561219887
    0x180a0c020f070f0e130b07181415090402070501090803100806130f080c160906060c0b04060f0603020d030314010e0c030703051f090b0a05090907180239030f0a 70
    0x1d2102c500c141c00ea40c030f9040300a941494000031441c00349d44518490030811200c03036205d6a641030382c96801d0754041081a20382001100040003880750340d00c010b00961070320b0204400c01203980c0c05180700301254042d003a001507951100a843d100708840d1042420440c040d4140010303185500780d00c42a009000007030401c0922a2140e180c03c031107140b07265015256490800c9503080c140a8400606030b80e00d4036440182d11380e92001e04540d0081c000600180e11821f03010716000082e03014500450300140000189006418090020603942c040480384110540021451000701f00d500c030300551081c00d2082ca165142d1608900801c4050f0490350b0003c0050007003855440b03c0c0c1d200f24003621407601c2c00100300070048200241c41e6803035840317140507001200c00c00c8034840340801c451040300d2501c0c05228010f00700141150091040200104032a4041c407018910880c081003501d039020000c04840a514000f02c40f030b5075490146240040100d601000010a40751084c0d554515407805482c00034401c104070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 561222329 1250 561221079 561221093
    0x3031d07080d0528020a12031a2701060504080f01090b0408090d140318040e0c22060e0a1d0c010f140d0203070207230d02180a0c020f070f0e13 63
    0x200d10000c010f81c06410500c050120740d019070b15070b41074141010410a0300010000032940750080f44180b20303049180ae98030002c4007a420686203198007000400751907840d1000a481e03504a801385188611a628800c40c21110501c034171452a41c000d225144581da0301d644000b1198000a001504440e00c0140d1030001010481002240d1708010040d503260351605c0301c443e0038805e070750802520443c00e140364511030803004120303034032161b40c141ca103800b00084040310741c9032081000401c5842d440ca40000042c0c030004403000c05010311138100c010722494072205544012401030310300300500c80d004514070804542c0101c04c0c80d0380103c10b60502c095000705806400005c2d401280c0030000c519000010464200e9041c8441c0300a48080200c3c0c820a0b00e0300504900442c9030202c64501501c20301d01c004c4150360320704e5854104058045091251850035540750005448802d0a0030054030941560108244003c41c8480a4800c810407130104145016a05c0c05480d1010300701410721490340c1c8010000c1804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 561223579 1250 561222329 561222397
    0x7020d020307033e21120901030605031605060c121917040c06052a01060315090f170712030507090509010815041e03031d07080d05 58
    0x914200e1a13540200380e072510901481c400d01d1042c80c400000950350010149107030403401c0e1000e468078800007402c00126240d00141d03130b4001d1140e00c0f0f52501d00e101000780320f0050807002401ea80511241c1c1d50380d42815915009110f42d0840d0007030301c540500c06802d01c20058600e00d6044012140700005a12403880b90391312114003030300e029206032407000349c194000f00502d0035000200c0c1d8000c003615245d00c5001d0340c0403607130064004001000440b80c03401640707054074000034455001c403040c04914040b80d03640200014842180c640c01400c3c0650f498080a01c5034040c2a900030204419440d040d59580705019000100c0b441c82081c2403009001142e00117407006450b540c0d0b610300040320305002d031000d0054010340e485540709080507401888982d0b03000c50300b00c81c1078404070310988142d1254600004140d541d41d40301e2484007140d038009401d15038150440300a4420340c00117070740f0740c02980415644508107401000b00070340c001d5801400c1948604006d110f10294650140d195580c0e04c81c403c406141 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 561224829 1250 561223579 561223583
    0x1b14011b060231050603091002030a151503050a06050d080306040212010e04030306080109021003091505070302040e1302011e050c01050703020a0e033403050601060c0c060203040b03010b07020d02030703 89
    0x114003c00d5603001244043d0040207001c1c1142e016085140040360380b0342e1400e48514142ea40c5030040082486810300c2d400889032640030f1425501507903107c038150030512803a03d0000c070003c1c0c1400702003901b40303180d4401c01050728009007050103009816200c0004540c4083c1005401a81c00c100c1c10880d590a06001400380c0b4504840c2c540e035007802e040090540300b103a005400300e41d01d0120f10200607030b1070326540202d444290502180e0b03400343c1d08001c0b1411000d182c043c440c4a060200300150598103600900135600c03813240d035082e5925450409410110b80304c0b0000e020a141d0391011854035100da00d0140e48084900d8075a2070824070344010707800c4d940c060721500040b030303000300b00091040c0e0000108440864150014030702405c40c0000500d0800c4907100042502d9070b040c00b481d0204500b401000c000d141c01c0801c84449503591140280a6031501a0030b40302074824443c04a020384c8003100316001c5404d0600b00c41d0440c0d003046001c00300c0d0b601035082240c2c01401c207003048006880c103201d2680114 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 561226079 1250 561224829 561224887
    0xd0218040501060530060f030307060c02070f08031606020c0a050a0c030201171608070302070b0f041a010305100c0302091905151e070303090f1b14011b0602 69
    0x180c803a103110396038062681401d1441c2001d05040400002d085d011482c0d110301c1c202d82c951141c90305180882e06500c40c1c1400909a203007800c0c020f07018140c00180c140b080300d0513201e04108003540c030700a540d100e000e00c801c180741e603c401141300c0300428419006003510414031019203c8540d2076540d46458050300c3c1c1030840c3c2d182482082003041d5070700124042c1c00180d0352824401c25103051400840c440e01a94054800d100040c4085002c50707100b0390544014960081a0407450b080445034901a450700b11303400c40c1c82e05101c06a80c0c08142005c9030041c1240d500c4801041d0b6410303c00e0188003c5c01d1481c030000d04065003802000610381d01c502480314200b0406404500b41824001171101d01c0c41b1040e81d089000d10308204014500001030203203e0803100c58482146c4030740c1a494128050640840081c00c9010404d07100424000a4507040c05294103002400801580c0e0300f452138030380400c10b0422804181c4040c1c1d199014500381010048581c4188801864100501c0e0b664204030354100d1504425 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 561227329 1250 561226079 561226087
    0x60c0a020f06240405273a0203090a03061107060603240b06041202150418141501120e0f070f05030703020d0f050f0106060309020102010c090b0d02180405010605 71
    0x1c80900460494140340982d4184003d03e000001038a12028200c0102c17251b00c06107007484100c4500744681903101c441030020701c4511000c20310a1540301c00000402d607000390419448855107000000b00d030703d00315014050019503455500d9200080002244c04040b5040801079500090300c01d01c65900511722699583d180782000d9000c030784449250411100c2018a40315041710250380300c1d0305580440360310080780140c01400c0c5c80403488221080705a462298070104d404204181e07101c00d00091704103140c1082002e4072540c010903485c008107440807003c0843c0c000560340d19522440f515007144000c408081444d0112400d024500756071b0000110b15600310140500c602c10b410141f40300140300031001032a0b401d0564000449000d090600144110705011120003041800d105502d10410ba54008000079561900302501070840d48400320b005520f00001203d116010308001801c0d1074010882e41d040402da5010343e002544548003100c0c00070007110442116542e03601502e40038002e983c0d111612 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 561228579 1250 561227329 561227371
    0xb1e1c0f050a0b030703031e0306050d03031b1e050c0f0a141e0c22020c0a03080109021c0b040b0a120b1806150609180103020906040608060c0a020f06 66
    0x120f840005010f4070030382040c4010004641d10229a4985020200d50817299104000f000d034020440c40d401aa003010501201c1c0c4141900342c0e1220242c40117501500e40641c48100040315407210700b100600054450103c1d001829208001400642542034100c0b15401c9804c20b000e8500030340e0801c100c807a1050072210403840300007441041030a41c420221a0006a140d03152a51140c4041030102d0050080a090380401c20909050340b1000564040c1150798100e100c0b049034980300c5117001a40854060000047e440c0d007035108840905d014240700d101c1000e15844064003400d0340d41c2c0690340c00782c3c903803429071000d03515031140300000e0502e01400010707006d43d45092600c1600003000c07000d00d15203140300a07132141d001282c80f41d841940035a0715001c403a94031001904034040d030071140d41c11034690710451041040141d40e281c1038038002c0b1070301704040d07a0311410401540c1c4a40a084056080031b8049a4032159003405400f81d00c400c0d005507403201c3c030706524062800d00100c0c4c40780c0078244410501c5036 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 561229829 1250 561228579 561228581
    0x20f040f0b040f0903020a060e072601180305070609020a0b130e062409060d020406034b11070f060606080408030c07050111030903040f0b1e1c0f050a 66
    0x1c0203d00f24802d004c040542c1c0c601030345034045540d0150141d51108040c1c800c00d40301740495805001e00d109400c2850584c079809048110f4180202031566182440d440c0e100741c0c0c04070010043c1a03165940502d0410f05690b034401402035580100e820032080c004c00b1a00307890394006000c03c0003c0304ca104480303070716205c8880d0b02e100300508410b000f490104044a85400000884840d0481c40658655512070480209400344203442e03200c204c480c40840c002c1106a4141c2242862030740d100b091a0302d006c242007400075003a102082c809030446071540c00c00c440e1071450248820601d5040e01c0083c8071100300801030841d620410045520140138071080f010841c0904c80c45000d0500d62428045901e01980c50101512003c0d100c841c0d8841d01160300020000c1c00d401c072008001040020720b40f07a04003900015500e401c0b5000ba05491f243c03820021400c8100003042d54449001500d2801010201402040c05030340080440f28540000743c60b200b8225519000d40c2c1d4001c41500000540c510f070110601d4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 561231079 1250 561229829 561229841
    0x3020a02060619060507050c130b01020c04060f120206070209040c061b020609281503060602010e1015081b0f01020a050604030503150d0501050a1503120507020f040f0b04 75
    0xd11465803c449510100c000241100075544103003040b0f5600d200b03908010f841d10944401c1e81d03a2010780407610380b42214180e08480070141080e0225215416810104170542e4641c0c0074100440c000804100004040d16a40c48801c40c009030040d45010146d40210740007410449055440716117203401001140d600542e8040d40c0f4070346005801c0210140d50020b8007030312515510a01c10f61552650b081c8100e000034522a041140700b44020302541e66241c4051051082005400442c3c40d125002546038018000c40c83e141c50560090128168010310110007042204070b02d542024080c0004522000c3c1000140304a68407035440c40f801d0780072101000481040805014110b4004068a00000d20005000c5402a90605005480342d07507000c03880c0c500380030f0b810030a6401824401880240041076000300d0091704111428880d020400202c0c0410a0540c07000400c41c0c7c414005e4881454031842c064070319070344018450155510311030001001c0d10444103110001e2503a601c1040810710b058070800d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 561232329 1250 561231079 561231091
    0xa1503020a0f1a0406090e070e030316020f04020a020a0f061103070305010801110a050a200106030819080103020603130501020d060902190306061b0812090d170103240e0d03020a0206 80
    0x620310705802c085000303014440504c6580c0b0107e240d24085816580550404040b200c1c2c080c007201d44039858032001400b20070881c0c1c0141d01030883c0390111009030405000b11503010801d9002808090202c7c1d40e00c0728602c0c1307464070969400f9643c82c920104454000011801101113a501180c0b55041c0700d41c186c00c50708512541548074104004898885800009492a05407107050040000c400301d991200c101c2c101c2800c401c500c3d46800b03000310030800b40d000505942c50041049292040522030243c601d060203000280d404101400010821010340c84658042c500c100009401e001c1c07403811010540742c441c7c00141b805030b00403516050002e0160328072108201c2034039080c84101d1030480b02400c04144800d10040a1f0000d01d03403481800001170841d100d02d82c1e8a203101460346841605030f52910041200780340010381803000e0341303103101c51402c065059a800410381e140343d0610342c0c07040c0740060b00c529002e01c0c515201c1c210401080c1060042030344038980b5803005071307a8110b2110001c0c241040180301c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 561233579 1250 561232329 561232379
    0xf03070308060603091e010212060a06050304140a120503160305010f060302070215120108061b0a081e041b2102150d060902090f0906090a1503020a0f 66
    0x10900800d90041c0303282e40040301640c61035500e0300d40030002070034000100d05181c0c102503801e4603441020015030080550610b41160f1a020342c4070b03442000000a403c2c810500022003d00204000c284a41d21b400c540300214001c864802c00941d84a0007043c602d5104000428400b104101805140d0140d04071044190310b03040210b58105502441e4004440c005c25003010381c0443c400d070841d12038110b441c840390b5a01c001107448200c4000c508540f40402d000742c2c002400f48401081c041c1204081009801d100d0100550800b40d0740c000444000e807004000f50409418070f1100c201802c80c0f40400c83c02180610010001c90041c0885414070448561041c030281c00180c1c59007401110322500310007450303412682c4100d5240a200345107600c0c060b02124054071407610000290582c0664010034003440192100440d131b40000d800c20403c660125a00c5421002d8000083d400b500154025206404410400c6005980f2900030485e01d54413500300c40c44002281c0700600400344d83c0b01c1c1030f1105030760342c4107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 561234829 1250 561233579 561233587
    0x10914060708181e01020403060606050c03091302040b0703170108150a0f0605060c07080706080f04020f061e040306050c070f03050c01180302010f0b09130201121407110f03 76
    0x720040003028018402828807844240340c480300789050000c13001c1d400b0300c140f8180c000854443d14a000b54441e00c02128039629005000034400c3c014000d80e900d406612010354100b202141c18040340c004881d9080c44510b9003040f0101d185146400038000250003590380c0c41c800035201c0c0786200d0703010061308040000d0303004e01030310a5064000c22200d40d10046102e40802c0e088112058a00600103e030407040c0d0102000c0b400f00400000000c0c00d500b144c2140c8210340308950769241c1681c11400540c0e000303403c054000000780150606241c040c22048015260515050741c00420070b41d004c10300a43c03600d07030f0301001600b001031148900503140c104401003400c03443c01c92143e90303065100071049802014400c1c0403a010004102c02c3d03101140c14040110310444034503051800074002c107071310f2040d402d60710b1400440d40120f00340010110b03c1001032003011039039081c00d5001074490100303902e5115605034545040100c80d030b080b044514040c0700c0e20380300c40d0071212030b000d2041d0070040e151480f0701051340244 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 561236079 1250 561234829 561234841
    0x40204320a14030c030a050d1d06070206070309030c0b2205280317030103210f0309050304360b130c12090c0f0512060403181701091406 60
    0x904000b11035442c0c2024500301004008a03040c00928110941d01d40100d14142d0140540811305541c06003107a40d40080d001d143c01c3c02900340410341c604550b007141090154100608040c80141001c078041d00741400641d030f4030b80d00e210701d8003501c0c1c100b21048072010a21411040602c400300368191241c00010b0003690505000c6003840c0c81c00c4030440071810302109c80302501081341c0c4440c000355820044644c401c036002090740115600c20311040700e200141b2a01c801401c1c0806c42e0805d440d019603954104103c00c514002c40191600348070070b540e503010800001038000001e091041d20001d15090902c940480782c80310310350140034102400c11003401d2001040940d500c40301c184c6801c5c2c4c05448001407407001e09a0841d1294440e0900b0a010340c074050000050121601b50841110806082d50740b88a48440c1880a0101c8110001754654404c002060009003d003443c0c1524003c2e0040d840c4442d580c800250001444158100103d41d540382000b0050201001702c60581c035200c44d0003402c3c1400e005c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 561237329 1250 561236079 561236089
    0xa09080307051203060d12030203070e180604020c0c0d0507030515190c1106040308160203090303030c030c1c0c030606050705060612030d02180901050405070f0c03020304030204020432 81
    0xf409180400d40e0000002440c6903443c1034004007003541100800c486130a00c0c0b04d001c1c00943c030507155500402d00c1c00c100c4d00606d03d401c070741610085612072100b00c00344c1c0b00ca00501000e90844018040280501a04641144c030342403071401d002ca01810007030840078039509049003001d044c030507815543c200140402c50300d9511010403462650200c13000080103400c40710104d80324020318070200031a000c0c5400388028194445006070003840da21854603401200b501c010b0b41d480c0710311400c00e81c040d0001d1002440c0135440d2400f555001d40c8002c100c5103040c031000541d030204880d214841e0001d60f40c400986a64a13410301c030300e8015103a2810600d161208030b45a0598522000780440d12510314400340c8002a5000e00940c0e880501c140750642d1201480544420540d81e003540d1107004580c00c40c0005150703e81406403900407510307626103030351140340c074a011952405400415000e42c4010000000142c50760300c001d2000b0200b60415002013032648030300184000c410342c0300c44068490b0310390345107103aa03075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 561238579 1250 561237329 561237343
    0x9050106170c0a0201060308121005010207230d053324041401090c1205070503070804032f01052503020a090e0406090209090708070b0d020d0e030a0908030705 70
    0xb4014182e00c4240c3d20070124054000c41d00000d24540e070100d45040c2c3e81829406c618014004540c8580312980c8404c01266101d0042c412207a80001c41104001e1180d04030404030301e0110003030168098281c450315101e01d08035683e104008421014621480614484141004100c1c42d0003003003241c03400c051980c1464020f1040c02c114200c2002c1c003904010759503540c0f2440c4e4198080c00042c61310340e540d50080004100c0620709502040128044030041c03549481042d200380f40c0354581508682340d6880c202c0d20300c403008004030244052201c00785111000c2da0355000142c0c007455001300d40350f0f00c2c081c405401c2d00d0300900030070184400810130444a2150111024040c00c4e9407a0044c0c4802211204843c084219809404000466824081801700030340203a11098000e030789004050315104d00e10b690300d403002e110322249900300d42000c1c0f00041c011f5000b800c034901d0703d00c000340c1001c804050040032a81d90901040e01c6600004200300641e0300189000010589003025604243c02602c8841e16514 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 561239829 1250 561238579 561238591
    0x90506030601260a050c150304021f11370b070e0d140f06010f03080403020603130b102108030604150f060e04180818010e15040905010617 61
    0x88608030410218600d900310b003d9104410100c54016481c0c2c1001501d400030496420b01441210281c9040f03074804134103c9014a0b400340032440e603a50b07411050040364880703420107410084816442c41c852070003000004911841c40c85101d2030182d0800d108030034808624050682441c1608880300450000c6006503440368082c20000d4421800a00041c0c502e03501180041c40022440011001e00c6400141841c52280e4907003115002c1e40c9a41034001c590103a488010000035081200703000505000c80910380020a5903903c15041110385c2d502c8494190407103a08140120210003040040c80001c0c40380d91448401250000b00e1209840d840c07640d103c02400240103545441e800401d10042d00c0e5990000c0c5000c00c40c50303003165111a0003c0107005d5452034940f14034100781802c509000010b4005004c0f560011515240402701c004035404040c800c0e03019418820419107505083d11158044921912282070720b50303482e42449240340c02ca0390180c215078104805200f1100c21100c000201c41d400c04 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 561241079 1250 561239829 561239849
    0xb0a15030e0f0d02060a05150a061211120a061509090b0a03080417010506061206010f11100f0515090c0f040f0f031104090b0106140c030c0d020601090506030601 71
    0x2082486029241c0328280c5010400c0b4803d4107800781c181580815aa40078034500d25062000fa1220250385803019030142046a11990f152810070005000340341d0305228190704c01001c208086403081c0d10b041c90304103000c4d094203114480104903807102c5910558014021004100140701c1003c070380100141960b019000e401d81d51403155070a079546900101c0020b56118401c40c0e03466865040440400c0e01d40810b100c850341c2031001040d02450308106948002d4850900054180d40d80001106e10002c01080c513400d00045030500c003400c800c14802c00d1b0804540041c08903141c3c00500d1082e003212801006140344048031440201c0e40da454030314142e00040700c4444c917900c0c0c01e503410841c0c505100301da005140c1c10480d000c0008118056844100490740150900700004a403082404246c034840c1800901140b4508014003503035015003811192814040059804d102800800510b075500403a44550503502c5000030100780e640c104141805404480300038841401c150010076951003040c06070342c11070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 561242329 1250 561241079 561241091
    0x11090417070c03021f200d03020a0c060f0e12040b090f1305130c0611100c0201140109060302270a05070c021804050f0d0e1009030209010f090b0a1503 66
    0x8080785081c1100a0f64000b0300003040d070034865604c103001035600244840803401c034400841d0003070a40d007401d103088191031014103556488000110000d6004910b840140508415000c01040781c074072441e00c0c9241c65400001c0c800041c3c4000d90b142104481c1c031980c0d0300c0d004100074840c0340303a0a026038080701380607111001000da4a600040190204840240d040d030716290800a04941c42c1c842c84a000e409031081865042d00c4850490307101c400390505101551124051006040c0700380d000c42c9a0308031030310001074000c12604c2031401a0800380d200c8210a0b894081c20f105501c0c144200e5900b02d000c50b400d60000d050105142411900014482c007000c0f41d4903400030710300600441480e07120030350007060a481d04081040f140c984620507501910584180902e10700107030740c00512070341416559100c22400340b090030f040014012176803980d030b0100001c00c40c0c00030040c1c50f0000c0b4203028000030f092442c582d80c140300c600da08a4100440442c85102071351810230840041d031000b21102e8616180114031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 561243579 1250 561242329 561242333
    0x507020f012a0c170301030c170d08090705131a060909041b0504090506090f0303060a030807150509101404030c020d021801060e0117250311040b071109041707 70
    0x2441169006070107201100203544813440704a00460599100e4000d51a0003a1500b0554901401d16800e01001e42d2080d0302e12045280100180303948504c0c20003c81d410303e0303112000f01e0210744c80cac500d0b00b114107030f10b84240b01d90303c49010400d5003001905a40050401407074200181308a040540050000c160341144030b10b420000c026400003600000e0018403181011b85401039a03840b0440d18240240620145403075640d8010085070300400e40280b00c8105282141c03914030903039101c198200c0d0b2001074a0498080e8064074007032944942000c00c082c2a081c41411400300985500d40e82810342c40021208102c0080d4105840c003042035010b403020a01d501d82c40c03005c60403000b01d0082c600c4d0440103120000a000b5448000c0c030300301c0303d800c2c1c0e1110b5040c20004034607400c0a10175280d20080328503204040c04854125002509414035a01d00413541e0311243d500d0801c0307980107400007110041c000030980103002202c18400700b04181910320380b06525168980a600714504c0e0502403a041002510400b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 561244829 1250 561243579 561243587
    0x90b06070209040b0a0f09030806210309040c020f0a060b030d0c0317150d110f04050c040306022208070302120f06390d0b060a0507080306220507020f012a 68
    0x110241b21890108519441403c026101da1011103a5620038600c110310415074164012400c01e0481c0120015420032440e2010000a4650f5000310b1045101d50781d41d1030f0440e003080011032421030280f40700042020303400d010300d428150a90a55828420604801c4000070340c80b80020001c0000c5031090b041c0754031803044030300c00394961008081d800b420314590a42800000310300c1059140040380c130761100312100b000b40000d940007110082154007090008002150154000b0103c00c0c030700b00130450780020381d8030041e050344440743c204007081c1d03000c207006000314201841c2e4001202c2c1c8000080c9800d504103c4500d07a2940010048056a1100d01740c0c003d003191500125003072005400e00f00055078001d01c130b003005990403410100518a0414154551504044049407403009a654507a0f203000180c0d15030741e0386540041c003402e130030a044d00307083c800b1404098a100341d119034901010446007001c1100a14042ea03130b290030f01459140908640351140090034451401445080c40b96446620f0030041d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 561246079 1250 561244829 561244841
    0x20724061502100c0e0405160e010906021510030c0914070302091011030d0c02060a140103020d110a0e1609270e010b09010312030f021213060b1306090b06070209040b0a 74
    0xa8111f824403040c8101c010f43c80040555031034240d5654003005100d00f00455500b20184609030150700849039028400b400c410000d80d00280301d200244420360350790b461180c242003a41c004031045584001000152682c80391071900b140c4545070540c104041d480c00180240b0300d40129200b03102c011203402c05485014801c1e00c204c13001000d82006a82e19800001e5101e501c102e584070fa03907620704404d10301c994000d400350302d0507030fa00a00b02084030643c0b80c0d030380d41c600d20741c1008080d0b21149505001400b8840c2d110303502d102c1c2d5400040c2482c0f03000c5c0071401804858240e0000400c079000b000f107a2802600300541c00c0b04048200e03a010840755840f1180790b0041c0010944107070061500b0b80040107202040c2d130b01100c402e14640d010040d00d400000d800c0102d0046030964100310a00070042510302d03035800080e80034030303000700d0700002d01c0c0c1441c60015409000031201c904403070703480306010000e607400b501c44d801108800343c07000b52404510b50300041c11030f180100024035402908012501d44251a4804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 561247329 1250 561246079 561246107
    0x2182205090a030908071401081008072309010503120f04090501080a02090c04060e0d210905040c05070803041e050a051c05070c0315020724061502100c 67
    0x10069400c200c01965240c03542e1041c10740200b20a00320011740d125000a861040f1101e0303c104030703081041003004450444000d841d0f620012541d1401141a0700b0501c5503000410a0020f0450a0303080c504841d02039001506401e48107031881001000130b600d0109144451001c00108039541c1c1c4926880e581d00c0b4041c40d041041d1040c584000450280c500044520106000315400f044c0c030368680440c042e40b4410350044000140c1c200c2401000c4e4202000302c074424a20800e1014042455800c8160151400301040c500041c02c1c88402c21942c2018440c403d408481d07450034601c1c0c96100d4480406610010340018031000c602c04842a0142d103210000c00d003070780d000064400c00c1c00700d820b01d5544c1c2d29000088a05550a203040c4d51115400307502126002030303104424030000e9103075464010f20342010790385484d1640c0c2c0030000700d400070b078004480010304c0c042c5a072903090040b00341305010105d40054100c096051292001e499690340c0001d4000032070102100701290300d0131070764000c4034a21009150 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 561248579 1250 561247329 561247331
    0xb03070326040e0a0b1c030f14030712150501090311030f030408010c08010f142e1805030a030828090b040201021c090306020c071d150103021822 64
    0x4049250600060303524004c00c840e40003806055250010021850342400130301c006680d10b2102d01000038003079036080075051881d051203540b50740104c20b0a11a54030848101001801440315501d0b101c1d441d10070b15101c1c002182d40801c11600b80b20000c1c02d220315601028190341c0760828007002640d020061303e0720910202c41170b030341c07a0740e034490425003c2d043c0c41c202c83c0041082a4008198441d60b400654112801482810b141d680038005100f81c40070844c2c481100d8040805000d0701840703810101c0c40314010303690394003101444203803c2101d4510f8039400ca10f20a0700b05281c682e0109912516094000e10024000d42e5101c50301c1944040c2068050241c0c89d0040c05d101c090000c2c40020241680f045000ba000d5817801002c881da03010681c80005000790210368004014030212b0580d030302902076643d4203422901101c0d120f21401d100f00103000303001c0e4401d00000c010482c90b41c20121450794400303c20b090540c10300c0f0131000c1120303500d40c0c2c00402c103000d00e00300500c0d1280032940004c9002c41d65038202c4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 561249829 1250 561248579 561248587
    0x7060902030703030923061210050a0f0801150501020307080a020a02031f0509070501120e24100902041508070e040f060f0605070b040314130602070e07030b03070326 73
    0x40c011700328169030303c501001d4110220303800310054401d205640050f45c00070035440c5424201c05c40c0c04514070b4003400100010001000c0400c103a1502d55841c806040760000c50110240f61202590075030741c1c8241d07000d9850100c9441000b0030b90f000810b03180295449002c041c0c5594881c0405c070703c0c00e43d01c2d110282d414886d41049844510a014071600c900041b044c041c0410ba0b80e0360b0700e01d0340d80c928510500f4001452030308a620b80c2074031a0f0108000000141c2628403a80c0d06400300ca0b00300700e50802030070103aa4054140140500621100d00050034021020b41c10039252121558035002d41d0a151030a01c280800010780d19481880c00090440005100304184400c8510340c400605050040700c028440b2080003083e142c3c013070000c0d90f0281d684040f034138106546913030b4115614100304409515441c01030201e84e1100e880445040050907281e801008002c1c030380400c400159802602c14400c4c0361030071803d41c0707031a10041440400da03600050641c80c8003240f400c0584681100840c03c000e03200c0e0101d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 561251079 1250 561249829 561249833
    0x1c1404080a02150a06330305091603050c091303020607030c0311071a010602070f03080c01140703050912041206110405031002122d04061107050a0b09011a0607060902030703 76
    0x544410b007522000c01b000c02c1c4080c10304084603082401d1500c210342407400451280d000c648240c105c55408100b00040d160030b88203001440e10b0542903908200c8007034001210459081c10300c0500950b00000d154030740300040705142c0300a5202d58001d00410100368850040d02c2d9690b0081e0402000b08036684a40f56a51186007451100482c8010b647c01c3c4204501d000041e03018030006a0800ba503810342031412400d03242d5640c20516502c01001c44505540710002c194500d403406521178440e60103a10302045918060705010b0500d00100c503101d1181d10b081c0024480502c00c003100160720359001400260b070011001040300d0601580e8041c2d81c1c1031040d2030144402050b00e03005440001401e00c945030941d21000054a900c910130403542044d982c50042c50f940c0c1d0302c60066043d80181c014000051654090108010303280c0c442d40040ea01c039848440080104050b40205542c081620802000756480e21011402082511011240b0540021074030400707010055000d5101d6070303130050444003220b03902c0c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 561252329 1250 561251079 561251081
    0x20325090f06050a02210f180913060f050c0702040e0724140c1908040f0308070201080f07080a1e090b01050a150806012001111c1404080a02150a 64
    0xb20841130b00601852030504041c2003104079070308100c0300058011b828805404a1260b43d0b800000c2403580004a69254034030b50749584500c0342c0141c0328000c00049400c5241810383c10749444202003210b0900c0e01c410048481501e1040e2002c40303904560100c0c1d4420b00490140c54603a298010090a002d40310340c0e0200c13400610034401540845846c0c00d0300b4456101c40f10b00c000e0040200803840c98004c01011500e1003141c0c516500d17500d00c1a000542410f85a00304520304c0c2885400480c0c069900086c41010b542c0c0003960681e1081d43e50601001c00e103403c80005081d0785c006001d6000c1c0a8441c0c0b8904100401c1c441702000d0074940e0342042000354400d003045103500b0020f104150184c1c03107648010a40f02d03a80c82420403e40ca0540b921903c41c1ca49400446400380b50400d507400b00d0540c0002d06401b54400c5c054a0240031603088503036100c1d0750400711940d1601c8402804140a850302d68852003c0004c0010150712640250106443c0d0a50b0b02c01a4106100d82c2c0c01d660441a010082289180003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 561253579 1250 561252329 561252337
    0x9080309130b041e0f05011d04080d090309031a1005040218120714240d11070507030b06061c0b030f030c070f121e020609120309090a020325090f0605 66
    0x54113050100700c5070300804500b118020300030006001c030880900f40c0702207200005141c025101d280050702e440e90300c540340011a405003070308030f00151380d1000400500145080d8240030700c407003441c0d140990030001c082ca95030550314450f41e4015032300403d2a41880c0a000300c000072500b006420310f0604560902070540f151400d0250801c98005032728500400e00701a0a15001c0d800100360034240c030511180e5802060300301d80440450261624059454900c890002e416442d225000800388141145880c401140c00100300900480c0140040210a10f000343d42050041d080400000c10503103c4000c00d0030201c440c00e00810364880040e00f4a02c41400040d0b002c1183e44a80c00d15039102e031200100391007294100303006009032100c6545d500c141300a00c0b00e45c5808030700c01004a4581300d0401c020500c81111a0002046030300045001c41c618100a0030550340110380d001c0171407841c5131024102400f15400c181d00c11059a581c071139180054090b11546000d410b50782e09001c11255141c10041650384 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 561254829 1250 561253579 561253631
    0x1081902091003020c0d17040f11120a0323070b0a060509010e070219110f120706030b09060a151d0d0b011d01030506010513021c05100609080309130b04 67
    0x3141a20103100d00b88035462a0f600300142c07007c3e4000329201c986074641400f002c14000d954152451559504503540c0c09892560324003040042c000c0c000e014140640490f501c103000c1010b0b0035044c82d500b0565212417084854156000c1588078403500c0d003c001c04024000d41d000b85800801754000800c064441c0f44402d4410449942120026041c0c481014540c0d050184000d02d1030140c01050050b034505817125541c9510041c0c06040024a41a002440c0070311580c00800880e1b81d82c0744100310f6040c6444282d0f40044140c42c5140d5039031600f5101800c0c02010344000c3d00b000f6243d0500203c01092030315500c11901c0040c24580011071034184980c01d14028440d81c490200300b445070000c208000890103040360b4010f0050b07e07290b072030041070018201c610b01c09050075513400c1120300c00d0b80301e100034072048040600b50000754900d4501150440f00c4041e030042ca09024004000300090003001040320403000c404c0c0c1e4080f04615914030000c0142c101407016079442802c061011802d032030b41161403c0000c07 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 561256079 1250 561254829 561254833
    0x1a0c06070306030c08070e01030212150711070812040303140f0a02060a0f1b050904090602040e15060f04090902060c010c1d0a1d06031e160b0901081902091003020c 72
    0x6542c1c1ca00499442c14141f00340c581e00b07801b40c4010005071519101c4511005486400e440d14403207021600c0e20280c0381100c031800815075103031a420a100f81003003004084d04010700144400000030f14500138500560cc001020001e1030a441c80e4045585c0c800ea4203103802015074591504200107001c0d456660440719122400d141003800c1b054450303a4052544070401070080c03600c003205052000c80d20360f8841342c000382c1c2141d1582c201100180842c40208000e01468400d400c40e801d048101100200c0b82641c580c1c0309640501c08940500711100c110740031203814800000d068901d910100c0c815018a0304200640d520380b0701001c0200d07030041514035412840e81000c01040502130204071110700c09001d00c40c1c42402c11051940d1711100f0001840e0004001001c0343d101c0265071211000c601512401d250994000300106140071080c41c0c10f03200074080012015060030000d10008180030b4000f8061114001c00760b01c10304410000d5412030f01c8150010340f0303140f0001040c12028000c3e501080140350b10b8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 561257329 1250 561256079 561256103
    0x1113020a081b090d020109050a0b03160e0922140607120c0e0d0c0806040507030501050c04031a06011112040f0b18130e01020a12050708060108011a0c0607030603 71
    0xc07201e1101c4800c44150700081c5824581100f0611101c040408000c0707051000000300850309940302c00500c0c000340f00b4504116a0703850f1843c2450144507016107000c041c40f05c030a055425a944464845a1004c101102c40200e1326003030b06c10000d000305440300074040d500d041104410103000414141c1c420b00c1d45840301101c00041c0c161038801c65110f4088000001d00b181412030581c039103001c0c40201240581c0c203d0b4101038450340704906160064808490607800341c201082008000e01a89601c2600c4481450400746035407110550580c011080d600301e5800100001c0042c0c2c0071380000c0725410342d800c0440b03440c0c0c800c52100300080d030b00501a01c1c101c9850b101e00060142850b00c05c6540c0e10483c5800780c0e424030a01424080c00b040e0b01d81d000c03040341c4c0e182c0c030303881010000c244081c040c0700e8a41c0d60392031441410100e0000480d40701030456020031000710304120503a6000001c050460300030214401c0c000807c80050741013406940b841d00d0301406400c00b40300483d0362540055090300e0158a54860b2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 561258579 1250 561257329 561257341
    0x306050609060109060516050d09180509070909080d0608010507230f09130203070c0204050604020c15101703071407080d0e0a090f0e12070206030f041113020a08 71
    0x520200b11405800105000d40074015107100740c001c3c02180d071000c080d88641d84560741d44c060500c82141518000100682c004000004178802800c04520900c170040202d428090f464545803d49801480d00d41500d4a002204000e07850f8211901200c8042041001689a80485011380b0040c4d51035000150600d504028000c1100c044202d040c000034016032505004d4900156580c010a104c3c0d5030054660a0b2403003c018980000c610030702855075415080211441080104c5034080c0410340035620600080200b940d001529802c1941d14400042c1c03503030351700c48401d0030703a20700d982000c0321180800e001101619000400341c00301c280314142d64400c905408445c15034074807503840391540950001c1c0b02d080c0711034085c0300001c600910107002642400d41395280001900d280102d210b00203030340e401001e9450380091103454500a503015600c1e151503a543c0000b1b1440c00301412a510900003200031a003040005200101040743c094009002c450314040c0c07590094014881801c04a009500050310b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 561259829 1250 561258579 561258589
    0xf01090b12041217040615050619141603120b040905010b100f081f171c031802090c07050601030f03120501030222110301090e190c1701020910050403060506 69
    0x4c40130708020000b08407540c81d86c8400c030261185040c070b036204c000d80945c0454503403902c000602001e04401d1580740110a4010300822800c0900ba100103550740c1400f44100d2000c0204d8403103440d507094a414283d0311403441b0120002d01c0c11081c00e82d0702919240441c0208030043d0020f984505048580426958400c0002ea400d20f600740207110000d0392500001c0c1955501040f02c402481c0c40400611165071245424140e010080951100f203500c4030746554121402081304041542d0540780a1100070480c00f03000051103100900203215190b48000281450b0413503041c1e0392443d40080854102e0b5a481c180861a0145844140e000501000c4180b04420b80c6002c0c045c100c9501401c82000c40e92700b0b4855021800700201d001900360384403101292100010f0b0041e5019100c0d4450000b105048000494501201c00400d0006c95501840d9a03010582000e0207000b102d0743c0540d240342100750f2401542c0203204109247d80d105120421a0042c280d021000c3d000713580c0b00301c40070007040d118201004 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 561261079 1250 561259829 561259847
    0x4090b1e030703080a1b11090a20071a010e0f1305030d020a1b050c030708010608060115051210030c05030303040b0a15050a1d0105120c0f01090b120412 67
    0x154041c1d0000000f000044d14403001001041c0c120301d081004001c095900302c00000681009551501b424500c1100c24130b810a5041e4100d201044100620488006503401c10b40d0802801800988085440410702c02407010344c04140700340200741d20240da11210068070285050742c10141038503d142c000f4081241c00c0209071714840e0044002c608100c1c3c6410040302175446403000600300302c00c1a45400030301280d08540390300b2a121b4400360040401e0b0303400349460845281d1140800342c1c1000d10422020344c0200d43d007030540d80c010381d8008003a02611800d48403449061459480700b18003008020102c09540c000c0e0060341d1003010b41c0d07541c0603580c10425a8a01040d0f030003400d2030500383c001c2028100300d540690700c0c000c540c80901c0ea009035550009250048281e01421100962082802c88480035001c041e02400c5d0484005284540300d00c01990f4400040414038041c4820b040980307400d030b0084030414020300c0c81c5a10195a00800d003403402c181c61b0141d0301100e41484c1c0c8a111541540148103c0d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 561262329 1250 561261079 561261139
    0xe0f07020f0c0f010309060515041b1e1e02010b01031112060904020f04060905150a0609030b09070504061401020d050f090f0a2103090f0f1502010e010204090b 70
    0xc0211034490b80801c1410b25a5040042c1071565944440002811328007034035102e1110041180721400382a0b0074841501c02c422144007030101180b2020020980011021560134801501ca10b40304000c17140540f07840040d020300241c00342c01c6218130220302d039054200903517481c001e03a400d11413072a07002c00e044418081e4a400b198a402e02c41d0010310181045118142d00900080c0b61403501e018241c049000c0321400e811198000c2e44030000c200028003842110308110300252460340000d0303d003020043c98141c0a000042c11021880c0c04a04210020481030010307010080c001c0000a5a58101d000c114030f0f030425141c0540150b044000306103000d0015660b00c000e01c44603640c54426083c00304500c0c6030a80781000d0344116500700104542d5084c01c402e05040510300143e41341d580041c00e000d410400903901940040680c8101440400b0491140104503103d400038440000e004210980c050444a01347c1501580f02003800103201000340c0143d0303001207098a030414100451305446260101c01c1110b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 561263579 1250 561262329 561262333
    0x10031502070b0106050c010b06030c0a08180712080904141608010b040620032b0e12030a09050a1b0608090a1713090f0e06071e0e0306010e0f07020f 65
    0x401200d8000c20041207510220f20000660081c03050000d035094102fa01d07004180e480200f01540c1d450b810044007908090082c1050707040c40d0074590031300e039220810301a2890b84510966914104100740b416190b03540300c010b01c00d00c21415440e81d0041c40c400d045070741010410b046401d210440e802070391000e041e1aa034900c19441d10b0305009060740d81d041000c2240c8141e003d00240308a8903d000d001034000205151218044505e441560040260ba030604041032240381403809250b811001580c24503058131184566100ea0b1440108801040e00c0c880140881c051040f40c602009242d00d4001d0f0780c0351710500381c141c2613a140c0d01c08440d0460b08485c0081658440300398003001c00d0782c41800c02c450000344400303a40f80032021002c0603014541136102c040c0c035680307400c440e80701d0a4490103000c07a50078407140185514074212500074502416468041c524007017140d482060742d07118186850311210040c00316103a650f13581407a00d1058004444000c0400301c0f010100e080b030352007c16045540005000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 561264829 1250 561263579 561263581
    0x5240a08160f0903170403060204080705040c1106060409020a17100c09050d02062503050a0212033303030f0d0b06030c030a020a030f0e030c06060f030a030e041410031502070b 77
    0x900e11180400c181811317503049070103000000000d8114002000078102c4c0c038000e0020710385000180700c207032000203039440c0511500d07495a030310401c00003c5a07503000100f2240071640c041c0c10300208000d8040c0d5044180c3c446484040b0401605002074422902040803a080005240a51089820b151a809856803142200203404090703e0414054181d42482c02d9a0300490400d0403580d04000c031007440700701d0120340041020107115405000c0c2d10800403c66540610b5450700326251f8030303007603040c04132071941000360a1207000300f03204a0416840b2150260441c1d5030b503a44803001002ca90405c072803010500c0d0421450740980d0402c44190ba02030880e0540641c10750311340300c2820b000f940010091600b01035607040c2e00584034600e40038158845440a01841e07440503054000c03414214000e110500461800c42e0300462030f140092080c2c41d85030903244c0820b844080500140c05800400020810307a80b50f8010702c00c01c40185e007181c0007102c2c03141000f000d1900382e40f4010000d902821102800c4903043d00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 561266079 1250 561264829 561264833
    0x61107230a080c031b0601030c06170103030507050109080d0f05090304050d031b020303040f060806010206071d0117010b04170f07050d020607020d030e1e090105240a08160f0903 78
    0x40c001d44801c0d03010f007054a00300100946241d01c5801c0c0c0e400c00400d142e100d100108144690140c4d80b1000c0e144070b290081e94500c030280f5105009006100090403c0300014424042c0700c804e42c48a49942d43c05401903030341c1c895609584d80030b40620350b050718080e440c4c0008141402d10020403601217400c09410000c8101d04c9450940f500102460340c0c0f54080e556410380801079074180000d0028080d8400c0d80c001c510b041040007815000002e10250665001206010791280c02640d800c0b40301c0d5041007404441110000126030f040341d003604ca909181d89100021444030a014060001c1d90070407120355045a10080e840b50307a0742e554825410054100340010311032810040701c2d03100d095002500b441c1c84c1081550100d0031680c1c00480c10740000729082301c0c0f0740051800403074407109120002242c0304050312880018910b90f2041c8112442000e03d0003000e4040100c000c0308030300d00328002e9170307040d00c0e041361050250040204503601e40424000036a6041014010f02c840041c0d101e842d614001d006c3c0c259 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 561267329 1250 561266079 561266093
    0xa0b0702280314010f0b100923120102040e0906010f09050c09101e11100e1c021c110a0f05011e06050a05180c030402060403061107230a 60
    0x100849041c0800507840070002c100707424940e40318041c1510002508800604910b8100c0c0c14600c3d0007441242e690394030b0345460364804042e90070703074091503903102c07050018550002c3d507807500500264004200c030f003080d0310000381940584112104880940b1840d922402c085071038031024000c00001c926900414070003200c55512441d4091031001c1100d24000f0803100140441148903481800102c13001003141c003a0807400d08240d040d40d46800d08045c0c50000d59451070325401060b501440382582d80c0c44020360f5003000c01540c5c0d01d020000580c1011000481e100a40340c1c2d0f24001901c43d002c02943c484070304103100b0000c0c0003c071040b0390080c0c00450025514410481550501900c3c2507490b0180250190070702044040b401203413001c0012034926000c00c3c82011511980050702c035a884500d140111a0911406079022005045640d981d40e40c601c00582640500d4002801d00c51400030b070001c0c40210000280b062030701a412006000803100000102118110904800340c2c0080d4450310001d001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 561268579 1250 561267329 561267379
    0x60209060d02040b18030105070c020607020f0a060504081c090e0628050307150e1009080d0f0206090120070c03062c010204030210050d091406060a0b0702 68
    0x802004140380c05400901e420581e006904011075515000841c2c07080031811100304081120150001c1c0030502d40090003a008007a01030b000f0740a1240003680104655030b100d0312407007986005280c00070180e22200014041c0c1c00074001e582023441015204800180b0311a107040c46070320325a13180800141401214020324401030009a0000f0384800c1051721007070a40c40420900c0c1642529800a80ca44400c041c070b031114680c07004d410713142514040d0303420944c4846004105001520924602c41507840c045a0b07200c555400b020040c013500305903100c0d1981c0403180003c10300031982140c41d1502c035668640d08807109a03d5600030b0108400401040546100190600c24007070034220000540d251580020b40308108039001800e81caa2000c0b441e401300c40c20040c0321005500f0001c6007807a0070341d03000c101d00d68003900700c0d503040c0100410481600e10050b000844581c0d4000c07282400e840000c0c003107a99903a0306a0b2428441c103205e940110341c001008081e40c82c1c00780c00518606034242c19070091240d2041d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 561269829 1250 561268579 561268597
    0x80a0803010312030b090106050c0d050414220f05010e0702060f0f0c0d090b0106090e0129091c14010c0212070c120302030306040510060203030402040b060d2f160602 73
    0x145440d17070b4030040da50b0100c140b40200100c1c0c5801303541d0003e1885250424038054103100c141302e0148000d0102401c51502c45018480c1a075280c1c1d80140304507810040c030307031160141d80049800c10000c1c0312a00c112b0303089a4104d9040811400c0301c0c1c1c442c4402640c680604403614561601c00400042c4c1e541f640480c06034004403071201d171a2900050050220603038800f02401d03140f540a4a004201081d40205004010300714a8941c0c4440d505055202404e400f0300568803040d00401810003400d99800c2084038031401009044005101e080310170a00c1412841c88107443e42040d21181d00003400c410b006030304c3c54514560141926041d00e2103892400c0c2c0004c8020340303030030401c003001061800c410141c0e0000e0702c2c02078008507105d2070650700708010b542006000c00402c20801c0c3d002c005081e000400c0d00c1c1c0080d411100410298262004145240210081e49c5000c42c1400c42c41d82442441502d100801182c10700700da204000443c3c0b0446240c41201404600b041403050a1000305013658090318100d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 561271079 1250 561269829 561269831
    0x3030e09100f06020616140f0c032b0c020606031e0f01020408150703020f0715200a11010204080c10030204180615080106080c0d0b060301030b040507080a080301031203 74
    0x140d25403240300b26030300031504010302507840070045c800001221081c40f80003941500d8540071182d48401007600c503000310442154021404148010300400c00c0c815241e8a801c0458030307813100041c0b1400040b004071500c92a09401e4034100c00450b00034808240d00380320340c10150040c068001c01c0e402c441c00c1c5c210711805411050113110383d61540c10000b80010002030140e10000d10441000880d142003030000540580c0c1072510421410111000270750030380d180309030014411002c4100241100300a0300300080074201c80d04100c3d5000015442031006402000d10580e00c81e8964081c00623128200d104500138108030340d01c20001c0c012180750001000c543c440c41441c0241c1025601c4a00300c1d01582462018aa20754550350144208046892015003c00e850315220815524040025020b400094203c0024050006050390001c0322904840000785002d404590b8075a502c0c2000c0c100c98200762000c5450b4000c200d030002d005600080da11585030380001216255034038694805034402189451303c0c041c9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 561272329 1250 561271079 561271111
    0x1209180f13080d0906090210050a080f220b09100b0303180102150a05061c030f03110c030f0a03180503041509030506091e0312010909060615050d060b030103030e09 72
    0x1854240c0501309203280301d01404140754085104204040d80d2030031340c0c43d042160902800c400c0d00d5104a0039508400340c034412401d10303120740c5504009010804031466102c8119005182004028100b413840b03035848905494010001c40d80c20f1050741d094034980d40c1d00d0360040c480100d1340410040c0c03c980c40c403414011114000760703401e640740946e2011510141116922000c003c000e0a1044149100421415008803a19030a54003c3c140c803150010020405135604450907104481004485881c0b034980101e0b034907001d000a00284039400b1607038a1000074180b19010380180300201031169010382c0000654141810405075a280c06195414901080200303c80000451814003020b400380c0511409050f2200795908001c2e40d403120b0319480c9030315900400001e00b000c2c0c030000c036a5040d25107540010442c0da2603410407001500043c2c0141e4032401c04203500c480d405400c80005d12690404050510000d6a96040c0075260b0000b40f00141c0403803144204000340e4a025502c82e9400050309500d2072903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 561273579 1250 561272329 561272347
    0x190b090d140a03020d080f0411060d0609061a04060f0804080409020309010e0c12070521011113090908040303051b1b0306060d0507030b070504081209180f1308 70
    0x600d401c940240000c5030014258007041c540e05011089250080d41860a09030402d041c151340c20903001040586005085480703101a5030b1080121116141076060601106848200443c020580d510035a12880c01c0e122400071141d00c0340d8182c0c1c048a0302a261002c5070450420300b9a4125002001112076a8041001041c122003610245009444030400007030008607024499182104c41c0b8003540c8035a00b507d084011140000030000c050f58400d48071251070840300400c50914000702054000d05500300703080512a40c0302c0c01c02810600001d4002003001c1c655800f070880490340117002c064030a0408200c01d10100340140001c00400c200802e05064590001d17500a040640d05021240088001e5080105610b01080301e80e4015404941c1343d43d000b44903035100340e070340d00c418800102aa00401c0000360400c1c0160141e40003851070206944d03c01d580454010083c0d480190b510b03102d110076102c04012000a00d000c0c038130900d00c10403c00c106803075507201b181c0238041c1048100d0380b4105c00c01c4100d507 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 561274829 1250 561273579 561273593
    0x201090b0319020f1c0504050619090606060c170711100c020a09020a0e040209090402120f070f170f100b040906110405030601050d080703050a0c0b04031d190b090d 72
    0x964401013800648805190844607201c00d8600c625a507402e040500b4400030a81c00f1540b2504503205100b002150903c0413044409404500405000c0c145130800c00203a09400000044030b5078869641108014140d68509800c2c0c040d120020f08200c0078034087d26039905019203ea06416503504069110724202d40c0040c15103441a04601c9070b864001c116421115003010020151043c00c44055082881c0d200116411400003403021340b048044984031020304070140310300040d10103034205035407a80da19050030700c0030140d640c0300e140c003903080391050030f401000089980c2c1c1070424100b002d4140d00001c00c0307090000c3c0c5543e030101c43c1e0043d031780c0e00305400081092182206c01c070038500d040c0d522180381400b00341c109007051744039a01a030300200502001903500c070110707400954035003002c0d03803201c56411f0221510501c080000300f802280b002800141504000402c0b0103450342481102415196011311070620000041c1d0740920040345001d1018082c103d0140c020244003601141d40c901301910703002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 561276079 1250 561274829 561274837
    0x2030a08072f061008191b0e01050f180610200705100806010c0b0a0605090a09020a061404060c06021e120f01050a0e100801020309030a02190201090b031902 69
    0x4011030082402d05540241c003400707110f6010303003081e02c58003241d0300d429141034540d0041c0e1a9000711426586800c0100840b0301d0410003107507024442034009a469444000140100307029091103101c4c0980603048a00d052502211107040150700c000483d155070f028030010041c015131134028001d045090400081c641c11041c00303003205440c000c0401d036180006024841445148070000c00c0201c40c00c00c81240d03008000c040318550303c00030091443d924016400c00520f0f8a4208a512418a0381031101c0f0000ba0b800411800f4000c40d43c0501c0d203a66603206550300d2410514a0480350301c180420800e69000d041784854082c000d80001d0b2504410610403421980b041c0f5041a4081c000b250311901030652400c0e455005080c0c0c2580b45c50381d41010b000900c0c4498600c40c41100102400004018554582505008100d180c00a541328144400700c0d541300e4005081140042c400c030014520400c3c40c000d01c0042254043c1c40b03d2110b541420154101940020b20381449414418523108040f11548014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 561277329 1250 561276079 561276137
    0x40504060f0e0a110a1d04030903020901061d030c010207090221041202060a0203070c23070e01080c010c0b0604020a18150905040c090e09070f0e07020f0a0302030a0807 74
    0x207040161841e1070090f8403c3c4429072498041c1102030820b01c151040090601e0310343e00c0486070281b4951f00c0340b5045480c07070901e4100035084201c9000019806405c81c0b107610002401c2d132800310559046c034040c50b03560020002918016030002104010901d40e50b4020003126444400c926002c02d48030070796190000003914111040c04c560250444600d606000700750b00b0080d0640306603d141009000102204d0342490050540008011010086219810300c0d4190400c181c0030385a5155a0701010740c5100c00074403601c0030500405402810315882464035211440e40308850402c1e585811061000079009080c02038188110700742d29010998180e14a00010003141101e48850000310000810501103540800c0c0510b00b01300000b02d0260300700c50038a05503a00401e16014036690005800e241125a90010b01000e16100d80403c00b031180b44a0030f0301c541183c1c1c08035000c041200130460b941c0e1491000c0a0016081400792030720307007846401c01c186c01200c40c2c030348816507210395800c503184e030388a01000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 561278579 1250 561277329 561277333
    0x50c01081b04030b0f101d100e1807050f0a0b030a091713060f0804020103050a0209040905032d07080a0210050a02120f090d0e0406080a05070303030b06090609040504060f0e 76
    0x100319001ca041c0340303070b41d0f03004264205000001c0e1074987c00000c020741025442002c010110001211031541d456481d0040843c8002e840c0e2904188908417040e100301829004a401a44000704107801d142601844a02e00500780ca8802e5140c0429600e16400c0034003c0b07998242c60f104404c0104040303080801422100c100603d603180748840030030602158030ba201c0ca0511a0034801505076641003281e0a84c0b0a4080c02c01044030741e2482c414400038401c40071520380c42882d10791120244040000030f010402d0201c0c4920040e2001103140c0c1c0d6941091914412240b20104811400075191070080c1c10350f1107140c012100c0544600d603a01040d04c10440c8d400b01c1017a40401d0303104200c007818a003c0e400043c98600c03220700b402d00321025502d90004128003800d10002070300344241da0b213a90303101700001d18604e0b0913154102d0a078035281d40c40e182d40c1d22064001900300300030030541740380010469640702c078020111464140c4080c00d00c00584002842901c0280e0b4919034107010f0144e0b030055031011032030080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 561279829 1250 561278579 561278581
    0x2040806010f05030a080406081003050d0908150f07120b0d0f0506060f2803120c0c080111090405090c150309240a1104030606031a0c07050c01081b04030b 68
    0x312030302e124101a07001030b2103a840141010041022603045600b0b0714000c1c50180c1c080d03a54031206468803003c6030320050851040c412442c201c0c9610109001c145c0b081e41c0d0594418101c587e5a440307140d003094650030810500c050103e0041c500440901e01d13080c2c80c02c00042900e60643d030002e0000000c01409a071065803448c1070314100324082c420a03900c030400325050351340c0c0044900855541213181302c0503022012008a420f1903200c146881070003c0d94402401c0d8141420030000408000b0a0102103601c889885d0020400350018024152a8501039802c076050603d14070800001e8000681504054010400300e00e003180c44101603800383c0c030182404140d0701c2c00d04801040c9422906400003004240c2c2c40a160ba07030204450302c50f0380188082001090b07000307145407424140e204550000b0b00040c91b08100100300881c00e00c1c4440240c00c0b5495030005541d0f041500b02481c81800002881a0030a49103114a9802020800c0e0080340f041d001299015401c0000030042e407240d0010f40c2d009113864 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 561281079 1250 561279829 561279839
    0x6020307020c0f0915010302090301060b0d1b0f050d050709080d0c02010206090d050403060b1c14190210030510050a0609080d2109080702060d1401080d0504140609040204080601 78
    0x4007076100d0f441d0262009505071604040000c50302c40000403044c1015000950944655800d4008601900e001040d4966420054007050b00801010b0710f02c3d00c024070314048101e010b034001c0101e0146004642c03540c2c1c0c80c1000d906094001004010300c0703079091000582c00450481c3c001c00400e6800d40e21605d40c62240801c0e800060314107400104204865400500c5883c60241d20009460840f80e0005002c24448460790010760580c40c2c000c04d9490010042e60420700703010070000c890309900c442c41e054036020a5821204820390041c04006904118184004032483d40b00f0390100754000241c803088025203031954000790411440e07500990005640200600c8003103c144000403e010b10f03800d1080c2c100c18813800d01058101d03800351000c84581d5620780d0b42c1c184220314044a000c5a0300501c030301e682d51410442c90005014241121188074100c100205001100141c40403004800303455250034a450100b00300d4078052004a580e4110781d043c005c86116440d5400a8009440c09101402c0c080d8181 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 561282329 1250 561281079 561281089
    0x130e0702060f010803070206090301090204180b0604050402011d0d023109120516020910360e0f010516120209100c08070507090621120e030a06020307020c 68
    0x1404070b80c000e1008000400c1180c600100300d8030300b00d90541d82da50300c03002440c0020340104034001b80130b9040350515110003004024000c8804441e482000c800042c2d031111002c0c001202e004981c001d012404410411040080d250b4100c3c43c4800000d140031200030031680490f68043d00300c6440701e201600d0b4a0b40310741c0403a000504510b00c01460204010940703e0b500d55242884e0451502818032070001404c2e050703601060750404401c1d4000e0051480d03410f04d101000d18030002c910404c07035064070000c030b01d1070001000071441e0124030580761101340070041c0c214400010024015036035494031444943d03000008080c000c40e0320032007101e169103405808007000030b06501c182903008200b992041100340030561f1200d2a14009003460300d4400c01c0303c1190f241413034151042e1000070340a0712506100203820002a0001c0c41a144a40031501340c0c0c488501001c001070301e9550b001030044401c20021182e01e442800c046070103003801021109032800c00d0f00c41100b240c0c03040d01c0010043e002030399280114141 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 561283579 1250 561282329 561282331
    0x6020306040b031b1c080d050c0c12071101051c021b190215071709150d0b0a0f0e06060c030f0406090e0601170a0c030e1f05010905010b030106080a02130e070206 71
    0x1500104400c90b0352161b4403958648185080407100380e03642c1012481c17007403280007902c401c030903281c00301d4103c0c25034450354120981002c3c0d030441d04258640420600c0c2e500c58400e4440000d6050100740c41c58406002c2d04020350010101200d010100c1c00c502c0500c07000801240000007103d03480a01d900190380103011914005102c40050320394100b010f400051800c00300d0043c07661131070140940322012200021a564004180101086030100300f22003d000c00341e0000381048801c03200e0090b1a5510108000042010b00c2994048800f6100041d098100140102851b031601001d580ca06060700e0070614031600190001400200c0803401480f080c00382d0341446800180900300044284445c0c1c3e25480c40040081600400d940c0b15246071104c0c900030f4100e208007919080a8a000c19000b05586c501c0107001e840c0310b104107003041c0000680c1105482980d044ea81c0300d000072851070307007061020ba440c100040d200040f165800c011000741901c0d0101c0078000340c10407003025102d608107013800a180c840 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 561284829 1250 561283579 561283609
    0x9010605040c02100c0311030405031908101e0f0b0d2d090201090e01090b0f1203040618030506011202030115150f02120a030501081b01080406020306040b031b 70
    0x441e142d41032295035000146141202c002c10b8001c900710303440840841c0500b10900111801050200501c001c100c4040701030540d0202c482407142445ea214507040f01c40140907100d4034040d041050013400001c0400b40702d54882080b01d550741030a107035180d0043e50000240c0d44000364010010890000404d140d01a003090903c2d100d15050b060504100c0700074008003500401c40344070b03644660391400c59004880400050109441c19905581e54808034400b502c025141188103d15003050304005107820351083c01100c1141d40210705107400c1c94401d0350070403110b640440000b4101750001000030300c10088540a02035800c2c1c840b4015240b031040c5801d480305404520726905142c002409020020b050440d0940f00d58034040d20741400080b0240d092124080c50040d115400142c140c15907901500000c7c12501d604040720190642c48800014400c0c04400950009410501040c04150103030040c58002200900002d644034a00d8000303403520701001c0c2c01c1140901c210820407200d26051040085d920 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 561286079 1250 561284829 561284831
    0x15020a0b011d0f1312020304050103180515190f090c0605030402030a06020a0c02060d06140907050909041509150e0c031005181203040611090112090512120901060504 73
    0x104468000b01e0203500080c0300c0e0b030741e100c8000001031001440c0d644107081a034000c0f01000c044004804007e481e030303000340220390100341486d107070341040d102c0100d400341c803180c02a02920900e68036412986d01c070400601048100b49124014881005447c8129196903030003c9002800c0c5183d0b10b00703c8a070101035031122041c004d0a0041001603200480e02c00c0f64103602a00050743c44120302030a4404841010380a9000ad00101d81c10a01c1c0c0c0041e4007100c1030301c040c111400c06220343c050400002c1d480843c0e14031b0008000780711050303d40c242610210303045031040c0d0320f140711800500c13502d80865000030010b60700090003003282c0741404942e00c209240c04142c81c024200c42c42000c004655900a442e082e43d6080d9a550001241c0141072100052051002810364415034a81c44615001d5041501c4c15500303a40b030b1000021102c52000100d4208403410303102c1008041218640c1e0005013401801a905409010303081c03010f4042400c010817a0441040c01c40e502c40c00c00d0028682120000d401c12400340f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 561287329 1250 561286079 561286109
    0x40303080c091e21060405060609040309060804030c080c0102120c190513052709010b0d030e0d060c03020714011104051207080601030311151612020415020a0b01 71
    0x9511036111000040b0b18922003191000c07401400b0071040c0804d0010110340c1d000f0f0ba40041145080401c0340c07030080d40207508903003164445c1c1042001c1c00c43c05440c000c006c1460300c541000024000e00c0c0c2c0340d5226019040c840b010241c543c5480410394446000c000340e5950005442c070164035a0703002550020650341040d4203140f10f150100035062002c2d0780790310601c6008540000d501c1d0201d01204060400035020751035148440540b40c03031101c05da40b4001280d4086a000035500341c014481c3c1c0c041c0707200c010b200181c07240e910344042c0c1e19010859803450700070191a007144085041070003152018929980d0040e51951141031541c00c4038061112082c2a9050a282d035032040781c1030082d1002d0702c601b02c03070261840012000701843c0141550010087c1d0080100000c01e06411403145d0601d8840c14007641d09200800c890030085620488041d0103000744881d039014554400c1264502c0c02c481d6020061516450301c0180c0544010501d800c00140e01102c222420418121030305401000305501040700c2c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 561288579 1250 561287329 561287347
    0x5061810020109172d030114060d0c050c121206040903121a1c050717070e0c0901112a060c07030506040201110d0e0d150207210e010203090d0c08070902040303080c 72
    0x240c84188542c081c0009102c042c2d420507902c1c603088982e1001071b060100200049688007800541188190103400d00540390802400b04510080781e1000191250182047d0c1d15a000c1000070072705850190100500420720984400a900c2450304412110204a5200a0b00010481400001c29880081030f2a1804000000301c00055407000d945101c0c6001400c4026820710b28904501c6030b1080c0c607000f4801050181001403c00207045480c0280c0e030700c4400f40129111141da960011800034503440421080314864a4044041c602c40000201414a0900546c41c103502c1c0442c0c9030070985194101c6002c0c04110768100c3d80c2160787c002c170310000c0c1c00003056200015050303011040c80700e030140070003a01150401206c11401030020418200031034482c2c4041c206524480041e142920801c8003005000d0740e05400781904511280050340214640725243d0140a0020368a03070044031451450300340803a0f580c10a1007080d001e062a40d80050311613113142401450000c1c0500540042c88080055a41d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 561289829 1250 561288579 561288667
    0x609120304140c0d060204050906040902030a03080a02040b07050105091c020d05031e07030905010c0503100b1e0c1609140601030905070e070e01090506181002010917 73
    0x98001d030003030300c040c0001c0c1c440b820321410042c4030a061a8099425081c000c01c0007a154050000e454040c1c40c00040f82d59110301f840212122070320040d40c5a804a0510750000e88030321806e984c0581c00e941c0150902350f0301c084070340103500a0b200860b00d99444004000840c03c080000301c01143c100140c1510340140904040d40b240c0d4182521000c02800000040501da000020b601040810380a0510703149004400200200340d801d0040700c0e40c0d4280400490824400e900751b0780200856100d03592321740d03e0504030400d10360100d02445002c401e184100d0091054103409811103404102c090401010001c0020700d0809240d00700c00130241c50071010144010b00c654ac4207602030803c0c01c00083e58000d030700348240b90048503804030000f41185010420741b1640400382d035464542c20f07207417052203a49842c02c0003d40c0c0101d80c3d0721440040c0d002c6815040f03180c641c581c905c05000c28000012807545039203071711f01c413044c507444030044001e00020b40f6480308840f10b0600c1e43e2a1402c8003030000404100f91845 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 561291079 1250 561289829 561289831
    0xf01050a0b0a2d0f020708060117010b1903031205010e0703180c032405090c04020a0c0512120702010506030d051812012c0a121407060b0306091203 65
    0x312201c1c0110350702108500940000c156240105800a4115409030809410000890b070080c0020079844d40516000c1c00003800c24262025100580843d80c00c12140c0d09451600811904996403100c3c0c204e103031a10798045c901407583c41c500d14080c6080c19400d000d0f02c18000c4d070016074002c1d0701c0c1c0001000755484020070580c01c221203280c0031030524a05410880306048030304001d8401c880d940c0001003049050ba010240c5180c0e110080b401c1c40e19401014012140200d50010a03504842d0794000249000e600801400143d070400001c5240c040c0c44080c50400103460003000c035000064880034040701640c146912074a50309c004c1c0002e18056020035140c210510800061080110f130f001c10310039441001d25440200602072045801b5602c9105010744800040a40410303040c460006108070030546040074400d02100404004a56584110036880d807034078540d08010308411140680c05201008080300c500508000c510b0100c50400c060403c1c2014100503c140d00030806100400b201c0400d43e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 561292329 1250 561291079 561291089
    0xc082b021b04020f030a2c0715020304031a0108071505070f060e01020a0201050412080c070b1b0a0e10030209011b05010216051c050f0f0a0315090c080f01050a 70
    0x3071012486660104000c2e00500e1241c00807070380d002c010004480c206520540c24081059044400703a4003031032120180d4a87d207a4000c0090700941e00c24428080c4180003140d8400c41d40c8116841c1681e2500d030031000310802c2803480003503c9c40f20010402c202c02086200064083d500d40c032800201ca24a010f40070f40306060009200e9070241c001340d4140300e225803203c80070b0241040255a645c03c2018000e000b05070071102100c0042215641c0f0900e0341c03107450914401c5107d079041c10300d03010250700c42c4120074200400380010b880c003051660151884950242c136a002c403a84a89241c8100340040250388011002c0710020581f043c040341360030743c0c0d000070f10f85250158041e0880c0b1307040460a150740a481603e56841c03035480000e0340e8400300200010042a4ac01e9100255104458040001c0700d00d44114860042c44d11014800e003c00050003600400104609040018442c03140d00c41107400415282c0c00325945550b600110034155411000c0c0680c0a01d28010341d9000e5030400d00000c0c0c16000c1c50107a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 561293579 1250 561292329 561292363
    0x3090e01080d1218060f0c110f060105011d030706050705060f060901090902030f0303040c051002030415050901030b090702010f0f05040c03061e110403030f031a100504030c082b02 79
    0x200340944c02c4454040308009802c100c0030700c0100171001c0110040c1500c4820080011072000801400e07182c0403c00405001003c8050810799185c5001110030101c10002c220803000e4035402c0d81d509035810003254000f0010f81e11002e13260b07052411300c1400c0903002050282c0710003100c2c080013102c0d9034a81c56541996800c481c0007400010764004240782100c03001120005200c004140400d10030b901959404550040f1622007403008010812610307801148100c0c6c1a6043d4074004031a52402000684240038040c9000103084020400180310010280e030100050703551a05114201d071018003c04403800e03003218050095040c00e99814a0300c0c492440042c100542e0360035202185100c840e200f01c0303c0c214011003449082c0786608903001540c028070080380850305404852001c00d019000340d010705e69036070804108142c00304080c4807014101442d01c5041003070410010001550303203811500038140f60b0000300300f0100c15601807043e0a490b00c006814500c00d07211404002540011480000d8842c009 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 561294829 1250 561293579 561293591
    0x604090b1b130906030c0b0a050403030305061c1101080105010f140f1603030b03280b0c0904020c0304080c010c08030406151a0c0d1d0d081603090e01080d12 69
    0x440c0320346402250580ca1840c800038100140700300081d00031101740d0307010b51540c0d41882d940e1005040c05200d241c1c64040420020300041010078040d501280e400b02025101c40915280c200d20030100440000048480c00481040005c455a0107007005000d00030a0030030400d003600000f409442451501c904160344180002d040000c0503072581901c1c0c0e81c101c0c9648181c024190b0f482c0c003078064042c40d44443e009218004d00400308401c9504820742503c00c00d076035005e0184441c3c031410180d000003004225a14020400c5542640b038501c020102132541030041c5880340d0400c00c0c01c03030400c241103116070704000b0091882c4e008120720008480d00154024030006c0d04191150419a66021039880500c071a210a040c0c1800c0c50300c420700801400964038280c6040382c0320458180c9290300d0a83e01c45401e65020a1100010f04248801c039060b2170240f4015400c0030035290743d4586a240c000d50840015050349410400780d001c40038503a0251a0b05000b0703041a0108103c000d20034403aa000316403107139403203038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 561296079 1250 561294829 561294871
    0x1061202030c091804061a010507021002070f0b09120c15070f0203030f030403080907032103090206070f12051c180c0303050a02070602030412081308060411090604090b 74
    0x30007140c8998002800c1000080c4c0c42c1c00000c500c15900316030070382d441801c100103c0100d8002c4885401414016110766003442c000741c00b4407101400da0036201080d44510080805d0f01c400e03501094008082504c411559042458180101c201105d049000d05034808100e00c21705a48074250740800d018a80000c40d1607100b64140041800610a8042e425000004004040c81290001148100e010f9103848196490300da0b10180d842ca19444090800082c1c2483c81c0b54442442045007200440b0346808101d25590341c000411591083c141181d50364501c640c8503003041284503100d201c1207200e040407401c1403420464807124080320f1003120a0259125206000c005035800b400c0013450f004028498400d49900e0090029400390018401500c2269000580359200108403001d46000c1040f030504505650341d40022a00202c6014401004001c00866040020007041e481a4059807103480d61003c44814083d81003005003080b40294240703550380d4003207003406d6070484d00020310f9100f44100354980 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 561297329 1250 561296079 561296101
    0x3b1911070611070602030408030f090c0f01050d0213170f15010302040f060b0a030501050405131a0601052206090e040209060907180e0907060801060210051f0b1e030106120203 77
    0x4a0b0b004281610206c184001d004c3c0c680091031203000c1100000090780c03100c1410f50382d45c40403110380546c80b0804c0514040d855204402038440d80450715405402c00740140e400d0001844503030810b0100c0c0f03110660207144120100040f40841008a01520446500c040350403098001400007034003441d1507020781d00c144509a44543c00130a03c0d051020307200c0380f000100801406081c8103e41c4594182800b00d0a529080c1106104090340400b078010b01c440442010f90034801e009050034107011040c8000381811490380c081b15104500a0360380340c03031141401800b8081c603c071508180c2006c80704404000041c0c45904c00250000001c4800c3c0c0407965401100300d6203490755482030343c60300000070b0000900c7c043c042c44d480d000b0641442500c0302903460340e10845107030500b4854800144e010008921701d0001342e43c400c54000c00b107491802c0e03a400303503c83d116107201c031141d010085042c00003824501e510000304070400e001c440341817140e155500d04a001402403481850781103080d5070000209001c0000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 561298579 1250 561297329 561297337
    0x9040c030e0a201e1f0c060906060e010e0103050105010803030408040e04170c0304090b0315040f0302030d14090f0d0509010f030f09060501080f0a0c3b1911070611 72
    0x100404c4440c1c0c640030000326071485500d0440c078600450070700310030544100f407000480b81c5160503030350f03095121003d64031080060041c0220980312180c2e20000401d004e1078581d400c601904180000c828107500d0761a1075800c50b1030590016180f030708107005100009001c48104d9003128034005c1a2540ca484a003000e84402d1050410410391000010f40d207004184040050b00440b000750358100140d030400400e03d5200c01f00c0e20800c1c0c8076080080c0004d030000d046017414030441c501901c100d80c106043c1019280841c1c191302c0c11000110015020041c0c900c03401c02003990070f4000d00c0081c101c4a480d00d00301901c203000302c00086040c8000d14000f140c441e40f04c2d50103c0703061600c40b0803d0000f05424140b150042400380521010f50040012091f49000c1c00510800c0d41c45e8003480c0d882801b8a0959a07007958600b50601c83e0041100304614200814080c5150145040d21400c5142d94249600c903811444406010a03426030700f01030117001204c444d0410384034080d0300b000000c0b07002c4503080324040700ca02c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 561299829 1250 561298579 561298643
    0x604020d060e1605030705010509060d09080d020f0409050c0a0f080702010b0303120609060d05100207390f03081b03040e0901050717010305030702040f0b030a03020309040c030e0a 79
    0xc03d11124460744080f60f09800708584003601500d8005844900441c1c091140c400a0761308101d08000c5a0b040d02002d52142105070701a103003041c02e11203041065002d0383d03c2090a110780c5040441c1c20b0040f04803900c241d43d00560007405141c41d202081001601d40c502000c44032052010070400141d8050003900f00d2000702c0e10040039030360341300071140e0403126001e41038500324080c010301d0000580c2820050203400c0c809801000034201089004c5106c40a54000076003141c001051001c1d140000c002c15039801040901d03000c10402c080c99000d1aa13044d80e90990190007e14130000c41000491000780803520713612501d018825154151000c0980703940704a501c0011010741c031404000004606510190145203217075202c0d203070101c00303680d0403061003000c3c08040c0c01c0ea04100311620040c602a405005044007410380400c18108000000b4244130844034141c000d6000029041e105240074880c442560450341010815441242c170410350719811810300800072461300c0503401410680d4840461401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 561301079 1250 561299829 561299833
    0x2010e030d050309010c0807090909240c02062409090a1202030310060207030209060f0a05030d09050405060a0e0712060b0301151214071b080309150a06030201020604020d060e 77
    0x40794010005115030310840707070700c0700755481c240c41c5035011442282800d01038000baa45890404c0e05250040004094400d411078060701907008400900404100a00801800c124005041250307a603010307040c504014202074006108820780c00c08045402c4114107400300c142c451031400c0da1502c410700d1606080c442c0250075550340c04e800600c5254008010342c800c80075000e164160547d503101c02c0ea5250114080250b112a850001031050b00f003102d0304071880c840040c803102240c0d540720040307400c01d0743c469001e8000418000302817249044c9030080c660070500c241c8903041c07402d140c085d46015980e0080c00e10400c001d59107100021141594200344068484990075a030b807941c1d1000d061049070501540300300410010880c0082c6e4607058403901100b40541d400b4241641d0790200c048030100d001030503600c9480e0104003010b0104410001842c07103000310300002d0254005c0540c2075160300000600c143c0c0c0c8103040000c1400141d0b404a00030307800950548140380d0516003440c101c0d0160500319a504568 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 561302329 1250 561301079 561301093
    0xf03051b22030f0804031b0503102c010e1504080712050715090209090d1709100906050f010f061e0c0506090a0201030e12030105100306050307090504170c0a0303050402010e03 77
    0x3122001d001001100d100c7c03014520405136407040c55850a905206155264104c1003030203000c20060303000540221142c079101c80c84100501040680003040111811701c3d80c1d9070315403102082c0f008020a8800d1400c0c80701e21a4640b03410b6035003080c14441c0e0700700282200c03043c1c002a850325004074180c0740150f900030040c0d04007203145510030004005034241030348101300e0b24020400000022030160f0800d19203542300e1080c11005411420340480180c99500300d48640d215242215045208184040b807064034040340c10304040d00100a8007030b06070046616203075020300c1040b2a50704901c0481d082d8001d4040d0640c9071000482c1074960001100f005449800f400042007000d04003c520004c0c0c3d42d1003622304210b0040070f0b0b442142d40c0c0014601801c14141c003000184150724101083c50783c01043c500d00821003c1c0c82c0e20110b420400c10b81d001d148101e444205110402600c41a0080486081c07501c0f241441012000b050340c60669010140074559280049000d5901c034039401144000c001e401c607400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 561303579 1250 561302329 561302333
    0x809010e0a1d01060e090a1505060c06090c010e060a0807030f061404050a180f080705030c030301060e01030903050304081b0601061107080105060a1502100c0f03051b22030f 76
    0x2004001012140e0b19072032110002c50b904d4020240f005040e04041c086546942d18515454000d1407004528400e1004010703001483d07640e0301d0014810302c079804000e03091900700240a50300c1c1c2001d0350b52103414000340c030300381c0042915020190f8079402518a404d1855031207128060340100702021b680d000751030074020702103022008000d40d40c001e6041030347d08119a580d03090580c1304a40c0c40c50200a100c0700c21310f00c0000801d074004076400030203004041c0c441c5401c0a5541d200c1ca154840319010800e900080700400040307402010700486800e003801c051011808513503000307080740710081c0300400307060000c581d40700c4030980c0c0c0c8056854042044100c4100e56100d0501074003580a0846907000381c0301d07286020510f004107010f890300900e409081c94003c581804291030850301e0701c0c202d85003140f0880c1851000508580950f100c0d8209949829064604601009046da54010045840c5500b010204120008054100c6e141c1c001580c07040f03031018a100404543d0000d455001900705c0c0c00328401c0c142 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 561304829 1250 561303579 561303599
    0xa060f080d1e11011805104a0601060813050304230a08011e020705100e0a0b0709050a0801051b1c14010504140114040c1b0302010c2a0809010e0a 64
    0x900d00d8040c20850300701103440f43c844425034100140382c031a42094490001c503504004c100d00401c00d00c0ca210840d0040d40c0c056140b05248840780d13003231031880d40a000100030240c0c1040200d1b800c45c1440807070901647c1c0544490303079203104038490700581d0b0700f0501502e90160101d11500c151640003d003d501d80681d2b50b4800d5010f0403000f001b030145580d05010541c2c0c81c541c43d20868108590050240c81001030901c1d03a640200166014014603003d42c0c011f12000a0f6100171301c521030840350f00d4442c0101d0030202482992101c0d50040301481c1e2504090040c403c590000540320030120040c0d00360b035002180034694000748074004100c00307030b0708200c0003100d104100140d8134161082582d08000131084030810784409102072240d10340a1102030795054450915401006050340e080c1448020f520b483d4400c08200c030128807050f0010b0755500c00b80c1c002d2a60042810f50440608070345c940140c2c2e551f405004210228480041c0032609c0007850030f07541d074000d40105030b420314002c1807a0702c0d00d565456101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 561306079 1250 561304829 561304871
    0x1e080a180e19050a091106070204140405030d0f02210c0f0c060412080408040b2503030504060c09060906110705060f0d05060d0c0306020a0c02090a060f080d1e1101 72
    0x8060103040000044c5551054818660640d0b00200030041105610092060f107078000903050760019140e86456045045178000b45001302d11030001942d54900314869030088562540c3d181c0304150040062102e41400042c1c05000b216140031810310903202c81030941c3e0b4500c10703105800420381000ca207015940300b010802512941c05143c00c203c40b1256040d00300d5442100710b400030040070090101b80300d040d50302c034003400218040615910300001d280c4040301c890b443c1030740d084001070b890308200001c001e06800740c000c01150070305084140504204025200650a004400c20005d10402e0705c0c0844408000303c200408015060982d0b41240b240001c0655011304e4488464070b00300400b044071803c20354600951703103410003d801035507802d682c1c802d00a0360005010108200d81d081c0c480000da91200c01c00c9008005540e00080e8041c900b520040344010503611400e02a086504284510394202c4d00a441e201031140c00d40311074041c07a00741a00d01c002c2005011910307601e40380944034a014104050 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 561307329 1250 561306079 561306121
    0x50919080705031009031b110301140402040b0d031d01050d09080a180506490f050103051507021504120801050402030403020c040c02010b09131e080a180e 68
    0x9548140c83c000030840680b81d41d0317180203000035007000503204a209103144810035240f080008440c1d0301402c01c002030a503242c20140415090031078080c40214035091080100f640e0042d00e000418201548000d000c0142018170400101002c0021004582c4654203c6649040d491400c014a4001d400d0a920725000001c8400204d6500d040d944062100381c84100c040301d030000c2040d0301d8019a00035640300028801b58503141592400c070b41c0909c001044441c0341880120710f074444111800743c1c0c4240161519081d89003a49403804006201045010460007010480315400c04510380b21103808a1800307540c2c0e44d0b188110040d001c1400200142021891072041150352140550391700c03070040204034030055400070050303400620030b000c1038101078015145c4c892660000181c01c0e03000d1004074905803000c5404e90710a40003042a6001c0100d0b0389426418591038503c50a21139031181d40f864a5031250000c01000c0c40b100140700803080040d84c0f4281c000d403031640c0d00c0702d445081142d8482c500b0b03100d01c884 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 561308579 1250 561307329 561307333
    0x609270703110303031b0f070515070201150810051305150f06090603060f040809060703050717070b010b09060f18100f091404020714032d090105091908070503 70
    0xb400924500041640d008001880e604098440c2c0400d40f10341d80ea0240251400101082c00548003050b405c2c895003401c140c0b4074005441600c0e240700001c1c21503c0001c0206043c0c400314000703100e800400030308410101681d51000500341c0340d00c00e2103415003c01c010700600301d1049160055000c1c1d0b035101e442d809070380c6020400c3c0044e215441000808107089038110707015804100011049138011600340d4125028914480c80d10380d02c1e402180722a80440da056003c110002400d1040200c6040d46501c41c41f0004800d6040400c19a52036484007010320500e050908007017441c5980303a50b8581181d40c150900110582da4540c0d00030b415a0f1041c600100720b1084814001c2440c1440c02340200b9007855005656200702a418500b00065000c0c48a99140c3c00c56800c1c4103a90003c0e058032481003a5070111030007140c0f01c10200070304008100540d100d284d940030301101c2944100102130290b0700001800d0034120384440c004ac1c00f20340440e1645280c10501a07000034000b90000e0080b554205aa105800b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 561309829 1250 561308579 561308603
    0x406060f030b0402120f070309060507111002131502030c011503020f0102070e07032a082e0603020a020c1509040c05090f1011010519050114090609270703 68
    0x20041280a149405d100b8075121a0004641c51440d00345103500406504001036020a2034845000b103850440392200440d444003112049000e0030420004001e02110007986001e8148600030360221583c4220603c1071501c4e9113904d00d407802800ac0c0c0d4891040007000f0481c01605121401689942c4c0c40706034003411540140b5055175202090306801e4940c01a541540c0c0d49800c00214020400c0c807810b0b4104a410f4503100501002051841b00c403002e641d0340e803c08600f4106440c540102c000e00317800d19840c0c0c1c0c0200143e000741d1201c00c03d0040705c241c1d080050300c0740c0310900180c1c28095001d801e40e40c484080c6941c202c455404401811070305d88103690030040b00f080144140c680740700d03492005500038100d20398107200f8179000c41400018002840c16000086021400e1070a4030f606481400c0242c88200e071900c90040c003481355a0050000c030b0001780c5000701d4680440d00c1d217100035140d18018040c041c00a00807041003c01e405113441c280030800c04100c1503185950700d4900070f00040320901d010070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 561311079 1250 561309829 561309851
    0xc0f0d050d08040614040c0e190e0c2d01120e010516020c010311040e0a0207050d0e010311030f1902131404060e1603020c010914061501020601230406050406060f03 72
    0x500240b10b035a0000c00e11f41218204110000d020000030103041e03880da001d59202400ca5010f0003a0f03440c2c403c2000060103900001c0003004007001440404e41d450303940800088103108081011904640000e007400d6030320125000d141e0000e0024003294411541c00e00090000a940350502400340070001d5003035440c56107024004500b034810091052041501c10701060010401c003020b03140e04000f44020041c545035495444500b4042c60303080ea8008900403a41000003560140106000300d6100d480031461843d010560041c202809030010520040d40e03060524507400980c100e4030444500b80c18009451703542c01e80071850040c00c4600a000f9414004001a922521801c2e44e0062071a03442c0941d825010400449c0250854103000704c096403203503102c00114144d190b0003c100c0d440d4901405003450000358514040160706955811035125900400c0100b1450304010003400d070411100050140360700014026006070f81000e50300a1030311200023a02604490004500881034a0502c4907841c19 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 561312329 1250 561311079 561311111
    0x906010816090218030a0f1b050607030f021627020406021c18030804170604030806010c020d061b1d010210020901030e0601030804260c0f0d050d080406 67
    0x115941d4040303030341c030003091004000580140989800c8400d00108110504001a00e80710034580305450f501003040004003401044405102204424120541c032507207040f0105640780f00d881d4000c0c04002e084010b030203004e4400e015074250313100085102040d0b80e40b140174110b403c0d5420b000812024850001075585a6114000e0318100e40030390b0094007980380d414400b0980e14050460000422206060b01450b049240350100040c41c000d400994445040c4002007864000b010091260750380321004200000e40d11a010300d910050a20b08041d480f003862010031040e80c3c61910060405040240200b030f9190403a80030b80b403402c01c0365601c0e0f482c40003440d0b200aa0100d0011038034016040a00d14800c600001c0e001000784280600d80001c0e00c0c10b242981301d0802f00b081e0021180080000f40c10440984810321000240d0515001c0c1c45420305201d0080340c0e950f080202560041c040d011082030965101c407050f0302115004410707145d00200e8030600900306034040b1011107005191041d15110348040d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 561313579 1250 561312329 561312343
    0x50711041a0f0d080d021c06080d0f02060f04060c0203041d04060510030b07050319090606080709111801021e06010503060a020304082a011802180705070f03022409060108 75
    0x90f1850300c2d01502c2002c011f58491000d5080c2c1400030151403105e80e00f40d20818008103001303030150884803001c031001054000509049411544007034288200003000c040c4550300154045000a4502c8442c5402d904500070360f03008042c18218a101841e206c140c4001c501e1146124050400096a070721541000250980c00040e20402400000a8581d0b005038010368001e441c080031051003581d41c00000056a55040c41100c00a49aa5003000111410403640000d050324020a10041c500d4141e600114001c000490740c0c1d40c41c80310b03520794a50740203000030724401a0044450b011106080505962804203100c1c03240a4403420000402101040c0b003500c2c005d940c01007141e89048200712002d0705d100125800030100c508111403400250500740f01d2030400e41e62185140007456198010801143c420441224a03010baaa0030485c40c1503104041b00c504070b40c0100d21207000e060a090403450142e2100746111301842000c0e5210ba08100080180d1184801034100c039540c0ea20303004a1619052 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 561314829 1250 561313579 561313583
    0x30605041110080f06031c0c11011d01081b032a070f200909011406030a02091303050408100f0c0c120c0f0b010b03060a08120901050711041a0f0d 64
    0xa5000c003103603d007041c0d103d000e904517100070202e502007509019007519200030000d48030f01051003030242c1001c00074440c654003005d08090a00f0300b40c202d18405410310111001c0401410401041c0c00102075510071002100200c00c0b001c2c4440d00c914244d50316402c00c400050b207501414009640a10840c03001000301c680541d400440c072420030005565074100040011040c003d0952221082000c98840c1c3d107400d4441d154450020035082480c1056502c5540050201ca010750001c201e503001586880390001e8210030200d403503204c50703081400c048407035000d0b49d005000a4000d11000b066203010542001c000302004500400410140c241d05640140008030014030440c89405034503a114041d810890007a4003d1000c07603c100303510350b612101304e402600215844d500100c103120450170560700c180c020b08001801801c4500c2100042d803141e005240f14141007140006030401001191401700c060904050000e020b60b8002c44211541090620826801443c00089441705403a20308400ca00b010303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 561316079 1250 561314829 561314837
    0x131b03060f0905071205092505040b0d2001021c02030a0305060603040b0105100509030102040e090715080a09080c060405010c03180803010e06040204030b04080d1104140f1504030605041110 83
    0x1c0017050050080c00e40140007016500450840b0510705000c11140c401214884001e030032868207107420401111380d041d0700f050145490400c107100244ca10903c0d608a041410010900d501c1d070000100d152403400100303140120034908040801725000409000b5000d403d0f10b092055548501c1800810b010417100901080e0341c0800400c03190414034409816014145080d070b01e030030344910109013a60b00a5000307000c80c5582501b007103a010414000980941080c01d100b00341420a200d008181c004050411100a95140203803401c02c40d544084913501e50881055503403070714050421a000300120303a128008a8140f81c14800350403070b144800f02c46564001c1001c2e0450342040ca10554940009000d242c00c95403c00c80030010912020fa442d200d0342c41132807078581c6e800c2c0c072007110707004c0e03c2e20054850724009003404288000c0d10710b0004c4031103102e000c0c0d8010240b800c9030000651201d415080e482080400002d011040c01f005820103032183c2c1c022001c1a401041aa00303010502404000ca01c0001d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 561317329 1250 561316079 561316097
    0x606070f060506032503110102060c0403122115090e030720221413030e0d0b07090302180709030803040827040f05090705131b03060f090507 62
    0x82503035000740d800100c082c1c01c0322201c1c0d1a410030707040c2e482d0701000c1095045d0a41d21040003001720280b0a07015080c0284058081401d203a003c8400c18040c90100030702200c072041c0280e04503441100740d0145400c440030f40c81001c1c1da4100f1072a009141001d904500a800c443c00805c0c802101c0c020f000104900710000c44c9400910340300c882c504001030310191403480c840c21214403603964006004001c28680b00040b4640e800d42c0711500d04403441816103100b000600420850806245401c44040d6901801c00c000f8610750140020f043c1c0c0e0010b10700400c0782d1144400d01030519130000120050701e100369401104045c0c0044629254002203802c00005021076a0500011749910301450700184205113a604004020030b903c001540203819400405902c0c40c9005158030b441d00400a480d8140002080039050064000d91100c8690040e280181d245036510741100d8010b0b0302142651010244c60030820305100d000800bd081148910000c0302d02103140800d11a4803881480d00841040c0c41d01c6402c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 561318579 1250 561317329 561317333
    0x60601090302060a121b080f100e04030302070501150f180203090304120212060f19090b0c03061311070b07050a1d0a0503060f0a060f0303120f060f030b040b0606070f 73
    0x81681708400a60302580c1b5901101c808418080c90760342000f080f500d07980c000d0325100c0346952081400501094400c50100c00c100f00003802d44014680081d058540542d0382c11040c10700c240544941440342c1e503001007101c0c00062500445403060250307121060507048450005070000240e002c10358001c06947c104000c100005071001a080c1103580c4042d0090b840300c1e858100c068180402110040303191401442000002c041c001100911038582c0181081046420340350103201140c0241003e480c004000041040c5545046d4010078248542c0340c180400c40c504200ba180c00c0c4c0080c00c040b9502e151540101c6c0e42c141c00f4a003030720703c00c0640340c0d55045214090b211254000c0e002030100c03908000303800c101046c652010b111b541d2180d865000400f601e1f0500c586030000f2196181d100c00c820340f0b000318013800006d6018080d41c222050400c4c2c081441d44108a8060052065a000c919259400340000080000e8008c82c1c5110f90300030b070742003081035403035005220703951040460003061101ca03e400800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 561319829 1250 561318579 561318587
    0x6010e041e0b031c03020301180c050d09082a0d0207061b17040b07110a050f0f030106051c060e010501150810050301050106030603110303040e0c030411130b0102060601090302060a 79
    0x4502e0380010f0032103414600032902001c2120644541c000000e40000c010b208110040c911100055040b03403042001520803000141580500800303840400c0c0c650400c41d0034003c0b040705981d000705032103144030f0354401001e078501c4e440d0040c61403030f0003180550070389052054004141c082c100c03080c03610313003040c01110b81d01d40d40d01108420400300c0704424425402c124240001d4051f002901c0034010150f51100b007420720074090719401c100035105201c074003001d00060f2030b00b100c1c0c01071071401a03485800b480d0400c80043d01501a9800c000c0e08001c17500d64003c406000c01c20044800d82c05400c040115851400d130540c241d400901070000880d032030303006000c41184035150850b0302940000002070310b944c0b0380c00020f003074030400e911520009441e91401e200f0310030303100342c030b0b082c12801200118507140c0791486150000b54010b0828189480210018080c000d506e85c1806070000c00426021a07178862850b150021b0145d08800f0f4018411f09000441079401007008005581c5c0041c00389042601d0480216 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 561321079 1250 561319829 561319841
    0x190b0c0c06090603130503130312120c05090402092d01180f0b0a03090b0921040f120305040306020715050a0e06040803060a080a080a1e140708090909010506010e041e 73
    0x2c801d1f2200f0808110000c2c551024100030754422400c0c45420b40404d0b4000b010103011070403680d5114544140200442d0b005400c030f65800900b0354000d0f0702c48590324002190704031009100700b00000c43c656884210b0621450150204400b41c9820400c0307070403d490145115074070301448000140c2c41d40c0501c4581170070405001025158580400c1d015410b644807020b018060b100080302d80e010b040526098502840c0005d50381211004240c1445d250800307010542c6000d00c0798660300b005c50b1100c038060610503001c03140507540140041d0344d0751000307182c0300441901c04125480f200e483c00300818007140550062203102107016004260645550301d807034025500c042c208503440019503c00042d41e01741417086001c034500a1b42640d48a51080b00701821540341c1c2c11200c0c200001e41d28a9001568110f407140400003100c03c81180c8413103413898001614401c0380f111a0303018084108001440005400c010b2191000303985030004a0840010300040c2e640c00034820a450544220954604a03194010 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 561322329 1250 561321079 561321083
    0x40206031512010902030f010911100203190206010602100b0108061918051603090803010e04060f0504210e1e0d0656190b0c0c0609060313 61
    0x8090040454000540e8801c1c1040d9035520300c3e51909032030302c15481c0500000954079000b10007407280042d1603450626000c920391034284503608006408203064030810a075004110788941c1210300759612013020351340b00e5013445280014485c10840b030700c10082e2401240704a00341a1582001d030b48921082280c4000b801c65885d01c0301c21064400200b001040c0f0000c030794442404000246401c0408954010418052020080c0340c00c05041d4000294090100d0741100e44010f074440d41625545461409480042c64003e421401c3ca0180b00c09e20410078440402260310798034100d0b821041140955200c86a0a25941e02a0304407010740044424410103038040e1038014840c134501035480e41d950088425034901c0440c04500f18100c100da034840490034250494180b080c80501039441404604230f40d400914481e550103540c94105000d884603c450701ea170092078040200955100c0404051075000719442c04840d00c2856000c840d00c1c00d01c0310440317004100143c0420300e1a90b03541c0c01d0783c6c08110b0309002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 561323579 1250 561322329 561322351
    0x4030c331d030607120f02070512030406020405150901030f0606021b040b041d1b0919090203070303081506040b0904020f160606051314070809100510260604020603 72
    0x1c0800d203a5000d12400d44a0394071170f03c0d00c2000d070b18000c800c20121a01603141c42c107101d2041003803902190000402c48003007c20362014980c1daa4851415101038081e642c0030680010315017404000900700740b4041c0c4200c240a82e400c128040c048150a01612242e211380d0b005038000800300003000050003e5001c0c16117029001050001450000c03c04503244000c1120340005010015413101b1401d01650640240c51140f900200c940c0c90001742d80d4030406842d000ca2942c00d803482d1400c0c40842d4001d000400d400500360b880301e0380d8138100542510340c00c80b000c1d0390b00408844013084920701001514240c0d510703500601e0a0249000a20000303600085000f40410340c00d105042810314080c0300030f4141c6201d254080740761340c6002c0500441c4031641c10f00c0d800700c03810100c412103024840300c8429400722484c0741c82c6200b47c031101143d90a04039041d02c800031090a0604022003031083e01001c10071202004074400980100c0586241e0000b40d144030310050b500580d02040144c58410059500213081e001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 561324829 1250 561323579 561323627
    0x31e060a08060a0204150f171801020c0f0c030a0f02120f0a061e0507120f020906210c09030304091e020a0201200c0a060e0c0604030c33 60
    0x32200d1410030210f90420903950005002d00c044404e80c0000c0f400b03a103403070601c600760314041c200140401c85214200719510109000151300e4200c50788100a119400f107008550b40c12401c9100d030b440f4440348001400b1440740c52065405400c001648810302ca421603048414520b240d03003041714075144842c4d9420345203d501501c0352100c1003480806082031240100107a00c1d0302003c0380e0b0111038208200e80040350f15210030007514a07001041e903001018590400220521061200c0700240641610300d500090040794034071a1070300c2451080c0e0340300700c82ca62101a030f0f13403441081030303140c800c22181e9034040d00148070401101c2c44540001041d0000030164110045440c1c0c80001203811070920200181e4440d0802003016030301c0c4201c0e6004520464200b45030019401009a0700e0b01e16840007844a661190a48003d41e0140054032001000600c0103980b5656400c0210404c8041c4c0208240f6000710210340c0c010b201016150003109840308c03c00c0840d0704446009071200010102a50500c0140c14 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 561326079 1250 561324829 561324839
    0x702040c0f020d030606080a0f090c17010b06160206131a1c05060a05130f050f091903020c01140904050406050a060623031305060702010506011103031e060a 69
    0x10184101100896851845207035074458000d1038110000e04540c24145408028001e50f6405500550300c40b910400118030a4814942880144160040174180889210012900c803a0140d045d0b0860340c044030081c04186007010801c8418803d85000a11906861030200e0041c1054005040b440007400c21941d04156101c0441006020500034a61000b40000300c0c05104086e5815103030040c0050982089580750410108100c0c40c1c036070150178810f9000c0051b0001450302500303c07201c240c420072024802e6040003142c07408001002e0b01c5220290180f0310b020096003134504840e26200740c1642c02840342180c0180151080007224007640d540113030400c00e03009541c44a00502c0d026500c1442c000441e0324000c1301c50001c660382c030740140d01040703e40190401002c10150030a5440881e040c400d84d03032500c0d0411001040c58412a000781503005180402c00c2d0f25070194030161040c0420307290841c002140410b415100c1c88110f803020311180c0f40300e440603d20a00007840f107910540140641d100b0b42e440e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 561327329 1250 561326079 561326081
    0x708300d020301082a01080f091f0f0e12090405070903060221150a090b0f0d050c042a0309110301060f1e0f060c0602040b0a020d03050f010f0306020c03070204 70
    0x260031a0a03240e0140400e1110103600840100362070000e00d501400901c011710009201c20310160900c030300b2440320400300315a0b031414014044412004509480c211098000aa0281c001e04410b21480f900d40b41000c824004003203800502c80300454401841d280486040200420010340b0341d104010034801c0120028015100500f40b083c0c2c1128441d0303141e80300e05ca090340e080400810f805280b2000c4109030089450701840b14055401143c0003141240040005c91000000801c181e41d0240320001480180000440c03c03001c013840640c0c09200501c46e0707024240c2811410102440001e802c41c801c001c030540319a0000540a02c6803c0110604022030b00207400d550068000c070303060740c41c44041000f030214200c030441803400c0c0b0044450615031500a400540020600c100c0e014000300107455006c01c00554110f0f0f01420f6403841441d2501c210000082d42d482607906084082442e003070102d21150000030b0200d0482d9441d090f4145081d02f180c1e03d50000c0d41000e2400f41d003603c824415500107a4076 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 561328579 1250 561327329 561327331
    0x31110061a1c020a0e03010501080f1f0e1c0f090614030702121911060f0403081302040203010b0306040509070e19060503061303171303140c0d0305090708300d0203 72
    0x31917522a000300d0081000c00d42161b206078801d0001e98081c0404404140c0085650210400c10a542c0c00301e101a0001080140500030b142101c5401a40c1c1c0c09165017000740b880382e0584078070f07603103605005401e44825202400740d07002d400c02140110700103282e6419920025079015103c2e00c19640d46004110840304680c1281600441111022030710b54449940103841d10a20280365005000c1401c1000d6544c190705000340018082200460004040d92214000e01c00740c0350380640119078039a550b025500c120303001a10520f01c214149804104d0341c200000729001911280b2010f120141c03038580c00d5980b030039441c07006101c0098031600006030580d424425075100754028a171321016170240c0e141c000c0c030b400c2001ba800810940c2090500002103d80c0d40400c10503035150400b0034030000c0404428040b0301809080d03c541d446550120b0200c540d041e000300d4007448000c000c6995a9858040700d544414660100d013003511258000401701d0481880300032068056888610303d400c0e840740c2c00d181a40c1c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 561329829 1250 561328579 561328597
    0x70206030720010c031107170a020f2a0105070321090606350304090b12030304120801060903110405070c0b0405070f0f0b121012031110061a1c02 64
    0x154405465813081e0305805695901c05020054500d05644c9580d0000e14005540c4500c03000b0002080302c007140b500810441c40901036100454102c4a900050f2a02807002198058450941c1c264003400700d5010707030250f844043d80340e103604600d07401400701c05c01000001c14030405c0d401e4a40030500d010400c10300c5420058000e0504201901c156100fa11003410340e07404413440c08448a03041c9689032403000c002d036020741d0390781c0c0808914a000340002640b090301e4000700342c51f039000010a00c41040410310200030001007944030029960303620407050700c02c1140c520000c1c1031405005079496142c076150b40700d994426a942001d036a58011622500c0c5c48070b5044130704460795480140c0c140607800c1c02040c0c03840100440024103510a04080291906d400344030100251609040081260a140000e0307085c0a400c0c601082e22561102e0300340107101c64080c000c900c2c241e004a0040e091031007120700407a0b01392100d8200c070800818040c0d81401950b400b070155011000500c07007039400416024001880c6a46c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 561330935 1106 561329829 561329831
    0x30c121e150c04031a070309080c0a0209010b0c0d140c030301150e0301090c411201020304050d200d0e01020c0102060609010611030c0708030a0207080105070507020603072001 77
    0x3c40781e018012701d40040070460714214580000c00200c01d5000720340c81919640e80d036218807624460305643d089181c00c01c0c1075a400481c00b41c100d583d0a4031a90050f14908868106260f046810070780040080a180400e42280917900464103040c1c3c5500701d0080164490640d2900c40d100c005105128061101031511480c0b00030440345008011600f0f00300d071545100d0015154009000d07860000d2003072021130307005100f602c8144242d80c420b42d07014009003071520a850303042e6400514480c600240540003485808080000e2240307840740c20f21522800b20310696a40064107140300e039404e8504640c00038040103040e584001c20141103810f40d00300352401120001c90f4501390706c180d0510305018800c4413400208e01d03d000005088001c0117900f03840d582d40d26000c40138269003040d104c1e440010403e0141ea001751800c03500640d005241400c2081c0344c0f0a4019070080442c020314103c00b03050b = true := by decide +kernel

theorem cover : BRFrame.Cov 561151079 561330935 := by
  have h0 := BRFrame.cov_init 561151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 561151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 561151079 ≤ n) (h2 : n < 561330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
