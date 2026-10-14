-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2590
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:09:38.208965+00:00
-- url     : https://prove2.me/submissions/416283a0-8980-4270-9e5f-9c6fabda494f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 465647482 ≤ n < 465827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 465648732 1250 465647482 465647531
    0x30204120309092d0510150203030105030c090c0a030c0c140604020a140307090b0409080c060f0903030f010e040203120d0b0f03060103120507140d050d0f0606080c210406 75
    0x5800c01e000d18000d00385048400441480042c1a10744000c1030003803106c001920701801185131059411014404001d40c0c0790024400d882c400d110b000a084441e080100100b402005400100c43c5492690b600540143c40c00b0801380003000402818140440d1310340c03044c1e00b641900000944041d090078010428030081640014101c0054590b01c00200e9900183d0b100444a4401020850300382d000001030040101c0d110141840e070f0000b51032a00000d000c94024401c841100d1380200b50303210455225074a010841d00410754400c44801800880004031605074410300c010b08841881c14200345000c00380c0c10017002249c041341c40b810352200c1c034030b03040000401c0c141080d0000d00d41c662558880b00c04850080042d4400d115000801d5000d000c800780c18001481c4c1c0c2101240c00030076400c0b000600a520a0250f060a40d151648002c00c00d00c4601900d41159502c4d070b10f000c519100c81d4200b807034690210452400d1844000090428585544040c1d48a82e020714400901c03418115440c0c04401c80400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 465649982 1250 465648732 465648761
    0xe0c190908150f0907050a050409150f06031e020d0611070c030606080c190302091b03010f05091602070302090a02070501050a0c1b082b0e01050405011a090c03040303020412030909 79
    0xc40a204d152107c108900490760122800b0640160b142041d0080ca00d40b4001740750300c00d083c51025198140720750000c4048070320840000807080c2030004c409a100548030402503101e04c800b101c0b03c01040d075541200e4100600c40c0c03900d901c1e10b00680c0d01d501c00c61045078800c0796201d89034101001030240c24007208424010985084441141c50101381e9802c0402e800024410300d0000c01084000c800c072407000301c610211005e861f503256103441500c50300101901c11944512105000510660303400320101241c00b03038a40051121a086508021503980000e01050480c3d81c00d020103c0840c03400d0082d14090700700114000344281101000804103070b0f00d4051950281c020040b40070016245030102e421031485480c110544070407c0c1c1e0800030f50f40c885103003084250b0030904a0b0520b09019480140102d2244000300040c1051922a1544550110300382d07500c10b030704071300040c840c0f8108001103501901c00d1600510341900e840d02503140800303a400c181e0000d000103909010120b140d2103134074a480c2001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 465651232 1250 465649982 465649993
    0x90607110d0614100806270f0106080c06090609090405030903070306140a0501030c09091b03060c08150a090218150d14010b0306211b0405010e0c190908150f09 70
    0x41e0101d5a146e00c003411000b091244405540310585040300e55820000b00042610450711070100b00d00c0c082c2c000c81c000e815450041044441c09490003008981004002401507414225200b04008000d40014410380310390100700089462aa001c1c01500050b5108840c00a0340407a941f0303c1d035841200c02021140fa1910700f2005001051a400c0c40e80d0848042c0400031820003a60b162002e20707401e0300035084100e01c0b00100d010081002035048681c2c2c1ca0b01c80d644035040c0e40e84030b02d449103000321042e20841c0c000b01d04000c10b00542c04690010221507041d809043d2420784c0403404071381030364024526400041c5022070012001d100a0084002200c1c001d0341d40401541401c20040c194800604001d10406030414101c0918281a80130303004000f038901500d1490040107160310b003803007410111600c039514003400444c1700c80092090901070100c171741d90703e42001e80d40b580140180074040a8481480b11070170b070002d0448410480c0983d40310710a0b402001d03504146665581111000d4185074498002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 465652482 1250 465651232 465651239
    0xa1a0609040f0c080304030c091b08010b160210021509010b09060108071101060e0a0f0203040c09091b0b1201081c180503010905070305070b0f090607110d061410 71
    0x31250640c0c1c00940081e0001c090030320702e1a14040b00f200a5001d110280401301b80003050040001b010700442d0000703202400a07001c401c4210800f0b40440a240700415000801403101c4c00c0004080c1a041e6905c2180c030b0b40030201500010303c0d00001105400c01607103e2803100d96848210401c05030000e080d0300c020706c0300315081b0300010040e81005200318100200382c0002006e041c42a440410050202c400030001d064070b4004030811554112142c2c820182041d0f0008051001c42c400c40307100300d8000009900944c2091442c6014020f01e01c41a40c4403440350082960380001c1c00100001400c1803884a0350b5000041010614040c050b071190300d150304100030003040e070603105210514140044c40d00000218540c1c00b03e01102c3c0903501308541642ca000c6801e0204040061200150f0b4083d1301110b48043d9500c0c0c00c141c0c58030403408102125039050103030107018140100035241c1544100c2c2240c28035146400415080c000c10003080d42c0590325501505d00703070360385c490301150802c0d000d030340a0741103d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 465653732 1250 465652482 465652489
    0x150b0d060e0c12061c120e01020313050603040215120a050a09080a030c11070608091612140304212607030c020d020a030305031f06090303080a1d0a1a06 67
    0x2008444480b61030743c6400a681c0783e6031014441c0082e501032016582c0410b46041440540e0000e185c400c000c2841c81c071070f180320345d0b00000c01d03280600711ba0301c0f407280d0441c14403050107440c1d04040c1080307810103a420390b01c07800d18203480090094082c0d800c2030812185450050704094840141260001614104804012582110071550050351600300840c0c2c1c9542c02c0d90490340c0c0180c0502c22000d5001c1d146e004158260702805a6005802450032202603590500e07104540c2c5a60340b09044002c9418044d801c00102e64041000720300032142d090f40d017023a41e45c00110b10315041c0c414a40b841460b030700810008101e084140080352070a0101e410341c55200d280e40410705445031910180504c503400c483c00c0115a1401e44d039417825540500141c003041e42e40d26010f001500182e80d0104185c64548410f42580c00411041c42100d049075114000946942c80a0b5103121024018907a11340c1c90344062078016200001510344400550014030140e2400d00f04010144901e40260218140360030501c0090f80c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 465654982 1250 465653732 465653737
    0xc01090f0905070905040507020c040509010b014b171501050702030c0607081b0a03050901110c0a060f1b1a07020a0b0702031b15010612150b0d060e0c 66
    0x591030030000890f5181d6240c00c0d103010840768480e0343d0084c01d000800807a40d50206a000c5481000d8800f07000340e46892082c5030030303140c0442d00c20b0300146000a100701a503071301595085401c6014011420150b81136140c0b214440f6016000740000d41c40c0190f040b801d0740d0f1007200c0402e10b0b81e040c01c52551a080c400000a0348120f20400541000b0000c52030b0303425036070309000200712920000c01040c0d84030000c0c40e120220740c01154401010508503a0704149122020450400c1c0e2036240e600c042c030380710300440150381003c40303d40c19911610400c035210101c1d4807a00b242c9000340c00e0310b84034000102070342040240303529140e4001c19841c50030094030400007043c2039680b0340105071450380080310f665508400c9280c520f040760007030038011341e042c144001c082e000300040c4012195401c1504c1c90401140159941d94640405400c3d03c0c0c0c03100b00100001c80c443d80781c1501c0700440050200f118403480400d4095000150001c42c00100d00003803c1880c9903481c401c601c000c0000e100389a4041c90580700c0c01c4c0560 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 465656232 1250 465654982 465654989
    0x2010c1d0102010e1c080f131212090f02120c01140711090c07150507050a0c0201030b030708070f050108192313060e0319210e0f0c01090f 61
    0x1064040d40415960b07000390082442c1103e288102c0b801450291926a2052110004100428601c0300803a150a0300004628400d00d0040320054980d10395079078008501d10403028460400c8882840c0301c4c208126030040c21401e500804852600c00c92900401c620818400c0c1d0791521907204040410311a60040240981d07200a02c0c046601e03900361b424480040f2010080703055111260b00308021215041c03001070903070940251003401139500c0840c0041c08841302a00c1c2c0801080c000d00c020b03444a032103020080100c52045c1740125201681d080860b01e0f00c03020380c01007942500031310300900200fa64021044001c01e024078112415061003078141403018804404050690348500a0005c041c454400c01c41e0700341e107003048000300da1a03e0003580038400740300501103440038100a400c20040100005640d0002d00c2308140b01c000c410294000c1d200c00c3c443c001e91000007024060882c80c4150075106a000b070521000180c43c02c0c45075041c046083c40c0b491202a41440a042e400b84042c0744a0030411095 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 465657482 1250 465656232 465656267
    0x306011e090303050d0906060608010f05061c0e070521010b0d08030f040503121806130308061c15090302150f0a05070e030f10150302030a02012003040e010f0602010c 73
    0x980c0b145c01800e6014007922500034160790f08001000540551000c10141250640400c0f4091103440300c00300440c61246a070080507000301e0107903102160100d90b00c2901c2030229101102c00c40e03583c44020a5502c0d030050040707540050010ba11119120b021301401e80703010710488641e46040c0c1150b961000da4003020f00500b110200500006040000410440d1210242e011440c0300c40c4ca0040405d041030040b81101660740d0241102160611040a544000703075079240e2500130003550340a05004400c0d106210000240d03035070802ea5000b0401e640c900a0101c201a00041400403650901918060600e4030780c078401c40782e074410041840701045080e5080311a0200200c2d4980342c908d02211221201008181d25014440386080d4131400001d0301000004a08001e100c02184d800d40402018080d1101a4041d0068500c0100640c840c800300d40f502039205111030300d0f100305621958a19080794102120000800e00184a11841d04000321f00038400f030301c0240320303d28103420020000c104050b60f5403070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 465658732 1250 465657482 465657487
    0x20607030b06211909110a09150b0f091e0907020303090a03081e16031817030a2a030b0f030d0e0f031014090a030206130f080c030306011e09030305 65
    0x4040b44c1d03071410410304842140a020201890404101e141c00c00e8607614851034104100141240150040240d0240000010300d1710514000c4c0c4048a58030481c0741283c03240c803c0014070300a07950134070a040881c2ca0401041042c051a01c1481003200d0043c1c400f00542d030007801000099180000c801092039894504182151504050b00442c481c2442441030101944010080c2040f66100c145035828459a01404104141d1f210009013402e5020040c040c003c1e143c04007864a04600001c40c1c00400e034801c0000c10403414542922000b07840030015000315041c0051015407a418000c60316517120481d0340c540d0151181000958808030b843e0b800c1c050003c0301ca00700c806941e48400c0a00c030340d003015098444481281e5020b00041200c0e10300208035900c10b00c00f0941025002a1221061b641500100340c20f880b141075005210107503c00c03c030765000c0402009400038081102405040c411040156201c1c20030000150100c001070b2100407110707001c2124a4000c56026507401c045a42500b4650b5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 465659982 1250 465658732 465658741
    0x15040b0a030605130519021c05010b09130b03151008010504080a030e01060e0103110406050303030a0902030118052d0102040b0d0f0b03031803010207061a010801170705130219020607030b0621 84
    0x301400012040c2401151400c00002fa1114040b0028808004c00b01d6014210100c03619000044500e40d43c07003507406520a80c0d10a01100a0100c104d8010203041d06a041d41a5290030103801e440c011101110010380209886414030703054081c021000406c00000e0000038100074014013501c00500c4003403c000d9030900082483d44940d400040a880702800b0760743e40b071503d010407401030040301e00c04034000d619100885400c43c1c0214040320195900030003403d11500c5010040d0f840c2c41e44c42c11a148030059107450601c00035024802000103040710000551500d05030765140b000c4600b0459020102400c0c00c00401d040d503008001c46d41c4004a441c100d425040c40d4502007402401180c000034030082c9402486603c410200c41891045402640c804403981e803941c105006842010502400c03603405504284110f00c0c2000c1c00f0f20b611000104010306080c2610a411605402880d2501c00b60304800140312400b50705001c1c0361847c840554803286014110301c00c4810840c51000a400c5000c0d810303002c034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 465661232 1250 465659982 465660007
    0xa021c05010903031d070e0c22030b040b0c07030f030509190b0108010b01050a0206071b06050a1a0105070c050f01140307020c090609040302060615040b0a03060513051902 75
    0x410059005402086500c07403628020f030084c41c0351502d80c504c0c2034245417480e000e5640050410142d50b02507030700b110162a41d010395841504081c48032a1820720090003690025940800c2d10011800382c4888035142c02c090514288c1741c030028001c1100b262040240c1c00100760002804580c0307215034500002d26036604075034182840101c61b1024003490081c4051414030581d0003000e4141c81400d00208465101c1c0401520344d880380341e2110700581c004030005880c06004805224100780d4a4a007000c8030f2600e95261411208200d40a4510540c0d40d103848401041f03071080710301102001e0801d68940b00054903030485800b072a100f00f500c5a10750800d0104580d00c203100058603885c0110070561203003018503001e512000d12601c014003922070030700010310700e03d0910009402036405801801942d160710082c00840110740744c9023421110300f004001903d180704801048140c88035500000c0c414206003c00208071030030311500c42a01d090006004481d0305184445191140421006035110131802a5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 465662482 1250 465661232 465661279
    0x13090816050f030a0207090b0d020109030f0f02060703120e0f0a08130302030d02071a031003030e1503130507150e010f09030803070903020f1203091e030a080912060601020a02 77
    0x602c1440c000400c07041ca5071a00022a0710617214107003000d06c81e19a1520500440307010b5014080d0010b68291800c1011034031020b142400b05002c0c20403aa450a00344d0003103900c99208041c114005614201d401001c10b4007403291403100c44082010740424920302d14942da442c149118027800c45c0500080400207030311078800c410001c1d580941944c0c0000300d011000303511125503204140503103030349503c030030b21310300146040328802d600310002c2d00c01484c15620100c8250000300c070080d07001100410280001000b0902031440b0340303e0b40f044851104c80c9407030400e04010082c0c1c48507084011003102414070540106070115500401c3c42d103516061141081210640c1c110f83c40038000ca40700100f8081d1465001240b034003564005e0b501d07a40c0e40b0515100740711003440c042c094842550000c3c0081c03202403a22a4a04110205030161404840b20180002c1d0610103004002c40e0308490000750702c1040d0520b05510200c40f0341000280c001446d02e500080d441c4c0c10300e40b00083c4200900b4000c040d015056010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 465663732 1250 465662482 465662503
    0x13020901020703020d0c0f0b0c0712030513030605340f0c060606230a08151302030a021b0304030c1a040e2415070b0a0b06030a0203061309081605 64
    0x241030b181c05d0303003400d04400c05111401420529440f4803408100d82c20244100c1f0710006004009140040c50114075850fa103044500c21020080304101e60704100c4011145e01001e540660000607a84c1000030080701d0319500c0e00000c80c01d503101c0c2e198562440d0000003030075007001228104500840030020040365000caa00ba0010070301e901c0c0c0040880c0d459445041d0481c510500d00c0c42c006c0743d1461001048450244c0c0d0360480000e60040001500c00c00d400300800c0b051031000c1d125503000107034100008140d0300215507410f005680440e59100005040580303440c0200c0105c0a14941425601c4803403c28241c0d0003030b6441804001000746044c0350920499008203070005c10001142400740108400907043c43c0707000b0859421080c0c525041c40e2840c403a080b8000c40300300700c074503101c07950f6a07e030709400b00206005049999000da824150315040e00952152103200b03801603a0340313007100400c60700b481c40c5e0074010181c518040b41d0400150f1103608031624038244104008100340146042440c003000b004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 465664982 1250 465663732 465663739
    0x309071503050106020c0a12060e1e160e0c1204051f0921020d0806031608070317071e062c060a180212240f060406051302090102070302 60
    0x210800c0d081e50550219060711040d5095400003d00034081080c580e0060180301e00e0800c541d1019000110703150702c0503c030b0455200c15201100648004251a80600c80809905c0c2d00302034280d141c134103da070107814081c5c003a5040743d008030b0401ca5003a1800e40030394400c10b154070b0700190100d424013400700020b1215111100e100a24011b903141d2a8002e400c4600703045414483c04541044511061020301150407016801800c0d0824a1a03080380c03540c502500311601401444200300c850a205404a409000c0010050501d50b00d14a03020f007298041940640e400da0b024003142e00082d0340c1d0404600300400b00691600b00c11304c541001c0000b0700342e0324070604010282d902d9082c1d03400c5003008401c0c992001101074174240d0381c45508840964020202c2e200040905403400b000604d410000f54003403008131001c407102400400180c20701c0c440e4202200031107814680411a001c410300034641d5120400761024060b451805001c00c0300002a503180e0300341c99802203025440350348200803c00045030010b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 465666232 1250 465664982 465665009
    0x711011d0915040507030902131d1204080613020a0302100509030d021c0e2b060c020a061b0207031e081c0c110c1302040b0304060f05070e0a0506030907 67
    0x45401019900b00e910305502071030034400002c41030b602a02c80e1f201003d8001c1c11100c010784004c078a0000801004400d00e00030313412000e030040a401d04008003000b200f49521075903a030b01e003410b84040c43c2c0b24000f05149108180c000400b001a20380e00b04100441e64199190030101124003030a90b0540a20048160903100b24000340306601d500150144142c0c100c3c000ca82021080e01ea01207a8143c24244080c3d0085104000c0a00003c21010240f4003000c15584a44400c0602d42c1c40c031094a1184d0300e0080144e0011080d0300603c00d480c0306803243c1e04080280751240c21480785020f9181c880c20301c0064915400034208450307140f550000b00740c2140e0710540140c1d59203544500302010155044151000c1031520090310034890051010001e110502e400074041d840780c000401c61100c0d0200d104c1440d01d5024000010361001c210042c2d805644152001705007201c200040300c0484030000d00903c10001a040d0384400d90b21070340b1a58040c1d85041e5002552a66019205482c11910380c1c001402032960 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 465667482 1250 465666232 465666241
    0x1905120912032206110705060d18031106161e030b030102040e012306030112050106171c050a05040302130b0303070819020109030e04050a11130806010504020711011d09 74
    0x1440c591040750105140349242c0c0a48480c0203c4201116402d1100317140e101c6c3c8010f002516146025124510350100c000c603136400f8100300e1304a200c101c20303c11004583d80061a25032040240b00c840c3c1c1c40800d4481c01a00001701c9000280942d0503800342150544450949480e101d100760443e20b844035005e802956241e42c0da019038503800400340300741202d1183c030408024082a032400071030780b0580020301ca142140d090615402c40c02e01e0907002201c41c0e40d030700c0d040001e66110342001441c00100e040050500d10708023940100102c84004120b10420a081203003d0415801106035002d80360161980302c0d030044100c44100040070b80110032941480f0204c0d004082240003001010008041882d034001d1090011042e42a241036201c02800700700c4801054409040c103a00207a80305035100b00104118085100516031944000c02c0806400d02c10308041c05448010024140106400d0701c0440c0b03007220380d07251005c01080e0424428104404034507060101d0517502446404004018000c0119041 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 465668732 1250 465667482 465667507
    0x20409030903020613090e19030f1e0306060305181207020d1b050a0f0e01030f11130c0e09040f0f1a0a0207020414040c090221090d02190512091203 65
    0x10717540300341d01d407507820807419190003000418074840c17070003041234148650407a603030701070300c40c00702c480344c0982002079462409a2a00001000d01540c5003280c03800501c1d0703401c0010044c10742d4801000b01d0005a180c08042003840c3c0001a1901d440003144869615064644005180c2070f0032090040d001051044502c40c0c403804140d02d00089a000b110f107110784a075200070012907200c1c0c510403003061400007801003001c1100c103500e0066080c4a003600c40e001450500001e40403a011000100c80140d54145800c44550070100442500030b00710b0700d41d0070a180c5503035030010300001e5042c000c142d04030100452080101300540b0000b022020b0400c090706103026854540207410412050b881035042480d440045a203044030030b401385802c82c1c0504403a50400185070040e5100c03270014690b524244a032007000c6504004440d01a0300a400586440810907800924040340103905280ca0080481e107038001410018286401c071892a101c1c0f619a428030300064940230280c11105614040050301007141d41 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 465669982 1250 465668732 465668767
    0xb0604031b060801140d0311150103030e040612110307050907020d02060f2505211e0c0d0c0201090807030c06050c0405100309020a0b070506090705030a030c0204090309030206 77
    0x81d1880c6200405659400c1258062000e105c2c0d0b203000c06500703800300c0700b5080c6192104c60213800313410800141181d03151340919080007000c4007a00040d00704018420551703c407000c02d8078118100c40034401c0a05080d11003000500c4c1c403200401882c030a002d42603080d101408082c005090003803858907640b80480c000b030740341c4241c6000f210040c0a6900000c8a01110039003590144851301c1c0f0742c0c110703041a002c0c003400004148041ea000d01c40140003402501c0d62590000100d16180c1205aaa50801810042c041e00c28920720700340312101e003070400c02061400c406580800d60540c00200b0315664210f01030f801420388003400b03803403001c2c0064100281508107484051451080b03100304003603600c0344511061405140030301d070f0340b00881c4110b00d145a071080d08a000441d000500090300b0903510050b5220030742c402207040b01c1c0d075040f0908001401c0401d200880c028030301600a08801d103060741c1d00400652001d54002d1089a40e240180c05061280001c1e030044c650207050250b440344000501e68084 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 465671232 1250 465669982 465670013
    0x4030c0e09010c1e020109080414030f0a021c0602131202190302010e060f0408060403200109020603180a050d050c191a070c1505041109061011010b060403 68
    0x1503030800400c500315014414001031030b0345507850892105030080700310000b07400300401c1800c42d0349030384014000c03030700c01002071005020498002c1902c54003d0140b6080990191000c003103900020400c1c405030704c9040318222100007064131114840d480b494880001d0040c03684401c516420f102010807480052604c0c401000d001303c400300031041d031300c802d041c0800019000090028420701001000d500308503010f8607a80b0f128403809820241c481c0b02d801e1800300c08546c16800650020900032852409080c0070781070a151000038082070b00c441d004154640b0000e4070442c0c009008800154001d8001d0216842341640070f002d4a44100814000400c69004951603540394009c0842402c100000c0700039200800d40d100090301c680c0031148941c031291000c0240361006010310354036090000ba20401c0440a0344508403400101030515007003900781c9007030206c1854003400441c41403107683d659500c010a80603c0314031301841d402c100c07507408502508000d0300460304a5404180482003000a02a1200741d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 465672482 1250 465671232 465671249
    0x501030312090201020c01050a050d051003060e12091302040b0a170112020306040b060d0503160605010b07080d09290117060c04031b180e06150109050f0a0b04030c 72
    0x140103062144400c842c141400240540c1c494004034000c2e50041000d001c1c1c01105041c22030400481001140c240c0304216442c07090103244032010704c1003004a1103212044030b1454000d0200c134842500800041c81959105845408000360030f00c4c031030513141c0403500903008442c5042c0d10381000381006411551003801040314841d64500100e20510703c404829099074000303000b4645910303503071620403041101070003080d00171050691180100e0400c0004000ca0003164029004901071824000d08540c01070300911565001000004081021041500c1d41c000e0004000501100240f41909030409141500a07030300701c4601c1d00f900c408001c0040c4034122001d4a80034440c10040c4501c8903141c03031003166990300b000c0c024030040c004504075180849050344030b0300019800544520040365002c216a00d03000100b92141403205c0015028022190008020031000440310305c1600041d040e036442d8007800b03004400d1282030042d40e9031604d1541005181c18074086585079124144001e00c00228000d0080 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 465673732 1250 465672482 465672497
    0x501060611030f1e0301062001060b090907030b0301110d1103070504150e0402030f01080c030c03030406031503060e01051b03010302030d0c02040e1b0f01090e0a2d05010303 76
    0x440a02518441e181907490700c002d1440c00030a508004a15048407000b031039521408400b010000300d0600c01107003c0c054039150a01014a90600348030012240c125030800c50341410010400150014140c07100701108031002a91681d03807003412802050040c0791240d0560a140b80c10700c03104100c100400586034050420700060b10f0f941e04a5600d4802540e03c0000984100004c0000c81c0c1520301201c00f80c00c1d00d240c84c514a031560380005069070015507560012481c3c000c01001081820042c0040d00707041074000d0140c01c0300303131b40000e51640118404d04c030905803500301d40314000c1d8414017804065540484c04212910152840c540204411543c0035407981d814071185510340b0b8408143d0b4126075005000f01034242203da01111101240142240c0040d15215140d40e80070081c0580c00e00c01c01149518490800d0700c0040068913200a91954103011000070103201c2c81d034a015280358005800b51021a9080c4410381042e10b02501c20014001c50a80c1141c04500e490389400841c1200d0003541c4441c0d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 465674982 1250 465673732 465673739
    0xc011a01180e06010e0310050a1d012307020114100f06110c040f0609020c0a020a050d0b01050409050f06040302060709060f0f0f090f080102071a0417030c0f0d09050106 74
    0x10030425990040c01c00c00d15102c0c001620030761088010004084c006025148070140d802d411101340c4400b80c036461405a1503941c40f4175103942201001e950202d0190003132001d810004441e044441c80605225120b095000000305068002d40100d50b040c111004c548440385802d40e50b81c12140d00d0360082100d00ca580c601c001400c11b01c24a01c225007200e80001400356003012408200c014517040c2040c0d40340d191504c1e800150703602c4510207807070150700410190040b24a544104600340e030181d004144203455030b030180320102d00500c0c0840d055075800d450004807003030750381440c901d400000c0380c0340d09232031060030f041108165012a6090041c1d0107601c031080c4581d104e11007a00e8821401104900140c0d05440d100c21049c8145035003400d09825061006085840310070380104440903401108980c1e400040000800101e00388050724000b0411140c04507081559031483c1c0ca4a0b40091104500e0010010034441c4410008550b60b1090500701c45a9135030820307040c031005d8040007009451a519202000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 465676232 1250 465674982 465675017
    0x6060102010b09160e0a030302100b06130306050c0903031611060306130b0f030102041706060f091b0d09060905061e06190308040e040c1208030a0902060c011a01 71
    0x110040c80d0052807010f06903201c454503001e020410010340c08020f810702c5000d42e46d44034411404042c6009501901801d541c155858041d100000a601e000b0a401c1001e100c02d000c00c1150318095907030001c000700702070710759050303c0460b80260360303c45525000004440304e641d00c80340c2c42d00c0c101c00c2c4105180d038034040d2118100500750200b00c40640e0006985041e2030040d999980c0f12042c0508010127180f100768034440460700f20780182d0400d510001c9410f000f42c0b5141c40c2009515800785007243e050010725400004170b0740c1c81c03201401c03280f000c407070b50803442442c144030000b41c0d00054005801000814030030700302803001d404103550030b0704c1e98068000400d4502e10a902c001c1210481c0418110854a032030050112100c1035050182c20100211000701c00907490f0b0000308010035100c4814020f50401741458240d881096001410a060201100740001d03841c4054a42c4103000c103e00003145c452600220380e240c41544a600599464440c82c80c00158218941180566081e40e5503003048800580300d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 465677482 1250 465676232 465676241
    0x26060c030108151e070302030108120c070611070308130501110a050a110307050423061f050f0702030f010c030b180402090402040e030f090f01080f1f080a03050c0606010201 76
    0xc2c40e440340c000c0021201100303500031941d0b400c0f104400100d005104d1020000b8441901034a000c0006a0000010040e94004000901d520000c4001452078004140a030799510f045030306c5420203004002d0010440d5200a004071070003075820000c001c0d42d50060307412058035050103000d410301144140c069649000c0c00003030a558102d03030150082079840b42c40e8030344400d5134100e201420381c1880740d44c00125058845025040c06142c003141d17403014070900045500c40280b0b004180340d010381c600c40502e02e1801c01e540010842d10106040c8980e40318245840130a1038415410065054410175990b11901401503000d00001e86565804211b1444684104856682c8488004484001e03120100e00586850341040c0d402ca44010000226034079903010060a40d046401801d001090202d00c2b980c0c1030900850150342c501003480c210708a440e1a001c0054a204003811a00d5440110460381d16a036072085641d101510f140e8049410f41542460000c040b80e00c000380c560198000c4402150855005004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 465678732 1250 465677482 465677489
    0x7060e0d141023070c060e0f0a060516050903070b16020604080a020a1a0706050c1204031808060c190e03030c0a110a0b04051c0c060905010f0906200726060c0301 71
    0x11400c5658200d86c0b0350038040c041852640a0600413400c8402d000d410800601e024144a5540442c40f072030005e456108840d055a004c005020741080440c48591300418420203403600400d40a45601680d0300460140c031250000a42002000074049400100003480900716403080710010490390f01d40c001c42c0d00c035003544559400800014021031001030800d030403907980b162510100d18100f8202064a1744203810580b4241c01203443d0f50070110810032949842400b5050380c100500c000d040c101d4248803a8400c90001e00350b03400064030310b9131240e44518540b00a008004045030345881c1a54566034035050403a0003204e00c000000400038036070912503014401c441400728241d0910b46020f061016002041d4a9807901c03803032681c80340d000034000505020281c01140d6588c2000c1c2e00349000500051015003800003401a14801004029840002d003002c410212a20500e4684425095840c20714113402c0175400700424600c1400c0015803404002405144400301c13501a02d804941507c148003e00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 465679982 1250 465678732 465678737
    0x20109150b03010902061303031101150909030c0507090605030c040b03030d0207150c030603060e0c0a050f060f1605011112040b04020d0f05060f060307060e0d14102307 74
    0x100a00c415422640c00352450510103070000c1440c04455000880540c4518511000501a0721090060582c0b0031100c10000c414000200440c0440e141c44118401e074034862400c9485e1a03c0d024800c00d84119110a40c0580c00011681c032907464040940103820280030b0140070744030300d80032001e1a01d400d004002e0707008006009145003001524611000e5403002100703172484000200701010080385486420302c40b601640d00041c000e815441c240c410368035500d80203145548100d5a1100550b86c05442d0012920102c85814900b030349000070030090b0003080403183c072a00010803500d29152100c40341c03508140c401e074000c005130b00c0c40c2401143c0034041d005030703089203088010004002074811200c19400c07034001803074031260702e00d1039442d40582d004d9603030200c51a80043c1c0a2181105e220020b441c0c005170224050041c2504102c0002d00c21240003040c58451140405443c00740b203003640d0f0034480001088190b80c50501c8108078800076104540f00030b810480d0016608100b01d40c5032002e280900c0d0700b81d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 465681232 1250 465679982 465680003
    0x50105030613240612050c011205010e15040b04150314030c030a0c0503090d0305090414011d04062307090b160201050c0f03031806011a1c110703120c020109 69
    0x80c0d00c0504003d14000358005520f40e60200801c8005204400e240806c0c4240000c0088418200006013034208a43e4030304c8186040c00014000300d0001e03c0c00135800f4018121615482d0141d42c009400703400118011504545465043c002d40c0449040300400e690003014410621000001419500d1050540a56058005008035643c0d41c1c4581d0410292600400450342040c0c9000d000408403480d20300101d0101d400040c000c00f43d800c0600490b00d400c0c0d03c01d1141402503152030042491040f40c416404803800c60400000c04011711a070054042540e4002440780d5140c101c012245d41802c180c038204049002c81c1c400003101d510700e130300319060600000707081c417128101c9900550342c0d42c1000301d02207480c1c01070395458143e00000f08087c510400c65040d04c041000007404039107042c5041a040500c42e04103258408020340c6030142100c9024a50702c122010042c40c40003102c0060100651140180d94002029404e240d480b400c51046031800322010054908140410390032100c0c07204006065942c103 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 465682482 1250 465681232 465681263
    0x20117060612042f13140714130b1c0c09030b09031e0d06120506040206030c04210309080c0904080c070f0b041a030c0f03040218040501050105030613 66
    0x390b031145400c98031814090980d40d04140d03551581c80c001040a0300f030350b01c03441418211031405124844411040034001c021502c0c10b5034080a0600d40107100c1014480342c1c10907003850b40b01131011100c4c0801e80544880c1c200380c40b1104402d417603006400001c8804444118031000c01c0c2c2503c11a40c04018588500403190700e55544e20882c85130003804611507000605c807148140310400e11a9801407a003482c000e5071410810500c4003261100d0308260302140802d0055000510002000c0342c10580440c2c0041e00c1c0e43d0b545d482080303584503c0d000303081d03410700010742c2c000340350b101c645254030781c130b20039107170030341e10a4031072451130303038601051039400c2c1e10841010206020846400003401c5144a0b0800e44150303646446a0300007001140e03001c881a4440010100942100d010008400d0485089164914240b001d230250042c0110900c4500401001010a003196582c00c80c0c4070300c071000148100c00c24a441e0610364024402446140d00074012203002906061440c214620404c0c2d2090300c22041c8400d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 465683732 1250 465682482 465682507
    0x9070303140c0a060504030206010f03110d06150603020d060902190f050c0d120c0302030c1b0a0204050f151512150a080d030b0609010905041e180201170606 69
    0x8107030030080000c08022514016609110326030006020300004107150506250007407801c0d05c1640942c0e040380101c0414400941c0510748102141e10803100d600301d8040324100040108910f21003149040310700c1c0700000d606901500030f80284d00c0301003420806103950b1220001a4481c80d036030692f41c5a103005903007001c24001c65880d01940d0340e525140d4140045800e134903250407440c10201c40450b519500d0f82482e0241d41c060404203420324a42907007181803000f5441901d0003807008880540410100c040040c410820005d420541c00410501031410010046a405003040d03d2100c800450ba64900d4400d0821008284c00301c000c81500a10b48141805192001607010b00807201c110f25001c1c11100359079915010201400c040740c0074040d40358144d90041d00b100c111000c100c0c0210414484035840d41c4e0016260011070b5810740300820340080c0750b401c880c0400e1417101c90002c01c0b45405540005209180400ba00d824401c0c3c81e100180f016005030644050f4086695941c402000c211100d1801e5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 465684982 1250 465683732 465683747
    0x6060801090911030d020106090e0a030905060d23190b03030412020409060e0105072c09070513060203040503010b09010e0c070807080d050703180210050901180b18060309070303 78
    0x240640043c2c01d034040c0034400241810117030318620340142c1d1501c1c0c09015182052082101e030707240142c01440800c046940151018030980f14645c425000401e00c0da0b00340b07400c1d40200b0740c4c2c0d043e0b5042811030380c000300000700c41301082650700403081c200c504081c8403d80c00c10700c00c11000800050055041618090400b60140011b00f0701700e800540307804500002076040d02504610a00300e400100e0b40d449c280710018581c01e0b10c0700401c0400701030740345006074803d203507000100000c000307488460b52507403040d44c295403602c09c180c0804071401501400042c0d4513400310180059a00c210003c6c01401004c80030010b029400b03004001c04e001c10000461032401480c401011400d200f104540e06003030780ca032201881500022100c2c0c540c1501e5900300242d15a051082c55030051458420207038050390340c0c001c90707503104501c2c0d0b0000c2445800103110485a0040c599241c1c1000450150000f42e512400030000c0380d0000d04000d482619000c940381050300c2d00d4804e580c03082c17808030010200740303246403030496151 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 465686232 1250 465684982 465685001
    0x6080f0f0c070611121012060c111603020a0902040803030a0209010c050d05180d11040e1603030c060501080a0f030503130f050609100b0d140c03010c080f07030606080109 75
    0x1c008004800c006006800707481101d11441203940c0c4c56051940c540c102d0703648000d000c24280e80001009220003c2003640c08061140c21010002c1c124a14101c145c0d6248001602c028541c0b01d8078120648000704084030070140d07842a918980410741c1c3d4001b4205034012400f80004541040c00010000c01c00755016001107481490440709020b91900e4050801002c0341c441d1000070000580e0300103a20f402c2d6550040940c02f580d0151840c4481d80b40c40711898201c42215200329125410460010030400110a031131881105c1c4000d081d90741c0c54094040024004100d034000c1c2460300020f208800401e9802d15142c0200b0100743c5804540c1d000c5503a503200504641c5c2100b9650400e0010a8024080203031142c80fa070024262802c0c4400e6151519200040010185060a41002541c2c0740c0700c2800311a02c0d03100c5254150070707145460490410500c41c981c44d070150302e484562007620342c2c840941390040d000300c40c100707030191121501102074922501503403000c10210701c01040201c00c5030780501e010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 465687482 1250 465686232 465686251
    0x40501060e0609041104152307030c060608030315011101110a21020304060209030115261905010c080106080601050a05180a0603051f050319050f0105010f0e0106080f0f 74
    0x400c20348141c9401140c02a1f081544000701c80e030006030401d80c11031040314071304441d10802c1c50000c41350811040300303108410005040040c8003a1500030484e503034002102401090042e02d85a1900140f0401d2070885100071a00044629016400e100c0041c03265400360207000d58018507004603050213489854960031000c0240c003c00e03008465a807000c0c4091070003180720714809681e521101d4105401e40d170365420721116000503440204050704c1848404408044140001d180d905e00390410030341054860102c0041c182c4580c00381c402007240c19445040c0003c119200c442d80c81c4d03224001110010720403a9118080b44042181c00d0025000c1c0b4050411031565860303000000920402003840030660741d200401082e180e009014618002c0e84103019a40c203018400c191003468400002d680f00b00021202c044e0b1440303001c2c0340081c400180706001d00e06182c0f200a0110b5603680c01410b4003852244a0407020504480002c00e0083c0314030300850141c80102c030104d203d6128594038003882c2c4030142c8400d40b03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 465688732 1250 465687482 465687491
    0x60c0714010603051606080f01150905090f090d08040816020d050a0302100f091e020a0b0f040501020c09070e04410c040302060d0c0e04140411040501060e060904 71
    0x103600400d00400d0051440b034005044a4a020700d80e40070b00314440d80154041c822100f040103603031040e5002090446907520f0500d081000da2900942c0c120000b40c000507000a0f5182c100140d00c403036030fa2401d000314410350440350300700c2054104035440c2d1003d45000b0324068040016140b0a00c0300c1d024090018001444074030724200d02e91750343e89400c0980c1e200707c015800c07005010030194043d04c190001d1940c0d070380c0284802001c07603450f90389081c41c1c02e401804803007548200078203545405a12002510303061843d0b0b5aa0321240c0148100341d0454403030300d8018810103000d0019410450301d801d0140e03c058440030450304c1032300c1c20800501a802c0c03400c03801480c0405140c8040c0f0303001c06000801240c00c13140700550b9605082c4071404140042c079440c0070300001c000400040e12050116240248102000102d43c05d800c070040350040100c4403460340c00760038010050802c8a075070b0a0140118030807200b0140a1410b0000d000c02e443c02441a0b60109154400310320b580d0a01000134a14085c00400024 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 465689982 1250 465688732 465688763
    0x507080f03040506040318051305040812010b0705060901090f39050f030706080f09030d150503011802130f090f11130915020d02071202030a0917060c07 67
    0xc9150002c507015111540040284024140c2100d0307091095210f21081b00461307420100840c440c1110034141222403a81c40d0b00013030030f10903000700741c3d4580c0700e80b05604076855a540c002040c458002410943e054082c05020500c400303814170650fa031036a40528001150050350f1503a0080080e101c800e078422409031030002450040743c4005000c4401d410200490b014103000a005848264200c0a8007a5014031010f100c4690010030350f9a005403280800c10213a40c80f402954198043c81c81940d001c6402c1000040c2d080709040c030160306886003a0000c000c4807059442d031240c4800c2c80c03d8082d401c0714a003212180c4030704030741d0890102ca00000401045401c5191f40e07961408501d4001540c0340c1e51024080c01c4145000008a164448074441c144138890050300c54622007210010094010396002541c011320002d940c054984443c0c0009891100340115032006e520303a80600303200000111100c5010038400030b400a030307031075032600000200240e13901c000340a490340c0e04caa0005d5030240030740032030302c0b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 465691232 1250 465689982 465690007
    0x10819060209040b0d06060f06030908030a1d030d0f0c031b141b0f071a03160c08030a0c080a150e0a060803040602010c0e040e0d0e04020c070605071101140406050708 73
    0x45c50b0780c442d120010f40c613450840701403448040c0307030040c3c401c06084c00901004143c0c41d1003640e412040f0448001820042c034001101c6000c920400c4a00c0703408003007070031b0751200c8040d84400c13480c1515482c1840440007004044040300c840d010260740c00c9141001c4685064861a00305105502420075285000240420303021000e10840001c0b00c03a07400700e446030400c00000c0c001c0c8402001c0c1014002e1082d0035180c6000d00500000f42542c2e0100a211040680d291003400d0f0090500d801c1314200c0d40d68100001150040c282641240700030400d0600801c0b9244254824041e02211441c0104009400c2417265801401c010b00100e440c517450301c80c003080111050000f40020320041d000096580070160016040e19030702034025100350314010000200750400b19040ca0805818908144400708950010b0000e0280d022041301901c1601d001007041d541010041c020710780108142102da080c5c3c4d100448400c0050319450780c10800c01d000c1042014011800340121503c00c9040504042205001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 465692482 1250 465691232 465691249
    0x110a0308191805070509040b15010302070f0302030706060e07090e060a0305030a110d030605100c02031507030e120a02120f04080d0309141204050d0c0f0303090608010819060209040b 80
    0xd0012215082c8030101080f00402c14074005180030348001c00c05241c81d465a56101d80d0080c00341e02c9400700ba051a940c541c0c030950485041d581c0c40103844812009505000b941e82e080094100c3d2441d14004001c40e0342810000c116202e00d241c0c1c1c1d12001c801c5e051004020310201d0140610741c100014901c08000150240050a8103440541e91a9950f03100c0414451a02d00310301500414545001014070458a8100012a56803440c2c2406600c480707041c80860300e06022000681b145610b0442800b1016a1540110765213081750000c451450380d60510a02d11840b81c1541540540d01103090140007902d000c0141140d510031400c100d060079503e00005003054140840440000d82e103801007401c1208104444414170190b03002400c2028001c2c901c52028410f0307000305d41c400ca805800311410003035400c3d002c1d8040c0018120300d800300c2d50b50345000b5000f0281c81c0140400b046140001043da1440041e0f13030040720441c1403403040780e03031142c0c4c658074025400b502c1c5060b00261224440d98003074846018 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 465693732 1250 465692482 465692501
    0xe0a0809120c10171005010203070b06031504050102181905010c2a0f1e0302090c0f1201080f0609070b07031707020f012d05090115080105060301060501110a030819 72
    0x503440300100e240080ba0102403002441c41d40c0c4645d03458428445645e0000640d4241640104019100d45404000074a0105c0c8800080703036001a00303041004208041d00600700b011001343c0f01d400c8000b201ca0410000001c42e40c140c103091810345000b0841c0e90712a2150720b90560107440d03595000c246007016070001d034a1008001d240b40d528808208024050000100700800030710306122605110102071040c0500380c0d110107845014000c0c04281c5411032941101c900c034500d4544141c0d500c000100c0203402400921900240e40038518542a1340100032541a00c2540c881c0054118a0708140480318940c10808041d0100405060101c82c400c040c00c516500a01e031a400521070240c4580d0003030300759407a18074000500000d00d140c507843c0e2807102c250304410304811000862a650b031010701500510045483c0221b0716109035002904007010f40c000c0d40180420380007840041d4403040103440c6615980050300550340f02c04118800b003403141c1e070115000103100d408041449500400001941d2a000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 465694982 1250 465693732 465693737
    0x309050603091b0a051809010b0409050a0215070209130303140708100504020c0309011b0203010219030608061306090201020a0c0605120f011203051803031303060e0a0809120c10 78
    0x401d007a01c01c0c0043c2d04031460100c0842e0303c0c0000300c0c14840410281682d09004440725a02200402c2c11800c0070f40100000001c0508100082106420460fa40c2c101000303042c4e0180c10450181400c05c0107810071a030002d40c015086184940301e084801d01440c0445400350b041603a2251800400d1040303032803503402141d0b581e840c1d010509000da16a800f0f4585035001c0c034469481007043d04e10309000401914109602400d250100b0710001088071030000704031000a42c15440041c1001300c040390321104c0c000201d41c03a03504100b03258035a21380540e5040103403644240340400b042d50340005841504040401403062058610001599131602075140036604140041403003ca80b0490f03089103040c0b540d500c15110b103200e0380780f54542615505038175040035002c0c0800800080740f10030a5081c10074041d4640c00601200e81d43c0601044040a042302800101d50481c14038000d030180a200040100c040346d00a1100e503c4c0907101410805801881444481c0601480d80320b4844c07940c42c081120b0b8001303140d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 465696232 1250 465694982 465694993
    0x140c120d0f021c0b011d12070906240c031218020a0605030628030b070512010b0a170601080117070f120201080f07020709050c0d0207030c1203140f04030905060309 72
    0x40d00200740d6000c006654100318540114001d0007014030044441813005840e0308000da400e0640031f60500f15681c0224200c44d040043c0080c1e15020712440080d0800d03032000505003828101001c55600031003036005800640c244641079041e00d81c40e8094258010b01104024816074641d0119081418607404800415008020441e140c204500016034415490300860703441c0d0810b07803100c11444401c2c04003070126590240040d0915008600302c400311034145042610750360707440c10740305501e81c08221240001040c0f80e0a0100e0a80d852810314003501c0141c4809103168203184244031080503a502c0300b051840380901c00038000c42e045c841075000d440d1600303510448005078000589035240262841c0c4030380145800300580d0030790100c0c3c100c5c00c0e9a543c2401103819101e1500514090242803148003980307100040d04400c064010000d0600e0740d125085000105c614210700360125a0324202d088451070385140001d0302500040c0342641d0151003420448a415103c4004c55070507002205c420906a106 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 465697482 1250 465696232 465696277
    0x120804030221121b030a060f060804120807031e06170d091520060a14100b0d061a0304050c061c180b0903040303140c120d0f02 56
    0x103200b14029088080d01c070700d0b03050054041802c0c840c45891420118007064902240350302c01c018045215440034040c131683c0302e0070700d4000c91000300b03018451041142c0500100062050060b81e010340715580080c1e99101050ba00345003075400d0a8010b00480030035075036410170046080c68034101e4400070320142c800100c450424030140a102820807038000340d5404100c0e40d004041d0301003284410f407800c050507070440c811500420b846518150f651000c4108031110352840a64001507510701c81c8644180a20003042084908010b9010550382031010700e0402a052000b0f5001c48001c2280b50356044001074104e995060042c0d0300c00340c0515000313100d0301c008184400d02c507003003100e02842501160740c0c3d40703040d1040b11111090684a0b0581b1120794039a210b01561000500d0242540381e0441c4190301c03035203071444a0030340765807090200b01c020480c417040e0002210044e60036980070113141401072640e41e441c00c110b1621900030044e82d030b400986642c1118030ba078019001411190300c1e05090300010488 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 465698732 1250 465697482 465697487
    0x40c02030c160f05010f031107140d08011511100609230906180102090907030c09060207031e080f0c030712030212060603070309050f0705031608030d020d0912080403 73
    0x151420000c0080c040b11040c001200c01025a03021150242000d41c142c0d09000310a40241080b2a900e403480302c404a5640280507910340d000c940580c010303080d0740702c00b603055805031b40d000c4088c06040700c6c01e6030002c1c024803090b004195040c029030580c42103c01a0320407a2030344080c1d0707140750802c1364219112030607010243da180101e1a10020003a050300ca151074010b1040d46d94480c0207103440304c00f900324151005071100a41c1141c05841024248550901e040000600070342402c05007070b000110f402d9800140c041c4042444001ea82c1c2c8100c042c00b0515000f241d00880900008040d10140802c200350310350300000c1c50041c4418200403010b140c5800003400c0942d2040c003900604800c0c580100002c10382d044c01c0030100d6502030b00c00c0301d0b000d480f51030780d000c100e00401d2003100050030752007000146200036000003251411104200d0454849410701d0502c2d8182c8000e900c5022040d41c81801904900b030100d03000b4050340709001400141515294030703101c156031208200440803c1100042c13009266 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 465699982 1250 465698732 465698743
    0x6020f0d0e0f0f0307050d0e040f050a05010f12030215090f0d09030507090606050313140106060c11010f08040f02010e060d020a03112106041104030b090c03010c0815010c02040c02030c 81
    0x94049011310300b0304240351285510342d15480c07c4a010401c0c0d00d0b21120099441e5404003c0000111804000c0741c9010440007000304000c0c00b0741c03401c10700040400a400c0445000c0010110340c0755001e45403283c01ea0b120390805200c0900240c06034040c80c0e65800c0021400c000040c515509581c50284091560a025080010700d03008031b140c082c10400d050102641010443c0c0e0030007141c00004030050700d6801d00c03411403140300085505550070300c50001240d039408101e03058118010100b100f13101c0c52130350054842c109490b911501180c0c080b000600401c01ca8121240070071b0041c101001d16000200004042d03030300c89001780c80c2c9a9808125025429410304c2a414002e400c0d444003481c04e81c07012000401c40c0813554900a04104000000e00c41d91540d4001c61519406108520303100c40c0c6a103031650b0202c03c12101080b003072041080002c22803a050181c0ea107142090345a4008070740f1650180e4041c100356041180c148610806c031040103032114810000600204c5d8065626081c0103d0598100b4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 465701232 1250 465699982 465700003
    0x30810171e0606010c0b0601021204090b010e090907030201080a02090a030b150f01120c030209040203071e0f08131a100807050604030b01090c020a08070308040c050d0c0306020f0d0e0f 81
    0x381d1020080001c0fa03600000641e107040d4000d141c41c0344a507943c00040b4580030f84444c1409480002050014000450741c0107002444800d0300c45020300d130713100b106200156400300c9149490b80c0c04024104050b500801d0f0360bd1308500002d001503d0040071078049100200c051b40112020388900040201c000d8080f111038040701012504407600b401d1070b50000309508020400c0040083da201e42203c405406070381100e03441640580190b4481c0381901300600345c05100e0b0340c400c0401c03140084250109200f0030255010401c2c903150046039456902e503186011080003003c071070310b4030381c484849803444201128a00c200c040340f01e2580c03098184480e403800c01085900c50f90081009000900020b88080f0360207040d601421000a031140d040c0401701e01d080034030341c00504034990020b080c0c1c1c24541e0103580c05100700e00400e04030b201107641c0c80c10320061602584010701075100c207803014000640250001c02002c261780c1110350905801d200150200d6500750501d4080d6407207403140299600702803048580c407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 465702482 1250 465701232 465701293
    0x110a2102041e12050c0f040905070810061d0a0c0311031906050414061c0b19050c04051c05031b0303010305061608181e0d03150f0303081017 62
    0x140f020710b607078440d543c1303402d821142e210300b050485c8600d03181c40f945e009506a5030031504465440d40ea42010544504917000c05281c0141004408a03901c640c0b550511343c2c40301040c0241c12156a59140403009280351003610080540351030605282020100c080c40c0540138140c403a044a1072141000c00840c1d07182d9101c18025403e1811038005841d02e1220780d944600c05854071840e85200301c03c144218003054000a11071a0044180540040640c240300c40452440e1020015a00d40b085120141c1c0624415035501801074841c040141c1e48103030703a4842c0544510101c1c1c0c03e04855600d4245042c1140390a03c4417a4808030040044c01401c20810746c0050720400440410702c50720100038150070b00181440b0001d140312174403c003030981c2000348102e940f0b400c0c1d18041260031410040e82c1c0300c1c8084012200001c0c00e041610010340c0d48461004202e90b02003182c5820b05207503030340690b1206d00040c41950242d440e1280001d82800403610014081c1c000405031400b0301c01d590340e030b020141d111441ea46c1c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 465703732 1250 465702482 465702509
    0x2030715032a0c060207110a03080307170c07080c120309030a140702181b070f02031b031b010207030f05011509090203070b070501021b061603110a2102041e 69
    0x40240c001e00c3c0340c0880c6800080c050398078159420134003200701242e507045400403004040003051044180145029002617074903500c295840c0e48600f0050b801c169182494410308011150004620100602c1042c0d01e01050756035650702c2e410020000d0f002103c0c6c0030300c1600001404040254030016121180000410450170030406402055150441a45980c0d01c14040d0000c42c0030107000d03c3c0340b2000368445000007644c6550300c2c6002e4814400a100880c085d104030100f444508100401c900c0b212800580103020703202c403042819580b05074410416040d03001d52403000c00401c4d8002040045a4019170001c100f00300031600558003444654000c0d2841c0703103000c9110300142c0e80451030300120f80e0dd11041c0c58880d40d00f4100540203101d100312a00388a20182e002c07894551020400c1807188980d16000b03204001040b2054054981030482200d80034003c020040d852401600d110504044480b5244100c140c001054012a0300076080728440341a038a030900e40e40d4103148808000762036811300720f00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 465704982 1250 465703732 465703811
    0x60915090d210c1206060203030f0705130e090703211205100b070c05040c1d10020708060f160e180c16060209030c0a0509130203071503 60
    0x6885800c0c000c0a4020006001c00401c146000d81048840300c610b1070404110003851104082c21007034080c1c4202c0405030410400045c0a4004020b8911403d40207078140015901e004084485070b2181601764030002c40c80e14003083c10010540e026112b012544010a18242542415101d4460f5408040c0c85c281a010150a1459011401090900e0000d0001c80c003610790700c1c9068111790190304030421014020035610103000841c3c01c1401214000e45081060340d19002c401c840307070140c00711a040c201c2104e480c0d0b034000d410320b070390000d241c1042d62040d14002a02c400185007450700035101c03c0c10384c0e84140f040c40540d6000c401000b01007500e0303080c42d000c2e10142a010800190301214085607a128060005001e601640d04840c01c101e44a5500030810030b40e8a0500000c2d04504c2c6108e01034440c1d100d4066060400818441c1602c200030300310a8507540351002c00b4046220964202d030140500c840019401c40c801140200343c0066460200320300c00003c50080890b1041c03400ca070044c10180040740d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 465706232 1250 465704982 465705001
    0x2a180f080703032604050109060c020115051302040b0325020c1f11160305011514100309060204030606290307051806160b10060f030b0111060702060915 67
    0x5100b00c07585810f2811a00d400108a0804a41100865401c1808841c2004100281940554001c1e4801d1030704008204514408078221200203061045880ea01c0c40280400c0c90f21f1412950018050306000d4a4640c443c6881e041d0b5400607500700c1c6140c602580207050140707401d1483c2100c41824802000c3c5450060005039034484140e2541c050b40307541009205c280e51141561041800c01c2200b25804840601080350765401d11380310554480d441c086001d2020703110000171004484440740000c020400c04400c01490700b81c80803000d0180742d0365054035800166980081c0c40198020a400580c592610100b40301102814010500d94050090000300d00030340d003c280c0c0d400c501507151840e121041100e101d1140007400c00102ea0049000ca2040c0609224070b5407a28135600c11140c82e11140c8072391018039010f0255015070300101d040842d400400a200707500103029540d0514041000c2461051424245503041c1c0310500160041e00401440759420000e900c140b0a0f154a61001440c008414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 465707482 1250 465706232 465706243
    0x80105150a05070303020a2006090f060903092b0c0302130504051e0a0c0b0301140303120606090d20030c0d03091203140a03091101050c0a03032a180f08 67
    0x1014158080b030110031f001c1c0701c1c84024000c0200041c00e00d40321609502c0d0944d541800b103680c401203100e03520b02d01b98101c1e0042801070065050300002c600301801601000680b809459401c4000c103000e2032aa07089103a10750780c03400202c0c090b244821600e41140103100c40400d000c4c501c04012820402884001400010105449820000000844840a04000d080610740a80640303076003101c06002c290780c1403e500960480d11103400702d0318241c0c0c042007490307103d008290041c0d00d1a11035a00064260030403400074005040e00404a500c224881e9895070044003441c418005c00e030f5034031714020210703041c01c000c2c3c240040b108480410b41c2e0b00107564010040401070142d0303048502042300303000401d030165184d000780a48a180a503221040c0c200f00078010b222042c804c3d203840003200a41c0e680c1f540600304403820807051030f01800c042c03402501d05502408040e17030b80310030362055180d1001c4000b01c0f0061041c030740000765a4240340384440341c500d21640e06d60764200b50175240b01306400304043c0a00150 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 465708732 1250 465707482 465707497
    0x3060819022101020c0d120e0c030304060f0c06110706060614040303123e0a09050603060f040614041a010e090a200702011106010602101109040c080105150a05 70
    0x2020281c03500800c014003900800d4a05011072060300c40707284a45801c49a80d8410801f807071010411004c0860003195a410138030705140d010380003003005012940c0315164021482056041c4091070084941d0f403c4202c450f00742d1500c0800d0000304481d0100013080c0100e10091546107001d00b000c83d0b40e204502004d11640c0320040521105049080c0603040c581c015612104c42500c00e0b0500819070311540000c54030003000d00b2041022540b00b040d0380101002541c2e0825210b50302c2d810017a0404081c0b11096001a108070741c8860045609101079980740142c8000c2d1201c2c10350308100b0f5080c24140310a6070300045900c07ca40c101e1894000c1c160768064030503541040100e414160684400085e03100414102c100401074600c0030801900a4070584c0050401a10030b0380c5c2d075211017020001851700c8000a004200040c0c10041d031034071034108281c12a122005c0c4003140c0d03919159440000404850000d0a60400708a089004205a2602c6900074101d102d030405040d1810465800c014080c2c400c024 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 465709982 1250 465708732 465708769
    0x1c020a121b050303161e08030712020c06150d060501090b0a120b0c0a14070602040501110607230d051017030c030706021608071a06031501050d061b0306081902 70
    0x341d90105011400048890808002400002c81b0800e82440e00c03071075200310340300c0c00403414002d2010b41e800d040e032007183d083c4007426003c4d106640315903c098000306c0c041d4034100d9010280148140c00309000e44201c43c001c003844040007510407609824840c0c04d0030254040ca910350f583d1010b51011a2075000350030307817210240c01e40030780d6600051020740d91200c1903069250709903804150340c02007181c6030b40103100760381003600e0b9607049208005c4520f40d50107080f10008002000c4400d0728041d18001009030715025100c00c0603508043c00c800e01003045a4044501c8441c51030f20b000d0410403070245c1441220f861822001640c5003a80040b6125506d200c2d80c0c20052070303650b0001da00244046005045038080e80d01c841480d5071540c0605041101e22680200c485450940202281c007500c1c1c009924154a00c3c906044846a840d042c00c0019802c06103809603061070f16120b4400303105118040c2e0280512064170000380840c1844070403072903c031006600b41d18a910744155000942d407201a580c0ea4043caa9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 465711232 1250 465709982 465710017
    0xc030207140415060201050615041809030318050a020910080303070e01020c090a0507082a03041e140609030a05091207080607030605180c091c020a121b050303 70
    0x10210b40140741e05040c994406209000205400742d0641119021b1081180c10044400440200404030700c60b0344150380200e103040080c880074180305c1e0440a0001d002c1e0600043c8901481b00c82c3d90f054803406400c54654004605140c1145841c0300c1c81a0814011141c424810741410841c960360f200281c658000c2c4001c0280d0940b040c0e10070010003c9524006d07103080502d06203c03510700c000e0719095039041c2c0800e0048001803a481d0070f81194052140784070088102e8407200340450441548090010340e800f1154810b8403244000b0030003640303e020310999544040f2000c1c009121704001d80540862100e800411a00004640c800280d8109a108507040702011102001c40d41c640003840e8068015130044030100425281c00d03911000c1164816184c000540c0040407048110000484890390a10740034044850343c2d0504505d684558505295425509080e5400003140b105040d841454408000c0840f01c0400c540130480c04180c00c09240c2c484410380c00c0000094a038000c0008804030b03050340 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 465712482 1250 465711232 465711269
    0x110102090d140c03030a0908060a0b060406030f02160507180501230303131e060905031207170301030b160c050a03111218030c0910090c030b1c03020d0c030207 70
    0xe000f003e00403031005040380e5403044071020160600d4158411303056280902800688501c03243d02600c010960000c0c087d0f482e185c01c1c80800d5000b80354014601c41119070134408044000590500c1440540c05000103003500c03441c002c1d2690180c4880300c2d5150019040c1030040100000c1c183c00380041510750303032844541c03500200101f40303035020300c1c02c0003d0b0b8904130403030009207409a4201103d0414901c0c0326410881e80701c0200b43c2d0b905480c2d04c260b81e0140d00820b661a007218a403030203865401e21a203c50b51081c0718921000d40c080c0c0081c0c000361900e00b02d110a2004581c154201c130081d207010350812000645068a5442d1100c100e0340c00078042c030181d801c081068060901c10340d44007544041140e615502140038400b550106002183d000744503a940c441c829140c201c901034828040308802c1c1c1c01c100d08000c444805440000c081009140d101d07400d501a9942d4981818252441c8c5404503c4a041c142002403070909030600b01024028103c0722400403d03801b0961905450071244002c10039100d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 465713732 1250 465712482 465712523
    0x40b0711060a0801030b0a091703060102070b0a030c180e0411120a08030402120106050a03110604050616060b0603090312090c030a03020604170a1d03010b0a080706110102090d 77
    0x4003481100e900100c0099140c003400d03000b18219069030b0240b203508010341c3c1c0b017240103022503008a8001e00454048800c50b10494030510045510041c184151842c1c0d590b581c1e80c80070785820130490240420f44480141d154194451b007072042481440007118140c602e0200c0303071000d08030003074000b0744552944900140107441f14806100340740c2d40801154684183ca040c40b40140c0c0081c0d07812807240c4d01980032070f0031810b814040c40042c0ca100a18540d90b05241d40e44d200d04405081500a8204c4c105100020f06039a801c00900035420040c030113001103500c0f03890280101c4401d890464400e682c1071040c800b00880010a4a4401540b5a000c20b03032510780000252408144010540d030510840c2403d0301011b40c08915140624400c0b40b20b594105918051041d0741d011341103440b0005540e003141112072441e01c00030b035413102501800004849145501003400101150881071a903030282104011060703109010039242d00340031008504240c82000001c01c00d0481d10409800030700e80403080468444c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 465714982 1250 465713732 465713753
    0x109170d0b0a0f050405091516022a01030b1e281409011502060403260c0a350408210a05011706041713030807051e03040b07 55
    0x64009001c2c4004541e43c000415403072040e4022907000c0c609000104020f000002001a4500d0359002540302e550350b0301404a1660440b44949021441181072500c42d02d5a0400c3c500c5140d40145640a080001700740003600b5205641409400ba1069030001114910481c880c0d13686604210703043d803901192460580816000301c2140302100729110302c000703000c41445c01c56040000c0c0903140b0071810782e1703030b41da048001e1040358201c140941c110800007800688101e58001c0540002010940048942010441c01f0302044403a02c030542800074581080c650440001080002100390103c241c003201c0e0710051800500060401c0c2d01d84405001c90f08016090042da5100d1401c1c2c00d0400100561444c221905c2400f0740743e108900d860400045401c03c2a40300c02c00c811130380440200041e840b5035072032004601242d541020007030402d00c0303141c0070a0200007102000314020009683ca07951a801c100b41007018603980762181910340710a038824840c003c008d440444611050389030301c0e59285d060200324507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 465716232 1250 465714982 465715001
    0x14030c0706020f040509060d05030d0b0105070501151701290109050303030c030103061505030d0810181401140d030e030102040e190b01020105060604050918010204031505090109170d 80
    0xaa0011940094248108004d001100c2d012900382516440d90801d005d10095800c0010b05181c0040001d0400005541c0121603031607010300d4403c0c54011030380c440e81d08480c203861500d049103200580411203403040607400c01c50307009450005c101c401034400030131051041070500c0300c0307040002d0103082c0300a078000d03901d00c4003c1c5805416280c1e20b24100001c48805c1e402404125602440d202052860401c40c1941c3c01c26204054000d0803103128a0f001560121001440722042c042c80402c0814002d001100c02c0d000d2800400d0f010800c020340d42c802d40a0901c0582004100c0415000c074030a8503a100400c00154503010f00313205103582c50a002190181c8075541050341d001e18140140021510440c000780400c0100d14010070150403c1030049003078a85c1650119071101c400d10041c45545018010b494101c40f0413030192410072202d40b41d80e82a078015030300c01c3c3e070784040468400e000300440d4010185c0c055000f45c001c2114421650b5094201d00c0011103000b1042c2c008141c0c011103003407503840284071 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 465717482 1250 465716232 465716243
    0x6060e1201150b0421030905130b0307090e100504030e090c220914040803150d1202010c020609070308040306022a0c0a0b03090c0d050a140703020901060f14030c07 72
    0x3041c1c50b480001115841071103030002181c0485c0300303040c2240c0c0040a41c0d400941c03590b24040150b140904007c0b25000c07840241c01c00c55074070001d44403903039000c01200000303090307408000c1203001070702e146103003403440304140ca144d42401c0104110020394400381040079414226880141038480380740707821590141e500c208005492324144103080e42201c0180c0811141811014800070b80700f580147d10881040c1e6005005401c244007050441000c44504841484094045c0380b80e00887c0d100c5102110001041101517555403540c900d110740d05025450307210391400028507034540365507182c40740d600c11440040c0440b90b010a2010607003650304c028a8610300300c503203141580d0040110003600c1e2005034162034030440079001300003840c020820030703203125000b100080d00240b007240090180e5040700c808100c40c180074092040e00010090442c02d401011313400000c0041504610500c0941101a0042c2d400d100a520310041d050350f0040d00054001407490b0341076102d80710183d1403001d601a01000811 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 465718732 1250 465717482 465717521
    0x20c100911040608010b0109051215010f0806060a060c060f0b0303031f090c20010902130c030c0309051c3005060d0b0a18122106060e1201 61
    0x14050201c4495800e01c40868042115940d00c1c4041802c070f8102c460705a0100340807182c2000f485c54002d00c1b0076040500c0c101581d0200c0e083c0011040c01c00d02c241c000400741c011a000601c0740300000c1042c0c80c0e10030740546c2e00b00c3c0c0e21400e003032028000d51412200204425220040d20b550b01d03096422542c084103015045985900785011865240e85085001030111424901c00003940c43c458000e20b040c070b400726103a0820303c400c82210030720804202c0e51107419640d00c58041d80016165000b2145205812860026400c0d1140c0001001d0b901c03c0080c074002c05052032111008a0004101520784099000301000d4400d040d04017612102082c4440b500740164000c1000d070043c201008201000600502c03c01550391103030308100c1c400101a00103803031604024000b82002205612501d0042800540c400141c1c800341e4414420201a96410000400480015880c40204802c0c0001c900290005200b40c50400100805415140c40c1c02c512030441464030200c2c18000390310882c1c44c0080c41c0c000c3c08 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 465719982 1250 465718732 465718751
    0x4050a170d0e0d0e010507080f030c120601090b0d15080316030305010e070804260a0306060f17060618030102030403020c01080a05090d0e031501091a0402090603010504020c10 77
    0x980641241d07074414a101d0811903803107180d100204a0320b101280640342c8016051100c4011159600006001c40d0342520400101003070342040303806184030b23030070102d40710365200010310f00b03200003140141c00541480034819090100c000d03000c0940c2c40c15440b031400010103000f2103452605101c0d082d070250455020001e106d04540324410344001540d4000d841c20302c40c5990b1505012076081003110324100050411020074001601d4404459510b0710311982c00d170844880e08603260560344501e4160010035a554400c020320394000c11503042c10342c041e003000d0040c2d048000600001c5030008001b181f003070800048040300440c15114000c1b6099000c1c00842d164506440e000c2c1d55901041400c40c08a9090000a411303030586000300d500c01c0148402409500c0602a0142c0b52003035082c2c0040d82c54062132405054084041c40d1403402404140808541c0d400e82040c2014800e07120540580103078010000e422003a181c45088a04542040d42d005a441d8105001542004808040d20035181c0c04c008041 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 465721232 1250 465719982 465720023
    0x8040809130f0f200702010503270a14010b030a08031e130c0506070809010e0f03060a05071e02150a060b0703050705060604060608040f032a050c04060e0f04050a 71
    0x4086142c81e199040015000944102410b0200320184210701141081035400651043d070142d40c00c11862242c00d03101600ac1072229100010221851402e03a00c1000c1e65070a00c10810521900d00100a00030080c00d6484c00210341c4810601c2c8010b80302400000210b00c6010b0001c802c10070b0740e001b0010220311805c144c0d41d035120b0340004000940744031940742c1d004a038038a003100072503080b142d00500e010f150400d200015222645203e070441e501204410011000d40c03814044688141c60402c4000390601d06860064095402020810350a0001c90242000684c0000d6040359560394610760010303981d074402d07054020384041d03046820007000c08a01c070710030950048013401c84240304801b580c1c0700b03a65880500003124540d114001c002210280840d0104e107900d044800450b0181c43c2c8007110003040c41100702185110051440e08421741100c0c8010310900740840c00c1e010700111001d016492520300c400510103005001c201200c800f0f01c0c0414100a000c01c403500ea0a035000807a50110f2103840b621 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 465722482 1250 465721232 465721241
    0x309030f07080606060a17040203010207020d120207060509060a1d0301090312050606120103080a0e03161815180b03070902091822030215100501110d08040809130f 72
    0x5100701882140b01142d010324103070007525008613080da0f800c2480b483c4224047d46c01c040c06007080e40c05550811501c0056140c3c8a07500b003000380100003664542ca01c4000c0286001e0782d0360701c8841003090900201001d079a0715002c417154140145807a454145120f00b00c0e00899203544040c030780c59031806484500705074110b5606100707141280010000d9603604001d01490b0b124440048201920380001400051050b801500d144441403400380c0603c0c18140120f80340500d80444001301b00d2181204100d1907101e00841092080035840c18811145246101d039032640d050b0042040300140c02e4500c900c0c0c0c000301d51002588150007000c0b508030694842e160f0b00294042c0543e28002d0b04890042251214002003ca00540e13041c4d070341c041ca005850402d4400343c08410400c0341140180144c0984c0c00d00780c24125401010003182014402d40341c000050301747d400300030b4040b890341c201d9001240c1075030f0012034090b4003980001d000340e60744641c6400141000400c3c5030100c0312a140080c8485004c06d550701 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 465723732 1250 465722482 465722489
    0x3070602100906140112140a03091208090406171002070b0a09080d0906020d110703080c130803040f1508040f0b0402180a06090e281b1403010c170a0504050309030f07 73
    0xe42843c224050303880c80e0740348c58880710040e012401413281000701c500102c90b0300780c80c00d014200c3c0310b0810007072100280543c0c84039444240d9160154031540d0b488001072205504000700e52000b1481c045281d035460405d8040104180035107a541c11840302841280400c40e5401a092882002402c2d081d14001009401144190000364942500000030351144421200703000e801d51100c07a990769a0010b02001a403113010554000e0110304000a44003070208080c0c0050000300c1c1900f4074981c20031111201c1c8204490340681000161801d0201043c0200c1041c2c0501e500b010207180556518000f0907034412050745014a840d184004011030820168070000503a00a801e06200c11000078038800d42c0c031820804000c00712110203188045262401003c086002e00c200e0310319200310001c0c0144000317500980d00101c40c000540d010480e81d85001c4c030425a0742c029608006d0403450100001e543c414a004103554105d9270b9500214041c0034007081070320b2400c5030003400c588200c05498201d0743c440c0f14621 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 465724982 1250 465723732 465723743
    0xf01020f0f06090c0d0f110a15090e060d021f1e02060613050c0405010c0213020a081509070e091905010b0a0305010801020412080d060504060311090603070602100906140112 76
    0xc100c0c240e14007640740307071a282d8000d21059414036141c1c41d074240c0c45e8107c10303810f030b032000101c42d000031304910003028880300000e59150f080321039207071001500c903814000b03021301d1054040c0280440169100b02c20300c0404004106582c0890f802e000040e80c1c410180210041c0c0710b210800340c0d41c0b64036800142603205400c00e582d040102120441807206941090f0b030300341c2c00e103c0244000d2240c2c0d4814020000120700040a403000401c030300c80d40c1403c03a17100080600000700604104000c80d44200c1c00030200c1d650a680782d0f0030303510f08900010700100c241c01c1d0303042c0b150703100c0c0020440c080140e01204011400c140d00030401965100c11500c501c0c1e019805072404241040000100e1f001c040c800d540440303c1c64402c0c11000c0030540d8071148540d010ac20841c0443d0342d81e0401048580f154031802001e0341c0b1410740160400c81c00c100700115100000c1084c0c0c0319520102c400c4c007245038040380381d100c42904900080303a12002c5140000140a140210468080c1e80f040005844c2840500c02c000150188 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 465726232 1250 465724982 465724993
    0x609050d030b13091e0501060f0602030a02070605031317090102010c0c0f020d1b0602060105040e061603110708180103141003080f09040c091a04140f01020f0f0609 72
    0x90100341e003611029240640d000c0c1100349040f103811001e03081800c0380e034440c802e980d004d003070003880300410814103150689080c2e540d42800d0002d1344000d035007800a40780500007142080d401450007951003103d80190700070400e001c4045007001c0c850906000000d9403103244038040a41c2d413483c85a04c0e802001e107103801582020b507981a13281c0614025034045070482ea40d00c03000401c5c0d40078041c859414210488480c0c0ea0014940c03c120070a629140c09407000d03a026140652614013000300707035207503281500315070b0b00325000f03111003001a24440b0a81614609011410710306000194000340110385001c5c01d42c0c0300c002080754155402545640060308240c900300600d03d4044903019629034105ca010050300001501800402c142c3c60180902c00c01c0901510f2520051001140035200242c48640106400520900c203003845a20402c1c0700003120100346050910740080e80f402e0000f01c20156004a51a41c440b40c2c580e4800c0c001210301010290490b041010000b82d000da45240c200e55104003030064 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 465727482 1250 465726232 465726253
    0x501020c010e010f110d091e0c03032c09072c090c030f0408030a0f06120c080d020c010e030c0405130b060604030317070c050d0203040303020c0a0f0b160b04060905 72
    0x19407050305012540000a20301b040300d414004402080700c0e100030303a8400d00c84c41da103c080401c1000c54a0507280324420340d0f1b140b01d00d941340207410a00c0c0301000001041002424448100401c02e050a80d010308898950440d00c491105071440e081c1c00600301b1085103102e01850b0b8007044890010044c00003650a10744582d5071070444e13820380c0410703a00207200e8084540414042018040516081075140c0307400141c0558100c0c0481c103e44003a80101440b42c0078805a20a00c081d101c0841c1c02042c44001524001c540d6a20094554521070560f6061115101e14006692006c0281400380303140a0410440d500b088908103c06d14504030301141c0806a440001da02030901406070307402c4030b81c951a080301c06101501000055480142000c00f00110f040a880200b00104241d00b01105c007500076582c0d842c11414000d041040c0c80c4000ca0140c0342440080210161051202c01250411940a0389501e08024020009401d9540c040c0035016000144070a004050303005910181c490b50841c0d110558 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 465728732 1250 465727482 465727511
    0x408071a040b0403080f040f060e0111070806010b070f0b0c2709010501030b0301180809120708060a022a0102042c1501020102040b0d0b0109060203030c0403080a0c0501020c010e01 79
    0x107240502d04103082d0500c030810025400380040e10b40c20f110389810b54209500e0320380c00a02d82907a0b07480034001907003218250034039503003207415101100050000b1345603035801c04c810f03035a07900b00610408141c2d820010b1f1520030300020401181c1c03055404002c4a01c2418001c0c000340140e0080e051780b19a80c3d140301c8054400c015185a210107414000e04882e0b610303860080190300500d01174030281d415540b01c086010031008000001c43c4024400c030106900c84c85013070300b40600507006010740c0c581540180801d00010100207030320707603002d09501c034090f9540702c0080c10142e0801c15110029a100c50300c0881e41014401900900142c1c0c0c20841940316003003000c46032004c802d0480490303840c4d00c045440410107102c2c9d1030184103034001d41800050303d03007543c2d0100d52115070b00080a41d241c480d9502c10220b230340d603070007110507004290350703c01075045041c4822100403500c59444010145180014480c0191b4040c3c421404020f8101c2c008545070003201045074007a0484202001640d46024042c00b034a55 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 465729982 1250 465728732 465728737
    0x9020402180f090411100302040e070f080903040b030a1d0610090f0b01050d0902150f0403020307050a1a0c1c0c060c1b080d0b0a0810050f04080306041805030408071a 73
    0x3030b0400240401c8805c0e40081c003a00c0ba44400d060303400c064080002046980d400600d041c044c240b04c2c1e0350101500c034840001400c1c0e8001810007800d40d00f04100c01c000c418851003d0380d8008820400c0040c8541440c42c0d9542e1030b54081c81c503102203020340700800480043ea6400b100031108440010311141500d4001c800480340c4038040320307010036000d01030705e034010303034aa8407003200540301801e0031003120450070903192940c0090041000c8034800050600031401d080c0302c51001800c098640040c07003401c4c011040040e44040c0121845040089495410441c0070042817042c00c00d168880000407050300c0000b01002258002651b205060100002e600f5100d15824500298201c2c000f003016400d0759550506540304030703501700c0b00d952100d0103107800d5911210540014403905009101c030641c48150075066a00060801e0800b030042000c00011505140490f64040c0703044800052480225801000c500c10464002c0c026210100340459031100001d8140251110110440940a2080320041c1c062 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 465731232 1250 465729982 465729991
    0x7060809120310060e0a0f0902071e0302070506210f040203010c02150109022206021c0305010b03180a0611031b09060a03150306020a02100c110a0308090109020402180f09 75
    0x1150341c01800c1050510801170781c41c0c5840020045020166a1144081500c20b19044144201d6002810408010840820018203102e1510032180f24049440c083d40762565803048a00840002071407810049001c510381c1c005400f4140c04181c1c0d030401c0d205244800320200d50403406986040689407429000192142740401d658007120310580c00d04c0c83e280080d41008140b61074040100300c064030100c50070b16012001d010725a0003048081103062220b070f0106d0400306940c040c0b5142c500140510350043c8112a400b1b020b03024401850060310302024135081c003490300504424a00902606840c0b1010011402070484203802114541c1c4100d124183d4411458083c0d4800401c204501005010381c000d03140603d403500307420810355600d0b2604426a4440844100103800512111070445001d01c5068001e0649107004540c1804842900e542c2d0240b207180941070001a50005c0d006030300c03d400c80c01d900c0f503010b0800c0d91102801840300031312005960260348514003006412845082003200c2520a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 465732482 1250 465731232 465731251
    0x907051c150902181e0d110103050705030c0304110607050d0e10031112090a020a0303050d1a030a1104240f05040e0d0806010c0c06080a0f0b1509060c070608091203 72
    0x400484810000390b0178013417040001458a07200c6024a0b561028410300520303000310741c0014a400c00700d00040480e40010004001e208040c000d0051407059072080d02da0040c0d110681070540305001c40000d040c0d00400200500c2c501c18860400c0134030384c2c01a050380308110117686000292403a08000e606864007003070010f128a805000315030f0415024000740e41c0141c4994140ca0801440ba000308444c038500da0000c1d030100d000060700382c0d01ca0303400b84074040000720044940c45e101040d9000203515581c103224080d1684000d4030940e01255116441001811501c3c000d009078030082c116041d54420702d500c1404000d24120100013181d08040c082d034000103c4160140044804040041c2e403103000103000c0c107041101e82454030000032010491000139110b942c452410398500515a00d080d100c6000400c1481820700c1300c1d02e0b0b51503d4a028143c846900454403588605048021580b140100b4015440a1040c810006a025042400c103801010080291600c80b020120030703070001d01c0b09a650303580 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 465733732 1250 465732482 465732517
    0x60f0803090f04020d050c0c070e0c0f0a02070906080705010801050321030c09180402120a0503191214070f03061208070203010f050403032403050601050907051c150902 74
    0x10303203240101d00c1c0c05078500010f100504048141c6101012100115081e6074407a0000810110100042100704c0061200e41e2002c00c0925001407032f6401d074040c10610303410039203020800d0301076903000344a00405495040000c000c07c17903a880791255684403910906005c10014070000c0b510b807c0c0401c800030304424042c441e18101044130214460b80d41b0003800084002428409074115a90320066480d40b0205144484901d0605004014240030a504a412a688030600341c00001e50080180c401484501d003509600200306001a540c1d40032000180420514019a2840358105006c9003805003469644074031500c19030701c0e800d80c2110050300420b00945030106280340020441802050b040380b02400210300c1849180c0c50105407101070300c1c2100800c0c4c480c000c0e22028501200c65881401940e0180a82649540c90b05901c0ea0010300440d40a06440c000258010b07001c1d8045400c4004895503446408018206110040c1012404a184c0c099031800c00145010b440c020740d101c2c0d00c0360b03205000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 465734982 1250 465733732 465733747
    0x22050303180112051009050702031809130506010801150602211812010920090a0e0a0c0807060315030206090918070e0109050a092a0b0a12060f0803 65
    0x800240300c80551504224100d0303007124903d50203001d0380740143c40c100c4140105c9400c00d000310003960402004103086510503c850f080300f000c4411250399046003501c0c3e2041030345900013036040f42d00080c103010300248900c0e0000a204801544901442450540f1200000782c807000f08903143c2d00034141071094114002850743c05490310358010104c04450f5402d00c031820301c4ca44082103d54143e182d22651696481c25998144004100c0d022802a040c40a80f0804031850000a5070b48002500130504189d6428410602a008000c01c550803078010090550749695002a160344103118064140000d0818804003203440000440505507540200824100494001446661784004000721b55006003000340c1c00d0024010302842c4080c000c2000908442d6040075404002c5d40c030301400c419101454004c1103c0450208009104500c820100881002d000d0b0700107207031900b207a50060070400030002141c0e0071598009640100e0006040000d100107a03440380d86004841243c4650720503a0010811070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 465736232 1250 465734982 465735007
    0x101203080a18050f010e030310090b030102160503041a1e03060d17120c070209010e04150f050403120921020f0304030501091a19020307111222050303 66
    0x960320801c07540000651280340180c0c201d07002c080c00d205440d1908107096040c4292400c0c011200c541c2c1172103008603c2e40c2820480380c0c4400040f4400d1480c0540d4402da800b0391507800790100d5084500f0100707001d60681039420403e0700ea078464441c18014035484000320781d80c249140c05450f07100601c65003400a02841074612166a880204200d0f40410002c14aa0001e400c41070000e0904005030034403a00c403150b0208440a0302d03405043d06440d0a800d10081c00107a40718042181902c110140080480d2240d2514515690110311030f03680702800c2c490581c02100450780158032650190340e44000104c00e044c1d68800311490010094a00f40000302266032201c4108074801014807c0e20442d95020050b98140d8190b03000358104842a94480540009015a05c0640ca611065451400c41d05080030300b51b0611804d110a005083d541d004070008020718016001074035410402008d40300e030381d41d55140f00715171507103e040c11203840f0303080040120440a000c41c1c40015907001500075840e1503d440b094 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 465737482 1250 465736232 465736247
    0x60c020d080c01091703010618030503041e03080d090213090c23041506080601052701092103031b020c0609030307170309010b041a090a06120317101203 67
    0x501c00c1d99241c014150011744140e40e90001301d401c0d9032003941c595041a8000b41140c4c80b0601c007254035a1824401d0000c10740200c03c98049800300010b041d52030004201000c628921944080c1041e03001040034510a003283d042002c58520850700705a1180c00d1700250021a0b61581e0041c050940c403885c2808910280d0009004140d2500d20301c48911149400140030380d20b1002c880c510800031194100400d80d0840314440e046042420080c0c14461050300344507900c9544d4210304035500c64400000d44e50b034046c45100000e09501040c0b10041d40708030310b6030503100280243c2100084d1800505d204865000c5a80c5114004540d001d4842d140c1c0090070802d0301c0d0000744803503a040c0410410900001c00b844592901080c001c101991a482c10100881c21a6040180107028600300365162819540c0004aa00500b000315100c040a07103071441105c1c0249082e0300090210501007400c0400d2541003c50b542605003d5268945d880e61603041e6103640c0e01a48c441da4070f0300c00818182c0700c0080c3c0258007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 465738732 1250 465737482 465737497
    0x14090906060d0911090c07020105031612060308091e06040509091606020f060c041d0414071202041b051606090c030803040302061e130203030705160f060c020d08 71
    0x20981415034010b4440101c0301c3d1103400301d0f5510030503200b010306400c00c40e1a580d0301c03040b80c014043c14a04143c00283c210b02c8000d11607005c0140f1180da00c8015030160415a01e8441c208204008140d141c3c603000030f07140c0c080d030030340e61003400e058004821101350038000e144034880c00f8000d14202868041400766901d00236004038018000d88086030320030240c8001c0900100b54650003414034074112a40903042003000340404ca9000b00410090201703603407042c0036509001000c0103440d150360b120b08142c80610700c8110100100c0c040e103400003070b00a100d24035886555000319020001c20038902c03144810721006030507040224a0a110b10404001d400b0b00861019001c2c00c000315401006a88006110245030412a1000c401009000900d58101324040c1d20083c811101c580c800d10806401030180385c010a410005c9070310480040031914140b0136500010b0780081200e00385d52075510051019104d80c09115504002c0c2e480c001141441120500d502c40e4001d013031b04641c0c01c11516100c0d8260300260 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 465739982 1250 465738732 465738739
    0x160302061f12021c110a120c03030c020d12030501050307081501030602130b0d0606080f04030e0f012706030c020a0c030201030f0204050d1101180e01090f11031302090714090906 78
    0x440c4420754039134001d804850500c00c01c0480e107240042000c0014404a03600080120a004245c0600040031184074605590b01403c0015000100707100003140740511240007131001c450103c11a52054068200506841c400c800383c41c0f0043d02c1d10100713a074a40c40c40d03003580d010158100041011510543c0141402c05014a8444881d6140d1401002a80c880014101040e42d0340c030003000119408010541c000e2044c2c0340c01ca14038140703070302e0082051030350700b4143c0d1042140a03089661a03026107519020007030008114107584a50118402404a05200785808a4103100c21511070501c0407031610009a40105a07084450070b50300110010910b900c0c0c2860040c1c1e003000301042c1580c8205500551500ca4001c5000c0c24003808001040d0a0341c18201e0304007080141c005001c0e104602c6003c1d41510000b402c001540311000100801400101c203551040040020500c002ca0410800400d13080d40240d4902c4081c2c0c0b40c1f03480484001c0c51440d00c40c6a26030050150103414540021b01c030f5004503004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 465741232 1250 465739982 465739999
    0x80c030702070b07050a02190308190509040c03091e0309090c02010605181e1e19090c03030f020c100e0a15091406030c03040b071103160302061f1202 66
    0x41d8400d80a513400280300303941c0d0354022600102145005142201c1c1000d40450400010340b4503030790702e0385501403c8111201080c90b4140500054441c0081e0ba4841c1c2c2c00078814401340181c05800780040c58848801c7d1000c14038881c640d0040800904013440b400d41c0f65654010046c500f80c2000020300b51000400115500c55000107010341e03070030b0350714016200c151016440300c0c109203240411404840c2c2e05124192092010051342000303003100d42100b00c0081410700c5250355282c004004142011958007010751401c4515414852050381d009d055911030b4490304005440395005030f9890b03035119031950340210350090303908105102d07082e07a000518004d001561a10744800c0c0036008032000c1c4030010009003195a00300110300c448031405401c0380058a13264a1340c1070913843c07103880d07100040c00a40400700c00004602d146103d00001d2012062200640b81c5808290030403020916150340d0603001131040b0404203400203100c40d040700d80303103c00c0d1002945c3d01c0d01d070041b4500d039101d003018140d0341304880303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 465742482 1250 465741232 465741239
    0x504030b070203040e0705031504140c0d060504090501020c060a09050d0c02040e010e06100e06060307110f0601080114070e03070302090a2703170c09091005120705040b0102030a080c03070207 84
    0x40302640128011f886d1030351240750840c2d400071411000ca0b0150710031420100f1769940d444a4403480c940101d044014075940f030658995610181a0341c0c0d00040e08545441400820300c0010340c01742044241d00c00951301582c9806200f10f082d01d144040203415504418a411083c03401483c00c40074042c80a8130124607021000c64045c00c41d001d03001082d04581044040040708000310340c041011b880284c00404141c2072000200300c3d07502004103901c041c0076098502d4408040100a1802011542401c8616641e111194240030744208114010116100d001007a07100b07005100c0e0101c165000b034000d0078582c1c13460f0208802c0f500090f1404002a50b10030209400306840c031001481e035059101c000d015501c0320310b4010000e005aa122401200041c130174049031604120480e451540211350b81c1e0403a44540c0d0a0661105056005c0342d030114170300c165542c0070280407030703c00d04417081101c0c208070700d50307520005903140e11a0a48120002e50701000040010280d14040d41e040000c61040b183c0003504c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 465743732 1250 465742482 465742499
    0xc1c0c15030e101509060b0d0e0f072d080606010e130c09030b090d09120809040f050612060112020118120b1b09060a0c050c04050123040c0504030b07020304 69
    0x41120f01c1d211a50b489204898038541200c0d04500144039640303081120038600071004203d4094071b504400c405450322051413900200300039400c80d01e04580241c600c9150344010031170000380e582c0c0c00c14403c031140550302d5100c0e558100c82c1a084521010140400d0303030768140112103140d05527a01c00e42c0201c1281e00010940401d2050f4814401c5c0703615803906650031401d02819884008150401e60740c40040f422982545c04030480080301e0040f0504a103100c4c9500d000c404601030f507410250003500d4511502c41a450f19004280280700c04c1d199119102070030080c2d00e8803100709008a03510690104050801942703c1c8000f00f00e07000b44070049503070103078542154a181511440040d50340d407100c90305018464840147c5803440c190b0a2110503c1e05001c200407031000d0081089000900408100b02000e12030140500d00842c240240200039640c3c4500310161155000220b0288940c07485880c00020b0515109245100200342c40b040e081070718543d0756070489070005091a0440c00b09100000702d120 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 465744982 1250 465743732 465743743
    0x6140d09060501060f08060607050d050c030408031215120606060c030c07120c0618050d1505040507092706110c030f04050f060a1202090402070507080c1c0c15030e 72
    0x1189540b403202455071044010048000540114883c00c8c08126680c002a4002412840c44105041284c0c54000402845040d400359611031400ca000008041c0b5420f58004800351142c80c900c02a5132517290301c0d40a104400c1203a03062003000f81d003d10042144c44c90080060300341c2101e140100c0f4504140301d02c6d56804c181b183c0d44600e10b1032400300074080030000108143c4000d481c04d490500c800f4a08034000d00c1c4c4d4408640306481c01054000c515005100c0c00004100c0385210501040c0068209031500d079580398094030400b003103640740c2441c155a512006014912624140380f241e0182000ba440d008010113041c41250004001040b501340101c2c41800502681d81c44050f0103500c0d40d10788002d0000c0c0e15030807114144203c900300803950350350703400c0602140242c065506c016150013030400402c00030b101d40340c006031080c45079402c0001c1c0180006000004804161100d00140740000340a8040030802e0f540104000703120a01406901003091400c1444626441d0228501454910850504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 465746232 1250 465744982 465744989
    0x41a1005040b28060915020601151e0e120106050310020c03120f09010c0903050d0c11130e010c0c080a0c020a0e0a09060b06031e040c0302091f05030706140d09060501 73
    0x82c04400010030213140c01c048003800400250540040c09040800000c0d1603120500034071002c650000c81d003c80c801d20912003041d01c6820040e4525202007509000392040084007510b51103440c80e50b00c28407250340306024050886402400a01d2000b100524810207504142021441c0f4401442000c103d561032840060207000c0707000c44908181480e140c4103003510279000c00b000034084241010000140c0c00503020464000301d1600c900c04a000d440c148014520384507403294050038158440e040b8108980c0030003030203112034008000300401ca150a071000291440701134002c803410701c42110a03d01070640ca400301d61005011030845625222621150001965094402a590078460040001621a800149800300c400b58203500e022408914800c840c01e04210f850042003000c1410082c2c4c441030305016641c01050312006240c40b2003006e414034401462000b910807141c1e000107950401262460a40f10350317a80707500d80040701003406030950b440444100c1c4141d50b00c030465000308485c0d2080c035018 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 465747482 1250 465746232 465746299
    0x150603020c1c02074407090b090a021e0a05211003021509040507050702030f1506040902010c05120703090b07030f0813021f0909020f0306010c020d05060a05041a1005040b 75
    0x21701d030031040d554500101604000d01c921b2a101200ca010b0303035403091403540040c4900c40580e035010002d40700d94040c2c01224021018003004155507103581d800002912131020101554180002040803148003000309483c44e40304040c9007401400541000c0b00070701200c0c15041c0080c0e1070500d080c0d020070101c6400302c41c12000180c01180010443c07401b8801004008540d070010b000180180c40d40d405400c0c005841c00703114030f40d16851034046900480c0614a0141c111040c1c41c0e4031007080302112650f6000c01d0048002410315900420344000b0310083c0c8400c150140e84480b04072103101e4007503400da517019140058805400c80c0240059903016140f00d0459040f500184215840d00d0b07014048004540202c0d0440740148203a00080001c101520b6000d08240f91080d0440c0b19030020540f4074440140241a0340141001c000c90080300790000d5000718455a50000c030104c0541c4070001440c01a540c02c00c003114202401c0080e0715140e006418030400051480030190030108686800b0720300c540920030b5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 465748732 1250 465747482 465747599
    0x80106031b02060c1606021206100f05090603040f020316060f0c26040308040b030714070206090d08090d0b010503010609150b0a03150603020c1c0207 66
    0x6000d5050203400d5026606078092290028410006501c40d08020544010004041100c05001c202c00001190745a080f0300c04642c0d41c5012220403805003021070344030f4003d4502100c03d042e030a01c241c2002a03072076016030b1500d0900b141c1130204a41a0300c00f41058440400071700c00c241c0565000d00c107648030035200c1202469828030f40720000e0a00515019001c3c00d015242e6140008101e0000003115507119000d034120098540c00e200076a180680c1d0000381501e44007080c04a11311850704000c41c05440f00c2d031181003807020340f41e41c180c0c020310510b000250801018031401c58030342040c01c01c03000710303900c0360302c0460625280c4030104c0c6400c2c210310019100c1000c16001080103090070310805000c1e00301000e0a04c0701501400054450302d45920504074002000210600602c1c4030303510217001c0300c0502113079244881c1d89070b00080103500001f08040f0180110004042c410581c010944074000d600d401174400175140100c40700560700f2070380580035012002000c26150312a5038280100c9580d0b070070180c48 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 465749982 1250 465748732 465748739
    0xa060606170709050d06020c010213120303060b13030809030a06020d0b0f0a050120010b04020406170717060d151d0f061e07020c0306070f12090209220c060801 70
    0x41d519140500200c1c14040440b209011039120608048125034100381c001d030340c880d4105005070091082c01c0c0312480010000b203000c50460081a500c0e0040c501070341c2e042c8041350301c5080c0040320341700d800b03075000d41c1c44c4185100b0400160701d58058114050018117840c08007030703d40c565900344d9008608003141c2e076136a039105450529148440c141560401c0d90501d07801c0c0d003001c0001e80480c081444072614920110100c1c850074409400001800f038000d842551030b59513505c400b038005070550b000c0003040e03004000003941c11413280d00292001c00c0703040a03d000c151140d009102d002c150a00080d04d034507090b130480250200d81ca0084000c3c0001a20020901406000c205800c20101558104541e00540180040c040c85035081151120820f62108416210741401380c0c80c0c800c9485034030f50580100c1080010340c40d04110079804a000d02c1d00c540e0300141c00e40549a04072043d0f450001e600c03405240c04542100d01410511400c18002c200d141e40c07211080d100c0c02004486d90b80020000790f030031001071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 465751232 1250 465749982 465750017
    0x330e0a08010e031206150703120e010b0a0303030b0402090a0f03030f1e08070915170c090a0b03060d050714130c080601080a020d020c0106031e031706030a060606 71
    0x200010402540204410040580026101d100d0403000d80c107860003420108001e0365a410108004510b032214130b070750301e295501c1e02808100100701400d180500d002c14644070390300c043c000c81014000c010820120300d811030340c0541c020000d032480684c00c960b00780020801520b80d04800ca004d08144251041498a0b5250080804852110300d20422100b0008104104294281541c44203c2d13410000c0b000d0340d4407002240d0a82c9543c0c8010340c2603002c41178600c201d5800c0040c8003403038101401103041c980d40760b0002d00d2a0b803140e00f0000d0303000340e085541040070b4604000507603003000c0c00400346401045262110343c40c105071504615504450160200d004c1d24001e1a001500c8480e070005100c00080c041001d41410790003440a4184403280000600c00180c0380d0440f0111044203004544466148881c2342c02054176000031995641d4410601c000001c144c45c20760312250307241d600c855506041440080d11428050a403907014030840c841000000c586018001c0500f0301c17a0340e40c5454802c500c411 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 465752482 1250 465751232 465751249
    0xf0723071b0b0f0d09061404050c0609030d03020c01020c0a0302100501050414040605040f02280f14060706020702040f050403030f15060e01020c041a01022104330e 72
    0x4070052144980c000c11441048105039002450361500040c0ca800e5554500d030f001d0400a42e00509491510040c51141500c11100c180114041c6084a151800940c00d00829100e03040c07015034198400c045003d14075100b600249201c87c00d80c80090306100101004078a80920404e0880150300440d94044070310107188a400d0042c20216001e2101100c55840c60207034034000b4102401c4a92030b1030000301030210300d650b800401c0f40d000e450680b4070014428060305202c0380c02580120401942000180c6101010050040c0d82c0007401341c0b04003040f03035401c21a0300c0d41700250407680b464080c42688013581d2580328038051013640200c0820750745800e140041c100c6080c1d04d8808011031034a900e215943e10703079039a0101a1444c6040000d0403a01540042c0d207026540c107000d50f8418105031503001013403090428012040820b8085603003c1483c00c81c108440b6007403212850b00d142c0c0500c0f00f009802c4079240714000d10040404015040d640c0a1040d82081104940c081c000c104400412506424036021 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 465753732 1250 465752482 465752513
    0x606020d0305040c09020f090a0905090f0c0609090405191b0b161214030406020723120307140a032004061202031b03011508150303030f072307 63
    0x1d080101d442e02c0d6560300d1040708940507094581e0350110300142c14514020842d4609030008080401c0c143d41c0314080000761000300d801400500502e0210526100700141030704e2030b07100003803a150400550380700340610404010021b44041c800c04440141044484001d005114018460b404802a805961080d1520941d01441e0014000c01c4401101102e21517400303107095100d9114041b01c11003040c00ca03441010015070090031b00d0f0000a1001b005115801020018440c03984000d243e110103010803180c0015060031078503904544010f800303039003400c0025580f10340a800d0503850300e01a0340441714160404442440440d80c1d403c501b112150795442111a602e0b1003404051425060074001089001301c2e0701c0e2084c01d41d170003002003a484200080400e182d080781125080e100c1d80e41782c820701c04400d07a603448180486c00b82000305021825450304d010710303000b01400070761031516000190183c3c22002400f400400c403c803030621480d142100c2c980354005c400b212030f0070b40390450381c280406510004035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 465754982 1250 465753732 465753737
    0x10507050306130e100f061a04050a06050a020316110102070e150609134502010806040e06131703100314100f050f1321020c12010606020d 61
    0xc200901d40d61002c4814001098400c400700b4030071130f0100468542030354070020380d804504158500d1514045644000c040f42d502885040c4000184580710380c0d2885207006040d085441440d041c00154000c1d0700034a120640c0f441240d25040da22020ba0b0b0a82c8400d03001150086003c0003440c03615a8108246006499014441e17031036410031b1443e11101c0c01c103680810b4041d1101081c1480283e8641c03c4040051740e2080c424050042100c1004a64002401c4880003010000000c44150148400d4482540008609105031081550019101c489000b8461507106032200270308003c045060180900030100c00301c4020b403125151400020545030a0300e403400040d024004c10040b0000e107640442140e801c0b00c40010306041c802011350500006404a4200c1d40c01c00c140c41c408441d803076100501c81c10341c1c50104441038072070300f0188000510f40d11015004099046401c0400d0b03a601180c0c84504400e401240c007428016004500e46d102d44038240003c0e0307590752400700480c40c0c040c801c5c40001590362 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 465756232 1250 465754982 465754987
    0xf051f050115030e0c0d02030715270b0403020418020d080d0c03020306181305120a030b09162a0506040b13030906030c090504020d06060e010c0201080103060506060405090408070501050705 83
    0x541c0e0441e61040301701012442415510b035040c003951400e1001402801d21000c100d0344803040303030700301508140001c0040300c059802401c0b01009402e400b003d020554103104556032500b4035540801c00945841c41061400140703101c03170140141e17102079800340c04501c00c1c1e20007911905504480e03000c0710150101c2e0702c180360040080012641c0c901c031580b1034000c502542d1581c1038440c4840b0b483c145920000040c820300c01c600c1c0d003042401581025003900c2c0c4103a5170078860161a0814061501019582030034254100d55030603000d1405410a6860507104800000d104111f0210750742040740240c0c07042d603042c0c00c803600348002c1c00002c0300400c7d07104100781280d103004001e83d5001011091184610810540e846c500341108920500c0c0e90001020020b0040d034655003001c2c0250300501c058803c00d004941d049400f60140e502640740207400c0c9405840e40030640e882c6072554000340070020140d9078003210400020030b2507915801c00314081c5000320341c0340340c80f885030b480d101d400c56030090484028410207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 465757482 1250 465756232 465756251
    0xf0512014b050d2409020a06020601080705010c11010f050903011e0506030c151804050411090a0c0e0f0d080403030503040b070e06070f05070f080a110a0605070f051f05011503 77
    0x100f1100100314411868001080712404c01000600b958040254800207078040081c446900060f814103a40040e0b00340c40a440da580e0040d149030039900001412004158203030003656005103200013a034142d600b0140d20700002c2c0b40c0000e00311010075401003c00300004601c030300030098603c24241e0008040e0000c06c000c1000000207184000c00011080c0c103c0b6001590010b0b04600749502c00d1040c41c0034105100500305031410030b40e11441c50402c1c03800341e1030f28070000f2100c1c60701c0e014204a64038107894100164500c04140800e81c20b80c001e080e074001c095019140000358503080204000c50007595460349a0515251175040302201601040401440c1642205a55611802c41d41842d510440c20740080c91245070813420106c0c15072203003150322402580000c204c0400318110205600c038107804109000d20303404003d032982180c0074681c006841440003c0c000b4660111810030140541c00300d461f4608201d9000c1c40644282e640e140c0110f4842004102c66005e052804860145a08007401016007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 465758732 1250 465757482 465757493
    0x630060e06121f061a03070305060306010f061206030c1215050f01140d051f0606020604050d0c15020f07020a05040c0c0204020f0f03090d0f0512014b050d 68
    0x25078221082d14a60058030310f004107000380e1040c4001e02c01028510001c251643c01d81032260811501c07403001c030b801c0000250441c50b020820906994005002d03a103181c1c24660100e4800301180740d1350107a82ea41d450040003291422100e41e00038030106020b090410400d1411028403c00b440380078018500b00340c20f0202a1451000032815507540c40c0903c50011900c0d00042c460200410b0043c00d036019803c1e1074481d4840c0c0c1a400c42401c1c8007500700340600b41c4c0c7c909040780d13035500c01c80d00a405504081d0601c040c041c446e20601e03000901640030768400b0a1104540c5089901c80030030340181038800220001142803000516000b040d04580c10800d0000e40c0c0c0014080c03600d0810300070701c25076001640554084004003502d00200c0d4034a0b04a459280105606070740b9a0101800e201140104482c1000307a48900c04440300d0b0301251001036000d03440d10502c488032180104040850202c00e680d40802c4210724900d03003818285242d1396075005448070036414542c031481e801140c0181e0008030550302041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 465759982 1250 465758732 465758743
    0x1510051009030305030a021c090501060603060b0901140702190b070201020111040b03150114070c050f0d03120905150708040b0702010c14070c0b0c060a060902070209010630060e0612 80
    0x540c0d00c0c2c405030b914041d020210158034203008c040c0401c146000d54200c00e003e4158800401d46005844c10081c0c0b42d00d03520319018600407403900a00055240300340002e089001c3c001740624070300c0501a0000380a940c03200300e503441d0841d041034070713240004101c0e281550707424004d0f510b0114200e10180d250900305000b802207031000a00c4500195041d808240c800e903c101080e0005203507001c0d40c240c0b42c0c106850045c07841629445a80d208503054030080416103020641c8520072036060b00c0d110b10300e200c84040200948003003201500c6a0240c8000c190740d10501c0c030b000318801d60384c581d5891414030301841d10000701040030b40700e04210f83c9025900f09410342c000b0804000380001c0c05040b515001c04e23103044026909540c2000981c100085414940000002180350140b00d8000c42444041e8680c01c90f84100c0c01289001f0f50b05c02142c00041200502450f22385088010390082d80c0603620003051261004c0306003001e0980711503074603c1c04001301c55105404035003002c4125040c2030000d4201600301e6030752 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 465761232 1250 465759982 465759991
    0xb07110a0f062316053d1e0e012307140415050c0d02060705072010050901030c021204062f0703030e090f0f09151005100903030503 58
    0x11228010103803190b84580c00d5100c3d90103c1200554681351401d820420782c4051804a40f0751040c8060b00d0b585078480600d0106500074220a203c54800c6440142044a88000d0156010369210065403031080f14201c081e000c00d960340d0f8003040d110390441d2a5400c60b200001c2605205404034860f00c01d55140a190342d402240764501440740c1340d00302400c00a81d1007254001ca19846541e05000140c0342c00101920400c809402541e540369400a070a98944000700c0303515001501c10403807000003038600010040e4803aa00035400c041c84c10181c0200710704d08895800075010034408507140c2c04d20340c0d241c01048040782d80362018200d94150020820200d0085000c2c40080c03254140041e001080c41c65a49401015100408003803401040034103511703081d41e4001a00090412040382140c1c0c204a18001e0280241c801d45800301e64403144040410300015240340980d00404070040035402c3c030b0044690280d461208101106031815003001030211700d4401110500004140800100b83c10900351b0360711 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 465762482 1250 465761232 465761237
    0x9060815090c0d031404092310060c1b03050a111002010905030d0c020111040303090e060405070c03030509120c06060907031e0e0a0b0703020901020601090e0c060d02130b07110a0f06 80
    0xc01541c0c5c070381d8002c82c011078204a1000d4906100040d40d1203190b80740034500100d20300320421903100c00704095407401103400341c507020a4040349030b8070001d08079101300383c0000f15142d41d0710711a40d00d90352101d0800c0d4011500340c07160940040c824005140110407041d51b1070702800208461009a5103092300d0b405911015a21903541d01c03982c2e40d8030f034000e402c110919003016001e140d0301c503107e01d40038241c081e20780070f00122403244100044142c2400d11034140106455201d18031300c809580d03000c401400700205031305c04c0340c003d003880740c03021045070405030a0640c2420003600180c035001c02444a080d41c000c0551301050b050071030440d408802e02180400003442c140b404521000426101d9240c46030500700200480c22640401691302e5040e07010f000080400d90a0f9903480c4d0341d8000d42c034182d80f04100c820ba80741d0072003440f159642c40c1084c001c0410039080c0601501345040f04807510400c0e19a9030103108410f80008405080000ca611245003601e8102c491141507800e10107690803060543c020a004d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 465763732 1250 465762482 465762497
    0x10f0e06030304030b0c07050d0309150c0e06040605120c131701140408030a0c020f070b0a091a03100b0c06131a16020d02120d09080409060815090c0d03 67
    0xd01d46007402141c01464005880341e41c80d05100e11205210350020b2800d0b201405208401074a00e442070207101c0c20180c10040ca80301410b1162040b00050003c805241c0078042d03105140b80c2e4544030f80b0040c00080c42c40340c868a80307803080e044145444840080005d070f203918080103d00d90580300c102e912000d07a642e40d00186110b060341c0392102e00408019504803126a480002c000410140200842c401d400b1810184940310440f0710584c1da030469600100040e42280c80c040c81a5000c1c01c019016052903803502014195450610017a00d81000f031035000700000000400c11154070b43d19600006084a600f003510300405882c0b540c0d12448094540b546070100c450f00c080038414211a2141031811900c210103c50030022502d50106460f041b0301d10142c0681d0501c144282d00100e0300140c248a940d9040340782c034550b8001300005004441e001c85209405000200b6490018821300001d4020750f001480700165400319120340b62070080c000d211236400b240c03002e000c589405036080401b5a0600308540d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 465764982 1250 465763732 465763741
    0x61407030e03150a38010e031f0f0501050a06050d0f02040b180a210609051c0206010524090906150c0718060501170a090602220608010f0e 61
    0x341800710440202c443c1403407820910000710340307990000035003000c00044000700740c008900c1c4500454030020001c0f181050221015210f5005001941007e08010151038510741210405001b02503404102c28165580e2800109464036a105081c003601b402c0710880030161074400000c2291044030000c8400d2500d65800c0c034401d101e40e4041e9000781800d601c1c541d4840e55107a114503544030441900d03070b119220090b0001420090030250941c0741c0e508080d28860503003a86c842c040074050401301110103104d00440d14807500c80c001400010510150f0103481d480d4548001c000c03071560365040311040054800b064000b10110402200c00c12a8180c4a90b10341d60786040002d03480003120301410b108540f00040e000d10b41c00707000c1001d200707a641210a85411400c0c00c41000100c0d0014012940424012200c0041e5002c0800c00ca41e40102c09810100341024541d03201001ea8105030440115003004451740100c101c407480c10303240507050314030301035078258980120080300c0103e0703108800f40c80f020302000c02c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 465766232 1250 465764982 465764989
    0xc0303220503150c0c070e090c0a1e050f211b0303090a06080702010b120d2303010e15100f080f0c03071101022709090a0b010302060903032b06061407030e 68
    0x2400a080e000c1c7c0981c103c4c604600100e49412003c00300c03501c1444482404101340805c041a4203c24403060106000c3c2810101840030381c0b00b042d00f00980c4503507100040c85140c0840c0741007402c0c2c0f02c2d500025060416203882c4042c41106114911440f0360803c0c881d2450545503096071404031469407030b1010550300d0342602640100780d800c5001c1d070481c1c0c502c4000c882c038140c001540f2551603170036500d00c541444603226080503400100250440070800700300420190741c49245054201c60441020100c1403040c1000612248524a281c000300c1c9110303d0802035150032a41c2542e010301c0b040c2140704079103003100c103800107444000d04803000e006141800c44d4402400b5416a0317007840c442c1c0742107600c100c85500091101e1802c0c0e100c00340300d84203400028140e101c003c500c40c110300e80d0203481d0401503400c5508104c9a074100281c2c440e058402800f006800301a21041e40141803000f100e9503400b100705070700c2c0034142c0d405a0070801c01d020041039000f907a00041002c4404590f0503181031409502900c001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 465767482 1250 465766232 465766243
    0x1401050a20060a0509070e090a030c0c0e040b0f01050603041203050c0c01020c030409060f0e070807030e030d05070e0303090114030c07051b0102071d06010c050c0303220503150c0c 79
    0x1079940e44922020080c1540c0c1c5a400345010b422814201c9005a94072083d44400480071122042d8641240d1215000030303000d0039440c0e03104c51145042644141e00c8400310318806004031000e6844106103824041d00441391003000380984400e944507480e518160f00c40030722100e0465910740400d82e58100140b1078401d60b4094416400603440295601c501020b102c0d6940d412034010400709c249030101c0006c1c00c90300418850200e070394a5001008568480d4010f80d840c0c00c000340808180341d00da0031400620b04040c8010490003c022100040c0350a05100042c46409e500a015000ea0720400060040da030b0040100e0144600220150ba52943c8401c40d020135030103a0600188180704a980039020799222106041c2e040e4020303800c5a02240d5581030240040391041c811b40301242c1c0f10b0001c20146e5100c1c00001810602503000c076503070750345c034140420b1843d40200400c600d0000001a00c2440c18209500040200011001002c032000400501c5600600103090440038490010f040a00c01500340315 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 465768732 1250 465767482 465767537
    0xe1504120615050f03070303030203060103021908070228020f030f010c0c0302160608010b03040309030512180316170a12050a02160e010b0f090406090905071401050a 73
    0x4560030160203840e0000241c0790a00c012004074240e6a03021a05080031200030091100050041030300b41e1641d103081d0001d41c005070181d41059000c00002181c240c8039464910984c0041c1c1e81d4440c103103844440242840c8054a02d441c548099440c1c00354101204410801410f80484e9050110404200041c0c50100d1000349904e0315420100100041d44c2c01c0440980454060340075510418629506044503503000e0180c180403174a980e0040c807181c000390b0042c6921034842e06003882c1c1180c40e510b47c2407901c0303c1168400056840007801812120311000310703d0300901e05a0080c003060224800c44413000425016582d540d0114034010701041c00200180c000940c0c1014043d03a040051080041460348400380c24400b61140300d0010300e49480c9142003400b212a030304a0400940d0901c0110102640983c0fa60b0030920414030007030b04e407a5541d101d000000c00e03655030000703580031440c9491802c100595100c10103540b0305c01d5000380b81e80d80100440e01400e45600e003440702103034204504144c8428090 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 465769982 1250 465768732 465768749
    0x6120605062709040b1801020909041205090901030c15020102090d060915060b0d181101080a060e0901090219030507031b080307060f1505010210020c0708060411010f0e010e1504 78
    0xf0920040c85080d410181c050317200b80e00c0c01000d6001800d83c1d01d09031700c18500c0a90b004a010000200880d052606441034183c080c0703410f81c6400800800584110001e80065965040b0786e501044001e0707442d540c250075145140004e6040c50b840100160207644410009800c00c0d4030b480d005002c00c0341e200340306038282d034280c101001200c2e101d00d410f41ca581c00442c0c400c1c0900c1d18003441c2070020468110890003242d030294101c00301410010044031846005400c40c10340a848100c0450704056400c42144104002400000e40880c40d00400c40c114000701c0d0118610f6100c00814408160081741c00340a50b600009440d40c40c215040c100300034030302154070007515400042020b0040001a80102510b01c040c840244403030100d4108000019001d403141c603015174800940402c00381440d1300a02000c1c101d00050301c42c05613803006450300b07290084404075482101484252807568000061781082c805500c0e007802d110324034400103451800c070b0800355440380c2d003c5901810442414821076026281c1c03003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 465771232 1250 465769982 465769999
    0x1803130b040509010b0711131107050a05150403050a03090206121e0c0405031504150c080a050a0203060d031d040c200c011b060603050610061206050627 67
    0x20116030929030828001d0a1140b14107600000341103d0301420b44800310740103c410801c0e0400300302000403516030801d44c5906039031540e407150710804a000140c120076000e20064603500d81c582c40d00c2c6040107a03c1010132000d000c03010600020030b038044161043e00c5020300b0005041d20480c00091150f009865500b0309402d980b80806c09403924080c01c2c8003103503c64400d140c00c0c54803500c0100d18540528056941c040d071003081004640310042c44210741050061220f000040310801c03981c0142c0b10039400d02404180d1103400d200d0094042c3c400c050b0f01c808211401c500318104840001c618400e0719401600300010344d0050408452000040d0004e848010020058940705000151012440700c80300301740c503211162070041c0c056001c500564200d805a5400345640c41d8031058040501c2025020781c0c41c01c3d66520040000f1700b003040824033454411a07518452480c04000421800d481d00c140c40c0600e08040c002c000316103940050390180312845200c64001c109a00f45ca40301044680000ba42c00b580f10b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 465772482 1250 465771232 465771239
    0xc040b03070f120b090705160204050c030601140414060702012c0f06030402030703170d0905100e1507051b070f030203070f06080f0c190206220506180313 68
    0x4a402480d03404a4480140800310040383d0b0044070350020240d41c00078141c2c000542014411001007903006c2c6541755414090b402500032508a8108403540b040e950310010600899607048168190346c22200c01d03005281c0b5080c46000e17103103d02580c60003030042101041071f0045a028207800160401180301101c2e180c001c3c150f04148132001c83e401c0a009110807450880c07903040c90004c40c0d1085401230300a0500f81e01c0d541c0c1d1110705225007005074041340c4081c1b2541c119047d143c020f04914030700070340080403a02013080d100d038120385081c81000b00c0b9604c90010200e8820020b410b49900100505000d9155491500d080001707a244d0900c011203030103500400b064480981500109482c02502161811038962508540d840d10500814001c01c0c8400700103200e1071002039071550300880c1103501c6400e00c0e4030395840442c5c06c1c214411032000350308040d080122508503440d030030340b1803201e50b050b01c010071410340c8920b904c0790307005842c00313442112100e0440b0b079500c01001291191211240c5080e0300558 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 465773732 1250 465772482 465772487
    0xf0206070605070e1918021905091c02031009290118060605041208040b0d05150405011805060a030812010602010f050408090409111c03170705030f0c040b0307 70
    0x400f1207520010402c011450350450800d9485040781d81e034072941c2c0130641400c1024003910721030948420131a00d0f800f084000c030102c040f130031800075140e0310b0380791182c81d00d03140300400403c0d9407048c01400b40c0541c0b40c42580c0c05a6800901c44200f6000c03254005600b4403142001000c00c09801a17584118902d20780481450300c41c6043e0324101c0741e00b8071001343c0441d0540c40001c103591407880b6610004500380000d2004d0145003540d540b036035106000300d85c9416992140c41a00d608400c0f012a1201d80d034108118003040b040740c00c07111203501180c041100758100070302203405003007220008000559a000049045d00c4e4072000e1405550000ca915031079180e444614083c2510902440e0015402c0c86075042810940c1e000701802203511001c45400d148581c0280030041207005403d6417026a1100c507680341d5100d20710300940242d0041400c818a614a003030281019200c180000c0310441514208040180e1000a8035041018100114456111404042c42d54080d9411094607441c0000600030746c40e4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 465774982 1250 465773732 465773741
    0x5040302030f06040309030206030903120109020c0d0f1d0d0f050a03170118052a3109020708040e0a020d050c0703020703031218110114040317070f02060706 69
    0x28030840c1100c00100b401d018241d120002500c005000c03500381c036070500c014a000400b031580180d5213001c4070700300704841c404000300d0003003030740410255a4005840e6495150a0081604e054854140707440b1320980100014249000f0945915461170104c101d400c1355a0b074040341000c1c440e0050f80e00034040c940781c02c2c11500d030000c995048010482c012184032425246410107070403103001c180c41103031250402480c0806060000c018140350f03c1c000c55001c50048040c4000201d0194240ea0035840d0b1020341c40c40e4010004604c0d6580345007105001e1602920316600360721080d0340d00d602001d83c9480300c074500a0040d02813604a0468000013008001c40c080e0139501500442c100f11030240301c00d0710b60091126003481800c00c041c005030002c0a09001190007402d111495103002e02d40024120019100860b80c840a49012151070001540c081080d40c0c0c00300c0b21080c025019076015181524603929841c0d0340c045a4000304400b070010a103031060000c4140c44210150b00a0240c0b03a4645040c0742100c01013 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 465776232 1250 465774982 465774989
    0xe10020313270207121e0203120402040204081501030b01170c0f0a12060e07060912030809070f030311060f09071203020a0206071103071e050103091103010608030a0e030d0804020405180601060504 86
    0x20386c00350b5044101560030b19019224515a005185460052400210842c45c01441aa002a000c000c00900c0e074804004100703114110b89400c1da0b445d415403404070310020044e03010344070307040c540c0d030f405203030f04d107000c46d08204251084031180c0b9400c40d80d4000c14007512407a03102401000e100c8100d1424030010350881e214130441c05c0150340200740c548070282e8003003400380030700c01008142800c03003c0001d000314070031074000004030200d448003580c0703086207072000006030400c90000c0c01c2e0741c020030406402000025084032162415900300d1803c2c1c816550f031a0340300d00c142440201c1120451060500a1203c0340d5441d4010713240541e100d00b603041c0041c1c2c0228848689009106141000554460811050003803d0340303070039041103052400c00110068207200741c007900c3c0081c04006203c01958244145402890904041c0da101c05036450301410518071015110300030380003c3d02a000c1c2c80d40c08000c895200341d04403030009854854080c00d4400c2481d413100048107105400020621035048805007044 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 465777482 1250 465776232 465776237
    0x190507030606080a05300313150209030705040e19140109030c1103062e081912080105060316050d06090609060b0c0d0806010c06020a0e1002031327020712 68
    0xf004031b4501c0c0b4050000710024580d02020400641c01c55005040007c2d0b8201002c182c105003d6421501c600e1a4010348071030a462041d8001255034440c103092100c10b0061400b1a4104070407400e407002d142c0c03180e5260400e900843c08900c8038900300f02c01e980d590144110000000c2201e1001c0d842e01601e0118800403d4445070260720b1020f82c0c500d0001241441062034140f21f5030807010fa015082001d070000201d80262031102d0b14081808441000890700b4254034552040802019003008420396200c4604030040022450051215440d0038089030741081260900e800c041c80d00c2001112a07000d640232134a50f060501c0c0300000da102094020005685034400b0401c056541e4003c0810580724503d4400202c5d000003174000004c40c01100b045030300c408181001c1268003095a074100484e44080040c0c00490a520034846440c00c000c10fa400402c080380c002940760845a00c15400c03024040e100c0c4c40302591000b4840030140000e140c01080003144114207540300c030b030716150407074242c004000708100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 465778732 1250 465777482 465777493
    0xc02031b030a09090c021b010c05060406021801080c0a0c0f080d05180106180e01110c1605101d031006060914040b0105030705071b030506090618190507030606080a05 73
    0x5000001784907840507403213990010020490280351074000c035001c4402e040c1c144031200b042c160120f001130010341d10541c40741e10016501c5c00034200b010b20103442100800e0410443c042000103200340c0008840b95030480703040100440d1617900e003202509107c080700610700c00c000300c0c14021120b05900500d003d06800b9540d1600c04100351170311400c81d10144214243c2800303148880c44c07456881d6011010030b0388040d001060441c1d0400316070650340d0180d40d80103c80e5214076140200103415900725006820304580c0c100c5903001c190b000030709034070118017012042107012a0896042da010008400c1c4000d40b8402413001c66910305026050042c0c5103c1d1396815030310020482d88510b043d101d0129402e00503110b903401e540b03a41c00101c0e4a500024400c0b42d52a111041004090510949400085100d980100b030383e8540701640c1424820043c20484403269400c05c1d000401c0d4011840088502e00807620700c51100307903414070901e0b04803a80e0001e4101850003001142601d0b000c1202c00c01c0b54092000c40e42c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 465779982 1250 465778732 465778739
    0x30a1b080f180f180901060503030403051c0302090114130e07091d040b01060f020f070b0307030f05060f040c1403010807080f1b01050a05070c08031b01020315040c02031b030a09 78
    0x3e2294444103a03407024203c20981c03c4440044001c80d040090040001003241d11100030a2850303125800c01d4070191301c60020802c1c01013041ca120042407005240c00e41c00c0c08407032000a0101600d01b0032460180d40003246204409840702d005c1402002c41e82c00881313a50410800c06480c0c03510a0207000c00500309141d02244e0541c5c8014003500550784101c0303030b00b1030781e1900d44120f41301d48400c8561300460003040d1036030201c2281000701c000a884e10b5000310381e40c0d0a2501011701100c4a131100555914204801c0050703590301d0307030380d02c586403001582c0100ea091000b01080b102c22864601e44e0061407804800800d515a000681c2c8054511420460b0444c0d0040d0586554507404c44800103080c01022290702415481500507014071803035400c00c181809095234540c0c40001054108a00c15400031a04500051400440081c1502860021840c40c1082d25500b400d98a4480005004176100e600c0300030564400c20864107d12452200c015030040ca01c2c45080d180d034030070180030000850608020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 465781232 1250 465779982 465779989
    0x160803090f1203070e0d0f291b0307050d181119120c05030105071707050403170a09030203100504150b1e150c010504120c0302030a1b080f18 62
    0x40c0510b44a45011410350b642c40300202c2d01c28000e01d0b0015080121982140000381290306c070041c1d00c82c410201c1001b403101c05d203c5002410b004800030380e10440071505020b501e02c01c0404450016816004040c0d490380c07030b80030175107140c41418260b500c546c4c60a0303d01c54042034059400b10056200340e5410500503a250b00300700c0440300ea00070f021103c0300c0c40356041020030302040d80440319038455080a0741195460000038211502190340078045254a580225144c1e5000d43d19039002031913081c50f50400e070a54607940c03000c480540c4881e2003020009406101e0030b000d080d00700b00440d4001d003203d51286e901302c4004050403003a01d00316085030a41c10112022049800790000c3c0040103041f1318450480da000302100c4114040c55941c100b8694007071212a0801a0001c25085200f4000403c8904003803405403034403498131140c001041b41c1d542412001a0780801201e09103c42440c102c40700703011882e01880308051914005011186c0003440c4206100c0c0740740a080507040c0040f821003411080700a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 465782482 1250 465781232 465781243
    0x51f05010303140d06051e0a0b0f0a050f1b0709051e072304080d091a0a110f06010e060f030c0604090f060e0114031c2003160803090f 59
    0x6001c500c11403a61100f600c940405041c80c0841100046001980c0d80b0208a400000041e245044440284000014180303001442e0050103900c031317880e1400300c044040c141907018480010041160004d019600100c3c40825200610302003079011842002034400320b030f51000d0b184290180d4608110018201491840c440400786030078003101c00d41580d504604035440034044a50403141a40364108010010f0154082c00140803810010217128001007030141a261a91344454001064404041ca40d07283e501f003a41d1043c40203041450182080032201802c00b4040340300c0c4261840b45200000d91210448003017800b03030708295804428800c10405040c0c50300c1c003d111745c6821602c200402c20207014a54018242c80a040c2000a55140c5034410f1540e903410a90100010540120f83d00141b49000e010085e002690041c1c000d914404041014240080440d0050308058600703410340800c500500454084409220902000600d549410500c5400640310f2008521545400c01b4419000049 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 465783732 1250 465782482 465782489
    0x20c06130e011211010e0402070b0c040f0503010e030a1407140c040b0f01020d2610030204050601050c0c0d02220507090b070507140a05120c031b01081305010b0d051f0501 75
    0x1d941c1390340418600151860141d040105410540c20020040410804040b5a0081c4041c0000c141c1d1245011008a480721251700300304d10a07403402c008024204d05c00800c40e035900d241c030f080c900000d800a400019503030141850241c1640307002c00e8040d041d00c0c00880c4074600e6040844040024031a4403061106651031072512601503030081c0d03095104140280408015200314a500c0d01a000e00c00321a8201c200068a001134071740d030f01400034421031030203028517a4400800e00c0e100f4148004005415912540c02c46014001d4a411811005544030803281d0342e002c044400c21100c5040c041a504002400111008070004403898004a941010304046405250b0400c0c001d100c030500745070000604210b0040c010758001d2003803c0001d0340307071220707100000c206030402d015044560031682858140b03244480110b00002000d64040b105a8202902c1da0700001d01800f00720385100c05282c01401000b1f01442d299101c500640868104400051803c409032000754054a615018000b400c007039900c05e00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 465784982 1250 465783732 465783743
    0x601050316060c110604080a05071811030112030311070302061006050f1e070203011103010911030f2805090a0c0e0603190501150308071a06030c060a020c06130e0112 73
    0x100c0f440d0100304240710342e0380040300090586240550300c0e000c031494240205c0044070181c100440c00c02035100c01494200104840f090f050262040381c1d0104d8000b480140507440c8000351a503118420b151090b40003180d40580c95404a5407500181406503880b601101c3e00d00386040380c64008034071548200240d40b01018403000c1e945c06d0085440c0040407040c101c29442c0c514080a110040243c0d0702401104640c0b1101d80c110740da254113290241c0d00b5508c5070044d800c0800000c000303100c0c01400d06807000c1d600200d03030400038111211091380809002c10101c80e02c4e10325400c107400e00c4414a404500210341c50320400380002510741d01c117541d000256045940390b5245d000366a681c010010b00a0b6000c41c0315104200010f0602c80075241501429050b81065951f04d001143e0302c01007019001040ca12001511803108940c41d01d04e0000e692000140c1149000300000f0485500050007000000f0f0807000c001c080c540c0740c1001540e0714084413100d2040e6180b421400000052400001b4102c078a001d8200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 465786232 1250 465784982 465784997
    0x1e05041e0312020a152406090501120903050d05040303090606060206070e03060f0c0a0c0b07020c01030c020312071d0411031f030b0a050709180e0601060212040302092205060105031606 81
    0xd812002c01007002070446c03600303c01c0c28100b000620a46901070000f410842d12119003c0d41070400044c502000342000c01d800394a0301010002298002080d1800500b280c0404112903880d03141c00c50250100c100000d1006041c904086601e980106240e4801c80141e502e04c20360041c02c0301003554800c403d41d04040c2a00a01c0003007440290541e00900d2010b1035070400c039103d01050781d0350340c040c0c800468107800140c010391145d00c4c03d5a41030103848100e41051000b5418181c0384c4020003c100c0d00030700b5401c244149151001d035511100b1420480841e002001000a00e800500b0001756610486802c141c4015040d0340300044070354030290f20141c9801c0620301e0140c0d60380048842c010800502004140481c0d01320010b0210403403400701e032403440e90900c0414960a01004d051902406030400015500520a9030300c01e02c3c1130505030b50440c1d8045074006c0981d200c20958001805045079680c544461074403041d018480b0008190b03049401c203500726032101c00303a220500ca0644d101c0c02440c0004044 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 465787482 1250 465786232 465786263
    0x105181b0f12071202040521030c0f06070210270309090f06050a17030712030f06151403061c0c051c05060604020702130c030b0907110c030c011e05041e0312020a 71
    0x40803a5000c4212a00049034a0407440c00540c92901002f5044050103900042c100103010f58103001c004081c52003020240042c0051001044940009548009040d44800c50312018940705205160040012001c1000020080000d1501425041c000c0034090b4040c541c000442e02c0041e144031100d200304c20003075401c048440c2e0350301103091083c0c11081c0070542c8403d41a8492402e078440c20004244003036000c40c91503104400500182500c42c0c05079600322007481044070648580c1385c05040c0855420684481c0a0039142c5401d024180d03412182d00125440106440d030b0f030b005c44d060785c2504d00503401c0b18081e96a10701000300382c1c400c3d003000035002144084079181c040099001a4010001400d02164070058540410b007d19812559140010588001200c00442c103204044034090280c0207401c2641c0c00b0000a0801002c00d0505814440040042c0424070311410030745010b40168842c4400b060000c10710400c83d00010700040c0c0d80f11280c00d400103504e500001c0d61001565000c10b00d884800c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 465788732 1250 465787482 465787519
    0x6090e160f050d020f0d02030a052505210c0406110105060d080c010b030109060b0117010b070215040b07110f090411040203090c030102210105181b0f120712020405 72
    0xf05101c040c495400f8420819a0315080d401342c00c500010040c010b8030b0b85810907030b4100380c2e800038001c54818071802c0c40f0b41c440b4088031401d204c0301c50001d044c40e036641d0b229840c2140710b0810006d10b03200d10180440c00e00495002e4400104111149940e54100b40503580b4a5a07089407401d4580e0340e0300505d40c1120f200010b94240c050319560348501c0000540041c80d801003800e54130b0000c01290025600c00200c513035980c0005403146480e80d0411980c14a6041200356017461103031060203442001d484840356448241f0f14122000382101c42d880d1510745629103001c80001194180540c0b1424006070180b82500b01141c225100350380140c0d02c0c03444c8142180a10000394030160100c45540211400d84005490034001002c046004204000b800020b01d4104030500e00c0603007000d80300e0b036456400d42c000c82064080640c2c00a02001800c60a03500003100703020705128420030030302506000719071400302e44844d240302c0b88103030825140d000c100d11052560b10124400c500a403580814298281c00d074025 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 465789982 1250 465788732 465788737
    0x6130f031a011508070e0603040b180307030e0d05010b030f0609060c160215090a060e0f040920030c0a24030606021207060f060e01140d11190f06090e160f05 69
    0x40300d070906c1b0000802017800705a55500440d030030b44070040050140548403080101411000010801443c1001d000340d400030200e0031223046c030070b01c00c00072054a2024014207500100c0300440041c21030b0400e0300d0480c0010346940080700e940101d402850009030081c030502e0304455101551000c160b002c28410340c200130b11802401011511340e00144880240380e21020b603100c02811441c0c41d0503490b04500d40c1044095480c0340805405642866050300c0020344000745156034407414800c60f403001c81c8000200c3d03c0c00b4021071340154418200036000038004048540520b245240041200c0c030b02c12a0a8180c09880e6180700381401a44400c01c20802800140302614000f0310602c3c0100743d260140c5104c406540b400c3d000040e4010102c4010008080703000c0032004003280540c0d0f42170741d01e981d94580700c2c0c401000c110058000d005d900401ba2400001070a003038003900f100b50310154501d407141402421101c0300d0144c040061421070102d20240f8001030703403440c4200035968401410f00e03405803c59064 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 465791232 1250 465789982 465789991
    0x2102090904080a090806100302150f0307052107080405190209072f0f06070c1e050c03060c0901030e150406020c030f0d051006080603070306050606130f031a011508 72
    0x704911301254098041c0080c1e8000d5202c1e4155225680c00d500400170722072101c004952040400b080f800160f805a2000c0e01c3d0300c120300d400d00c41c2d2034a580c10b8000580c0c41051070900d01c105640d80030000b59940000b04c4901542c059000c0301c200181d8a8008907000f03a5280020b50300034491800a0441c030b108884d125a554070b14851980e08104900580d1400c0300d00400305640303504a070401c10480c000400c03400303900642c02d107004c90106075103458850342804c1c0a40034658200c400954403042c08420000b40b000110050201c41c1589400c020000700381c1c0182181c0760009003440c65812242e44001801204514900124021030700c42d559050001e5208075a0300000340030a101c01c2d440c08400c0005014140d4240d4804205440c1000100341d0054250f0007400a000d494810b10160b41c40010b00702040c1c0354071020009680d00c584c07000030114040d901c281c9a280a81480c0850011700d0b6612110483e40328800300e0030492344003a44150014003d0140700c500c1040ca2138002da0081c8101c1c800d5810 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 465792482 1250 465791232 465791237
    0x40b030106030c030b06011e0503040206090409050a03110c01032a02011b0504060201050a1a0d0519140c03010e060f0613110c0709020c0d031512032102090904080a 72
    0x100307aa039502e054000c3c02940c41521107205038001c0210325600722102804004148400d5100d0010b044006072103800302600190040202084c40303032443c3c50783e0f817040c8021504081101d29540300e600d4005e1600c4503820413000c8a01610183d110300b075010340500492162910b02c034900c1103044440181d6044000030341c0204540d200d64002d0240c0800703400c128403186241d91007640d55810000040c2c04c0d900f015207100701607480c04645455402c0034543c5060207110854001c0d000d2292030a10a103000080ca0512880c16443e94109080003081200c0344c3e105580482901d900740102020903080302e61889a407100741d041100011000000c041c03503a64440c100030a01407060b0a0b4046003411a0542c111500c003117080054120030b20141004044000c08a010041d40b42400c503003061900d49094107107901c189901c0301c40041c4c0e119000e40c4802c018064050741003a0224540c01c0042041d40f80116449800e459001c2031200c0045034001c40e103081c28050100802030300c0720380d00c0c601154081141e1104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 465793732 1250 465792482 465792491
    0x1110901140909070f020d02070b04180f0e030406030605090f040206250f020405060d080f0d0603050f0102071704080304031101121a010219120c0c030609080703081f05040b0301 78
    0x2d1559070405144c0c0518141d588480081712110ba000c0c2c0750003040f951042c19948a9042003200700c0e20035040305c080d030383c1c00030b01418546030b0301c100b40780501100c40550308540d060052400c4c003088004042c00c2151429a4144015540c900c20700c44c825000341e81500e483c080003030019001d41403c0340281200100c900e951050810a03001c03011440403e40000c580380e43c605c503150300275850a0300038141c000c0c40c111072119010704669216490707442803400040300c10401188104510545900090045400c80c00740c815045402c00d41500070350141104580c40100903404005184103075050700c0a50301440d00951610b400d589602014040c5180001d0402c00c9051403011210340500800d032403901000c82c0000300c040a02c3c00a8188100300d690036408007003e44080000c601d414010340132401c1c11307041142c44030009003400c10380c042d490340001c0c3c03005041034804020001030900034403107940a50b503240100c1e01c40c00d0f104510320400002007134041741024014400761800b81d0012450b010010f00014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 465794982 1250 465793732 465793747
    0x5070c0e0f060a080c101206050307030b071b110105070f021804050111130e0c0f07120807110c15041a0408150610270e0403110111090114 61
    0x540c803000440781a41106003034014050709041c040320010280070503402401608015401080f0f085c00103a650a042100d4034502e020824101e0b4040405084090300341e540d843d840341400300007040700f40c5c1d60300002061411642104158401048022a40540d00b001300341d242800442d45908485000c0d02c04070300c0240701d07400594840c4040c00400d00c1540e0388840d030b4a45800e040d400c44103011200c1210080400000c100c0c818400c1c415425100c2e01580c050700f130345030244000120f008800304012162130010b0581c0a000302042c02641c654215540d03041541d4680408980c0c0c0c404130088443d0356400650305400d680740c07540880c030340101d420801e40e00b4203a40700e00503100c801c4400c05814011400013020700002c8001d010400a035001402100f9450900c04c01180e003010105500000704076030710700500c0540c520a5800f45011b400d000900318601d84417030b01c00202132000e0700c0450106114001c0c605650f5010700888007000d81804410341011114001550b00419085907a100c031801080760a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 465796232 1250 465794982 465794999
    0x40809040911030c1206011e0b070302160603020f1b10231506030c0a0309061d0709020408060f0c070c09060509071e0e01021507020a03200a08090f042a030b030d05070c 74
    0x900c0c0c004c0c00cc1e4010300202801c184440002003058000c10205401044208550180d800c12a80d400c0c1103171407040b1401501c861000e09022112242c110101d0078120f038032180d251fa03904001f803000000c600c03803041c9032151500c0707000741e41c0d004c420b468014009000180c3c041090a01610b154402070030b0115018900f56285402c4480300f0f03136014840b6001c0e40d94040000810840c0c2006031220780c0d8114502418001c0d101d0765a60010051840c0700c28410000b200004031a0681c1d41056000c00f0841e291510345c01c403a0003030300c0d0500070603006401010000b5025032240c036175401030782203d0f9002c5000356800303242191196201010307a419403003400b43c142c00030245981500d1056246030b0103800040b401c0d1a00804845c3c070441a0304000502100300400c49001241c1c20110710750054078207554424000c04100b401e040b0103405d662151512040c0406c0c2030a01200c50810041d2003140c50350026080b030160121303540030b11900e42603800b0914034440f9030b010380300030141e0900903403800b2400c1e030b1b803007420 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 465797482 1250 465796232 465796237
    0x506180d030f15152c190906030b1e160f0e0904150c020a0c05010e13051e060414010e040204021c022a03070308040809040911030c1206011e0b 63
    0x3140c01411345903100d0602030340900355410584940b113140320541c4540140350030070f0366441e81c0644511594040c5441d4500655050001082e402106016455a9040c20810745000315000c41c80714104102e81408034100345c0106100d03d500394802802c511613088100c0e07552034130440010a11441031500880b5a4034036408a10a52141a034030210300080200c400647d40d1146107042075521950014000401c4440000156982817801e0300c546241080055070040ba02101c0f6140350346040c082c070100089943c0c852020700401e00c680341070350b1504402d200880d100313006401404496100103010b0a115200072a802c64001400942084401555a0074403082c210300c61120302c4c1d000072590460004204420381609002c13180c01784103000c03240030945030310aa8900404100d01180040c040003443d8080c0c0b10b0358000944100800c0e40c070b6142102d501c10041a02c5486407241c0800b010403440c0c00d2410100c0055288081e04444e480c001c030700803007010358000f410550009900081140c0d250701c0701 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 465798732 1250 465797482 465797489
    0x21207021f03021b03030604150501050a0327050d0801051c0f05010b0604230d0b0604020d141608090105040309030f050102090319120306080601050d0809030d05070506180d030f15 79
    0x85c1d5900d00b40078041008032402281d0500031005043c0d820040f42e07030404180e500e8401181408603031010740700080031118103c100c907001c484000700d0442050001c005071094410a0989551140d40d0f225400c001100324a2040c01606d4280002c06000081c40900c105d44040e20910003c60344002c07100000f0b03219045070300700b024894900034030b00d01e60404c4d2510362007044406848000207043e503a00c6584e01000000e124030700954000070000d1340c412460f407000302d841d04940c2a11460b41099800032002401550928001030300340004034154071410700c5070601569068840095840c40c540d5595803900d41c00c030040c0c900b554240084a1992414800419440801d1102c2c003001040c034684490541d0500051000b05032504005000502c2d0014405054400488001100f01e10902d060f14407441003c1040b0340501641003283c844541060140c04d20900c03e00668055a40c1c03880c44603580c2c9070070865140258004940704072864000c0d8001c0348022901c86000c0f83c8030841000c3d8812007030b1a030b407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 465799982 1250 465798732 465798787
    0x90501290909010918020a0311010f1e030b060706020d09380c130923040c050409020619020f0715080f07031416021207021f0302 57
    0x50024080300005051a035440c20409006400c1c5004500818000c80e014003e40300140e50314030105807441042c140d030100481d4020070f00401d42d0786030300c0c000b150340001d2102a40400d000c07101c11082c25015510504a10f840a41442031602c00001d04401414070360081c01e070045010041c600205086000429120a5585010560543c0d52034444d110402092180b01401902c00c0440c2c5030b2258500301c2005841184a000526240e4a0540007a40308040c14015840e038201d9001071944425040100c018403185005c40407000210010110b2080444009000552451082c0301034038250340b100348124000b030302d000e051448040b189914182d0b000881005603019000c1246085400c10000300500110180310500160045000c3c1561101404c1210001420000184a00e11a03405500b0359014503602c10760740d0404401c0050814405030304a40117004030f02206e0034401c01c800403958003543c0a050542ca4045120301061805e0303070511113104140c4c0820510507d070401c1c0cbd8071469500150b1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 465801232 1250 465799982 465800009
    0x709030c080f07060302120f04080c0a26030702100513060606031d010c171e04030503010305011109100e120105071107050f10050d0605060a030509060624070c090501 73
    0x809600780760003a181d000c002014010042c0d88104211f019070b0a070041c030040c000108689440c07408903242d01030764a07080d04602c2000d4014080c0625911a51228010440c1c00d541140b00c003180c3d0400b910040300e40101682c032000f9a9404809603030702c000d80c40050b081400700c0c800c0c40c695405094030566842600083d45620f43d042001d80e000642d0081482a40000c01075041040d0000e4005441d418a006040c041e28000807824003a0801d20b6254104074220f661161070240f4000d8801d4000380415600d5601e000008101d03952100101c605a40009140c4501d01c0d00103942100c1640e490038032035401030030201c1d1984a80c0000d0107143d014520684448071021315008036103180c28540e50001d80310308040102d0ba465034440e80494480c2c06440d141503650340c00001c0714040500500da00c1b40d90000700001c0c02071804e550660201e03020306c100340240c0d0388a880e03030020042c0d049102040b1035100807d0a0b411040c1045200003043ca1905c52600c54105d240d0b1501440106d840c03d900000f5020001e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 465802482 1250 465801232 465801253
    0x803070305070309021f05040302042c0d17040f06050c04051002120706091704081b0907020d030e160f060e0604030b01030210030e010e011506020a0203030d02030709030c08 76
    0x50140719440003052808100c5150260001020a04c880100c40000000701650083d000c1c131410488018580161040c000d59a1545e0a11340b030000c0c0402a030704402c0c10703d00944050034003148000e01155690349140414103a41c2142c0020301d0054002c403880c0310081800000140c09024480c4100d0500e000c1644440c0342c54103015680c20016a03034011034003d140f80300403581e2450191034105801003c0010a070025241c241e0511040402403012000c0100c1c000882490000c4d045050f04d0a40d440413141007135040074401160025580113002da08a81803a5035154406d40c041206503200100300d90f000d42c06010481c089480030b17040040c40303030001c1000307100040d0802d00389d2414100594080d4545480c40d01d4659041c0c4c3c042c04020701c616011004ea40080744030390080c9185103074280080045105c1c54070b0450003441e24105c0c440000d01614800280707a400820035201213034028026529000d00d030310310b250007540000c3c60f403000d110040c107010011407412000f42e0040c0883c8001440d58814 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 465803732 1250 465802482 465802487
    0x30a0207022e052701020c0d0c060e090903030403180f06050304020405090c030303040602090a0e24030c0f0d0c030506040b013b040c09021c0f091109071b080307 71
    0x242d105500081c41070800000114282d0520001d0060ba509124542e030748404800403820315402d2210303130341d00914203c50384007888010100131040350380d00d8940480c17005801092100c503c0d02103c0841c0150018800500442c0c0590007002c40d074044841c914078250b840d440e11034468102c40e0040e400164000c0100011800d007446410341214001c00100319880d10780d000255207120042c0014030f029004070340a40207880f00560803001d0401c0c240007101914080241e103900841c011a030003a084080c0180440700c0c1404107159492090161484030248040800d00c240408060030484400451140c00800b0a4041c0080c030b010f10b00c11420601036500d442c13184402a58004080f008014080c03800c940603100c03c00c042c1c0000e100d0345800c0240c0d036031503041005e9040010b90100b05010700001d034401040c000c8106184034950642404c100d02810034188000309d461910006000488840c02c8000500d082c1c1c40c2c081d13112445151454074101c003100154031120f03900c001124503480200c01e0000458 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 465804982 1250 465803732 465803809
    0x603050102031519050a172a03102702120d020a1208070c020d05031204080d150b0d050910090605010306110c10020d02130b0406081e0c030a020702 65
    0x809920000c2600c60801001694610047c07103143c410403010100403481f64002d10034000005e02010f01c0c00c090341030241c2d800d41800848182e07503110340103640c1280350040f402e20801189400c0200024402c080140d1111501c1d0381001c816640910f50345030250040e4000c001aa41c260110340c040e10841d241c91400380c3c0601603844541c4c09100c5010104080c80e81d110700010a8260100e0b1410742c0310303650342001411803150b007030b0502c2503090480401043c010700300028000d8032103100341017141e00c5240a9481d8003c860f40103141d10300404005450405010760001c03600084410f05440c103907036185030204103c8140f40070132105603458034010028403005100b00f100004005100078540041c003210f60303403038440c01a41d03007484c145e010030032200f2519142d05540300140c003040c90401c4075032034071741410309900980308003000140000c0000703a400d1f6203030707402411021340b03020894040d0b2541440b070503680c2c200421406059900f40615005642d0740e003a507120707100c01f44c0c1c49120714000c282c20804064 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 465806232 1250 465804982 465805009
    0x417070c140a05040218090108120f0d0f0c0c120203090102210c0304090b04061a0306240406021b1c1e02091302040b090705090409020a09150f0807150c0606030501020315 75
    0x5412000452181303c582201f0bc07059411001240e40d9140309032000180209044c00400c12090319080c00407905641019107650003a00070800d45816240103c01240d680c80748002940c010b8004040d001414142d2030041115504404040da06051030024041d00e550007c0d80164610707074440085400c2401c1c01d00c0340070041d208001e00050b9404200c0c8e040d60803480042c116501600b1841c01300b84140341c1d248990816900c00c5440c49139103d41d1510001d643c0c00c08040310100604184a07602d90a29000c2480101c0440544454000c203c103516030401030b14400301200e901c084080300940c016590f0001c1030303110b0210481003919144140c01031008444000500034081c2d0000340c184a01c840d080010b4501c4070201300e0340456040103d20200b07491401c41e900c20805107051141e4006480c00300582c050070341e1b07241030380c1512803680e40014603920702081c071a0721045903038004804c07860b40c0306021040c1d40311702810000c11890380d203623070746403ca81c401c84080302c100000d0390a4490310300d40481c980040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 465807482 1250 465806232 465806249
    0x3070b0c07140c0a030803040219080109050f070608010506070309090903050403060b040c0504090207380c12010608060616110a0f1409090a1203050417070c140a050402180901 77
    0x1803c0c0040b011500e580c6150001070502203001c40020219900c0c084400a0503840d02c540441c603943e00da000c540039010032103080319503010710307486034180e52000681c0c2000c0b075003a950f0f49101a46440c0500c403ca5000030000d6003080343d160004980c104150141c4141c19110303680742c580d02c40ca142000d404070349000780000d02c0303142000140c4401662110550b425a07403402c01c0180d0f078030520b01d01200c04440402e500e402e40c0320003040c500a40d021010100d201c1503180f801c010b18560b100d81d0000224032034003283c061814801030060150714442c0800c0780e804000501028501980000b140d1060151316504a6103c0c0d6400581c0500b07090489840c8010306440071491600c40c10281c840b565500e4841c04140036001e10000a0543c2c40204144841e00780c00c8501d0031001207107581d006018010454094030080d01440b000e181000c0000c013201e00c1a41c10580e024181801e0010000307102001180c1558000103020020400d41e0700e0384005c014400f44034000060302030b948000d1001e203e805a0001d1721 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 465808732 1250 465807482 465807493
    0x18191203120b09010311030f19060608030309031804090f1b0f05030a1b030f05010b031908030609060a0801140108060702030a170712110306010806060c070e0903070b0c0714 76
    0x80c2e03100d80301c045045d654000101c4111640c01c40c04285004e0750104400600c0c07061b04800c42c01c0c240d40d401c0150305503009040030b000f43d503203a8452030340c0c03480301380e8203a407030f50740200440606210b030b51904c00c540441c01071011481203401c6c0ca4140c07240108420548041d03c013509130980c0a00b0f000061030043c0584000c00c2e4400785030400007900c0e1072040700050104102021045d82640814041c28090b650011031400150585e0401d68020100040c031300c1d029100d0400200440e03017090700501a010b501103091442c650b0744230144241d0007405407144d80c025660040c0800d00d0070080c054000c0220340041080703002d602d000409841c20710060503820941d002041032001703207079006281c848074480081c01a4829107954404841c100880025a44040d1501080c001e0002400000310700400b000d0707a4400d1161101d001b00a054803038001100590392040d44d08001d8410b801a0159004680340103490a00105440b01d82034200b085a135184030000c00a0668200010a0394422210310810014007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 465809982 1250 465808732 465808751
    0x40314010f0605011d010c0501020f0309030a0305010911090d030c052a0d0b010e0709030204020a0503150103060803031305031201081c0305070219050c030f0601050f060f1819120312 80
    0x3602c4040d21445c142c1041080c070b4400003801000d40440b80403110b01245240d803441c0002e1260344a810800030f00d40081d04220001500e01114041c441d004200425103d1030148079000304a00070b09503040890078400e503a00960086001440340740000c0e407201e1910104070329080310b240700912850b49440c1c8250328560300703c80400d4811103801d041d070700101440503403074076000401d598004007940020350003400000d00803541580070000c1e6005518080803507601c20756400040d000d4a4007030242d454075a02c18000200700b05071101d00c0d90406801349090747d1a1210852201c02950802d802100d0540d0281c0b104c5080811010041c0d800d0301301c146070410281c28000300003512811400000c041054a01da484030510100340012180e00a009046400e48039920300310a448810910070140305050388a2a0305080c2005400c40d003180140c1c540d00e03440c004048042c0c02074048405409900108106107121704112a0b10081021f00000d004810020302c003494002d0511144e42030703140b101c509141480 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 465811232 1250 465809982 465810017
    0x10f0515040e0c0a020f0304080703110301020304020d150207060e1e0a030801090b010e09160305070908030306270702010b030105070e0f01080c0c01180507050405040b1506040314010f060501 84
    0xba9002052200a107594074400d0308100e00d4038200f113411030b001d4003002034002035480c00014103008586c0f24072a9640c0405070a4105800c0f4041190f000e03400565074201c1c1000100d580065281d1141d00240050402196484400c120707800f01200c482c1c00d92103115040c0081b240b858031030441307141c500d0081820408980c1d00521204040c81039006540d1a5112100603078012608035803011000b401c0301002d440d10b41001407400c143c40f2000c4010900d0034011450755480399842805541d4150000d610b141c48000a0141c0a80454402d000914024200052805020700500e009900355400882c9801c460010942100c1000d0414000d00150b10f011224a0715064170200486509090405850742c0b05031720010244200c08043d445075103031211022040d07002c0000c40f01c086001c0c0007100c2115855030103002c12244161406000c0800350030018039601c030b01c540c50110408011f800d0070305040da01d5486560f001c4070700785071030500e0f5100c111f03503581c1034840c0c030802c4010a02440e00051440704c9002a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 465812482 1250 465811232 465811259
    0x8040309350a021e0109030b070302070c0f050d03110c0409080d0507090f031e050304080a110a0b1204030201090c030c090506040510210c1502070e01051f0215010f051504 75
    0x100d01240c1c4c40818a01c00d80c0292100402903401c5901345c01186001400100254032400e07044a45824144010400c9180350240d6000c0d690080c04180d00200c150b1001e65a40c6141d6100141c1c92042480d810f050351918001d4141c0c80307224401c110345480c1e900c3c2c1910207488d4010220750801410b0b00b41002032150742c002010450b604004250442c002030700802c3e00140d0a03105c0600300e880002400036a6440000f8020f17180c500a04201c1c0a80081c00100101c45003c1d11624120013401c1c01003a09140c0c2da06031180c0c00900c00e00001440c044195140441c0041c02e0780207450040b0403481c10800b6241a004140d031085080740c08000e0303490104000d24541d0028003585080e6401001c1107000c0c0c2041c10050903900750490b00010405a50f0f4800340f14403a01003088500501504a001480d036614119442c183c8030300612209549001c2c00c2080f00d1906036489800c110300c03601c0340c1c4032104003e0380d1216020340880c00001c210141481c0a00902c0b141c00c1640c1300a88004200401c0141c841058 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 465813732 1250 465812482 465812509
    0x80c10050d021e091519141b060a060603140403180e0a050411060403050a1b09150503070b09220b060307080402030c0f010804020108040309350a02 65
    0x108203880303007840c410501c0240210908003e03d0b1060514240c83d240764800600380a19088035080e007030041a042d6841c65004664500442044a40300c0880e01d5020b007640c01004240d0903041801c19100c518040d0101c1901250001142c11135410722217106401e00500f4040c1005080c144840389052503080d440301c10040c0040c041200013040c120300c09882c10790050060450118040f140d00b04540004010f0405031000c0b12043c2884480c00141e0a080041d1412243c00030054500d003007094035055600641c01062000200c00180c000c00c00e0284ca03c58038181d2180381005200b940d0a0006140c50a0007507007040e0a0301400744400e1400c5d0f9034010786c0146900350307000c41030035500020b4021005400d50f02243c5a000c00d0110400148030382c4801507902c10f90003202180e4a554900042c080604400100d1500143c142c0c0005000b550040d0049500b00d8481e2a000a0300c0d50b0310048028843e9214501d40c01140032600484010100e544d40702c004c1201c00c9010341462241079001500fa26034206 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 465814982 1250 465813732 465813737
    0x6010c12030b0121050901050f0f0106050901030b121f02180d0c03061410091a01050a0207050312070b0c12011e030f0303090506100620120a0203040e01080c10 70
    0x1401c00b106039110b04040c007161054400c818024030134100000025200c21164000f107580307403000098074004488039460113043c1c50703140361440d642049030032195070f03000c04031240c1410740f104103400c103540320141c81c41c4078012240040e01d0300c01806020212600e0303800ca404c44150b0f0040c40508480715030b90780c00300315428003100c00c1940000c191900180705401a40042c20b124600b030711450701c082c4030420303ca00c45c04512813502031301529511044111403100c04072144201804900d03001950146000b44405c14441c0101c80100c1d6460300064940400d0b8850f02007480b80200b940700800905d00050303034000e400703085120700300170380001640c000c890148501e842c2007203400424501d00c6084e041c440c010716001a041811042c3c0c50070050013030003035034108990f240301c2c0900007540b040b4541e042505441441d0f4455800020321107955900301c0641c4c01c680c0c018011070070b40e5423500404400074640398031150003550301c0c0c40c54a80d880304480e105a102c1d0b0702c00d40000060b12241c0e5190301c0100100811030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 465816232 1250 465814982 465814991
    0x501140c0a0c050c220c0809100e0a0b04081c06030c0b070812090d030b01080108190c08030c0d0906020c030c040b1813030e1012020a0509060c10050c16110f03160e06010c1203 77
    0xe0880cac514212140f00d001d0700d6285580c1c1400144206080203142103da0790b00190301854001d0403a400326503c0d032201410491810f4000d02000600740014100f140c010049d00d400c02081d214546000c0e0300946007240c10b98032074a075240d40640c140c0161320241c0d009081802807989050311260b00d4041c98000c40c10b0711901c480c19401080703003545400002d490440100c1c4d40380c130080c424095413003428242c2000800d1110a000030710302d10019503001c1032140500a0b08200c41c0000074040070b07205104042c0d80c000d86400130141401c2e020001036103c0c0581c020a01d021900a040280803030204260941c0505498180407844079044000d040081c040d80d40300603603403842000200d5250184822072a840800003601401c0c0400000364a8160840280104855102c80080e82071b24403841d15046400a810b058081c007107514000341208407070f00906946c081c2d0329854006030910786180007480016503424000c0c4050141004190f038410802e080950390340b01c00303840b1008204e548200d240d04051b01c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 465817482 1250 465816232 465816251
    0xa0b090f01021c0c0b010e071d130f020301091104030c060806030703122c0102070506130b0703121505010503040f02040b0a120501140c0a0c050c220c080910 69
    0x810403040f40010380c44a16079030304020310000302007010109040d42d005900304000720b503004d01b22180070300500141d112020110240103003100b6200b00301c420b2a03400031103509039500e034007682d02809032845070303641d80180d8a60400001804440070748a100004d16002e000030310024100c614594141c03400d904101307041c1d6503038200280c0303005001d03007000300318100d90072200c80400d8221272002180d40070403007158041e244100d00030b00505845041e090069000d40c104002e81d00300007000b0204200000c0000c081c80303440e2803035007040382c0c0482c90403000580c046d4200e5008580070301c21081108400910842202d00d0300e0300003400c5000280c000f604c002d04500784a01155216130150010740c1d4058008407140303644031040b14000c46002c10546481d420b007451107103010a8001c000340316070a191a000d0824a070035400f01c5080500640403900c0d4411400d1303400325036541d01d9503100d44400d904041620449020b080c074080d151440c00c200c0500c41e8034001e000300018082055820188050300000d0340340718 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 465818732 1250 465817482 465817487
    0x201080c090409140f0d0207050609031608030702030d0203091014090d030224010b0a03050c0f040308070c050415051c02090a020a08090a121d130501030b01050a0b090f01 75
    0x203000300c102d50062412011608002100c00180e080c94003400564003192101c0c04459242e4106501160041c0c0000d4414002860300f50050851010090200c640d0400212000c15010002ea0032809160703001003403d008501d02001710000c1003480340f000d58140031040003c50440c00070410160140a6035081161074407074140300352610424001c11604080c0c06905020752640c0c40800d443c0d01c10751000a07040482110040541c0c101c0d04446502807804081c20307411801004060101d0005000400c42c2110b400042c2c000b07403024501411450f5950400da18081d0303c1800b0381c0d801070780036608000101030f40c1e50000d0180000c842085e11004401c1003611394644080481010081d441081c01040c4140014240c2c043c01103001162200d620715110516034941d112403600f00200a0000101c1550b0168800d0640c0d08410080c2040010250818000030f092841e480c00d0052041d6135990042080c0400d20003058010401640c201a07040d0508541604a01c82c0d01c1d00d481c0140201803c940c02c076407 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 465819982 1250 465818732 465818737
    0x50904020d1113030312021602090402030f120d140105010e040c021606050c0c010207120609030c1e050601140310150902030c04080606150d0518100f110f070201080c 73
    0x300700c01036040d070b2518800b00d0745052400c1800140c0005691000f030080031b524910881d82010025481c400304182160700704601c0e004001c00c1207030503001c0d244a00e0a42c0c1020070600700890045e15030356803205510310070541240c03040718005100e004403100412072640c010000106404054402089900d14428103a10340300c081c4400078002d2920325000100745038020003a06d02c2442d14400e80b004000401c1c01242d071b4800c2c038060720b00407034400f240780e80c0050b820340d0081300e1007032082c100480d10b91800c0c1c8498401c00107400603115039007150701d40c1108100c001d0022602500c03808025007a240512408203030f0b240608100c214265503a20300e60a500c40302c0001807001005d03481e0066540340303020002200a600103204080451084c50701254251070198610501e5205602c0c440d81001c0140458001500c405080004000c00301d020f0200c00384030900000040002c0740c00d0100715090022a04011034904106444240e4800d0080d5107480d10f450f4101d4945640919200207035032101e1155503002e2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 465821232 1250 465819982 465820001
    0x20d0209060301110a020706021212010b1b1e0d0906050417010209030a0c05150a0e0d0609140304080f03030103021008060102100c120b061c051302090a051f0303050904020d 76
    0x4c0070110307064090b10b5000500a06440c4213500392800c4903054130710700c2918010002e4412465903d48014042d541000d0050142c10001e002c02e076254101801c042c0342410090303108110100d40314014954540e40401202c040c15242d440c045104a181500041141c004e80c0240440003010354148100e0351003d4041d1100003600a0907114600064075003015104144e2041c00d0081c04021030b080c010b051038005032450100f407600c81c8170030b80008404005110003002703030131a0120380d582140000f1030301e44280310356003100150045580720b040c404814502130040411034565807040005000580352000b0040c44405d00c0c1c101070265444d03101c0180d041c031008007481c440300303844e01c5c407100b40e040d502119203084003040e400c04018480740001400110f111700007407036000ea00b0645d034004404c405548050b60225024035051074410595000075a04030058031504d800d1a2241c05002c4c06002300d2200c40d800ea9400301818015618540d004ac0040c0603401045101d1a40807410680220f029009294503 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 465822482 1250 465821232 465821261
    0x1110f09031e03091f0f0f0c0b15030106061d010c0201090801020706060807090204081009020f062107090522020d240914010e130f030f0f1b06050c0909070206090f01050103020d0209060301 83
    0x34132b0108858003501c0d8032050302e10311940c240080000c0083c015600000078010a0122081d1010707000010b560000c2d8810089040010354030700001c01400030b101a24890f44120008100c140c41d1042113803906026801c00c040b8140704110800808000007000c1281d0281c081c004180754010f07000044c1103490f2803d0198007c440020500d07a8039207e10120401500e040d99071060b41e44511800315107100c0303680240794120402d0f1000c01c0d1148400100c001d03807145024405854105c50078400010f50f5141040c080051000108a820104100c081500502070504c002c01c0f03485000d00c800c152012040c442c0c148034880b0f038408903003501c000448030703103100d500306901c0c1c50514a1840c0042036102c4503800200016500414400c00d5031080723004c12169404c00016032200c501944800c40100405404890520010858900d0b00e4403808019032003802c558010300f0306480c00791461800d00b420300c00c888140d64504401400143c1d0b0300741c11030030031503016074280c401a0f03218800f0134010400134020106 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 465823732 1250 465822482 465822503
    0x5061207030308070306080604031b05010e07060c020108010515032805040807060b030c1020010c0201060e01120f0605061c0605071101110f09031e03091f0f0f0c 71
    0x82c50340240d1040d000308050b035400c000203547c404405407544c5c3d056130b0050000700700d01e00c0030541c508501903250f5018090400001ca5111f080010343c50035045510641c081980e0446a40640da00720111030700500d020751300d00e45070300b05c082400301d464800205191846d04181c0402405070010009222003000e0f0b01d0010411403c142c1400340040c3c00260044410a080141d1a480383c14003044600740740740c0107003544030410390300700c415501d0701d040915414402d1402c40c4168490300003400384280c002c60503000007030300c28149001c020301d2780d10580215039030041c4400324000007401c0c010340800b0180c00503800038440e2600030014100b44003461048085044860a55090160325880940142c03885c0d221800744208010b1214240c5c0c0b40324100a490032814442001c0614541c001410059401801d959a82200d0701a8080c0c2c0d0510707641d044a5940041600609410a8407001d06c0c41d2800c1111136040f11a889402008008189140d204010018030650400ca0060a1010182c0e40c07080390702c0d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 465824982 1250 465823732 465823739
    0xd0507050117090706390210050c0a0303050603011e0c0f02030423060d24080a080405100e06030c18010e060d0f1e0f0507090302090106050c100203070203030a0b0906030c0405061207 80
    0x200d00f412082c0c801d1780719920001c1e18480950091003181e800b0310010015154030302c5ca584cc2075004040003406160555210100c030056198000116494030201c0e0000040f40a07514130014481000950b038401958402c0006200002170441c0d865402005580040e0050248001042c40f40c040c0401488510342041c840300c28041030440c1c110140c03034211503c10109684e0388455a52050706232000782410000304424041c40c1400700340000075845604081c85010380721404941e440d48216614179005101140d00e4155901340241c603a0b8a6800f40f0b02003c42181c890001036541c0310f010407100320140c1d00c1c460344502280b1034001c0848111030100708655446892441c1c8003a00d442c2e0901d01001d4030300000290002d009001c140241d03a000742411115071b09241d82582c0301c1d80888560892449448680824030340580020b5100d099a0b60245441e400c00d0401301c803e40c3d00d0420031038441d00042041050300c3e10005050b01c1000d600b1207010484d40c0311000440d0820a941c009014180901000032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 465826232 1250 465824982 465825077
    0x203040309121110080c0f34030801120308010e0a1116021c1a181009020108090715030c030209122503210203090d0507050117090706 59
    0xc0103a10003130f14032040c0c121141c3c43c11125844122030303c00d00c203201480103160b03e0105502800c0110700e4611100c12078828400d444030a040c5d110200c40d21101c00d1402007040590011260b8010500100000d0400100303030b5025100f00014064050980300301c400250443e0059000700590320b1a480c070150341c410003105801220f86c1c0211050313002d50903601025400c0030320700b540d1205040e002406d800300a00a1038110038100c10281c41043c108031101b80c1400310070800e1280180140381746000068aa61500c000740c05084002c0c188005504408402c00c01c0440c0045140c1202d0301c54134000030f2103440c411007500240914601d41307401c81d040b0b2034130100005000038550103000c0d2420f0240030a0b00e25520891141101e07000042000488030b0320403070003007202d13408140e240c9c1440c01034a00301441040429440700e807045003a20b5a80c0200410415540c12460f4880051580c00a11000e03290900c05556214a50710500302045101221400302030628000601d513803840501940d040d06903200d12 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 465827338 1106 465826232 465826253
    0xe070b040503032d03100501140315121203040c05010306080f0a0201050a030e01151e06091203140c010603030905040b03150604060503011e2409020304030912 70
    0x2086011000139000e076100d1061346240410580c40c06000400c62401c0d603a0410031024100184651590a00e2207034048141c241c038280307080120011504e140805c0f1f04d4800d0b030142d4021040c1302c02c203d40e410b41181192002d03601841005d48030401c0d070344c4400301c00150f00990385c019410100194010f40140202d0025800c0001c0c190240d0115a400c2d00c1e10080703000c500c1e40e5480428080403c025880300644241c903403001c0e078501d0800401920104040c0100040c8031840484181010f2150304c1400049103802900c6899000c13080c407043c00b070b101c0d90100710085880302202082d43c0c1068450b4001c8000010014442d801004070240e44080300686481d0f00181c0310500400c85071400d000d4081644200141d050500d41904c0b01002201e910507940c01004104c084884a50f40600070710405448103c840180e40340c07128a401c1e5030307040c0b244c1d00045d41c90404803004020720101c4141d = true := by decide +kernel

theorem cover : BRFrame.Cov 465647482 465827338 := by
  have h0 := BRFrame.cov_init 465647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 465647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 465647482 ≤ n) (h2 : n < 465827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
