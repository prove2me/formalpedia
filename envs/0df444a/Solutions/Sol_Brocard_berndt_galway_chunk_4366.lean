-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4366
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:23:38.27157+00:00
-- url     : https://prove2.me/submissions/c7660490-b5ee-4010-8212-ee763a475284

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 785071942 ≤ n < 785251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 785073192 1250 785071942 785071999
    0x7020d110c010807031b031a040501080a03121d100b0118030201030b15040303021b090417030411100504030c152307020d0f1b062106091406 62
    0x9600c461441c503840c2d80300c0c0c6a0a0342c004a40d02e0302182e142d002406010026003103641c0e071000320b5125680110310072504042c0c150b00c0c0300111018000c0d540740c81607081d203c6240c1e002c003408020b03c044814070340000c660400b0740d0740161140f43c0c61103900300082c010b8072030402100f10f0b10914109888600c01d503100d078510001401491080080c094a07643c0103600a000320f03418a03130000d83c203401c0d0b401e1540411016000850080d00508004420301035008800742c0402c4078188036503801d01c02c1c040440c8040100156100e120400302da0b4135156030801961041440001070382c0f0080c40d05804000690003005002140c6c86042034030304580e1110340e000b5242c0024021a40068111480c10203608908035000e41e800845054040c07621003141c0206030010300e040d07829500d0000440400c001c0080b0310300112848405121501d14103410008003d0600c02e02c0507055200404c490049400c00219a120038010b0600300c0b8100300241624071000720114040b161244a0f030700176401e11445a0f8190100c0301d00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 785074442 1250 785073192 785073227
    0x9120306031203090303090209070206070824091503060c09130204080d0c17040906031505060306180c2d090103080712030216050a0b0606091f02030f0a0807020d 71
    0x80b11210012030007040c0700c41041e0101600ca0782c0700409a100da03184180610f10302cbe8050052854071800141c90004003801894804d1001c4075100b00308541d400505c801c1190440c2c03a03008540b01d440201d12000c02c076a21241e810300460b02400030704030081d002002040400d40715090b80c074902240403401c070b01443c81115980c2d0020b403805585d00d0312404821081904c904c0a40c140c80c5410074092500d5040b940000b02c507207a9441050052041c180072001103680d641906001074a407404c08692141000f4002000c05c03650040c0a00c641c82050142d617200000c003801c500c00140b0b03501d440300282415074070713181d0b19003040081015803800c0008259040c0e070740006000d032410100b40d40e1124200ea910f01d200080503400e1103030f900f035044400b10089400f4041c0e001400e01040350304000b40c065401810f45445120200320205035610703890310320000b0100c490a13180644955140030b03401c52042140a800e43c450002d086010617402c1032407030780a1380041d401c03120050310000055410281c184002c441 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 785075692 1250 785074442 785074463
    0x9020a050d021908060709092d020c01020724060e13050312180723150906070305040602120901050f0a0917010c021002040b03041e02130912030603 65
    0xc41c0c10034002031010244094505100700d02e82e000c850715084240c0d0000e03109034100d01c040c400800d0b0302c44da0f0040540342c200e00802441592001c855840716500b0340c2c4680740c021140340444030380700d9036054801c8048480c009541d910011b1801c40745980407644c040b0425082841d900d0305d904034070301c00d50007914100c6050000782c4d12903400350300301d0007070b0841c0440d142e210030411007170058002031003a4000d454040c0c032582900c480100050a040c000e0700620b990002d05c40c0d503144c08801000010f4070652044d10031401400d1000841398807845000070042d040200062402c04040c0d1007002001112030341e50030b030741a000c01d4180c41e0002d40310760600e00340094424021100410400e0000b081c1c11102c6040080c4a1640c40300c2d06040d4200075036004119035503074540d2150b003a03014410394608240007001149801c1c1420743c1601e071804060009446010407411400485152540c01c0212030340080c1050000707000c3d03200074400307003450450440d1540c0c02c42840d555080e00138010708090341d902c0203003584e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 785076942 1250 785075692 785075699
    0x306062c0f130602040816150201050910110f1b15041703070e180a1508120a180305030d060b0307091707030602180f0105040602120f120717090109020a 67
    0x415001410307900f076401d00d500300400104403400304040404000040302882c003c61030500c100707880300300400051095905050810141410204110242c0300075032a000038651410715984c0c1c042d010341d11030500c00340f45c0041e505200103000c18820160444900c11a00340d2078400704003024030035066400815060344039401d6244c0b0f034900c20141d5401a281c3c1f0f0010400c00d40b04000a141d041072804100c0c2c118804818030000592a0041a10380c1d543c044011001702c0c60100200d5070b0703030640c41c000d00d06c1541c08141c40341e80e01c0c0301e04526540c41c079403030340c0c000382044d16030130307e552203a0000300354038081e40c0303000b2002a0350204142075a102d602142c40790f04809241c050964811105084002e0b1203002c3c400d03003c000200309102601410f110444001c4a4042c0842070040c0d01d000d5a20036414044c00707100030001076500090341c0c03e40004140702e0a841c4e00a2029440060148400707040d00c801c2c11604004445074001a0f891440da900b00c556035150300c074082d00c2400c80d604103001075001039100d00d051 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 785078192 1250 785076942 785076961
    0x20a080a1a06041b0c2312030c0c12130e0105060d0507021e070f0e010e04060c0207180e060106090f0509090a06050f040302071a0a03090303060306062c0f 68
    0x4070b6010b0350180c400306035001100d440c0b080c0441c0c00d40311103000c514542080003d02484012080d0340700b03c43c494180585ca4500007444c2d45020902542d82c0445000001580300020141599550b031b0543c5c2c00c540d06016111900e403465080111301da44001c002074000101000800c4e440c5048480241185180110030704400000d424010301c83e405600c64100503110311410300003402c0b05000d000010700001421308100c0308810b001e035403101940b080c0c0c900060011118020f46244c1060388600c0007d000c40c15804203a050610550020142c582d0080c18150724002d40d4114006051403881500c0c0c03280c1c1c8071070068031410120301400701e0188000000340590f0800424990704200400b0440b0800300490b40d0f8542940c008880785100716544c1400e0204040c2c04000620182101c040840f0941d0a0366170840f0890160796240c600b019116200c0c0301c00e141c02030707101c680595000718042c4540c1da201c01007040e60120401c1c082c07200300042c5110a44601c502058030740640170441c20107000c4c0e1200d2204 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 785079442 1250 785078192 785078243
    0xa090501031505100c02040506060403020625020604031208060d0305040b0f1303051f0504050a060b0609030604052a13110d150512010b0306010510200a020a080a 71
    0x1007140e012000000400d05654441e00c81309101503079a140040c880c442d01c14403064420252240340103003400d00c0207000503928102030380c808280072300c2c02c1108200b22540f0a05410681c040c0a07402c0140040c010003840004400309202441c5515290703500c2e02d440c824010354890305180a03001860622050107600328034002013001a070031012840c240300001c48030590b400803a60048543e540a600740c0c099031008401c402154045540c801c001515254681c0713512500041c90060480d80e640380700358965910f00b000d8803c0d0080c0134080355801d146c90b1418940c1d8145041d44440c039424040401420410841284c0d20b0586d00603141d03011800464900c50041d1211082048808406004031011521035200f4008004002d421402d4101e26190911030020400361255150364104008641c0b182c90010704641114415110354070919032220049580b110381003405000398150803030105501c500014500c4c580780c005c0700d0700d50800e42d46e02191507070380071081001000c00242c094085900d00ea00c420 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 785080692 1250 785079442 785079461
    0x6032103091f06080d170f040804031203050703050c0a020a1203090f0602180604081506042705250b0304030c0c0b0d1407050906090402070f0b01080607050a09050103 73
    0xc8a0510b031400d11401d1420b95021542e0800301d0b5114420882c2c01000c2040445001c2c1e207042001c84c21800c01556000414002c0151011003a190085810400414212002103821043c110800b50803e10014081e0005075180b4000a04042c00f18440042000449050714441d03002441c4d40b5441360b8a04507514540ba0000c420f259407034180300e0208203030694146095205901c0103917941407a08401401c503d1039070301c2d24001d100900c81804131040016024038074400b00d02e041380ca0350b614400060050311444003a545003a0721801198404a035091074900c010344901c080e5844400c400f500041130401ea0444290b0a804203201040f024080c2c00c011500310b0701a1030845814041d54680400d00d01441d400b02001d80000101d24945404504c1140c0542c117000e0030b0520903041c0300200a005004181d4554803401e0b000582c280d441d41e560341107654980c0e0111085501080328105414103880c24800c82c2d0150045000240609109408807a548001d42d1142444541481700440c000c014000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 785081942 1250 785080692 785080711
    0x1062a020f03060c1b032127032701020715090506030f0a0b2e0c1527020d080a170c0c010b060f0301030f0c03140105060906032103 58
    0x40800e441620203002140c4103004d001d101c5680da81d144403144660010f0401214007540041c04101400d845010444003020b01d15400d000c0607445039040008030442c2800403900840460705000e80440d004009410390310705117554441031942c0c101142c1013100501900e10f0050300b08903414418241c8041107200003030924644204156103483c0424038a030700a0f034500c504a2491000c0101c071082d03d0040343c038501000d645141d060071081e0490f404906000c1d40310014549460303201c0e500075100b51504000c450b001941004c0041c1100b9910300240030000140e030116030303c0d2124800740c8010300700c4006d031240e001e802c40c1d10307a140070b4032401d40d20340211000c1c00800c407062020241c011803214001c0e020728030300b0050540d600c426050319801c46071028102070040e501842a087c110140b18180c074110381c0c02c0700e4154031440552401c5503014580780c0008055595280140041610551106110b040283c640d1111502c0310790030581d45a82d0b40307491514042c10214541c1e60700080d600552b070842c1051 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 785083192 1250 785081942 785081959
    0xf12030f070c052401080f0616020c0a090902030105061801030312110a0f0f0309050c040f0e030d05100f032a1a0702030105100b19210b0901062a02 65
    0xd540302804c240038201d40c140d81818012180003071100c0c180c202e9004002c400010102818000400380d2141c500420004900004100c1050064001d2140c0c071100d140c010700300850700c1d480c2c0c00d90368014030b1a2582030f4001c5d8039007400100703107040500c000d0426141c0d100d04801240e01e959800c5410881103810420442c1c0c58030320704c408541c4613001030541e0b0a0945c403400e41082d0201d00003040100c10511040402d0704200303032840441c001154041c4981410b45010500041610801020f070113448070a0384980320005268440c0c40080d03011a016900720491002d5003640c65004260303070304090001030844441c5005c104e0919401d18103288102c070724801241c09030f50343c4801851101e004e08600c0e041c550380000d00318085260038412140d208480034807000441e0306120454059010750715080c0d07812a05401c250364040d003d00c203022141c008a5140710b020f20f01000a030b41c060b00281d807030940204078040005c42c066000d4090780304801d5240555500c040554640d4070800c4003144011fa0300100383c2c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 785084442 1250 785083192 785083217
    0x21309060902090c03073504080c0303100f09021c020a0c0203030a110606090906010329010627060203090409020402040f0303080609090a02030c1e0d0606080f12030f07 74
    0x300f0710814819402000c2c0c03241c803031030701280141c11401c0074002c3c50500740c501401040010308080d11003d040034228082d00580d40c41e40381c00583c520500780840101d20010040103012101401e20009582c020504400b00d56510a042001e0b4014201e03440103056020500c044085510782c0a0715002c1c00b2860442c0394070768140c0110341076070300501c0c07210000f9400400c030b2100384008110440c1c12003070968104615150503464030780c83e9003040c0001000315943d07034402107030034009507450004e11041800d03003082540d40c1e44d000340aa02d0700998000c151001349400140c402d1802160b0360448200d500034511717000d0b0a00c10400200343c100400c0341d105d50b00740808648044184202d602451280e242c090080c10020108030785100c0040a6207070300c0d48921a030100580300402e003070810f820292100010b04089901d420f40c00200c0c8800305030400300d0b00444005000f00d41d0080400c55009506a80380a000a41025250995001c00300725503441040810031904516207042d5101d1030030f14004680189 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 785085692 1250 785084442 785084449
    0x305061501030920100504080309091e010914060102031c0c050c12041706070512040609120f0906020304060203091203071b05040c03021c0b03160f0306050c0304021309060902 77
    0x60b007414542c10b8401068024038182020103500030300c2c40160602031f0500d80391140c3c10303907244196800300740202c4402c0041441c00381c103c01681d01c5d424003054214910340c0c46a80d400010301400902e0b40304400c000001c01c1455001104503003483d502008a0710041c01d48280d4a4050710401030681d0400c401009400c00e08041445680981d84a010b4400d9490703242c4801c1c9100301c0910303c0f0301c440300d03000501480211600041103440d000f0b59a5082e2040b0f0b1303141d0a003000244900c55005d04131042044400701402d40c00405842501c0d0541c850114130b9858180c00ca03504c2c016400b501c409a4003c01500351070785000280e640d246241a02160b00d008031590711036021548a2a42c9105c00d0700c2d081041c051483c0c41d00410b4004126403400318140a04240a00d44c0e01c40700c070040c00050795440c0c0380c040003501c0900a8440000c041c01c0d901c04201d5460b602c04101110750700c419240240380c01c01050282035001b041300d0103140c00900315407010421070026401003440c0d0748211010740e81d4410a200584 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 785086942 1250 785085692 785085713
    0xf02040b0609030d1d06090a14040902060406050c010c020304082e061205010f1a010c0507151206050a0e010510020102040e0103030e1e0604120213050c070203120403050615010309 79
    0x841c1784d80703425440707031081e4204038012001d51016103e03220900860103580c8580203004211034944030038110901c545004100109200d9101035040503002a002c103019801c030009145080320307603008010380c0304640d00481e101d0085000314003e0f0742191103103103d0400c03500498101c01802c50b007454003400c152600d850482c0d026600c288115245c452b020410300c0000e200d03900101c20050700610050b08040c900300b5401c8981500c3d941072180750f100e0300042c481c040000c00007904091003c12020305a02201400000f0480407603180281040008140e030300b405803441e000c9400c48d40a1503400d900340401c005061f40441a0382046641c24403002544000c032800e180c0c001c0d402511402c05034942c0009122010411865494a00354106000c03c0541c43d05801c590880f1108403005000e0700407840024045c1d0100d0507820304082c2080c052082031123000000307290f154421000c0b1003c42000c580d4203203281c021844003401e6500b0400005d1424203207107001e80c408420500d00060078500603030350402101e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 785088192 1250 785086942 785086963
    0x1081b090f12011508061509041112010b270a020a0519170723130308070b101d190e25060504210c0b031501020c0d0f02040b060903 58
    0x181c0d12032000e204c04550003007a00d806044000003030262032070b18010640743d000210607501e026038103102c0050284030340d9814a06411500420f21482a40c00074216400780c07807091007403407245401c6042d4100700f01000640240815007003040c10030315a60518584000c2d000030f410041844420084d4214906075080c800000c41100e854010300e5076880042c642c03054500500d00c9050140d0865601007040315890480b49940c00183c280d561405550301c5119408103561004100b4500481c5200400c92000010b40c0306850040780340c1d403a590344500800d941c00b4091071280b01c0d2007800c0086580250900c040c0403520f40071312004180410104200d51a1040300308905040c4203416480c451032035265120b2070001c10741d518000c1d04150500d106203468107a1181100c0410102443c44401c01c4043c03500c14004220030403060b52245000c1c1300c00c40701001740c140e0090050243d592030500601c0c000c00c00100094000041c10303906121036080c48020486440803d0b4440f80500403904141c0d810801c54070309 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 785089442 1250 785088192 785088229
    0xf0c041526060a06140907091703091309080a1d060d0504020103061703040b031f06120b0604031104020c0708030c15160804080d020708040f031101081b090f 69
    0x3080500d001c0141015805031480802030f00344a81040301d5460380603403212100086070424510340742d26200703072119941c2c0c0e0300100c40c180c1e14401c0743d580030313001001401001c3c00540f204050080b200c907992080315061a4000e00710074061040070b5403070b4401c44900c460310030001c03a030240181c200400030720682c0000c2c06040c10161210100021943c1c140900f40082c1402008402c0e20080b54080c10740b680500c2c0113440b0a14008000500580c0b000038200c203140907c40c0318000c03800e4580800074100500d1440b507002442c208941d104542c100081210212500701a4600c2c01c04114000c0101a6004900184051041b8100428050824802411281814001003599080d81d840126034003400401c001140301001c054034605035000b00350103500c2644240340302c3e0740b00c088405140007409008000780c4480000f150104400e0400c000e03d0003901d0241170085030176440f22004541c082011108500002c84083c0c130411880300d00400b0300089240185500350303400d402c1d4040342920850202c94040d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 785090692 1250 785089442 785089499
    0x61315050d020706022710050901020109140706080115080c07050f011a0a061b03030902010c140102070308090609120c07170d0f050f0702010806011b030801060e030f0c0415 76
    0x1d01140305803080d00e172503620171401c00b074000c5000003558107c15100c10400b4002d0000d03191409038400c0d8032000480360720110600200c001000c5070795403401e050240f0800700d5100000881c5c51440c808604403501103070781c2d030180640e5804003100101e810503107080b2014403c2004800e10300c0d400b806155109507405c44540742090400003000440c0c22503600c031f2824481b080610681100d840345c05110a0b6802d4100071451111510040b121030701152400751403c7e091150308800d08070190001c3c01014080c0e80c850a107070f264150895122881900c0304c44843d40910a050240034003000070f00481c600362400d50305403036643c49043e015402640030f00080794012419403200d181e0041da0102c6201d1442c80c1450801006014103a00c40c400d040d0003038188902280010749680c4580300b4020b215003015021422031901d45000341c41c0710000e0042c103022134580e2407122589d060002d66111100e040b00c0c010230b51407000c0783c18440241170400800c0f4000440d40d101042030741000030f9540b84141452403450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 785091942 1250 785090692 785090707
    0x240c0506160e01030b150919060807031a0f09070e060c03040509070504051507021c060902031c1205100b070f1a13030e041b110c061315050d02070602 66
    0x24120b01c03490300007a0502d440d14068000310303111141907200030390040690580d9680700000107180c4840010455014560070074001c140c05034000700446c090b8059807400d125401003149846140e00c0465401034001da00c202a144042c40c0c291070007034014842e4101100300c90158804078840f6800912300350f06a60001404121038100240100d0340039455103040b41c01d0604080001d18401c1c1d03010004540040081240d900b0f56645d00420b00e01110003061144d8410346c00d00d45040500074445044e84240a908010b060741c00301d80c24140d10b040c00b9070380c03604001e0801d20303411001007034090100c040200190001280219510b40180300c40b0b8000c00081c005c10405180890b505045200d0741281c0a80c90000e100102a4800803c0400c41d0302d8282144202600b070301007402070152518201007076161094090801da0401e018060714554241134a00454186007031140700d100b000030100b1a054010703010000394441c1011900e0007545403501c0c43c0b4040641808070280e802460b000d42d0240e0b070014515 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 785093192 1250 785091942 785091947
    0x1e24181b0812070c140312070503090a0909060c03050f1807050a080708070f030206040605160c030b09010b0102060408030a0b0111030703021006080c030c130906050408030403020f0304240c050616 86
    0x108010100b0b038161205030300717a003004070752620400310801d01240e102040460400c001070050364440f003409005074880640d0350741560054a034205081c0d44c064504041840081e100b4050180728160030711444c030f40c540301c42c41643d40f900020459081c1c40c1c0151000800c055442903e1030006001f11310003400d401c3d04102c4003a0400c94103900074a2014180b020400c0140c03145002e4800320b40c1030b800c00d0364a40c1c00c0741d601c01000c52a240e80c02405582e200e0408401c00c0f030320403c1c0500400304076008004000d070260042e6560b042c2030b1009823000c5000d00010790098516000200c4c0c161040c50302d800040d12280c540703803454001144c03c40140c0c118020070152031b042c07449a0401000750b103008003401040c5c0f8001c40d844582210070507000302a1820800b1030b40704690032202440c1d52080007000710380340c2401d01032000e1300151400ca0040c044c07520030550041000041c0d5066451000d50000c103a5900d00c032140220080415131010300c47e101036004c000c6101030011030302c92644411181391100009000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 785094442 1250 785093192 785093213
    0x1e0f1201091d0708070b030709150c03020c1c020d0203010e03030709140a0303050d0e0309030d0509030c0904050601061d09010306090312050712091e24181b081207 72
    0x10b10010341d11010007040f898000040c0e05044458400c503113603403a12003500031100300c00b058011051042109a070482c210303900041c0d00500500a5085c0d441d801000300030004286281c02c989200281044101e40c0546004a42c1c0381c0c501d44000c000060403083c1003b01410340d00304482c04000f0902c9281c04210380703741004509482c2e00c0454440007550300715030300a8070901420408441896554402403444c000800c00c0301c9032448000c04560b4a0320314008001c200ea40861007060284c0a000b42c644540c2c18a800610300859205c03000c2c3c401a800c2050850701544220003020307862a2001800010351a030b40107403406180200000704090788182000340010f094060a207a200d442d101c104900d0992062940383c0603030b24801c0100b0728400340d007800000500001d6443c00c0400c0e012852204205080384040b1032007000c1c80c440307120100340382c149400310f42440100e00f02c450003410040000a0710240603001c04403441e4080d503419a203e0201c80c1c50414100d8031606280c100180c1c00040c00702c4d0059 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 785095692 1250 785094442 785094491
    0x50f090c030d050706180512041d011a0708090a0b040306140c18121005060306100509060103020901051b01020d0f0b1008070c080d06030210051e0f120109 68
    0x201110041c0002c0200544140360000d803855645119022607190010002c851003900b00b400c4030641101c80300800708660040c131a0316160000c0300500304101d9403103941181299881403001c40304a0100300203a829a1101d40100d500c602c04001e490110740c7c5003c4520701a1605065107070f111400c52500d0400c58100d20701d44101000ea010070003070000c002804491114070302d2444804542d0001010a410402075410034416000d81a410aa0007026a0103144103031022009c030341658880e404136072a08061b9000361a000126a000900c01c2c0d402034004040858061405a24140180c00d52100000046024a209940000e00c410070541c2e50f02561040764442102003001d07140b48000591502c000f00800c0c02030140a0000078201d80c014107030602100c0d00700082e660340c0e1918408c17201c020101800124030800c01c0c0ea2100007100e1003001500c00440021010852150283c0c0000345640c10a840400340020108070841100c402860400d0081c003c2e411302041e86c50740d50401300c803800191708 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 785096942 1250 785095692 785095699
    0x5030912131a120117010e0f1605100c061509180227010905060301020712020f070e0c03060919020406031d0f03040905070905040e1c0302040602031b01090501050f090c 74
    0xb0141d03005042e080d6811140d03007200004211781710f11384450241070503440782421406000316441050902044200d500001d105190181e60345402c10030941c8190b0603a0440050000ca405d100001c42550124420010745e900d02401c50740e42d42030030b00c280e800c941142e4001002c0c0d0b442c100308604000d000340d031000c4072100101441c2c0c02c13107000e4030f080c0c05c00512070038160540358804144036440c00e60407501e00c5504840a0780203416a954080e40c0c4e07074038020050702544200034000030508007024400b805044800e405074030f161034000800c01c00c0e010107486042c4402403184150a61b80c05c40c8001d10003416203031008036280050103164040740306280c0c1c0c440341640089200f841c00800c04002c80e41610b00340000069144c40340107080381c00c0e01480e00b00d140c01500c0d00201c18030301d240c00569094545106103171041d19241064084040e402240b08050251f402440011002c0b43c00c8520929902c40325000018a4161601c40c5801c1d1442952540c00044951081c003148050610005415200a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 785098192 1250 785096942 785096947
    0x303050c03061305100b2208010b0a0306151e050f10020a02010c0f0c06030506040b031c111f0b100206010b09150705070b0316020703050d05030912131a 67
    0x200811103064500c92040b0f2040d984000040521340410034000140003100280341c4c0300e0aa005000c0c0d0100446484410780752484e4000240b0942305003d480715030a805051141c603d440c607620040070300301480c6480380031100da900210b144851001c0b04852007000024006c000351400c1c0901401d03400d200c0059026104100780503400c150000f40010b1625820329003504410054140810400d1010000600d020091180000c1c0c5540c0740d0080c0f03014100403242045000115070805989094494041c80d6110301004103d0b201c038040d110210300c0413000b1003940c41e0b114090100d0303641481000800034009603101d00f5898113080800b0100c6240751180010502d6505020761404240540d68110f446001110250150003c031348090b103100319840000c4800d141c0d102c074503400c4c50741c10846100e0044d02640082070304461000450800f2203030801e0107002c2484060300300329000d51004061078028030600c0385900c01003003000001c0c9855101c44204591860401310080000082d01040100b104000d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 785099442 1250 785098192 785098201
    0x5010b100507120807090803070b010302040c08061e010203120a050f060607050601140a09020a0f030b030a08120a0902120604150614040e0c060708120c041802090d0b090a0303050c03 80
    0x2c016000303003a400c42e420504c00300d0f540c00c0c41c110fa4441450701311000c1400081201c000700560000c916058903c2201e040c041c80114600c100c5000200701e524991010700c8003010101c61000d0303030004120000c1032040c1c07480e1462405812142c030000f07580041c5169071311403c004050804c200555040901152424074224164035000e44ea001d06000c1c50030342c109400314096881d030390001030300c0003800a08025074488050310070260058400400da0790209007012a6000c0078038001c94200340150740f040050703013403044000700585d00b10001005800f80f107545855410140c1d40388001c034039242200d4001070007145000e12340009010300440e2209151400c1540c10b100c0443c0c5c12960681e6810196000215905091a80c52409405a200301c0c2c0045001601d007080c0a413010062815000c41c41958a0580b69610b50007064402c9102e01c08905025240038000001c15800500340c075017001b8400da4440000b6101c00388030000c1960450368980c0312404800405815008182c0e0040c0c0007080d1504500c0d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 785100692 1250 785099442 785099453
    0x30f030903033001080c0907090b040603110409050c071406040f080309100e0a17040f0e09071a0d05100e06010c0c0801051303080108032502061605010b100507 70
    0xf00a40d02c0015000419a00c800c941104504004541601c803090351559542010030789071586898014000c80410700024066809030213554200c6561180d41c5103000c0c80c00100304c0c01405040803004010781d013080002400300740c90080c0d5000d85e64001c0380314bd0350500c514041029401c0044564080c3c0c0040c020080498a0f10306400710194021150751381d80e503101c02803507041071001d80751201c946140149614680400145500813980300b00118031095040f030021311740078020b0340b0032501c0380110140b05000039003141d02030f1a080720034030302120f04050300d60411212260121000000c40305000c61031b0740d1a4005030098a40006a8030804490dc0341000c00508406800030419030500210003240c0e0108101800c000e070003401c1180c001c200500b40070442507028011100301b5000110900d00115190034080210f0b0508042c01115605010707200c100c20321984481103060364002c80a021240d814005003001810b064480d0000141400a070030411007000030b1900c1400800c203040c000c5000140 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 785101942 1250 785100692 785100697
    0x310050f070e18090c010e1e0409080f0301030b061309030c17120903070611030f040222020d0603051c05030a0e0a080a0203040306050a0513030804020102070f0311030f03090303 78
    0x400c070b181003401a1200c001048050510b100a404002c8180081200e000c1011814520b034050903654140031002c88010082d240703207240c0210324181002e105020301468544d0081c0d80d02c074800c58506092200c90140142e054000344c3c416580b03400050100400c0e80b8000768002018a8650020810f10b82c0b903440007042d10040c10402050541c018201d29241c030021426900c007003c07800400c0586140103100340c1d841360030801c41101c1c20b60070400225440d451120a60f03120340030143e95200d040d551038023005400005103812400c04110280200610480e600040c05080d411100101d403c80c03440c545127140c030292600081c05104640c20250001d540720303040380d801001c20385c004038030200a000303118244440c5050040000c60f0014500d5800e54011010300101ea0140c0410407241d90f03000030b0541510000c5a03440d015400f00040c5000181c01010450740160041c070403034100e152207203134980c00711440340c1099892140d0701f91042490b02d020804183d0480c41580914144040080407a5490 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 785103192 1250 785101942 785101951
    0xa031517030313080c030c49050f0a0507030207051e01140f03010e071106010509190f050915060402090109170f1e0105130215090307091a0310050f 65
    0x600105840303c00d1007031001c140c032007003001d202c16130f5a25480e448006540c0c0c076400700e02c0091070229090443c000a00500600c44800455000350340d1100c507110419055180c1c54800018440144002078406100401400003000d0b00e03141c0b65629000c0d814007910748112507001600c40e114909254401c11150104d500342c490007070030a01404508118030a0060107024401445007402100019640030a014801d01a008a032118000c45000c0503445440b0b06090181036081040756003c01c100c0d002d0500c482d05404c010600c0001c000c507452002d14140e6105485c000c80c0c40d4003001d01950303180000341c103070382c1c0002c1c044808510f050445000a81041e50a10603940d04240d102c014105210b801d20041000e1b814a270142c806894244084690361106004100455031a110009a171114488802d0004c1500104540322543e03103a01d400c1080e03803084180031b405003c1c049001039041103a0041100d003500c42c1c0c0d6080c03c149210700600d49030a00184c24400321030b0400781400442c0c00d41c0750003143c01 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 785104442 1250 785103192 785103211
    0x110d090b07030912061410030203030702011d0a0609150504230a030b0403032a02060a05100e0408120601050a170c04050d051c030c0801050f03120a0315170303 70
    0x101d5145040c10b490100c0d0503800100f11400c03082041c420003115a01942c815050150706c4441503c3e03106004056071000d0100942640c41041000095070040015031203441c0c1e5401d24407401440c280100e00d004419620481c0170410b480d00031b03c00c030140004180c101c1207980c074000381040c2c81c1c0f00210082e0b0f6910070b4500b50010b50750040c1c0355542c82d0f010b2008007075904520440003a041a140040c020203910308203800000b900962106000b100300000c500764181c540c010301550312140d400c14020100900556455035800310005400300309002617901c030300c1c0500700b010385444050a503e0a44000140382c00d042040c204035040c041c98200d854000c000802860b040016910465003122520454114543c007141c141c0010040000004252a5107500c468107508850b201800540c142d941c21042c2d000401e140d40014401420654600194040000c0032030740c2001d6601d0450300ea0341d0100b90003100285d11f840d00980d004541400302c0005219000511020f00d181c1580140c6900029000061 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 785105692 1250 785104442 785104447
    0x3030702090414030f1314040203060102060a110c0a150e0c060a08190230060d020603091c08010e0601080f0117120c010b03011107020a051002030c070303030b01110d090b 75
    0x2010b0f20070030684015011848001c4d545100428070066026080d201d0010042401d0641c1041e504080c001d0b20f0180e08107030001c02140e21100b400c1001303051040c4e03640c69020b03024014150900c00420991b4540c034002c889403138129004004010981e204444407080741e41c8150072000e0a911551700311101c0c1c1c100f0340b81502d9251141d40c2c40c0c0c0250102420303a0800e441c00803071b103169511001200000c42941c0c1d800e220f00c48455400171005550001c40d451a40101656405400360800c1001143c0c021048030665206a203503145c002240380444560790001580d041c01846640720340c0c46001e40281003400c1c03c521526001c00f05516400b014082c04018213040c40d2500404c90f020454407840048401a807910b0340d2031030175081d00030320f4401c250510942c20070903120745c0300040760101c82520760081c1108400e41c0c288070502481c81c0b202c1000c1e0003148401c114030a4000000d001c4400654425a03003c40c0c1500004001401c050100c503400c02c081e00280c11012201c0c2c1c000d00030f0401c4545218410780c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 785106942 1250 785105692 785105723
    0x909020604030f1110121a010504180e06010902130e1501030e2d0706090812070201120609020a080603011a10022b0f02030a09090b0609060a020106080c030307020904 73
    0x404c0542d010380c0c2160428460341070140081c0d00120071406403810280c0420408412110b5602d11040707581c66036010400821043c064480301d440c1000c4a84040740e00400c190140001c40d41c0392480980c03140c3c011941c04241041040c101c81d24040017400004100301403410103116103e64040c0104113103050541c0c81946c3d00c0c0304241844031608498804900324440c0d0400c58440d119001400f0340d902803402008400b0500030b00440381801540c40d908020030411140c4c15040c0c003143e01640c03081c0e0500c40c80c0305103203403400c20501400010301080c0c4400b58581c0300351000941100405802c15100340d041c504c01c41c10514403010f0b810500728080310617000009107240d0030307410a0704904c45090604102d0752002c581d041c214804d841c000407265034a148001074480202d80301d004e2004894002181d000d010020000301d500900990307640100311030b2401e419040040c003503502c6842c042000d070751120010000c01d42d00303120a00880c0c505401540c9024a5070340001c0d10413200901c010301159070800d001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 785108192 1250 785106942 785106953
    0x5090f0a021321030e011d091015020a0510091a040606090903200c0d1203151e140a05090c090405040b0f0604110406110f01020d0204050a0909020604030f 68
    0x15009003c1a050800782c0c03008690b024540b00901c3c24250049084070245010039446000e0f041d00d02090391050b12902d01c0000c041207035171207000c1d001185203001c00d440070603510b070140b10f4200b03200030030340084c034010203145040c03810325080300c14425001e8605080000030507130140c90301e4002e100e020b8450389140e0f42d0303141c00801400c081c1c0003201d0161418204030b0400d90042c1640190411819084031801c002500c041c0d607402e06602c00d01d400074010700e448400100e9450603c02012400d0401088603400200d15154052290380700b0511254552148110311403031309252000307409080012030300c902a050120b2007038502132140394019a05000041c1541250304241d070b82490000b4003e103e241040d0405038800e09064404c1e299180455000c6100d03840d0038454900b41c4000030f44100d081628040003038030080b00c07901004020340034292010b80401001c2c4000c03c50400d68610058071b403400c080500c48a0700d07558101d0320354a0320704418403016940b0001541e048907441b82100390044401c0c03910 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 785109442 1250 785108192 785108227
    0x703050316060b0301020405060702190513140f061026041b060206040c1a0c0618121305040507050c061e0c070b01150221031005090f0a02 61
    0x2808900011920004018902020740d200c82c0c050b68007803015001041c1054200e03c10780c80380d1a0f00020400030a070041c1003920b090f18038005122581803049503168041140480d400c0c2500c0f505560f60201e800030245801c252503000460003607914403c0c40e03d20041070103244032208003000d005500811010300703071a1180c482c1ca5020301001910540c2820319251198011a880704040b0600040b00030610305e10010320644900c1d041b0a003090510300d800c0501ca2840040c01040f19030785801c110b80030507904d041040e203004000e1502110007482106060600340318820040c051030301c87c10032422901c0e07441200743c681941c5c0201e0b40001c603903e03001c17020380f103d100350320288030180580340821a040383e10729103800f20769640414092542d612f1201842e50f61041c14002408200b00e1401800404000e50f000320f03100b070300ca004540d80080a000558510642e429503107420020000030031440520b0307548490002c2c4020341e0020400e00f02480e41d0000c06d03100400c0c0d4104168080340024000050000 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 785110692 1250 785109442 785109449
    0x51b0f040f090b0301050903130b0702121b03060105010c02090109180c120312021c0903200f070e01150e03070b030112021908070302300303180601050105091207 71
    0x303a0201559880c403860143c100020518425440d1000140881a0200480e42c807803a03d614014456400c00c0f016103001e420808040ea0800f01504203c400a0b10400c5243d0070406056042a0f0200c0c00d6400c061400e0f01c141c01a0741005605142d440c01600c90340682d5040d20350301040454a10507001800072804507415020b030170701040b9440010f04c025505141103043c0c0c029a03c450103804d00d080590160b1203148144450036201040205040921340e0000501a04c03a10b410a0021000820310207260b02d0705c10018481c0d00040c032019070045080003c40002c1c1080301400300d81f503151204601d500d4191981410902000802c1520695000e01035100504900e0b0340040e140d5171603042d0006d442c40265002c900414580f603a050804840e1030350102100c0d000300040c45182d0550342072140c01c102d94800c2515518107002c41c01079551818201c6000a4003d4006507203074a130801d45595444030245100f01c854001754018401030b40d010080300e82000c4207480305091301c080164100c0c5030244550 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 785111942 1250 785110692 785110709
    0x603120a02240a0623040b1203210f06010f030b01032004060806030a080922110306010e0a1815120b04050d05070b010b0309100c0f2003070311120703031e051b0f04 72
    0x381080b03801c4805448ac5c0b413400960300170210725074800034800380c0d0503000d441c464082102ea24103d0b0340d03103200707030010303040081d041c5030202c0d01101036420410b010640d000741c640700c000041018408103500480981c0c1c801411402840d905005484403409446144641d602540000c80485940c200340103690b030090f0b0f016802001403030076600380b04059400545202d400030f0502ca074131060500d42030a81d8400d03503c00b032140040030b42c21414100b0003442e49400b400700984c088400001c081e0014103e141c1c03418015080354103249001d241c883d050034030140e000000e010060164801150040218506581800c07141c00c2c0d41c1c1e1038143e480d034030386a0300002280d46c060030500301e01410f41d4003250303a4a00389007a45940c2611011501c509107541828585203500360b201f8858400424416601180c044000c3c8054595260741c44125030380d0f50b4841c900c15004681c403600b140403400705906003403102c0d244022081003070b8103213517410901c03412101c50340c40b0801c0c2012615201c000e050104840c010100322 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 785113192 1250 785111942 785111947
    0x11e0b0a020109060b1807030f1d0303070206070504031718030604050718020a1403100302060a020c1c050613020415030c0306050f0603120a02240a0623040b1203 71
    0x800d000b8064600360400300c810700d0400b0b00420060a000440720180082c0440c1d1a400d50f961401c100c1c01000381e560050f141e1a05d51f02007041c4010b10080f4843d8100c1030801070f568074548008040d00c0c0c041e014100108010040008001003001c40804940144603207003e00e1313a03103120b0080208601e800c1c0c1360040c0d044c010300381448100007000681104880304400b0442d50b07011040d00c0b0400720302900412401040240f0f41842000301840300465000c030380d08101c07a12017a1281c020841c0e581101c410000940d20441c0a00420f01d0000050711148150f4142d4480203806950364a860348809041c1d1503060f03815115460071541c40e504500c15580007010b00400b0566242031a46800019101c10790302c0914140106a0003100c0c03150f80c071311030700001c3c00400186585594406465010310511000c5001d00d0690049d240150740d207611003040c001c01c1d00400c504100a1032001c440c4258828200c8908800484501c1403010800c0308400808650000d40c0e1703111807000c1040302440070480d0700c403030000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 785114442 1250 785113192 785113207
    0x10819083109020705071710050c040f031401050108010b30060703020a1403060a12060207081305030d08150d050c061909081f1a031006140a030b011e0b 67
    0x9070f50103440400d0144040315056075485200140500b000361050102c0d801c52660764651095a03000150003103205100c1502e45540c0702c84002603024650412a1201004403107000749660074010107002d00a590002c2041c440221700003441d8048841240c000d20110303803400306848080300910b000c01c98680041e1a001e1403c10b00c01002507022011010100d462181c0d0807030010a01c41c166803123030300050401d80c0c034113003031a080da802e0b4190244101c40d215020032101340050180f0010f4080700904201405c50541010101030516031241c0011041010200030404d50481d00b10300b600181c00141ca0003100e812950030014144040c215016400100c00100341c000c00080300914103982689958a0b0440c50b15072201580301c003007200c0b5040145100c40c41c484282c02295001c22018510400a41d03030000c4582e02080c00c0528030050609090b030f45100030000300b0052042840d200e4012600c44009030301390303507403140c0340718040c05050040704540502031560580f221060f0040c10034900e10310b407101003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 785115692 1250 785114442 785114459
    0x82a100c110a11040c0810260a0b010f05030604030e0121110901030e0d080c030c220504051506030415060b040902130909023f060108190831 62
    0x4483d0300640580c0c50041c000450381d119600440c09109040500801c0b1441c00d01204c180001c030400401003120b59142e8900300c14010021072804034031130740702d2826542c0741c001302103400211035000ea4003a400030000c0000180d0300c0f640140801009003041140c02c5007801c00304050380e1202c554880340b64a402c503d10340c0c1c140c002018058000b0242d800b80022146c00f40741d15100c01c603d082c1c0c9004900c0340d0010510668011000c0e550011050410034100202003180205135030003c41d0151000a429009101c03a081a0055a5001851103030640c1e003c517801c03000c0780722031100402c00780c04096894024900d550f01da40000740148080540c0d240c44035221008000258046074800e00c03c031a001d0f0b00060381501d82c2c022914120b400604000070703004200b0242104100030300c50041c02c100c0140d42c9030fa016004502090008000b98028040d43d81062246840d0064006460f0115415001c0d2600002c2c030b164204c1301060f10304500988040d199204503140070f03d4030f0085031807019010002066240 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 785116942 1250 785115692 785115713
    0x50c040b070834030c0809040f1d01150611010204030b07361707030204060b27060412030201060f1202011e1d0d0f082a100c110a 57
    0x5525101d8080c0c0807100c2c0441c420f501c60300b0405004201031108500820300034034541c0e01c1a4010007105152480d00b80000301201e201c00702c2880840d43d911601c0c001030b02e4000490910303022500082003003038500d00100315107410a1044804000d90340c0c03080c010751070702134059600a42e4003100074411800c01c0d28001c0d21000312103408110310050000c40b4100244150080038008040181c9002d043d800c0000c5458840180c002c1060a481140d1700000142c42d1441940010209031315810740310300c3c1d4100c41c21071180700400c1c00000301101e661740c2c42065a402c0c044034112007443d02590080d03007052030203034050070700396000344e50612560708000b8640005074024003090380300341d0703d0402c0e070100d1501020900018485c070000081d604070340003140c010003144801608c1c00007084143c90303800c0c65561509490802c80200c0300f14001051240380036604401c84262000000540c8200e038072100085a038500c401c3c6042d8030456181c01101507000c1c081d501d030b0f1442e9003a0000b0b5480181ca141446a84807 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 785118192 1250 785116942 785116957
    0x810082d0d0e03060702010c0905091503060f060a05060c03040905060a030b042103360803130c050d030c150b030f01060303020c120c060706021b0d03290103050c040b0708 75
    0x90084c400007030039062040c8120107800100742c0707038142c09501700b0b000e005601c1002001c0690f9403800c50315134032450303404100d05c522a44001c1d03041440c034606041440f550b980035511040c0035080034800d410741c0e460007109550945d0301c6a0000076082c1e8035400010031580459002404c06080c6009000c00d201c070a0360364800703206ca0044540d82d4100d400b41d08500701ca0070320744101e07184e880c0c1400c0b0510701c044282410761490f5440022044124003500d6512090f03100356452907001d00c45100003010068000d16400c002c250450743d2494507240c0342c80c083c28445051300300074025081c40d4078290300601035a0100e0081d010103021500000d4030768908a00a184a00095000d4030402206050324906080c0e83c0d00084128406080d001c07586406100a80c0c01040b01240c140c0e03002e221251802e12500c004c1d228030100d001c02085e43d80320083c030282c100d928024101d01034403a00200340d0078190710000c0d200000303402072a0016071035454400310324007030040b03130041c00a944c000203801007030148420103403009 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 785119442 1250 785118192 785118199
    0xf09030204090c15120b01050301061b0c0825050306070813051203010311031b061c06080a0302030715020a09030816060509030705060907030b07121104030c03030810082d0d0e 77
    0x400c031001b006640310b0000340315200016810b0030b40700901244105c41840030f0b84c0b00c0c0c41030001680d26080e049007850235405903400002c00301940c81a6108141c1e11420051009601501f20b80c1018240107000c90710080600e203803140d0030f00110f0108101000050300100001381c203282c5a584925050a0300c0d8400c81c0424401d00c2691250300045540c09212420b041006180c0703403400004c4d85041841360881100c0d102c1c0b80ba51004002205401071002e00bc80317500c01d502840e075443c458070b054024400c003142800c4c0c03014070500000c0c0300c00342c00101c4201a250411081503d40c954400d249014405190006003d2070070481803200c00074002001e00350701d03841002941c12542d0744c444142d550784150312003e40b0340da00c3c5201140980e0701494418034141c605210228040c146942c3c2e0070a03591040d4001c40f52a81c0c00d01040092640c8010426080a4001c1d0300d00952481d00ca42c02e036941c241926005400f401103081e500b1840241480f0320300789040c2806480c4040b0131200701400503098441d03010300 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 785120692 1250 785119442 785119451
    0x180c041e15050303090f0409051603031706030303070e040213061d01020a0809100903050d09030314030907051002150c09030c011403150a080f100c0f09030204090c1512 74
    0x114a00d580c185009442e40038000307604013184070003000b510482060300b2a0300195a0000c0901141092200e0803088101c0d03000180c4007441c51800600c40040c084501c01e03905c00280c2804104e590202c1269000105480d01140c5078604c0300c0014000c2c8202d003481d000c180c246400000c2c0e515001112a01508104c05820420060352001a40c0f20380500c1002051800f04010100503458440310354020884a4545524070b15200e43e0b0b11351030001e18000c050080307842d1003010000c255214000d100380c080c0e115a85800c50800c078002c0f650f80e1140e4040c05100b40004150789004074800c12003610102c8602028880605004400b240241e2120b50703814040d0080b90442c0481e5402601003151480c072842805107903680d401681c650501103609a558401129980010942405c00500c0914150180034162200444074410112003141601c001400107145890720515084007086d8212030301a24042011117a510380000c2512403504000b0701000c0101c0c031400c440e03902404440112803124030800 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 785121942 1250 785120692 785120711
    0x70206061c2406330906050702090a0e030f0405100c020607062a02030909070e0a060516052a040506090c0d091e02010909090b180c041e 60
    0x4210241464081e0808058407806840300400000d8298482d1204500041e55516403c07500214107810003651000c12150801510081c107050500300c4c40b1a05082c035151071440e110000d812801101c002921400d1200001044030303000d138204451000741d00007070329694103100a081410303400500505000b200c11926200c816030203034080c2900c0c00c0d001819181456100d90382e000c007a04046d00d5201d00401241c2c00b0140c0b9244043c03500c030350202541c000c1d5881381c0c4030205001c56a00010000c404220b090751030000e143e01c42c11200000d4821902c0c0c0155100000ca1030391104a040c0c800080c40d80c1700fa01200034203644143e0540c18594121580900d031110044200801d842c400d0f1816a400040030b000b044164800e0760003884502d50100c00405d0903100d903114001c0f50140b00700d0800049200c00354000466034840d22440c050a086401085241e00c1500c41b03010f080e070014018500352a0040d01001320040801c4292007011009005001083d81d0780706182501c6842407800880c2803c0c1004103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 785123192 1250 785121942 785121979
    0x30c0b16021b03070308130f0609030b06041b0c02010201060806070305180c0a1203030b09090f011410060f02070803042303010e1015030609060e160e1302040204090507020606 77
    0x1000000340043c002c10000c2e0071616280c54907070104401103c4055080e400151041001d00e18030014001c0da01c504110a2950a2035028044020f02c15446149080c1809028400c441e6810284c10b1943c07900c40c0c0c030380c41148010303070042205412810300c900c607407403c00c45a07583c540c22040c0302c0e2080c0d611a03100150404003444d43c901101400a50100201c40309102c410401010250100d01078600131039003d441c000401c41050040e00d4051403034005001d460b8104001740200c4a8004c13455040038201d103014801040c011805003e0001004000803440c011a40300b0404200034210072020384c1d66403030340c4840e404c5100c03081c070700011540314005101000ca403506100e8190403014590207050740c2020307001c03194010328803440030000350b200340c00300031001c1840c1d8883c0514240c840c800010b40d20141071985490003001405461440380c50100500c20a005035502982100b1001d4600d0703401c103043c0c4000340c040c0c09580c111955241c604420800e07604c1d4002810b9001c1c840960341008004450b030b084 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 785124442 1250 785123192 785123233
    0x1a010c050607140d0903091a0703051207031e020901090e0702031801030f0c1701120c060c0825020f060c150c090a0315060506031303050304030c0b1602 67
    0x140440d0000400036500600500c000f010407400a5080d07072400880c0200724080f1000202c0650020311044018000343d5440d403002c2c0c804a681d1041d00b0b041903802c0c1d500500e140b240107148070070704400d03c01140302580a0340100e0080c15182c0d20340020b07a2a0103446400039002120142d00188038035000241001b40e22140d41c0c050b00b560b074003952030b00c26103101002110b550300d4015810141d441800214969080c0304e004010301c0701d81d454402c1c86a086115418130750040e00301072041c4407000c0f011000200c0030000e07003088445c00d040c02c0b03600d42641c0c2400000e90040c2c1e00804540b60045001503440c4056480e0001c610303100311440c43c848e101020031f10407507000341d03100c10800d50b000c007941c10400a0101c4269910010340e01c0d65a24050940340800c00d101e003e540110b4255103000540203036001c5500610010700030580d0968210320340345250700700c000e00901d00602400030001c04a4103040c4124003100c41c3e03542000a13507801d81042d6802c2c036070540a600e0b025006000e071000c2110400c008691 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 785125692 1250 785124442 785124467
    0x6181c061a010f0804050c1012050108030a021c02030f0f0903060703050606180d060606020106080601150203090105030402060712080a180f1e14010207150b220e010207061a01 77
    0x180c069100806040c203640d113000141c000d40d6644a11102c0c0f500690307171000140c0712100940d89407120012071001d032205a0350107070012030454000381700786222581c1c0083da03d0f0000c6440c0f50800c0d841070102505030708500c0703014000d100009000500c000c01020b104000d09504409500f203680310b64030030307404030b00702c1e407041e81e200358071180400500f81c120040340c030008070215004120700384c20b0354580d9404046a2036544070f540503035140d090801100d44240085030052100910280000016480007900c030b00c20700d412035040c05808800301e405e540318201038a00180e400110000b180e040e0710405000c58404540083c006820b1032a02d030040c0307101000c04547c0a074814070890411400340c0d29a101140381050320041071010980e0070010400344d50120f2007204040000607585e40349824100c1c07070240d0740c2d050700c0416030030b101c0410387da622845040d14803841054080311440120404c00005041c00c2c403031100300b540c0007203211018080e4036841816900c00849540f00c1d141c12480040d01d5100c003864 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 785126942 1250 785125692 785125697
    0x311061617041d04030e061e1c0f0905100908180621101203020d0806012001020d06080105190921050c10061406181c061a01 55
    0x1094002402110306180800e10301c2080506003a00c0e4410034080f000400b0404100c0b203407242c14402859040b500403e420031080c1d541034500400545880141c40d00000c500310303d0500050007601c07041c002c070094880580203000902c6401184400000903020502098500f4000c01c40c60703448210952003558001a48132500c5800c05030f43e0815402035007441b00c00c080d0000b0341007000e032034100506c20701822604010001304005040203d403c2005100c0358001904005d00d000700c84010940000305015040704628042c2195601c07040101c0312045c1c10104111401b03008140c5540414040d00a010b001004107010480b1070740d00c0ca61a030a0f100281c40c01d07004040e40c5407112221001581161300c1032401104000300c2c04000c6041d604061034201c4c41c54001920209900b00d4004003448030382c03d0111395a0013440010f0400c04080c552607802400c261098500140300000e072110312866648024000308040b031151403010700c4c1d086518056000326070003803804490040c040c4c1e030944040c03070441060707 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 785128192 1250 785126942 785126977
    0x503070c050324060f061201080c0405100905040c08030a050903100b06071b031a01030212061014040608030a08070f0807080601080a0b0d030e01090503061306150801050103030504031106 82
    0x3c503030005054802074a07403500310320700c410300c0c010645602008241407460050660710075071400c00d42030706050b000d280162140b0704003014003001c0c038a0003440b06c040c3d814138400005e103515241b521612010301640b0455540c000807a0060746250010041c01c13480d1400da00755401c40c2e0900c2002c00840d0759502d03206900030001d001c04008100321100c68485c01c4d00038101031185a031a1745840c101c0c0320f01c00b0300720748114801d10300610850506c1c410840e54001803000804c028184410301c0080401d150203214843d20401020441581d20b64102100906071641540d07540c0300d401c0710041804c0400c49040d00400d22084003240c0e0182f003622414828209a030741d04079540c40345001110844409029100071a0f00c554000080d43e81e41546030059a02c01c1c0c0300ca00c007410700c0708009400100a03910152083d089441045400c808406100103000e0b400714001460240318003102a014080340c0003117030b041d840c2c2000031042541040060080d01d00484018445c01d0030f501c20040d8034401c8060401030304600 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 785129442 1250 785128192 785128243
    0x1b030708120a180b09040c1707080c070602190f02070b030606090427030801210803130b04080c06160509011805130506090c090102120915070503070c0503 68
    0x180005405090281c1c03419036112601d07112840035940c60f07504506540b40d00025500d10700d1400d48596120000355041c408130210002170881c001d0a00104058180031074a0005150801d0700c800301c1f244160710100031915040d011355150f450130800100c40c0c01160394410121240c4c0e0001030104115280e11064510f159030328014000340d13403c49003a00d90000e86a54091a464a49090b284520070800461a085030110b040041c02c011043c1e10104042d00001650010310940340a518903040c2c1007080c4d66500d441e00d0103c21a1100201c1c4050201005c0c0800c0c0420822110020125941500c04a034010b44031035243e403280558450010020400820105c1442c0d400f90801c1d04e4a45401070309800c2030750355180460498280b5203000030400d0343e18000c201284c42c014032083d41100214030141e040050850000c0d40d580d510583c0340380400c0d80030405400503a958801102d00c01810f1501c1070b02c40c0d5091612907660f410070402107401000c0c1e50000309850400123022410482c0c0d481021584502 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 785130692 1250 785129442 785129473
    0x60803030f36010c0f030605010504060c081315030b0415212114040605071410022701020a0506071202090301020c0c0111010207030801050f061b1b030708 68
    0x10220400098078040b511462980014400700b4611501c8010010640308041c038002400190021498000d140c908001800f082e40c0c04402c0d0340983d4050304010700000c2c0310f410882000d0084614488a41010100110b0105120309034a0142d5803c0d850500c4000c0c0b40800b003100342c980320707100c24036000d801000030001c10320170300240c2110700d09081c02418201005c3d00c40c602002c4c5c0c0000e81300c01c3c1546001d404400c541c0e008410540418103007003a541094141230b4010850f1080020250994820f11214071a00d0414031031140b60301c10500c002c40d0749181c810341c104403190000d808210072014108000c0041c0d400892036640c565400700c0508015130312440b003903400300b160f80c5154031034603070078400342d402600c00f44000c0070705003140b000070301c0003801c041300060280c080c082940710315900600c2048000780d004403c1d54107503101280d404046403d51400701d140f034000c0442e40107194010b02e580381d09629001c9944006c45070a01d04813403c02030740d0401e00d6070301c40c00d6101e01307002c5500800d96400d0740d40 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 785131942 1250 785130692 785130721
    0x11101404030818011d070905011404090c09063005420603010c05190f0c061a10050403021c03020c0306070305010906050d050c0f010201060b1309060803030f 69
    0x19843d510380c9401040081c101d608403051204010380000f10000d419201ca0000c0050000a00f5042028012581040700480712400c202d080d881c029603c40380c0f120100600080d03102c0c05005981004c225443e070700c03100c111000302d880158404a8000d0080c000340745164013601210183c2190080c0100c0a00c826800e41c0c840426010581644075030649100c414107040b0410480e40312500f4aa480c1e080c003100f05421100f0210380da07001e002081100048101080001601c20300c41e0303060004890740b03064030503116451000c0004001304e00d45902e0f000100101810420f0079607042d50b400816082c10181070341c482c41240006503000c0300100c40d604a0340b1050034002280c1c0d10038819a150b8900c2000864504103040c0e0308040030940343c0006100b903444912410700107140c11a010600b0000b2612520703101c11703511180c0c0d030094280500810950b4002d42040b4002d05c184d0301c0d540e5a844100c1010001c5001d903003d680501402e266000400d0b03c400015280181d10b40e40f0340c000035446e000704540400c0d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 785133192 1250 785131942 785131951
    0x80a0f03060b0a0c020306070813031103040306290a08070b07020f1c060509010606050a080a110307110610060e09090a0b0a0f0c090f090b03030c010c111014040308 72
    0x161180000b290715040a0050003c00340e450303c501808185500c105410048018104004c1000700000c202d41400031024070302030150981020801513844104942c114032031a0005032005080150021419082d00702c5078008942001d801c880b6900e5103410094002110b20440d2540d43c05040203000c588010f00c01424943d01c000d2250020201c05800303e0302d02442c051880c0c03a0181d286c210003080c0724140c05080c0e800b00500c8000c22116042010140042c000d90389110100075184000070f40c868a954401c00e10000d000044607100d10b4102d0000740348802031003000d0140d002e800c0114800c80243c84285090f195a0346441c40f2400d880c40070701409100007019452030344600d96488010030b81c0008000d0107400c2c040004542a0000d0a40070203489901a0480411030b031500100542428116040103640d030700d500200f80103060f080003a2460250001c410885c1d440c00c0c0a800070140c219440d6141a0740103000d869030b40d00842030000807a00e9054620130110001400038001900c51110107602 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 785134442 1250 785133192 785133197
    0x80117010e0a060903090801061508041401110a0f0201060b0a0f090e040f020a0806040f14120f130614071127040209090f19080f13060e0d080a0f 64
    0x2a04070389003455151040b020801d58549030384491910515501c0100d09003d403807400700a1222600e404500909101c00410003000c111400c804201000301c11244031201081c018001e104e940c084010804503644000341c810301245002c01da9400c0540180540d078226900f285442e0b0030021050350903908212101000c44c10440c40c118013242a81500382018003490280c045002d0b800900d10500014882541007080e4586c0040108400104035007044a41c85034848030061720300c1c01d042046840d1800c0c0d440120655030021071003030356042e42440505a44490070a00b810400d65402040da0803084001c0501410b0b1002c0041201166800e05080c0c42c5510103410880c100f16868050380f1003e190440300030394001c414041c4015072801d010000d401280501c09000d420410030000c03940e9007402410f440c000c0d40c80e1002d1009000701441600d03000342000303020b940c2c4c400c03400c900c02307050640501800707010410303c1a0000c2e0a003018040400880c1e48550001e10300102030318150f039050700c80a112800c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 785135692 1250 785134442 785134451
    0x30f0b0a050f0607051c020d4517011406090603060109110d050112170301050a26011803110d122409090c050607080703050711182508011701 62
    0x34003141c646c0000e404141558060304800c85105c0c0c004015444001c0404482a40c440e0710f440c80c00c0001d174a02c40d14002c01e850384900030641002414580c03c0540c0a183c0212040c51440800358064000070700c034504150b624401030340c2c0d0800f00314264200b0342d0880e415501020041c000541d1f83d40c031403442c0ca000f0600300d40c10004200004001d60300242c20003015100750b4854581004007268102d91401010900d5a0441d030500004c90389a192510402c01030803281c2e030300d59010550b80c2c1e528100e80d4082c1e10080c400040419124118580150310032070001e840b042850000110200d181c4242020315039031031030308421403269400545011140c03160340210030000401d241c0c41000201c801800301e02008100100300b030800110800b070581c0000e006003010014500041c22440884407410b03403505080d41c41c0c00040c1045d081c56040300140d00e802065014220b8280385410610502c21076611124034021055000008902100b90708141d011410100045c0203490b6814440344002444800006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 785136942 1250 785135692 785135713
    0xb0a060e132714011b0507030c08070f0b090714040e1c020d1805060708160b041a130c090c020a0507261605130615030f0b0a050f060705 60
    0x6001c014a5403072024511410040281000707507007843e450840806000800c510740982009100c50440d01200504101c000280750040500661101c03a400d40c020707003000d84448091030022050865000d050781c0c4081c0c01000205d40e80d10016100041e100480861880034041c0300030b20000d06965211341c011409805103420040390504184044500c440e8001e01c102c4038041c030080c007086030501194900a00c688024003da4460f0800c8541c09580514200c0d0f41e0040c1da00803094a0f01640002450030a04009001c103110a403001d151031400302d9820114240c0782c00e0b0248070303143c0e601c12740100080300c4501c042044104540c880c41e116815401984e0041030b04c0d41e01d55007031268030b403c010301403103030041410509002c3c0d1403444665150800109a00c10140710f074407403003000e544900707403003a591811400c07850103590f04144000c1590044844c0b60510345507001d800350049109210405140003104262481e11204a2080394009045100c0040d40b0701c060100d1540701d544191054441c442004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 785138192 1250 785136942 785136971
    0xf0e0414090115061b0209040317040c0828060b130f0905070509090307060c05090607050606040506040b0d02011211040e1b1c020304060b03030a02030d0b0a060e13 72
    0x284240c11a038000600f5800388604440c240c0b1075a04000c04000c07000500c01284102000501c3c101c0380c044504080d0f030303543c034a07046841d0f62000c1a09207030011000240000c0042140021003590a008180d6401030040000042d9021140c221280c803a231040310510040b9070207074049440e20402801034601001c141449030150717105d0202c10392119950b18008030a0200074043ea030040c24007102c0e14440f40c1026840156030340030743c07230000c2c0c807407552a040b66032158003440c1121030140e030280405272108001d041494440314115031141c0a50304000009070b40c3d144c648108425444010a0300401035840d03001100c2d0f84800301c0c07141446595442800e02d500d9101805030000f041c0c2e0501c0e5400c01d103041c2c90100d050b01d00c170b10320903280f1a030140300c0d1070309040340b825440c20552414a0010303202e0b074442c102400980301c80f05500b5058080064214844d9a0105c0103108001e034a100912403590460240702d4007031114420f10700028003a4506060302d1405442180d840d604483c000b00e10309a4007610b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 785139442 1250 785138192 785138231
    0x2f1306180909030e150909010e0603060414010615170711070b07020a0b19021228050d090804080106080313050405190204080c011103030f18030d06080d110d0f0e04 72
    0x32171140309000c11041010b1034130302c0d04c5da03002d0040400f04414034140140440e9480d074021708003c10300e084c032030300c403090601c02580400d00801405215810454503248050245941100c01c403004400c2d080004010f42e01034040c041030300e045580100007641c07500d0011f40c0650080350040342c0c800d0000800041ca04000000f0700303101c0c0ca00900c0da058555600030b0181c5002c1c10380400d103d5400e420703c880c4410704011035a03032095464416201e10904141c54045401d440740009074043d04d80303030000d000203000380b844c060021749840c80000c0103000d480d12500e41e5070780101c080700c040e8160701c0c40081c030503810715405c110f400002000b03590140c10071305070700002a60456045100a07030300c10700a40c0f1166900c1080b14058021640c090352850030b00101003a40e40e500107056040c00300e429144483c5580080007195280e1303080c560202710045e1142500350b22050003000c80c0c070001d0502d0184648681000c0740035032402031580c07280309401d54401000c0e038a0011200c03105174010790390441011594055040c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 785140692 1250 785139442 785139469
    0xf0c0f2001020409060509070801030c03080f0c060411010e0f0d110f03030c0102030f180319050c07060309051006060f03091a07020307170415032f1306180909030e 72
    0x201041702410402407041c2404020200010098501c0c0100702040c3e09211207001d680c1c001000c0ca03070f1404d100503406031a102e03030020610300b44100d50800082c449a414101d200c06030036030b11492841400c10070800e00c1221011f03031325840100307000c0303c200148500340c070300000410103001e41000c480746600003801c42c0c00a25a00b4640c0c0d4000040040100c00110390f640e0040b0328203204501d22000c00e910958902400c01c0080041003c0c0a035404164042d0040d10480c11003101210204c6481d100020042c00510070202c50b68840c6210b0f05031007108a000703000c01d980c0640d44030034100b031844404030060000410252035610210143e0361015040b072202c00d1044a42e60001c42e40c5000030701d05040c0f0480c8104045909070824030051102206415460551219034170340451409042d1130351044800d2801c051442181004c002c0c000404070030320150031600490b00d06a218165101c50a4420844094140001e115200c00c2400b44c01190b520000c01e103402031030881d0710045c2c410041100303100d0800303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 785141942 1250 785140692 785140709
    0x9040603380408040504021305061909050906030303040b0403050702090a05010501081003020f040c031d251a0c15010602011b1718030d050a020a030f0c0f20010204 72
    0x1141d0038103461000c95544442034418100c0c665490591a0450a030240340900362040e50006862001d04015020f0b00010b420000c1085584010b02d002041c1c00200025082c404a03280d004005440d00e03044c11100d02c90310028002c0c515550395541c856190940051003142840310502c0000e016032601c824541c8540f021032000181541444005440504d004007680e0480d54409018401611003140d2003814907800d803000701d10260505416406045042c48004400e1181c20401e07080880009043c0901358004075800200c0903400703000010001c00340240030f0421213003111404501c00f060000d080c5400380b002a02c04100c070000f51607280d501c0070307405100182c4d151600403480d042c101084460181c0c680c1803592060107904c0360400340d04802410082142904000700f10745000074000c4510003140d00400f00228988156507100a40080b2480f4002070314050310700504041d00e102e502ca80b20119100c034102600300c0351007103070355001c1703400d007844c0d00c1a54903038004d60307403000740042e001500c03161 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 785143192 1250 785141942 785141993
    0x90308070605041a13060209121b0405061c02060f0f030405160b120610030905060a090c0e0f0f0c09030a081b12031303030605090103150e0106140609040603 69
    0x242050003401070018090000310207013100f4031401103180341403441c00b65400b40015881e2031380640000c070482c03c1d9400040f480c2c09480c101c0d981c484010158148031440484080016445840500800c2c1d40500ca410500c18120790103c4050f1400601034030341880700303642c51403400003000745800f46600b095900302c0d01603200d20041c28805141076101000360034030264107070400704101c00030003a4500103000c05000d4050364038541c03421842900602031443d0850200d50048c108001688002c4c09a17074800d9031100840b450200e00c0f0b07081107000500030b080c00140c051580d2200000c1c480715040140002c001000c080041101e952005e00c407409445001c0c100c80343c1c8074010010920304201c128100e441441d000150305140a4080505407a04804410240039103205589815001091250005a84500c6901c000020401003222014090340c01240c02d00c00b1301458a0311a00b40c0b103540c0611fa106106e05841100b481c00e0000183c503110000800100300556a6100d40c1800012401c031901d100411 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 785144442 1250 785143192 785143201
    0x7033b03010e06070906141b060906090307020a060f030e0f010e100c080403050307020f030d06051003050106050f090604030618030f0c0308040b091024080307020d02060a090308070605 81
    0xe11550280b000e5041c083c10140c90020002011001303940245001e21020489000b01e8048840a841c0c3e840c00071001500b0000c0594022075a032001120038450794400d030343c00075620600c084199100142e0180c00c04030b0180c10070b101980e00e480c0e041907000c209580c1c0d500540804104100b09424a04800b000145166410344018205580c1c2c0c01c800300e2440c1000035070f5070090b520240195200b60907203030407034590703c910004074244501074440d41a144004940003040301c845600c407008480040f03030607a1212240030380c00d4082c0c90f400d21039240440c03410311074104942e0060f8000c203400c62004000b286400d45030380d500d404480400c2500444100126496420103821100200006007942044400d81c03034259001406d0410040c00200ba007064034020030340c0c001c0200100300c04803c201d0024050360780ca07688203038008003100b007001241c5002c244000030101c00100440359040d07000313040c03058000800e03000d000c801ea1180d1801010001c04c0e801c004085140200038240e4a845080c001c24035051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 785145692 1250 785144442 785144449
    0x5250309060207050409150902060c030d0c0905011e180b0d0c08010506030f1302060c0d0f09060e060d020f071e0c0504020301060203030f07031803030603050d110307033b 75
    0x9844e0890341c0160700c1c1901c907001040c40040426507010110002203491191440032903658014010711000900c404200080104000d41010780c20700b00342d586818016580d5001140e005d0000c000040f01d00210320072000029101d21741005684602906001c4000c0d40c0d004105440d502c0318a4031000f43d552507440d0300180394440c2c1442d0041c04205c4101e421400d1111803070b810010040c044505035042d4844220454075802e081c1d84030b001c501c1c42502c90350380211401620490b0000313900400200e105202140d442d0240084c030310241c001504050030480580c51040082d481200d5800312481e041c001c82001800310741d0304269100413221810b40d109068038290180c0d18280d088203200b03078014401031000036400001d480c0d210711034208610040d00c81c108242c0080c2010304040101a0704e0030765540a054043d00400c088034803c00449040703208000c0100c0d103008064556102581042101c440030a110310741d61220b024240880070000c0750031100d14a0399143c044c10341c58083c1d9100c0c41d410302c0b514 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 785146942 1250 785145692 785145703
    0xd02040801060b0702012709050a02090306071b150609050c0c070e060f04051e09010b01110106050a1205070f14040c031104050d030504030b13022707052503090602 72
    0x40510681c1085a07a50010302484010f10b4120400d44e098511620207c1900f11640002c0900000801442c100343c02c090b80a54407041e0314501130300c100400300300480d109403000d5900c41030144000100071569038500c03115030404d04c0031a240c1902c1d5900452a192580b01d114005c107035524032107031b0707070030004d0b104d50305201c0c16511500041404c0020043d079a01d810342001e0351240c0803640058913039100003501ca60f2071041c000c0e00250b122a0400c000031030405611034800b043e400d82b94441e0400b02403074032a098030058000c06822020856040100920b00d401c5000b900f4030030800d4415140c1c41e11416541904160f100580a484410300c0140c942094400c0905405045c5070901000304050990362051040e0301c0f038a401072003000c480300c00b450320500940d0041c541c41030307802e9007a007445070107500c0d0480d4070001680318900300003180c001c0038181940b802c540c090000c032401c02036403070780c40588181e048030600e020a0740900c00011091030f085a41011410300c2521598100f50030714100a00c0c08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 785148192 1250 785146942 785146949
    0xc0a0e07090812030c0d020d0504061508010515041d0615150a0f120221060a0e130602030a0905160e0106032c19120e100c0303200d0204080106 63
    0x1d41202d000380c03e025680d44100c2c0d1307029000c1c01c2c0701540c880843c82174000900c5190200d0000c0e84c944400e110070440a90050031810444042d4a6242d64a84030420308030b030350942d8860700d07150b4210f82c004090300f415007040c403821520920900c4840c5910403514102081250310140c49511140180003600d042100790642a048456442c14001e0350b040140608291040340404c2c491a00315580003291640c046580c1140c0710040300c500080342410b066080e0b0402d0b600d20f4480c0340391900100b0210000c240e2284107104003800345040208a80b1042c0c001d41c000341600308201d1700d404440012480c1044500798290081080c0780c002d52820100c0c944161042c5c008004260030240d202405810340b034000710a454101410f6103080000502c82c80c5080350340e1003c00301c8021610301c59410f01110400344c000880311600d54621180846082000300b65001d140317640400e001c0d08070480401e1181d0f0291610400244d0050840707023140c0450300080c1c000d08a180c1007a50002000d200c0441d083c02003a008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 785149442 1250 785148192 785148209
    0x1030e1605091e0c031f0e180f16080c030a230c0913020405090c0d03050f12100806070203040b2a1e12211902040f14090610110c0a0e0709 61
    0x80b181044018446240050711000c1b441d8110400c81240c0707001406142c00d40c3e40b414042b94a500c0211741c812075891100e10031603503a8000c417042c9484908001c00c44904895201c200d240d4815000070402c0d400c0103d00101c4001d03407003598114801900c07080720b940d000741001742002c40c040d039982c41040305440d00101801e81e0740e04804940b5905482c2c107500c1880d0140d05080c8992039410015954506000e40c848601d900da02800c1171201202c4181e0007001680c50f080b050794071507981d0b8401682c0e640f080d8440c03081004d0040062404801100946135607448000c3d13010449418407050b501d180912480340440240c060b0018205550410442d102d20504030000550800d41d540ca4020342503103c4d10a071211b001030090001c1c00030170312442c0d0120405507000c401c540325510344500ca4441201402807030300c07800c0c403901c2e01d55951810a8003140300b208010000010004c10390411140443c05842100b414850003145a5090340d501128002030204088111114a400c400080c45078549910a451 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 785150692 1250 785149442 785149501
    0x402040e010c1b0609120e0a06030c1d0117040b10090614060a1106010920090a0b0a14040801050601090b0a0801060c020f06071101030e1605091e0c03 66
    0x4441d80c0103c10300031001c07150301c24075402c0b501e5030030705502510420900400401005c034140ca806a000001207440c3c10080d110302244c6502c030071055084803905210000401ea01032101e900f420754402c24003003245018900085a40000368507400210000c1d10200d035401d80034405c000740041c900120000030030320400309128584ca0020400903c2d0720640240d1302640c0000748100d20240030720214120701c0d040108481d69503030b44201c0c080081100303144600d100c0c04c090103207004040002c001e503000f90400601003203610307207480ca080b0340c1c1c0c0d03200100d030030184107884030a001d014505c00c020340700070489080081740c1e9103091400100429081d4201e918521401e011182e03440d9402540c8506540440c00c001d005240c09000240c240000c840c0100e034083e00003e00401009510f0442c035104082c00e80b028000b0101502e20740d61940030282107921003043c002000c0110f0300e026160070380c10421028103892401c000c9001c10b203486c8800c46a4040ba44000001c0c8500912f42d80e40c1c0c0150300711014400032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 785151942 1250 785150692 785150711
    0x70509100e10031101091a07051203070305070215070f0309051011090f032a0307090f02180109060c03270b0c0c0a030f080a1206081501080307030e101b0303050402040e01 75
    0x20101d800700b1f09035020360000c6400b50030080108041110040d450070300e207031030340703000d40c4000c0c0940360484600006000d20003219144800c01c1440a00855060b292891240c18070355089000b0030300b0100c107840c5803042c003000381c6c40c2200741d10500c0d031a0300b08175100c0f66980c0400700c01d01503070304aa842c00c2d40c0070341e128002c94440080d091840001c0c0d15204c0c0380b103c9000d140180002d00c0c1c0041604920401840c01000503001c11080e401002050211144541402d04100041d00c52500c103128200204142001d0400013130702c03032018010f00781c00401da200c0300c0115442c0f000707607040c000d6040340791207110001e440c00780d0072010003081070144070840b0200200d90442e917400c000e071210b519004101240120b2140004c03030040309500c92040c03803036508010a503036075060995510117808105648400403070001c200c2c9100130040360350749a055215000d40341c22100600074a21120700960081118405002d041808440840c41901d4001c4d40c000c50641401d00420040f01c603044103000d0242e240a120300d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 785153192 1250 785151942 785151959
    0x3010f06110c0108131b380f0f040302100804140c13020a0219031106180a141e01020301090e0c0d140a080d0606032405040b040b03011103041101020609070509100e1003110109 77
    0x50f04005c01508c21551180d00c003c030b07440b0b070f107004070341000b90b1184440760362050685c0d00c00f26883c4964062655000044c400c410703150303101e50760032420b9a0019807420034006044055001040c8030713111403040b0751074034541c4010184440c0710303d4011000908419031b60510444200704c100e401480703040070705a085003618001e56403110f807554006c0814542d81c003c0583c0040501101d1608001f807052095030301114500c041c001d60090081c0e10b40343e450204ad00800c0c0e0000520300101c80b1001c1d0654050289a0315a142015001855501340e88a00e0003d0000a84003902400c210074800d40041041400c100001c0d066512010410f20740e800c02c02d4000350781c0f0034007001c40c030100c0d10103840015032644110081006001c413408000e801d5801c040c100b240c06034980c5c008500c514000d10f94821070360380c014012a2561000e4031910807503401181d0501c05884c01c0c2c02c405800c85a10115592111394600c0b00000c80982103501400f030b002d19490402c00d0040b503d500303c04184091030004001410040e44 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 785154442 1250 785153192 785153197
    0x110705012313030908010e1e030403030e060903010618020a140702061819030b0f06090c1206060904090303140106111009150203010f06110c0108131b38 67
    0x46042c14000d540d0b0000c2454010742204c005400c0d605c000780311001030b038200981c1c1ca000140a0300b03503011400002410410001c41600c055039070540c0e520050300552410081c6c1d13a00440d240a0381035595080006521207282660030009102c42d001580744e1616010241419101910610243c101040303994010386d1514210748890780c01c0d0845007244511707007000c01c8411888101da65240d4003000307004020300a0740014548039000c42213803040c1c0f0b5a212024031001c50802d94984404d00000d105540c0c944d070010314196030181e0b01030407140c10b00001d040000c00340d038103201c4190040380d6201003110312041902e0045e03024284908200715036401d00c0003455580e200403a40a04a01d07030310110301c420080891030725440a2000c82c029512561100c00c03005030f041d81b5205a00c0420001c00202d800e411020400710502c00c0142c4441e00941e85011440b0400052040304468a41c0c03608000b010003181d1038019405007140010f040e42c015201a40400c00340840c1c07000c0302d2210100260346501302c00c071404 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 785155692 1250 785154442 785154451
    0x281e210b06160b01050a210f140714030c0a030b130f0b161706040b011205070504050108010f08030d1e060b0a0201110705060c070203031c0203040c0b030f01060e0f041107050123 78
    0x8405803480d8082c03c1c50f54030304402a40c000d000270200c104c9041e01a000154550648031840031a5401b000c4c3d403410159202e140c0800c85400c844100c00400100d07103254807030740d401032419490f01c48941c00c1707544940b001031a802c411110300301c8110621070582e180d10a10018810360b410004140c3c0c10b034511078086185d00034a80c40c0700c0c0c1e84070090110301d6407040344405240000d800d0280a5400c0614028100703400c05d005450005140300c0000801c1b10003001101c1c112001400518504030072880710501510045600c7c5683e02800b060719180d41c0b0042c418100148400282c10f916241c0c01d10000742900d24402c0c0495207408180024000f00b1808030f4640d0300100ea900480b9500c0f0008e101003821400789040c4210200c2c6121440c0c18921140c0c2c00540c400c0344200c001c010100d4480c40707208041c1c001569180c1000064100520499000301005204124010091800440004006003e450303049a9188401c800800e1080401909010f4201c408418001c02940c4c10300c001d0b11070501c424000d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 785156942 1250 785155692 785155739
    0x70e0d02060a0c0b040501050610080c1e07140601030213020f1b011523010305160804030504090e070306140603030a05070206281e210b06160b01050a 66
    0xc1c2c003801c0d24020008502169400340c0d1103c031525150814034001c04040742e0181c010851807600c480e01500c224801403040d64150300003410089451038050842e8880b100480f0030a0003000781d10007080003900004180d0b910b0900800381581584184120604a40140e100d642d00601c00c0010300c0016606840c000e103d40c2c100103e00300040348403640540b04103415909800030074640447c13100b041d8505207892216004482001500000044080342c1c02242d92107e85c02405040c040b4840c40350b00b0040c0c115000b032922600381500c84422000301c880040d00c0400913400030780100100300300d6005288650002401610300c41c5803610100e80c90b403294008440802000041e110210340d40c0006403904c0050350b80c1c604040c8044074241041a001c0025a500880c18261800d072411840b03500b60002e1103401d9441100311100e0a9030400c1d000d590540d80040c143d2140b00c440300c00e80700c3d5000303032080001c201c5148845000780e06004401e004180c003c2130140c0d02c141c0041c00851910010204007102a1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 785158192 1250 785156942 785156947
    0x1906050c01090f150606051206091509072c010503061c0b04030509040f1b0f140c1e15041403190806040c0903260d0f060905070e0d0206 60
    0x80c9100d90040001540082160303110408000611524005040c81d079628410300300462600c400c000d6a690260301c0803600e045108500081003411300c0301ca0f65410501403c2202005889940010f4510303000f2a0003a0000d114008034518610100c0390504450300c0140754003035049801000242548801080316008031900103081d81c0d03405040c00c500ea0900d0300681881c3e058103107841c00038440d90000e080309100b00d0401504440034591840303041c6140307810019204460a41c118299616442007005130140591a0280801c4000140c0186174020000002d8802103c040e5000420003c1e60944420140e00c40500480d10580e00c0c080b45801c15044800f08071401c2c0f400c409186188605041c2462844000800c0020290018611402048111000e102078010203000f218005901d105c06082d080710600c1f5060018141315a4a2620164212291600030f40d401d004055a140c01840d03034481c1d0f40c0303842c108034a055922419400980c1440c2100681c192440082c0542d144003801900c2510b00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 785159442 1250 785158192 785158207
    0x2d0606071b03080a02031903140105010e0f0d1128291809060d080d0b01020708060705030109060605030c09010e040e0106030b01050312160308090a020607120e190605 73
    0x4600340800110f42c0020100c1d03a8081d038000094890b0001400d200a004107010320068980c0240108001c88000320320790340380c585c0b0381030045500d4111060016000401904d500002c0c1d2103c180001804e0300802c07910b00d004203654207100c0852501c3c404004c1034085000007280900480d0701c2c4000311040407106001078880100e119460380070b0001c005c3c1030110001082040408035020a6103407540451b07600140755180d174144000550211801414200c0401141e07a01c200584d100000381d40e018811210855210503450349091001c0c2d65100100da0040b0040100703000701d005603400742c00903280103800c41c204210030507070318050224110305101040514001d01e80344d5502c0100080d0103403000f40b11841d03a034246102c50304420f000300d40c024028002050b43d40c15200781100c02950f00c1202083e007003031007510202e03850100540100540d001e00c80030103001d81d46850140c540680034034140c103440a0b919201a14504c03440c000d2902400c1c3d0029440c6201041d03c0700e81080784d0a904045544018 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 785160692 1250 785159442 785159483
    0x50402070c121106040603141503030708030a0902060c210a0806090424020a021c0206060114070507230306070203030c0a1b0804050114040b030a0c020a0b2d060607 72
    0x9951189070b070803942c08a00007a906d41d06400c1b48046100c540c200300083e4551a110007a010b80040449406a10800c1000300050610f001140c4c040c02c1840700142c6a00d107035000541c10345c0040c1c41403d803a40100900128414130f81c0f10242001010000280f0303140b2000006410f41000402191007083e04000107000d000d15800e143c000090075160031580010207000c2c0341c1c0250495120b180061140840032510b40ca108541d0303020300200c03600107281541d503c07401110f03000c080d0001021164401e02080000400c2000020007500da0900b1886030402203909545451081001d11b0740709034030050901c01e8854000c012250810440006079503201d11900d0140c2d03030f0000000c80b1300c0035050307000e4044007408400006042074460903130715102c0700550f110f00aa8140034a002c0d640d0500410804228006c01d5544003824111040c01a240250425280c0001c0308004894a550100036040d000142c104c003c0d10001840e000303c820140141004001315126010302d000c010100c58650024503140070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 785161942 1250 785160692 785160713
    0x50402070f141e070e06040e0708030a02070302120303330d1a0c250f080307030501090507020712060b04090516240c1104021b031201050402070c12 65
    0x1500003a9911204495010441c0d907200d03454881219a122203980f98010f007404501e0704110750440080640f01d8694078104801880800c04000d11885940d400027081801480a00624030040e000341800f1407450061002400c014490500d00e0f400c1041001001a08041c0f81c41405040407120008030340305d0041e24500c1b44004004545c04a410031480c0100700300300800314083c0306003502021840e290b00c0204c18844c054804a180d00f24144c0c5102010f43c030004660003e0680910349030190004c59494044d565172083d0f940c44006901c0e4001400f0030010790043d10303002441e510007441040d281180d6800300e0541880e00401481c2c44210200e4685d039650007050003190003800b43c682482200d0314071074071084136204e050b081e101c088038092602c0314103c851601102e22a221541c1113000307580e543c0f04800f41030780d01580c00399082c0510320780c13120381d5009174205403e035100031a03903111001c080c901d05040c164422481140100103c1001400080d480c004035000b40d000340c10624050b140950400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 785163192 1250 785161942 785161973
    0x3060a0909020148110604030b0f0c1207030917040b090607050f010e0f37030306081b12010507051c0b0d0f03030c02071a0906190201050f0c070b0105040207 69
    0x20403130780d621070b28805140c99030b400400d01c00c0c1900040b00c6498010310001d07000d50f10024002c2c0f58440006800c1c110021070041e070045507c05541d1911407400310420351b002040d46c2c101d00080c0e50b000a80108410000b90040641a00d207059042c18078182100d41103201e9496494050760002c0b610784200a010008400d84400c00f100a0002e80c40c02400e4a40d643c016070040c103814800e03031607107008600982103e41c15480c40b040030300210b60000250558404d100c22411000c05680782d0001840408c1403108200a014000c10380304122007000c10001c40e0380901440314884e914003414464560340000407503103a100c40201000808082d000b003007001b031910000f00b941050400d4160f00400040d05039441d4501c5c481d4a0400000c1c3c40d40c00304036600d6580e03000e0303143e04018424120b000031a0324405442012801001d161500103000712644c0c02d807040611290160b0744860138000d0101010344030070b501c100f11540d8181000301d07984a8890451044c423806004550000e0384000340002c828081a44 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 785164442 1250 785163192 785163287
    0x10080f1c031d0102120f130203060c09120d270f03030c0f1713060e03060f10030f0f03090b031504111b0c040e0a0201080a0506030a021503060a09090201 67
    0x1185080d40d10407503504170071503904044181200005020007050042a2410341e000b400408090303480208144c1e450b803081c0c1c00b40f580000c00e041d030f01568141c2000525002d41d09a03039400780b1444401818119054030541c51242404016020301441c500102c2600840350140782800c001e80040c2071a100c514211040075009410840c034082c241020800280590703050000780d5078005a50f030008071030b201848080d856142d0800001b1170f9420500c05481c581002d20340c4015100f4958a83d1100c3c2c88521460044a00350520300b892402e246d080904540203103210b001c407900d145401e002d601100450341c0302d02d0b403042c0d90342d07040c10480d080c3e60802d40c0c5e40c0c01181c118034450703507440140c1c1d02e0390740007a40e24081c49641001c0c3c1c05d600030707940402c0b06603109074107864103819500ea202c666805400000d08c0d090300751013407440da4009a03a03940440c0800070115202240d4a007022403c2c444c00b8101600440f01c0ea80c185034100006036400340a20310406150740d00d401103d044110750005c05011040780c0c441 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 785165692 1250 785164442 785164447
    0x603060439022e061a07030207050a03050a320624130c02030f0d020c0d0237050115090b090c070b0907090c030608071a030606030a1410080f1c031d0102 67
    0x10000411001b4540140241c00302c0300c2d003507958000c2011580e481c1c00002c0407034204900c0c0c1e1000402d541410074000c45051a501c416050031502c42d00042c0c024640355070541d010109000d01808440b003601e10744036884d0950055100d0080c003094041005603019600d0782d6946034031000440c803d005031540704a2001136140d6a56030038218901070740082e090003a590060900045003140006034160b4202c07404446d49034006100f00281020014058400d101885160741d480d00291013881424060442180d10280d61800d103500101155010071ba03090262500c0300c1480030b80c010110948041c1684500854002d56540709100d051840c664011b20f849810400100295070700350300890301791030316403040390310789950303807524084508065894440c421820030104030311b400d18000466000c6503901000ca811880440002c08114040b504441c14030358031441231264510500a41054a09840c01015880c2c0d2003a0410304025100415506250f95142034000d902c00da450200d007070102d044000c54 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 785166942 1250 785165692 785165729
    0x4181734021f110619020a0908010c03020408100506030a12030b0d0602040611070b0a0c021c0507090b01020c090f0711100e010612080301050603060439022e06 70
    0x114011400d55880443d0105110b503c00d0200040d110b8030484105031820a03610f080c00420000750310084501080058010380442c0184c024021100760841a42e80142d46a18085a650502806042d035288081c01c0030705111046d40c0026140306e41b5908605020000b0314016000d8000b0010400e240360803240240081c41400103070750203402128019215000b03001754500c00117441d070b40d843c004d01150540a21005d1040da100d100d95000203032000c0d140080820003140f04440040001000b164141d008030014021500c6900808030207000c20300040c11123803c1100002c1240070000c2030341c1b414011140001d500284650520b610611070402076440890036881303144007514000740700751403641c200306e0b0000b515034480c0c0c2101106034100705900d0640e420081042070681c00030344590b80c41520380b40c0c6141000080403528500703102c2c640c140584000c1000c48800209800f14406055402540c0d0aa1446501d8550814200c801e135401c102e00d070402c1c60b890340003040103800c80c8041a403410346c0710 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 785168192 1250 785166942 785166979
    0x411031828081312030201050708090f0712050106182f1801091e09060b030106080f0a0f180605010608101206150e1b03040314180418173402 62
    0x180200c90302d0fa01c0c00c41d2b5655030080b8070f40d2003510b10240103056002072f000f000312010317808401c0400d5124500128140303503642c1061201c0900083c501022690f18659583c3c1d42d8003401410030104c0004050f0b002614030301034040254000c01c40c80c0001c000d500501b54195a101d0f5a413000545032020a1416626024007031511924440c01500d580030f24110010902e80313090000d82c1e041752070503a503401003a0b032019840e0248480c0039150280403501d4403202901c00d440d6000f0b00b00d85201441c80960808118101a03081c0c7e00d060741709805005041d000e00001040c500b207914240c3d040d119244e411005d03103141110041c030000020810000c1c032940003041e0321240000c214043d54610b807545130402252030100c1d07018403040e58000c010074158001413051600c01c40c0900350340301c580381c1242d2030412002c01050649a03001504c81c1801c151000502c104400003a08010b66000d0a680b21f0801520402c0b003105401c504080400f0700c000008180c801c03034420503001c131000398058400c1d603616101c030031103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 785169442 1250 785168192 785168201
    0x1205070e100c12120b0a122303040603050a0506010903050705010f2105071d0d0209090c1806120a11090606070512030114030105130305090411031828081312030201 72
    0xc559241c200005c042c151321703001080718191807181030410070325440c2e5070382c541d442c128a400b8a0f20208002020b03c00c1c6600c00d102034002441207840200795803500407140000c540008121a0510108800c21300c0460720019a0f1003e03540c080c00d1038080112807800030b6840c80e031420342d126480c810700e41084034035001c20f80145008251030b44501a8128543c6583c0d1a51409440380540029981d8200005032600c0b11000350000c80c040142ca001c51a40c6011500b804107010201141007074403410300a560400d068200c0d24146560060709115200395501415103001b248082d01c21180140403c4c2c1594a2034102d0340d01d00d80c07103000c071003280c080091000c509401c01d00c01c03250104035a4210110900703041c001ca5114188801c200d4142c0c5845660541e80da800c20026960807070b07902c0740d036507165828100085002d0002064020203182c2e51144451402c016280301c020705011000018400a60100c42040d55070741c041d04245e00d50140107020300341d4602c258444070241d25480300405c14190113501 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 785170692 1250 785169442 785169467
    0x1111b27040f060e031810110303101e050307031221150605090f130216060b030609160911070602040303050721020307060908070f050d1205070e100c12 67
    0x101407243c090190040b075241e001c0c06c1d17680d0810400354050f1001500d07242515100740141810480b5507240c0841031030b49150000c0b01c080c5041020041d050100303206003170304202e80b00c600382050114a810000444e80302c8840e0b1100421003400c0400c52150f0303e0242c02c00c00045007403500250641d0150a59403000703031140100002c00e240440f034004c0388070741c4240d0864a40d020054100100304201c1030500400c1012920201141a424071600700811051500146e110340151700c01300301c208082e0109030400700050000d8100346d00c01c1071400101c1e5a4807284400712445c6000000f800c0c03c01e800d150030103100301c24004050310310006000c410141c2004c09408140d000c5c80d1002c0003200e19140f54101205003410400159200b8800c00000440e660410711400b032080000504004060384d4031228103009240480e1250049000050b80d1503001114400310b4003100d50502c071174188204003418460762601032600510080e03403510f203800c1c003031403860320165881600400a5048004020810300d25981e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 785171942 1250 785170692 785170703
    0x603060501020102040b090907021e070305101b1b06060e09100c0203090f01050c031809090c0117040201170a0e0d18090b0a080703030201090201111b27040f 69
    0x2501103015441482a54155240102c0300381c6031401501c1000040d8500070441d40440c49403a0003002d64426181640485149143c02814001d0842c500030b824010541950480149403141c480c0150b0070780c02c040b000400c054180142c1a0031201c6d00c44041c0603040307074060076040c20101d001030001650560b0500c201e18031070035201c0410380b107034502c02514100022000180c6c0140800803440c513010407507405044050520620300355600765298196042500d01c56218a440743c0d03289143e0611400d66a072002c2c082000e41026271026002910303000a0490703421100031040001011a4002e0707025580d24000d05420395180c0c5040c07a040406004001c0460030031780152455114603d00400002200c400040100c140e01c5040030244001801c4030000250b1102c81c80c034001500607424010f80010714001e90020517003113503500025100b8400c51655000e82c2c3d1001c03564800014049000540b550800c590008260704180201e880c42400007000c1d0303441403103810520040004042c9500210b0348100b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 785173192 1250 785171942 785171951
    0x70f140a300507150e030726010609020405190810050703020f37081303170f0609010f0b070204050a1d0604050d080c04170726010b0609100509040908130603 69
    0x10030b0202c0b00c0d200141c2103d900750b072010300c00707200c6200d00384140234030030042c8045c205816242d1080766003900d20541c0281e4030580d00140038081d6081039035808004a1b401c200c01c00105191a044646d280c601c403104c00c0c0d4480c3d40702c01103a030a5129070102d40240901880c65a180c8421034031107001c2d560880d0004410610941c8007071241003192007002d501c81d080342ca42807100d50701c10204460640110a0440811907044925101c00780c401f00e01c18018000034051041615004d02070240c01401a00140358120038504e040000c0b400240481e032060740e050341d010840740c0b44c110039500503000c010500145510903805001d012a03002401c90310031030062003114600e40401d038040c0d50343c078000c0d183c2c0e00710590104000e1107254912050b08000404400880701e2856232980f0007060942c0303900039510000546030300302e07c4403402400342007882c040032101c16107400401c0c0009030481643c10711100a0000206205609a44650085000d01c1e0880701c0c41d582c0d18215400001c009903640504000310749003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 785174442 1250 785173192 785173229
    0x1703090114270c09010f090c050403020924120a06050f061c0c0306020f0c1506060405010c060204030203010c02012403050a0b0405011d070f140a300507 67
    0x46241c45801000384901440c1032000a070180d0902e4520302c0a000c84a11440000040c2503c4818880b4001c2038003502504015083c0203001059611131a00c0e0310400c4414401031016030394452005410929141101086034001344500070501d04040200c1d40c4001742415010b07040c82d0100381c103205540300b00c00800450740c5110300941c03040c00039540160880c4200904001544400d20400c101501030080000d41c030b0364036500e51041e640401520401e004001c681c0c0d21032218100f09200d0b000888906110b02450484045040741c05140315590400000004a009104160341190040c503000790080c040c0100f00e640190280c61680c94462807500b041942001c1c5000d40040c001c10349500c10080d02018103941c98020b0802c101030030540741c95580c1c1301010105441c03010014014400d02e0040c1004628060304580074030402d6101e981858800503031415281d07240d40421054541780d040d00504c004003500300901075200c68803c5148450b01c061810148140040c0c0d000c2252030a10804954442 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 785175692 1250 785174442 785174471
    0xa2006150603130206090d0f1101080601030917030c041e0e011203120b0a0e040b060406170a060903020c030d1107090606050711011e0c1203151203090317030901 71
    0x1240c0f099141001610f0500051030030710010131030500d000786800c01d9400e6546402c0b8003892201001c589617810b8105848a958002d001954010003d080070000320400b502c035184419100d0600b041080c2c0008001034140c41c1610646000d0441006200d40709103250202c078050344070701d001c0c11040401000000401001041079401c0d07995042c1c0d598844006409040406032151900c11a0302648c100d001080790380601005a200314050b80203221103007400e109201c00c0b5002c982010035160040d58592840c00303000109003400942c49000040d40c402c6504003282012881e840382c139454000e4146440d174040d84240032000040303010040d10f482030b41c0c4c1d45a5a003100c0c4548202d0000c101c3c20702c80c400200390f0300290988402d1041c1040104642d1070951414100003804080d000311341ca141035002401000f000c1082014000c1c2000c01010803000d511030b655100f03e12904010400010301ca008242c41800c001d4011580128101c2c0c4060102182000035001150401841e40c0f030046081e45100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 785176942 1250 785175692 785175697
    0x6020304141c1502070218060f0103020c0703020f0607050d0819180201030203060301140a092a0e0a20070615061202090102030403050a0b010609150906050a20061506 73
    0x484002c00d589000d4a40c2d0ba40c98040008401c092005034203100c0e040c05611035101608400c01c1c00140d00c1081e2400004101d107000e00d203520181058410b024442010100007040c0007507a0b01103400500c07006030140010031911a011008150f8000d00013200111600300b111140034001460711098011002003061085070115100d2802c022818801103015500030790003550491806000458a8860711a03410321000e81900d0f01c9941a60b140c004ac2e0038055050100c09012001d11600c005410700e00844c4030500400c3e010b5020f210001d6401b003a0782000da42e1141032400841d220303000d0244c240186184650304954800c1e50382e203041c4410170b41448c0c002d048200c1070300d406845000b510281003000800a401140c50705066120800001c000b1480400c80310032510f1007180b942d0141d40c1004402406d140003a4050744c0c0300306804041464990308002c0501c140c0c0d08918001d501c0d02d4100380101c0701151446940c01c000011210038590150021070140c1c80b5081403402c480782400e00e9401c0c000e0b2803 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 785178192 1250 785176942 785176969
    0x14100f05090607020d0f0b0709050603040c062703030c03200d0e0d0213020706181104092d03030e0a0c090c0c1b090506040b1c17040602030414 63
    0x5a0204050725861400b40007400803d80007a05190410303e1903903c403c1201042d2000755a0040c400b81005443c44d0302220600c013410007500c4003411070905644401c071420340d0b80900c100f48030b8601c090200d4070001c000b6039501440203200305044940c1c0c9007806096400394440c113a0000d000d52180126224041000c010282000b1004001c0000d903003604071040c00165090990011222070b11001507541c00d03d06250003e280d0600680c1c0e00c0d000d244c010200c42523600b00d80d002c4805000403034049010007180e800148800d4901060100702407921040e103148940035000031180305e8070001d2800720680c00c1e01e41d0052007524200402c0074084481e65880b410504020544d041c084001d21004035039420441c03001d0018184191010708581d41c201380180d84002102200c55114410440c1054501929420400999040101024540210f01c0e84201c1c040c8a5808003203c0c400c0300d08000d00801203404952a41c161540c85544840000b502d9a000c3c0c8600010407907440e007485c0d8246460704581850 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 785179442 1250 785178192 785178197
    0x90e0c1e03090d0c230f011a03010b01080702070608060414130c08010e03040923040503180d08160c0e0702010e0c090c041a07020409080a031508062a0414100f 70
    0x4440c2c1400741c15804122040203004180035049024011682c08d0248034030800c80d42c03181071038841210040c9421560b07110103550402131100c2c2800b41064000c6082c0080c3d851078074190341c480e51a240818040c0120544143c042010701c000c1015203480319402c102120701c45d034082c50441c0d40e101e1202c0e00742d6040e034440c40d02540003000108409500c40d8451801098075a071602409a601e661030126424100c4040da40742e0800208550501082c00c08250411401c550032400214107860303540003406043c0c01040d0000344004104144814181d80740010254640c200201d440c200c43c000f406041260825100c9214010003900c41d0301c2d01c2e4810034412083d03003a800c0c1c1058234150400103c1c3c0c117200d8441090103010010500583c0341c0d400750f4800d507809008255903076010b4840040499002154000621110f0102880951008126950802007204100300b5110713064a90050751100884411070040300010005510305070714070500401c0c2c030102c8981c076280700205800d5400c0003c900c0d41c0b400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 785180692 1250 785179442 785179463
    0x1081003111c0506012402030c0a080c1501141002120702090402011103190e030c0a150215090d030b01020d092106050910050a0903090e0c1e03090d0c 66
    0x41d0350070b150042810301145402545a88020340e03d6142c1010713420303000701c000032844807040e0480101042c804611104c181c402580f030010380b403802c03949407041d40900a00c0e00c01c0010310080316040400a44980c0340c40000428040d5958801082e0b00304c44201c0781d24010300f08030001152590010811400500c0c680c0c40c154984102542007040c0050004c0c0b040f410300c20021103401d52940104041c03c2d013000541d292a01403561050040c0030800d00742d5104d44039900c5401b03c1c00d19074540100003c110340d0050104580d514807410140e0800e400080d540c2d420038500e000b00100b01c0c4000400803210003c41c1c6040107003950b88001245c440b028100d086002c02e03050102042442c0e40140740941914040180d00000801075680d841a62401c2d1102c15299018044010850245208494000503001d40820045120b070750094407a402c984a0110b80c0c1d907400d400210500c40500855942100742820380c620310309a45000c0340190001d0b94444020710900d0301040707680d0700640e4010700450700700140c4103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 785181942 1250 785180692 785180723
    0x70f0201110301170a1a04050606102f0d05070218040b160507060203190c05040501020a0303021b070b04090b06040302090c0d09050607031e1109010807021207030504030201081003 79
    0x104d031500082c04010b200c0c42100044804110383d1007402540b105680c03c080982e09007800c085281c4031020305207d2040c010005809a6070307402113220900329180f03c6510041503c044141a107040170040d4180b40c60113903440c03825031a64030000901300d052003199001502d4501e4105030f01603290072a4010700b640000d001048140e0025490480134900c01e00d4011b15060ba07581d540400d03604151642d91141060034003030409156680181642d10740c5034607010b4241854500000c0d0345205240c00982419400104000b0003e550414006160188001c640310341c0c1c0d90b000400c107a03920038460f81c1011860601d006030b452401004480c02c0342d400800e00100c580b06c00d001400d0720b5101c40c1044c084ca40d45e50b51028000ba03418040c5d24030583c03050f100040d016000e9900d00242210040f80d47c1d40c0e0341c0c9049400f11240d0a503406483c0030200c01e00c1d050400340d42c4c0b00c0d030603841c02c0d07200c0c107ca440f011004a000000c140c2c2c820021300c01d43c0d2003070b80c03038900f141c6846590b00b4621589010040480b0a0000b003107 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 785183192 1250 785181942 785181959
    0x9021602060705010213030b0402100305090d1d0307060906080c0408030d1e050c1317030406030b0109033c020306070302031f3c1203091805070f0201110301 69
    0x402c00c4a00460006181211002003031081c02c0055100700c56044c0180200029481d201d080340070b0a0a0a090510032440e0440c0361584940200c0400c40522080d00c014040700b018184010003400005012514119140c14001d0103031001f9100c1c1c0ea001540c4540010036851645c4207407011aa41d00000b541400c000210140141071088944030030b50411000000240c800b81c040c0e01c2c003407005c10340c4295036807103044140000c241c05070f080404008003465810742500400400c80e03080f01c5241ca00000c80c40c2030200100c1c0e014030680d00203065840d502079651403110480651104c507440c50400907109247c12401080200800d000182d40750300003600203038400d8005c2e0011b5a020701c5190499003c006845010150f000b00c6070481c1001a440c40c0505052100034001c0c0444402ca480341d840d02080c0e0350b80f024480300c400740183c01d03004038051000c07001c2601070161180a00075440c2d40c082c985152001d101c000700b030119100f07030000301c0d40380b030300314800e40180f02d60f00c1140b403403485403480c1d80e0804940c17 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 785184442 1250 785183192 785183197
    0x31b1020041a251e0c1a0f03071e0e1008090118050703021017070e0102121803060604020f0406030908360306010609091a190501090902160206 63
    0x81d02d641c2d1002c004541c0d002440440346404a048855045072401c000e0818484422001000d03440d00b09416400c003002c1030405a29170100c44801281038080030190002c0411030180502e000800c04000c0280135040b90483d108440c03040c1010031480a00c00c00217421124843c001810075040500c00c2c50040c4064420707544031364000d0f540310010451240070381e4441d0720340e0321100055030305800122090085180400c0c121584641601d0003040340c50040001d040402d4028000d0000d1005c0301c0b010341340a90090014208424904803220384803000090000e880a03e22076003144207008440006a40b03181078804d90366240d50800c4261305250a060080d0000d01026074240c0d0000c0c001c3c003100e5a000002d41c41c0e00640700d0802500e6100c81400a50b040f002814004001c7c800d070002001444080c0e0321410084c1101c800079408110b4582d0b4114954000d10440310b0190000121410250007400402c001c4086a1081c1e07070b00700001d07945000350700c00ca0040e0000045e050007401d43e104050f2a00f01701 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 785185692 1250 785184442 785184479
    0xc020409020312030a15090b0f0d030e09160e03010905061f03020909030405030727020d021b0309130504050616050409020d05250c0311031b102004 65
    0x88441010f01107a5800050300f00b03c40c044d02207070b100c0048400d0710409421150042022490a01991100304001814204061f00300c50240410103a4001414821400c135500204080e02c0c40c0300701d040201d044031000c070400b200100800c4084100000703d040c14428803100e245c0000103000151034a0311000d1480c440b40c4075072240111014004005a954248603d004100c120700650307890b8540420b240c1840c0c11030744642c0900301440c2c540c0e0110f1030301d6009030a003441000b0f0b005030781d482e403140c6a1000f03002e400b0f09081c6180ea1440342200c140b90001c000d224111040b10500845201ca09082064460454004001e60041004035503a059112151101404503044c0746080980f5900c665089800202d03408200c0f0761103800344180a01d81d0888102c02c14004a003440341c60001c008040c000c2a80420010708000500341e515030100e0303050056488452000010500012500c0e410036039801340784201c0b00b071003483d10700410303070341844440448070303420f24420005d041a01d00145001d03510340404 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 785186942 1250 785185692 785185699
    0x2062401050d05090303040c050306040c1806230a1a4006080a0504030f080c040f0b03060f0a08060f07091d072c0f03030408060705070506160c02040902 67
    0x80b070200c0c0d0310101e00071075116006000040d40c581c40c06050403541e007a581d9000500035000401404046081455164103484445120080d0314810381076000051031940e112041840c03586071441400035550941840c908402c03902d01034555154107818a04070344054a4201c12803007045000181100020f035000c1400030b1114402151043c00159110b4844a100d89810400201d0302840701a40165520750048102e040820284c82c0c26503002d0718400b4491800e40c14000d075240059440307002001110081c0004600f41c01350640e558050507825002038a40e180700d0601841d40818504007084d90b401200c0c3c0e414024031403a1a604605410200f018219808000c51400c0120300250400d9011524001602e0800003925201800804407250301004032800e125034100356080004540207583c00c4c56080307410000641000307001074550f1145a104805a0240d6401c200c1140c0d00140a444114080c0c0c0c189d856642d50a03805141c182200702c001008503241c0305140c8050304090344140c14951018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 785188192 1250 785186942 785186947
    0x140405150f04080303040605070206060a03030e030f01022205060c070608040311030a05090301051509010b0901022d1203102d150f0e030c220606050a030c0206240105 73
    0x60741540c07503070744590407080c0381e684000240710800803288589030f80640380b880074160604109000a403003685601c4061308200482c040c584241d54140204694070121800841d9a0441c1021810a0030103460760704803958042e0000041c0b504205007102c00c0502c10802908140341007510603200d91401a000740c0801030298041042e2701303001c0009010015454407810340354130804040600359100181510044e440744c0d040700020740c07991003141d03040d50704d00403826480e9112000100e14100c0e04980d6000c0e203400200340144807030701b00e0280302801c003219030640e21100740784a8428240e00c02038500410280f2404410032000315481c0040c1c04011041c2002e03640c0d004024108280d441003900201070005046401610745604403548c11096425810702009002c40e08002030785408081501a00604a02d80205001400c1081001140c4d82240c0200441c540b200030007072081e0440034494011a140109101c4205e0001171101d03c540a107541195008080a02c0a0707d1030106d101c1c880c1c1848002e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 785189442 1250 785188192 785188207
    0xf0207050925180311040c0516022106100e0906011518081b040b040905150c1b0a020117010e160201060f03080d051302030d030e0a020604150e0114040515 68
    0x3c5091640003180150302c503070220a41d070702c03c10044468180600d018010b0811800003010900c0e0340070030b03071240c04940740e810300000c03903500b0b60214022001c8102d0b20300444007000030042e0182074141c1959881e45c4c0d0140c45a8400302d942d9591b0000b07009610014014006035595a80f21316244900d00c480c400000c000203a0302d000003454580401d040440220003100e0402c040d0420f44950200220101c40c1072141e4442900da464880c3c031002446030302850354500044101007508204c50030001c0980c030101c1d81083c15003480740c4034140301e0b50407030028a80a88500c2e00040848510b41621000c0d08034400b00d44514107012841c1c920340800c80c0c20355403100d400180f56088d040a2500a5004010a035910100d0f480c54100710342005041400d280481c01031503000d07841c0002c000c1d40002c2e41d400d00056002030740c07800c5450040c0800000758000030000340803a41a074000d40d40800c413011a1031714840601c4040064560004040200c0042c40003844104014a003801c00310001600e400c031880c2c5404c09 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 785190692 1250 785189442 785189477
    0x1602150a020c040b010e0a1206020c07260d08070c030909060803040302031204080348100606050306040f140a020c06010920030604020d09030f0207050925 68
    0x11120480c40941c000c040c0210b2142044d00600d40002d03401d28100c2d914540e0400040c4144080780659082944410800380c00c000351039040721045204442210001d40d41c800e01d05194220010701610411880030301c400206100003002181014161100c048941d1404e000300c5400d000050180c041207600080041c2446044c03056074042d00940c1c2c00fa594950941c010b0500e4411203883d20b00314000c04000401c850031001c4241c8810381c600700340303184181541840501c01c507011030842c6000e1083c842d41c14520a074034040c041001c1c0c044501500c0e1183c0c4c44010340811608284140004035a003080000d4651034290b01036100440501c3c0d000400038600032040d200d45e00100c5404045550015608070740f07110402685005000308d07102840070040c50b500d0340c0d6400c511014011807401011010503250f07509d98060b0789045903921820001e254090070000c1031040c0c051034010160060003000b046a0904038056031181191404ca1802e480c0240c1003d202400300a107108108004d8082c0e5001c0c0780e2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 785191942 1250 785190692 785190697
    0x140607050a0b0901060f1706060d14010c1d06030402030607030b041409150906090a02060711030a060605120d0c08070f020a030c06030f050403021e030f0403060501170303040305160215 81
    0x103450800009417142040d801301d9156529030400c842104840c1d40703c0800340c00008196074468410381c2e40c041204071034909005e0103c008047d5403200e50901110341e00007940b26003e255000010b8000d00342c580004824417020b880182c2e0040d40542140700082c010728002e421240c401c00f406400051902c1e61808090040402500c0c0141540c0201040300396103203070341400e9038000341480c1c0540580d042240c0031355550210303c10003c0c000c82c80821101c051141075521f00e408600c020303003036416914a51601c40c0c001c0009020750ba2244002c024803200241d800a0703410026401904e1781c00d101c0380e26440c0c02c2d44980040c02c044132713111104007402c401038659074004e0f001184160703441800c0c2400d0503409826510500c50302d00790780307213044100700100307900059104030b06207035440c01d40ca00c0c280c12007290b0a51140b01800b050f0090000f030008200190780e40518101d5a98040c200740c0c001d10111016100d12094602600260b01803086a007034011400304007100384e200918a01a01403032103c13256254 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 785193192 1250 785191942 785191951
    0x190b04080102190905100e0411030f0415051504151d090601080109030e010f17070c06060f06050f030a0b100905031c02060a021c091b0b0301140607050a0b 68
    0x207940100d440044418003e40c0b50911500da03040c11184d80d410507006c61598070300f03204030750b0401142549001b030913122030b4006003840e00e40d114203071340c0c0785052055075502480580d07048644801c20b00c40c002070210203110302e80c0200010341c0c0c400140400d0a040101601800c2c1704103d07919404000001c04062011a040c01d0304070642c9034419a1601002d0316040020581c8629016410700005c04000fa03801020490344201c00d00303005a2100840600301d83d0030f440c400418110b0901c80c000d2006064121020132840d610400c4203014407500c0d95404162a101440307408041502801111850500a40910b0303105800401c00500c6120542c002002240d10341c200d0008205000424011400c062040100c42e95400901075101c0209250095441c07000820341d040340742c0d0100324030b400e1005c50780400c1040380c00d00e4014094510941004030b10905860403810350040d601000080d030b10000e005a038120780740c19614603407500d00d81040c0981a80300b40c00880d0580988010640040c1c502800d05014 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 785194442 1250 785193192 785193209
    0x90506071d100c02120c03100207080c06010e09011a2b050a03180506090f0112060308071b0f080c09040c090f090b1b18150a0509040612020f190b04 65
    0x3c2060318018460041d200e02d00c03000154010703544812071a00c000480c915444480800143d941d602ca09190705d15005113502000d02d4000c031b00000038410320940d00c090182d03009400030003048002c81001c100c2d41c11540e02c800e800c000305516966543c2c504400c1003400b92002c01d01d680350010350360764450402c281c000c0110b01083c8090030300360541001d60140b80c080c20050707580a241280000c00550b031650707c85a818100041c0041408415082d0340000004552105001d502c80328107180c02400d00068803416903801d0400307040000c8000b1a005480201c2e034410016054000003901840400d0b040188180c03490800d0400000b500031603441a20644119200005041e034002e14000c4405900034000d442050b010316901c0c0c0344001002c08940551300a41080b0914410440108143c40320250666407406004034901c41c0c000e40000007003140c160201d0341001116210f4040c402d194107500c002a400c07015040d03030849103041114211030059500c40e410007603180d030f682400300554400d400c008071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 785195692 1250 785194442 785194457
    0xf050d0519030c1b020a09140411040b090c0703020304270b0a1d1e1e0f010b071b0807140102150f2706040b0601080703090506071d10 59
    0x9040606103000070403401c1c103203002d00c24441010341c000c05180c0c41840b2140410002c0354008110b54800100c1002001c020703a0500c403081540d506c010030210300711000e540c0b51180070440b509524291080c00307510340d8000e0000280b0303284e00741851250703008a20103c003944010000070844051031088000700e2007603990070300300550482c8032080540d4401001d490091f40441024048030301590310030101d03180040a001003542d00d040c0c201c141c80810102a2040503c41d2044c40280f80705146c00004001c18805015040d84541e00d22050000c424072900c50a02c40512801e4006500303510400440b80710a96610742041d103460410341450420f0340500700383d24501e6815019940c0521848804400e801c91010180c908181c1a104032600100758059800501340c02d000055400d00b000010003400101b294030324506440c3c4000c00500a85d44280072803040d100144050b48240031f01101d41e54800043d0003943c44031201540c1380704a4008032030380c419855602c0002c9031036050a8030701c0100035a4030f41c071 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 785196942 1250 785195692 785195707
    0x30a06092d11030c0c01022a0f06090a020906040e07240302040f03030809031204060b09150a05120f15150a120b0709030803040b07020f010212130f050d05 68
    0x50240c00c441080c00d00d81c0e0509000b803101c031151805030703644940a50703062680c42184482c91402840f07200784250880740007005020710318908100d003103403800c1860111420700d0260009180d454000700c52120f415802184004014200342000c2c5411003000740c004507445030a200918200302490b0000c42d400c225044110804001070172001d440b68180d030030118a05421b0005e400c1105000d80009801d101505000c0303a1031072f504004486c0c04008800038502c42d41000e14100019004d400040344c441c0c02002c0c045031048040500c00d40785110000d1004007100d280c0340c01c0c0309050780300340d43d41b00f043d0040401c219004a42400b07000340030080b5103002c846501d0003908100b1089040c082043c02058040810702011180c1c00700848104c0d0080d03d00100c590f0b030385404460014550b040100320401c003006000c1080041c0028600440031a020f645841e42c101e1350241c01c074000c42c00c4040825141309e012900c842c031003929542c0c4a50061089008070803843d141c1070315284902c0400c00c0010360020700301 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 785198192 1250 785196942 785197001
    0x1180b0d1e02091311040c020c27070801210203030415020303010e010f060f030f090f030e010306240e030f01060806010311030312011e030512040317090d08030a0609 73
    0x103a408400084600004c80c40340e01da0426212000700b10f44d000e5552465415a420300810103070768040c3c0c0c0100b1030407904400c01021019089400100e0200c60986800300d50000d00039000e16069039414252921040103000d20190f20344044002660980410800400d076044030b40b81d903c1c04118250029550381d45489050402403405902031034146080c8001400320b2940301c5010a4409107916010481d441442001002800b200c24000d0400e02c0c014100341c201074000c100c44074a072000341c8042240b56941c000340e2303002e645d078684020191b520b103c1510310481d0080b14004038111014040720b94071a07401c003429003180c580390402d2400e640103000420400503940040b5840da841074014505019004201d002e0381103042c040d008a03003500783d4a500c4003180381c500d640021508941103c160810400c9c1d80d12984d03219009c01e13200d13400c90546503005401e592003100c911031006400100c41070489d84802c80d4a42000c0d2801d02941c3d00c0da00006400340c554010941c00d10b45000300c0e0704080396101182d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 785199442 1250 785198192 785198209
    0x1101110105012c010b0306090709051f0e0a03121404030213020721050a030c1224170a030c0305040b03100905062707090315200301180b0d1e02 63
    0x360b600743d491000c01800a0701c80c10301500d0304040180e800e0003494603000e50030355440b141c0d03030485a00803001c800042e01d0942c0152040c00d45202d50307100c03442420903c809100312070360b042c080508080090000580c00c10722030085100c0b6450f0079001b40d8245600c03580060a02040a482144400d4021910f2014004007000c00e001903186062188001203403054040c000e07003d58800002070641e5885404841801042c5400d01040d070031804024036031400e4902064480a42d0818181c04141c03000419245541d40c1d00c0125460190000c203141102c2d664200c42070000b00380d0440801c1028440050040d4150340a540903c00404e007040c0ca250800f00c1280031100020455480f442a0701d8503240300003246618150045450700f00b010b0155502c001c00c1d940115540d000030840101c00c0074000031445594030144a1403c689180d419006445410f120940401e01a002203031005480000c10049960300411003900040d00c003144c14112511500b401245510000e070906184132884000c61409641 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 785200692 1250 785199442 785199509
    0x90507020304030c140f0450060102190c030b070e06031303020f0d0206040c05010507230c0607290709050603061f050a08010b0a0804110111010501 65
    0x1c60615185444a00408809102d121326003008101c4250244d255455001c0417a5030113401400000c07507080340c0c100d52a0010f4680d0b54800c0c014071425002a07080e0014000c192072480c1260405251940c03071010b003010240000e41584211000811852507175102d20300d40d6401034180038510b1b869400d2110200303000600c180108070030b001d541c0c40d00d9a41c002c156030708402c4501d110541c543d018a8103910386190404642c41d40d00c41da200f0703003419550004985100b0340c82000e050303049640d2200152554024007030010407410049590314400c054030501c9075146280d840c126820340050f00c0c0840c285600000c003c1d50500c840e04402c1081030b8550054800d51080c01008038180c4c40c01130340090680b4a00d0040c20300c00c0c0070000224040c1e42e0f40c819030308282010003110751009010304002402d070380d009010f0034001c17440950000415022100c1500e03074588040d181c60740d4039615a5900c0c400b081c1d64203003d07418031012201c1020140d00912036540038040c00707440c0405406000c00d042e461081c2c8040d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 785201942 1250 785200692 785200697
    0x10504060b0a0c02030a0c080f0c040b010509220c030f0b030a261210150e010804020105030a15090204080c0409110f0a0810020a030605300c0910090507 67
    0x4010094074003000110341e00342420b442c1c01a00503805100007800c0000040c0040c1c2030410002e00416001070100b0290340c2600345600b22030301480c02c402488103550402030961b0202e84140300c89100b42c1060510255880d00b44450900d64a0b58204143d0403544c88500341300c0000da0313810051040405c680300341d900e40f002c06c400030308624800b9540e02c6d80001e0b2014000b001282d40f541d00c1d005030f041d094240d8400580c0341c5503907800b034541035012100100d0300f44500c1090a0f000d40c50aa511400f40d44507502c0b01e40c06075290203d0303690360780065035140e00c09000c181c81c242d030310042000c45141a144000160819440c0503030340b10714020720702c0c1c41c03d03404040300307440360f031402d62000000b41c40584a20b10068060b682150250b090000060103110903901c8805180104190b81032207906941c014240185c0540702002000e40700c109104507001c08201c200d0300c07807414101d131810041c0d40c101c880180c9804502100c801006113404500400d030142e0304000c0d081030110b02402545928054a0f0f400340051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 785203192 1250 785201942 785201951
    0x1509080307050303100b0705070b0d0209060403081905040b0415052206140c100b0f060c0601180902010c11040617060f150a1701090b0c2706090913050a050f06010504 73
    0x207844603500c030350b80ac0c4170303030240482c1c002100d8101a9094050310f0409000800803900d443d52404e29060a07404070003401010b4800c1114022141d000d48255010340304034160040c10f15040200160b80342c0d140d540d504084c000c0921805030b40b1000100c47c81c0d0340c0b40940c80c028603910718208000e88800207012480101c40c4040c040940b10020004036043c4200b41c440d40401c08040d41d01c04034030861303940c000d1241c004d800003c03e1031180c90001425030403118003502c40c0c404030494010034412201c40f0100240054008c3e00c0a00200c3d00f44500d00104501c010700004106588940a4032451240070940b1000e0700f2070010400140e03036040381ca582c494041c40f065542c512084000882480c0c0c0c80c000d48420b4140b00380780300389030b00095014455540d8400d20f07403d001c0c100243d0070b032800e070407002402c107859294204803040e4464000d09100101806003030305042010041c00c010190100030485101604c81d40742c004041402042130106050280b000750076941d201544107828140146c0029019a040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 785204442 1250 785203192 785203207
    0x10b0102010c2c0405040320070605040b18040e0106030605060d030206010510021005070509030c0307051e150d0e0706080609010909080c0a03050405031b06041509080307050303100b 80
    0x34010031041c3e02030000d50340c0d410f44185150304800d030045a50000d161104100415402c06506c49105c060004581101085140705a6540115024183c00250103200c1001340d00c81c46030141c4407540c500208018241c1c041e00100301103805400104180c1d070b445030020400d1024510400d07070040815102443c070050540c50103982c038030040c460240a41520300d100c031001c510902c055800c195500e0f00910181c1442c0d0070041803a0483d0030030500c680a0f440c02d0342420315001075010100c45002d40441c03c481c480c00080183c102c66a400150800d000320203019080030074800400624440800007d1700304546e8030002e260602d960082011301041c00180921a900c0b10117490440d880c501340400c030602c0f14503041c40c0c58010b0481000c01031040010613000c0641203400b42c8140c6606800300ca015000340c6140305251004003100d030b900010304100501202e100710010740b0074400c45041c0201001d03074079059181786500048090f00e00760404000d10600d8a4a224400024441002414100000b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 785205692 1250 785204442 785204447
    0xa1d1c0b010617091203130804080a0312230603010b0a080a03091703030a1d062e050d0204020c0c060315031b0f3703061404170d180501020c010b0102010c 68
    0xc85d840402d01074030201c0004c0c00c2d0050f01c07001e60440c6500c400e005441c1d07507a400f1a1a9600303d01c03007040f0042059004405400074841c4510480141020010541c0d00140612400c450384041c0000d074244d501c0301841071994031900300c500014991800148005101418024032160040c0c0100c4103110140e102c08005034000400d9941020030305c20001407040103005c0d4a000c0d4a80540c1c801f00b28000e034410050310300e0f840c49080d020142d10f00001d60038102801e8000d410850580592584940c1c00d440500150071b241d40504100d80103c8210340c07450320700000042d09608210348021900b480ca403050740310741c1421312140702480303008480b4580300d107034000c00101404c43d8985c005010309540b40000d04240800751604040901600010218089800e0840002c540d140019164242840380301140301291070184c611680d040310303c140c0c002e600d00c041a0707403641c003000125503102e840d02c070004d0b41e0a100f02e0000c104ca0348980001a6101040001c10742500d04000c0c00505691401c0ca002c1c07503664 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 785206942 1250 785205692 785205703
    0x52b0c09030b0c091c1214030603070b0f0c01050c070606090b010e220218090f07020d0f12020f04090e07032001020708150f0c0a1d1c0b01061709 64
    0x2041e00065901c80100c0b9010400c006140e00700045031210340c250003002d11000c010480c070746c0d032640c2c1d03284500c85541038102c00b0070703100c25030780d080e01580001c1d001c000b07001140c406411580f40c40b0b85603034503207800e4411032425580107032800160a00001600c10400109110300f40080c0350103d000d0007030ba1345907400a0280c2540c04a4075009100c1d00c5400d0b0340d094922000d00c1d0010204460440d15900c546142264001d0b0a05e480382c000e16940e4081444400b05031501c1d803090030154000c2c2003e140862044550344101701400d4140301c42c411441010003080d002901c243c000c815a15500c403864902d03a2419181150b08442d480c2c0c00003034041c400b0444a000f1845214080c82000c5011450302004038544103056201030341d80d014414200c980526031890b218003903c05040c10700019264803a00d5000787c45580a0362000c00c07a07032503012241d194141800e130510a4000c01035481c4080b00e281124200c0c0703440d032045038101e100500602040d500002c0c411400032401d07103032440901d09088569540e5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 785208192 1250 785206942 785206951
    0x1e052a030c07050109051f0617030412050f0f030306011e08070e030a1b03050d0906390b10080d0c1104021309050a0b01030b03190201052b0c09030b 65
    0xa000012a007040c06403d41240d1049135001086840d00c41f01000c0c115220840410f458107034070705011000540b6488a501c14038202c0c440c0c4051460140b07071a0310314001c0104003004881030b0203900440e0f0009141404000e6851840401456580c42c2000004151040b074410141507d4a030079040d0003051780c1304910513840039150412001c014690300029142250028000b081c0d00c50101c00c2040740364003942d1960407207104200316518000d8200050729000c7c0c4901440c00051041d40d103450030300c41c010718200d07890007404500c2030030788032509508080c062029809030751004a07582030015107404030040d0b40041840c0f40240444080a813002060b0128009010348840701041c1e02115641d2194102e410300c01101c42000446e0350303100c140401402040b1000f1000034a0080c0444140d4080c0c00f42d010030700350041c0644211a40c120280c0e0081e002c010069041060600c0b68007030301da080076840281d01c00e840405100b480841c00280c003d40d4030080083e801c0181c00401000003c0080c10484e030030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 785209442 1250 785208192 785208211
    0x60c04031a0717061f0504090614060d110f18010e0f0a06080a1d0f010e01050f06040906091509063b1009030c060c0e03070603020a031e052a03 63
    0x1180c9411000542d01e03551141c203100705000c01e171300a004c0d164100e0002c10842e007102c1401e024249d43e5018146c1090b0b0052440e6030400e104010454501030b141d0310188044002e0b0b441c035400c040c1c1d805101c6411750020f80501c20a602c441c0360744035003036030803071412440c1940850300003000c105203401250340c60144c0d00c079060600c8510800719517840c0841d0800040d409500c60200300341030001e900d01d80c0d07403062401a2171003546022514074140c0c2c010f0003000c0c407984001e8030440141c5c85507000d104c0100020101038500030340c0c1d45245d50005038500c0d54043c0440e1a09000702c2e03c48854200401142e800b003040030360b80307290203450300c1d0224080d048240054402c24888001d001d20150703124203042c80c0c1481031200c00e1420161108054001c544203101e1800741c0010887d055036907a043e104d03091701e002402c2d4961701240d0204820303407082e001000c0d5164685000f1a520514240d1100e8006164850109031a1140104812031213000d480c0f450079401843c640024895101d1200503031300c005441c5105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 785210692 1250 785209442 785209487
    0x6140409050106081c080703050f01060f030b030d0e120307020f0609180405211305041505090c031b03040809010806060f030a060e09010c0e1c05060c04031a07 70
    0x90003420f40c482e07001405240142c03100d40280584140341c800c081d40041c0046900100840e04c154407921410303225100745032064515908088050b9000101310110004058849001c061030780c4080c4140d4942000b03640302c028880c0b41c2e060410031014203103820102c1704d600c01e002c05c1015036148404011850f2098901c0350fa0b808550004c50b407950348032910b110321028444103000070004001040500703c103d80030300442c0301c0d41e07800031a1000e1203a004410a076a5071080d0506c49450564001140f0708041d1702044c66107031303030b46000c90440d1000301c40104100e1004002c1208034000d000140001e80719001c89a455454269522605030040560950401c80400f00240c00c5481d418121400b10000300f610765224503144140a0240c100c1d4000c80c0a003646020109a4101050080200000d1561624030000c0e00020911250842040c030a54044100c400c0c5c50010403001d02c801030289003c0ca0031140c0d03450850512000d0701d885040b080c01e084002008002402d603110300d040d10300c616402449031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 785211942 1250 785210692 785210711
    0x1d01081b01020c0607060b090108030a0306050a06080a0c021c0c0615030822030b04050a0212031c05060312071a060d020d140f1b1309080a082512050a061404 69
    0x2d0040040c1501d051b0130000023800410505000005001c0c0345c030083d5028880240c444c0240044114180f0400e0081000600405c04200e03050304107101c0c0505a1044412440c1040c500f4102c0d040121141c2c0e01042041c0c1c00c0406110042c001c00c10f840440744956240c01d03240d42e4501d41c0d01e108000c8903003030b0034040004424020020440ca80000c42c0c00142e50145414503040c942d803610b1780d86200724400d515402d030720501c150001c0142ca1034401115103140d900c1c00c0001303207000500801000f00f50315018403610100303600c00f803001402c091801142d441d0380c00d2540d610382403c10301c00030b4032031441459440c02c0c280050381c4601c0301600c19544603011501030340b42d01d0046490049030015040325402045e030030078035002d050215018140f10440d00034440d060740c1d900710400c60381da8841c050000401000301d950300c5406080001d411151031800614041b0039001e0070044035654000100010b411101200790102080c0070382d42d04245a01c804100d103514224808140383c8001c0e000c0d40c001c0e40c5451858 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 785213192 1250 785211942 785211953
    0x70f03030c0615060305010e18030a030c02010b0619090807080d0c020402070b01091a0117130f0f05070e010504020a0c06180503030a091b0f03021302041d01081b01020c0607 76
    0x30070030301c07155044443c8496280c01001d03010700000d001306624482e1510000d014280905250284001c003800914900300781d641007180581454400d0078299921500780f8003c0d5180d460041ca40140e641405c0e0030202d81c54807004107489030581c08504140d000090501940202007012060f803251801c0180300c100c01440414064003546602411442c0102c000007008485a000800c2c10722941c01080090000200103640c180580d442c0b090303080f4018800500e002d8814200041814051a2030110840c12513840c500504102c8500311001d4010300300c10410725050a6100f805020101c60560421052038030081604104601c064042505ca03103886108041444000000700e4000d429681e59140841aa00160044a00c101c440c0c803400f00c4030000035400c1e5180003064034200755403221224919001c0001c0c1050f4801d10456031a0b081100041a0010070106080c8402e003a9001c44250b241c803505601348510003a989643c04030098038004607a0380403400300c003840d2040340e4060b120015803c26 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 785214442 1250 785213192 785213201
    0xf060a1a040f0f05130b04060e011409010b0102070609060f0e04150803030f010b1201090203040809090f0907060801060e06220f0905090c0616030e0a0b0417070f03030c06 75
    0x11260410b00c0c050030490001d216802c20b04800702d902c1c07400e11143d1126400c05121100307495002c2e219444c510042000200c5030b4004540d542080ca0010a92142c00801c075040304e0701c01d4134610b02680d503900b50641c0c5540c051103207400a10b410b00301405114680040507010540075010740c010054895000d0849954560000ca165031015000c3d00484c5e89950b1045d550f40e0007a0340c91041210b8501c00095941c40490844000750490b065031031480e4a04040d080182d000078000321500c52040c06041040c0c3c072101d400c01c0c40bc91141c2c1e1541490301f4480744090403c0450342010040040c608014010b450700016100309121040e542c5954490070a410310aa4884090b107504800d0710f4014001840240d100e490790554811050801c0303540c80300d84c401659442e0514000c0d40040c0c090004001c2e008210600d00300950081c1442c0307102c9601c1070001121450aa00214040500403400b80311089165005400c1035090303000030403580d03090051007600340e259880020208603202060b0420450036410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 785215692 1250 785214442 785214491
    0x1504020d2c010b060405010e091e100303110114011a070203030c1c050406020a060203180a20030105041a0903070c06020a290103110307121101110f060a 67
    0x800c0e01c140d030040c50a081148141400c080265070810240700c05910b0200210380072a14142c644141d11444403080c041c4030307140200322204803580122603450342d81407102d4040c4102c191400f642030480c154900949503280340c0c40b5401e41c0340e152007080811a9080d091290540c0d410748070304441350641d08000d80481c0300d01803000390140004500d4104c120710008410302d00002c0c5030301e00000700588400c03c1f42c041c01a4480c000050348006840d03000325032180d00440c0c0014040030750340701511407110414903140c2240b07012240300e0519600209190180641e023900c90a0880007800f890405403690540b50201c800192441002d08020640540f010400c0b11a059070000d42021069944d900c003946800300e1540684105449511052104a124030b0508203e1492032089805900b5a06c40780c0100c000540300940500c10320b03101141010f030300c080400d00c840c402d8081140c800040000105400f1078510010442d500851384075116520102c0c0c4c4a13400000c0c140001041100c0283c2111400740328136 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 785216942 1250 785215692 785215721
    0x3090e06181005042901021c0e0105040302040e0d02010b010c051507020f1005150a15080901020f1314040c050a050306040603022e020606030d0c0f0803010f031a1504020d 75
    0x4041c20403c4130054065492400e00b010409056151700160385802c48500c2c1d90b09100c2c1c24101101406005410041c022101890441d08264490b030110b803c0b1104800c0d110700c1c6903c8003040040070f036424000c2420542007840e04003954886560b42540d01e8220b0209405a03062250004000c544200a442803401d03422080b50b40078041e240f60740300203280507211003440410403c640070081c1840300b00f40c000c40e901400303041000d000204c41120301000280c00041503540812402038106060744c0034142a03001d03442c229032043d00c1d10302030700b81d00400140b200740106d06109000c00f4190700801030b41d0700f1786200d050a6580e552a070000900628940c0c00c0254854100c14407804480b09840724902a070621541c200811a1103200c01d80ea6100d086460550680c0b00660301c4003041e106019924102c0d10a40d0b611036454590786c1e6218440c3c000340c00400f51400230782820000c0c07005e64030450b4101e5001d40740960850800c0004403040b07412001c00c283c09640c00051004624800768444031038a03001c8c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 785218192 1250 785216942 785216951
    0x8090a06060b0307090914060d031e03021c0b0604030b100b0d023006010c150507020102091309080d0b0f0307030501020a180f0501231603090e0618100504 68
    0x14825412183c005480c04070015542000200e2481a070b403240e04806820241503c00c40c1d0303903850070070400c2c121011301242005455244164944c440b05065500100244c40142c0c952402d201c0e42c2c01485c1409541500080c100640b201030380d110079040798113680d0415030f005c0c4241d681c3c2040d068103480036800f40c004041c00040d4444030110607030140191251380044041d00c00030440382a039400c00c0301c1581c1e19480761098085401503004100e0582254418034480116505c04541e15040710000c07141500581d4000481000d01c1c50885c2c00b60f20780c8071583d10104001180e030303151403215001310080200c07400c0e5600b519600942e1225550483c0c48030081c1103440440d184d1601d1b81c043c0d08400b00e58030104200241020b007214071400d01d8026603507044d114660041c9480300468514521a01d074083d14080241440c096249510061403c0c003507140007072442c1091031a00505010311584411600030b80d490030311106503600980400102d600038800c60b2207464000148840034070f581c1c451584a80b40 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 785219442 1250 785218192 785218199
    0xc0d05130f03212327070806010f030b01060302030a140a0f0b04061a070807050a030c0c0e0106020303071d1806100809060a2a021e030a09050108090a0606 68
    0x400900300c490030030351544643c400040e4000c01a954422220010b00d12030b8182d5208222050480c0e0b81c3c000e12400052139081100d4042e091913619010016900ea0003410080c80101020040640142511951200810314640341c0c4002d80030180140b008258000000c1544525282c00003880e80e0601902d050311401c01940f058010805609007410f414204403050001d450300b40320304000c450f8811003459603080c0748035510200340d001c0941200c0700d071001e200d00300200318200452030600380f00e5146c038000a2554208021010340ad42d010810030080000180800b0364007105990b000020b030300781501ca0b51810000b00004081d482519a008008041c0074400c0c12450500140903c0050710f540a01d19240da20445a10740102c0e8105a140c0c030060201c1d100003519800710400903400104010203040e4a680c00a0906810049100690100f540700000b540041c81c41c804c0a00703078100862170011445e030044c100001511515043c840048000303242c02e60180b00da82040c1e03900c04410002d9a0300e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 785220692 1250 785219442 785219447
    0x1b080f0a12060501031a0d080408071d09010b010c020f0315270102040605032202033702030705041a0307062003121303022505030d080c0d05130f03 65
    0x103501001c0321800c041000803594041d1080d9804031a1040362400d680b4242c2003404403c1030b034542c0444130005d04010001d804401804000d01901d5000d0100030341c0322000c481d00e035110304060310b00e030907a03490141440c0c1d02e44e0300f0485070640d4503030507607036080d801070f019000a003400c0f071000f0750a020101c2d0008129130300d0b081035540040c1041550900c00d0980092125500700c0c0251302882011510400101d840344022602d046141621201c4c0f401480013260b0100c1d0503c50911320241d072142ea12450f51038000359544010102010300b621802c92042c003900001e6035540c03d84110703802036503a280030000c112140c02000092101c081d040760f500c240c0d60303240180a00d081008040350b4504031010324082000110890701c6144045035041640d0703c1d0f00101d68403409617200203c0a42c441c0c0004510300002580748402901500d400a03c8072500c3d000a143c1080040303aa100704022a0004103e408402d042c2692a81800d0910004007689c81c40c00c0c15480101000002d0b08011055485008165 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 785221942 1250 785220692 785220707
    0xc06020d090902040b030105061b0a060507080a0b0f01030f14101d0118180f03030b10050901080f0702070833010308070204050403050f1209010b010c02011b080f0a 72
    0x41035954a49505984010007000c901441c001c0c608020000c1004000f1807401a01402c0007214000004a0f82c40140900b649003592002c4111580ca071218108403103141c2021500fa40200614018404602400006a130702008401d995062542e1200c2483c0c11501c1c50348007082d21042600503c03140c1c1001000080041080c7c0300d05085040743c03000d00d43c540002405910b040700c0d240c042000441113008e0392000070b070415209002c009003400180b0740c0400c125224096015000c0d441c0041c005001400b8025408886e248260a01c0010803a21046903805032003240c0c810120459074040d502ca0581c100d080010ba1b5014081d40e21502410020505e003204c80c3d400d041928619034205104e6042290b06948824400034107404800e00108000d0309041c0c2080d035010f4803900d40540f9154070701020001d80d4100b051851009401c04e010001a03101c00d100361044030009080c60310b1405c1c05540000d114420038204c0843c5c8210070482d810030408a20180c1d016426580a5141c0348c1c0c052400041401 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 785223192 1250 785221942 785221963
    0x140d11040807030606080607020f071403010f0c0302030709090209031e0708010c0546030b15071406060924040207080309011b050f090630071706090a02070c0602 71
    0x14003447c00441c8089000041454001800101a142031850241c0d070007000304d986400301d900f55407244030000244d00c462086050281460302c0068072800d010800a000b6050354001c01880f51040082c54015a0009100706501c1001c40d980c0c1400354035041000e0900d001680182095030a120601203200d810501030103441d5011401c0814010110b0b03001d050041409015402c1700008189a0183c80184219149181d00a00b00444e00b80950408202120171001000c0100c4d880030410004201c8144820342c0804d10700c90060a20f401e00c03a00268982c1400340500c2c0088409510801040240000a01c3c4407407000300b045403503070b41900b0800d40c01d60046400c6d0711b113546006208049080910094100c2c650155101030802c85007070342c0101643e0204410a900040502200f030342994281000c907032900070101007000c1100c41003160345803103002800c5841800f60610446007482c44085865038044e200303c03844140c0f031b100c0d5801c1d0340003480340c0b65012b0100f041400021400e90b40001e04d05c0c0d90b0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 785224442 1250 785223192 785223209
    0x24090f0405010f03140303100509180706080108010c030608030a1b05060a0204030c15022a1915050a0f120f020304060c02071a0301050904051228140d11040807030606 73
    0xc0c1e000e0300307402c146c5a00c0200e0f4049600303212a1003c0c07159003821140a903000d007986110a01c580300310300d801850030300c45a200c20001402c83c4014020b140742030250720031a06241c1011b10015042c030182035124041d84071080b0030006d6070214a2402503500c10f9500065030000280d80766414070708074040181d401804140e4180115520014050400281c8140301c2c0700319a015081103500e03881c82c00c0b202e40311514515088484401c4014095407a50100b8010010102c1c490161a190055a8803080c11404021003400418000c00242d2500004510301011140c500182c6a05180c0e24800040c41804403000340c242c40802084100715042c0d0140001080d2602202c0c00181e84140c82e020000d40c01c8010100e0540030310042000307042420701030b44c001c0d01c5031043d41e29505d0759070f00344510340d00003840d130410341c107a10b480c5800304549900813660450550b1601b014424134000703001c0101e2081c11000c0ca5100e688843c0c0255424a01064070007030000300080e54645039980c104a0b014000702d000d070901 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 785225692 1250 785224442 785224463
    0x80601020c0a180f061701020c060604060303050d0c020313090c12150902280210111e0903010609021917010509060603090c06030a140624090f0405010f03 68
    0x1d464040a03810844080544840c140e00018040c8006003402c003411100c601d45075030010580e00c071a06072803175402034108001a03c80402c0601d01d07140101c090030482c0201d160020030300109a2003402c880c3c0d101e00596011482030340c1601c00b06e00c0d40c400c080344500c211200f280041012480382e000b0441c00951542ca185e608522002034404850703903009954410300441400b048040803640260411580c600c89149100c0100040403400600d1880c1f80d40c01070b0050450004010000e01c035118040881c0341025003003420701032100307460b03130030030800c0090210000c034841d955540d00f500701d80c000e440d40c2c0c031056444007643c0c600310030480344410380040440c81a0a41e076555043c0c1400060403140c00422466194a5110a02400c4d601c081d105030694099041c800c0015181d081c000d501840905000203103000c0c0d0809140445c90024005c3c074844c8c00c5480001e4071404507414000340d03c40040560998546008000902d00030214100d550000d050400003c1c0b2410a109035108072806400c0200 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 785226942 1250 785225692 785225713
    0x709030507031202010f11160305130e01030b0a0e0d0c1b03120905010e030703060b27070914031018060e33010b030c040302030a0f02120712080f071208060102 70
    0x1030580300c14410441580509000c4030403081210030408c0c111034000e013061850510b0ba42c108103210f0a080d002003a110010200410400c40300340d51307140e886a4034040030003840c1000940c050310340111000035001c100b0480c0043c0144005030011002c811500c4084031052039581c81c01c0056005908424030204003c414002840c0d40600500005040010080c00d141411070795000000c0c203020120903003224003107841d4007000090814180581c100882130030380390301e000c0d4801040c182c0c142e0060b500d081d0039030075820400d890000d0605034908940d980460b42c50310f05034a01d01c0e09007600e940034041c0c0341031216200c02c602c00030840c1c0c0700f5081030803086600301e50082e01503001d400803a00703000d0003103207c2700041000342c1c466070203950011030503d10b481c6016030760b40009260904140081e0744a14902051004520382400c01010400746071000e0200580380040b01090007044a82c041e03c442c2001a2481d11502000e084400050740450b0035410300790207150041000c4001c64200380940306584140f03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 785228192 1250 785226942 785226971
    0x1b0a0e19030308011206390c02090609070210090b01090c020c030a0602030a0b040908310603020c0102070524010e0c030a0b0f060c010209040f0203040203060f070903050703120201 79
    0x405803a00b503107400740540d10301304000034520500e05050f183c641d510b00c0100e40d00c14030502410007141d40d81442c0b500c402d85980100c82c90303a8043e451841171004034661304006840e50008140d00c04012140b084503556101001d07130410303041c155040542403408621a0401c40d024441906984d0210b20401001c580c140e41603944003001010310303601d64030131200c10000490750f4004607442910f1410100c1c62101140c0824143ca0015000b00c03415000402c2040d1100c41003448200c03407080d0b0000305413008070741d80c08001d0a0b0702c0c54001c441c10160001000c00c0c485e1001d404948072070741e00c201214003026010b1040002042e0007a002d0a40c80c084038000145000c441e048d0303500506c542201d440c40c50311041030301e07002401e0084416402012018030490180c1d10003020308540b070403e00000d42da6107504800c00046425140d950f815107481401808090b80740010001ea0082a4810b0028592241c46042e5902c0c4459031000b400b0f03100744032020080040000d91865044e403181c0080c000c100050400 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 785229442 1250 785228192 785228239
    0xa02131a03030a08130f05100204031e030e0105071704030803040b0a0e0c0f120106060810050d1101030207030c12020a11010c1101080703020403050609012a0203070b1b0a0e 76
    0x2100300151000000c54194400016443c100c10710482c0006a607011030f071f0f50325061031480050032489550100d020028130028204001d011020040481001300b00c60307901400c4940c028042e9030401c078020403407604109402e01054031009611075001d072166964074004403643d10458040b600685400081203104071940141e0122802420140c94280030f048144400340c88203c002d141d1107034402603028003010007071059902418069a46400d940703000070b00c0c09074803580307030b0310060040d248101188049481840c42304416602486c001d42c0d10016410221002280503401520100001c50700350b151940000d2188a400d225220150a0502440c01510410540c0358058040c80c056401d42c0039542c4900802d40c0e12142c03e0400500b01520f94550a02d0000c0072500321510b40c2d51440c2c050b1590741600d07056041012030200c4074014240003a4000c0d202e028000e802485400c500d00400c200c48080d1400e9049024170020b540d88419400f04003c00c5010707126000c6004d0941640c2080071024000c6070f = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 785230692 1250 785229442 785229457
    0x10e15010308090f0405090c0a06020c090a1109060406090612090b0612030c030714060a021e1c0504080901030b0a300203120703020723120a02131a0303 67
    0x50924141e1075070700c0e928210307482a160140d01110700c800d011300c0c81d5030f6482010b000f181e0f00c00c02441c6d4090844248032415480703130045419940418040c032002d035264102264801528040071941e034100c01c20040160007480c0309240d0000b004200800e0741030340f122481048520990741c002c841c1090480c46004c4034a94a00503090307420000014616050944031004000c3d040c10172680b501c03d0380c1d034003541950040e10044404c0903c1c60010104070b50200007141c0c02618000045240c40c5031a0004c0780d03040b42025181004200220380b4281e41d607079885035560070400f0100300703000c1850103261404e1a1342c0b01d0b2501c28046803030040001c0090070300e900c102d0b0075079148450072050080010021030b03210a03c0202d41004010700c20016005803402e02454540e101c91134101900d0741440d04c1c0c040d0400304150022401c03c000c640d00d04c602d030b200c1c0d41c0160013220070540301822425512200c850601c0c44580d4086d4011001d045044248140c83d0310840b0080c00c440c00341c469100182081589034401c2e00c1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 785231942 1250 785230692 785230723
    0x90103080a1707140a14180a05090c1611100504051f02030f070f0602041d1e0f060d17030a060b1317072c0603060709090c02070b0714010e 61
    0xd103118013984840203150112403818400000400403203090702c981e005144150840920780c021804a091055140000d0a8121031607045440c0220701c1034003a0003103a00368030a0132420f10b003000030b011443e045c041d924031001c0d2141c1c100300e142c210013400c90f5100f07104550065061405e280f5071140d0010141603d0861a4095403800320409502030103500003078403c0d10400b2410b11110f00044080c40140028400c800340c2c80140c40b814810742c0b890030401045003a200c50b600a04035011681c04a4955100a103103085060580355040418924005000024400d5400c0c844c46074044038208083c6200314d40c100c40134080141c56a001c1136131030042003000000b20610306401e2040c0440900c1031b802d01c50f60a000c6407429030303450702c0b4101d80701102c2c1100b6484101000700c0350411741250001039480103040e80204094280940c1c010702c000041d00c01e043e6501e50300e420000c1c0051081c01040010320001184a0300d1340b066040580d0b405103000c2c4068020340ca4256000c00c42c807004161303520100c2c043c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 785233192 1250 785231942 785231957
    0x5040f06141522050a020c0f0a051905030901080c2205210c1512130308010f0806060922030e0a0603151502070504060611060a050112060e0c090103080a1707 69
    0x56550074040c0c24094600b05d40d250302031005010a20302080800387c0901401e000f8207102441c0d0070300908040f400455482038610900b02d03000032810000844003a00003e103045645680c6600b00300f2140d01600c0781706038961400904840540e1140329420003503800c115200c02c4400034000c0025a1100010103c031900e421805203c0400e1905400c0c100c40200a841e505103400e860ba0b40344001c42e0740481c1c04841809000b242d040509d580144141d000d80a44014020740d541440e00306680c950004107424441d918880016000140803007104480c06284000d01c05941c503246000742402518400c0300e4050b28494800082d4a40f007030003003818241c4142503000c1030300e0801d5400e001c00403070031b20f054003503100c1c0300b200180a4030b40388269402010f95690b80300c0e070052411011802d1400103840d06848a09010040c0411284a242300002c02d40c0700b000021400c0011740700310f04045410121550001c0800000420310500f00c0c010203e542032680c4401926034003008440c440d00b801d231407440004c2d441 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 785234442 1250 785233192 785233249
    0xa06090c05030d05030106020f030f030109050a092102010506030c0a1e0e0a05041505040b06041a0904030c0219030f030c060b1f0306080a0b060405040f061415 70
    0x550000000a0082000c28006515500401d00e0310040641c1280040d200000400030315606000b0301c102c030003034980a14580b41c60b141349403d1600060007014502170342e0b8004100c040c41c10742d2001001c15440f01d44030380a10f6001d924541841c4502040c800503500380300c0003548034500480c081a0952008004000c01e0341480d026048a4000b042e1280d003034400f450002c00e0050600c8450352040307200e100f0100341071510340340c1783d00d044010020340c1004508113800c5c40000343d08100a16800141981e000038420740d90480d4540c2c0101c26454030707400c101d0b07400c280310500d54804c0121714200d00035551280f030b45146661080082443d44009008101120000d0000902c11510039140f980206404111407c00600044100c22800c0c41000400f0729620012810354050040b200184141006800150b00e0742e250f62240c44001802e15100e00d0f5110001802c004114048580f0260403140402500d0052a41100741c18415540c050382050800440700e20791428848400c0d2001c0007111000c0511079 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 785235692 1250 785234442 785234453
    0xa0507090f05160c0f080304050607093614130215030403090306020703051b060106030606030606090b0c030c030a05030a0f0c050d09021c05010207060b0d0f030c0501140915010501110a 81
    0x421000071101510071032117020201d5035002c0a54045d0740518003070304050400880150281045500410f5032400d841d20940c01c0c03c00171400e40b480d9500d20044613590b0190600310b40300400300210000c0031034120200348103132051215418620b01e4400da804c00e40d010551002c8810500040710b005001070740300c103000d00000310790390058410366100723060560900d2074141c0c0aa020817804010700d01c0a0384200010000540d02d405424000d1409040c200719490401c1001400c0003560f0103558024040020460203003801001142c20400e00301040c0c07030b01c0d010212030041081d4020740c3d5401100e0b06204050500c41c0651055418070952070b11024500031900c00d483c0082c0c0500c2d2010390748642a00c190200e034216900961154038811000141e0f180d106241040455007000b10f00c90240e00f6021000340011070341065406145c1d01800c0842c030318512447c0c041d000d01000e0441c005c26144840a016400d000003810501c20b42c0710584852580c2e03258801107944c16001ca1800f809548041d80c1d5101190307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 785236942 1250 785235692 785235707
    0x6021c0e010e060c010203070806370312050a0e0414220203010507020a1a100303111213080c1e121203040804030308011a0f09120a0507090f0516 64
    0x10181011110b01a40c0700000e80150802da10455180c0d40000401007019800707942184e204070102c4422203950072192080c008080c0040c1071922140040400a00041560f881400115800590326040500610004100d40c10150500010800c40d61602440746040d0040000321080c2c04c04c00e007540e650700389c440d411f21003502008581c440c556104640250724280103c501c41c80d0310382c00401425007185423802c10503a134480d4a1040c1615403042c0032040314501034480860b0b4152500320401c28429520074280641e05040a4420100152094480000b442001c040300c812a040d0781800d8002c0081c01900010550b901d0380741e042009403e5030b245070298883c1e0010b54424221020060310007a000b0315a0f001340c0382075a445401140800c101984941458050a00040e141c4081040700c2c0c241d44103800f440c04540070082e03002c03a50a10700d80f244c81101406034918005c849103204542400c82e1912050f01440f030803e070034542c00c2c40b070364040c50040c01d020701715008100b40040c10000c0115a00d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 785238192 1250 785236942 785236967
    0xf03030703020919090507110a050309090709091e0c03140105011404030606030f05280303050406180c08060106020109020d02100c0c0308090a0509130311032205030706021c 76
    0x4007520030559504c0800403003a006031680210009103801c00101c0a410960480d6044c04650702c20304202d00050b2000c802d03180d0f155005c0d00c2d0904162500c400030343d0700c2882c0c1d800000019203071120b24100c2c88244455082d50180c406030401586510000032015140700c101c6410121400c0c50041100e540315000e06d0682c462405071680c10991655649000e0f0b41d050b13071083e44d4205803080702c6401d10105001019501c0380700243d080c47e42400340d5090786004e40350302d805403d0554030000102441119040f181250f44050781c05285180c0501c0e00350809103c5002e4880309208902c00898824014401c80c1001074000b0000c82d600034050382000f4008519550600c1044841d42401e80000c80424000c005103200d02102600c4a10540a2003481103065100d207209030901c00c144541c40a51981c208443d40d058034007040118003a1005034078600c1840ca00051254056242c405d00b900c1c014800d0042d110110255019280d54444c22a03070388100e160ba200c034541e1202c511140d5140100e200c3c0100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 785239442 1250 785238192 785238199
    0x9040302010e03181005030601021504020619080708070e010c0b09070e0106050a08060406030822030212010207030905030304151808030f0d05062202070813090912020f030307030209 80
    0x15180242c030300381d007180c0180c0d94114a2107500f540e1620701d450704844030000300c5044c0c50494294584980001d41d1002d21002d4188400c0180000c242591240c2d802c80b580d8041445902509035082103004018201c102c130132400103141070b004603882c64400c01a0030b4a03010169910b500d00b0195450700d0341040e10240000281f44548040040c240080301c1d030f5a4001c04650f1502c545070300c0c02001c0500310301d01c0103102610440c83c010080c0005500001504e10414060254002c4403040c1c060038200d00f0910340001c0c2d4414500703510740f22207460540003001c00c20b110b40d6450f101075949405041c1d80b80101d0040035024030710240300d030060364030030311004000c040b80d48404040b65580f10b4103d410360f0b000219401c0e0210002a503070700b240340107000c0d880c5c1044060702c01241141c0f4001080b0034101c11460007815981c1c000841c0f405100742d01c02038a1030014491100c4561a50706d40403080109045281142d800c61840c96418183e80003080000d6150801d8003d1859075035804021002548880c440720b50 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 785240692 1250 785239442 785239451
    0x80309040e150c030105030d182105070b040801060f03350d091e1208130213090b090a0b01120c090207061d12040905130503030a06151106060904030201 67
    0x100018000c04035020351007080f407050792941072005060409400c001c8440a020300410340140c0c00c0b81003850742c000c0390380c0344240140900800003026a0042d032110080c7c4180709a802c04241c0c3c4182ea0020400c0360700120017008044c0e43c07499000c030380d2901d51002a00b16011354074482d5280650030700441110f0304c84030303007500e1800c200c03142c00801d900100682148180e07076140300400c0107003c03c13241c03410744620310440b480d00c2c440340c0e202903600c0c2c2c54480030700800c0030903800304030000d4040f8110400c10364002c0991112480d03480c0c1d032200926058a05407002145840071031140031001c94012a85c54110300c00c1c24803030b0f0914038074204419855008440702103200c1000107170020b40344054500c2030301c210000304864400c25403c0303c1130700101c0c1f9600e513140c00c04c011403e42002c11030201d070201c90410780003003031680d00c0102c003003600c005086028000b4000001000030300605a881b250a03100382e03208003050b013240c40900f2506514000980155640960b010490510300b40e80a158840c0c441c0c0f00116 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 785241942 1250 785240692 785240713
    0x141e040209090c0307080f010308160302030904020a05120f0106050d110904020c1005010b03191d0106120605010e010b0d02160206180a050409081605070b0a080106030b0a080309040e 80
    0x211800e9044030740c0320303d150001c4140000d06a0000c00142c000c0700c810074039000c550641d1150600c600c0742140d200d14044a510f01d01c02054024401d603048510004e0085440e480001c50181a59001c1c01c098106091300340005080101500402d81c10313100d41d40c2c2c42506080380c02c10030300010326010f003440c07003c48424003281c40241d42d03a0005060114000001d8000020740140d04000c0d180103800410314208103104000c6514420445400d800400083c0030802030680c840c1c007454004084240307919942082000b00b03000210075030301c0c2c2e05c0728442c0c131003001a82e0381c03002041c402c1c0d8070038028a11400c80c20056078419145070b4018040007204029242003890b426400150341794449900c0240d42e031510101d107c00e80ca40b10320b80000408003030340d040c000019a55112680c602c250b0346050f0840003100028001e00904000d000003400110780707a60781d203070030401025040c102c091142d680080e04010007584d06081c04440b05080314007400043d030500d140b010401003c1c002e030a901b085244184819078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 785243192 1250 785241942 785241949
    0x20604080d15170607090303020c100c0506100e0a1b0311090a0f0503010e030702030a12090801020a12111602041d010204090204150c05150c0705030c06010906141e040209 75
    0x49005001400340c0c03c40c00000c10b61014200b040c02071551050261801003000030940114281c07414031b00071202003565841265040d100c40403c2000a00b0b680311b11810040e5200700d0b030311000151081900700006540e5940c0495080d2481c506c04c01000f0f2100c08039141030540280c110781401105214050f0a00318280080340d0301c13100f107522604940c580804100710344c0c1428422205058200006185898995004a41e0b181c110020061207805030074021b50362644a000d4040243c1800710095640d800030000040202650024151a041c9030000d9403d1030709000b81228a034440c404000c400c078000e0b9800b044000d26100d1404410f0401c240c411200d031400030300c0100050f001d8400c00680f107038100250951804102600038052140718a82c100200301c00103414048a122206000d130300343c3e0349444200e514060024001c01511000c01c4450302e030341022170780a0684454030410811259202440c40d43c0d44d0034010210782180540d6040009c031100643e664800100190015103080c0300f19010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 785244442 1250 785243192 785243231
    0x307030f0504091802040e03090a05090709081e011404022116060305100f0b07080702010e10031a01020607120209030c090f01031511090108091e03091201020406020604080d 76
    0x10042c074100e00b00c1c04c0821072500e0300c101c000700c8052034001c40c01e0142510110309045034a01419100e500715000051100780304078201c0c4040d003508415070b8501c194043c0041d1034245c84111503c0c455090024003400f000ca03000ca1644502d400400d824041902c50b100e02d40c0c40c998100b00d084990240159003249a00f0007503a40e030013001503540004180c60318003610460700b20590040e1080c84001c031000c002c412803035010389617515000b841700c40d5070300e4880c801079981101080c046504505e41104000d0490f03090362002c01108003084d0f20032200820030004a807030f02800c85122010941e4500d0303524482000f0760281800c2680030b0204c840c010865000505440320441d1040528404000181f00304845209001260101c500051010043c3d0403080076080c0030f4001e074681080a02c0c0c1c0002c0352418104041e8048895110707000710301c1c0b0108a4003548030b078844002180100540e117184844c1101c14800c030350407035081e036001c0e140740c0d159940c0d00b0945a10070044c0342d41c41c1ea00c4180250101818411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 785245692 1250 785244442 785244461
    0x140903040e0903031303143a0b03031615051006121103160e0909010c0224070807020708010c0315080c0d030e0301060f030605090f0f0307030f050409 66
    0x2551624981841407014103002041024250400e105000441c0c0c140c01c5903040d00d65150400c5852a84009601100e034000c001c120244924442801c03d06180344801900612151780107480c8070740714003041b4800391200c001c62a60180d10800103618503043c100c6040c2c0041d803080b42100c40c14070140514001341da5040c0c0710300d940404c00000c100314003904400d0481d01d0369101d010512203100e0005c06440c0c14000240940401c0e14005081d4680c5031148054481f0138000600c41401d031705014083e64000c002c0c50000074090301c0303843d2a14000d0903100c01c42d1440322102c080c5140b415a15140201c422382e6000d0039520561088031404602d544003030190101c8124196030014040c118a10010200d510075030000074990000e84030000340c3c0c1c8402c050f030110181c03d8105940c102480b00040b0780108020361012014444641d40842080b455421144c040c0204104a680e4510107201883c1c803205c01d1800c2e6815944200034010000f4068004900142410704007541010381d5403140e041520030419 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 785246942 1250 785245692 785245711
    0x3100302131808090a0f080601031704150809062412010e0601060216050d031704030e060c0c130e07180b090103050f060c130506250807110619030f14 66
    0x4d007160f80d90803d84004002404080d902c029007a1a18801d207480d500113000141031744668620300703407441d10a002100d00805920310f030300501c0710300c45800500180d800e681e040864010400030801e640c000d840300354542810030004002c450b804000308410200303900130fa5511035481d910352082c00001803020b40d00070110341e0060401c881c0c00e54200040c001480d00114403401004050501117035000c554011035030a507520710012a00d5504090714502480f4038010f500c000b000800840c0d819010403420044d04054459030b0b03c0118100175807007528240a4411600e0388007940400800200e5180120341401c89080042e90610003c0429083c500c01d0f00117581079032203440d000394002400c0103169880b40d002c104140c01d003d201103110000701041e2107900e00c80d603070100c0c1101515080c96400c442840d04214241014404d6240c0b81c0364a8000c550280ca0b41d5a40d06034034640b43c180b00d0101e500d4821600618407800035078100540c010010f00030300b501010703a1404001000c075410b00e0350a000345480c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 785248192 1250 785246942 785246947
    0xa02091003051c0804060e0c060f040f12030e091b0403060b0f090f06010c0311030309012003060105070b04060f0608062a0306092a09011403100302131808 68
    0x5080503071601e070a100c003d4000101200d0f048911561200001e40c00c0b591040010071600d64200c2503d1034660001080f03540004001180440c04e2841401041244e0440c0e0803035035516a160403285017031001c03e42c0500403440d1100203840620300a41120303441106203844d11000034400c56038807101d81240c2c00c01c82c0c11682e98482c000d000d00d07101a542420800440701a002e62034000154550a6000b600c11414004d002141d4010540280c130000e0000c5a83c1084a4480c507080e10594081c11000c1c405140402d900811605a04504800c4920600c01a1545440c260145d03580c426018402841603c0c03850340c408244c000c003002401140010304070039000305401e040020021003403490014140300004a5404c088044c201d00f64140c1e503001000700c80980f050398401e961954084400800e103241204983c444041000c0d81c4405403c0f0200c00303a03140500d00f01840c0414600d84402d40340ca003540603078014104010716101c003680d00312024410011498110074100d40d60040300d801412140040e01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 785249442 1250 785248192 785248199
    0x7032a060c060b040e150a090206032d04050d0c030306030b0406090b0a02120406020f130f030b01091e0c09091406100311180406050a03050109140609100506030a020910 74
    0x10302943c0e4900004407810003021100c0381c085581d605c8100002d0942d105031900140005c02294091202c690700a0b0142e6503174900441c0c24040c10041c400e41100031440c50100c180e040248e4070351a0300c01c0390b00000a040001080c1d1040e240081000021000c041d11513901100044141a00d1401203125440100f04c00c00c20745014402c0400080242c41501d1040c000700d401030021409184d08950468401030ba01c007420400b81c603079072143d14113841c0d110500c0c0400143c03010301a0400c1040780d015201c40c901c40c0c0d80f500100c04c1642c9090b43c4614880906008800180d000d070b41c44031031903540a0810b40728559545030440155132740c4684101c1c00384004030802120b41880c02004004140718903007004842c41c03e203190100781c0140c4074100c410f41400d03c0f040d1040c1d1517a603c050040c0900800c90005a5924549540071f8460b03480c00b22880004508500c00c24503002400e00d01403014100900081b20310f41940b40c009003801040180e052003010104000358442001c140d0040c0d418039240c02c00d2509 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 785250692 1250 785249442 785249453
    0x310121b090203191503060209060d02120108060a0c0f05090d120306051801030201321b010f0b100f02010b040c0e01020d02030a05070b09150a0c0216030507032a060c 73
    0x1c40c6213410b43c01c0c07420408040b10a180d072880301d000360b03a4803240068441e0030010214859001e0040720000d514800241305c4403049464806074102e41402045421507074442c214002035455500c070b804041005000c04039800c501850140c904800701030040319002240c0d45900c00c0510201c45054046070390782c1014070660520f6030042c0030502c505401159207516540c0000c25403121000303903a40e07481491012a00b440b40f80d006061520403141c0801d62a1009002070221900d00600000101e602e444280381011605018440c000d0400400e550540d8507032160a0700c0319202c1183c0b000455682d00c81580701a46c840c400c0350f0702c038002c1f5602c0f005210080c00000e0b19054550310400c2c150340c01441070383c0c00c1c540d00c00212044141c0c0000048074039162161843c1c603041048052500d042c1c0c1d40810045101c94581c0706070081d0b0851360844003a12002401c11200120b68000940307540c00500050000c50b0b030301819020141c103291038030b103041120350003035a5074000340c0d801000004118404410a029 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 785251798 1106 785250692 785250721
    0x3070503040f0501030608060709211b05030706140f1c02070317180a12141b2a1014120118020310121b090203 49
    0x2e40700d00020071240554002c0f07a00192901c000022102d100184184c0145219140c4c500440d0900c0503c0380c04101841c03a0071540e00700101c280d000139404242052001055509600c500b601703010415040c4191907000d042000030035084100100148412500454011981c4a650340203260f50400c8100c4020f0400001c24404107000d4145a0000c9590358003072207040d108070603542e5007680040c03112031404558030580c0c8200034110021340b079000040014201c07810404403285e4600d5010806c0d6000d03420721032150811150304072182c3c5003001004a84401e1180800c02c5200341c2c0140721060004442980c030a582100d24005180d0081c4070b08010041c540368026565164155650f007108402e200d00a4008003104c03196004d10000d100741c0780201346203100f580c05580703469804080c180540740140c500d041d141945644005100d5030755801824103650258483c03400001c1a52043d = true := by decide +kernel

theorem cover : BRFrame.Cov 785071942 785251798 := by
  have h0 := BRFrame.cov_init 785071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 785071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 785071942 ≤ n) (h2 : n < 785251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
