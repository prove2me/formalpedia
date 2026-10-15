-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5369
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:38:47.869358+00:00
-- url     : https://prove2.me/submissions/b46cbcc8-114d-4ffe-8705-66796709c32f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 965467625 ≤ n < 965647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 965468875 1250 965467625 965467649
    0x1502011112010308070309080a06050612060402030a03080a0f06090b0f01020604050a15090803040501050a061a0306190f0801150f0605180120010207061512060e030f0a120501 77
    0x2403000076800d58441480014035102000414408051250001078010310603002282c011040914003103003d00b170110303a180d02900000013110014280011034900440e0050b01810655100340ca04423030055004100c00b04013074580407000040803062040c100280304032400011000101c80c1000030203581454481e0456100000307110110381f0108041e064560321081da03414401c45048054054100318602900b07004000c820030050003c10b400062080c401c041003000758688900e001d00c0c0002da115441d08955005100184060601c2807032042c600398100c070310720b16190390b407043c20b04001016048409580d45030f00100440c0d03c18048140c02400c2c010110841050134498000c00078041c02001480c40c0340f84031240c51840e4020168502c807100308072840070b41c81e100d207142c481c0030703520010013180c4503450700b01442c411111010a503000c0d103002c25401c0000d0401ca46a44001d4810060f40c05c21070300080154000a0010b1802465094425100d000d201c402210111048a03416404007a540c04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 965470125 1250 965468875 965468887
    0x203070308192909010506030108030a12090b16110303010b071101030905190b0a050f070c110d140610030c050d0c17070503060a141602031315020111 66
    0x50030a9a05901002c0020080194009004807a014041100d480d5401407140d1800309071103480b07a00740a0301807600351070064141c0d03602d105020141c4001d115880f41a0800d200d0101800d109010300e91207c8484038000ca1103090549600071105010344602c0e03010514201e030345070280d82180074007042e110400301440c02d5600d49010309109110302d040c01400f445c100018204030b6030181d440107940079040300444408400c498160a00c601502c0c609803015501180000e145c2840d60041c28800c80346501c0d45505500c404105036091490428102c82e21003d040303201d2139603210041d480d0700050051580c080341c4c400035015503041c4580541001d01c0e1541e540d2060002c42c42034580d20040701d80c140c43c00b0a0041c01070620440d40c0b030041d081043c0c41008e030031800c03083d60800603804090b5241201030382e88035205e21a80b0b030b0444261052a02800302101f0000d0385c0a945c8100b00c040031000c43c01aa0316040040d0101221844190400444415000c0c4108803540d8240700e00102c0c003440724110384c40e10b8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 965471375 1250 965470125 965470127
    0x60905010f08090a030c0510050109050a0f090f11060c06070c0b0604050601140a020106180b1c0b0109091109041a090a05031b0a08070605150f130b121b1002030703 72
    0x44c0d220103070138030840b03480d03900401030108019050602200d0040007256112449a0b0240100b5296104040e050200d40c980c1d4400c0c61040719081c81d40f007054410000820703a40e50318401032403c0c2240d0f1100341444101480b8405221091040c14103075181e840900341468a03080b010809400079000b2450b080802140766003001590741d110f1809400750b0740318170380c484d000ca0140c00c060700300c20700300080740d20381a0b0b000748250803916076402d0454400c00ca090408480d614680220380d00a08249150f900400140d00b560f4400f4048501a081980b188903480003c200204c00c00d03601200c00040080d81140c010b50040f03043c03030300716074104050200042240ca61690b280910110840e100b801d4940d242d83c0040304019903102d80b0f80c0488a103031103242e40d0030708000408007100c2041e48092040300c40b82151a20425804042d50010034411103048281c501c000203048140f50b147d0071140b0110210380340e00c82004003402c05419250f21000c203052240a01129030b11100c0e0a81c01e40d40280040000a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 965472625 1250 965471375 965471383
    0x6140924161b061d0a1d0405011a0a0b07060b04020708071106030c09010e120d020a1106160f0f14010e071e1a0409020f12060a0f1202010c0c060905010f0809 69
    0x503041200404d18484d56690014801c0301c0a1340c009030011020300442c10b01c007200000301034401c0d80280c0003000310000d4121034400c0389585115281d481065910180b00307105410000d400458000c0c580015840c0499000c54101da203c504140c1e0f08142c0400e400301000300040e10304085001c00d0368001d04508048100700400d006180c003041c140040210081950340f240d04401d41c0c6410081c0865003e5514038402944800c5104029a41e85001ea4425416410000d0860700250210382c2071941140e915160450800e8590034111403900c030718018400072400c0c15800c00702d00001c4000000e90310442c1c83e82c140c600b42650348076214458030032540b00c120b130045422000841d881005401c00580185120001900c9940c20484e00e403440441c1c0108040c00d03a902801c90002c4040549200e40c40700d03001c01c000e01c1c032940b1460b50015880001403000e03c4045102c1c000c00c61041c142030f401181269601640911301d500120001000101d0402456078010f8001c1c0842d21581000700d03c50800d000d00c6911 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 965473875 1250 965472625 965472647
    0x5070524060f18072015060d05010b0a0312090911030609040c12080301030b09030909070f03060315021206010804050318060d1b0906140924161b06 65
    0x110301e48168040c0d042c2d8840e42d41510f0140c28880e6110301500d04008058040344a0104410101100f02c0b202c1030610000225a5035480300e802c050101e95070b03507108001440383e040704201c0d055500c0c0c003641e401c9030321003000d044095407080c0c17440f0b0102c208162380205000070705c1c1d004070103c500305030220703050021140440342c00c001d080d28500f24640c1d4506008038401a01c3c2d210076810400041d0510612035401c1c065070503a4411051996103456152116580c1d000d0030a0940d48080d80700d001c510101d0050041c200c403ca100c3c00d011985a40d41d80fa40150240c140c1030050b59a5000600c80490412110034142c1c051002d0900103041d040c0303603c40598038020341d100c0c406c21081c00c0040c80c0040e61103005603891b43d410184140207446800010b25094030300d1030140c070049003600354041041406400c92244401031480b4403410300c02074404100390000d2040010700e010504071110f164289850b001070541411040c0c410080b4842480c15001034161012000d080000c1c950091044952021513051 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 965475125 1250 965473875 965473879
    0xb032d030a1e0509310504051009290f090a030914010c150903090911071b050405012d0605090103020315030d020f24011809080a0507052406 62
    0x281100b039040c15103581c807a00d407800343d00a01c0641c825004c0b00e8004150038211105140070f0500002d141400e0069940c180c03001401500841c0d800c4442c80810b520032449540141c0e0a07144109008681c001a41800484c0000e40e5941070b0422204035121034070a40c20019a800400f00d40310b964074020140e181c4d60140c035002d080b807400449a1a8480c51040b601540c10940c00030049000d10104c40003402c442c5000c0300412641d030340010b408040ca100c0c0d407041d8030059050034902800da1380d80340450111700d440100401000c00010405444500ca080e0181400301000002084030648000c800c0d508103140d5481d90b286100d0a002013503020040e03502854003800c001d40c480d207550b1002901e0004542d450307a011f116000c1c40d606104d500080101d4210b140a09584040303004e030190030b1441c0003040c02011128891001009400c0071520b04111401c0d090000259041d85980d4000d40e903800310b10020001000418000240002400292200e408804071402403d501103008080303404000d082074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 965476375 1250 965475125 965475167
    0x6030a0206210c0703020f070e0112050307080c0a0309140a03080309100c050301090612020a15110303040506150607050c120c0a090515030601140d0201030b032d030a 73
    0x61103007281041107148103940d0b07840c441c64a1060300d6503a420994060700184035562815130700c00b00c0440d2440036100054043c5c600b036803d00d449079a0a0000300c0b01199603110401018000c41d00003406445800d6400010b030030152490709004201855540001400c450411205090350f55090303428011260f00450762920713541e80040190902034100d041c0b1440c1420402c1405042c1c1e40440114141e4065000411400d6111307007000328800240080250844a040014040001200e480d102080c400d440d01c648415000310200b4210341040e01c0850b402e03072154050155000c200001c030300e102c4000395400c9040c41d003103884542d030743c12040d002e85003c0c984280c0f4075000110144005112198080d060344841507880c21807030000e010403030b90711642400803400401980707404243c2a04a40c60061002c4a240f01e0104010603a400000200c1c14981c0c4c40b09002d01e26142402107a00c0881b9408000c1c0381c500d141d03141b03000701c0312a054543d146070b002040440c1c4074641180d080503a101c0c82c2103d003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 965477625 1250 965476375 965476387
    0x1d100b091c08070b24030c1903080705030d0f110d050408090303040b0d05100510050a0c1a060906040513110409050106080a0501110702010e0f0409142406030a0206 72
    0x14296038807080405041040c00042003001d0011000b01e80b03004007084201401c0e030500d4503c00380c0c2600488404d40350325070016000c1071000e180285241e400081d408000c2a0300682e02d40d40e003006030348070400448050300041442d440c623103100d100e1050513006940b410302030340500c0d65a81c6800d101e00c2e0310018000e985d60340414107018000d030960741507044c050212581d0f00d0b114601c4090503088528500b080c9401e04000615121641c84c41e00c045a034084e00c10a103d2003034000030341e1b00e9005070401d0340410200c40108404610a5648203440300d05148401c1d0542c14444240400311100800645c002d501f45010302962001124043c8002500b111081051034a00e40c0002c0107000300b041e001c0c15660800001240d00c0742c010410640a501c0b5200070414206160b01c1400b16004016010b03020805542c0e05441504101088150160300144000b8505030b16959400c03d20664030740c0ea000660144031402182d460200102d185260f22002c1d1030014500300c80020364440008000900404000c900 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 965478875 1250 965477625 965477659
    0xb0c0a02120a0306050f06070b070503070e04110405130506060d020d0209120106051c030f03051e0a0506120705090403050a090e0405030909010b0a02210d061d100b09 73
    0x4400701403140001c51507a10611504020050302d01800342c1403041940e5007102071a0f18156040341c400e5179000c3d08100c030507a6440c00c00c0d00c0580005040380140000704c032070032449070344d28030a0b00c00c40584105865280c908041c05e005510814594852401d840e140601010780d5800040d03a2141080c81e0001d070b41c604221441c080a40100000316800852038071b900c003800c0c0010b400c084195142507401540c081c0702000e0180411855290182c00704003d01601006540720390070069200c00104140074040c00703001441f4080d401c04407890f1000d15a0364050100a20f0448060b85002d41400001d08405d810400000c150220203000201480b4000840907002c5004040006c02403482c1d03d08000549044d060050b00c81e44081496846101c0400000c5814010401a1060300d040c0f58000c10040046640700100c030508905100700605007030100c3d84000402d401a000030700302d00e0f2190300c0102e0113412040250280501410040724034114107010100d0404152461103c00700c50740d5025403d1941 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 965480125 1250 965478875 965478883
    0x1d0307090218030c1c0b040f0b07030614040605010813020a0815010303030c0309030804020d14031c0612030f030b1801030305130e13261902190b0c0a02 67
    0x1010a410300d0010801c008091105a50007100a4099081d00c20114004040140645d4804045200e04c0100d0280310003007120800c607542c0c058819204d0140ca0b001a448400000400b16617440c0006d884145c240f01c1010b40c90181d100500342601e003070060a0800d00080d06491000b0609032500010440990039555090a010020a070382019a01c1c0e42c003444d18a01820242400b05402090600080d40d540c03d01c20b1007160443c40d0550b807008040e483e283e080040e50403d040b019110211504030032540300e801031000f022048881c40400c00f1441400c00404141c840340d070f124540c81ca100340c840d0004640c10020303100e00821589400201154088001502070a0301d980c0039940c5038204002204243d0404000c1c0740c1c01940115051600c5e41d80d6080b10340364841249c1079814080501501000183c444082c3e182000c80444180c8100005040182c89038002060b030b8100110070244c880011901400091107400247c0d012003040f030500d440341a4021130150013803200c85c000007090700300140300748 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 965481375 1250 965480125 965480129
    0x90c050109050315090a12170c0304020901030209130503370503131502040e060f04050c1e071e0b15060a0e13050a1b02060114191805011a0a1d0307 65
    0x1000040c00321f80300c07400400803840021501a040011000714800307000e0f0388140c0740b06582c0200800c510768215420301c40f441c0805840c05001c1803a0f000f0180c0000c0c418030217000050340824104030b54045e0042900c00e1001101110801032038041d01e02d0704099801000c580d0b10280040045801800500d80090780182e04168020514404100414a80b0130142900c2c02443c0c05c0740c034512100f5100c2d0070003040310001d84140480140810285c0e00100704142507000304040c014469083c905180c845640c03841e081800100c843d502d8540e1203041029402c0410340040190b030758034101d50341c05008151503100310724245052192510420604c0d81c3c0300240840041c508140070303c114200300d1880800b032b046401900c0b5004e03051004520684d440020a60704942c0800f0079101da8440700f00c140950540405982c0c17480340d80d07018004c02c1e580e10484105040a042000c00291580f5210440b402404158202a0a50401c0004041c01c0394042803884020310081c007010004030650b00003c0c9880e541d070f = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 965482625 1250 965481375 965481383
    0x309080c1606030f1806110408070b090301050c1e07020a080d08190212150631051c03201204170d20010915090c050109050315090a 58
    0xc1c900c0c0c5501c040100c024908a694980b01405141c0c0e0300104401078840e8224240d940082c005480d42c040b0303d241c0c11420034445884441440c058a45103505d0401c05190442d194401c00024072402d03505003403041541c4400740140c11402d0103130340d800168000000f01d5400c60403a401054400a643c0c4450b084001829120102c1d0315018100c04080c19521044070b0104822241c80b0700060f51904074000c4682c020010303070f00c42c1035541e41d080c0c0381082c107a442c500c140d402140a004000e56601803a01d15042048082140c2007013041007401c0b11115000b0ba00800d0080d86442000030041c0860011001e8046e8076080030018803400b03000800d40c00f40c0e40c40f0b80e20118803a1550414440165100030000c0c0d9000040054080c00d0454a0542e1114030b03142e01030014203210303031290014541038482c1d0200c00b0300e0030011440c060651200600148690700802d140c6555050905c20801d140c00104001c0c00300382414029076242000103034584104000100ba100c001d0070000d00d000509202d1070b03151a500c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 965483875 1250 965482625 965482633
    0x30d0c0e06160c0605040b1b030f121f0b03010b0a0309020a141302040501140f07050706110c18070c11030607080708010b0408071a0904050928120309080c 68
    0x8541c00402c814412056480032183c440210384140301e00304490644408007070180c5030000c1075100c00e501c0440309150402d507000520100c2c403440741c4a0002c00745445c0c0003950344c0640c00e20300a0304140702c0050380c006400200242c2c0401c04034202505613411544e95021942e1a01c3d00808140e003e00814203000b076120190030750124070215150103080f003000003541c0c0313143c482c91610541c0d0124410307400703030707a0108101580c08061418a6002491442040042103060802664515281102c1a042032000c904032010040c1d64100030090808a44012a1140c06000116001c080c4482c40644070004200c0725186600031700400340900c9219183c050221407441c509440c0c0240301213400c4c3c610b0000241e00d000001031140c10b82041e902071f02d102e203015000a0f0301d010103080c8480802d01800e04141300a201d50205555284a1948a01810800740c0311550b0380245a0300c3c5146240141c0171103490980b201000309031039070b903140b0400e440d60030001004c216608101990303016040020380306201e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 965485125 1250 965483875 965483887
    0x1b0d02010305060112290f0d0809030703080d0605011e08071b0f050a0204060503070f090507030b0d0f03020c04020703080f090708030c15010f15030b0613120c0b0309030d0c0e06 78
    0x150000002011301071803c9620501d00181c0c040100c0d1035081e18180d90300c1310711238420b00e020501500040204110040c210fa15440c2e603035403004000e4205a4071703803024982d42d070010016940c20650300007110b030a18184045caaa46002c01800d01f00c005000002000450b40880e030a100b110088000950f800c081e41c070303600c9005c501d00142d44242c101d4049019034208a030026032400c0c001080005c0d2012240344000b000c4c14020741d100141001003005007059203c40b141c2241d602c504014030942400350a00d4139000042e8100a0f14101d01c5407001e40c001c520402a203001b081d071040d840c9400104800e07442c08940c80320808145040d500b0380110300c107400300062400c41484000f412041e800708014142d29641c1c2e9900000213064000c0c40f40b00645482c025210000034442d034081c0308078850003400c850804480b044d0007843c110f9960880000f5914500b508014810301621100080800d203910510314076005403100c2d228003a20845608842c1c442146c0d6512034000c501a442400c0040c040a8480d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 965486375 1250 965485125 965485151
    0xb0619151d060f13080d02120a02010b1c05160f050111010207171806070b0a050402030f0d0906020f030a0504050112110f180d03081b120709081b0d02010305060112 72
    0x1612007a550460f07134002801c0080c4191012030141d6856403d50050141c0841a40c1307014a07942c4030004030f404655951080d40d8071a62804049014460b030360304288443c51091600030b02e400c01001c0b450242c00e00c3d01c0030400890a1201a0105a540a2800803880201d122450340039002c0e820b4000d2000840b50b42040d1140b0444000d8241c14040c1c260030250200c40c0418800c01d40700d2150090078858072440010600c801e681c1180c0e801c58405400c40303c6000d80f0210a074240190150580f00043c0d00c00810440b55604110f8202070087c1c07040918134150100e00090311038070440c0b140505001d800d2810050f0f001341036000c10070140100040d96651103c08031154142e40c401008641072507400700101050742080a2418440c2e545525105d6058640801c5000946000c1601d03808a040170080c0d006500c1c3c5c4904d0b00c0380611019101c80700841d0611060500302288000114840154003a5980c2c007643c90364107580103d6020b0070700050a0700c80000403105401c10210008240c0c1c02c10021281c0c00d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 965487625 1250 965486375 965486377
    0x2030c0d020a0f15120b030a1113060603020c0d020c0a05010c05030d020304150e160e0c0f0c030a1403190c05091801050406061103030a020d0e0a0b0619151d060f 71
    0x2254030b503445c00c105c0e0400070585811a000b810f00d140e0503a03c41c12171080016074500004100403402880c405400c1424003410056907016048040000e40103d03030a5051403040000d003c05007800c1c005001c0c13010343d400100d0201070843c461030b8100710f06104000140035040c41120303c4000110019540c07460182010484080d401c1c4450481c83d140c10401c42d5084404034035070381d0303030b814181c242590030b45811461288220003a0001710f020504110015003a2a1f581c005d001e002d80c4100a50748030110340001522180c0c2c807080c410200c103820002c11806c1401c05080b15440102442d0004881044140440e402d002e80c6c48100c0d005201200c01c0f100e004000c0081e06e0417210111001c0c401d05840300011510742003d03014040c110752051010440680300c40c0c002e01082240c4079400079044101110040c40d000002d00c05640324190f000074003100d4140340c07a100052000c0d4590503101185041c50300c1e40f00d403801005c507100b04460441a0300c8114040d4038a0303201554000c04a035100c101120b00c88102d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 965488875 1250 965487625 965487659
    0x60a0213120b0619060206180304080106090b0a090e030a0f020c06030a0f05070e0f0904020d1707030207060c0b011412060106050a09170c060a032a0e04050402030c0d020a0f 76
    0x10404442e0601100d010340601e001e001c0d200c09901801c5551108c4030340d210403400c0e80c04205903600080c400403603c40f5091251000400303035034002050003141c850610401405c642c2002c1a01402c10040402241000044807440700291a140c0c01032486140c040381462681c0910a500c14000400c1c0141f050444c6c100c40740030100c180d070401c42900c40302000d80d000240325001c65001800b030080d804903403600d40b60260b4014000381030400c2805203540c940f21200c010301e441e00d1408a010441005051307040000002410141c00c107000040c13070036100e85182440c140704006429070205100d0703a0a458007082c0207200280303c402c0707409a5849000207000390f0403030300303800300000d140040029158100741c0c0001d00c9004004003604004c0880401d014480c0e10503200d0005154403920b141c4100a41d111030310780c03039040031680d1803100d12292500070130f010100b03548180b00d103007000240005030f075001c0740c450b010400072a0702d52002c014030720204a0b0740d0096800301c0004031201000156a426078400040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 965490125 1250 965488875 965488879
    0x2130b0f0f0114070c050405070f09080303101a27011106061806030f0a060b0907230a3506010c08040603090606031e020a090e060a0213120b06 63
    0x282a184144481402070030349160001d584030507206110a400401008210f000707508444555803980046030039903009031060b0002a4200d440c540413258003c003850003401e84d08018520f5800d049044401005142c060740b60f0007072400741242515154074088540521241c0d070041000e403200454000032481d03012005000c501550b0420000e0790740800e03200e206040052402c1254003d580000c454800000c1c001078040c03250b101c542007016820040c008803144078031008513200d02c104051014955001d080031042c031100e102c030b05010808041d03821a0f8103841c0500c4980741d189a0500702c98801a4540c00d01c401c203d010f4005907000c00100041140340000340445800c0e4580350011074502940c40e20140c00d0040034481480454481d420041070a8020130740490b034561607072121111517442ca081005610100560b000c00c5007018180100104400d0104104a41c6c481c440e80b03440e048000d03c000005031740011614010700c1145c1c001e201900b03100d800d55420b000145824902a20161103981c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 965491375 1250 965490125 965490139
    0x1802041e0e0d021e0106030f0f1b060516150608301e190509030f0c06041815080307030809031603050a0201110313060608030901020613080702130b 65
    0x1c16641000030b690300e40010a40c0140710002c2d0451109801c990300d0741c440c240a540f14080000814a40e03c1e80f1600303280a038500c0c1e04110060f20b000301110600301c03c482e40201c1c0f50344c010841e05070040d0956820500304580412000c0c078514000c1c0c040035542203000d80c6207184c8030b80072410501c0042c030045104044409c8004a00054500403000840c0c4401c54038500d2041101018265099540da070500802d17a416505022404000c00440e0003004001000030300d011a000c03039140340070006403104040c0c6001030501501031300c011815500c10740c01103d43c481d070201c008a40b42d104376448404400414070303020b205942c42c2e1124a489501014060f070010350044042010240c010040f120327040c1030115907a8080c90940c1e070645042e0050f402e900c065550340c0400d4240075a00500540c442c18030200c2100e120740e2140351450480e4250341003070b1007907401400342d960140d80000d040c64100d8042c181c2017209100c580b4015081d8400c20000941026801800003031001c41500400d110b168100d41003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 965492625 1250 965491375 965491391
    0x106080f0705150c071214241620070e0c12040b18060702011b090e1f03050f0d090b070b0606030712051801110a121802041e 55
    0x149a90740360500400307038444010044800d00034150750040c080400b00f030042d6040706a8400c0f4043c00c642080806440d07400610502c00482c88041c400201000c0505069900c041071b0b200446e420780310300038441ca4200d007800702d5002030707180a0349600700940201c803440203e00b060301c40801d4031203c0c184200d110400450000c20700345403100084d580010340302107040055036100e031140c0d0120480035014440224400900480036036052107000e204020350340000c5074a0070115281c4044040c10081c0d1800c010301040c041c80502d009040d480c0e080311190003000714001201d04100314ac022640e00080c0184601c00c680c4894200200e50b5140070555901c03550560780e520405c0c2003080c8540c0740010303c040c0110b800624240380c00310156422504030728000581c07000ca083e03050100d45099440042d0385902501c7c0c0c01e0240401d008903010303000d000400764240114900080d220034000490034402d19100d81e511048210348110781c64025400a2061200300080c24040d510414065204107a482c100300d4a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 965493875 1250 965492625 965492653
    0x608060d0f06150308070c050a14010c02040c0e030703061b05090f090a02211b09090711030f1b0f07260709060e1812030408030a0f0608010608 63
    0x800326003181c20440315595032045984000003490080c4000c0302c000301c001004004281e80c14050b1036010322682081da40071b0f0900082044070000340d030200101100300800c0e580d0503684420070411165055601084420a0000944006510840039074062281c92000414811241c01c0362511100e58001030718038250006040b64207100f010141c3e80c0140c4a03402c08852402c00038555980018544001401d107a0055040d044200ca14103420416426031010700000303010b0b074840f441242c08140400e40c9400c6021001c20701c1d00700020304107c1481814440c070465144240119100c1551007a26980c0e9030418038a1000980c105054411691107039403a0076040b03d6000402a096502c610b020180c00130341e81084800d034072015010801c6a014203003000800d20000e0003501c001e804041d68101007840c041b0384e040f0394000101221646503102850550441440e0011643c2150300084c0a641d2035940b2801d040280c9090f0032140081c034600540061040c00642c001420350380884140c0302c0782030074008 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 965495125 1250 965493875 965493889
    0xa12230c0a0e09120a050409060e0906060d1e0b0106080f19020702010302040801050a050714031510030b150a090f0b0f1c0c0c0606090513030e210106060806 69
    0x20041d4105462001c1840040e40004a1540c071030107003021241085041030b40d07102260030513041c0001042c0040b4050050540501841010304001030125100740b90440390300c2d5440304041c04060240c0040c1c080c00301401500f1100c4200307180440c0004502503000e1a200d08203031070034420000040d4450b4007040f01c00e400c0319a114003400151000740c1c00340b100101008002c0d03204000485c14158204000500c0c05400e0090382d1040c6a540c01c0010b06242440010780910b102d01d4081105500400400c4010b0312a0803941342c1000e41950ba03440780c2c085941094000b801c03491280342e0302503800b0001968408101c2c00500032400f090b80d070184030f00d0f03035607000d9481c0300014020843c031800141f01c011200449480508100c816401c4501b038000c0300015814119a0700140000014400302040c0003484920302969006110010080241b8603180300500010000c0c00340080400c08130b400704001603038400700c0c12091514007001600e0100710b80003505000f40344900c20b03e004100031200090711850451 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 965496375 1250 965495125 965495143
    0x21071407020901270906060905182107051509100605011b230601050f0a08100b030f0d021e06071403070219050c1323060a1223 56
    0x903180d80b62903402c0014082096009526841c4084860491010a2002401003c903180c0c0100c03000074909003051100016500b00401c1842c1c101c000c01c03d81c1d2040413000503c4a212070401000400c1c43e0100d00c008105440f8460024146118080040600c140382c505920b020390b031b41070200e60b50740078400c03050404e0f1041446000e000c143c0d054440308100707401c4200f84490324400d10420038001e80b40c00e41c0d00401000c0a0008009a120100620030303421700020755142040d04407144000d0340e01c0c22002990b11054031849030040c5d5101d42d001d160300e071400c000e01011080400280c5d503000340c07413400095407408844910310110720450140f107204403006c998240100704540e102c9a40e280c00d039003135100507070000e026441184581c0150240e41c0300011381100d0500d21901c0a001c120344617904000066007456805000700b4074048a040145074240b40030040b10562500302c0d503c5544010010f003444945a00980680c2c1e001881102008401080f400d454842e03000100081822800143e0b9039040740c2c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 965497625 1250 965496375 965496379
    0x1e0c03050c19151d090405160e150d0c0b030a020d14010503031b030c0d0906030c020f0d11150c030615031b0d09053c07060509062107140702 62
    0x6200200c0e030394418490042c100c40d04110607040c541350040851155074084405949540200302c4004030300700c0800340c140040078032440d010706909046d40881c1843c2510001036106a440554070010400690040c3d401842c0d92980140c83e450400301e01c002079404600d00c2d41d405894a12008450520410b805060b0340c00a40150709014046444002190780a0a0030900d403000f80202d6030118810401002c100e40540e6030b01c00068540340002d4240c0f02e40444280035034212800300865080002201e810500b2145001d82490303084842403400c2c252011410708100d03c49004014199100100035800340318281c4114a07400e01c20007000c6994001030750950b0440749402d00e42407010303102a000e00f29610305a48006818542a1f40d036500e003c004561401651078406032104500355682d818032100043c85058140c812001840b49442e02000c0c06011706204000c90500c00d5600c5c0c0b030703064501241c4081103920044a9080400c41440c108494020000e0100c0401d101542c000c40305884810f580 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 965498875 1250 965497625 965497649
    0x31b030709110d0c09090c09060e011d060d020c1905190f03050d1d0a0b09010b22020c070b270f042d06050f0a03020303071e0c03050c19 60
    0x5084840240c16011901805c00015440c00304510180d4070a24000403030356102c404020340341c45400750031861141151414030849207500201905000c8500b03100a40c1115001d0b5101202c0f0300780c00080c001c00d4446496485019007446c0080c0d64120b03a801c69074010011144030741031140f410141002d10740d2b0b00a1040e16103004280001e030003040074100314820040085203214000f148013045008642080392a80d201e04004803d1005000d121a088245e100081c1310f03050320200400e48042c1c200c00040011000540954083d00d140c7c3e042c0d9410804120903030340d00b55a9402038040580080c50040d501078004003203807003404150300c9200d5030000e014110360010b110000400000303020596400c22820444104a0703444041903061840358540610005070090804040c45600b59111b404107000c0c82c9114010f10140e5400002e0f00c61255125249800c0714102e03840101e00700c80d402000602c1100b20318004010000041401c0048038426600c1100002440421042440300c512070070312400c40d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 965500125 1250 965498875 965498887
    0x30406030c021507230412150f0e030415030204050d060e0a0804170f340f0905161e030b010e0a0e0105120105040b2202031b03070911 59
    0x8040d4000e00307190540c5006486030248280b204a550680444044000441c14200500e64a030581e0f10b00c0744543d0b4003c40c90341040e04200b0110005078807000054440c1d40041c0354003555040581041c6d40801c1120410300850020010560740d03078005000c1c1c0700b6441140c2d4041c4c90014402d10940b03003115001800c044a04000361138100c000d00700031200304060b002e1070300c0c003001282d030420080c03004103050707160340d202c4041800d61350342882099888030420350891124690320191881a03080c83d0317980c0740d6000d0842c0900385d201d02681c0e034556010400500d14a040098042415803022380301d0318008181006d42c2c48410030894120b0801e02c0c0142080c104014240b01b228480d90281c074031024113040c10f000081c1308000160808440d0740c171010b003600000c4014410360400301c80100c01310800c1d000034400760a080c0d4030002d004100408030100030030084660588903c1070078114028a80280c01d890300f03009207018501040e03c09880d034501078812001c0c0040c01d800ca610444e088a440810011f0034a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 965501375 1250 965500125 965500127
    0xe0d02060a02210d0608070503030f090a08060901050717061f1403010909050c06070804120c0504022d0c070306242309010b0d05091006060207030b18030406 69
    0x107003014144000314400e00704115084614140d070307a403c1c2c1450f0b103c40f684401c00401d120040d036a84c2d800c0340440760802c0108000300e0b100081500d4607031100b000d00319110300201c004519030302403550102010348503500c1400f0341e041040d80000c1c0151040d5455840030040180c2c1c0c1d62260806890958200589600b01e0f02c200f56170305006444000349240801c00c40c6500f801c940c010760000c0c0c224400340c0340da03801c2c103000700402003141e40c04045003940c0d45030070418140c69941c82d60107a8800d02d0748002d00d40081078100584504401c003d400010000c54464440b88903014406e52011201c8003481f90407400300c0c5014a00d0400e454401c903012009000c260704581e00e080c041c0161711404120301c880f1400411118001000020181c02c40c400350f503c2402180b000d0343e01500d09045010700421103403006001d110710000c111500c84104030000711701602d50049962138804182e015040c13a618040012400c2c0754003041c204100c90140720a040661140c00c4006810920b00b0b6415103a41d0040204000403 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 965502625 1250 965501375 965501377
    0x807080f070c03080712060602031207020f121e04030b150102010209031002070f0507031407050105090112050712020f121e040222050a020d0c030b030c040906090812160e0d0206 78
    0x41800c525001d9005481071181d98182c900c1070704208d0140e0030103d1103c3c0150440c20340d4a6108500e44010f110600c804148d07580c46a40b0704254a00804000500380391110114600184a40383e8400d0603903283c0c0ea03800d012903080819a20f680c44500d001007020300f070398414000e4803890031005014017100c5988401100003036000000840d40c03c0d081c1c50760f2001241c410702c030320002580075050a03001031780100c0170a4108409034002d43d040c040144060002d59910280760412103440000c009542d4485500580d0349406a01a21103428000180c04500b02c03074401c06040c1c814070001500c0c041d615101d481c10460710030f4440c5212800d00c10030010b07002d0728020070340040301e54120400d440d0300005180081d0640d80c04072040702c0c40607000103404440c03c0d4640b00783c40e907450692408114005101000945800c40d043d51a44a00d032140200002d0020b00c2c0d12448049030311000440d0b4030100050b00316804181110700c0160f2900e066104040c04d40900d20101210800908040030002558204909 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 965503875 1250 965502625 965502631
    0xb03130606030203030705030a021603030906200106030309060201150311091018020a090602030a080415020c03120f0f040804030f0f02041a090105061305040207061b0807080f070c0308 81
    0x141d03101c00c80000940c5080c00107012450040000d10741c0c40000307030b1020b1b2401c03c50721120708407524038040c00c03c080780e03000101c80c003659803604d82232004005001d19100781c4040031010315042d5290510001c209600b00140ba400c075840c580007480ba4056214400b10305410900c0003a103406982d80c070720b1000e8a41440c400d6840f40c0c000d4013005640ba192107102c0d403000142c1c106401c04650020342d81c484981c0220303121004003c80e1009603e488541e4100400e202c2000e40300038070503103040755003051460041d015110030240305012640c880e40050000300843c00c040e566045510410400300721a09244d080440c800d07074010b04050302c0c00b840c6a9405d0204c511080040d5540c421146105005a8480c010316200d1111080c60704040d200500400c003001c80c06920051040e141000300e14900b50007466000100c580071280103860381403906001001d000000140d00146c0d5000060790041500a6121402443c50340c1e01c0300c02660380e600c1008081c0d00262020404a2902075035400064410a0400e034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 965505125 1250 965503875 965503883
    0x50d0602040305030d05010519030f020d0618030909060605190809030702131425081803191103090d0209062b060b030307020d0206161209030303150b0313 68
    0x101d056500e4407414215000500c1c1110314986801c010409850402854403803070700c030300700710b00c900500c4c5a548144841035541c1c001d018441e9440c5680c01e211290b40008800c0c0c401c20701803038041038180380092001800780500360505203840804106c951088003607503070409446a02480d0030004950561f85000018140080d42c801084444016100e00301160700765004000040780c0c00c04580ca04940c0ea1030000d1928503c1007a0424980c0c0d0202070741c50482d03800c68a0b04101c2416210501b6074894a41040e0901c59544400030b442c6111034103100c1d80c02c5404071030f60307103240d0031380c0088400c1a200d109440f42294010704403000c0c10003501d000e40145070032050040640c6003500c1320041b02c0c0c092542181e03d010142464108180501959000c0c0ca032400108401440c9803132070aa002031079208550002a00030350010494000d03101400359200120754014048440e92000c0c50002000443c50f800100d0019040c980c100080401c101c82040035120108401030a41e910a00c0480ac0040034000940b = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 965506375 1250 965505125 965505127
    0x5130b0c0c0307060606030e012c010f0c05031e0c0d0f0b0409031d0405011503420602370b040b0402041104030305040504021305030d020d03150f050d0602 68
    0x1600d0810001045070504c10103000c90318602d004405000c9800e030300da411413684d0610030046e411020031900b00035025030801a0324030482c1907205941c0105014107107552114070b0100203001c0950040080c6126408845543e0020040859900c0301010144c415104140c820300c05003a400906802003005250f41100000b0112440300000f400c0e1040e03440182c01041030660310072503d42190100522050055400f070215516040081008811032000c9008050341c903000030a08a00c0007400c00c03803058480201d10004544080386582030b0018401c1c0c4c0d0140000743c0c81c0010028004199412259805c031031100c01440f405c0f40c08401c54118010440c01c504042d40107100090b07021141900440c01001350700c0c80d070f01d018418401141e070000d407101c000034014041000004d50080448068902c00d440158503a00030030412480d006140d0011689400307100180034680d0343c00541e40351512700642c1d0a00020308404221108000f0501604840c002450030501850134030004c0110840d01c101c0c001 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 965507625 1250 965506375 965506387
    0x30507061416030506031b090c0f19120e1e0c0a0b03010905090f06011a04180e01051620100606020303040c0617040f020d020306090a1505130b0c 64
    0x10005188211084035000d166410b140c00c0c080c2d810b00c01c003a4054400e400402409011643e1114500c1c16112030906c101d9110b0000342002484606841700c0001d500380c80f44c5c41b0b1010340e4854056442040710480000c00b9010000c04400c0c01d130003400c0d060740308807014182407516100c405401100084486100e80300795240302410f51035110f03204009208086400d03840e941003d03181030a076200039291862541c0a100344000d03c001c0850030b181121504451000d40c80c4150b42c04100c50b000301d5100d040c180700683e600c3c581480450b0090501031200000030442a038134941c1d81000300661080c500700280015a5007222030f411120300e0205100340c4000c070340400c804286207400b542c50a400000040e0404418002040394021052016007a81e09204c1d10211100b00c1810701800000c001400f0480f950b2200020354440002000260b0340207015503005103011f000d019500d80c10045d04031b404115140300d9048001180c41994050215a1020b40f0549542d45800c0c0302c00c0009068543c040c4020881 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 965508875 1250 965507625 965507651
    0x2505150703030b1201021e040806011806030f110f01030915020d0e0304060e330a0509090403090f1215020304030203131e09020306030705041a04090b0105030c0105070f03050706 78
    0x102004c42001000150f42d40401010902d80d180c07804203490300b1b80308140403c0c010018080b810300d0544a00d040c031500448a4013210b103019081c1a8009400d800300b02c0da04c6d2050001c1101c680c50003140558100100365031a00046003107641e09030b0041c08036501240307d4104005641c0046ca140d40b0800004222806001e841c5070669020340e2010020074003202c2c81c0c01e000d061042c05c0304802d010b0071043c2d94900d09520507014031780c01e1403c0026030360440010000d0981c5d00402c140c034600a40601040d2035850300e440c010b402d400c0301d4000d011408801070300000e140110060b450100990001981c1c1510999000000180d080508220150b00080c000091003180c0038002000501404c004c0c3c451342d02c3d121045008a103011742001121a004000300403481c3c500180030b1044450544001800d0590003141043c1403041050311a4400d0600703808070240f000121116060b18011419180000c04120041d0703087c0c03080620013050510f84446820100b4000c1d406441d50500885021130031054042d0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 965510125 1250 965508875 965508889
    0x903010b090a2a0807082e05010908030c0a151e0209010f0305010302030a111201022a030a090e130c080f0c040605030a0f1506082505150703030b 64
    0xd00c140c0816514140d00803003d0301a5049070141807400c003030301c201022001d401040da842c024202c206000140012172403550015180b01c00303d0024640030b00e110035100301205603a40c020301c51280001d0f803a0301c000c030b03181e0350200440c0c002920ba00014040c141d455030b282d6004a840d82e5125140c5642e600741c1c02c010101c0d41040c80d05c0c0310151080140e841c029000054050004a0640001c00d0324003801440181c800240c0da041d4143c2044903c9410808400011002c19040410761401e500100b50f0203102c0c45001005c440e510100b8600401d00a102a5515982d025285501001541800081060400036403002c3c1c0c11500034410070540e980680c4a4000000d031950000d01d4035480b090b801ca00711903042c4016400103600b2030b81401004c0c5080c0003e03944403c44800039040c513245140e1034040105008004460740c250388818403503582d403001903d4440c1302208100d820320020003000c8000c240720084400a651004007400d241d94411144150315400120081b0181039803040c1006456444003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 965511375 1250 965510125 965510131
    0xc030606040e09102307180504180813060915091e15270e060402090105041d0610021c03230f090f0102070807060c180f0e180709020903010b09 63
    0x100304104000305d0500c000f204c3e540101b0600400089592480700004942c3c400011510101da01180619042c80c0c0d84d00c0c41c484c15800204219800107810740b00c900302002c981c0460b0290344490425590302c0c014404030188503d001000200d900005100c3ca082c51515803043e4080b0120000e80300b504c0300c0c40361603124039a6107450045558141da011154646c1d8800603d0020014140c004031464203c0d0a0360084014045030721503a004103e0790401d0344100c0645004080b81070042500580c00858104124420390320321307010300c40710503c15142500000f0903510498401d03003070204580d030b8444c0450041141400a000309000200342410300c40c00c4e0f40c5000d0284203000c200c515141441c1c054549404100700d50100c0c1d59005001601c0032030b0070402641e4042c2d0f007009011528602940f0219850f1001c0060252580400540440d2941c100d00c200f8060722080c40025541f5252240050410b03041c15106d1962640440010700030303803100e90081d111040c400380020450b03030320b60000a042001c0031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 965512625 1250 965511375 965511401
    0xc080f03040b0a05011202030723040510060e010207031109061201050f01090b2209050109050d030213060e030d0f090b1b0d031503290f040b0c030606040e0910 70
    0x41d06010f4084484d2041600410f0a2000004180c0751680800d40f90581d40c0300fa680b4130120081c0d012600299119050181c0d00002c10400c540d1030301c07002541c07440900d13005070710018590100150380340d400004e9100944e13410150001c0c5800e02c14003013202c0391030000d0240d03400207400e480b04066a0f400340200e81c0a603c560b00b1820544d07040c01c441070119135001c004a8480d05200c00900d900300000d040b0350f40d05128064010440d0251410f06a0260a200000410910580308071038042035140d0301920007581c40c241ca51500942d142012640d41c40044940b540c580c10200041701ca242c040d000642020b1003d0030320790485a5907048100c2035030031042c8801500c04070345040302c070402d005000c0c2240d041b54500f4108000310b444140c00000405602004120606480100d00c0602c541c55400c0aa4100382102e10040d15100c03903020a0140c09a9049849c68807030000b14002a0800050703c3c0f2034040900041d050510b03007101c4000700080a0851003844c000c1161114400c0c1050048558850700 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 965513875 1250 965512625 965512643
    0x30d0c020c010e0102061603020304020604030203030f070c0f06050a0e03010912021011040b032202030601170c030622140f1614011b1505240102010e0c010c080f0304 73
    0x2120700250948818455150454100c0c104000310701c0c200d12400f052480591074010380b251b440c0c1c4082005e40c411030300082e41c1340c400450360711906030020b0300a014152044d4a40a100c9640b4075446c02c1d400f00324050b01001c64070900040c1c61280c4a18550321180a0040007c540d401c050388a5102450703084070300d90016000b251466100b100300b07018007403103400c0070408640303411302c0d250003c025808040d04c0c0768001010140f413031840c01311096103032000640040a4030342650759540304070900c0541802c518441d000300306030844646400b0440320307c9094882c40611101c0c20780f8500386502c040e45031086900440c280341d00c0b0007001d010481e40305a02405401461301c518041c80302200d00003594050441c0008400c40310a859a2012001c008200403921031030520829140002503500c15810020b8114900001c2141003996040c608081712901c000c450032100900e0300482c00d0343d25094060303089901402603400194407d4199140c0e09000f40012410160301d420025100d40c002d480c1940c031070315 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 965515125 1250 965513875 965513893
    0xc0405040c0224180303010602010b0a1d01140612040f02040506030a0c05040f02040504020c0d030f0207080708030705070b0a020d0c0c021e190801141f03060e030d0c02 74
    0x2424814500d2091460004080203441015078008850f808040040401c1c4000f02048140b450591800c600b1501c40096907143e603196400280240a009100c0d07126004102e80003550f111006c154102c6088540c90309440c680c01e25540030f0803000300280c11a0451010404500342e0b02514071090b0182d44540c1585a000c611801040305130341000d8001407007a0007040b0040000381c0546d030120100c03101650082a40b416002ea944024040d50b80015081400041d0700c0c1005000400c2c05100401c0f941c508202e0b030180c0243e0704049000310300005003040b108201c5500491210740103140d01010a190140c6000c45a5648500000068549424150b00450351080a0101d400396413130a0342141f420018041c1c1d1a00000c841554030752440c000f810003440d600c2400d40301c4484503d102d131566115003400070795440e0154001c0c52800360140c0304088403800704031000c0c0000b1040c45585e5151a0350b06010b421601c81d44010706070401d803078116200802140343c3c2c1002c00d000c0d0814120198016114240d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 965516375 1250 965515125 965515129
    0x10801031a1b130e220f060f0626030f0901030b060d02130807051c060504142a0a0b12090106030b15100f050d09030504030503180a120b04170702090c0405 68
    0x84081c2000001c02c14040d170301a801a50010540d030701031340120590804401a003040401850100302c02031400d0708110700843c401d0b6000d0004a04584109051080c003215514150f840c1d028212980803800400c10403141598030035004a00c903d00014481403810002c210004101e0b0704c00745960044000d000301c2044141814040c4000070a000da407003415100350a902c0340020000c1c00002011941d0300d201180c00d0003500d8140c001c900350b1400c2100c2c941005001d00410100d003103240a20f02107074020303640380e441c00d20080040403181060038903810103400c64094845030000800000040d0f58601e000404603103841e44007400350f1700f084c02d1020603c0c41d01042c0013944d0a5624481d052103214201600b6a81d4030030b04a0b8640346003002c0000300c1e03407a0b900e011075862041f684050701c60f100100304a0390702e160400d420b650b600003c03101c111040c0d554099640f0b4000c00c0c00303005004100d00c2c2000501040c2180c0345290680100c2c1c001d941303030a403280c0c00210290803d1355401c1c050b1001141c144418 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 965517625 1250 965516375 965516399
    0x1140a1e03140f1e010e0a0605060a05010c080304021005130906150c11091306020f0316020a0f0312060b1210050406030c0b070201030e060702010b030c010801031a1b13 74
    0x20403111405006120020300c982a0340701d404a41d139503c0c62060200c114a030003001e600003614000303540192495610700f400e188000e0842a00c2c1c1902c5192003c0000035698090b802034916640e110071758a003141e50316000c1148904c4034410820501c00c041000c030074122180520300c40a4400f03004002800c50400c04d0040c002c00588900b0014800c1c20803051011588502c254200808200c80b103c03c541d656980d10005000e00311001403080303001186210001e130082c00914407841180c0b403001d006115000f4100da540c4243c02014100300300e1000d00102217031150f051a107a212183c18040b80b01c0707960f079032003903111ba0020090301d018a0b1008144129207103038055481c01024104c0e801d11005040d5110f464400b646071280c4d0380400c000243c04811a4001d4010488440c4002e081e0741280c0b401d00e0019000c2e14581491510a00400b03001e05102c0d070150149034142d98211701c54030500c03a1200c01c1c941070002d0140a8200400b0901d901080c245030001c0289148622a400b03585410f2401c901861703d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 965518875 1250 965517625 965517653
    0x1609050303090a121b060f3b01030b03070e041a0601050a0e04060e0c030a060b0a0f03051f030b0106080903070b0a0b0a080f0c1f0f0807180e07170103020901140a1e03 73
    0x2440c01e039800416600740e0440b11129801c94078401c48e914590f00480142d001b00b8152a80d00d82600900d480003c0c1c0030680003d0600c00c0707014003003100f08100b1203141884046000c0744c84c140801c4062001e006598400d241501c11180054400105241c49013400e850003107003292040940c240c004100b0210408500515004241d01401682010036900000d040c500c4420300010401d5a12800203080c00040811010460b525480d01210303941c880c100548070130000d00401b404101d42c940802c844041c008229002550000020342c141d8071a0306941b8054540b0328100d030f9202c0c8500305c006c25140d6003805140c00000c0e42400400724201c01e1418001045208000c0300196041c04c5042d010560b0004896080524107150068080d0303500d070700641c0e07a10b0340300c42034441001c10300340007080c0c584403203061500804140d158034015012402d2500942402404004c2d0000550308c010083c00307900d5419402c120303034028030494507640c6035401b29410300e08550400510b10503181040080c410b01301d00c1b52079 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 965520125 1250 965518875 965518907
    0x306060a2d0b210c031303050f040b190e010518032103101403070311150a0237152a110303090c060a050706051609050303090a121b060f 60
    0x110f9860300840c5010b1a000003010751042c0d03189094158201845030003140c0c211100030941a8a503a00c40d140070490380c0002461283c0200c0030f85010141354020304804103100c405a49417440c00401420103d0701e41d840d007034880d4151052480c03441c403000e10010301f503000702207899846889181080030f601620310141e01600d20000940b05608403500d001c104c0c4001d9035041086070500c008a100890a224100c81c0c2c2c80074046808160002e09580c0800e045007070325178682c0300150314002a1041d14200350010031401c019566a07017180000345007015800041d110004000452605000d21600c2070002d80b050703051980010035112005a802c0282c400c801031610000b90700310f250803108240c1e01d0070b000038014445c00020540c40b81452044c01101c0c10a58031101c01c0c482801d255100341e541e245400480310100b0404000440e0a044c0042518483e00004000c1c55009150001200411040794002c0e52008411200c07054811070182c02d980040c18250350b401c3c621149410020142191851303190 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 965521375 1250 965520125 965520187
    0x90b040e0a180b04240209091305120c0a0606050f060a08100b041715131106071a0928031803020d05061807050d0206030711010f0e0c0306060a2d0b 65
    0x447c80d4445c03400c529400038459504c04191051030030306500d040e01c5401c0d02c440c0910005286288000302041c510001c520404040c48020b456600f040800403100e03841c50381200080c080d11a92500c80c803025600a2186109500941e4503034041c2c1c42160700a4010304040c40d11080700c5414400100036200c038000c020700c103403820790400d003420500c2c07800e074020081c281d100407440040d07c9030b8441c42207a810652010112800d402218004c5400100c00c5580b29664082c64404881c5420800480500c112003810040720041c1181e806403004180c900c141c200300210a440400180c4989040c118654015402000107152030b024008100d0714405441c4c1807074000311020021a1101c0f04c114540650407600f00e9100e40d034004c0b0485040ca00b0150902596080800d07040701e0742c0d102c3d408514040a0b00c0c0541d1900401d8105042d92100142d41d91a00902003807810010b0384606900e8000750070402c0701107202840821042d0120f080aa085944240741c0062004000185040701401c0c0708041e0280e4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 965522625 1250 965521375 965521387
    0xc0906081608132f1002150c0c01021606091718010302070219030b090c09010f170a1403040e160c0813081903090b040e0a180b042402 59
    0x10b01000c005031034495140701c401814010040c804880c1c0c5246800b40c1c03098980c0390090100f00c03186504814450b4040c8a05071007800e00a840072034001d204071040920307512180c82d0041d1100c0c055111038140070b0955424005992045103009501014a01650b00451101c00a04205104202044091501b408204510036441807041030100d2050303005d003801a199821800030501d070301840070041e00c580c442c003a004000c001e404003405010380c0c440b03402c9800c5648403500b4049240310a005080034058210802c112902010880c01e90310070461007070701c13440501ea507150481341c816070841380003d40001c2010300804040d1403030560700c400c0082c000059581e10ba8805080494032500242c081c0200160004486c9205d031034000080c01108101c0380e0600021091903000c0640e50412400a03140e40c400191030480b44040c1c4003940d80c02c51580e1540e0301c401c51048018140c181800c0c0500c03a40003424404102d01c152260b10450140380e90000142c2d0a51650250045290441c18a10310602c60707 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 965523875 1250 965522625 965522627
    0x9030e03190609031215032a0510090b0301030b0a05060105120406051b0c1e0604030219060908030705030411030706050a11120309030d140112081305040c09060816 72
    0x1e1401095003004000500401e2030a007125428032902d5405100340c10601099141c00c210301c814403c40740282a0303c900d9002c60b624118404580c00700004c0807a02c00301c000d110503c0c250000300c05424003801c103a0003142e641c030300040702900300760b200341c4550340d0240c10000942800e0054560140007482c05503d414103148045c08190b0018102400f219910400070f003804c0880c80d6020111144080101d4440c44180d002039038079981c008011000c20100380d00b99449900000e441d501443c0d258015080b40210251043c1ca500100d00090741c14a896071a005e000c10350200003035020301090341d10f803507891070705040005440b61010006070195101e20b40402485611005031480fa1507a031410481006150030b0302403800c1d600c0011141020b0000040c802d03042c00001c0244240a1044c009000002d0880900000c00400b44207046030345010760007000000303142d4001880c2d40903100e000b0611a030786130313408181207c0c0c49410320700c0414070a2000b0710409030040c0c407459203c2510000b0011101040c00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 965525125 1250 965523875 965523913
    0x13020f04180b150c1213091503140307060f1802091509040b0105011e140c0f010c0201060e100312050f0c0673021207020606010804030807020c03030d09030e03 70
    0x104641800d942c0d1030742d11040b03c02e008c0b010340045400210103140c040703030b2684940c0c480c0c0c015401107404501c3d0110280d00716015000308608240084000101807040e5000e0000822000700442001e052007046a40716598a0070742901880c01401545995070610340007414582030b00c010030101040314040050000d50140088202c0a044101d030fa846500b41e0078103138500480500304405a500f00a0036080c0103034158040030403109610070000c81074a81a580d8950046c4c0e6010190482c0c0214004030300c440d005000605100d881414002c0ca004007490704941421401c0d151807480e500464508600481e510b8096111108804042000b04192100e400b00e00b0000d403420328404031084800200600c0d94101141c165890900112028075802140c09c00a500c42c5030003c1d00803802c84081802c1d94800200c40340300b844180c40710078164490791015104d0904c005c001b68114440e0041d0030102d52000d2000c1e2020249540d0041145101c40c40d01411b58241454414000d520000d0f4409076150464 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 965526375 1250 965525125 965525129
    0x607060f15120b04260c0c1011030a08180f060603010e24060102030f0a09030317070c0b04020f03070603090b01080610090e031201030f0213020f04180b150c1213 71
    0x60b401003011203a0424021032170980c0703281507160300c0c00032800b1542074070f0100e6589420842140c11103c9500400410782e0709000904008003503a0007807140d9002d203805405140e4022400b840100d880c9a5a44107462074a03116441421058201d40144045801d00340070f810049130342e24010b01700d0721040d100d0f03000c0709242c450854001c180f0f4a9001c10307801e90080c0304640001e00e0b0001e0f140d07a501d01a0b0f03009071807007a880c031046000803043c0e000200030460490306d46000300c0f03003540c491400818603103a08a0340100079109a0b1301040880c0b4201da039940c1001600020103454501140000c01c900388034508980c164000c00142c2c0110f0b0400c00c07034011040004081d55000440007500a000c40815440d600400101c120803210750400401440544500101e04502c00c8805150640131007451209a0184400c0c06521080030303c001d2241e59040c00300b0203001d21414000003034403211140020030a4100c140210390381040090307150f00500007070100d404000b803801049850400800290110080740e4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 965527625 1250 965526375 965526383
    0x12120f1103180411190212031506180402183a0516030c031b06120908070803010905060a090204030201120b040e1005070e01020c100e0607060f15120b04 67
    0x181c20340c10305039580c0d40c0513601095908030000d407102c40c13080c807100700d501d18101400003522a0080001c0800d082e20200e82c4a95801d800014405548106016490304910001d818101d05034144184607141c0d0300c090035801d0385c01c805801d180c0c0c0b80c90b403c0c000840c4a03041800e14205c03114603207101464841c50b5446102500d03002d144103041c0c1d98181142803c1c1210b40c0d40e46424251301000040c08030140b40d0800b80c0380500060154110b000c269400302188902c542c05c04181455076010390303113025600001c0058040c902c0d062500d01036644850003036000b42c0001100030b581c1d0050003280d00b0030324000005064a410110b00d0305085030006000c0b80012070070341c01416141d83c071500040e20340b5001211029004400c079407007548526600009844202d031001c002030104886540c0399803000400c00882400a80307041302d00e083d9444101c1d592540c0100680e0440000c0103c0c0d130002da814070940640301482407002400b1481000d0348800e84546500580b0708141d4005400003040c00a00119045944 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 965528875 1250 965527625 965527657
    0x50301060b070807021311091003090b16050c0f100b030a08071b05180a05060a0b030a0c03110f070b0105090103031e030b04110306030d0f0203040e0a0612120f1103 72
    0x2030f501c0018500c3e0a21401c0f40c1500f4144000c0d45140c0b10800040c208640f821100c2003c66450340c5001c40803101c1202c004cd1804c2d11003008108485400c200410466101d454542d00c0d00560851081c40d01481030318a000da81c1c003a510345080c1c4c3e0700c203105284440101714007600105540343c82d90042c41c01100c1001d00841c0d040407562503000080c01481c0d0091070003900e005660352181014511180b81180d54092003410900010080e1415072048030640d02141c00403802d42e1920448030008001100044052556600003901c1c6a540c69016200003041105015542c005601e013030080c514060380114080d8240303800610000342c201400c240078280e13040040845500c00d20080b13011b0300192403920340052419908600f0000036500841c4250804d0f070883c0c80c49000c001007260035000110303c010040e00140410f000074580c0c00b4146810020040020640545074101000d0301100e4990445400031042e24170b02e285038001015000c411590b0604040030560581044d4480c46224002c0916800b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 965530125 1250 965528875 965528887
    0x12030a030f14070203180604180e030714030a020d0f050a030905010b13060515090f090a0b06040e0f0f060105041206110c01091709030a060b013006050301060b0708 72
    0x5031035109034100c8602c0c078100348503070500100213500e0764003a20311402c8888514403101054103200c2c00302c0d0121000000c3e40040004041a000b00820800c00c00e00218001044620046155400380c144044884006541d0f943d0040e00041d16201c80869084240200015007001154000041d58002c05c00d508003ca0040708a01e0307c0b07401042039440040e1702000e4810342406d0b96180d90700040c2510030594881107503034003c01001405004600d0915030046584c03031088030714208a028160130a4400001003140407104d400610150006c0d080201405003c00030001c0101e2011104c0d90464040c01d511199820000c000034814841c0c0d00508103107240740030508082003415402081d98001c0c16807450f44510f0f9010100e4041c00c175140003a0742c203c1e86a80c00c00b02d2024403904641c0d040c01c00800526942c14550b5499010300101e04100703060001d44000d9030040d80010b40b4801c1100305c4c84440c0e40c0841140708070001141d070070b60030aa010b685031140034032448010318111940a9000220161504 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 965531375 1250 965530125 965530151
    0x60904021b01060f09020c060103020607021203040905070f0e01090e07050c060408070215030f130303020c0a1506060c150510030f061b050909280212041112030a03 72
    0x407140785603040e40c0d40365159a040101c601940000300f500e8007450301407002a543c03a1443d090b0f01401d40800031a800c0580100010719007600140106440585820342a0005040c0d141c21904140d0050780b4940e2140100050298801c0c000210701c105428540030400d4003c0008041c0d4040f805007442c04010b540100d01e0301d6005800341e405e0100e600f000c90b10300303113000d180c9282d598010980c200e0180c0540e00700380d900700d0303000002e4910511a00c9400c81203556800381820070781c2c58010003501419401c1001d414201024070100c3c2c01d01e40520211072a82e045e2035004821110540d110f24100700b1f941c0044000030300200740c3c155900d040c4410124080d140c035400b0205815050b1700062001d403107000d41c54100300b49504401c031004164031644580522000040d02d41e84103462880758401442c400081222000d0740c1d903403000e0110015054810058034007203000720303804031040c5001c0c0002d42c002c100800440c81c0a26005090940c3c030386810215403440b5a90380e000c1d07813504605042c0c807410107080c84 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 965532625 1250 965531375 965531377
    0x14011410050d1805010e0304060c080a0909020d0b101e03050907050306040c170d050a030510050402030108070503100c1e0c0f0b071b02060409110c0a1a0f01031106090402 75
    0xa280006020000112160f0440354031640b001012500c0303509020180d0039401c8040180d50072507010fa1240c4102a070955100751036548444400c80c140080d0500c081082101440644100346c0e96130400501c40241e10200310141c1c00e0b608800f400c10102031454030000940c104075901e002c4460034040ac26490320401d10342411200d401454151045008000a0040404c040c01c1220301c04042d482c030895900c0009070b16a205002e1810124004014030342ca01d620987c0160350050b80003010440190711000010282d920070ba000082c10340c084075040c0a1880d051100c1d0401490725402000960403803400540080fa02901030395011002c507190580e5940101884403000b94042001307400150117160040240341c0a943c04000603c0b19135500501d814002048040300d60014015418a40f404040c0d9002d4807510304207894901d001d10413417407010030401c0400e1b03c10703200d40e20098030b0170349000070002071081c000c2110f038407210010010000b062040d81c01104110b016a403060b610703820000400d000e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 965533875 1250 965532625 965532637
    0x14060c01020c06130318030f02120c040e010e0106060216052e0c06050601180b03150a090e24040602180612090607021f09031b0f02041401141005 64
    0x480c024a000c00070ba5903200310616004c0c0e440703519040306074002600d408484203003c1c000107110032408130610700075240010380b40321030b059014204c3e141c0044200c0410155080381d051150240c1d101c0b120200e2801c001e026000140a041c401069484080c0741ca105c8800528441c2500811003441c2404007084920b00591003407080e105000441800e0000042440fa2300e54001d40e21946000c000c03903a01e41c403404542c2004c4150b40140c10b0000e05100201800751300162400e4110f110058401006458659000c4000c01d0751640c0000c00042e0035084a003001000c0d054201a1002000e0a00721019040d00c131503001030f080400143c5460041401d41c405c0350008807070b40c0d0300440c00b1035562140241101680d21038642001915100c0d25400e50036a5102c81c00740d250540041403641011009001c1d510980801d4000e10f490407040302e010700c000d92003114402c401d44080d0355060728a0190708150040840d45001140840302c1e9614004412808028050030288116031080494803494450025500 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 965535125 1250 965533875 965533897
    0x12060b0306040c090f0e03030a150f0b04080708010507050a0e031609090203010605030607090e25090f240c0c0819030806060421061526010614060c0102 67
    0x41c41e400d05081c08440c1d03445602c00c0741039403405c00048a20300c080e980030f0350059031042002035085856206100c0040e002891003d00140c2541d40002900d220071840c4100401d40b0b03001c1c060b0b88a0500d2642030520000b500404400d0703042c003052000f415030250480b21900241c0c64005000542180081d09103224042e010814107003d0a010607a05001e0348000c2c0304500c2207008020709036440040c10b40312401211351001141407600108000314400c3d1136558013080d035000c0c008010362002458a1108244034011000403070300394040c00035104060f03501d070281040041d0080c140d4080180c20310301894545004c802c00104604c01410001080c10720005044200c0545005004401401440c4081c102c019000035240c8000714070f03682032681c00c9a058900d12102040c03420038110105460800b040e0b81100c04540d11080880350000e02a0581c000e4017140403000040c0748206330301d10500c0c0102c08150800d9143c4841088100d81c0e103030200a106105481850316040b203100d40d640203020f201c0540d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 965536375 1250 965535125 965535133
    0x280b03030a030c0305070206150d02061b1608070b0409180507030b0613050c03060f011209061a041e050c131e1d190906090b0f07020c090112060b03 65
    0x501d140b90190083e00144400d0f035070802240c1d888003022a03032403000340d0b00c801555549170042030321801c0ca00307010803017203001514541c035010200c40e0500300481101107510750358000f03101c1d58180840c50000000100102c078014080ca0381043e184800138442c500c0b40c40b007520742d500f00404c800d054030815400025002410f41d185142d0302c2c200070600200807030342588102817901c1000d1260318107201d4140180b400468150860351003c090182d5142a8030846042c0302ca81c8400c030080da0440d0141c03655840c03088401040001070746d2100070304940d603401200e104da0f00700100c2804003021038048000110091a020400352540440180c01d0300c02c949060340f01002c525004a0950070556603041202c7c0180302c102c80183e81d45203044400070000c404000444422030205911181c090104e0a000c07004103800070354107550742d94513411100140300c100d0b80f03d40781d041000f41e2400e107820303041da00c6009400035144810f29040040c110703d80c14080c0000060a40b2160000d2181c81e900513020340f40050115 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 965537625 1250 965536375 965536387
    0x3051308071a01050105070816050114010f0e06010e010e100e060714060705070c090903140c0d0e010f020d121103091c032d090b1f0509280b0303 64
    0x4607450300000e82c0044030600540b400040c10754030450407203c1d83d07a00035280e00d082c0f814010307101c031054103151426103096480701c81c55803080100006070741c02000ca80c00000c100a1820b41c0340d10340e84000400a5050014400000300307966008200280729200c1221300503003014140c1000c1e00d2400480c0102d9402100220b43c0804109031326034640300c820814000c9400e01d54441c0c000700e52034468040000e0100c55007180800442c42d0175044024010b1090401f03036420300164101900682010120207000e80c0003000001c00b81390000c0550040490138a0051002c0c00d14420280d602c10006142008010306150b640502c071210340c1c0440c1d1400030340f19615a0700e04044004c5d580c9d5001c41c00113000311000c0002c110012034000c1c46111a00100c54509400d02102940740f020481d690043c40b52031303191901c200c0000a000f0301e842c50302ca000b4010151520107100c41c111a0108140c2d00006d020301074410910041152243c000014040a029000182c2e0050b0040c18003511140044c0c98041c4004aa0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 965538875 1250 965537625 965537633
    0x111010c030209091501020703121101020d02091804020f060d0912030608100e07050d020f3c0307120309092d0b100f02030c030f07020a0b03090d0305130807 69
    0xb002c070003808079404d000503112002c1d000043c002d6011100e0250788801420000101084940181e0800354101540c1c0c20b104140303801d0aa078816201c51000300d03800110604249070040340c0c8154a2030400d10460b4507c0c069010078401c0440c4031030240b1404000c40c45018007409a000b50805a9000d408a01c1d905640140900501070340d00a0702824041c20070b16400c0d541c0c1611440d8072122215000b07101107803609050000c050101101030b80c20070141c040318182c40d203840c503c0f050070201c0390108a107001c0304000036202c00c2003560243d107031000404402000941d070025010b426285a40040c04080104c1d140a40306003045a0003454100c1c140402c2c075001c181514091f0740245444411480c00448a1a0300e0040b1804000d1503a40101d8050003007245600c115170149a8480c5c03030040b249030800c000f80c4546036070090007040c6c041080006840c021420b02400c1080100401d08101b41582014200d03980c0b10300444101108061fa24000200c1c0c0d014070104441c03980e50446c0e0b0040d0f4445403424 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 965540125 1250 965538875 965538877
    0x1302040603140601060503040305040302010e0112090b102705062b030201050c0921070f0f03050c0603010308030103080c031c0509011406131e050106110c030d0c110111010c0302 78
    0x6401a07441c0900f40000075002d0190382120b208540c1641d4940c5064255030042d00d46030041184141040600010300300300420a1160300d1440d030060501001c01e00c0d196010740300900058214031508049803110362162404110340a45823402001c0c017184c10343d40c0e800450141e400f5021440740300c0d00c540c1c440e5509104243c1e180c000c014003d0b4020b0045554000d0310120901c2201011504a050b5200044040140301c403213a0844425900391119250f84946070000782881341c00c188406001440e0170010020b0410100c40d100605445150441d89140c9514a95001c1444041c003000000900c103242600180300311145204040c88500800003103071121b400619003111036054a601c4c100e0b040b401c800c280c41c580351143d6070042410203094120a8a480901010020300041c000500210310391180e484c0100b038040e0185d035840c07240600400c40601d02d414a810145806504903c01c006407255100030303c0c00001c2e4211015061140142e00102c602103945c103080c0f404c5500e407102d5400d116074190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 965541375 1250 965540125 965540153
    0xf03180c030f031d10030518030301080c09011d0105060a050405100923100327030c020114030c040605070302150c180306012d080a0f060509061e1302040603 69
    0x1035540c442180f050010910b0001328400060b43c4070001c40d40003500756201e9000107510100d44014250040c07040020203280d40c10030703008000150400200c104450400c584034030b0051a21882c0740505182a04583c40b400c070043c001c031ba006200c00a0364140640c0504c1c00c9a005000251078800d1800c410b49000b0107908030b5000e074200c041e441d080c00d00b286400d10003a8246080c00100103030200d0018500c01d03802810f102c0d900b400c401420000821750b40d4900003110069034026140e068480c505031000403d207a90310242000b06400074801c2c4078010318a4030541303040d03d00f1410221303681c02850070181e28043c03085800001c0d611080d020420101e03402405010209240702c0c4c840c2d80c9442a20805072188024041c80611a80422742065008080d0320b0340b840c51344400040010281d200d400341c03404c20a600c8001c0d0b40b00904103070110f0402c102441183d5000c1c268401804940c18440650524800340c182440704906c2c2c0040401c07460301c01c18814580c01380c1c0c010010000e081e564a84201090011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 965542625 1250 965541375 965541377
    0x1509030301380a110304030506010503060f04030206010e04060207050316020f06070b06060d0b120d090e041e11060403030c020f030106180504060b10050c0c030d0f03180c030f03 78
    0xa507014070000d055408546030004000b410b80c40602001410406460304409855400c00020100500c03421000703100400c055801500685035543c140700c10f06141070b030041c1211030000c104004000c00300b5404100310b419501107008088240d121414048042d0150b10700281c080e0000040c401c13207100c00c0300009001a40301b40c0c0e80c2008034480004000043c022818060a03071082000010541c0c0351500c01400001c10100e000120020800c004c146000010340090400c1e611103203003801c3c0d25030000b04d40c40050016081264051810740e1700c5005495200c5042050544450041010401c0030000070f514003002404080e00c40d5034074103004041c650740e8807080e80150343d0050034041f01e00f010b000d03100030f43c1d4140610001c51030f8200032100c000c0c035004000783c43e1556103648003c09507a40301d03c1170760b071205942d1720b40348c40f80c074104139031420b01013a400b4035071090b804202d18240154001110380d81101090500146c0c01c00c199805560b0300e0320f05c0ca402007564100c0c402c04000c00020000c03280d001130003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 965543875 1250 965542625 965542649
    0x80729100603020a0212090a09020a05040e0c0f0904020304020103060e070c03091d06121609020405030c0d021f1b0f03090902030702100b1903080408120313141509030301 75
    0x2440d41d05404074401c244920005800c400d401480c004a5540108026940505200c0681c0d664140c1807040340c001c1c51071480082c0c4009403c0103405440c02c62203400038034040405107051980c0905c41d03d20311914028a0183d0f801000040135680a44e200034001c00c5004020a11854203202c01043c428001e8011400f1600c001d1011a114014000980a441c8030071086001611132804000c1c05410103a040c25031381c45801c25a5044184801da590700030306c0d212501503100d6040070105818038900b45c0740300f4000d51419a4030800750351407045a03da400024003000c1246c0c00c4242c4100c4200341c18a0340a00b1400c420910b034010082c50803010303115140170f030703a40400c400e4032090310f50305030f01c0140c1c2e600e00160300607050030f0140415170b441100e642a00601181005038045100001c158142d030050300c2d50031000c50104007200c03043c040e950282140403689455450f02e544c040b1171100c0c1101014025141650311500220340810620548529880d9103134010325001c0709041d0307264024000c1c0444d00798 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 965545125 1250 965543875 965543879
    0xc011107050307270c0503010312020c130509070902070803040b06030a08091504080f0a06050903040501120b060c0f060423030a03110f0c0a0b15060708072910 70
    0x400418450141c0d48024058000310386410450843c00810110305803a4400c14811070b0340c0540103100e402002c94680e11441c0e140d600d10f0601d800e040d0751a504e8401503422028003058240d0318100701c40729075484404005150340300c4d49aa5403402d480f6410946000c2e10000d9600c041c001d41001551051344564802c861030b64801060584445913a60f005010920070b0040103c00d103010560800703007080c0c0c2c402081c1801da41d000388600e01010542c4a0025800c580f000505109860140c258040150b1004520300762401b00020044468000480d04007503458540f411240c0e42c805c211510340a2140c2140c40b0340101840042d290a4107540031140c1e5040e50442014401008082c1c1c403560f403041d8040d500341080c0240aa02030090078001e001c00c0700081243e000d0703075040c02000e07000032341860b0020b00c14400c480c50800b0540201510808030381243d0701e10030541782d403201c0846004c0742d4481c5000351220400e2422510100c3c0c58108402d0b551001d06034030b01040c0089440a10520301580c00c0f6921035 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 965546375 1250 965545125 965545157
    0x130311010e010921020d0e0301022a0d0906021e03120c031f050607060b01020a1b08060f0103020607021302090402040b09040f0b030316030e310c0504050d140607020c01 74
    0x1801a06458005d80c01c00300f01d4024460003400300c01c940c07007000340001d40390a01e90010720070607100d9050402c41c0c04e010a100344046c01c000704004052085641841740300c2c00c0c203200c80650758600850041603c100c1440d0121140d000500039600e854429407a400340d1414540a45000e9401c100c58800801240e51412070f00c40c0c0300300c8030300c1e03045074400b0b040c2c2894071095032030f202c0182408200b00c60551042c80b080f9000030781510f548140c070504d0740f80c0080200d4242701030b00d401c059001d40402da004544400500c0542d403154100c9001c1541150070003641c8400000307401c0a809904801640305201007000559001d18000034070b14910110303800c201d4240c502d41910300307d55690340403503050b40c014001e5501c040e608a0080711102d011741440c10b000310190000032682444110b80c009039640b0011221415200014034030350001c0800b8017841112929580205640920300ca242e101e00c420340e10381402d01c05509920f686290f01c01003a10032030b03d00014060341c1da4002170b480d40c0c005100703188480c1c042d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 965547625 1250 965546375 965546423
    0xb0a02030901140a21090c140f01260403090803070305090f0d150506040e030f0403110307031205031503030a111b0a03020625030201150902070506130311010e0109 72
    0x4100a4071016040381c900030f0030320740000b0800700805c10303607a44403030005c080f42912640000602e8a02c004410492040d405c1c0204407226210003414001800c0e5080b038220000d012130402c0d02069800400c20743c3d52030401310380b11300d00c9903c0324581c0e000004e0309070305041d8820020540810251500b80716000c206003401070614121601810703d034400346507446074000d950081e80e00624010b0012030185c03503144c52981541d00c001c064031111080003400b00200024009004010304044000c1c3c0030b860718584850410043c008a020b0070071400000141000528010b2030802410140481c1e88404a915001d000c1c690010003100c030340c0c410600c2042407414008201051400c2c0900016000c0e49940e0a2000035044a100c40c22a04100c048901c06011a001c01009442c0039074000b08039540d0101000030407462503009800f10718010030580300400c90000c0d04c02d800000c52454032000b90100e0504480100b030614011256508100140b5409041504941030b00c5018845502c2d854000702204843c1c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 965548875 1250 965547625 965547637
    0x1002030c060f06030c040b01090f180606080103080307080405011107050a05071a07030e060912150601030b010807260108010608070b0a0c151e050106020d0305060a1502070b0a0203090114 82
    0x101d5446100350308200c6c10140c0044c50041010304107900e809446200c40c803910040c40c1c00c0b451500032580e2405c6070201050290000901140c20031840a5040d0f031210a074510000300924180321910300418100402503208502c210030301d5900d1038450015103025900d4038103111050f07405100e200c2c0c000c81c0c0c008400d4050790b03141c0c034541ca03c60314158031940c05540e51155400c45582c03002061109403a01c0e12684003100d04000b40c0000340c10210003070048c0082d94000a01100d0415180a03e00b000698004e1041500310030941007000411034903400c000003d80701089149881c03a092030000424040c15003241d000d40310001c0c1612641900c80248400701d0061451010004a4000d01c0c0e03008201c8520300030802c403840e00400710300645440840700b0038103505a00364100740c0e41d90004008003a814005500c150003036207000d00c45403c0600c0000c1c0504058011034144000071000302d03420754020842c2c0d80007000d102c00d607140c441503001c00181d00c9130400b24896010600c003402076919105541d0440e64 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 965550125 1250 965548875 965548879
    0x914060103140a0c111b0114070b06060903010f240617070e0d0804030507060806010c02090423060108070f05060424050c15100b0c1506030c1002030c060f06 69
    0x5036112801c10000c0c01c2d130380340c0d89801d1010100041100d8401400080034428050710134a4400c002c101c0018284444034111900d2010140010000920015804c80d08402c04960664688090328006030051041860288803146400e18a001c00d0342a12103015250046007101d0506030b59801055511000040e02551842100e90006020902070315800981202c050022104d10320341d99030706100c503806600b0550381940310000810504d40d01508803580a0401e19200d1010700250307020825207980030f403004090a0b8041c0c0024a0102c4507569075075821925400c64900356580c008090f01c8503420f000342111540031740004070f0305050110884040310141c20040303841104808230190036818103500c000400c542000f1035210074504005440950b2610200303201d07181002c11300c41d03542c07800a03440484240b4040c0f103500d003240b80209180704c40c034040c410241e0300c6030349030300c00a801c04d44c01170080e41e4880d0303100d881c0e0851a54000060f103902c44a01c022564503883c1c0150100c882c18044039956 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 965551375 1250 965550125 965550161
    0x510080c030309130c0905030f100f0c0221160b060a1a040e07051611120f030f13080109080705010b1f0c14030c030a03110406090e0907050a0914060103 67
    0xc0700290085c3d00440381c00c60720780b03407504441391a88000303814100740000b03020b0150b1103100d201d03048220314891603198110700303141003140d030001e8000a5244c600030540444180d801e0400340740100304040483e4491881000f02e03481e1080f852034131120942082e600c590041d07680b03640100b0107601103000242c140e503088007a2410545055501c0d442500024100d000700401070103c9280c006420041e100307001e2054800748000b166000a100300040f031800401455880a40712100d02400841110703800b80003501c0066890707040e62512b403882e0050340d000607503035843d00001c0820b006d21600900701e5544660024030007580c0754010003100445245280c0b8030004d4403030807121000d0090b850304c1506c82c899040e40340450030324400b080c11034001030171042040c5c00001d003201c100c60780f40c0304410850184690103414181007a90017844003080b8080da08000b042e01000c5820040b0030410200105001040303d04440e8580480a014105c0b640d00520000c1c41c1c4008031300b45600a005c2d0250740082d80c0d581e0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 965552625 1250 965551375 965551399
    0xf0c11190f03090801020708030402030c0f0a260708010c022104211a010614071101050901050d09060911041a06090d141510080703030c0309090510080c030309 70
    0x3030303052141d078041101440075100000411107000e0002d882c106001c1c0c12050380300d1805006050400007400c00f80d901c1034146031241b49c0705a483e02c042d0000e4815540c00e810102918a0101d02d054801c500c1d0041503206280c00011940415045100e846e50769500b6207420888040c015914940088140e1660000078082030201c40d00518144559100341c07007241032468072170f0715040301e1503c07032881e01c0d6400f14262005208440d0020000ca0320104009100d81c50061141c07510b1070514103511035a0b04101001500322420f038400c5003559a0400b000004000d00d01c054603240008040e81c14046401201c000c00b9150686014850207220702c1200d0b410f000c60741085010002d5580c0000c2210390b1044a40c040c07240801d2120080f44c100840703020040051803c903c07103070340c0c0341100108001c450080042080c0150341000c61030004136503160400403403c100600e415180d00c0700c0da400041400f0329003820004401c8482c40d2000403640190181d6034081005000d264891041d1001e45400502504030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 965553875 1250 965552625 965552633
    0x1603080403020906040216051606021209040905150907060e0f090a050604020d11180a03030903141c021605011b081804020c16090504021008070e040f0c1119 69
    0xf100360301c07902c014001032400c0860811310406c0c0704454816074040d4065407040105601d400700c9803000e48002d000400d40700d04010303051056803160a010601440e21600c1c11070402c0350030852400c40058510500c03481e031a2015500740d451039031b44920400184d140c2800b042e98140002c045d54100d401415110403690b415160300c020b03200207030105421aa00b04104074190b9031511444062850000301c2d00e4ad00d6104a5001b07100c00000b0803070b588203a540d41001c00000e80c0050840d2f0480e6801420100d80c200780211950031300202c0d0710307048207800b150111071041c00c0d0301083d1403d400c0c80c80c01c3c0d00c10301c003910740b00115401a41900040c0d29038041d103094901240000c00600718020351a03462201d884007090100b0240d812440702d01185a1007900250001c40503100158042c0810380da08112a01e000d030001002c04425809400030f0000700000301d080140324841c002440100500107001d81262a034441d0020f00c040c4800c000000d5417042c002c0a21040425441d0070313406010f5040b480990342d030321 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 965555125 1250 965553875 965553889
    0xb0f030a140f0708100306230105041103010e0702030d0c03140f0c0a18082d06060603061e04062c0112380a05070f120522050f160308040302 62
    0x170a4074040740051100000003142400796040081c0d503000807040d40d010030b40d29003c903824180c100500c17403400d0841d4030950901403030a507411242d000701841050303110050143d08610406c046040c0c414146010010343c0343d0550040d440c80c1e9030348822292155680d640c1e04c100b02500342c40034840b014042000300b020300c0c86090441c032485007201140302803641d03c0003454542814501c151986025054402c40d02820700980790380c018090002030206c920b010f03000110a440020901c074801c6070b20101314030b60381d00e602c8001240c440001e0810013015031a41c2c500c0e050140c8085025010920718001e0081c01c044464205048655480d420540401113a80b501c0a580b04140c00741006a4034200010010411510850403211040364641d800c0c00c2c6846c061090b640c000b0104814031000f0316110005590298003801d203422110800241505c80a5212400300348541c0e04004544108204005111700400c0120300e0110620440350119032000412401a0b0b2910001c1e0195505000c10800341c20030f05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 965556375 1250 965555125 965555131
    0x402090f2a042715030506010501050a0306030807050a060c02030909040b04140303070c02100801082a0612060f220e03271503062101060b0f030a140f0708 68
    0x10002d09003515508915908041400c1d2280d680c11036072081d40552101c1e01c10f604000308902e0000a000f801c50700c07920303036404041c45014100540080c10444003807081e40050b028690203039410b90741c4e2000c1e091072030351034207144800e4030124074100c1a00011800001298080b01c2c02904000c001da0781c40d00c5802c8240c50040c01230368140b01f02041201040030600046209545a4443c0d450090050050181c0c201001503078000740f0920500500144400154000100d8003405254a008000160745140d00c50966540381e04143c01189541d525400c80c050303144a40000d0303541d4604000340c441004000c00e151031013099030f20410a0b4a482c00e040c1900200740000703001c001c0324a070010f84e03c0035000d00000c000c03510584403282c0d0b211181e0381c0707420302d07a03912912911035405040d400c0910004690312840701107441900c0a00070980980002908000010000d100f11143c94120700490030b4001c0c0e004582e590600341c80c0500245610101c44252401910040381000d000c1e030f1101c405a400300d03009 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 965557625 1250 965556375 965556451
    0x31017010209040e0d02060a0903090e1801020f0a0806060708030103021207050d0305091011060705070213050a0504050f0d1d0102011b051c0e120f04030b010306050402090f 76
    0xc001441040d211401132051248011000b010f11141c02a4000e080201c060410464503040c04031000110b54089680c1c01031310703407143c649c854649440e01404640b0ba03038000c20800c01d5001144070140c019041020303102442c101e4172070007000c2d603c0d50100001d5210f107400c010843c07d418001407001d810124200c4440340d403154112414203071a080041d1213407000c2d42c8201c001410004e41d07015035050074401101c040741c95003448002c4c0e2052905094031600001c04a01c2004400300340750302999901c040101183c0010201000035080014018028100456082d12117100b4030310001d40c00000061050806459a03031110230414013150400584605405041e0440d904c490300d00b122142100c003010070242d10b030b4540c2c42c0d89185c503100350102c050340031241e404124a441200e2110340703c04070f03104100c003043d0170716583e030380c54620810f1181d400b40750000390144250b88004070030015960300aa0113140204e48840309030307980070401025240111120060119140050b074014130806071300d0311800d12070b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 965558875 1250 965557625 965557627
    0x9040609080c1204061b050601050f041e0603020a17031c0902030d020129090118110d27030e09060f041404021810060522090203070e01050310170102 66
    0x40081402e1410f103074280d80949850f030005040013459001441c8442c0511002019991056103494540d12002c2c1482420702403174108555103c01d54031540002006d14000d054070b403035203a15111440040026001c101e01030821a034000c5940141414110408190080214500304202520360384414101e0a1049410789074108540145d405100e2400103151aa000141404911070a4580c0c00c040e880c8540404202c0c00e010301c5030f0f440b0010214191418602c0b481c40030509903030326400404040343c0508213028007107114605020702e40c000c08200742c16001c40807100f00d010348070115481d5500000501082c41900c070b401007410031241c80365000c2401130800e01b244c07004201050a4681030680d1260380c1101400300070452030b040b1400b900b40940d40c201d810540c50400c0f6807840300c2d8450b0152906014010a1001d140c00072002c8045803094401c402241442c5e42c1e031201006500180c81c80f1004c03c180001d001600d52081e01503a1145c0300d400f03420b507a111325280e01d49074240d10303940e0501c20b5550 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 965560125 1250 965558875 965558887
    0x160e03100c0c061a0f0d050703050d050316080f010311040e01180215040302030c09040c150804050f060907120512040e060109080d020d2106090f0c09050904060908 72
    0x69104084044074140c44001c00841c4915100c01103801040c4403072a0103040c90811030181d2074408000a44000945440380c0c00211820128a000565400103040d8400c12005000455001313024500074080b8a146a030802a6030720161000142120584c10329204840104003089140c0399001480402420000d01980e0b603050785401d48100010300d070000301d00c0320f00801c00c40c24021040c0d24501e68001b1f9481c1018290f030300003a254403943c001c0c030f44a00780d00c00100e01403104050741c88000748096200500d5290200c8000381182604a4042c3c40a0083c0044034050a101244691061682d04090b00c903040c1440721a034402c44088030300343e0f11880b5002582c010990035030001c0c0050100c400303c10b60f0b175250250004207500042e8112111503000340c94008a02da8000518080904442c28205148107403006917041e4150a2164030414a080107000184000b096104030201c0051040c02c1c01001140d0718155036540070361103010342100e0000005800b2030b18a5102c01c0c1d08510030045146400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 965561375 1250 965560125 965560153
    0x109030c12030f152c07050c120c01270f0b0903090406080313081902040b0d02100806030105102d050d0c05030c01090b0a030507030e191406160e03 65
    0x40c10b54492800702c04001c44e0900c05180e070301c80316103107030041400030201100b030240c252440e85034003804000c203114011580c0b40315968140942d0300b00d50300c90040980ca5400386035060307020b0a0381100540d281400ca42c0c80102802e84184910343ea1600702c0d01000400c1080d0f07076100da80c4880204007040f01e00081c0120aa26520317070060300014040ba03001181c0f504120100312188106550004ca16035101807003000124072071005245c00c450701214000380d0364805a0110fa00c101803144001d5000720690300d244051500507186070300410301900208060b640c0d481e0400610301442c0a01150191070000014044126100781ca00b81a22682c031150b84640c1ca001148886501c07035012034860303510320300501245c10700300402581c0034824642543e40300d1409000146c107100d941c1a01041544a000240486000e0341240843c050000c0803550220f90401d0400e0807042d0440c0101e4a107000d002c04600c909100042c03050054000440108034054a2030f0280c41941d801d40103150075009075900415a1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 965562625 1250 965561375 965561381
    0x50904090809040c0318030f03140a0e06091906050406090b0f0103060b01020a08180d14030a030e24100f060807110f030409020918040f02120109030c12030f 69
    0x395200303030a015201c00054040005560052002c541003510700700507a04001403a1603503103c0107402d42841d41003000041411409881d20501480070302a40c8000d110081000340d1194500c03d142c481990042d40780c105d1000d4807100485038140064540300b48103804a0020b81c0003075002071040c600060f0103000c03562400078200301241c1001000304002c5c0104244103da0007944100b000034030280020081550380d0140ca070155070441d500302040d07540c0502280d00d900780560500c5030003c2d98507091640c0821641c1ea00e912080c4a000001e0605034041507100000403d12608144514010703220f6030320750b800300092200104204100d403070849000030121040f40415014051540d1014002c1c580600007424010682540e8205c80d0b1003581300350081403002c026141555008000942c0d64050000011950544141c660f42d0900c0c3c58020f01042040203115175841520035a040c501130b88103c00036908a4010080c054045403024003800d00081d8a440e0402c4400c2090400249101814101d2021 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 965563875 1250 965562625 965562641
    0x80706051c050901240b0724050414010c08040b0609040c030b0702030a0f0e091f0302210d0503100306050c0f03100816062a12020304050a0f060f0f050904 68
    0x41c0d65910200c044440d4044040d00c01680030032080c00c0d41443c0a4161b401d500c141d17503000c3c142c501d50304d5590300241c00c060014101c11041c01014072890409040c2035070b09604007038280c0c01540c60704081040c0580142c0345140701d9600564810f100f5960340c1b0600100603801882241c0c1c022030f4082c040300003144102514054102a4011516412803142c0508046d23181000c041c00e201401d541c810301541d81d460403a900c181d4194031140031072080f103200e001a0109810080d44800c0d58454640500108020381c1c201a01c090210348050f100c0719002d946511040e1407890801c010001c090010804c20380102d6001900d11b00385929204005240c007040343c201341d60310742c18007140c0141088858070401101a03081c4400300e40302c103030b01e281c20703005000080d080300d00d58181c80c6101000b0140b50707501001f03c030340c140d0812800c11078649410002522507000b03019441c400d00c00c030803000c603c01c0082c2111409440b09a290100540070300ea81c180c0c0e03404002800c44080104c10460104140c5903030040d404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 965565125 1250 965563875 965563891
    0x203070f030507050712020607062a05120106110d0e010e0603040f032a0314191808030a050403020105090a1509170c09060d081210080c0307080706051c05 68
    0x5114140c3d440c0690a0500c41c0e4440d8601c0d4510500043c00b503620031040b5105180e00000c0002d541c042010200301900b0346082c40403840c08421301a0692175000700c003d20f90b03c6c1180c0d0042085a80b01e0700281c3e0340310100d00c1403512650041d64141e0009003c0c03c40241107810505080d03850051840001e0710340e60040340c085030b018221280740010150807122085000d00301001c103140c0311010071484590040c02c00030140c00c010444e40f04210320f0555100300e480d00440006290800307014401c020b00414500582c030038682e154440c0014941c2d1001c0140c42600c101d9560b840d162500e15001101c00381c0102080c1030303000042800010301d40d892040b00000300c10082d01d41d640500d290000406101402d0000070708140c03c500070b10b022aa5400b807500c0d43c0050102d65053780c07000b83c0d05094441c1c1c0160340c10103c29102c054180400004040c5001d4111482c2d04106c86945071b41209058850b5014400e0282561103040d003800212b0048000e0030018001c1505406003264968180c0c040c0d07042940c11072 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 965566375 1250 965565125 965565127
    0x9180703080a080f190f02041205030714031306031a03010c08090c0406030c050907020a14070e1e01090b030a05012c0303012436171009030203070f0305 67
    0xa0741074100d80b01c5a4086100314880500789030008020310740d0740294510f1003c0686e18203500c0c450a50030340c1a44e02420b4040908403d0010503c1c0966681e03001d01c0c002c2d1034015500c0e11380c00e08590000102ca01c02041c074045281100d140070f00503809045027003034507200e48e0009840e6450783d0b00d00341303d104e20840143c0d88990702400d00e000c0c5241001031140310907010314148007062011680c8298840b003254410b4480c10b595941d51403049040800140d4010014000404070404501002078840c060303030a415405800d640b40e452601c9654950b401410035280400f40040040c5603080d400b0382c104c8000a0700b6500e80c04206c0d901c00307084407070111018048400042c0c210021050011840d01c1c6808010021803840d414a20505000c9072062a40308080500745000c4840c01d100d004140d41d85a4030382c50500e030610311040c081844940c0301440741c01c0300410241c00580002c1c4007920110010a54004d003451070720141888016242e01d45c070580030b6110801101300040c00000004240901070f40d285 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 965567625 1250 965566375 965566387
    0xc011b08070b190204060903020603100e09030c100507080a0b01020f0304030b010e01060903150f020403080301060e100f270e0106022104050105042904170c1e0918070308 75
    0x58520503c0c40754034020000c3c03040c0800d100854000722103070300780d070b404441c00c81d2250b465500320300d462011504640c2d0091908420320041800001c050080b00e2220800e4a10003c80c901403082200c1d82184d2100001d103803017001c155044910381c851055150188156100d0380801451580b46900907401262a070441c203004000056071107039014050002403404405145c41c42d1659052103000c4480000f000d0354410107070b08915116030440c1c00450b4000c0040c2d45179a55020301400e080c080c0b862003400b8042d1504411649031003100001600702481d10b03409400d0400792224150f00311860b017083c0e44c83e51100c8003c118107d1400343e0707900030581e590080c2122013445001c1600442c14140c0300000860502080c4001d81c2c0103025078065503810701c0141c8001318680c1030b072240702034a0320039420000c0c000a0041038428115819800814000f82100c1010064606000d1010a07452008ad4409820a40c2903103614044070b0940c1c00880c103400e525034030024840840d0600016900482d4240c0000860b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 965568875 1250 965567625 965567641
    0x32235190c0b07090905151f051603110115030c0611010b0307030b090f060712020c01090213060504180213021b010e0601172a010921060e030c0c011b08070b 69
    0x265a47c8000700100030f2103c03810302004514622007000e41040c1c2d201c24a0343c101c104134800e0060350406100081008110502d50401400d503030b820304082c030308075421305901400c07805401d40d0700c20459034403150800728145002403c4900349850102040155210051030f01943e8041000b10007540c000d2841440a0500d4844285024481d515101e00758014908003c44240c02116410b800c4407802ea01507560b0000e50701160040071000e20007580800c60b11f08030581e40c04c1550000050316020b80b000c01c203c4038000c1c0484005440100700075405080f050040c0648200c3e90040c101039401c4d008086c2501707000103416400d440988800c0201c55101c5c000420034840b03007144210240c050b01014040880c581c009110070700c030000541c070f0903120410082c210103034030407040326009103044010130401c210101030100141c108840d0990328103040ca0441a4400c1e008001c9650510030000200ba8900c20f81d001910703646110040d0301644903800c0042804600ea51004000c440d101d5501100c0a01e84414 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 965570125 1250 965568875 965568881
    0xe0405010c093c030609050f0105011406030a09170301140108130f110303040b040b0d060504060806010e130803070527060708032235190c0b070909 65
    0x221210003c00b01ca0381c1000304101c00d0b00032140c0d9107680160214280100c040300e000360030040c0e000a1600c1d16041c900d0090000104400307105080b1308000388016684c621903030303010174540c0307940c658041c00410120f141ca800591058241621a894007410050419540c0c40700750400d902181e04a44803601c904250341e0300c400103da2200403000c00fa0107907040d50b1036035900075810200040040c50421307106007941e0307410020b40e0000c01c61884071556803501c40e0181c030019007058599491440c107090f400b0540c1d1031709004400c141c2e2000740c000d100307680c642007602c400c18001916400b00e0008007108039020400c2000150f111300d415464007507030703441000c8040d1000b044509038100d6000300f040c2c14140304e070b58a00c00c0396050360300002015225182c920b84d424020001c8540001178005240c2c0c40801c109401d10140d034600302c00350032144414085d117280d107411580d07501d00c84806201040600d1000340f49240c0042c52900358500308264a04540d291030000c032041d1814004114074560401040b44140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 965571375 1250 965570125 965570129
    0x13060816271d0c1309021c021803070b07050c06030a0906110403260a05180405090a41190605061302090f0f12100504060608030a090513060e0405010c09 67
    0xc0480f07031030100c502404070345516580c011000c62a80015010804444810501c941a00c444104641d501c41c401c02d580c00e94000340d0300c954068028080001403810140c81591515a0000090000001904104155540010543c0d114950f403820804049001d51080a80b02080d81c039410755100c0c02c40c1024018064400c1903105413501e0031405400d4035000d0001d4814605440c103161f030f2540c8402e4034001c0f000101100440c0c10a240408000c110500000c408000314040c11104404414400c805401c5404180c2d8440c11641c0d046d600104c4902031907403040300c1003250410381e1000107030317954507545000b0481e000317a4006d9100c0f000c3c0140c600c0c002040381000301c1c415500710b203003044d10f102291403890301e200c01920410080510010944807621850504683c08050710f4160b0304403c4640000e001c1680c0540d1020303e49200811940c0001003114140c8540e901c4007547d0074504410401c0502580c10341c061b0b02c07512141e000489a502840c00c6020b944904004105061200b900414160107030f = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 965572625 1250 965571375 965571391
    0x12050102180303130e1503030304050c18040f0b0a020f0313050c011812020a08100c0f0807081611030d0603060b030613080a0e060705010213060816271d 67
    0x2004242403013003c650b0440101e803494800c289650b038a61000e0380d09070300181c40d1503070540000010001045804a1038070702100c001c444030340003040100a10304200e8000c8900600b035032914a100c00c0807401031000160700100301c250140c90301c2411000710340700780c20548010000030100e043e29001c00c0b5081c407031058815400e20f000900000c4807000340340c07641e40350300c00c0701e9030031010200000c00d64851200c1700c00645001c01c121440134400c41c0401008140800140b00011160814240d1041c81030a030300d801084182d071020b41d20b880b4049007048800201d1509003e0003203614074981640000d101800d180880c04100054440c80e60804208ad03551003e10706100f600010104176592084100c80303503919401c00d10b61510340c0e01824082e03604040175040c440d40b1020104200c002c02c075054000b01901515400307545880396035190240c5401c40705451504010304000c1d4280026445040c0d01da44180140e056000310700a201c83c07052100742c4a8111403801c4021035048aa11110303422178581040b01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 965573875 1250 965572625 965572627
    0x12010b03270a03020708030f0409022203030203031504151e031b03051b092205101a0108010b2d040f030c0609031a0a0902150309010c1704020108040c12050102180303 73
    0x552223020501c0d100e140640c032400c543c00b15501c2c0c1a0480941d026804807869845c03048002d0b00c03401e0103581c0783c0084a0b106602c28100481b0303030003800d00f80034074140506880055025182000030300d0801180a0541d00c85c04400c501c4004003080140c126200c483c0410050b1914003800c600700702e4149034562045403070007990b2121408041d203d04040d2540007a0103c1241c0030b00d03d4102e0050142c031100e072000343c014450b2404500c0508541d52108111031010115082d461110000640d403604092280600c01101400b800b841c3d050310300900c03800400083c50120080e11128948107554202d41c019014a040e441000d104115400d0450740c003400079410710352141072440d0364480e401855240046030f0130b141c40d030108a080300305400072040da0354003c00c0c06460281140c541c0403580c108a49040c401e42c2883e040b00c40890046c0351403002982003c0741821300b0355980e0019115810040c1c812103504600401c00101d407441e0445079456a41300c0c40c000340c2d8a040b02c0402c00e01d444401d803251842500 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 965575125 1250 965573875 965573887
    0x503160206010e060913050d03020306130e0709020306031002040308090f030a050c01210e150a150510110307050102030604140601080714090d061401060512010b03270a0302070803 79
    0x9941d4603554404c80803101d090581da00c0c84030f083c1100540540c003d1440c403c01d862084040d4140c3c018510824041e00c8680000c600100004103560b800e26000300a500103c0d02404580c0b21500116845103000d01214182d8100072405000c80c0d21590003a1f41d950008581d508a070314006201c0204004200c00078036074842c1d00c0e01e400b42ca501c4031010481c14003441d500b400ea4400ca6001c1c0098031700c0400d01040108042ca132088076281d0540100701e410320480f482c0061042030040c414408a0056290a102118107000c1845080001c00303280e175042c00301d1400704d00902c02d01040140f21180c030910026072a82070000c2803001f6a0881200301400c0001d802c02c20020740d9109844c568049541c0c600116031241080aa41a5102da5500c19801400c91110300043c4101500100d00c0c1c4d43e40d84412141982e0b1300c000c121003e02803040c0342c02402441c02c004224000d500c1c07014582010a10791100700c408222001c402441081b40c200300041e401030188170083c941c06101d000c0c018800700703000d549485 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 965576375 1250 965575125 965575139
    0x110a0b03060a0b0c100603050d020f0610031506050603070903050105010b070206121b0f1c0209060901182103030b0d020108070c03050f0307020f120406053106050316020601 76
    0x142d114026000030040100303c3d20400e0f001006440403540c4203071401c0101c240c5a041050300c60703d81390600d8004d8815406803034550f5a002551070700c140700c100c0ba0f001d1442e0543d82e03131030b202030b242341c1e200c3d400700d52601e50201e001d40c0d901000314015085a116124540c0c503514255081d0395050b0f0045070303280380034014840940c031040c0883c1c40080080f090500e559841c0346600b84946c10180d85040640d10105000d403806182c900248001c044241c1030b45186660890200e05034032506118a8002c0c405000b46100c070750050b82c42c260099120040c29120a0315425070203201031100038140a42100c680341030084c1030b00761042140384541500c200d80c00e000d00da00041d040b100050b01c01e000300300100300d80c0000e06102d4002e566066990351000c9580c3c1c10014002540d950b00790700a8010b0b07010314907a21840210342400c4a0884001c0c0d110541441d21200001030401e80781c480c0c0031069031202e021114410b995014074405030265071500b684030b040c840c0001c0707504100c9041c1c2500f5580b006006000074 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 965577625 1250 965576375 965576389
    0x30308010501111f1d07051f1403040503071203050601140a05041e0503060705041d0a0b1201060326270a060201200708090f1507110a0b0306 62
    0x75a50a080140d0708085850200780b03400038011070f1220040718540032180e15040364001482c190400091180441441e021007616012244101580b05a614803140950b0140c1c9202e10038610740da052041c01a1034542a48155030700c02c07501242c0c9500001110800c22020030280702c89220185020051840c050001900c1840c500301400740707130600481c0e8030441ca8030913022a00540a030a511145510507507107010340d1100c0f82e00030b840c401d0181c9400990810301c584141d4007255a80c41000002d410429141c0d849640040d201c4002103890300003c60583d21510406805e803d00ca0000003140d07451343c00c00c00c25203030003001d510542d01c0c2c1c41c0c03c0035400c0e14002c8040c1c0b14130640312405540b2151481c040b0b41d440405151045401440c14000082ca240e0190f12200c41003440051010060300b05400f100711074400c901c0300900b101e10900080c50302d030410314a001d1a2100242602d94010302108245c0300e940c0120400b1210031502840f03810507418418415801404072418150540c140300c0005000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 965578875 1250 965577625 965577629
    0x603040615050a06201203040303020a1b0f050d05030610030b0f1504030b011a0d0e2113050f0108060108071e030504060b01171503010204031b050a0b0403030801 71
    0x4081d2100c40100005012050900041000520080700960748180203850546502c401174044802c0c101e280c540c10902140c140d00c0301482c40902881c41d540c581d02500250481061281040a42189805101e04010309850b40d20700650380015840c0507860403514203416541e00004001c424406d01000d619244030400c440ca4483c100414080884800304076080c18a02010381d00107c581600c100000c00000104243d90203004841e40756a01c0318004a0700b02c0301c0c520441050541082001e48403a9950b000720396035441142601c840303032100348003040c03031034644100c0000c0c0010000340035060004080903480105420307a041c80841e001500041c114100c0100801d0602c020a40041e5049108100c64103200e4407020406100c80140c460040003440d0840c0d0454140345404462010b540c052500040d14044682000e100c81d41c460005494100b00035041c3c6400d0343d0284004000542034100e800342840060841e1070145160004012011010364032040c50711034100001e101281d845210541 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 965580125 1250 965578875 965578883
    0xa060309060f1104080f03070c03230610080106080f0706032a080a0c0503090a0204020c03130e04050706321c0c1e020a060b01030e2e0209060304 64
    0x34a04a4038200600503003030101945125500d40b0341d00c211808500d10190050714030200886550b07541c64505c10b50f40340700d00d200150a030360503642d003080010603200c20b0840501d29604152403259100d8800b914115080d620740d1880060240240303c180703400d2140300014802e000003446011181103803180c4450550251000b0103131075505a11200d5036021820458603000301c1d03601086841030300002c0c00c60f607040d5034003088903003400d503514810351041c000c2e00e0282c1020701c0604440610383d800c00000354010090500c02e80014060600d0041c040560b0000405c1e41452038842c603d05403070000c1c10f1002c0c6070068824018140512039201c0d1444990141d44021019130324004034060071545c1090050702c6100c162860181840d0081c00742e96000341a1000140e203846941032046451400304a0b007104070800160305c19006180410803a400016180394103040c00980c085a10006034140003881e4402410242c14416842044545100c0c0fa105d101c584402103040155150024109100243c03000e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 965581375 1250 965580125 965580131
    0x70f050706090203160f1845150e010212221211010f0c0f050d09060501031208102d08100b0a080a0c030312020903071d150a0603 57
    0x1c0c2151010040110011a15a4844170b80d40d03994075003000c40c020500560344801c240c100030941012013800381803d00942c0c912030300b5102103c0c0100c0544100e00d502d1440c0d20707100d82c1c0300d09841c0304800c078142146640100f0840d07002081301c0c0000d5081d150a200a801244e104100b025000104405d02d2034100c5038030071500c2450510344100040d1000000390140c050f2040c841e548080c1c6801100003411000c0c81d100900100c0741a664201c1254544d114140220b8000c0385047d0801d4400e00045c81c0030768103c1e000050101d030f03988842c8225003098004440d03600d100c0c1d16a1010580205070682d0242007400d1001105040c208011200a1003510701c0548400314a4070f2030749041c40a680e000604416000c8035002e04c91400c0550150481803c082e0003500300080c04940e544000c666440659007140400342c5c1c1034919a401c0f51081541c01001e0400c960038043e1640d5642c0070b00440c4001c044d00c00102001200c03a60780910300445c0a400082481d0200d44800010b8031695005c40403143d01e81000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 965582625 1250 965581375 965581391
    0x1e010912060e060c0301080c150f0a0302130602010e06010902040305031608071a01060e01020a330c050d0e0a030e04020903010906061212090e06040f0b0306040f0506070f050706 78
    0x120380504405115402c090040a0401c0211202d00e000740d81203550304012100492029010f100e0b103004080491a5038400c20003005810854800080035005602e14005103040c07281c450055071460140c11500050f51070702442002c1c0340c41080840c0c09880c000c1e008515041c60340c0d0700c01d42c2d203204103604000c1c02c90000f2400d030107000c0e810094910154010720003000c0000200c1c101103208009001c1e01c00818060703da0b8403199480020036984140e0b01c482c3c1da9400c02d11000a0190000d0b030603500d09800340c40105045451946805005603001e49911480d4854001107405400e4070540f890071300301c0e039008140343c0e004260b101c414011b1404003a2001661450004040303809480448405001c040c00c1c888000354000801540f181c03524043c42d44030082e00c07002d100440e40642188103000c10340414602041861030554044002c00d454854001143c03e180000b1034104403044609a40348030b20705a00509000082c4070150f881015403a0604040e600c0302c0c0d000d0700c140112900500304c150b58003a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 965583875 1250 965582625 965582633
    0xc1e1208011410090306050a15091512050a02031209042304021011030406090302040b010306080a0b09031b24070c03080a020903150403020c0a03031202070507050402040b091e010912 80
    0x110b04080e540150f1b0034801032602c54094030180600d81741c1000d490b02d07042000981e01c040340c8908103410b049001d59444803842c20349000c0c7c80010110058420f8040e035103010006070f0b02005544003007e0150001500d4413808010401185c1c2d2103038150a20303650a44035543c40404643c0c40ca50721681c101d0316800c001c1565441282c0004141d5688009803000007004a005070f0800004411032303208036001d1040c070750303802e00441c140c03440c0e84612822940301c602c22400269200c00380da5070003840501145e06200240c008824502c941d44a00c41182d0070032245001c2447e1b10001a084d02280788002c21858244410002c00352111002e014041041100c003141c11466250111001070000804481c4800060300c461050301c14103940132000740c81410503500c2c142c14a00c54001c100c03500358582c006d4550400c0100e17000781d440920f044840b03029007140418255a07038405000500f0030b20341e003562034101c86010310040505180b405032410719484c11000c0680e0740242001c0542e0354040ca502207014a61070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 965585125 1250 965583875 965583887
    0x90a0b160c062f22050603061c0503040e090607080c0a120b0409051e070e15190e011805010f0501050c120a0c15020304020d0809010c1e1208011410 65
    0x8107104200381001038040c084403400f1300100346010b10880914150300002c0440348040b8490f00b500072105000180481c6400500702c1c2c0700750003544920301c00d9142555824110350158124000030700b249001c1c400301700c000b00011507010295041c24904c50609226080150146a1180c0c0c00c00030402c03604404912113070000c05a50364050018403410a0a142054a601c0c0d521200b008581405d9125914258001040001c46044404154060700c880c51004144580d0f0400305410940c1300b481842103c2c1d010200c0d0b0028035120488410311750603c800080c0a014503c01c0354a131604000040c000c6806501d1403c0c21282c0900308265500d1000c860a82803005400064411120100703407203442e075170408400c02d0054403c2201442491100721454124041070702c019403c98180a0003000140c3c0c00301c020103010005044c41e40c1e03901166900c1c4003016951511140d86108404041c8040282c0301c0c1120a00e040141407821056060207004101c1150344228a8031458240350b6100210380141 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 965586375 1250 965585125 965585171
    0x50d0f06050c1e0901020d18050405132906030c1f1e030905011b0e01030902030712030c020906040e150a02130b19020c0a0509060315090a0b160c06 65
    0x10b1001c45054009410b0744040c0d400c4801350314054091080141003042c42210403000281d840e40e039400556007002d05000040100401c04040d456030090000c01007400842440e041a4402120f21072604030b00d60b20b00a14480034100313501035071000d042c01e105030755659590180d010b016582501143c40016048480c501c6032541c50ba5608124400300754019410340003070503000d00480092203001c40b60300801d0700040030303444840c00051401c540c0030071540c441c1d040041701500080440e00c10075240c3c40e046006603d05c0c2c8044000c036900c20b02c900110306140905951284080318204120b9901900c4c154580001080813886107083c40005650400d40c0c0e419540b08001004120803541c1d11114005125403007410018420840c1d1216900340501c00103045200007c084e2541e01100c1c50a401d01c04803000240049500d80103081016a0410354a680300b0300c105410401000c400780182030003003440c44081d1a03081580500621000442d8108417010000d41d400b09000a41074801403103091500108 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 965587625 1250 965586375 965586397
    0x100e0f060309060708011509120201090b2b02040807030f05190803180c0f0d050a0501150320031b0d02120706020114061311120a02040f050d0f06050c 66
    0x3009206014800040302d074400c4c11140c0b2126801c0c1d0300d403001c0b0340d0f00309003031a80301d0000b64444006000c86094404410032440c410706010024079128040e44285070030550302c469080147c0c06498580e01520342943d080075003800d6045190074204484181c542140340000f42c400c072080491a000c0100030400490080d10b589521604004985011034480e0300a83d107100d2408107006130a0907000c0c2c045407840760140018003000c00c50203520107015180752960303c00d50311400740c0c158003401300300c0c28014a80d60500103500315408506501c1c11340d031614500c002c1c00c50b07000030742c044007540c030b881c005504902d04100c600d55207c641590000a02d020050150003904002c00039141400500001402c0d02656866002401028081e40f42040341c2c1e802240d41c550b0240c203040e1846004002030b403100c8408012807110903d08401034038801c0c0b0b0440c054070412b101c0c0d54000b50070800d8003a02080c6001400c012181001d034010b031512203d1101d0b50811015150940d100c2c08900c004022108a40100c900707 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 965588875 1250 965587625 965587627
    0x6080c0c060114120114041106040e15100507030207031106092812030e1e0904050d03050c0f03060405070516030302130e04020112050a1503051c0905100e0f06 70
    0x503550f030404002458030500d030250081d1486040e11321418003550000411280001245a94503250724154100600c00305404c0f100801000c41e0041d00081d0309031158800380141114054800144008081c07005451020880140106400240e0115244d0106c0c2c0c2c000c1c00b014209001031000442ca84291483e05500c20b135801c4403940d8920322105082c80500010b0302045903256600d05e200d10b0b008210100400051a0854404403450071079000b20321401107101020b1244a001d0100d20782e0320b41070780c040c2d9160380300e8403004440c1036150007001d41c030240c030100c01424818098200403e0f400301800c5544a9a00c440001e900c09200e8810b698903d00380c000c2590302d000003030802074001e5004008070022950b0881c0d0115541500c041198007030380d81a52051410991710b01043c0040401800c1203040700e480b00a0b140c1c4c8130000c00e540001841c0500c002d0715080d02c0da00110704090720016003501c11302498041c108202d40d130300c030303a031076a02115401c2c4040d40d51844000500080d01c0070042c250301000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 965590125 1250 965588875 965588879
    0x1413051603050115050901080a0204080f06090d09060c0204180203032d18060325110c01030905102309030a1106060d030311120106030e07050d08030106080c0c0601 72
    0x2400c04103281a903925840c01c025070798841c1c1451410404044000d004034204002c90703400c4d54811895654825800c52005062070384441e011800c1035142c04034000e250b8443c1c0207000c0020703030a004c00c0ca88600300e400e00317207001450705c80007602c42401010068402c6d652500701701000d4401c11b03410350003c2d500800b40d81c0d5855110072800d01804c2e0541c020790410700e0020114a01c01c1c0208212040015948004414001c00200f00312050b030000341268180c1805a09482c42e508410400101010f403607182d404e01014900312581c68102c800c250181003604200c401008214045440203410b01d140d000800c03091810b082c000c510300c01030080048020384d082d080108050012020740501c500a6031201502d002108600e036451070140c03003065002400700d40000009020b80d0082e07001010102d001d9041c6042001c05224200090b880040825110444042c01c61424400200903000c2100c00354054800c580f41c003044c50005010b44020304c03011301e0100381c05141140640c1c500303071581c1c01110f165603 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 965591375 1250 965590125 965590141
    0xf09062a0b090f07090515040509120c1b0103180623010f0e0105060f180109030b09010c0212040b071506120303060e0703050f0a0906110a17070c0804141305 69
    0x80e410f0041803c02e4080c0c1d078004580111076008040c01920307201c00d01e60b410b04481040200070700028080c21650310071031a03180380c581c0c04032000d003000c06004405841511a80d56240c9202c50405260904043c5072556251030310307003011045c0803101e0308204000350206034069903581d51681180200b038600d001400010703102850440b888103444584031411050f03640c03170081c4001c50003901d040103103000050250740b001201214801800b440145054400256643c5a5000e000029205106280d44032005440d0058041000440c441c40000580e441e040c41e01d030000b4807600481d44000c110b5811940d81d44d0030050700c0d401150107818095880310846860345006030003800c042c82038902010b442c0e00060401c9010f84078051040d039940140040c9075031000c000c0b01c02031455980443d207440e40d402c000764244907084058510820340f80c507011012050350700d00401941c1c0040250041102c1160b041c4000303904402994111009100086203c0c01c0c030328001113070503040101588485280004005c410 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 965592625 1250 965591375 965591383
    0x606040f030b1807081b030a120c2310020d091208010e06040c0507020f01021e0d08090303060d02011d090c0307030c1112070309030203011104060f09062a0b09 70
    0x43d40f000c6007100000f03180c0d4402540c9940d29031145180c81e422010711555540120390807034070400300040a039000341203140c0d07840e040001d50a0051001a003241c0c41981001092507c0300c0640b0400001415032040c0402c205a031003480d85490744095801103110100700d112a000000c0c00b9901c0000d00201c02038902c0020700c200d81c00d00c6800912500480403c1711070a15102c0d07445444415628149005030b190203128008024a0340c25045110303012041d403030182c034001014003003081d410181c4010300001100820fa0000035204d044260010824003800c0c2c2d0300d16000c60006542801c0800e01410004800c0300b140c008040b0168002e845070301001403d40c0380800440c412101c82d14200300347c0418243c110b84143c1181690113041d132001c413503445114034071000342004e50311a140a800720b94070f03175000c2402e444840c190020b41d68001309044c440c00d0b41145000030406400e20780045080c0c6000d400910451080015a0558a2600b1007c00d8400c02c2c1c40b09280c0b0b03c1d0062818417840c10103060455031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 965593875 1250 965592625 965592631
    0x1303122d0207140f1c08040209040302100515010e06040506040509041e2612190e03040b0403030e19120f080703090302010807020106031106211003110a0e0a050606040f030b 76
    0x542e00809141417104155030740c1c800001515580e401c16955182d1703003405402c04001e00161305520034080158006980c502485216054005c50b04850300c105200141030000f0071070401e441000140700034405915107030292822108110b903001c1c0349844d81c1c1091050400244000103030300c000510208144020142c1c4485d00c9080c070760310112a0079090071686143d00650210041520030b58011803105078003600500c040d81c0907400001002c20490b202c2d1850341e4001e520031414418003040410a15802081540300103100343d50b8100d4800304c1503011050f481080c014a00300e1804081c0c60f00034410380340c07484071285078800311903940c50381141805001d106480c0b00881c0090300150001384a0f51042c041c0d90f040780d034001e1003c40101100300c10081540c205e00b4541c0211448040f56481c207049a110303a034014804500c0c103103002425400c04903022585140d82074000c145542040080d1010103820aa00c48522600020151a10b900103480707480365600c142142d12800e080030043c452070080b6240 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 965595125 1250 965593875 965593903
    0x50307030521060108131e0b09060702060103210c02040908091509010e120c0315010608070c0f0b0601030b120304060809061e0a141303122d020714 65
    0x40b059245140c2c422640008070b80050008403000c0100e20074010400010400301d125441400300d00300d000c103804076a0340c00c07504169071401d10481400031260341800792540021491001e0512507045480750a81032038010258809102e815400f042c134144640700004455034001e200780001c038101d0801c0c0241c0d0700007aa800307100784c5205011314a000c09000485102c0101a107541181c1e0410f0401c102202882a01550319406109102e071602c0c1e40c103024580443c00a04404000d55040c03501c0144202ca00405020910426800060200310100000203503a0390007040d52101390380b075900480161000c6001c5680240740c01981940d6040003101070010355450382d80346400d541e0340c40d43d02c40c0d4884098a010303a60440050003820225204c82c102036100110760008560350360343c81d4284421101c12034404a03000100840b10f820582d0013190100e400761a1481800b904086551291304d166822124a0410850340c0e0441603c007429011b40e01460340120041503c40d04004202e61a00c00f01000c0341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 965596375 1250 965595125 965595157
    0x30603021306061d030a02100804120509010503010e06030f070e1509270f073b070f02010e100209091e0718151808070b09040c03090503070305 63
    0x2103a0240d204800c03c0740c0311690390100c4000580100c000485030b164585405004103104100561522010301e409070300503035519451460700342070010204240c0b05800d002c0020801250095a900c00103680c15105007501d00501a150900000e241c80040c00200f0840c0c0500c02c8005281314082e5001482030026604d1034a01c03071010000c000380d81d441110300c0300c4c48000c0111a02c00a00002070801e4000c00b120b0115070580070780e440d0340e524040c2254030040741149100094a01803050000203440500e02d80c45940c91303032484000c1310a0390800200b04104200711000e100e41d01d28400d400c040c1825840509840d070224814260358041e40c014030982c0d01030440d000100d501400711440c0d04a02c820f400807806416110b0311812130365900e080c210034021900300f20020910150070f5602c8583c9003001d8456000588032140c00810030b690b203920000303454110120802030b400e00d4004882c220354044a0004002120700300540007003000c1c2401400c0c038400400c80c00c042603005401800c807104500584 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 965597625 1250 965596375 965596399
    0x16080a060509040f12051c021e04030f02010915051204050c0402040f051203040f060c0303110301080f151b0306030114013008091207050402160201030b0405070807050a0e1003060302 80
    0x15a02d5205501c41c03080146402c24801f00c07105a9903016100307106091381c0500c985c60000e405d0002c030740c03c650002d80311003807041c1c0d84004540c1c00859060041c1860414011540c1c280d03070001e003150282900441155491100290400006225503500d284006004644481c2c454a4034010b010b82802800c0c040d2000c07107140701d942100001135900300e0300d023013009400203030038a64100c0d01070482901c12001d05444601c1d03010090032001c040c501030444000200040c090b802c001e14507024070542c0549000a5480c2031100d01c11044000c0c600d060281c0c047c3c01c0da41c0d111440801e004002102216103614619000451750f1500100ea0650460204034900030343c40c0e682c4824468143d101ca0010050a410001c3c3c1c0d01c10f040c0180c000c8d03001c85000003035820f00c960760008502a03900c1450269100e0f815072908000315038041c40380040700c15065908000c6403915070409002800d01800d00414858041102000244a0060401d40e00030140941c440c044c1c039007102401400c00c90204901c211000d001c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 965598875 1250 965597625 965597627
    0x1005040c050d0b091023102c06040b210426190804020d1a18030c030412080714160618050f12120304050606010816080a060509040f12 59
    0x4c1c40c01600d09035904034003545480095580d8040030b004056403109602040c0259a45400d2000b0307448156464100340350038121000c25600d103100c3c01c441e0851210030f080002c0b03030f10b4010644003a9025034400075900d08d1000c40540700d400101482420700e41803c820042002503007681c0f482c0d0301e404060401041c90f11081d00049900a01900c000080428140d107008148100c8101c0e0700b040c000f9244420760101600c2d15003403c1003070218400743e1004642030040c0c501d681c6840d59070f4604500041c5082800195550f6124401ea21036680c4d2041902601170602020381c0032a2402035012200c08885542000456111581440e070016808030002c00012036078020320701c00e141d00e4484540420041c0c100002c001d903009500e000c2580042c401c05030100d4001c01003100c03a00b0701501880e000e4682c0303403515100c3d2030a40010720b014100291340d818455250034000c950310b2244154148126199aa800444002c22441d40450fa05c0701300082800240300210f0714001c0918010051000346943d0120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 965600125 1250 965598875 965598889
    0x3110912010614010c080d180609060c0f0e090105040203041b0305010b0423072001020d02250507030f051c1805010809030f0325090e0f10030b1005040c050d0b 70
    0x5c0613003420400c00c01071a54002d140e005010701c94806810004074020794840104507204d42104545980c3d66142102c111600140c00da401542d06e464520100703000040812131020703061107854011a0040040f9041001e9140060045403080031010036840c2e90703081182c0030b844046c15043c000c52402c054812910070390303c49810030002c0711007030300103584070410100c1e02030040d00302215610f82c0050041c14848028002800450342c810030150711600000d20b50700c800b807034000d0394190400242c1000c100003040400d960f0101d9400107401207803190b1505000d400c1100520500159154440c5481c5200d50007458001c0c003400621001402d082d205c800546a605042d50320700781c40c1e8003c2c440460308808010040d40c0c0044401941d940f401d042c000e011082c503502e03106210200d9800d2800744500c182d4440c120394840c929500e021001e00307048c2c000c44402c18150201610010b50391000981c603141d440d4101e001080c01804c01c10001510940041458000740e50840703605007009600b0380907281c950 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 965601375 1250 965600125 965600147
    0xb01050403020618040b09100608102603210712050f0c0a05040305010c0503180105060d1403160303050603010c0c110904050a080c0303180307120311091201061401 72
    0x103440e051500506018806a842c03084607040c0d4002e458450320310b690380781c812041e8023618090f1042c2d52410b09040001c4d054450003004030365130243c100304c10400c000b0003914205444440316030305414058550309203400d620400c11286c0c2454144c200e0004600700300501284941c204e07030303121008001c407244800b00755202a5204014003160070042003441028a0040010380144d007019450503689030360f8a070a4410200c1400c000c03c1000c8100001001619194500c2c4803515008218034503100780020760f00d0141074400362000c5040b00c0d0104105000700121540880b04c0240f8448a1015203402005081c088412a02a500705140804601e010b200d0441800b83e12000c54613030f0000d0b91090240f1140c00400c140c3e030920407071034050040741100000b82204c0c101c02000e9076032403030110700c8050818849540d07011a603000300804000b181100116007860260b516000c184075803061107000351805520200e681c4190f1101d0f00b29100c120551081d0102c401c0e19501c90003501c0740e04011340d1845120 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 965602625 1250 965601375 965601379
    0x3110d0234050703081804060e0a1d06040807020a090f0c09060c0302100f0204050d20011e081f2301030204030f260a050c150907140303041205030d0b0105040302 71
    0x11001c140f002444045c05060180c45100c0c406003c09803850001d03060fa000c603401584082d080d48103101c0340403c0c80c05000c420050b0100144c5000b0412002165603010050001d0621200440c41c4400c550b580d145030381c020303c0e0344141440b42c20503d010140c001e11015009402280d0701c4100003a00ea1300903107000003000c0c0c0640140030030320000c14800015101141615120a0342004041341da44d8511b60314070310303072401600d1102a403100410290f4514070042d082078103101c16000140101900b50f210021807a42c0c3c2d2901e2101503d804a10254803412110365000e034a03a02c031004a204110003400d400e000c02691140e0b50b96a8124005400b2445140800b8003e401409000340218080c03010122001500340e07020403134030b049030ba44201560007042e4a0342c0044e4000500a185d81400c1003040110081100140411304000d0314032130b6074000c02e10a05106880d244401701c0a99011b006660040404050f0440c0e81c0c4160305e4440d4699202000b410201b903d0180c1407074065202d14207990907280c5c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 965603875 1250 965602625 965602633
    0x221060a0f05010509060403060204080601140603150f01091a0c120a2015010b0d0b0f060319061502031b06060d02040f0f09080c0d050c06040303110d023405 69
    0x100b000448a65000b0a180b5400000c2040000006a090310040c402071180b0070207084554109038103209400612140e0f0341c80780c1802c2c01840021580303201001d0340503d08480d0f584c00e82c04000c0c0180c0d40c81038180d10484010341002405c1031000c0c0498002d0040030448816502034010640e10110940501400c0900180000511040a44503220f15034201003540c0100c840101312140c1c181542c103000d0704001a444000300c0d02044055860007008808132003192500500d8054102081c1d8034000109035203c01e135041200301c01c00b6481e075071140014113242c1029003e586d004401c0650780f41d002038044070f01c1c545c00d00f229548455010903181d0058000900c0400c8000642e001c00000c3e1000c1c400342058203030356030003111004a41e0310a81e0f910b24442d090880e00c40c512070360400e0500c1d103103581ca01d041c02010010402e2648020940650080d858140012059552140452a800b031042a010340620008104103030f111581c0c9030307120348a00700e8043c40341c2e080c0004208080c44c425032401003903030340 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 965605125 1250 965603875 965603879
    0xc2d03011e1401020d26251b03080702120d091406040b040201030b120601080a12141c0b0d060b010e100e0907090b0706020405040c111c020309040911150403150f0902040221060a0f 79
    0x1120307522b580c0e0001110701c11925070803045020741c0b0480c0e0100001c1d01c130040d0350380000c5007000310300802d012012801030090119407800343c6414000300e400920003410155618600d50300c0da0b03640060b4081c0e04287d4070442e00c0303568454444540e21380b013441d0255540b410802070303812041c0c4208a614440310440035201e08140c03c404c5880c401941511203403800981710442d1002648074145180c11031800f43d5004505180044009400044908000303401070004075864500c01c0d03008444140001d0054400c42600c0c1e84204041310340c1c050641000350119800103642046c458140c028200365003088800304101803287c0c0c415660b03086400c50a40050b0804415a113002e9403c8140f898500c4250060b249400d001c1c000080c00c9551140049072075002d8600508450305000f80d2465568008010662400e400c6855032038461034030884411040c1d0b1103070040c000c82e40329038100c0260306a02074000d546610018884036100c0009604100040181d040000c2503403500051040448084003400c8111138 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 965606375 1250 965605125 965605127
    0x6060a03020d061203081902040602070b0c100513052e050a06080f030c07080703170a02101409060f0c2d03011e1401020d26251b03 58
    0x2d000302d0300302c1d1a2669940e0000400150009203249902c0c4266070b035810394509070383e5240064980300c1d29984078610500c020f004d06a00003c100c4282c40440c41c503243c4504072078030710520f003403c91001400d20500340002c0c81801c03402540522080d0384a24103070b680590121758003010041e0100368a907c0c0e03400244280c01100d00316407081d03400110819020440d00d40342c000c210b05d08031840f450910340e40c3c00010703860301380c1740c06000c3c090251010102030000c251079030710361000c0007442c084910055107000622002250081125101070515400c05010805141e000c500e00304c4421150070040340104000a114014034000c030301e02c03030014400124201408200880000492001020300c0c240752021420b000c1403d542c0614000c1141044603002c00340b005c910700780d42070029800030014071082d110201c0f4981e004034004140880c42d103001640420101150020458041d6150f408001040c062102d0203d040030b1490b00140810303e82004002c07030107021180ca44c044403100145281e1600759000103 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 965607625 1250 965606375 965606377
    0x60c1615200c1e1206100e060d02041116050304210c030b060109031a011401020303070c0b0a062103140408100506011403070305060102060105090c03130c1208070c0e06060a0302 78
    0x325209082d841c882c00f01043c042500e0288081e12501c0561100040000c100c08030130500d0042c00000180d4405410b280d0045a04100c00d0400244519103a4012258800e10f1138266540c540401403102002e945900303100f0703103c0c0d0040c02190b840311010304c20007100e8a180700301350601c81c3c1c0c002c0c60340d00710600c0c40e10382140843e0040c09282c1001f81e15000000031414550fa21001c1d0341c01c2290400c0039500d0180c91140701040203086905641003401004002500f204014101507000b214184c0c0701d40d200d007004401050950131044526451407500e8179910220503400076214425152068403d0003660220082d004511800070942c0c0485018a240780355504260340050381030402250618030341507504080c9d00115a05400a651801007010070360b4104582d034014070003030b01e040d01ca90800c42e0400d26a44030050441001a0b50b040c241c00800c0f00c0105503000520b18408000c140b908903242000e410303440080291412a14010041a40d4411080032401268010b08261a0060026050b006 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 965608875 1250 965607625 965607649
    0xa0f0204020913021c0c02030703080709050d030c060b0928090c3f23030406020c040e0f071a0408061608070c050c060c1615200c 57
    0x280c0c003800074254644a00001521546883d01c0140c0c80d0800140b850060304084902084103e04010b0600701c0c640c1c0120460f0741d013070f4151400900301e965515055a0b188200c0c0d01c070507040300c10001300d84107056000c0c0c1d904550f14071a1500b441100590000c00c58042019500040d001020049007200443c0000c0c007040011228000423803601e810b5100c102c6009000e41c4030440d0314105c0d82c007400d03000c0500c0c2c9030180303ca050900103010380b840c0c5941c000708007a10070000600c1c0f21003070040c601030743c0701c0c4034800103003035005408881d652511120000d48820340300c10114001c07403c2145100400f40d02003041c0088180060051040b18689814805d5880c1000e2000d484040f0820001c10b04c2802849800d1051001d03c00d09107a00601c000000d00e6480014140410400300d20009400100c02059001421b00101c40150301c4000408100c0d0402d00c0a03280c440300000d4211000400c40c2502c00755002c0510140c4415400840c1d06a0b1000c699007402c0802e40d00703401448408922340b03081d40c52200 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 965610125 1250 965608875 965608879
    0x1c03090510230c07030509060703020f012c0303010509150a090c080f0c1602280306060305150103030813080702030f0606090a020f030402100c051c0f0806030a0f02 72
    0x8032004407404860444084000c1d1409034000500820028050a584150400069550300d480c00c0f0490f20001e015008105c0c850744103501c00a00c203002c3c9442080b40c146101300e005d008000c02c11840c0d401035808070b606c9100380d81070f400d8a41c7c010110380e0040240d9040700d4cc06403c5008a641750300050b03002c00720154809610020014011030303800d00718480c0380241003c90b1110945400c20400c00c07910084003c008070594401084400340d041c0c20010030790507566042d00e0071241840860f0b0543d0200040300902c00700503004943c004103001d0749801c080700b02c0c0d001d05c042d9410380b21000300640c4908403d0001401181c40d03200450035140303100c8942c01a0500518030581404441d900003810015004100c0b103580d48a1414814240790000c4070380d40000e000342085241040320700d50440b00e408002c0010b8403c1140300229031025005000400180740d0100c141c90030311507182007503003052600703240c6080006c4081c2d0124800c50700681c0700354061200200201002c888603070f149240b1941e5510101d07 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 965611375 1250 965610125 965610133
    0x190b070609051e060103110904051b030118050304140d0b0103030c0201091221020d0207060804020a1203021b040203060f06130b040902090f040c0c0201050d0905030d0b121c030905 79
    0x20302e0840c0ba030f40143c01c440070414050325442d455800c00c60030050780c0c9440248168004014480003c4000429103490403070528045010340070200001e0051405840404540000314040c0c030801401000401c1079400b0030000000c0440c2680902c645262800d80048c0a0b20042005001090081c400350000da4030514181c05060b443e803c0c0120a14010402102e00c11223840307042e074106124a0685103140b541c0d1008054610803c24029a6841c03203114881c00d00c5590b202203015520741000040240a07950214a5110090302d070003540c3d55079400001c1030012400c002c600c072501c0e090084a02614004000746000c50042c0208017580e07000405080c110341500100080c20f80d42c220143c4001c00301e45130016200c001800502002041c10303210a485507141c00d51001c0c7d200d8000042d9082c036502880c110742c440712080c500314018511048082c01c81e1102042031f9025101a400507140903a0540d0f0f01e2401625204001d82d40c0c1c0769464950303003560301d00b502c00e4059900c203070b112981e140c0c0030b04100c07 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 965612625 1250 965611375 965611393
    0x13080702060d05040b13120f050c0d05071b03050c01030506010c0f030815010c1205090a0b030a06062703031b32030f04030821070e190b07060905 64
    0xa0010b5026203940300030280c452003000300744100300300d400750f122040c80302842c111b1109a494403e24402c8040b80c0c014454094403818401c1c0c458420750300342001d45800c070749200488000250084e0821039044131402008000c1c40140350700c5510280803241d201000b01082084000194080d04c4024042c40c10041e1054001012809840c04801d1480c040c1d11008101d0400c04125060507030f01c105400d06024905003240b000520340d5400d4441c1c6c05042c90100d4903000c1d00000524408100d034408200b403d0044140711005519034040c0c0200c98141d154031920780320f03205103280066084000300b07120300d15480c000c20101b40204050796800089403c00420000503079920303e4951130010300400591005003ea040352020135440c0340d102c0110a00071f6003000164101903c0c80d1196010041800c00085419400d00782904454107034621041003070b030640d18040741c0080510341802d070700611460310b2040d1400c0d4000c0d1004024241c6645102c0d1914141c0325848003c09004c000f00b0481e214400c820324 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 965613875 1250 965612625 965612629
    0xb0d020d23010501030c09050f06070b0103050c0306160807030504020406080f010b130204050d031110020c0309011719020310030503070b07020c09060a05010f0207051002150112020913080702 84
    0x18660a02640d0441c0d01c000200150601da428505030001c50605150489000c6001d400c50604411140c00b00c030741d14080040e0700d001c21114061140020440080c4a0000c41000800b040c003c4440c84281c00f00c4485581e107501d009502c24600c00c9800110701d040d80800d06240c0302c1c1d040f642e031190003c0d1000c5a1b2a03a20018146854811456080d50b0f95440c5d40d0b100f91858100700c02c840c20840c0c1f420a50501c0e00704130005005d251180ae00a0038042c0681c03510b9500f00003401200c1780b81740580c00454540228805650b100d90103403100c50700245802c0580c0901d41d80c4103120a0040844481c41200803503542c1450f0001e50000d080d842c0d02480d56000000000c0080004101e031920624519005080c2000042d1811102c00e0026108a01c008200103e681352082000c04440c2e00b480c0006800400301d00c04e80c14801c5a801c4030307401c078a00080100803590005003c0c1c24250a018001c0321680e070740d445845245100d21002944440800b0110b0040382c11002c80700720b030743d0141141510f08042030380 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 965615125 1250 965613875 965613881
    0xc1e0417010f05160f140d0501051011071a0705120403210c0f021f2003130504020f0d05190c0c0308040201120b090c03090d020708070b0d020d 63
    0x401030311044404480300108900c20b00869242d03003070105041c00541003407000804042108403440c01086000c04680c10401e02c584480000c4800100340c040e96a015400d1542c00b6120134000c0310b00412542d00f07540040351145d080001e075000d850b40036000300c500300718110f810004508101480d021080c010400824420b0242c4002404030480756940c9903e10324118041d60b40481e2115141030140302d060045039000303020360588690100c20340b4500c001ea4400103031f4489a6460100a20444050f000122508808001da401d2000085078404285104131280e881c402c580081c901c1032001007042019060680150904401004180342451307281070b1820304581c011104c0c8081d1385d145100b00348a1440ca48034400319140680f40114034421a624082c1c00c091000d40028108a0350030081c040210f0340d54090221141c0c01071040203d401e0441c101000c90300140c61741a260701030f280302021441e000084203030844070440054140710b4902005410103401c8200c00883c100d40800564011824502c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 965616375 1250 965615125 965615129
    0x30c061609230f03031e09060403050f06010501120902030c0d0302070b131d13021306080d02010b0307090b150a120c12050a020406120e2b1d06030c1e04 67
    0x14a07040c4003038010004016010101c050040d000c4d030000c00c00d44075010180c0c0d0180400c00440c0600c1030365001f0b40804210b43d407150f40e00280050040c540c1c038240e48040400c56904070b40003660380d0001d1822034140802110044c920081d41548202c00000090811449140c2c02602a0068411860380c5103c0075031075074001c403540a1a000c0755401030003402d4044074038180c441c0443c0310b0300700350f45003c803007541c80c800310b1041c068415410f0180c0c01044480366000783d4050b005d110181c4484502091001e07028080d07021045120340140038010a2601491085283c44c020091a105105242d0f40783c28440f98410307800c0303104022220340c1c02404a119030090007a0513080d55030708030041c10102160400c40b00d010f0803a1142c00c0c0104000c200c0c0139480100e42000350325410f00065044002c1c0411407502001c1030013000141948880c1d039116210b1020141c802c07084d035880391038220095203030a201500500c9940c0307a1080c001c0c40850001c8102001800e254014103520071017040c580c50320044250015 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 965617625 1250 965616375 965616419
    0x190b130603050a03110304140f030a0c120b0a09120f020f010c0c021f0e060a030608160e0702070b070809030f06011e1719020109030602040803090a08030c061609 71
    0x78003083d00130154000e40080300c081025001c0c60a060038501182041c4008414861256109941034007250b58280010580c80b0303800000c0040c41c547e90004150355440c0080280d070304903000c0c130000345030940c540a0381400340d900c00d10b00242c1c1901004242c80415039040014114411b005106c0c02078102485500302c4c1240b90f480b48409420248104448041a20700602c04c507644046441206c0c0c1d0001c400485180381140e0742038540c100c0c400101c00500b01ca40c0f10005030722a41c0c00095441c100071060351f069400c000e01d140e510b991643c1c0181e07550407642c807070411895020040140443c2c1e001003c1c0580c86401015544bd10048029241c5054403e8000d800302c03d9686010110310340342c040b1404003d0141051880c40100642940d43c0c0391850805400302070f5941d402d070b007411684a04906006558001d00c1192541c1d103501040c0d542c1e8021210040c05220183c101161040d0004180c400550342c0c10024622590ba6001c42c861100310b044024042c08604000860111251008045030f4210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 965618875 1250 965617625 965617633
    0xf17070f0209181b06070b012303030f040605130b03040308150111210903100c0216120f06020904090609120504030b010902030601090f0b1c05190b13060305 69
    0xd90040003841e11000c1c062100c10102000e40840d000c2e0041100e120407580400e00900700c0d40500c0118090303115075003000b00804001c00000c250f2055250b4115582c0c0811a4440c0a40000d030381855039a200e021071a80e03003110248010801144140014a2401240c00310808030960b1000f140540744c000341d50803804119034a00700900320b018103145844c0c4030000d107031407003801c180303202c41c81c0e01c0e03203804200310b603802445880c1450180c01110841e1401c0d072001e01140d9260f01c03907203007042c000c03c0390800d0b1030014012a0160510043d041000710251100a46404411607a0780d840c0c20040d45882400c071060380c3c0901000003143d640f03102d400c1c0468012240800e2921072403615812010381c45079420244081070100b80086a820f0710104d0545000030300041e581c0d1168001620309a00c9a8021411200c02003c08140421500b004d02060780101d22040c503084031200d0014241e400071205807103115941000f482561100303800c001c0c41c110340a4031410071582082d5002c001d8031056001580d084e80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 965620125 1250 965618875 965618903
    0x908101e050906040318060909050901150b19090b180f1905130e060412030e1603030e040903021b06071406060a06051206220f0c030c0302040509040f1707 68
    0x86c004400c140b5408030a041c50b010141002406841148640141c1d01c2d107640d100300141310b8480951040c01400d5000c11400c00190303842e241c0001c00d80c040d4080e452012454107032503231176a0050740309200303072846c1c0a42182004241070510451f403001e414420b50141075a10800c62648418501204490150341051603035420107090040e0048500b60360400740d40b4080042d40d0f01d205c040343c0f280d08103a0100381c064034600d11850880140900400c24000c9024265100020011b00e5070244100c0f403090b103603d09909104000c10003124501c04018001d60800488403407039041030140559400d4000300340ca4288a156110a403004130040c0c03440c1c109030300034807d102c81481c01140c0f40303000345028a0807626040e48200b480d01d0141000e0181401030070020000c0811031505003071003018008108082002000c20500c0c000a0070882201e03d022a18007400110200e22078000c80d0b041e04d030080c00041041c0c8035613071800701c0408006130941e0f0b0011089070a240c0041140001d0480901600000203507507 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 965621375 1250 965620125 965620127
    0x261608010b030c010903020a03110d06240909020a05090a060803040305073008070201030902190533030a091209150503091b0f030d031505010908101e0509060403 71
    0x5043e0b000b114140b1003111000c00069644010b4641920f911050400c0d014100001003289003041d4400141520300b0710403507400100600640103074480100900401c0d0325030380c3c1101d0007258019800650800a482e200340043e0410340c1c0381c3d5420400820002802c44e607140c84907030030354000780c0084580e500b004204002c622103850040d1035400d100341e0010820b50701c4d51030110990181400061000c171010880b90190ba0283c0c3c01029000c4e005012034500c1d2403406100c128624903405614480c03000c0d11500d142400c141da548075042c90003010030808120400d2015031035034000804000c80951201801c100003040071440c00c8540701980c0760240143d0504600c21270740d410700c048200030842c2c18420420b000744001512600420450492620b0402c500d01050b10441101c00a903050b1003880350b50041594541d00545010710034030130b6070304542c6d11600112090300080c45011000ea0140010007075200c1207a008011851042c4440b65030719103660603603001c1e0350f400c462103155600001d040000b41 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 965622625 1250 965621375 965621383
    0x181a040e030d14070801030f0302032a011118040504060b1005130e070f0507050c0a0f060305160824030615040b04110f130906030506180106261608010b03 68
    0x343c00145207007a00c5140500005007041014030020b088143d50360a070350309050082c400c48802c6041948884080320202e8031003600d01d902d0500d11403ca61a00e041c902030500c0100035148407495400548444075105000c0101814004c1c000b5900140e5900410890f9660035a28001c100455103c02d40c6136911144d0341132042c0455030080d0b9240c0c004008108036141d016003991a80d0315542042030721180070f4209986400200e030106038104071003d2010602c0150f00801070100c503019075082c040c40c1d0314a038106030b0000440500c1c40200300706001181d001041d44400c10790015001d822203049a0301d51001910b4420295030420404070b44641001c510f080500074001440010b0701d007408441e041c8140030303c0c0d81c4680f1502044aa1002c14181080c1c1c084420032002020010014440c0e07a840341481d5440c0d00c015038510400c0780849104803810801070080a084801700315042c42d0501240e04801100c00a02030300d20200c1c0a0300b45011002e1040304900006010b18130000904810003105144ca0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 965623875 1250 965622625 965622641
    0x51608010501050706021c0501090e0d090e0f1801020a0903020f0f030a080901030905161d0405030405040911060d1406041505040b0f0603070e0f0a181a040e030d 71
    0x100042500103210710798010003200c0405500004c01a90b81c1110340300d0406400c2e5090038002014105400083d0300d40454100c07070b01d418503400c2600c042c0080d0990a9074401100d04c04c0c4180400c40000183c23602d82e654492a074011102e000c0c0c070721011407000c1104e0072030303210100c68008940c2100c020b00940c18820350381515801c2c1030f030350898003029a40009540300821a0000d012000c0002c3c02200791740300350426031106500004031034a5404210685400d50a94000d688841e903e4a4005001001c00e1401034080c41c2c0080c003842c075040c10901448083c1006038800d40c0e812032010855082ca0720382c08000d00c00c240c0406400285403001050b0640000c07009030043e0322490401290f0420500d5849005007114011180091449041804100201144c145080c0e00030004803c10407002c1d08000c0c5800c1c8844200c48003908210706404003d81020076000b900c000c03007101031035000403c800b54030280701c00c6404106140000c504200107400c1d0351044000210b11703000491007824105483c018111 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 965625125 1250 965623875 965623877
    0x309060f090f0f050c0d060603050609061003030c0c0e0a02090925031509020c0d0906030c2106030c1706060f2407051006180b090619080703060516 65
    0x10790390352510350b25602d004121000d80301c00d00001e100342c200003040082c20800b960280c400f280d0505a42007480003407515100c04e0342c1c9809401c0000d4411704000c41d00c070744200085204510034a0035920b0407121603a40640c115402c201112004c0742c80b5000b0080503210300402c030f0000d43c0e50319400b41400f81ca20f01c0500105a80039455103101c082025038507800f8241e42c03140c6030005180d050340100300800c4400b84c0c0051146440047c4118014501143c5101e0742d5229841d4402e101d95135180890407592800150710002d03043c1c94206002c3d50440070310310040d1504450121b185070322034480f01e90400850340404220415801c0001002005012283d4040011510a50b0140c500030200f66a0035809840000203030341d0400d01c1042c0c20307124064038502600103040b210048003c444a03001004180240030744200b5503078504606580b18040c0c80084403018250800d0b90300c41100740b003000b1082241800c202d04c05080e0110b40c0030410012a0000c5001d4140443d8600348801e040701e49500e03411041c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 965626375 1250 965625125 965625131
    0xf0106051b251d0f0a0c12020a110607080f180a021e010230160507094106040e16140d03080408160204090c06141206100c120309060f 59
    0x18007009013102c013a0b0000c51004003207044c100d041c1007210322000d06240503c0301403003c152445480d0b400b034440c0004610313240444045403582d074020f0702c0d01e03007041720141c41000705c21000401c6844421401200184072034100c83d0182110743c00640030356039910641150b084500500641d56904125120700b4100385a50880c014422101104200441c0034254460050001d103586034200700d88101440309130010140c9a200f52100040d8010301603186003c81058440321f01e00039204110501c3d10340da207024110b2a400910003508803141c20700d00800320382e03105558034030303003078001274180b00218030446100050f00c20349040c0401c2500451030036144074001d00c402014040003e801c49905074206c1d8000483d41c0d260304080b41c4080604000750002504241049484010040c9800c1118182c0c0d02980700c00f40200003429180c08207009008054003400b441401140c2681004130307032240f04020300c2c900f80898646984070070040d04440744c0c0d03c20000f60b07940400350500c41c841c86401d0b00fa10b807918040c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 965627625 1250 965626375 965626381
    0x70210150501020a140a08030c030f010b0f18150414040c0f090b030a0605060705030c0607030c020a02090603010e150a0c020c010c032106120b0f0106051b251d 70
    0x3036807440800d1000b00700000415642e960117404002690241d07501401700c55a80c64a450b10541e20b420603502c0c002c1342c400b050f00124010b02200141e51040c5400020b45041010f24903517402d0200d6a12030301600001407169440b18401094018005410050784880000c1707030b40c00511089580d0310140e013082240f4258603e10751b83c0c1c04000b11088a0100e001c032612034444800d101c000741200d41c405944128002202010040301001900c094030014007070703580b5607450b50001d806490044461500580010405400620345100c2064001c0d401800010701d4998010031075203090070103811004000030b42c0782085003428681c0296440f0802610250020002c0f07040040c281268903c401424410162a8404412540d403100e208110507102d0910a01d5900d80340c0703601c81d55003000181e58403102000041c000e10516210f2504070703506603541620b041c4040c030030100c0342c6500707005001c403e00840c190040e8446182d40b0040c02c0010041c0031412003403901a40e0004030300c16106002420a4030020 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 965628875 1250 965627625 965627627
    0x120a14060127020409020406090e061f3603050d050703090b0c01090b190b0f0d110a0e01030b1602010b090c0906040305010204180501051212130509070210150501 71
    0x2200340c2c140880d4031115440b104052070502a0146070440100b1034070200e400035440b42c1c40b4907144100e40c00d074022080a038039920207001030301c0c41081d000c840c0903401c0314a51b10298824440f0388200c5030820079691040503000f007c0000d04000c035041064004100c181030050080038009050303200341a0504a10742003450768090582c001d03c1c850001d101d00040b80f0700902000c203401902c0120390140310114640380c9110b0100d07003400c902c001c0c15001440c224140006013400810000917036001880c08001034529a144100c40701c0891140e5081006610005040d02c040004c07980650700c1502610380c141703421001011984940d603407040845e814031038404010b4481c40340094100c6107041c06141d0703031070022010560600c00c0c1d50004015610000e0006a0303000394814490111207151010b1100d40d030f0354030800c18101c20481c2440300b1a004030000283d102200344c0205400c45d0900c00460582d40e9880c0001c2e1504001c40d03042001d60445207000ca04e52119100310041c05c046061301c042c0342810440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 965630125 1250 965628875 965628899
    0xf06110d020c0114120a060609050103110f220b07060522030c020a23150906160c090518060601080106023708040303030605011b02060711120a140601 66
    0x3010358140440803040d00c101c841ca20b421188000346a481411142c00c01b285088000c201600c01c07400041d54014000c1842d601ca40208420f620a4102c0c4600702040e001c4120700551200318424401c28030a9001140300780382c000a100101105e04c3c006880303030503a05001c4141e802c0101450560101c407201e001c040000c801c0d8400780079402d894001819251403001c1400b060581e000304564250912140c1020355865841d0340e001402a60020070103c8004003442080c05481ca503654003d4041c00380d40d88100c191142d0301804d9001d9070280d000d1642c2c400c1d10000721101540c04046050150061000e40c8a042014540200c8286482181903240490081d10740b030f41c03030380c084240b210a41040a4861903042202c12407409500c4078904d8602c461601181da40e0151004402081c14210009501d40c01038404801d0861150500180c103100ea50070440d481d0306c0100f084035448148e482c580012340b1460f480d0205040548000e1210310074600341400040c415500500040e848200180f0850080074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 965631375 1250 965630125 965630143
    0x6030c1801230d140f061f08070605040e09010f090b06040b030c09010b0a181e080606130c020f0106140a290703170c37140d05010f06110d02 62
    0x1da0010344018184c00b1403402c054601d209408240304802c2031001040d50740a41c00c443e04040904074020700d94490702c3c541c81c1c0307509224010218070148401c020100e90018415070082d07003030000251000ca880b5411040310468071099540908510801c00941000d20400c075126400314001d2540d54280f60005566440500404010031000f08600c52518000c1032038805c4890b401c151440c9160b240e0348810004440e602c000384146001c10400a8070340d502041c3c490003001c0140000c01c403600f6550421025104544100741144108200c00b00045801c3c4a13040c09801c81817680407610640400300130709016540c0041d4210610800485100640305104484c0d511240c04020749030503070b034282960400030b0200b400506541c24410040310300c030b4080081c90842440804000f40d040000c01162043d40f08c105d0503001982a00c840f000081e0060042106006a000d0801d01d003100201c251030076104280d02816a899030040113003c210340100981c2e0b408043c80740103040321801c1d0b2310b0095480d5904 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 965632625 1250 965631375 965631383
    0x2090403030c050f0318010b060a08042315010810150302120f060403122a0c050127060513080f280815030c030703060506030c1801230d 60
    0x70b0600710114a000b0000d4079180902d020340355890b407808404600c858101146400f1031540b82102c1c81e04249400780940751078200d165039204003a0f07207658036500613028850f5160f529030340b0685003240c4200d04005100e800c490600c8822000e502d8150807a00d0084440d82002c491402d06c103003403001b240804000d104a036011281281045401c024640c01c1c90200005105103004800802c801e241d042911031a810003012000c11000712222100641000c1074100e4440f0040b8880e29034009611070f01e596050280140b000181c0a00180c0c44409911401c00081480020502194080c80b000307114045d802541d411001c682d00c038495440109510403036500da40c01c0c0784081508804034100c201e80004904004062402d80d0744074280103020041c00311041204040307004005081e5080100d01310100300300182c000d2100c2829507a900380030701001040780f030b054490424681c0950b944e11154142002e008000b01055506084415080c00c240e803580b641a1044000d01d107005482c0e143e0302116103030308 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 965633875 1250 965632625 965632631
    0x9060908031e0c120a09050306040209190e010507020a05060a2007050703020402030a06180c0807031a130606080f06030c0105030406090c09020c190c091d010c0302090901120209040303 81
    0x296402c1c01d800c1c010044140440e1081a0403907a0001c110340040030321704400d480303141000d5520410150b540c00b049400079005204000412880c2901019400965440c01d0f800300d010391110001da42180c1c411154000141e00a017000402d0010620076940c0040d40c0f40410720007520a184100c14400c1c4064140508141c00100b8070203109082c400d000c06140d0007841903540741031441d50940030300824001c210940400e419011106810392040c0008486151035031011a901c0c518180c00610b00002d91b1211850b030342101204a07560300a0b950003917041c0040002d42d039411b10070000c101e50070052850312000751403c180f190725500000c1580c5e198000b464919500da480e440c2c00c0001d86080200188401c00074403011880300d045802504400160a003140c4038106000340c0d109040c0c80c241400b5000044031a0b00744105035840c0c0102c6800c07051100341d60a07100008030a00c0c00c4030b034030000d0040040d90100e4501e41034075004204500525003107860702018100e035000110350000141c0020103240d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 965635125 1250 965633875 965633917
    0xa0b0306060c0706031e0227030a0803010b0a09080d0203030c1803010c02151e19021209030c1b01021c09080d1211040e16020a020603040609030906090803 68
    0xa1900100c0e80d60b4440c41054403040c694518024024003800d40c0400e24056000490200e000c2442c0300343e60102c0034540700355a501c0c040410000900d01288809905405111040004220088020350092540c40d140310794583c00d4600081031091603800000c00c6400c50118464032a0b40081920742100350540180d64072580b102c00c00a01c0d011070240f40d07400d0350130082c040384510b802080c011a45000822001d0040d51005441055003680e0580358030052007080100b045801c141e0105004518030100061401cbd404084880c90074030f00b03c45015180e400002d511000c910305100381d510040500c88019495007d0380000f170340f51002628800000c0603006800e100807440f0310701a00c0140484030983d1802e440a0b10001c2040b840d0121001602d414502500c1d00e0081c11000c0b01c084540e041c062000c40d48400c03450340380c0c08201c080c06e03100f1480b951401102607690400114051849410300246203040c0d4075000d803030300740d0b550f102d04140100850200f113451030100442d0b880307080040004070719074 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 965636375 1250 965635125 965635129
    0xe0604020d060608090f030a020a114009080337090c08120a050f0706050f090c01140a0c17030f0709091104141c0503030115080103020a0b0306 63
    0x4098207801d40701a40c2440e400150654200c511a40211040010341d2081c800d002181e030380d2840b4014405005134403200c080404503005c01300110440c00001c8c0f00550340210320a040b160314802458409507000f01d0000003e203000c1590b113100902600920901c00301ca1107448848690000030031747c45545004111102b0b9408034500101805950040d98500b000d01c510030f68001001f02d0841141c078924240004030301ca00f40003400d20303a102c1c0380ea400d051038140884002c540603009a10344119003c402d001c20000100745016461107240010050400c5140050f4800c3c0703041084444a0b05000c000200c00f50032440030802c0301c655800b28188242440d00c0e514048403040c1400052100c07085000c014844481404503850380201c5650b600c3d10208c030b444040c03107411159040044800d45504100070441903490b40c10300a2510310040180c0c1c00c1c01c4c90b06001100c440307050039048401c1d03000000144070b6421005c00310a02e4014a1400e07035010360440e80890740c01075070340c020120721010200019981ea = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 965637625 1250 965636375 965636377
    0x4060207051203100503070b031b0c030c03190305040c09050c07050105090106031101020312070f09030807060903030f0b03100e0a02120f07060c05100504030e060703180f0f0e060402 80
    0x340358032500312141c1e80c061468580c0c0039081580c03107001402541c2400969072600144810a03035581038140740c034544420011540d54140843e810865800910588004040900203801c002030942c0146075212005204440f0b46400b00116500341442c0c10140700110b840f054014042e512020000640c5844a1001044502500000401540c00c10341040a0340406402c05070440348240d00c0c810a0703030f00800c01a6206c0c080c40c80e00300184440b840010300024854251251051868100340080e10740300c0e203c070b5020b9848078038140c0b05552030b64040c1c000c041c0d00d031059003510035041004108948047c4002030316490407540e101865038460f21210b03c10b4100380719400e20700740c2c010a40080700c074903000c43c591160400c00a00c011401104030000e003e50291000c900e0080d448400380003004641132854006200240c001d0b0100300041c100e00c460f0b500d4078001000c00324081d4484460441502e440b4401c03081d80740d00a842c0761085003c00704251042103150b1030540d00b62155005481d82c40801050003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 965638875 1250 965637625 965637637
    0x3140a0e0708030d0905240f1308040b0c0c1903060e121b0f3d0509010e01060f050303250204050420010c02100f0507211d100305040602 60
    0x40e400f000804000415096002c416044d128074107888000c82c40058aaa500da611840c03804aa000000002e803180c00d00b0881c00e45c07001989061740810060394491035031030b4000390014060303401c00040a0706246002c0000b82d81d48031023110300d5004405a0010000c82044511000b40151f860704501d0700769110a004040103031070030384d154540b03a2171110030210000080d004404810301402542c1e0f000e82c1400b14a1042d1040c82010700705140001c64092807688150318201e0001d82c040d4401510010072a010310303409520202c1c00400c000e1188021142101e8050b0702800c0d20340340000040000e07032004011313500d1140e00e19981065000300f42c0340a822440461034000c0d442840c00c42000100080c800076119240d0b0302851414207129004010f5800400c5060080e500c0041c41455034000e42c40b84001f20801c103c6460018100059a6529840c48045071a4021031030080c07002d11142c0c0ea40400c4c50b110f11010007604018000c11640450701251883d0885010540c40d60700140038044550100e42d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 965640125 1250 965638875 965638889
    0x1502010204210b0901110f0c01140405060703180507090c050708130317090f040c0e0409050604021504064505120106030305030f0405192103140a0e07 66
    0x20310a207071440b01440414511012901e040e003d81c0414921801482203003c0f40e00f401051900d000d100b507c110105030407080381140250348401d44818815501d203101030003203109500408031400c1c880c0c0d01905482c140d90001c1030740c00d04070010f070002c580000f400078120780c441100001c1d115120002220148101d00c40503081020000d090b0425200c8003403840112400340d509000344040c0c0c401c0100d124880c2400703042d8042c03a91503690340a45801c2e80100d90b40241c2d410140c2d29248980c001c1815101c40380001e44468100c00c0400043d820300e48402031080401c1c10459151a00740314016100c044204006a2020040c4245100bd0640724400e5a0707418000c0814420100c0301d810b40d810764007002d00842e4003404058582e107044032014061003060f207900d40c03600d608644c2c60003d107101800d0000c02c25140303403041c1e00300c00b03088440c0418001e68660041c116a01310941c182c4642c0301140d1a01442c03000c040c80c1c4203503081c0700c080c95181a50800210100030900da8001c0804a00d8030400380c025903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 965641375 1250 965640125 965640149
    0x304060b0d08070b0c18220f06090b0f0a060c05070315150603290f060a0809240403080703200903100501060c03111507030509011a06041502010204 65
    0x1c010b000c41da10203003a18070710504555945035110502d040c00f90240c00c6031800003e0541d815041c00b403504140c3c0c543c041c0d9111014044070038035800c003281558480c861004501366511f1003400400c00600070804402401e8402545000d0031002040608031070f8420b0343c00700400c0005030420414240481401103400c0860815070400c1024040b0003030403440a90368200401b0400040e541d40070f030080c0000c150840000c04221203000c10111041035146c0301150303000010302c40c010401d07944d00c00a094240c1c2596107031400b40c81c040d00003514201d42c00c10070f04814031128451421140c41800d0f9554819414038049941e500c488005030094043e2003102100060b80c54030f1080c2d02d10328140981260712003202240c8103142ca078080359080356000e010304070002d1100254600424007d40c9400035108603201183c8201c00f0001c80f00c100700d481602d41c000002d86410911250090134003444064420700500038083c20164400100c007441244201812880c1704604025024001c1d8151801001e00503148 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 965642625 1250 965641375 965641399
    0x51804090c032d08091903050d0e01090902040303020115120b040809010e030d110d0320070507080f010203012c01050913060509060a2403150f0f0501080c010c080f0304060b 76
    0x184e50780d07000802c1d1075005904400c0c1c02028a02c10b44117007030460381c11001515101c5d40c18807044480c03822400c0c666040c02100c1b04001141c40951006100860096000213245110701e038590400320f02a80c000320b1a18001e1301400042495a501d00e0341155001c100159915181d000603192030400d40284e585c180a00d070300d80b0040c2508908160301c1190301100ba1464003031102c03415000c0315144070a2116000030408000c07021400c0000400c1001e000d001241c0d103183c0e0350600780b40b6041070510044441d940100c0108a0464186681b401c80f81c0501d80310070440c4007020085d00381490500c50310b0310410400e8003150140900e2448415400d03040181403040385000740e003055840c08181c070800040c5103095502600c607078003503000311250b100003a4480e0f501455074480c0ea24549041046500c0e40e5034070041a59504800c0c451401c100000c0c40c0082841e614080340d45040030140840c0c5418030100d240d45000103605201100c3e009090100300f5616500c5505080c0c0040604000b41c80c0c00810340040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 965643875 1250 965642625 965642633
    0x30903080d0e0708030c07030611071203060f150e04090c1208071101080702060c0d0f18020a090204060c020603100b070302100b041406061b010c051804090c032d 71
    0xa0307004480703454111180745940b040620b071740713105000f501c00c400d401c00b134014030001e07007142c001c50002640b455050b401d00380d603a00e420038034910b00e5112002017603581d6420007402402007001802420300c0044072701c1030000507102422414440040342e00c1103070350b101644204503040b481e510152104600d400c1e000017084c17520006590001d441038407050380748903940400b90303c00d02255206a1903035010300416200c07001c0003495a0043c8000781607003070700c52816003410505403144040f0010b540700980681c0005005006901080760448000c080c0100024041c440e00f09205484d821760540e4500e07076070354485280d041580400d8006003906d101c009003031414181d0005401c03500208408007003081c1c41c98003007003004071003450100911800c0c02c1b100003074540c6800e2000e8040100200b03117510010000808203030844c1d510450203404104003285503040d11200060418202c4020f60301040720150310740f14061060f1481c40014540041c000d0170308904007410354145840807a851546131800007600d0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 965645125 1250 965643875 965643881
    0xb0415090b04110903070506160206030f060907020714060c01200403151a0607051510080f03030f060f130f20280315031202060c0f04060507030903080d 67
    0x2851065042110308601401030b00c0072115000001001003020303d1511048c01001c0e00300e0300d200100f030080c0701090b0001d41c4a0b08020361188010348254461490a8001c03c41707900d0b005841c03001154401c100500c010300c01c074458040690012500540c480600c0c444403409043c0801045099822184c035491003c0301920103481500d00c00c1d0145100429001c180328100d503007210482c100360350034110351040703801c080e401800d015000e0402da8100d900f092101c440c911310191821820032859041c01c00001d00e0501800c2e40d81d2480c0400340d460341c20524404280c2917001f509242c40746e072a0180001c0c2561b00c01070541003200783c0c0802400710454000340c4600070a60115414011078100a000210222040445194561034064070380b440300143c1d0400c616600761902501410394a40703900002514440e00c600c0294860018580741c02d8808400a040000140401048410034020b50306602c403034034155030503190a40340072078540d902c6003000c440c00c05107a407003e45048400116080c981c00c3c550 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 965646375 1250 965645125 965645141
    0x120c19090c0c0b010513293c0109170307111206070c020f0d05011a1c0f030302040905010b2107050f07020307171c05070b0a0b041509 59
    0x110810240c0440074042d0303444085403100800c02c607003840040c883c0d442c0c8281c05202c80c10341d0800005004101d0612a00a900034036035407200d0781d640036900c0d0745030324018110b0060010703051224a031a0714a0b0040012100e04d41c401aa1801c081d803a100d807069200b8245003004202010b001c41080c050521071707a8490303000c590241c2d0fa00804009402041c1848810180d00c0560b0000500c0180e580140860784400980e00480c2e102900880322509540d86030340181402e4000d40001515070100d201500d800c1040f041003074011030000441e80c0903540b00c0f898640d0310682020014004805514040b80203208030740007104064a401c0003c51270001c4517016206140c1d40e007841d0003500360804020000400f04440d80000505e040140d03a40c50300924015003035141c03001d011150080d4035511114185111011000080c0c0c0c0011400b030b0303841c042024242b000e514a409c010b490810143c481c403002040040451001585505951f00b103900d456228152101d28500c4103691143c484424038040d000c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 965647482 1107 965646375 965646389
    0x14130204142d130b040f0b0f07022122090207060b0a0b1c09030c0f060c0e09060d0b09240406140f010302120c19 50
    0x2800c00c07801010030803544000540300c040c1001c40c2c214010080c6071200b1050003842040c0e003003002d1100403070341c01c04621007065841e4240725202c4840e4180c01020039922004100c000d808000c03040780a640a03500b40c0314120500740d680842908a100314100482e02089410b0044100b01040c0511100c007409009440d03903203640000032600050010349410341c0703a00740403e1500c0c0103400800500f1003043c0071401d11616a54025105e012034621401ea00da48a01640c2890300a0541240c8981d00c11404018000a40b03010006016004241008517082008003500c5142c030038100c81c46810003030503410a0381e000b03448a00d0b05050190892543d4042d0110742c030032003031039481e0728040a082c8244012440c1407910307205040f18001508026135404a0041c440b0b011a08504141160780445070042024a0502c0041c04c00160246442d0300c40400180782d0b0480c01d00101c1141101c0903 = true := by decide +kernel

theorem cover : BRFrame.Cov 965467625 965647482 := by
  have h0 := BRFrame.cov_init 965467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 965467625 ≤ n) (h2 : n < 965647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
