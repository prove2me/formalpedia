-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4842
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:54:42.378032+00:00
-- url     : https://prove2.me/submissions/d0bfd57a-9ab9-4999-8eb3-d2f84ca16329

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 870683453 ≤ n < 870863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 870684703 1250 870683453 870683491
    0x31201170a08040603061d130620070b0117030c071202010e030604201012090f0f0f0c06030204060e10111005060918060c07050703020d0503070c090b0109051c080c03030106021203 79
    0x140588203040102b07001c999442481104d80250300c0003011201e0040b9803090040d41009440e20a49224060348245903105018041117058041a4502202d002e0b03500c004c1c000c2c03000c0c801a101036081c03503245a4180a40003c2106022814800081504901c40703070400001a5004120f603103c5940e2812000900050b4a90324980c210303030015080c10f01404c41c252540010b5607911000d1024044102c486c4881d80205c034040083c000226805009542021b5041a0600c08020500100c1e00d0b1454815081943c8080042d40240c000c205400c02000c240c1da0341003000c20705000a004203030340981c020300da8240001c100910f000b1440303001e000384001420070350700c82041c083d64a4100310029940b5025141001005903100c0f000002031520401c050b41d2520264100324500d18102e51144821f9800c0c0030803032119a82c004181c0040e114102c407008c24114080d158028410301c00e4000800c0314a00050300d03100008004040c50403a42180c1c200e42d140041c801c4403042601042d1950858080304500c42 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 870685953 1250 870684703 870684713
    0x2120d1409420709212117070315090c0f120b130e0105060111070b0c1501030807150603030e0f010201020c100518031201170a08040603061d13 63
    0x59041c0c0242d03002c0d020207030191142d6910071400e06860303034004101c19800c00c018001140c0241109140309001c044001009034071000c107150b000c1071060104003181821040c2c8103010304c0a0700104420b95185c000c080c60041406001080d2481301e80c20b06072002c0d20b0000c1d4441c15401240a1900030b40d03986484240182400d64040410340c101214290b01d4503010300250315440c10007140c4149070040407940b03030b954410ba58210b900145c080c034100100001c14007000140003550308222952a0703115039035580140c201d9811308421030486080c07085900000414410795030003034404c060007042c2510850415000c03c00840d140d9100040c04a040008038180914103a41c98084c001d006000240c5052000410030781082d62600141800c0c3c8e0b80e407014069100040d002c440f1038058413070025403901e510034640511500c414481c0384020403000e00c03100c00b50f0b1824001046c6183d44100255103171500d0302c030041d001e00381d280103c0380008403034a000311a0005841d901409401128540f80710442503442e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 870687203 1250 870685953 870686023
    0x1b0307152c030a140d09030e040e031206091806010b0703090b030f19020708161506050310020a140c0a060b0105030c09010c0c170606040c0c030207060f02120d1409 72
    0x845013050303805000030a0341c01e07500c2c059030000c5031180d940d4000320080041008200c0d413000302142c045034014020110507044100703005070064012070f0307105140d17130368071441807010b00d00d45000e42490700401e8000079003074072501d01810407544a0344038030301d11640702c1031002c10901040700c0b08410f03046080f010030510202d410003102a40c040d05000f5141c1801a100c2d041030354001088045000710082a2000380f1800d81003402140c1d0071a4810b2005615000010359a40e0065800115543c0d00003908162240111100d080000e5525a101c0d15048280006901c907880c1c1c110039034603103060038403252056220302c04030381c0300e4440c00c2c08645c1820312000044444003c400800c40b41c0954516012a1003109031303e10b04070003050700009003442c0c40e009062006403140072182d201409502c00151002a80100d607460540f045e41c40c2042c05041206412858542d004c84c9081c41c2050005038540c05070b00e10b0300690010404807100b01c07140e0301c0e034080281e6680380c8210040380180c0d405a114001c0d02d00d03100c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 870688453 1250 870687203 870687227
    0xc0323040801020c3702040f02030106050c0106081209011209050f0f10060f030602031e1501030f0908030f09030d050c0912070f06030f0f0e0a0201020601060908031b0307152c030a 79
    0x1f00003410340e001c00b1448100d0b8402c1c1c201501003040403c0304c20b07412009004981c040e02e0042c0c007600c002d898a1020340b1090007580389130f42c1406000149912300541c158084c0c0d8405030410f04440c03000d0351441c501d580700c26058004c04120300501d00f20340980d66007030059408880d01a5000c41900d0300d9501ca540c020340000d030280c40002c400c0220614620b002c0c4940b9070040001c4400d00d105803155030700140c100c9411004010344603042460500100d003005098a82c0031090707081d240401e039601c0100d035003140b20f0071018807400d9140200b0f100344070f00001c01900d901201618140c40c1002d102c00c0081c2c0ea00e003588544806041840d0742441104c2c843e801c0b0b43c071156070036280801c0d00c0f00d0442a107001d641180302076441c41d501c860014020f540e4108440d6004010505002000c142001405601c80c8118405403c40140d00c00070580d040c207040044824950b013040c070701c05094030106a4240035141c0d0340416400c14507400303054500610303502c0c0b01d00c0039101188001d503c1c1510820303042e10402d491030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 870689703 1250 870688453 870688459
    0xb010c0203070b04080d020c030601060e01020a06050c070204061d061018182d0203070c0213060504050105030c011b0804050a1e0b0a0c0323040801020c3702 69
    0x8051140180c4041001501415061849980391030808801615011300441d0000c00c550281420b00c405840109059041d6411171611000d440d07032110051345001c030102e9004042c9854401000b150881000c040d190440c800ca0301030080b9540c40c035110320030382c0c5c00c0c520164042d0005004500d0b6468a145180408a045c0c1402e100702e200601c80100d4a10300e50f8000c1340041805d5449140e40b1010b80f00e040e0b004841d44c02480c003a90303a5002d048005010340a03012000603400008119214010080000521340c000c140c907402820808411000e00748603c21103003d13305001c00800c1d40d14001c24103141c460410382d52000480ca41e5401d04512031600e90702a5000750040201150030385400045c07401810210001c004101849203405142031035a6100d10204034007400f6480610f0303886416110050742614241c0c854400c001c4c040d00012a080d800c2d034030309000c00100080d030300e10103401400c0c4100040b0103950418814108210003035100c04038040342c2c81214106504d40340804104114464005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 870690953 1250 870689703 870689717
    0x806041505100201140604110304080703021228030b0d0b0a090f0302061b13030b06040b030712440c0a031d030706050904020a0c0501060e01360b01 65
    0x40c0049003002085512400c0182d4454034260f40b980c8014541e07540246c4182e404101061049103000c045020140c001002d070440003440005140c0708100c44601804045d94072561241c4001d8400e10307041d18068103204807203404c00f00380203460003842001d1103084d001c0d203214440075003a540c4022120f4020703c3d881900e6520498100030498001005008500c01d40041009060081c90203040c4618a0240c03109001e04100d024801544a030704001140e6001c0e08401c02500c0365400200944402c4940d50b4051044600000d240842100c01c1c558072030140020700c4107660350006036a90038000030360b002c4560401441126000450104240e28440440803060508959040c850b00305000d240c000d40c001078403807450841d1040101800e801d900000c8000742145482c042015110b4000d1811082c0308035800301d802c0001c28001c06032404850b0303000008204094640200c0c3c142e25030280207550380c40c0c5001c02c803444102c00e801e552610603920a000c0d140c0000c1340c200c2580180101141441c100004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 870692203 1250 870690953 870690959
    0x71503020f04030c030b0c180405090c0d061d0715110a140102090a08191e1401060e06010c1109130f030207030b10030b0f06010519020622020108060415 67
    0x50304010b0005180706207400d002d01491403c1c5a00032030b001034118082c0220410500c0f5130380c0c45040a0034101102500d01256a030b07110581e4078203042c0d4100006400c400340f0305841d4100704550340b007512941d54280c0c0b00c000d40301c1c814101d25503c54060141c1355008040d0007860a003d40900c00849090100c00e0490b004e049003a92149014140e0064118042c0e401140344100ba2400c5c2c1410000f8100f40e000401d0481408680207a891040c524042e24422805c2d42001c2c2c8036082c007500c0d03142c06822a080000d00e604440049000701010b00c54010b080032208082000c81d80300b5401c400d400e40d008001e0f030051201c01400c0108002e4098803817025003811803140c1c000155400d041c440d100b030094000c0d110013032442c100a0000100144812000c0384d101c00305000280c900031045802000c00740401d4620742e00d900c0140e400303124000c5040c002c2e000c00e001c7d080446500168980c46100d042e50b05141c2c03d00300e22090324001c200d00c04000e010500c00d03400100e560410351702120f082040b41d030082c078039103070703 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 870693453 1250 870692203 870692227
    0x11331503031602010306051516060e0f0609010e06040b0a110d1a09010b0c190501150f080c06040b1605150106031a0616120e040507090602011b0207150302 68
    0x22009030709001c40d00e080c0b28030009644e05032082c0d1000700001d80e80104940702504041e1518401c0d03040900480001242030000e000c0705a01240401038441c040b54026045103c0950380c800d000c4901e011507608000c4000c04032500031801030b02507a40a44409410784508011401400d0b030b00011034040401482001c024440ba40a216004400d18042107400096601844034152050308038140b13014081004000c0b040d400160074081549003a01010250300a00d8054090800302c0c03046410aa02e0650214500c10301001e00c10880e9554001c845c0c03540c10000600925004520400b0008002803100740405082c1141c440040c6211341c0c01e56002c1d9000d42e80790782c501d550a8000b0710001e591900b104550715221000c44d00006001c5600c2403d000c030f108440b402049080740c0081c160b513860742d10314441c903004140722048060020000d01c010310f00b415009181154512403034005609000d15075081241000c90031380b1002140c0e028017481403c00d580700c1c9071141e80002c00e000b0903030b0801001c6440c0c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 870694703 1250 870693453 870693457
    0x60d09050706050a110d0f050f090901090b031e0a02010804021c03091a09030705010516060c0804030e0f0306150a0e0f18060906011e05060a1133150303 67
    0x1103103890303454031602003410007011031217503440d0480c0b5980400070040245400048503500e0300c465103081c517550002103005604602034100c050b0380290248002245098180d0885003c1e8601500cc507840180d400c8141c0c103204080080842e201d81081111002552041c4043c9a0050001d031542d448a2800000744000c80240001030b030000d41840c00500c040645000034000768800c0003a07050401c1600c800182d1100d44900c105418004c00054110800307100d02d10700030822f80c009204128110590780068000c09088400303c001520b801d43e40311301894408100040c111014008252139030340c0c0c0c40420800d40c1602d2400b50f0044036903100160b03060103098103c0c882c0503850307411922410240c440f0b003880e0311b040c4001d1030b031a0411010002426400588641140e81c2011a4103c0d42000c0030443e103003c0b51030f080701e9080600012041800e50704100c80f140b00c03d4401045820f135200030f1251100d40030b0000c00080b562010080c0c05d002908034220042c2d04010502804070340700304c0d0580000d00d59 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 870695953 1250 870694703 870694709
    0x90f0b010905062d01200109020f0d1a060402090a060c0b0108010908030a050a06170307140d0906080c13030f0b0703050f06042f070203070b0f09060d090507 69
    0x1461a400050000d185940200c5410101c1501c03240c10a030114008021940c0e80451001e240d110314444034546a840349402003141d015041c001034010341c0001110303010309407030b54080e809406e41e40d400b0350060a1128407040d00941080501c140b6800c07001e00c1131440c25000c0d00d52940a9028890190240d0700c50440000501d1035450750914a90305182036405154140c2c854071a0782d01d401313510340102d040c8008032948070861180009640ea40c48810000070701294100c1154a1208202c5204580000004005160045514200f0008500d41c602c1c2d9804941381c3c0d94000460300c41c810403130107002d80703c241c3c0c215010b02c004900b84aa4101c101c84183c4556001742c41300c0210118030802d0046000525030000030500d001d200e14500b40341100c400b200050560360080340e543c941c2c0010b464514080901914451400c0b1a00c01d039001c40c00140740d000b14609038804d00600200203130b401c0c01c00048507180002e40640300e0134413200808121540d080b0711710700c0400c9a07e50b075900000400a1001c2805 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 870697203 1250 870695953 870695963
    0x30702010f180b1e0f2a0406121e180204050f1f06021b01110f0c03070b09090a0e03040b07051617060103151103010f080d0503101503090f 61
    0x42c051042c01c2008841c40c01908220003840d0320b44288030240e51141401e0b80c00b0340a2198001261107610000e06c0c10483e0101000d4500c8074000c02001c82c0014500a10413200b0540d141c1c800350504a410340c04840340100c1a404200100c0003001c080c51190704032105103013403400e80b1091407060740c011030103480e400c83c2c85c082d0024080c4100300f9a40f030195420301c0a800400041246203083c400c01954030008070170319403040b0b000d0303600b40289a8401c024210003c0840f8041d00d01a800310000701d640c0d5119000080c1c801c2c00341c0400428111180000e27901c1090b8010607200194840318030100090034405464085800100070200703941154000408006100e003000301459030785860b1144080c0c0e01900010084000342d90408484100040c6050640c2c0e0010803006d0103640c006141001801c440f0520185444040000148200741c44203032400c55440c901522102e080c9407004035a58801160f2484440300006801e000055030070b207032f819280445080000f40b0005546581e1150300310300300200c0d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 870698453 1250 870697203 870697241
    0x1506040207150f200414041e06050a060c0302070905060402090909100b090405060a0b01030e07180606020c06070807020102070306181709030a0206030604110a110d0c0c050402030702010f 82
    0x31040e41c0707512406404c2d114110711000d804500400c20302c51441244114024a40300c3c02d14071113a0343d1140e0000803030b180341e1503000ca98812039075880c502409070b500c100e0384103a4156500003401d40c0151180c048195041d0b010b450410b081c1040403004203c0580f005420582c01c1c0070920841e2220030382207018540080c010700d4448055031040d0150344841100301d018000030401d000010740002000c1e9006081080042604001003004900529000c0002420317031040e0680000c5000c200c0c805542da00404002c24007a40b52640008d0f6a100c51001005401070410081c003400300e030307183d0b010340074030b41c4144144c3d0f0020f9503c0e100d60741a1040c9009402c0300b050020440800c0128102d8041442d45000d82c0c4c0504011580e0002130301c40d025040d0180c095140000040d810703640f03943c00503200311400e000032911804a4000280802d84014402030a0300c40c0659541341540603805500181e503120ba20b0001207070900007400040d4001400003c00d564a440804e42402d0803409008228038040c10041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 870699703 1250 870698453 870698471
    0x7112d0724030b0d02060702181512030c07030b0405030c031801022e0b06070b04061e050103080904020f130b0c0c1503040204051003120f1d0102150604020715 70
    0x120354500624801d0505140504010154407554408940f4035011108561581c40703e0002c10400c0c00da0041d103007001c07103940080250b610541c0c0c684560080044d12100c03804c450b1340404650340d114060002d02c5a41c00b10002700b0018000c0307051a07601904c02c400360f030b09008034941074514540002c2e9171300b142d5520748444d1000035641009521025450584c940030440e041c528020745448040c149491841d031100000c04c101c1c4c8a0b541107849140c4d01ca0f00761912440e0a007400b8005100e4000281c40700d028000c0c101658100038080d803811303250040300b41c5140803110b408000013548102c6440d1048001407261110700c00d141914040100342c10401e0702d59480341e900c0510b050001e060380040c4201c1740c0d01c5070040c5086a003000d9990044c1d041c2e400181e60b45034214540500d4185510042148000d0800c40c5c0000740e20004d40296044a03841c0c4104c2c42c581d401854404661006071140160b0281030b204007065a541c544540040d4003810061070701d100c0d80c880101c8083c0100303080480c0780c0c4400f501 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 870700953 1250 870699703 870699749
    0x10b03060d060c1d0d110402030703111909240806011716030609061206200d0207170702100c0201032c120c031608250b07112d07 57
    0x160f071302c1c00400c8910410840855071607101d4001182c0c00c0c907004550100002d11907034002e40c004e034801445140d0003a1600c0f0b50040480140201d103010f000050b03c080e000050504802d0030000c061030b50300200ba101d400c442c0008655010004002c0c504100f001c18400886520024040c0d000d4010080444007850000c036001c0d09030750003903000a104901c0e01404100d01102d048121004030b500c0b00012600903081000070720507411004103d802c0207000520444034048590003440086d01c111010701c03500d12601d05048180c003450700702a400c01c00b01400207001c28411140c441206105040c0000d16820711a1240ca1a072140c6040d6021030500c40d00c0018901c10070004401d8040120002a01cad1050360783c921900ca0246c0c1a41d20301d00449240c92008000803141a82c440c5199410703040c54000c0440c1ea1100d28004241090f07510002c0f1130007241c800d034441e80c5068040d90700d090040541503120b2129083c090203101c058015000030032050b0000f04002c0c00450018012014003494040c0080c0107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 870702203 1250 870700953 870700997
    0x7021203090307031104090c08060103060b04090b07111e0109030206100302100f05040902070c051009060806060a020c031005060a06050406021b01120606021c0314010b03060d060c 79
    0x24040551051100101c290b40008040080da035114a03c01d034400000e00204010f0031901000620401d03900d9070200342c581300001c4190407280101000e2222040480600044900c20340018249102420000740024061080d00044441c654100ca581c01e2201d400007183c5a0718291441540e5122000d00050540c10005250000341403030150800c00d2841d4002030959406c84540c1e0240b00740e403042414101e000d501614024402a601950346403c64917101100281501856210354080c25003928010720039003884c3c09482c19510340d1511030b100c401c104041c0c0c1d000011541c086104aa44001803034400340200e101040f0404000305281c1410020426194020340144041102c148010022a5800174600050120045a41c0480c0c4d1036000100c442e54201240c0800e950308107040029410b50002d10512103101000b42d100e400d818049080341076400c4589560098400d20700180803410b0305400542e013141c4000d0418a03d0421960b50800b034074507a01003100824099000c184490300c0c100d00b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 870703453 1250 870702203 870702229
    0xc0604050c0a0f0e0718030b102c01051318110a05010c15020304060b030d020a03080c0702030705040b0103021c02070308280e2d0d0f0f0503150a06050702 68
    0x2410303c1c1d83c2800c010705100e140d030004101000300001890032a10b10700345442001c0c091900900740040500d01080401d0040e255407044402d02c8000000381410101c10400c118030b010943c00b1045010792030f00b0b00300001c1400c0300c6c640031810b03036440d002404500344400c1c03a4801c02e44142194004d01d20240c0c208100d07040320754030560620800d2001c1200040b0035110359000303100d0041c40180c03252a01c2c18a2001483d07802c0b071454040c411011049038807500050f0300100e1521070303682d402c015070b030307004665040c0d00800d0f400a406500c080428001441c1c540c200b420514010b14006040081d420a0102e042c54903031300440c1d507030340e0009541d800d040c0d2000206030f1100703018001141020f40900042c862102e08180101c0f6a42d80d0101e0350500002400b00d02c942407000d51070910214000c9021079001ca00e441504910b0303111b4524001284d0703004141952044400d0303111a00442003010007501c09a04c010107142194116400d00462561022044d001420f01c41d40c41c40d450311500c1c810700210b500d07100 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 870704703 1250 870703453 870703469
    0x100207090218190b0d02031906090207060609060b09040f020c0d0c0c14060708070f060f0f1a090115050904021b0c010309020603160c0b040b040209071707050f0c0604050c0a 76
    0x61028041c0c1261982141c2c17801494490041e9250f840855201c0960501408040325034104400041c0a103c140c0203010942d02981042102e5560707101e28104413034051240c06c411990030f02c901c19240c43c0c5980544820641100d001d480c0400c1090140e090940030740620000c21070303000c01e134401c0c050f0786804500505600401c07201d0b55411440095054010b0201c0101001e10001c1c21034200301001a1402240f0b034850f00520141c14034103d19400b0b880380e40741200c60f130f61400d40c4600241248000c481d4a03003c3c05412035442e40d080a010410200b440c900300e02c103000e070810991510f51030b0b81c4002d20403903d05190b8041e8034100402d06078101400c20300150304260600104001590700c0706e00302d81d000f040b0902004007000510b1400d44050b05665005400f44988004003c20300c144403103001e12480c4221200040781c0e0303500405440f8490090144017000d12544005090b481c0144001e02c0c8145c800344495040240c010708c0d03141b13800000c4800b101e850304511000b000c2c0d420300103900381c00b802002c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 870705953 1250 870704703 870704749
    0x50d030f022e020f21011d04120e030a151506230d09212309010e1c0c050a050a060203090f012001020901020d03020414100207090218 59
    0x41145403458070b035500c0042030b02941c0001c1e200b540c07181e000211030007a450184481e444080d1900d199003011700910508076000008a00c00c2d2413520304540281c4510381c4803101c00030540a0000855103969104801c680522072080c1c641c010650041070b45007800c0a810700801c28542046044400c3da40e146d0082061000e0303124880e8010b440c0401c035903858001440540e07129800e040801c0b01904010300040c04c42401c07a501c020707c01c003803e170394041000030300e80351000d0752112003124650154064000c030724010700c02d01006080e5071080411a4410500820840703244100000040000480c02401c6604c0d5407150010461420407504a00041404440e04401985001401b075201d20480302c01521a440e13041e8081e02a0303024045d40403410024440034203410159a14650023988004012405072207014a240601803180c000c540a44103c8000410203660500500c401401f0119483c0154024000c012800300075a20140580c8000c0c100f414000b603503040148071a0710710009240c0d46644e54 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 870707203 1250 870705953 870706003
    0x1e0807080c100b10270b12160c0f0303020f030f040b0c03090d051b010204230901180504022121040303020d0f0c050610030209060a050a060509030304050d030f02 71
    0x149011004c825000d50800c210607909401c40c0a42004010315507210f010501d100206285451b000500740e101541c060143e240e407242200040100c00c0341c486680040c074210480d10005501400703030746586210b814090705103078107400346c0c0030b1035001111000b0030480110108010b0280240c0e0858115402100c210b05d1410020f1020b901c4044008003002070100000f07040284248000d4601000035880008544680c0c45407907044540441135a0840001c6c041c00100c0403a00e01103031010304a03004004080020303800b0f1460200505001802660b100703415442c004405501140e07400c0c00303403580c4005803490400c0c10700c0c0c410023035503890f028451030401407000344002a00000c42024841c102d01b40001580c1d01b00c0401c82e4a50030914004000b4001d00b8188802c03144003402d05010740c1d1080381c1c440ea990741c400d014400341741d99a1140300c0c3d0208220904000c6103004c0d00091040202c0581580c3c074041d1a000850203140441100300c0004e0355800d4004403d0781d05000d1296414103452410041d064 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 870708453 1250 870707203 870707209
    0x301150305060c0a0e030703051501150c0b041b0810231f03060e0304060905030a0b0a1107020a0b12070f21020c0105090105040c05060a0503041e0807080c100b 70
    0x50010b005021000000440d0984e1030f024600c000c401c1d02c80101240c0d000ca44a02d000c1c3c1d141c5141c0041d004c00d40e1034000020519170980c0201101e40d21103940e419405c1c0314161a000c50181c3c011344162a01044681d42d403450790100ba803440d0252805c01e005000d05401d4800c0e6504031105805c1d240c04200b800503020648810b40800140c100510b0070b110b009032000001081d07a07d900e40c5d800141403034600108001c25400c00720150044a581ea15801c407810340c2c503c18152244900075006049242c01000a40b10103225400800d881d1a00342c1c4c0c043c100038140d80407401481080e00301641d01100441d45071f005088035801154404d9007458a58048080b0910140c0800f00f41a480e2070403082c2c2d43c85464014100d64140c1e160040d45400078429410300020582c001c00040d1000d54070f140800c8c00114050400c0000c50300d4080c05945c2e018a1503130340344c542c0201c07038800109d02040c480c211661040810500030150030a81d0044000704c0c2c1e40d5882c413000074507100000e010790401c14107013503d80b10340e65 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 870709703 1250 870708453 870708463
    0x3030915060a121211030c07091508031b071d010e1b030f060301020f0315011e170c0d06060207060806030703020a0504090203010b041107020a0927052a0301150305 72
    0x13980801d041c650310200d484203450707214514080008520011407028469180000c650303044407080740041008005481e2101c1c0205200e01854145030701c2044624402e101d0484039044040da000d0a4840c41c6855090110813031005602c0300c040850004014040302c0040000f0fa500903002c05101403268000c00c5404415000c01070140f00c0f80060b02001074416107080d0101c0d6900c1d488407001c1d40d5249080901c244100c8030f855503441c00682d2404101603248a9031041c0021000030b07403030303c2c481644400701c0865180401130441d03145c084244180a4181050302604000d881140c025000413420848001d105800c010039083c40b952090070200050f031190031200060b078100342c4001c512034a0341d002103405400982e0f5900e401238a4a1130180024240c0c1300545103c9100300e565000d5966030b0380e1048150760f10b801185103140020b44e1108905406501060f000034030404c19110b103100c124981c100c9036494131820500f48140c141805649150a04c5a5440d40362007068045806e404d54403616554 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 870710953 1250 870709703 870709739
    0x170c03070302130228030c0c110d020303090a080f2e020a030213180c110d1110050a06140105180108090c060d1d0a15020a1103030915060a 61
    0xf03200308035000c1081441da404980c02208030100190100340100e0b9219404000030101d0000a03241c03804840e00584190542c1c40303650340090b0250b40c107100650410400007050101264180320401146440347c0f03c0079100401040c00c000a4070f00c101030322070340600f44503403011119501c00d500c5020301d60703000c80fa190420800e940003000588844c250a4282c000b881518401c1002034a81003000806e80c110b54008001035507022801e202c4c480200034195031404410340f00d20000d4010b00040c1580900c16070300341c4000d80c10042260f42540d401a422011140c0995205d442c45440f00400d000e218a80b0030300301d0a2010030300e40280303800c80d55100014482c12a0291504215803031001c560b1000041046041e00c0c2c43c0180541c0d61011000d4414000703103941154101c080601c218003040428001c03415403001a0455140c030b8a00004c0180c0000a62100b1441010301c400d211010700c80400401c00f852042e00401b0050035491410624050070801c02012540704002c864406c0c0040e00c40c02e44d8107011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 870712203 1250 870710953 870710959
    0x609010506010c0c140a170f0115120803070315030b04030818061501031e020306040b03010c09090203040f060e030a020f0607020318060903190c060801050105071104110c010204170c03070302 84
    0x5c4104070b000001c1111046602c0076640c0590345260401d4a0004108100d0710b03007001008100715400d0341e64019a01c003152080c03075a00d080007800100030030b95400c02103920180929001070310080c00c4d071100c0020a110380003501c0045840c1c0403c010035400030340e49030304004182d155802084452402d650b5654000303040d4120f221507403401d60501d9000e42c202c1c251031aa00b01280d145c651040e244d4100940045400310310079070400700c1c0c400080c101803107022282e001b1030780d9502480e42818100406540040d004940c24080d40060a0201d0800d00c40c07401c0310b060050103166220340a040c02840c04070a004684a02e8201e413003400400d42e000000c464245840c0c0d1510500c11700b81000199640c0101e1852580500907510301c5511946049446400b00e0310440b10580c2d040d0700d0381030480d40c05000740540d901080c0d0811030707940030074070400c41300b40d041c1001880840c0c01a011000303800344c0d4208a00c1c85000d0380d0082800d00c03030303e5007204c089412000140000d0550300003160000fa0b0310b001c0f1380703c0680 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 870713453 1250 870712203 870712229
    0x1170a09020102150702010e07140105041e1520010608061302120d08240108181f0b01020c042c0721020f0405040c030204020901050c0f0609010506010c0c 68
    0x20842e4000d01001e100041d480c10481a203150410000c2d01070030b14420107843d41e00411a02080e60201c030440c1a0340c030034041c0e448904290900e55868039082800b11500c21900001c0000201c083d001800f0540c07051540d030364041c5010b0314003400b0402407a2011201c0f1f00b641400401c1c04240340015803103501c114650800040000d1a0022a6074081d45010b4a0b5940c0a64004401c00503003000702c450144d00000c00b01e110080049940100c0c8403403a030981030014404101054030301840c05180120340003e14142d03100e13144003c00030188903069494900a481e201c030b008407a19038040c4100ca2008505807020b0005084100206510880c56907041044030007010001c00741f07800400c03901018001c0c00b50741403a40b0303503407220f600008540d09200324414109100c40e40014182406028081d5500c4645950050709581c200400307500800e0f40c03d410000203000b4514114400c0004240141150014040c45c1c02c245401e58291400100918140085481d2404c00100d00c1c00c990301c201c90780820703202 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 870714703 1250 870713453 870713471
    0x907030b0f1c0c0909031e02100504030909020d05010611010e1504080910020c1e030a2307030c05030c100f0c0c120803100509070e0d15020c06100501170a 68
    0xb001e40b1500c108003900e98150942c0100d0340822aa02052806011351035614000307540200c0d402c1c00001451115006070020b030766030590b100141e0825500310b4828108010101e0b10758180c603040380c210040030341006403980010400541c1044081c450040104001e000700302c0500c105039580c07070161010b54040700280c000102402410030503141c56182c01010001c05040c0c0c86070013551204e48085080c0b04005042c082854080d03000c04900c404c60000e40504480340d0307103840b00ca14115496120380036000d407a0b41310801c03240082c4808405148181e001c2552242000203152821006828041c040c0c001e9480c10080a600705054554020b5140341403900c0d44c94500d8004100c0640b82d01c044100c1c214203a0300410060b02d83c4c00f42d40b00c5c0c150340c1e02d030820081e6642c0170420001004e64045001c01c104541c03a00356070620407002a0b40c240203032181040020b0381c01942c01241c1c480c584108450700500300b40414020b103503404000808007440e04440e020014032040516460103007006c210a80c0d900803103 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 870715953 1250 870714703 870714739
    0x10270c260f090f0322080a050312070306050a06050306010306081c021603080304140f060a0905060906010e01090f0b030607032406200f06071d030703151107050307060b0907030b0f 79
    0x20170103000e5001c155030040c1078a103800e82d6a50482966561714404100015424920a100d6001100d000030028081c407498458142c400c2e51002d0401410035448043c080764090341003040448407260b00d44401683c3c1014840203050003d40c01c01310005081528080011030001c1c000e80341c005412090b14600402e4011545192804201030003240c6d000700f008100e280c000c10303840250b5050088050fa1200e44d01c050080303413168024000e08040f07800ca01c0050150201541c031100b1700c02004280065883c0607400000d24000d01103613181d0000762030301810200d108600c1881c0c111000f40c1c0503102c030030030304129016018000c0809001304800c02c51240c181190820040303031101a0b0280306039122030400c154028a035903e00d920311030302c44941092141c1c884c01e00080b1182202d0700003002c8070380401c81c9a80da8000d4450118130381d048081c1440310101150040c0000c01b0214840c240010311000d110041c04410742e0020089010b041c500030944030240c450801a104596045030b5600f040305440d111 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 870717203 1250 870715953 870716017
    0x60306061603020c090c090d120210140105031501151202090d0b04021002120708090a170321040f170d020d020310270c260f090f03 58
    0x8031003080640035400602d50041000c1c550034800317070303031041c456034810300007000c18440d2580d8190884040544980411601d00d19451030700400d2045c0c40b030204280090030290b07010000c0c080005070711400100154a4100b001461005400c158843c0c80d40c50300c4040d9006411410f008c0c010f110040d4840c05501413194110f92000d48000c1c4411003245842c2401c10700d4103001c4138124020101e40c0c050114141c000200d074440d140d102d8801c20b140c48110b5891508036000440c105412044c0c0c103a01013030400b03402d00f004041b40b240900454844000c06020b201040c1444929500812a0000d000100700c1203045981e01c1500550035155082013030b000080309201308004032111a1000c20b000350702c0e4007250005d50040f40e038000040380c0207880e41080e950310f0111521138032401884035100c810020050f005000f80201a0074050307101d402c0340041c524052130304040000307410104000c1210038092a02003079000b211440051440d032100c090350594030b2051a18000071408005801441c0410050f4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 870718453 1250 870717203 870717217
    0x60c070c0914041703010803041406090a08101406060403030305070e040c030902180c031602030d09030302070b07020c0915040207050f0105041a0c03010312111501080d0809070506030606 82
    0x3100700440b11205580041554060720116441441442d5613841042424240c0b8140d0324000003a5240a00d0311651400301c01820524640041060004680c0b654813085550010940b41e805007190f500b0005514040b2512900c003c18019112010300615480c3c60b010784003135030350509002a841c2c569260646001429081d465030050401200c404500c0d4540c00c0752011901c2070303c0198842c10508050f010460f400c55203c62086400c0c400039002900020182e282030b4400e0064074501140c1c1e40411080e100312100947c04282c000900e4020001000c402e06c1e0b100459201802d03483c1210400604520070103010700c84c428000940e80f00040d50303998121148a54000e04540d15521070280f014040d1004460030b8031136105031851028900c12281d5818071a0030050300445c0ba6a01355517894044c07104e8407601500b0400d420551488101c01002041003410b480c4c004011258900302e49146810300c055048000c1041050a120103904005400b4060364002c44000d1303266603030400855400e0103204 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 870719703 1250 870718453 870718469
    0x306060d051f0f1202010e1212040312050a0206150a080601030c0603180c03030804060b090a0b04050603030a020a0f0f0f06051501051207120204170f0d08010602060c070c 75
    0x81404018408110142d5591400c04070090b0240c0d03886803c94002411486600c0100c4002040100158458401034403480001095401c20100500d892840e00c050340c0a20790300004005001c0c414030005114100c8055207514000f8500a2110402929030350050140c100f4089000409400c59946103a41800f42c040081210303900d603542d041c9910803040e10711824000c070340750680000140c2c001b100310900081d0861150007100d440c5940854207558003c10540b481542c401c200709080d1340340b134375550040c00c0b44138022500e00820001c000c1100c1018004520a5008200c6000c809802056004501e900701000d404814080d0070821121182c0f0b00008122074540c10100741000342d02d60001c0e0041e2039a006002c0440c66140054400d445940650191051031100041c2428415070402201200b0a5005030409036158415620b5a03040e92a0038600d805c51110318081003000c10030702c00400701910388280702c0d525012000e034640501520501c3c0e007150011b034084c1071010083d80200103081c08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 870720953 1250 870719703 870719711
    0x60d05180d1e0801031211070f150908061902030c091c05060108030a0504090c0e060a02071d130b040f02091e13150e070315060e0109021e0306060d 65
    0x7031000070b190000150110041c101ca0399200b288180c0b003401d085050320707404030104a250048003001d03504e5144400c801005d40c070500c040441d4515003400b1010060041d0185014450780d502d501504180c007941204050781e000c1001c0020481ca802403e44580c002c0e4032005130344e0740710202501d016229032195141c1040102421480b07003c022001000710034011000c0e100346989070704078652030b4800c2e0080240002c42c1403106010368403c070b0b80100b601030741d242019a2004c114801044a64101c3c171604405a003000000b002162036691003039610307a240c0340000b405032070070b00b281c1e4080081807600075140300c010000080c10031100c000c25400b940d400824a1038240340c50b01450090342c01581d04d00748074600c1d52010915549003a5601c0b000360741c1c0518103508a401ea200603e006103020000e0401610030400d0004c0403c040548680e41003504c642c02240759801c1c01510203050070103a101003d03540c81088031440721003144041c0b0216040355010300d580c0707844030341c00141c082c0507401c143c0d06018a4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 870722203 1250 870720953 870720973
    0x3040b07140303061327242708040902160c0b190f05210106030c02030f07060b0d02030d09060f09051f05040f060f030f050402060d0518 60
    0x14a202a2411612a05a04051030050350215840340010b8071515006154203080d18a0800142c000d000142030040c141054070300c407070b9072038403c22003c039105607074201031204464081d903a01180c110301c2c102658010b0100c505c00342d1000c00c4441c2190780c1b400590503108410000c0000540490700108890300b001d544400300d00b001e0800c011000c0c04c00301d035200a4001700103015104001942c0c40c1000b81c9070034580d1218002c0d070982d03255030140301d60810400700300008281c007107000c4071b2280130300e42c507003040754041d0f041007000b0382100c480508010556006008103403024440e003085450a651200001c0782c20190f0348040b441000c01d041f002903142c0a0889005595948501d1006c00c60b00d203036542c602151902c0d54140c0e020020b80c0146a000503030f5514580702010615100720400c1d08070b1a00910300356541c0074454103084150044030004920301d50008007690705002d20490030754070440401160610354005681480307103418514005444d8000940f070400c40d464210585801c940c00d54460984d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 870723453 1250 870722203 870722219
    0x907120303060f05370b0d1a031504060e01110403030c0b060f0f042007030215010f21110603070e09090f1203040c051c05010e1209010c0303020702030304 68
    0x100600400c5001d4000000c0028640b030709884030780f580345940549a66400c0208540c501452042140082281e50f2170000a4145078400091508406010340003d00e10411071002d4100c176a503041080c4a0761107000d02d014101c0000d0411a0060b03440800042d40d80585200140500320740c44c4910340004002c0343c000b060540003491040341c0d030b02c901c20048140c0d49540c00c01000550860700d0316004241c1283e0020701c2c0c10103038411001c4e10302081c121804480e541c00c4540c01d40d80070001c1140180c10a01c41481c00110102d140d078054000e107001010240d00f060030416420084000c005c0190703400c16500014002d0b4200c2050307015102500f05036403072400384c0004e89455484000c00780545481790000300041d4010845511100d1074001078130342c0d422000f400000980028005a8105811300000207203580c0d0092404005031154640c245414411300b0910308440f1212615445a001800e660040882c1b0070100c542d1031609007070850100203541001c034001d00519078003d401d03110005020601074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 870724703 1250 870723453 870723461
    0x1c031103030709090f1506030b0609040609090b0a093c0c0f122619030b041a010905131d010905011104060f0c0f1203140703060509010506030907120303 67
    0x10f0000c2e0014020f90040f417403824125540c0200182c1d0020f41d44005011851013500034070b030146030081645051000301030024003200c0c4582d001e10101da0b0b8591404d420441070381300265014082400420204109485120b002061040038085a405281e0b8a5981e1001c0b2032001c2030054014586510aa506180000700d519407030050344814480c000c0300040c2100110382c000000c80d4410303006010421010b2000081c40c00341114020074407002d200c4a98258900d5024001c15a034940c1e0218044040a007070008540c000c80c030307060008404000160b0280d0f040303403a00c412034074141d84144e402c5442581c503c0090588600e02014076115a0518001c408150030500c444c2e40100c000b0804170011031541c2c08188250320641000c034011100b0400c3c042e00032000c40d1003030350181400d80400b0301582c0e2120394035480040b0a4000c41d66455030b004958014442660340302605060420405090600140c0c0c24081445541d100d100300100080305442c041c00f400000301f494008400366001c09140150142c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 870725953 1250 870724703 870724709
    0x60c2411071115040b120702030403080f040e010b09030a030c080c0708010603020a0e09070b0705070509070201050a0501090605010207090506060c0a03020f150123120d26061c031103030709 83
    0xe000c2d8004010500d00280d00f107804640004c00100c3c5400c0c07880c1b00510b1080c80007403446003940000c0c480040848c4800004144984045c41c290355200e041109495031800183c1103011040c10500a024894400080e00c040e0103030035007041c080c011942e1402070414416203401003214000c002c0c00091001054100505580c8200c4110f03400a80b03071909490504c4c000c03102c0e254903611000c010841c8800160040c00369502400c15a015242c072040422000c0c8401d990110040c0c0d581c8040100e10120343c4121400343c0304550303007801034601d0640000d540f9946030080c50a210350321030200d100c0e82d41e02c10486410b00003090591b8194451400c2c01794983c40104844a018000e62080350354050303030340381d4140c1611407406044901000b10030500000c0b50820340c03d20b0700511941c10500b2100700402c168018060316035964954080b0700344d601916810300b413250b007090310449c0c014000d8540d0794640800141c0c2e01d0603145200718400382811101160b0212484010b4040041441551030b40004c0000c16 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 870727203 1250 870725953 870725959
    0x70f020f0a0906240503180c0a14010e031203070315030c1212020604050a0b180601080304050316030b070318060906020a110d020705010807020127020406060c24110711 74
    0x59007003d14a40050000e2180c1300d0b030000342e0030000a080791a1010300c50310641801000c4560312a1118041115015a03410800e00b00460710818200c96900c18800540340300300350040d045080900c42c07680d03040c0c00042c011000b8540c60316450401a00085000c40056030000d00e03035140e05948034138007440c03614000c0081d5407960010441c0b40c043d900002e0302c1809a0742c064000d20380c40c00662100c4403028000340551202d03244014898848100400401e4043e06255004d0360380d803850141003503e0010340100b081940300f02d03000b0800105540101c46036201e00d060030045060304841801918420b41084000c1c45145007400500038410140c1c081d050302c0e001603c844041c824420f080d6030355140b2074211540164404001840705512421029030000000d00021503803801c007202d40340b1104000f0f08a218420102d0190b8420340c902806180300401c0706040502c2c00c1e440c1a2100600c80340c0442c0204ac50501c0ba9510300800c41c0c107548540f10600174511543d444144a01e410780e00007000e881c0c40381c8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 870728453 1250 870727203 870727229
    0x619030c030501060f0e271e0709271a01060905011206051c05101802100e130902010e040c030f0b0906010f0818030c0601030c060201060b070f020f0a0906 68
    0x16035811148060700540c1c05901c004049036031088000c250b2002c402c0101040d001302d0a03941e8040b00010051a140100d0350300710239962042e0011030914000003036121034101d0f400c1c82d94070740005510018002c00a2507684142600010030706240b85c03055100082200188502000010020f500045103025a54244c1c2c5007140c029000300303190140c94a80c05030560040c1319002c1090203642030f0a10309085446002a60040442d070341300705044850140c4000380014081c0407500841c07600060309045a00c5a0911180c50f0800801041c0e41c1d50400b811030418503646c07252030065a009203249007282e01d004006110452510000030041c1c15440d1080400c542456494201882d1080c40f403440b030715043c0d58203036032140601001c0f00c02d10000350440d440d040310024078003070f0350300280024503144002500030300c074075451403074200c41000c400d074071034401c591410700107100402c0c400303044070b441c0350b00004e0741e200c4101c003800040d00540c40107904540c0300030003040002e80c021140d00010111500000345da2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 870729703 1250 870728453 870728459
    0x1c0c0b190507021c0c08161d071407170f0c0c1509010509060705151e0601050f0708091002010c0207060e090105331e070b0109050619030c03050106 65
    0x900e80e401100e100960200c62200c00d13054141c0003410352001140501204400c01e03039941c1042e824000780034040701d1102c480030f8061111400c0d110244000c2d01c1e0301980d02502d40303003000000300900f6624029052110002035000140600e005112141c4c0201c000101da88a11288c01442070780d20560081040d4002d20b800e0118510700b034101c042891403184800c0380f410301c01400448083d4803403080c00c0c4d440303602800020f012880800c41ca6201c0400c1110403030303c030309145600c94907200c03002c070150f000003294004109040e6444010f0301e95034400445841d03110030851400305a0782c090004015004000513403000071b196415000314840d6401a002d0b100003d4503840101d03120022120030507044000701004005a0400c2e680c2d1580c4200c5103042d005a441e04803030306413280c8646a6488006800100d4040d4403d80c1c0c4a500c2c1030440130246842c2c0c540389180c3e5440703044140501c6a1510301c1d070f030f400010b4802d0715050b81e52031601408962003201582caa240050021040b0300050343c0540c40c059000c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 870730953 1250 870729703 870729707
    0x17010b570a03080703050c070f050a26070602310608090106060c1202011e0509060a1404030807090b04030b01140103060501020a0605060402163e1c0c0b19 68
    0x24401d001e800d03940b5182c1e50390f907104058010340720140076804040070801007240070401d01040c594109100c0d03400707000d80d038040d802d00e041034250718080d55440c14103613901d0307800040c0800211070f0b400d0750000d070250304d4004103102d0074107000c19101619811800c214000c00d050740510b0014081e128107480303540d80c036125030104a080320401d001c1e80d00400d500400c100082140441c09480102d0b01d84008285809040001640b010081c484220011340301c00c01d01595234014403010342d00000c540c504000d00244800ca0300b80d0800060f002a0500c032280b004114041c0c42884824040c3c5486925550388543d00d26200802d00424402d69003207181c030b441c40c00c14961007406000d00703c0760164010503406c1d055484070402402c01822081d03105900b00003004030324000415440b0603a00401c0042e042001c04000e25400421403400c4c200700700180c95058660001030241512180c3c41602d10f0030f891080003100460704a1030b07a00107004015114070014480d0840d00003040b119074003030a40940c0308061502 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 870732203 1250 870730953 870730963
    0x50402031213030b0a0608030a1806050f040b03060d020915120f0d2607030e010b0108060a0b1312080901090b04060807032a0f17010b57 60
    0x1c45100c02c256450410224028100503604070342c0d4103800103081d598480351103185a2182c3c03604008520401042d400c0e10003100075030b070000e090030f00f0410b18100500e1840c2c0c08030711507402400d1583d20040046082c0e41c076400081e8442c154040c002e0245804c1c104618004820142c0c072040c850401d1034107009261501207210602e01010074000c002d654051541030702c042f000116001d01030442000c0012844000c00041030080540341c500003807441d140012182960f0040958074140705918080c01060389400008908948400c1c01c00d54884290340060115480a58403010110521a8000d01444114001003850318402d880716015569a940602d8050103030b40300e010045a140742c0041c4030540250450b20481c54084101c0101034489140405203005500117400043c1014a1402c410b41e08040c88071a841080c1142d44da2075031505500014504c15044180041441080e802c2613807440c5403004003050180d20070f244400c134403180841000c070f56415270402d090070101d1042070310b4800c007003070f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 870733453 1250 870732203 870732217
    0x415020115031113020f07030503131e02130b13151a2101030308133003060b04140f010905090c03160302030403020a0f1103030a17150d0f02040f020d0504020312 71
    0x3651410707c00c0945042e540c40e0801410100c001d440540400c000800c00e9641c542148a00455109003010078010300440100b41c80c4149602c40c940fa81031140e9954024003a0320f8142200e60104452100d040c144003040565401b0418100f0400341c00c0054442d0381c0c0280403001ca070024541c502648034103034501480e600307100203004242d1490120b000e4008031488243c500703026111400d101c9080d00180b908003500749d900c07148800c908800c445501360780b500811004004035010b141c24181007071105017004a10300c0c01184100d8140c4056407099001e002c40000815008003071f00f580e850040039106950340f040781d000a40442d507224403040c0034001d209176400340c0c0d0140d00800c6001025610b45201d200089019612504503140d4000b0340c0d903082005001c000065501d040113201c1d0454800d161403006040b001d0081e24070740c40c0c80d005843d8010410303581c50700705070052000c1580780042002410002301e504506400001e00421590803508442d0050b413007641200c1c1c20f200d402241e4a40d60003010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 870734703 1250 870733453 870733477
    0x402040f0506091504020702060f0d0b042304150908070b060301021312151811030f0a0b07090909111c02060306040207080c01050a150e070203041502011503111302 72
    0x3c404184000641340c0a85180316000c1d000526100164001800b030340c0004825a074050130000d41c90f2000c0b101c0c0e00440c48120300c10b45050288001c24001900032100045407015010900c100150a01100b0034540034404648542042100003c0c03e202c1082d9100007001d0300c031640041d001c105582014405c5482c82015060a00200d83c280440030500010b00c200550742d50300e680301307500c07000c452500c41c4038242da100081c1c07042c40c900c143c60720009a03034040c4820f44c401d81007070303200030503100c400310f0240c21490f44a9003000c0240d4a0820503a02c80a058001041d00c51600582108118444401807141e1004645542070150460b401c3c0004500c80b14000390055800e00100d6200d00307050300901241c0344541c0400e401c6c1003403c8030751800c40f901220b2a40311a074450f4101516480e52080003800760582c9000e00303940d460278a5029550384294440e81c600e0201003090805030034800e501c20480c0c8100c1030101c0213203d47d203042014809400c40390181c49200c840d007400c150840207100b1160705620325 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 870735953 1250 870734703 870734719
    0x190e01060216060923121e0c01020307080f1b2e050613020a090b030a140609101a0903030a2a1104050c090a06031b0f0e150c150402040f0506 62
    0x5ca110704034030300c0942d00720079040803c2c0d001030100200b040c828a03501c000d00c40e51011f0403001c40c071591843c000003002003d0564108019120114182e40b0843c0d080c2800c401c2c0d9a075660b50720300380c003d40307202c6204019901401110b090008022401001100307460041c440102000e01c580c000303108980c02940c80a501001607154480390108030307000303096003598900300144560350355080042158001c4130412074484e078030103c0620302c0d014411183d80100080e03890854914150b22500c0014500740100c1070500c1c00c00c0300b03011081641c1404c6071403801006d020b0342d85074120b02b40041c1c20701c01c0080c01c0c002141c03080441000c010a10314040280c2c25082039000e90701210f500107100080c18040d040d076000c0103041001c15500d44a40110038028103103030340d001540043d400b04900150440061300c1c1d0811007000301506032180e00405c4001d00f2901101c1200790041000b545c801e052280f261003071068001c5400892042012402c0644905c0c000d0750240700c07468a03407041000700e40c800c0f1a059401903070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 870737203 1250 870735953 870735989
    0xe19050108310c0504050a020702090c09030a02130b040c02191106040312090305010c090506042c070e090901050121151a011e0905190e010602160609 66
    0xa01e030389040c181e900290003461115041540e030b10340810000c905485061000f41d04028900707252240950001c0140390031400e00c0200da0000f204410701501c0030002d0740e80070405444a68040c04000099071340102500942e10700310300600080c000d6601c043e80b188e8900f800041410b40080341c06501114007e1444c0842e10040d41e070440181c0c0307030303400f115002001030001100091400040321100200360f00c40c5901d10346036203082403d5030702c2049070104018000b0000c01c903a441741400e99040d20750361540902403820b8070180b2002e0340a404d001d102c47d109228140800190011980402e01c1e200341c03111101952002c0c58142600d030b080c842c601020702112040702c8115190f50410700c103540f14003001fa0801c03008500d1395050314400101c4058045403075807032241642c1c0022034010206014040303000c0601a200000c0c08441081c813450740030b001c5243e08003045644003640880640700900d40c0400658581000a584051154600201201c0300501040140c02401c80b1021191036401c03c84074080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 870738453 1250 870737203 870737221
    0x15020a11060a140406020102121003170c100603140705030610090b0a1e05090916031502070c090c02010e1603020609040e0f06062103090402091206070e19050108 71
    0x800651088104210b089149501c3d1641d00c00400003040e9540c0051388a180e013002075110b45501038004145030400c1c0b081040003503c680300388010041d01803903507905c50942e040b0350740c2041051030360031010b41d1501c0c40c08401c0040342c0c0c0c1080f0b11014800200c4510030b894105041d40d48000b51008094012a1002081145001d4100301c0b0b0b94030014249031b6101d5550009100b0004080c20a10071603610308200344001e050004445a02220f10001480c0301e890f4030313411144a507102d000152040141e2005480c4245442d01214000c1e5030010a240c00580c3c0da075072410040c55206035450055007400b68110050310000303920f0103c0c04401c41005111840d40d0f081151645c000d90107543c000d0780741c13500314810703030800d00c01c800c0c1ea060b280c0064500c40c84d11408100a1005207181303c07807130103c2c0209050440e030000003036401190701078a00507550368400b8006420050781500401161040100304442250301418068045030306603103880d80c0e85103c80c00c110584d0030038080c02c0d000131800400956501 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 870739703 1250 870738453 870738457
    0x10c0c14011110020703030b0609130b040e030705061501030509070e090118110102060c0307170408070b090d3c090f27020301080c061c060f15020a1106 67
    0x2005041500305089240c41030360034480c0c1d04481209540e40801d100f42811f8041c040d8103800c00c070840e042e500d00b074030300b10020780ca031000024543c0341c0582d80c6100451039112a444034a0311000ca00071a82c513075440d80703442907540000300c2e00400300c0100c44049040035400f90184030b000e240c41d40050019030382040728044008200418490066480e4088030044010010722200920702339920780c006441c0d0880061724208010740003800c004801c1041000b0140c0c44500700024003910809010151110309110140d4000c001001e0040480031003406105803000030340c4c45040401e41c450107107442d110080000321209210304da02081400810308a840c11103142540901601c0c1d040407680542c842360b400d11301d01002c1d00203603d1306a540340e9080c000b18002881c2c512415203513905529540c10001501d072902012140b03113006000105011030301c0b01003542c500070503120001c02003100d15034400780308840210f180b180d03091051100c0e511031609440800c540d120380e030308040108030340040d002c1030100d10b03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 870740953 1250 870739703 870739739
    0x601050d08030726240a090b030709020a03270b0705090d12080a140402150703050c10050420031f090602180306180d03050c0409020705070e06010c0c 66
    0xf0b0030300d02c1014a09a8138102c0030660380c800c555075490301720b104031218642c112040a2803008142c0110302a40c440310300300705480003040041044003049011a1030b0400740c1c4c02c8040f100d4000f05070140c1c42903065200584002e00520508030702092404203022a020040029080d1005a400075420501640040001c2c1c82c020b0418441ca550a0711a413145118030341184000690141c01c0c010540540e005244030421240c10740300f66410705a0014080c004c0380003541d0f52001d00403d013a41814000d6050318107891a000942d601d0350b0326100c00d01d004100413101240c4100700700c0005106080015000c00034018094002c001c000300001b22203c0110300c601250354040d071500c44a00c0040c0c014000741841c200c12032440c43d000b040d8542054100390000341440001100010801a8041d00095214a40341a82000102a2641d444c10012445160041c030300050000504608101000840000700d54684001a1240d00c891004451103001d180c0c0c040d010b212602001e002c04807480309a81d600b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 870742203 1250 870740953 870740957
    0x70e06060408010e0114183c28080d0914070e1005120312040f0605011712090109212f01030207030f0f0c0c0b0a020f0601050d080307 59
    0x416a0301c203502c5007540c3d402800307011203035140d00e07031981131421220781c581e0021808442840b1407654203616941e0303a95040400042d2611504a8040b0602e441804088040d41e9408403032110541c440c0e00390790740042a2400c402d409121900300b01500328125407003046075000c01c001d450111a00081406042820029a80580ba45405912410080200708020a90319606611500e0310110840483c0701c50380c4610300a404041218000c0c11012045442070307400f41403008020b84450901135030140e460b00c00280818a054008542c14203040c8640b40d01144001c00c641403940c20b240f00d280c841c040c3d40b8815011580b6400c0030b0040f21100c804c0100300015002d481100d0818a40b81c100c0700d00c0915a182e41c0030007210040354243c07600007101d01d050380700a090a45c6000781d56540200164a403ca00d00c0800000c0c08000560a210350340600c030f641d4102441c401045d0b1a480f9902c00d035802110300102510921198400d00b8401088090403103000604403506107d5070345840302607520007030031001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 870743453 1250 870742203 870742207
    0x90201080a0518030301150e0301090305160f322a0111030a051909030804061b0b011502010b030606030601060c1b140108012112030204030f060c03060f030302070e0606 74
    0x101e03e20108041d500811084542d0604c40d12000000b408404841b02c80300d0003079040074070300d801098015085861041d12110500b80300856410030003507a45004400501074445d08182c2100712006003031f0075150114004481e5070f00c4521001c0503550b401c00003500c260700440300107452165601d1079485501000181402c5084030101c000f0f0604650144201c80046a0003003028000210301000b41c0c0040300b044c0c200160040e045071201b60f0b190040e4462030003000300c85102e100c8046141c02c0030f900d007690301c515607003425611030b4602d012054000390a980103600c2c0c038500b0038413860001071540c01040c014015201d01c0c0d0806d002210803190801040c1c8400c41148110000003a04500c800020f0429401e004251003503500010b104c0d950692040d01d0a107031000000c000c80c150400c200250310b030311003007507504542454025000790003654005040d05083c0e031001c2c000d200058001300200203407541c0400190740c840d455189281c00c0c500000e80140e20042c0c2c1070001018010040ea040440100428 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 870744703 1250 870743453 870743491
    0x612020705160e16050d15030602161b050112090203010605030d11010c050a0219210512090105010303080a020a03090f0f0303061406090913020a120b0703090201080a05 74
    0x910b40366400b1192056410240c000b000710790200c000c06a0007007650300c00500700c403811110080140c080c00c1c141e01d92207a500c03e80c030031415100f40100350045034000c03019500c1d150030785030540d400c403500c00d0305445041c10120310f415211203e42d2900d080d200141c54100300604940d0b051801000482c0089800d99a2410080b8fc669070400c05e40760307407026036910291081d004100140c251505511140f06011041c40040c1c0120303004034400c0e035000c08003048025044ca8500380740d0600f60171070340e05c1d0200c07001078169584195848401040d80c241c0f9211040c1d116141c4803022422290240701c047c0c00a1600b1000c100441b1040c0c00400d1405514540804c0302c0000391240141d07110450011601c400000c401ca40c01c158250264400624a80380846043c590740c0300810f0325032048108442c480e800a00001d0043d200c1000b00142c0c15401400584225440c0c0864407102c00050400b0341e080006040010322492003406556060356069443d042c150b00c3c0c40108801500019001107150340c000c0c0502 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 870745953 1250 870744703 870744713
    0x31d0306040b04030f0201050403141c060902040603151401050304050a020a1502162402011116031403041707050a060e1c020c15030910060b041401031506120207 71
    0x69809140a50b4641d041428146005010488142c1008080d64103190801c00072a030002258420f00080d00c4480d6500c2c04810382c55005412100c80781202e25250010101320415164050000d64220380c40400c4400d6080c0502006ea800c00c0c0304100e07200c0b41c40c3c2010700c0b49510407006035400c00d118100f16030702110682e00040ba01040741d0044406100380c1c5003014407ea80c1000b20655050260200c0c8600c58101603580c10002d000055600050001c0c494084420740300350300c44c02400c0c200d0149135455070703051428551105c121041c240c0c00941405481c8800103041000c40e8011a4812085c004640a5044045442d0000c4400f034407a4010b42c241239010454500800c000d081c03110029000c500801c140d40461814454034030741c02c5500010595240361a0824034a81d10301d26070a90640b290b4482e10441c0c900403010090000b9107080c1200020801c14250140040e108d0342822811210001c80045046421401c101d601c0c0c0a11460200801e5006940340c0e02c840004132009441d241440d218 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 870747203 1250 870745953 870745963
    0xd150320090412140d1a01030f09050c040b0d0c08030d060f0e06011214070801081227040b1c06060509190905030f0c0a053901022a0f060c0703031d03 66
    0x200030000100d81400411f0360303251180401701545010100400307141b0791241c950320b0b03c1c3c8680c100d0240d40c0d62a81705e12240e4607101c41c5802c0c154020400e54086443d0001d00c3d0300c0340c101d04000800d25080c8203003c03859640100521098ad8038072040d0202c255114401120a0b01100c1d00074120165202d010000050f110054a0301c11180c1d0b4131448146c1d40f40c007420901c1c0421500540880a50502007601d1500703101c3c81028840242961081000301c81c2d10010b00100446803501c0d81c0001080c01984840c640d403813056190303a02500301040380642c0e48003071103081c20003211014040c21404120090940c4258041500f0390b003c1e20032282095456044070040343c0c002c0001c0c80c201ea02c04e82441040003c100500c42030450002566642440c00780b9a00103a0713030320a0300f00c0c60340d540f0791003030126140d200f0014426422000034bc51003c801006500c408103510f503055850040340a0090b44036a41444821501c448440340010a0000e10710344040b200c050f040c3c0d5111105142e0700303403003840b02c1d641048 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 870748453 1250 870747203 870747221
    0x10312080415020a0804050c040608030a05091c03080702071d0123090a0b04060f26210316090f0b0c160602030306012709020d150320090412140d 64
    0x1145c0c00e15003080c0c1451441c10b00c400c0c02c1c01e8070850418030b09110003080401a19203d0002e801d0032501c0c0c22404000400d41c0c2d1030807107144100c0f0343d00c1d03042100381640034440c107005000540035504800d48580801c12001c503d081d2942c40301c9c00440041001401c0155420b000500c6484880c4080c820355002821001d4181c038032030000341c0c0341c0740c280071036145c00c1c0300d42c000506510300241502c13898a02c43e0200319106050303541e062000104c0d0305a41d1141400800400300e0420100c041c151406861402c02d40c1003031351950036000304000343e5420301c0d000f030a0420690350241c000080d8149440002202076002c80c2030a10300e8018101c682c0b50982040c3d0110001c2d04054000d1926032400b13600042c04035140404101c41030315000100c0283c000d0145a040586665010259031007411190398005404104030400358244401000000d105070841c21a4401d901d40e68661115170310342c0e08100c0b004009860180c4210402500400c005003e0030b20711188006500c07006082c8220308040c141100c407000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 870749703 1250 870748453 870748457
    0x803041e0b0703110309060604020f070b0c0301140609150a1106040c090506060a140d11120a1107020a151404090b04110403050a170d06030623010312080415020a 71
    0x1070610015540500030862044100007109045280c00304150390f444002a1119002d5540040e9112400c00c01e03104440c401901b25200c1c0600341442802800b503540309110f0034a80366105502000c0c00e00d803400807a4541d5100030691000522400038080803980101403447c103002d100200d05403010824420148968055131b00c84e81c005140981e2802070320300c024003651160404002c66820150841001d41c030782c00310b16400301c3d00d0710300b07501c903050043c40380a0481248a03400b00e90704140e00f040c0c1032907034400c2003452014024415486801e0311540243e4100941c010714440c0140401c0b65088503c441800062801061107508070900d4862648541c000c880b0390b036202c56202800d07080038040da8840d03000c10300d410f070f00d0a450f5440b40c1b52244021100102101c0c170144c1181040a0031005540c0d890308403410800c510303940d070314084005240425140c0103001c14044040c806480f52000541220740181c900b0400f490340382000c94107408000e2049482e0f00561105a0251582c0d20240041e00c0e00740d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 870750953 1250 870749703 870749723
    0xd0b0a0b030a03020a060b0103060e0106080907050a080c010e03010204050f04050615031611070e0a20040f030501060906030507030221060f0612061506090d02090703090219060504030803041e 84
    0x70300340f01707050302c000d82e07070648c14581001d8042100100003201c55045a10b51f14150030707203845a6504605108466201603840782c05002c0101d041e5102180c00300307214200b6214001004450400c5c5420307409184101c0c0d502911844078006c0704d0905400860f802200181080c0b4001e540500000c2c4a410584400e0a8000b441401030911a00004048801c2c9008401400340600d00110400401c40081121100342e40f24032244030300342c1051009600700c02038010741c40d450710f03281c90081034042e0151009441640c01e0200005d8048034500c600340c15250440023801c104c904580038051540426105010a10000c202c2035544100078407480d40242001d40b01070760141025020403803104003034000b60002e6005401440544050b0a0840d10080025201540c030303805540c0001e14208807482019400c40710450070041e03401d44c113901840e50a4400c0f0340c820404035403001084103640c05405100c0100300c0801050001c0ac1c0303140d0140d68442d1041a481044030246407107034601d00c074001d00840350440c0f4 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 870752203 1250 870750953 870750973
    0x30904091410140a0b0d0b07080a0c030e0c12030f040305060f1e06011b02090a14070f0c0201080c0f0a0e270c070f08030c07020a090504020d0b0a0b030a0302 69
    0x1080c8000c0c0004000c20100740950503d21181c05082d150103407040498035907030380356007500d0f49440f0402ea0341036400c03080d01e403500c0c07a0075800501a000304440c3e12144030f00d0700c5100e0046034064403464101c008203400400f07040d0031510500c00d002e510406440150301c02800041c0c241200751000b04051442200a01603a04041051a02601c0080c1001d412000f80f22076004c902410000d4840c0e0180b003d00c1e02c520b40300c00004503c0c1360b40c1c51624004e900701000d039041104001150304580340c02c0003a5800c003d00380d0785e816030032526000c0000700e1a000944c0c07051010013561050b10b420b034001c290185864a402000d0407110081e038451480701e000f245e4491080c6910341f409000150499948581940c034001d0b4a01c40282944c0e0010b01c0160101d5012400405100a880941c4c030000e0303108100710354a0900030048034130743e041100120320a0b03a581070017040007140750040c0380c003641c0d02030251035141c00300d50f68014241c04000c0c205040c503680d0341c10059860b03400300950b980f142d010760041d00d07130502 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 870753453 1250 870752203 870752243
    0x40b04060c152703030b030a050c21030f0a03061508060a0b03090304050409050c04090c0f0b0a09060c030c020405010b04030c05060a0804080a0504080111041d160309030203090409 79
    0xd6240c2c084410301e142c9201d41c0c0401401600c4007044000e504000d0600348100c1c5820b40c001d201c03a86c5d140c0e07058070404d00350000300140000c00c42e0540d8402c44440c01d90005403002640000280341541003950028009000c480f26040050400c0300d816090228840340c85890410584028800c02c5002846010074042a0f042292800c00074040d2600c080d0300d5490103c9c851540d070310440c41040c1c0100d650740200002e000081c4002d0a004200800502820350ad60410b50300e41d4816004801d019455a480041d041214004030707411a205a00c0f0301c114203190000c1602c010844e05403d909001000c0c0b40c100060b075852241a010713004a241250b01e481c1181842da070100c005400050188004200d103280e2590480d07042ea902552066000f691412100c00460f0207000d00d038040d01e0710750300f0000307180c0c0560f003840b010303100348c0e4150121401c28160200404415031400e070741c8509a07440c114415151540f29420400c01103001c2d00440c1c0c41d2442c480702040466a01c0c03002030f5210b9000c010340100e690 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 870754703 1250 870753453 870753473
    0x211415031c0c1e03170405280b1003031106040209070309030203091f030b010903080919030c0b03040204050c032401090816060311030f0109050402120d030c0908071d090102040b04060c 81
    0x15161794100c0c0080c50305135503d0366541c01b02440c56551541c1210b4480c1e03c2c200c040c440c000e03202e500030040e42441c00c0242e40c01d81541560b01040303001c522400200301080d10b00185007441030390000c2139940603882d80b038015401401e400758250214001049203403e15195040107082e10200c0d09035803055481425001421a034564203c14108903e0140400104014074190340100380d0407a44140052003081910883d501c41d540018200d00b05804e00054550400016500c928001c0c0c50031701c02e030360300c449481070144800c46100b24203114040c4102007105d000908241da611040c1491407609032a81411072410a520702c1c000c0c4441d03203429040c0607050707240c001c0c0c4410305c00900f0f90504605003098a450554014022601c410f690b480000d015580d542c02549403070984c86064840c0841c084d0002006013a942d8075000c0440c06011000580800028450080320104034048461590041d44c08107400c00c00380c01031405640034000480c90595080c01440280b40c1626032221100722482d1414100d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 870755953 1250 870754703 870754727
    0x12020705160803041d070903050703060b01021002070510111b1608070e01090b061201030602030f100f050d061d030409110a0801090b01211415031c0c1e03 68
    0x3600300380405c100d40c0c54580311600044445018400315a601c13040c08813560b5203a540054080c0c81010000000e001a90380880c00000c000ea00342d0325080c69078001c070070907031080c0320000300f150340104480c00e507400a642c0042c80c00e00700c0c8001e0710701e8418184032180041201414010040d0040c21204810f80520486031008000303140c060195240340c00580d41d0242414840c159003161144959000c59648400719241242d034840c40d0000c47d42c680c208000250000c81d4a22034440b00b44011845e272800d8910704400300d4081040c007a81da0390400e0184216401000000c40e1079985440f0130000c1d07140741c1e060b10038020340640015070f15140381c00d080300c00f0780e4110081c0084991041280b405021340c000b1066041d00d01c3c013440070821810060048822000c0e020004001010861290355403990350f03080f1420107003007282101d03016152502c15500111500c2c074065403590040448200e4510450075400810209040040744060151112414407074052003c0845914000d0a10109a0040348044c54 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 870757203 1250 870755953 870755969
    0x9030e22050a0e1e030d0615020d11060a20120603150915091006090b01031a030307030c0212030a0201090b0108060403021f110f0a08130312020a1202070516 69
    0x303841d081c18220754644c08418040d0010440f00074a40304101010000c9030744418000e00100900d642d2040c1c103011000c000c000c840b00501036500e000030464405c00a585960501002038001515005802402055200400c105841d040e10403061045e02500150401d90550310b08460140f0305001054200309101030360f41140d20950041c04201c480018443c050046a140e01e4081d07511060342c180e2614102c0d030050003000341001004641845070350032143d01600700703032014400c0b1412041c4103140f01000d50b40003601a031051205c1000b192090040c0480740f400038003408404600d101096055074010950f40340540c2d1203440080c200808492038034010001c00e800341c03c030b904040d50000d4445018580b00c1c54501070640c23103a0755040c403507813201d40001c1c407a00c2203d645c0e008208061310980c000506805c04a07481c200015241c1c0780010002c0056a4103540c4c41c807002c0d0000701c02000070340010403c80b04103c1141001407441166100070410540650000d1003e0783c0c1050105405201503041a80 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 870758453 1250 870757203 870757211
    0xf03050604030806211501120816060b190315090201050a030f02160f150209090415020409050109021306020304080a15140106050c0c03070b040909030e22050a 70
    0x105102050181e0840d500d89000045921600c0005a4200300c0c004003924442c600c1c1700b450348821000520a041064181d03030303040603a03030b1303038680542c11004031002501c446400c020050b280c008210003081801d10070000000d0b000e00d07200114021004022940000c0344101c0c6080c410300c12070341d60200040c0c0d003001c8148500395466000900324010b290444044c19140c00060101103181d0301034914103401d0240041601c030060400c40d5070205424000d03104248807130800b998108950084803070003603000d081c5904a4807940d0b1811500b2420f49410a4115800c1c000411a0b10050140c180200a04107015031504150b400c405141000c0750301603025580b04100c104807880020400d009107030f4010026501c01c00e8003030020303c0506000b200c0558001c1041001041d9a50090040d00d40b0302da0000485084861a07400d05d42c0e0340d540f5000d0210700d03074410f100c200085c50311038000c088071620a15000030f0701030024000c01c0c007400e0501801c1454184400100410302d985e41b06641d4000d0640c0360900c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 870759703 1250 870758453 870758459
    0x120c0618030a0e010503061311070219060f0516060c0801180902210c090c0a0921061d100614040605060417030c0d0206040209010608090d1107230a0f 66
    0x1c0d2081890203c01c606118010001940c50342d2008031607006d0043c015014043c1c185014807175140c7d5440302c041244078a44501c121299484260030f0a403c0d222030f5100c880000c2d0703126401b039803190400d0034441c1d0365042280001000a54034011038450100b10740f41c0140d0365042260064003ca500a6001c0c1e80d03c0c034040c03a100140e9a0701009503c44200181c00203450f1260940250404a4404005070004025000c0c000c1074803110004102040a5544407001d40b03803642c01640600301c0b6240b0088400040c1c4030b090011407240c0d0301540e003182d00043c43c0390440c01c0c041c1c035181c10309001290905040740c2d600c50800c1250007040300035850780d6013220100522414000000c0c0d21b40618016001d00030201510311800610400c22200400a80801c031017415918a000950f00c06040710100c2c0207104e40700001588a0060120300d00454804000d0007007080200c2c1d045403e641e10210154041c4a8490000b030411960030702d12060140c0184600550460305041c4400051241d0106040644e0a4010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 870760953 1250 870759703 870759707
    0x6010614030708160c0f080a1103040e06043617120103060c0c0503031305010b04110d20120f010509060d0323030c030702010e06130f05120c0618030a 66
    0x603400b100c0403140280d50343d4941c8040b184001e05e9030004011100e10000c080a200001000e404158074540c0c03511600c201ca00b0b450350b10b0b030003103100e0240d401c2d03041c502003142c92030181c200d088001d955681c01409130001e1074041040842c01c0400d8040060006660014459502d0340c00b0050106c0c24001842c0c042c4914502040c6281444050065680c0c0c2442c0c9080c6441a4090850640c020040365124241412850740c0c810601e642147c41398a440341002540c1481d000e80001a400302040604107401003880c0d40141c01c4200b9444030850388802d541c210148042e0250070b02016441c2004c82500d0200800000500c041c0c00c480e118410280c01c0103070035031f41e0030702d5082100c0c0d01d0300d00042d2916003810312242a040c5900075162841c804401c0200c0c15001c0c0c030207507100d8441c1d50300922620a0104501e502e884080e6140380d00d5016244030070303012450683c02000c1c16442502190400580b101c0501c06642041c000002d042c0c104d002031000700100b8128045a0184804c051441d185c1c0303039440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 870762203 1250 870760953 870760967
    0x20092202010c050a0503040f08011b0e13060f090905010e07080322090c05181503010b1b1501080d140331060501150c1e02130608060106140307 63
    0x90411002c403500300c04000c1c0074400c09042941c0101103d441d0361729695005c03144401401600880d40c42c2c400c074199000c80005074200105020707160914000c1c1240306024540d42d60080c0034256644640c030000b028401f0880c04c6006000d013a6001903a050300e80f60441c25540c180907415880d6105803c18015110040100c032481d501c605d49080d41041d113511403006410055206080362850540f074586800e401c0802404015040e003d80741010744804100a80d412548030901034040c028801440014600d9004010031030302d007406880c482d42981107261a28259040901c4482c0403035004101c3d80c0003c02c90415001c0b42810300b106011804640d205641c00014650070312148002007003091403c13107103185500054292000c80720181a414180050a428840d041c0b0856003032140c408214414801d802d00e050f40f1004c9208181807401d40181114220002640c3c00b084100404541c070038a80300b0100100714071005440590700d400360240c80201d4400c400c0e2840c540400030083c5844d40152 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 870763453 1250 870762203 870762271
    0xc030d0f09050609101b0b0f040b0915010506180d060f1b08070f1e090e1012021207120606080c01051c0507110d030b0a0f03030c1205072009 62
    0x19107501e8844411b4006402009465005010b802c2100b050000c4c940440300360340d01c030306e01403100d02103162125003c0c2c0d5507480200c0002e031340443c2d102006000d1441d11100801c1c18840018041c1d0320541c9200c002451803a002d40100c0b002035032003280c1a6000b01c05d016019030a48079080702403071050202e8014000607030040451007000002034903200071038020050704c1511000d003160300c42008144e04005e00b6070740b41c9016480d218004040018801058111180c1c2074840d46509503070035034084d600b8019030301c004244040c41401560000b054803429605240d11181c0242c20100342c451900f140c0508004840103824104081045200c2311150101e0a103a9110180ca1000540c0d03611110100c5a0000b42c40f8590600e0203006400302c1e0403035150304030170121031048690301040f50392408001c005c108144401004601940320600118014403905c00300000309090252801e1115902d4008240440303800121000721004614520309120043d594000340c0c00b0211000312105c030310500840d0b914a1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 870764703 1250 870763453 870763457
    0x90606020a030210020715020d020a121e09050705100f030b180c0c011e090501050f070906080c0c1f18021e010e040501030b16032c0c030d0f0905060910 67
    0x1100400c1100700101d400500c1e01d07c66003151103840300681e4402035484425182d000500c1440d0504280c1c22520070b03965840f0078540c11140d450f400d04068070241083d60302c1540d050280300030004007511685000d02c1d890031150740384558480542e02c050700b10b8443c8070100e40620f0f1b940e81e040d05800d00c0c0c030f54016040304141c0085c2d92503040c1c2031462805410100ba0301d40c4110f0004000c6856041e19800400f186031041c0c00901c8103070340c3c120100500020031584400021026002000039034003640e415a00441070b004420302d0f120300b003002207184c94030f05040c2e04003813102c031403803442c001c00c2c1840b0754040d003216090204202e1565400045185d10012046c07041524461701ca0b01a43e80a46910780324500050010700070f669481c1049a488002146e091240076000240840081c1c407a04c100c0c001d000d08a5500c01102d0100a40251b4038600080545034500c1039090401d41641c0804c074865112085648001580090090007170105242303500c558050362050001c4680f0b41c0e290640710354031008034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 870765953 1250 870764703 870764707
    0x120f0610081501060905040b04150f14060f07030806010c12080f090309030a111c0b061206090a111507120905011103040909061506020706080f0108061302120f01020301090606020a03021002 83
    0x4007001070024004000346d0800d100180c5000104000da8240c240201c5100ea3390400c0b086040e44284041c0c0d01c105008164000d80030001580081c0c0560480e6811420606d0320744408906503464420700c805100351840491107003400c005442e0319214049602202c03c034080c50030710000e00d021a5542c512070100500d0603030074004a10b40361311b403007800403400291869081d000c90646d00700034a03440000d94805d07002d40d034021091000d030807002482e9401901400e0040c594404540c0f41d41c1c0100300b1f10307008542d114240240d001c298900c56006040f246029051750f80b031012400c00c0151000030654080350500c0721140c6048004007011083e10301b00c800280c801f0940004910305031004041e43c2040510302a203500b00400e02e03a80c0000d070142580e0158580d005161256450609101070920450109500090001d050f1810056052222500c098529a260822555100e00b40003078803110240c143c0d808801044250424004c4c0e000411250000d450a11480e07100291284000398800c8020307600 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 870767203 1250 870765953 870765971
    0xc02010f110309190302041104030f0f08070602070308060a0503070b04030311030708040e01090605011b0320010e0a150e28060c08040b0610020309120f061008150106090504 76
    0x50040750030011006284c0364150b00c10708040507850703841c1d02040c1d0145140c00840c03400c103014401290300b5a904500348190394640c1d075940301ca40600041c2c08071480442070009200003881800038211052081d01d401c0114036029040c0b000c8200c3d00d0703002905c80c2d0f111403020085011100c0440f0180c0c2c0d01840e014400d1107c240d50360707180d841940d0001780b03c60300018001030034000c1010581e050743c240d078506100d116a078000441e4207074200701814584481007100c00700000e0107265001c0d15036103e0319a1150040400d55a5401c545482c00c680038140c100e5114282048079099900d0b0f580c0e01d081a0801032074104243c40d84c0d5480c001d5030341d241d241460080041103601c004440c00c40c1e050340450184a0328100550003850301e0707001e444c1140c80c07609001c0800d10510307100030080c00821007540114184003120f001c0044250ba0301d65400400e001d200c601c1c81c01181e003402610300c11401341070460500780c0b5052a04d45000008000b04480c400d20ba001407001d168070004140444408076008540015 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 870768453 1250 870767203 870767237
    0x50d0f080a0b03070302091611011a0402091315090c03050f010e04020105190201060f080102190305070302070506010b090f030321060120060604060821070804150518010c02010f 78
    0x61350704040d600807403060400039021800f83d004661182d81d41c0d41e0f004141000c0c0d4030142611286208062940000c012500c09424954051f004540005102b03403040c400300e1452004a0319070303480c0b5550808040c0c0b018451a003060280680010722840c0c10803840c90700045241c100b180c10f0040041e00e5041401280640e0b00c20000c1d03403007002181c0b400c00030808408502a0003060710340b0501407881540c040000f2038100610030344006c5105851161080f001d01082100103000c0180200103240d030a111260100d041000710781c0c080c110815503683d466610808001040110f0342a25100741c0c1300708040b482141a0b40f202d44200c0e4003c07014185540c03100300043e1107240b202d400201d20304603283d051518121001820034001c00c0141c40c104074103904c84150726102e0b080320420f024005980d08031802060516001810401c1c01984803d06107911400791403042801462400002100031a0110003108911061a82c00109081050b205030141d4000303400e21907076440cad03981803003103032003d02840d00c0f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 870769703 1250 870768453 870768463
    0xa0e1c0c0210092c0609040b0711100911041103061809100f14070906020717010609020a080a0b0315160903061d0f032a1513050d0f080a0b03 62
    0x138503100b0781034204071380003005200000e5465442c95080078001246050411403010f500071a084044180599110601643c0f0341c0e1805d1185d03807080c81814504048032406c0d2042080c20740c801c1219240000c80031003000159000b01e085090416410000d021807a038400300c4280003402e6202d40c2d00500e6843c40c0c5036508080044090b00140c0703080c0180e00c68540c2d000d034080c90b04150b43c075659982503104c0340c00032102c2441307030700075400560f110750030601c04422201c2c5a01c0308231b117100b00049400750f10780226105a030440716043c40400d05240900a0441440c091040070103c140c000f0014010390180e03d03c40300c54042d02c1c10111503882400c03208814890818407020303542007401030100751507006825200b04410110381c45036005181205042c08000300403182d05d90f024507062104003c00003080d5800790000486401a4807640c1c0e4180c1103001040c900c14070502e10041c880d40c005642c2c0c01d0490600300100c5008003040440d032000b40b403441e00100340c20713040300d480c070400071307161410310003080ca01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 870770953 1250 870769703 870769709
    0x121809040809041815151e0f0303020c0907020a0b010e04031205010b09010239012601140d0f0b06130504080706140103050a170d050a0e1c0c021009 65
    0x5802c016204400320b84c4ca80803400424070032201440003a01040000d0129440e0410040b50049054000c00c01d0700c04202846004202080c075541581d50354030080907200b004e55000301c0142c3c100c1000403036139207000302042c0d6100903a40054507910300c0c00c1d034456800e49414010303202d00105420104007498803440ca92129658140c00401803542c41e5071002130582c00410590703005214440303101000e00c0707a68040034805c440e808010b1060800d01000c107481c80c071100401c50704000f0382102c03403c0344c4035031030010060810f56000d80d244c1a505100c0400b1100801c41070850043d04980d506000051540110303d002c681c01503a03440301621044001030b544081b0b0200d80c00319600740414007085c00a003000800c03915106103400c00c0700902c2202141c2009009200c060102d404c03485845020070744200c2c1000510308940201da103403030000b180110844209a0b60682c04903980d0050444460007040200c05462030006041c0001d072181c600240030303444159000380100c1030440f0080c034850207052103d001e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 870772203 1250 870770953 870770959
    0x601021c02370c0302040b0607080306060d180f0c0911090d05070801060803040e060d0c0e0405010204031205070210090f05010507020f0d08120601050a12020304140706030e121809040809 82
    0x1c4128500b0410f19481c90340c002a0f114130700d032030303c101d8a51034586c086608041d4002c034900c4c115519082002026001200d6403a4002c3d04d4102c8003000e5000344481502d00d038030505d901c4240c003480d820005659060354020a40d054a4002c95a400690b800151166000226101c02c82103c40f0318046017410010781c406411982803400200341c000c00840a40103903212481410f0ba0b690f6200300700310030044081c2d0040d020b5860b400d814809440c3c62640380d80d0041c040e00015192565aa451003260b507201503403040010347c042449404c600d041100c02440c200e15107890301405050458109540745d81d0b1042ca8144000012084d0441d103c0011b0b1b224030400042c010414843c142c00c1c031003c650710080020400d5a40500000c1480d0b0280701070700c0c01400381c2d0341d0310400f903003c1103c908001d5101030001c0c0c425428141204000885c2001860041d10301c42da4085401ca00010401e031400340710941d0403100d1103041c0044489103031741ca0f110000760441100c100c9016151804d250a031031190901c5160 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 870773453 1250 870772203 870772303
    0x109090b0d02100f120c0c02013b1905030606060c071a0c071a0304020918100c030e01061401050a120f0c090b09151804140601021c02 59
    0x3140b90007501132110900725498680302c000100c0b46020441d406014042c02040036442d050016521420800b105082d400685e0103413240004e20024001134585542c5500e0303140340d4410181e50401d240041e84181000c40c000088904110000b43c4401d0001c08040c02048040350f40421901e040200000030b10f01c500307900f0050011910740b40c981e6400040b0840c1d5503c14801c3c0050b0121080f1a5907004100c22201641151140da0805c110321102601c10300c503034114445d1442c48640240403a400c004103030b10300050f641c09103800240c15252107646405040c0d160802c20131110070043d42c4450010b809190441c0c3c0d071340c04401c0546201c807007480c4141d500361900281d1814500709030b000e02c1c0d02c518184c4418451903070381d80d91408035225074400a80c10181688030b00d404024254003500c412031110300000c1e2505040300200f412a40102d9003078007800550340074000346507014070000780314501440044015400c1100060b55441d0b0350024641c11801544020f0100140d180d0a45500305034215008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 870774703 1250 870773453 870773479
    0x9060403060608070503240406020f12011415070b040822261e030d09060203060411070818040603081606050603030c2a0a29090109090b0d02 62
    0x4001c048502031040780b8800d91401107204e00d00081c200e207080a4601ea000800302c84681f00c950703000300290003128442e8003807240c0d007081d100702c8015041d4a440b10040320300a601d050011480301a100b80050b004503030403000c80c56200300d4031046600341900303e83c0b042039907150351030010818070030441e19041400103092001a0101c00780016000c48038030380031810303003c42c0741c1e42e00380300b000204540c0d540e155210f003507141d14104200a506006441c1102581d042002204500c411707500d61110450b55154000104100c40c5403e22031034503000c22044086040210a540710085889500f940300507100292400300f101e5070b00c641001014550040d0340c2a1560803030210b814404040301400c842090411001401314100041528088040c94004205c04c803d00307190040b8101005030284030f60800072260410360b88494000c080145019240766030200491034042000c554920110440b41100f0800d200041ea80306200809a400d1038034001584d81c0d5007800606003191a040c002d4000e06100707441 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 870775953 1250 870774703 870774713
    0xd0c0e011221080718230114090f130209030a060c0f030c080c0f0f03160816080604050a09050a0501020903070609081b0d0501020d0b010e01210e0309060403 69
    0x140503540c800d040b2042e01d021240d10103036614120803003003000103029900045090b841030000b55031110100c541000360035100c1440c0101e00c070440c0c1c032013040e1030b241a000342d8035540c0c0081e04041c82c28034030340c0c0d860401024900103422661a140c40030310866202180c50090280c50341241d100000050460701105410300e080b00181550303106400218008140104015020b409411a442d0040e03071001e0b21035980c1c9280034500d07003146c40880c1d40848103005902851000900441c01000c1c1c4610441d04040c00c071400030021140141b0034402010185c048900c3d0b03076000581180c00a200301e9020405546084102e0300070543c0c0c43c0040e082e8429210418244401940240414401a41038070041a11440d00f0b4480c00300c548aa4005507021850180e0422981c0c1c242000d0000010f010642c020010340391242a81c100320204101c80d942c0b628401601d42c2c0181030688040400c0c2004503d0a1a0714001e00a10f044050700c1a02c1c0c6813160074000c01c0e04020300c21988880750013080f0700c0c0c5a07a224180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 870777203 1250 870775953 870775979
    0x30f10080105240409030e04020f0d05130c082e0908071a0601020a170a0e10050301080c0d120305091e060f0a0504021f020705040903030b0103050601050a0203090d0c0e01 75
    0x165803c42c10b0002207200381c070b0038103004412480d90162529040c40d078290090000a5100340412800132030306210794800c154460103014054440041074210350001420303c401303505410340c04144564000030818000383d60a6a04040413403400500000d0500d00b00c0e9244050151000001c0c01000c1c0003403804100140003454418a4180d0304546205907942d00040e69101413000c1c01130721035011144030100800d5084010100e040c16441c0c400759180705040814100500501e40c1000301d01d021005100c0b0070010802e108034004200c401344d0280800b40c0314440248a140c51400405480b0400111006010400207400f034441005c4100d0210340034444540720b48090314180e42041d0810041a5aa08140600c50040d074004200c8100003074191440500c044446c1740c0c4a044d401490b0002a2075910f40c8036030b9800314025200440d0360030a0f01c00040c02c988005000c641405400e124802400381d001058844100084c1c4800f250b00c5118100440888066402801480403180010420650f0080 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 870778453 1250 870777203 870777241
    0xb0a17090d1d13020c031201030f061b0905090a140a093815130504051519020901030902041d15150402030c09030a05010b0a09020f030f10080105 64
    0xb032001d19040601d42d00104403000303902055804600c50003a000607284503801080046001d004884c50200951590304050700240c0c01942c3e407800800c85541803003524064003000d80f405100791041d41d00e03004400b514080385405018014545070f800940b0340355003035000d49400c034600e284140043c500300d00450007074452101c044501c2c00c0001d8a0444140d00000320441e1020200c00c05d0501c20a40c00b40210080070003811290a420031b000401d420b6111459940e242c04a01d8101048a00d06810702d54603100b108035004542c60514401c00181403401c0c1006400f0103031007100580c1e0317090301b600103c014124224020b9809480c05888103440c441c1d9008100f4000c1720032095508000c0038000810501c0001c030307209024006095032100c064907065009540c0403000c00c041a00744029180402e14025100408450360ba546084103286032500442c45c00050006000642c07918410b03130000b0f41d9500020b040c02540000c0030000c117401c8132040700d148002d001d02c0c0c1d00806c900c1c90610005000e11009207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 870779703 1250 870778453 870778457
    0x70c0c030b101703030c131d06121b01110109020a081506010503090d080c1224061815120718050f060304260708070203190b010b0a17090d 61
    0x280005600f4065410018084051101460079a034400025200540c040050070040e1900102c001c250180d41c2081503080c002c2c8003010088510b85281030100c01b41c2c407102d41500340d5200010005010007060040414000d00b0310388200c01b11803150361540900458000290711480c0401c000c00c081400150038800074400e007034094034544070701c00103444034030040e5030601040d0040d0005071402c4d4059a09260016042480320b45000f00307104c05440212000d50303140c008026080c500d41c0c482d035440030720388aa4190455242c0e241407402140f07207841a00001845005058a0300d022084902d40e00030b44a072104608000181c2d8602031234020006a81c0030303d6404180840a4041854100503010313403000c4c10090f0005156807a507031207403031005018985c1d400340d80c600008031050345000c1c20050310516108088180d00c0311443d104040c104116546c00003490900201618080760015800314119050760910f15543c44056600b101d14030104401c9038a038441c444203014044000050b86c400740300c099 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 870780953 1250 870779703 870779731
    0x6090612110d0503030c0304031b150528050406090611030403080702030a0906030203130c060c03020c0d0506060112020c070e150405190213150203040501110c090f070c0c030b 77
    0x50010400b044441d03400c003404030b40c001d00c006514001420b004542245c000d003040d100c50784a0444580a206910030116449980c4156400c50341c034480c081d40390800c860012543c82130420381003040b040c1032004c0b280c07605243c4a0b008a014003805074005104150011070a1104c0c600b451141072003a80305803400ca00140c0300c0000685258404000d44000d84926a90300b4419881c01408401a41020b0010303044021201404ca00003148422100d00070b002030384421804842a041c0a800d0111200a8a02900440d4488400103001085699010800b402c0c4410300c404400382d050020700410003404030500c1030748008a0700c10b03034179900c087c4980450305260b11427001587c1804180c803420343c0c0041c2450540c80c43c101c6800d5407038000d40020441704038410070265558044031222300c0b05014910242c4c00008042c03002e540d02c00d6001407000c00710401403408100980104038552401040f20001c4154940800c0c01c061085510f010540c0c0c1080724030401a8a9040c0340c020743c10290386040000c455 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 870782203 1250 870780953 870780983
    0x1080f01020313030c1a0405070f0503120a030c210605100f120518100f0615021002030a1d0706030b01020c0904020f220c02070b0f0d0f06090612 64
    0x8140212440344600340807810107440c40e5035040c0c45600844200710f511640714039402d600c50010048003881035000e40000c001da985050351040050010380c00c0207010342c000700c00414800300007804031140c40c0004c0c0750000f0141940103049401c0d83d12940305113403011070217a038140c1840300d6811800a64030100c64080d005030120350107550080302c448181002c81c0e400c2030100d503022219070001c1d0344544071114208440204054480c102079210240300045907485c00820346100503442428003800318899601540e100b40400a595001e003a420a02c00710740000000300c107a0703010f8100da0b01c8800320001404544580d101d00039110605401001c0000c1e01d006080c014640c40021000803508000e41010415120ba0f000e000c43d00c4c00c6e070700b4000d4000c3e0041000c0d904a0910000d00c2c680031980050008950b01c4800c40241444420390054003422070078004141803001100448a48008461000481c0c2d40085105006003015500c9101032500d840320000e00250492401c040003071203100e0449030344c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 870783453 1250 870782203 870782233
    0x180d2a0608040b1918140f100506040b10020c041a060435070315051b03100803031906050d0f02012115030308090d0525080a03050108 59
    0x48600c9003000149005001c5008034031030400190300200303d0341200b401c6a1020080d002602c3c114450403c205010001d448180030300b0391b606400715440c1102030140482000140c559805400d60300801c01595100491450303a90350b0300c400e1a003800944105106c000001010f0340701d4018428a50289041003000c01e034001000030452070588004105078102814003d03080c01c041b509040d2201c4010040d910441c00e510105030300444d007000b000040203410300710318290720b00380c001d13039440d8a102e0300348818001d0344038080c41980d0702d81100580c00c40d01c9588101e00305010400b1030b4440c01d45400000284403442e02da4201d4504001c1c607461040c4280e41e551018080c418850032405010340b0002d4038000c00640c4203170a03100008208400000101d800c0002540460360396142401e85003400c4802001055002540c1540c05421200505018444403602501e20700c10201c0d40c44a00510b45940040010000121003203a5001458552a0302400b40050700603e020b01401409110362038202001d01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 870784703 1250 870783453 870783533
    0xa03081b0120220906030201171012210906030b0a0803030a020f0f040b0d0e010e06060108130b090724090501080c04090f14060a0b0906180d 62
    0x190142c0d400003030302100309540450a40202d40800040d0742d500c200c0800c16202e200d0002e001e08090380002a60500d148000b618000c40188040e4650044d402045110400841c4a404440050740046490f150a29150b91003048408640c0561084000180c3d54264002c80540030781e01991001c001c1d0307010100800640b1003c40c81050701e20351003040002c2c0724001036000b4003a40c050740102c250806040c500c03d02000c0d00250041030b105800814140e584594034003e1882c050800d81c000c00000451380b61417500c03964028095414001d0030301c04603054840b0070500d55140e60300011810098141408459240c034500e01c140313a091200c42c100090401ca22030940c4c0c600406581304d200d0483d242000548914030b00400c3c808100e8003c0c000001d440038240103003540b000ca9a440040c014800c4501d00700c122102405807030040d003c0c940d051081da400c45044600440d011280c29886610401c01d01050152000341e1a411143c4c2104890070403d180756020001700e0200c2d24010240b00b0f04c00d00303003500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 870785953 1250 870784703 870784721
    0x71403030405061b01110705060702060a06050904030f1e180b030c0301120303020f070605190c0509120a06090305030a050703021c2f130e0708061e0a03081b01 70
    0x281c403c10284164184c007002e903000d818100000842d08800c0c030a001c1003250014441600e09800c01002c01450030760501045900045d440820888030703007450046900c9203c0104020188000d0355841994640a00084410400c00800c04c4d0400740e00140c0050101114400302c85243c460000301260000c80343c2c00307407407190841d61412421a0318000001d800d0f40410703c019014103908212400003000101e005151160151074003243c2c0d400d00041403001440c0c050501d1100a242211076036409a1040c1120300c140300c2143c072030049400d0050b460741442c10101d0f00034042071030b00180b14100368002010710720803410f00c0000c029950380c039007040d0b050780300f900030046107118060f48182440c00c16034420501c10b150701c0300e00d02c1807a0b5101c082c0c0021800f1083c580e4400340d00030950910080040d924040941240f191030036890030680c001900e502c0000e8107191064098000c0c001e05609000c1d0008035000c0d00800004003181e076420600d609902c06c5400c00640b1452803a81e0b05140c00501900b615 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 870787203 1250 870785953 870785959
    0xe150f0f1302040f020a020d09032f0d05010504021003020c120f0c06180c030f060109020309030c071211090f06190509090c01030e070e0115030204051002071403030405 74
    0x16640d030380051400034520080c00d500024981444407000750301c551080e5507156410800044c3c1c3e07150781050180c540010b0403510804c02c1100381d01400000c9001c01817052000c0c00034640d40c43c100313100070300710707612a0501e1025400c203c10a1040042c004150041c0740654001e0380c00092001814108a05a11442000131071540c8403001c1a07003606d01550042403080503010b840c1d81030000090b45241041d000b43c404030a0601c0c101071100301210180100701200f0b030110010300b0f0016814407004d0701e964052080f00b9a0950200008081c40f90a104030340109007000709032041d142e03c55040030010031240d4010384202004808860fa2410461603050244024101002640d40d522007081034482c44040c149030305a021030030000340b584030003140600880700d42002c2c00c00f0448420006089607006901e070306050307005580030030080d4902000241950840d621400489108034020b902a04c940d510264202071700c03075842c00445a01045150a9500b03803546c8040c00301900b02090b40d60b0145003e200e47c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 870788453 1250 870787203 870787231
    0x50a0c08010312051b16170304181d0a030206100b070b040b06010504090c0801031713120f0b0103110307090b100806180708090c0d1509050c0406090e15 67
    0x480180190b000d414040c071484100b603a050b902c40055420306d04169411082da11441c2d0f000c2c081000c28808802560040c0d030f0045040038600404a01418110424030081ca90398181007141450540c20342c04010120100b01c80320303c070451400941e01c15045580c8c40c0210451080800d442c90040210f50032250000c102002a48940d1101051914050903c03810700c0303c01c000018000d074040c041c4509564268446503403035851801d1090716500101502045d15004109107180c059000c5040401d8402c02001008403d0780e074500400c1d00071099038064103140080c40000308001c3c007400243c035400b0081e42681c001541e42c9101805076540060700c142d00c0404845e034801c5030b9225201e17440e44071074020100002c8001110b500c88003190309031903900015401d130b010841c2c100030411401080b6003069410508074401b40e11035026858807104100306260302c40314480280230703040081c0d200402c8000c1c01044a02c1d507a40d48240100010302102001e03018150304050b0880805520031311680c11a10014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 870789703 1250 870788453 870788483
    0x303071a1602160b09040b1504031e030f18030b0c0301080d090e0105040213030b041b06080c0a0f1e020c100203090a0902090d0f081e090d14030d0f050a0c080103 71
    0x421607400401400360001d0b0747d541e4801603681d4600484040c002002d195607511415401c0603950645031031280d2428007140300040000036070140032840340e20b2580c940b684a0501110b41410989010f92020b400000107074280090501228000c40c1280c50791012a103828550100c2500c61400c284a405407080d0768200402060600d1b8008103040102f2144803d02942c59603501524000c0581e001e4685602002d88880d6550340103500901416441c10b00030300318541101180324074401c0405030800c114002140185840c010030400c10481d145d20030340525101c0c00503000750380d04c2e68029a1403055260342000b800450020084410003900034161101c450300b00307802074000c0c0d40902403441e0040e20a1802c4000304620450700a40c2030b2040c00520ba4407404110b0911109140103a0840c9003081082151001d0f0f0b00c5100121049038464268266248490441070031400707050489502982000c0382d404111405034002d51003421100c0040100d0705081d001101c40c02030034000100f04006174500c0d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 870790953 1250 870789703 870789719
    0xb010f05010e09070e09090a020303030405010b091803070609110d050c270c0a0e09010915050a0e040b0619031b0603020a0512152d01050313110303071a160216 70
    0x1b0075807020b25003048590b1a0250ba01282c40c45d0b008036400d46403a5901d0600c0c240d00e1801500300e0303400c045030101644444071101161901ca00c545d00e0004c20a9540f80440020080d600340c0d0081580b10041246020307801c54103141e1745813020b01e1040c43c414a003a2513200341d45042d05400404403001803441d0748959480d07461400c00d55005019510034091490015000360b5078600f00d050190100b8000440c05000c089441c100200640c0c100318031070744a041061000c40700481040354040c0e0484c18071100c50b1076200c08a028104604028401c91213252008001d00101e85048180c51140c05900c1040300d6595008404a01a041c80e140010340304000154260401440d480c0c0c000c800c0b407501da8907000307a520010303421a0b40e0300041c08100c41c0300341c0501c5420020b04100c1001c18000c0c28450300d1850300341c42201800d0780a400c010290f40c18030710080140e0b24200166800c0c96800350310300f0111840840300f490088812200005452420341218600307a00c0422215001c109144021940c28200401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 870792203 1250 870790953 870790969
    0x1050a051b09120313080106080a0f0f0f0c0b0c0f0a0309030b100b1303020103150f0b36031212040321060f05010e120a03110a0b010f05010e09070e 65
    0x49030707012501c02000403800c10180005c04c000601c00c0702e096102032800e10400d00707684c2c0c19070040c00d06400c40350544002c5000c1000380400c16520024020304c1400d0391624a51010420380c01802d1a000690701180030011400200f241d069802c04441c0032107109955a0340e00c00110740f008001503503002c0308100080740c1e0407445802c00381c016075840c0d805d91189004002900016040c0c5015030000c0e03c20029543c1502c1051018080d403010004010700302907400c01ca9002c035124004901d030300000d1031944142845081c004902014402c2d402d80050505103800c441014940c0c203100e80240400080000e410030115850559000080c0205560f0b684090311100c0d40d940100609021650980092100318400d010180c00310707a0607038035005d083c41c000401740641c004040f4002c6040040410210400080018400e5171500c0c00341036849443c0d100300c0c1405446c1d140105104150000807503402da451a0f810140e810030b9886082001304441041b086450946410300030444240b040b02c42030a008131 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 870793453 1250 870792203 870792217
    0x603030717160f12020606010c110103091506030618050d080a062106060605070f0b04030e06040f0509151f1116050a05010f0212031504050403030504020301050a051b 73
    0xc03640d040c900c50070b81864035088040012540c400b0196211002c00508460f2600780c02060b200804080c6012070000e050b5a0140d0400740c411302e1a0030540f4020380c071a03089210700542c88003c0c80415404407909002a0600c0c1c0000c5403464100070181e10b100e56407041604070550060028100c0180724081602d108034044d10852a4603120030340444c0e8102d12058412550b0003440034403c040c5a00e0401c41c0c21190a9081802003240800107031000c10205d04c4c48240b010b80205410741c0c10340b80d81c0b505880c100c41000044e5003125000c10001604440c86c03400c401120b9007507400c0100707030b40e4120079140400300302800c26911000b4a044001e10440c0106008140700407800d010780c200001206403071404903a84507052440f00d541030f0501060a141070714400601080c00c140042c9001020080e4640480d000e20003808070002c00000d060aa51a0360388c8401e000c041d100300001d0505080003070181204403801d900070b60a05000c1100c0c00e52a00c500c80c42400306200112013070462004c0366100d540720003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 870794703 1250 870793453 870793493
    0x606101403013003050703181401050f1210080607030605060315220209010306080a0308400506060f0f150f19140304110607050f0a0b071706030307 65
    0x4000f2280b01900080c4600c02500030f40312980c44000c6483c0041881502c0310f00c410f00000150010040e80e22024048e00d003c1e0000d0a2850b00d4034000f55824545001c0c045000880c0700e07205d4203010242842d502d142c0d050b41c0c44802960b003d0364410500f134040c0c89451044640000301000064150003034088078503224131008220740c03540e00401001078030003604030a10455450b80015103048560b014070406004005a4005d0060300120f91006801c0c041c00030020b5208030111200b101c102d95084540c0500b040c816001da050b0030702c2440c00303284c82d03070020901210640b0074000414441c3c900080804040e07840149152855107098040c0082e1800d03607108002c0e031302e80a00c05110030090200c068800c0081d81c00d00c0d501c091a110100500d02c02c3d1200282041060801c00d100105803c1d60320a0805072003611713890781c3c0b00d0302d80c90b0140c540700b1141e0540c2c09502484041c281009081e4013154010030710796403086c0c188403141e0900c0c54400019641150f1560081006000060200045219010601c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 870795953 1250 870794703 870794759
    0x20a02040f090507062705030a0f03020f03040b040e0c090f040b0303070606031202240a15030812090c0105180411070b010807081002070201081801020d0e060610140301 74
    0x5644581c60000383d1740040c8007040f00405402440e00c1000e140e00b11201856101618041c0781c040440e45070103013030700c01404004228216206260007001000d50102c0c0082c00c40f0741e510313555130441c01c807038210b40103103407140450f24082045240324800340ea5803580c1c001c1805500051007030030031004102c41e000741031701400140039080c082907080c1300c0c45e00118020b2402e51080072110400132f00b81940000054036010100c404100040410142f01e5802281d00c00300082c20b0240c000c43c0c0030340d40440e0340300030042400041c1c9044040c0d00442e10701e015521000c1143c140100000041d6100d016103001c1030300d9072041050f015007514180d08000c00601006585615006240c1c07503004050b0000d8001c9103140c0d002040030084a64108080701e03d42400c1501141003951682c0000c0282d000944400500f845082450001b0b00c003c1d030450751400382c001401c10049070700721441d9407680b400703c40581c80781d180140c0d082107013402000842c81503220250820f19581c00d012102e10505c0400000d03140ca0707050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 870797203 1250 870795953 870795971
    0x15130f0503030313211706090714030c040e0c090a08030a0c110a03170c0c0d0b0402010e120303240405040507120f0503030103061409010c09090209040b0d0c0513050601020a02040f 79
    0x101003042107480a41d5868101d9032046c111b1001c00c20f000e0003490084410390100820300780d0018056000d6204041c2032a502e071074080d640c4a6601503500800310388401441807110b00d5100c0002030201c882e00707560301d9450565403041c036516800b84040e18000b00e0399251f0707444001032065426003c4580010f11241225881341c072005034107403a012000720403200028118130400300420550042c3ca80440340c5110701d26041d5079905004102420090500c003107000308440356556012403c0000300e80104a903124541401103400e007104105040742c07100004050200b880c2400c0c050a032040d07422000810a0920f0710b400305056540010741a18540101c1d070080c00016814070055009600940313004c200d00000680d800da1904011b44510145d0785132072452400da80d08018100221690400b0041e01e0b502a00003045c09480841e44017640100b40030094000c20146a1000040d25815211207900c1c00304281c1d80001ca0303038144c94560140c1d00c24030303011005203483c0d00f103104082440d060204e040c1382 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 870798453 1250 870797203 870797243
    0x204050a0e060a090204090c090c11010b01020c01051c14100e0f150d05010c0201021206010e0a09110c06041203180c0b130b0a0309030f0f090b070f0215130f0503030313 74
    0x11034120120b0f103510396044002b003540c00301d000410310320307214000c104121107040041c0d640c81031540101c1c144600841c070300c555040c5641c2502140c82030410144652100d080e4905c150180894048400c1c1c0d000e9400440c40c9070910180d07501c0350458100901c1603032100382810f0381840c50106100d6020b1445611400090000c1c05664070710101c03500050303120686031a0b02c4203070716070042c41141000344d605046180c96440c050140104d500f14000010103613102c41d00d12049100303515107201c0300e2241c24140b00c00c00c146443c10103204c200e255420003105261406041104080d2000500040380c4c80000344841c6039020000c01109014800c402200c9545d001b800d82c180e0014001140826070f40d40380c19040c036411560071420303a0103518006020014200c0d001e40100d0050261000e1400003107020010000c820311403805058000b406550701c00b5119848100592000220390640c200e810000500c0881d907480c000c1c03d071003004000d94215515003c124114050200d401e6411501228941145d00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 870799703 1250 870798453 870798473
    0x7050a0c0f06090b030603030c15090601050f101107050406120c060311120720010c020c031c120b03012f0304080703030e0a12020703031e050928060c0204050a0e060a09020409 77
    0x2088000c8410490300d8490720316070402e4414ec4c00140107185000c00404203684d0546030b10600b29003820505021030044610502d86010fa4014039042890307c3c1020410300451011500c8a511641441c9800ca854003011000d83c3e06050300ca0505507018402c01c2e0180440c07e007015880f4089241c005036401e0b900758001914921509400401d035036640f885416264140400c4c540000c0540c02001c0301d0105442c591a00c450300b42c0280e0802c110b032111440403c08a400200764a00e00030000e0043c880c80d800b28610100c13a0014010b1380188401070306a28807030a80a40b403043d608a65114100016074400b0f134080c24031a280035025000d540e48890004000248007008041150300405966065241c0038180301c5051801d501c0342c1b8409810502e00503402012601b007401e042c0c03901840d45106020203000c15107046200c0e1243c101920300840d075640d00c04100f40d6458000c507070030700a6440b0a5504c20440310003100c5031105400410000b0315902a40d00410075403440500005403010407501c516000c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 870800953 1250 870799703 870799723
    0x51b030a0f1b0b0306042313030504090c080f01080c090610031806020a030c0201050609070f0203120a1a0603040c061409040e1e1c0f120207050a0c0f06090b030603030c 74
    0x10f52012090103800c0c00c162003140055070b550702c8894a030690f1802d0158a20100900032002c01036050a00c1303003010b1082043d00d00425030b01c0c8040c0721a09000c00094448072003100c500d064180340c50000070322030320006005400080701a1900170280c031501309000c40011004c85800501da140e00f01007007200c501c40c00c188905401480c0042e00c0d090180780080686103101803007801c6a040c0014483c007952669034081e0042d0050070401c00d1245500420783c2980215610764403154050010032014002d81d410010004840d00010380704d0a2020342045081d010036500a045401002070034058a8003440560040e034030300e400f00a0a00c0c610400180035034a007401c0002c8250070448407400010b0940440c1464000c44002603c00d20040620340c0c8e200c4a00030103808100403001114085485c00785c10606131074019000300750340e6411182895959030507440d5045414802000001925039080c441201c261025a41c0e04442a494103045071384640028020aa150104006143c90039004000d0b90b145 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 870802203 1250 870800953 870800969
    0x30206040308100f0b180607060501030c150512180a0302010b12070806070507080405040c051e0913020705240108071a0304020607061b0507051b030a0f1b 68
    0x8926007480d0082200328041c20120b00842c612505201c106415507000b400d8500441301e5586407030810a48036079030903090f506207801100008020052003a40d8100c0c83c16203010f0030781c81c03880554500080c40050308141f9a41c000644c184010840c2210040d0032580203405681130004140c1e890f40f6030350604100380400c0740580e5444030401e016092803044240d10700120b9015104092a002d02141c0710034006200408102c0b00042c1902007010302001e44000d0107001d0000c1020490010029000f0b61282d01c00300e8808000340e08043d56006120700700e80034810003608882078500070812100203500702d400f08951138000c0482d81d28440d00c482580403503640714882020312039450320b4600c40c00e0a0403500107410746e44056036446005c09524084175041030707040d2803450b610300044c14403a00031310464140e2940c044c1024207102c10560321201414125000e041076644030480c00181080b801c50b244a52505604616002c002041c0c401c1c2800301c0e51401074040c0070700f81922140030b50504188d6005608 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 870803453 1250 870802203 870802213
    0x909180a12030e0106050301020f032d01091a040e070b0d0e010219110115030b04051f0507030c0903120c050f0a080a0e03010b091503070801020c24330d0302 69
    0x30f80801c00f4081c140c003d0005038021403810094021700d0b0014880204050701e41c0e040301070803511003400d4a5101c0d802d021020b400300102c0d6100c4900c0c0015040c008003030b2010581010021030b19190501c0f4601030588030000501e043c0b454405101101e802c2030b0400384a0383d80c0d030310100200020a000614840e0100300d03c3c0c80c02c07a02c2c1e545c0c01409840d031591805616a08d0034002c4409000b8004411040d25084201c1c20451707555460001c0c98860350104950b11035a80c4a4200c0f515030141d00090f00602c1c0680b424820062618812556184140b0001d8030382210030702c00250841c0079039a01450036004900b65541c09072020142480c1030480c01003110008000140d02201a030321040b60070018030114003d20901c03041d200001d44002c800707050340c912170301d400c0001a2a990100f108900800c02d00b0004d5444d0b401070344502da1070748151401b004041f001200301002c2140040310592082d01c601d2038414004910078448414900741140b003881d002d4a1500340d668555801b01c0131041c4612950041c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 870804703 1250 870803453 870803471
    0x30a110d062301060513090207151e06150212070809100203120c03010b0a0e0a091e0501060305040209070e0136060306050307060e0301090f1202120909180a1203 71
    0x2900d02c5405910182c100141485004550482409100200d0b04004070142c0c84540d1401c2030030314226003403c071010702c520f0150000d4101354001014039074800c2084c020040d9640d81d040300c1c41040100c0c1e803103100507000305091241094055018013446402681c2d12410240c601000c5104c1e1890300c144031b00581c2c004100c02c25001c1c2001c0c1003a6010310700a0354a803d5524010b07000c2e8241c014800c03500e040c0560040c108041d070702d6201c6d803400207201543d0f080c4070916190301007101074019204074440260418001040140c024000c06020b158003401c5044a0342c1e4a6400b03ca800b2032020844e410010765556044240c01c0007100c00341d10001c0c3e00c1c0c1c040a003a0120480c8071140e68540c0c041c00c01d05080400402899501043c04412034865080043c070780c0c0c4d549400a8010034081d600105030403041880002400440e03890050749030000e408444192801c00802e1119004550f071031030b4801c51802c0003072640032211807140d68070a180411a0503c1e00a91b481c8104441c0c60340c04200021355800441c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 870805953 1250 870804703 870804761
    0x6020f0408010e01090c03030e031f0b0f1c0312020f04330f120f060b0417070e01120201020c030a0503030a11030f0403030b030a12020705090a020306030a110d06 71
    0x12030320394440300f00800080d0042d1b601e007208588284409002e0020500d101c2d02e803610140911443c481c92404940d5482400d0011417005000c0d40342d45500420a114400225040188902c80812803100007440b044006a07412580c0800d8101c0d4400c40d95001d00c105c8118048001c0544082c0c208000e10307000007400c94016110340200804806040c004860f00016401e801140300301c070016030383c178255000e01c140b02342c4100903161044c1b8400800e4a04000050103514510151086d80c4018455042280e00103030311559868590144100603104000104002110446000d02c02441801902c0031361000070000703820a407408005031240e800010030480f143c0414410105400c0d1024038080c2142490302c2c00b1180400300a00040c20700d41d6500d1004969030b820060002101d03405074200003c5081404002e40301c920922446001c0c0404402207440100c040c001d4a1041c6006001002c8124403a22181d0041c1c0c41060078a8210010865040200d07146004010464110240b058410507800e165 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 870807203 1250 870805953 870805961
    0xc02030f0c0c011215051207030c0b2a0318040e0303070c1e081b0a0b04080c0d210b0103020d1d0607020d020d0809152e060906080a0906020f040801 65
    0x448401364a848658070b00061910402003d4400c01da9640d4040c45104540a1402069410103011341020840c00501201c4440041011800300410040000341c3c400031130900120101003948290010f204020720145080c0d03050300703e8007005001066100c01c00b80f81c00d007141d100303940740300c00504d0303540c203013418048403a10b10210b240860b504130141014a441c1c6001030300401c0c484000201c42403a800042d00410451310f10302980061440083c0d013031926001c011039100045250040c06900c008003c1030717009510b85840094a062451f46562441d04e02d80c00401c2d0145010307060541c00c2c007820b1018841c9104030150720485100d0250141d400c41107041c0340000085c00d490442d40a072100ba89444d0340414502800201402c054106d074540604060414131032801c000a00c510800030450403402c010070042502d2000da0300d140c08001081c0c000000c4522a010300b0001c18107100c010800d4a100383c40156000d590100005801c0409903075000580c2c0c07002d45049880a0041801d00421000b0701c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 870808453 1250 870807203 870807227
    0x4151b03150819170f0307110c0f061e0a090501020c031204120602070206030c090103050f01030201021b04090c090203010303120b13090201050910021c05070804090c02030f0c0c01 79
    0x401c00301d803a01d000611980c52082a40881025010603203290400139070308072a21100c403d0202c00754079070780301c865071086580040b5a00000600100d615070302c800c801282e06a0154000b600c4112406285c0d005c2c0b10060740b01d1030705103d05000084042004040c0704026050003003407030340d41650301407800300024984480158140d1180e0441c503101d02c6000342120072a01150030070480388104500e541003034002402050000380d0013032000000c000c8240e4103030008203c0410262020010f54030b64200c10140c01c0310900000b0b0150740254442518004050b03039801c07100100070404900340303840360b031581d104104a9100411440e0040014004c041e04100207841102c00c591040141800180c001050540c0c01455000060303506c850700d05c1564803480032110701400c080c1c100c000c490760300d11009588220b208082900002d1201c1d0b458041c510680444162540001541e400d090602101e80010840880050f080d803004012280307050382804040e01074105110040d00c510085140054440c246100c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 870809703 1250 870808453 870808481
    0xd11010e03180d02060706060617091903181701050702010e0d020a030c0f0f0f06050606070201020303060f18070203090a090c05030a2d0f0f020301120b04151b03 71
    0x8010b5222002440b95690040c040850703a5407040c0d01d0f14000701301030b881103080240c20241041030102e8082e1300451200407402103084028401da5807610007580b942e103000c44464541800c078882d0b00c04244903410748010400c0903888088503a681d03994036080920b02e07602e6031010f65150001c10100710340a20801c1503014403000039040c000044e820081d229114820001e040c019400c02520611410444c0c0002c22030703101442d03843d200c03800e09181ca05122901000c581071402e02d400138040d03013070100540c1c00156040e00218116161b001c20028001000307003c454000d0642010307400003184885440d402105244c02543d901c460010a00075a003d00b500941c2500d82803010800d100c80d071120492380e0192500e4000911040e400d090400c0302d0303003000f41a0382d040c11690703030310321080301d050b81b090007008a090401c100062030251004140d0000340307d85c4111514401608001c01c2c08246490b9206100e1000700900c2103500403042c0c100c03000e0106e85000c5600644003c0f20b0030f9010b01c607144007100d1f0701c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 870810953 1250 870809703 870809707
    0xc0804020f0f2814060d0f1b030f050606041d13230105010e0c040e070908102316050c0102070c031109071d06070204020909070216150f030b120d11010e03 68
    0x300082002e43c411b810003084640e90707811110756001c81c181d002c1c41000401d50003540c03e201d86121300070301805030900da80c0a00d41c40c240200f10149801c608850031034042c0d408520086684080002c3c0240c40102400340040300141c1d2580001d22290b50540f80e050141c60310f4920000da2480d0a0849505030041680c0b800c107502481850b484410983d400c035501c1080b00d0320aa80c07445011242e08106501c0041d080c0305034914018030600b507070000d114043c212003001581c3d00341c075240c0402c40030042c0d6200450440341da10450f41c00d8844c4004005e0021403a0001d860b24000359140c40002c003a9910985d607085058400703d10b1171401c0e42d02d0680165443c942040c800034104900c56044030380400e030704c0c0300d0030000402c3c10441d10350f40c064652a000007420301c03455280000000c1d454494683d00040300e8030344400007084a12040304510071454460303542c0d003d104401d0300b0a4008019501c0700c01e40c40a10303011005540c01c81001142041b885039900d1855000c00d21940c2801c0d0369640d40521a25081 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 870812203 1250 870810953 870810989
    0x414061005060d0207110310020301080129010e01090e0a09020a0801050f060f0f0301060e0108210a030c0e100c02010e03150c09040e1b130c0804020f0f28 68
    0x6124140d071529036a4030f000503540d040d2403820f6084400c00c03001c00358040c0101c144501b0350144a601440c12030790b51130024042c0c5808100032640c0c4041015011401001c1c4512088065111300700362015408181000480151504154003a80108480d01d10300991149110803c506007400c12200625400b8002e01ca039040005500c0d80c040402008180550b40c1c4003146840c0d03569001c00c40c1b0121101038003c1101503110101480081d9003401040e44610828242d03501c1c902ca04120500c0748144c2c1a031490070620200c1c4201c0140c0190001ca000704144043c81c0b00d031030390381c00d1400700640556840c0d0f890404082d00c00034007440040802644030350040d411802c0c2984000e117034503034003500c1400d060ba0348410007800a0010b003242e001d10a124415040713004610410100c00e103801103c00c40f0100e00141140205500ba94000719081c400240000c01003401401c0c4110f00450300d0200410030020403200102082400b504014a0702c0d82410b848001700ea8500b41e80f404501030f046038034442d002c8080b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 870813453 1250 870812203 870812209
    0x90e1512010f23150f0d0f0501060f050a030b07020c1509010806041808030612010606200d052502190e010b0412080309070306050f0405151006140c03030414061005 72
    0xc0400320150080000b14540e607852507581e048004c5c00400d0b041d620300c40f0741041c0115407160101115a5840c250012411070240a909403c075a4002c001404a80c15070380c0308014020050174140940c80341e005410003a03980d516510035a07125030b658040d1103980e0b01c030004111040c081c040600444c0341986400121000305080791182d034004030030554985550f804034900410490009145520b0004042285a440750542c10b074654140c0008a104160752405a122505801c00e0344c04a0020012404207008001c42280405841e41c0d014824940e01d4010a6040c1c0c0040969000c3d0051850103018144160560310f0141101c00c3c1c2a6040c58200054005400c440c41c7c00500600c00100000c6e5100700c082107007401030741e84144280710500304840c150102a8050345c013103400e0f0190207109044684940b0040784903054001c20544107030b2618a040d00d55610f1341581c100d082c20100a116810142040118040e922410030304c56031000d0708a00f45e04055010b01094203803030500c00104039542d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 870814703 1250 870813453 870813521
    0x6071d0616120801290717130603140a09080d0f0b1e0d020409080f0a02030a0807030507090608070314011e15090b03220b0601030506010906090e1512010f 68
    0x75900800c0d800144805e50200200ca0140308801001103000188803004908100d01900101c111008100c08050321a581039007580d4954001e0f129002070203000425203101900305c0d140c014041c1c0c1249182c0030303218400c0021740c0c4403c07005102e05920b400b005106400c000c980b80004a080188070070301c48003407000080c64580c111801030b105989504888080c06100006c4840701c001e200d03d005d50700e602441c030194507600481a04004105e00c94005480540240903403407080c82c450f503545000a040400643c1d40003009803000d000c0541d0788100784030400d50b0807404e60290186d0303c01001c1180d58202421907403030780390b000826400da03d4100606040e800400000c280c4a20400c0d19860f995030221010a40c110f03441c0400c915241c805408050005c0d0b039080d540140802c5c0d070144100d644490040d50303500c5403489404001010400c00304082c10000034142d4101480d882c0280e504031500d4005207800380b28805200107a551001b80c2140020148156002800c0001e020003201c008611070444030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 870815953 1250 870814703 870814739
    0x50a05120a1119080a0b220b0403030f0f1407020319050c010b180414071409040f05010c0f110714040e0a080301060903021302090306071d0616120801 66
    0x7160755044002e41d6090f003444a80300078020750588003a59000b207035540e50541401510720503002c0d1302056881c0f04009280d488600390450100742c04515070381d003038101000244142c1c10159a90550156000e40c0d00805005901c0900c02140c0701d1220030445545000107492030007950700801c48500980940081e29131500c0e0b0508200d622086541c9c10345024020718600d240e40f040e100c0d141d140358a0400c02c10540510b005051101525041001940d038515042c00381e40040082c10203125031b02e24149001503402849603180349614142541c50b582501c1c50011a0720200e20859101030049521104019a9910440c02050194684081845083e03085501240599124803a034080720714104031005c41180c0c0301c0c14140d50707036a40d888014480003c03400100e101d1030000585404601391402503908c0d400c0d00901401298032014019076400e078090804101c01c02c00388025001070341e9004003401c16000b90420004040010b4504140380c24030200e203031428084180010f1080725800c1181501d1 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 870817203 1250 870815953 870815963
    0x60b0c0a141c0305070f1d06070204090c1511061b0a050c0d0e010e120601091d150601080a05040b0c0319090503040e060a030b04081c090507050a05120a 67
    0x24403568911001d0074440080741c001c01520b14541e22a1120794036900543c81600300d9503888514010076a0119031040344004002807031030f50f00d070b4500c02c145089401000720303d200510000b914480c90b5208030b0301d00c40781d902031404550007502112446800c101c8031034400c203000780038142d0361400c00d440990356000c00100310440705020518088050080d412505d103a443d00f0100c4d141100003117401404000b129040900040310b006179200c107030500781190245c3d0706c101809000c05a00700403042005000c44e0081e01c409880740e558001c6400d609100403030041c41c40364403205d90752500c4400036111031000b420403484c0500d04410400071410410000b40c0210a004e1890b90b40c2c0c0701c00cbd004100c515030b40a0b00c6420b80c0d18000a02c410001c000006008440384e908405815644040c20400c0c400e240344409441340e00d00000203400140040010070010441401c04203126800040f00b4044440c503d03004c4038a039210500034806483c1c0034900740018541140d00c9049198201131843d00c80c2401c9074001c003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 870818453 1250 870817203 870817223
    0x9012306070204020309010c0e150d020703030213081005010e010803090904050c15070203150c0a030e0a06020d0902040f0204052101060b03090a0b01080a0804050105090f0406090e01060b0c0a 84
    0x151a920031007114482a0018020364490500701030083c000e020b43d00214000c903103440e03441511402c110003102090041200f0f41c1c2e003045004901c020107544031410032010194200001c00c03400054120883c06490004c0003022802e08100036142202d00c1a00701a10034000000108a150310010441c0c04001042c2c6014925880d1440c06510781071101d0759031580300e066925005094084500039140030b80c021001c40301c610220000b0760107a0f55060743c42d41544041003280c421428001e80201086410b140c084a518003600d444090407600003c1180b80340c19114a503020541c50702e802442d45403c03a09004503e45442d000c0064001c01046280107c1c10300d2078400865482029440b040060000a4865030f4a140144031140c4030b00c0754290440e80350401d00c0000c82e0580700040e0707816036a42d120103154901030618005603480c1d00030b10041a4080e80040f600c443d15112402840d001f452851004191201d190022500796482600815000300081c0903081d0039200009144641c1d07a003040d0008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 870819703 1250 870818453 870818519
    0x305060f09270a200a0801050c360d051005070c050c09190b03070f06050306030616050a08090f0109230102030f0109051902030c0403030306060804151a030f03030103110901 76
    0x180170421264001480c41d447c1400f00107400364103000800d04d180b80311401c03c02d114444244507118190f807080710220f14241c52601d00e0310341410034103903101a001e01c5c00c84039400d650381c07044800e0341c008440400010304500c0c0d9000030003d040095034010030007101e1400242c80e221030f49030000890710701043c42c01902c0c0c5000c0a41071f101801068003400b04020010781a42e11450050500e80c002e50f1414024421040003814042c518141540441100d549151914164080c2140c0c0148040c204022a020304034811034459000d20413003000714883c84000d000314180f64014031140456500c59078183e401001081841d10b50180ca0b03d06440300914005019100c0d1001499115a01d0310031800ca54400010300146110000243c81181d1082c0c0c2c09202603070b207403141200e4010054800502c404100260f0300903208068001c0c4a0039440300c1c540204510a107000246040c0c0e20341e0408550303400000041c4184208900d10b01e00030702056031100c9495140c1441c150301c5502c4240ca8000300701002c00c0305 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 870820953 1250 870819703 870819709
    0x162901090219081b031311151603091205060106030510120204090303090507090b0301050c0702060a0f020f12120901092f0d0501020d0b03120403030305060f09270a20 73
    0x100c0120501350341c1501c0e0710b0542c0001005005030182900c0000c6001101d204510b0807403040b60340d840c111034900f424852050f00d80100300c00700136004c4003030103013400d00800d503005260408528180100c0081845502d0800041d0407510003806154003070440020502200d020741d186d020540d80d056400091481550800701c0013400040002403580c00f500c000003c1031400d0f40c1280840440880003000303151100ba603503031100d101c1e00d44000d4000c101404016000d50040940361008002401580c0c00c2003200d000f40c5052440f01c4107010502c2202154040314580a1081b0b2648404503000030400b03c000b07500d51a20a140340c0302004960491051a840ca20202d07101085903c40c005d0000c0028491350300d070441c040d4006080c0740e001c080c03030005507004600e40080d4400035600d40d038100c5807a003415920220003400b0010714964200181d4000c487c100d859840c0444d2040d505054600000ea251010090340d92044041c6514190700c1990b00e2804520601c2c07018042d0b41031755400f014020750039008 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 870822203 1250 870820953 870820981
    0x1501110a080c06040c0f3209091018020114210112030e0a0308040504110910031d0c030d0e010c0204060b0d0c05040e0a0216290109021908 61
    0x6000203404150b0540303007a00042e000e4040c6100d014082441d82e00c511514503100c05900c9800f8001904004160401501c042d030038480c114040f403401d012204074004150010025a49159a50701440c1c1030b48a40e4400c0c401d44121004407200119000050780000f0980000008030220094000610103405080d80130f4104507030440d00c1c0600059a5540e00284618401c1141900442d0402c0600301035440d14100c0d24050700d91010425040034240410f10000713001d00d0440010342d41c2d040100390116540da1352185603000e400d64001c00c11481e03516010540030703041c100650f52a8001206040c4a540110304030032591200d00c0c020120b50072038401201c03031400e210380c065005440c00c0e170003040150800c4000d10445010308410312505c00028812276aa208038800c003040d444200c0c0c0411075810300ca40007803005140c2c003024900c10180b251100700020031411068411034040310002c1d80300198510040c3c5c01856000c00840c200884056006040082d0f074440030100b08000700020300c00e64990030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 870823453 1250 870822203 870822223
    0x30105210607110709060305100c05130b0c01020c100902033d14040f05060106090f14061b0606091b0702010f180308090a0807031e03090e0f0a0b09150111 68
    0x50000b87d949007040c0c1c4e1184018100309202d142040c141c0c0d09910b00540071141401c100640c840b0b882440e054000b54550422050a03a055401300191030984070b08010141000314a0100018110224130400d07141c08039002e40484c181403040001d65807900007005807038400d4500c01c58114551040c000c41001004000c1c00348110309141e038140814000c242d002c202c40c061041c0220303403103a600d4a90075164010f00d48141000c08107040f0013444881c0c0b0f566584125503002400c1c5a091820b40859101c003141d02c16107180a540c05101004241d140c6503072010780010500580003a1280c5200c1800280d201c4d03090007a044c00303500d11500c10503e214544401e010140031030b010020075140c3ca071500c6a030388000401c80c804d400300c85000c42c005070040f41e108112584500c00c124101c2c041d46016410a10381c001c05c1e0305001c0c0c0c28500281201006000521403442209c5100380c40c500154010221007020141c14091055142040004c0c4011483e83c00905824200b9800c002d2040c0340340c038600482c480c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 870824703 1250 870823453 870823469
    0x11202030604090c06031508010506210c150a080c030c181212040302091e070f051603050904140c0307030f0f060303032a0e01030914060c0301052106071107 69
    0x13000014509074144e0003140c032440c01d0280d5070680360303954000d2420703924195152544041c0121001e40e40070030441070898404d0700d003019a42c40d20603860009070085001c0d41034404038040003442d1004158001400f40d401703210784007801d0640c1401e4410580c035010345281c40c1d00d00c002c8107005004641c1d13100080c103880e0075400c048450400074030810301c11035001403100328040c44101d000314003503a000002c5200203608000404500e40e17500281291400c1c6d030302420b001840410011808000244480d212490780240c030f03000e0b0364005600a01c000c0350201007154070000825014005021070385402c507500a4186c0c0341c0170810101c140183d500500110300200c000a1034418004200b40d00740d00300c840f201101d101e100d030406029080c0c15102010442440740090b580e001100f103190b0180e0711980c2828090010526511800c241e000d00d003050982d500b100840c00070004000320b240c074130b134140143c9181190401140c41110300c45135035041d014007464240004800000708010003040403070000d0080c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 870825953 1250 870824703 870824723
    0x10050d0f050a032003040510051b070f23031b0402090607050105040c060c0b0a110f1b161d061c030f0f0305280204150203180f01120203060409 63
    0x103440d0240510303120900844c43c81ca0300700320081e10018007106a60461300054024100c030307403915a00300c0700b65001c0105040c1080b036400c1c050b90141d100700402c1002e0038082003007030031a5080401d48110280d00250300155031045c0500c9040075100030070702208145040703604041c0d4080380c0002030042c1c05200329403a00a030f004103c030002e12105400031800713180a0440c10185544a810072904d40ca40c82c5070140148501401107000b4601651000f000a80c9006904d03003003025500d54200c0a42c000c0340c80c00c03030b040075130030031410305440901a200c3ca2014a070a809030552070261420582c0348469090070520380350b1f10000d213035a1120700614150416020310070010b13051924015015521084401e00080ca001e101e02003864064801c682c0900d4a0402e0041142c480f483c082c0082c0001c4850000100e0302400001215124081108580c11082e00a03545404060103500200710304c0100b054800d123001217201513181d1b0072000640e190220ce00340560f69a07910303c08203028001c480d400401c1d017494 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 870827203 1250 870825953 870825973
    0x50d11151b250e0f09070504020d090302160f09051911040e0a1119030e03161703040c0b0315100801060815100e010c0b070e01080c0310050d0f05 64
    0x80424000d80303040382d26034040342c80200210038048602d07a90085242030400d44004c90380a0301c03030040c026401404141121059611b45c2c021800f0ba130440c00e402c40b00c00e0f0300c4034081c404154050040303003807400240900d10511807400520740103181540c0304503060966514045400e004107007074014890780d80f0440501c10040d204100d02c000741c2c094070a100d00781180302c01051444a42e40204120f5644600078182403001d505841074080c03010403401010700d0b5462162138088003051003e000d41000130800700c41e4225003424000703104402e41c4d6135a4030880d0100b003004002540c0e2400b110035110a20319207038603542c0da19001c88102c5801030940e5481b900c0c560001c400560b021881c141030303d200c2e9482c100c080e103070700c0780700c1e41c0900003c02c07116403205880340e804a070644520102c03401540d0503d004803c04149031542c031020801981d038000081c0e554800039581d560052100e0703130080da40e11009490b40c0741910700288049002d00445100386401e81d0b6080c21b0010352414004da080c1c001003980d84001d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 870828453 1250 870827203 870827257
    0x60803070c15080603100c210501090e010e0703030c02060d1401170a030e0105090f060706020304050d0c0c060f1403090c0301060b0406050409111c0203060a050d1115 73
    0x403162041407408105620303111402c0d442402032034010304c0041c0042c10a0010340519801402e01c4807240f1003040001c04012201aaa034140c0103401e06211900190319410170b00c2613410380d090709c0111401c50303050415628002d50001800d20450750103160480c0011168030000742075110b004500405182440c0c881c95038140d95840050480304048a20300882819840e0b03240ca800488401801180031505058540c2d40110010326541e040142503d14100641c00052003c0d004110306680d03403540032041200304802003119452000041c141004001c04641e10400d12001310300032482040002050000340303070302031a200240d002000c00394680b6498400411551460f001920b00d00c03079800c02c2c10025007550b40808503070950b1940d80e503052405050440030300c00fa101001c600c3d03510490801810900c24034101294540102c171810140c1d5034109142041100942c2d43c1143e4803c0e0004903140f0006aa40d02500f00c007040c01303070756040602c0d81c120700751403d5002c1c161071810821144850842019 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 870829703 1250 870828453 870828473
    0x1808040b0a0c02120f1e0604060c03020d06030c0f17030d0f090602040e27121e1306080609060604030212010f0e030d050f060303072d0809130524010306080307 70
    0x24980c0c411101c02540c2c030ba54081b40c2045034540d144094002c00045404118a900074042c480f101c0c2c00c0151810265540d60011601158004d56152009071001d201c01200e40c0c2841008050740c813483e5003010f0004806a450740714940105648940e0b0b5079695014203203c0e08a80c101039044501191182d40d94242080542c0040340c1c0000380c6417158000c1481019006403100c40c101e0100b004084820306041243c1881d0b004445404407443c8140c940e03101428540020302c000c80b0680a1510030a00d000c50103010388070081c24144c07040301e84804002d02c50b211507068a003100d80485001c01015001c04c64207005103444c0c1c80d00d41c51107040c222803a0b03800000100505841083d0102081155143c402100b140102a144a03a16410422803080460160903200500035540c07060240f40402d600256840001070280c211880c00010078249054a401c540c83c0c2c8104a1280d01801149081c0b0340c40c82d1042c1c4406040b03641c10000c000741d115103074800e0b403002c0c0160002000320703981c6940e2400d02c44440c03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 870830953 1250 870829703 870829723
    0x52209110703170c03060d02010e270709050306040312090f050f0f150f07090902033c04021504050409061407090303050a080406020903030d0f1808040b0a0c0212 71
    0x2144409500110b4158402c58070f52007841e01404c81da0440e140c1034100a4800340d0401c0984c100801301408806c1a683d80108141715010300f699500104400d2240c1c0c1c800c00c43c01840319043c05030b004000c102d42c2d10042152a4002d40c10315204400a0300802442c00402c0c2610010b0081d4110b0595401000000a2440c9400e60960100d40c1210340140c10941c0d100b41d40c0d10b086150318550001308480d00c04142c3d41c20782100b081d003007092000340c590169104980085403a06e54540c001000f9400346402950940010600094012020030403113400c01000c040190000780207a02c194070407181d6074150b406880c003601000744207000081250401001428000c410410003428039404556110302555010089aa0645401c4e081000c0903005459418005000780d07002602080340b02e1080d81d00340001c0c0344080f48071100280840310394523444101c9402140c0800b080180c42d1044000c1018202500e00301d42c2c151452655030382d1054022140744403580002500404426076044495402180d01110 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 870832203 1250 870830953 870830957
    0x12091d010603111e181c020f01050a2309120114010e070801060507020a0504050c0a030e210d0e06010308030405120319050a09170a080604060501052209110703 70
    0x1414407540302c01c030014441e980301c0b0710031104810404d420f140c030100e001d0020501e01c0034161925401880114117010311142e900302c07190f203240c0a0041141b5101800c0a01c02d0003c1c41c00a040c06552540a044078903480032540c0c1d15662a030f80540750307002030400c43d811100080d182030a10a0080700090107010403d50071024402440300100b445000c4091052081002d0368602ea07040e480c00c00183c55a0788408030a0f0b820520002c0c0118841d211400b841d40182140001140d551500401c020100da08980c2c800d60340ea00542000300500780d000101103102007001c0a815654001103001100030403040444150034011040000240083c00010314450341c002c1003560640351866a040701c80348012900c4601001e2606040703007034540184e02140e8401143c07074000940c4402500c8460940300300c9200e00019460021720704040702d80c0103492640104041e5403e0281038280700010b810b0b4000c44903140d607540310301c0c6039106030388920201481c014841c4600070081811500c3c0b101103940c2c41500b0980c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 870833453 1250 870832203 870832211
    0x3081f06032702010813060b0a0e040201020f0705030601210b0c04060210090b0f09010e0a080c07080601080c040203040c1710380411030a050f0612060412091d010603 73
    0x40d01c0044601110b01c159059455002e0b40da0b650120160341071542c03600752201d070350343d10740401d80b61142020040034046120000b041441e180c80024a000141c021880c03a0360010441041140c50001c8c016043d0780304c401e00d00e21041c2100311144600d00c1c1e05440036108584030400d10512500c120005c0c0217541081d400e0307858402d0b24407042d105403615040000c0660b6491000102186403158202e03400889110001c10050b00a001c0146090400942603d030f240f00000c689803120b20410283c8010400c407000f4140079850310b16030a40300c1d6180702c0d007240229000000203080085608450024018841503040c80390310900344140d454902d03d5141246e1450302c0301440041d0074081c4801050403d0741640c00c4002d840510a10180400c0650035401c29100e020181007207610700e0280d8401c1d0604000041c481c50400300d0340e0103804c00130344514014041c8a0041010050208000740d00c0f07500107000c401726490012080f120f40c61030342d0005070030340812034807107807030800309542c55040b562141d6040c8 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 870834703 1250 870833453 870833501
    0x51e0402190e0603010e0a020f04121101080a1505040908041e051009080309010e030c18090706090e07050c2121091f02070c0305100c0503100303081f0603 68
    0x303264031080c0036488891b0811b000150b003404454004009030f114229100703041c283e40c0e1130020b0464400f404110b0708845084048880742d64080c0c14645d000091000502c2960076810940d40c118225000d010300840e21900940c05101d80e840032540240f0ba0101550011100c00c841d200d82860f26000f030511a140c0d8500ca0001c0c1c0e03121307503041c10a07500044041c520705203070000159010840c3c102c0745038050050041e18900b56644004c424041c01c1422079007031862074000c0d0f056041400d241c1001091018040003400b0200388420788070340c1b03c05141040c5a5805271010058070f44001d040c103e214600301e000c400701e01c0c0050000507200c5540b00c910f00c0452100400302c40c0182440c03c031003082c003031383c4a81d548003ea210030b4412003400ac5261440140707046440c1c0c450640c0e88005400a0380c080e80801003141c0a00c00ea4031481922210a103040ca0a5080032910a0112100c80c480a41004480c2010070174195008000d0309061000c0114a04240c1d641d003c098080c203580000702d100b041001c0394203 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 870835953 1250 870834703 870834709
    0x60c0201090308130311060c0904180804060503040f08030c120603070b0d24060c02090705030601091a12040309052803061e0c020a020a12020901051e0402190e 70
    0x9007544540c141c81e15031095603844039418072182854000da04001d0010901c00c22010140400d5010302e401c441c40c0395503450f1040a1106417800f404a01241c02ca10f06901404110300d002a40c0940300b43d454001d17034076161401c1c1104000809030b030281401d000081401080b404082c02841581541c1c13019891958481041540b151100d100700e44124008000841e091103843d4007114020300c00845100180715030307003c01c0c0b1020312150003c1e4003151a403003c000552400d4101ca560003500ca00d0090300d1440d1240c0000c0c0480301911484040700d0301280010009803212058400384007200e4078984540c5011b00340140414110b00c00d0b50b0040a048210390007280020590503421100103544180700391a41d0784400c02804102c0300380f103900c100c4050001c04200d030746c02480103204540d4020040c0c0807441c010403000c5101d40d03202d003003207034154030410300107860b00040701e0304440d0203e0b485c10f42e15882030070300a00606182c0c00039520a02c000f9008180d000556140c054080e116510381000d560000d0078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 870837203 1250 870835953 870835961
    0x50403110f0d03050901121103011d0903070219230406051c200d0b01060e0406031a0c130f1a090102030d0903091205010212060301020f160602210103060c0201 70
    0x1005030042c10004820b80030030301800042100f000d0600d02410040304103e00074048603846040f05080020000042000003110035480d207540903d40750007074050400304001542d034071034004000e0040e40390000980e001405120b0300c100500480000040403800702c02144094451120f031544250703d841004520350910110034039001e85601e054031640c2e100340d1145141030740c0300320340c117020202c1100000c1d90b145c45030600700d029030744a502182210b5040c200043d00c4c180900516500441c079140c420400b0a8840d048100225665104040e4613100c0a4415007684100c08080716040710100b270005042c0300c402e000000b1912601030380b800c0c041d4000b00c042c0d800c0c031401c9007039801a0300034420f00780c02410700d9200c80d01c3c09201c0c0c14940c40349592014845420541940282c130240d602099000c581d08610558075032011041b03000714034003014442e02c2865400360b0203414800161218108040014950417545800c41300c801c240c0049100710715903644440700340400c8810301d041210051584d401401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 870838453 1250 870837203 870837229
    0x1e010e041a0105100c051219120b0f13150602071d01060e061308010504030e090906061531030516080705101214070f14040501031806060605040311 65
    0x900920251031030811034207003003051010364660184402c0c0c1c0c030710000114000c0c00c0b802000c0f232002c00c0410200720043c2220403004800c5c26090b003854440001c503a40d8890350303019242c044805640918050310400001e210403c00d60706601c80c003d90120b180f603000a00c26003220310110700900c0d0b10318034904841e4461428490140070a004511841c000e140403009000e00341c28105c0d04d084c20701e55542c10f19003941d4059400f640412402c943c02100f0742011103020364841d20400040c00507044c210086440c0e03100510340040813290100b8001e084004008450400c003038101322035070314400034500d941d940c8881c2e480100c50303501c40c2c004840b4041c00c45024400407201c50714040c10f50146001c00303004e00c44c00c04001060800c51f1103000d4245403403c505c100d80c0b101000c092120310f02c0c03520410103041000c00401d200f06021545104100c0704225800f103c05492080c41d0105130f05c00b000d503102d1401002544000c141030b0034501c0108606034840050401c0306e015000142c842e60103442400f02c02c80c0110 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 870839703 1250 870838453 870838459
    0x405060301060c05100612060b0102032a0a2a0522020304020d0204150302031b1c02060426010b040c0e010806060d0f09060506030304050a06081e010e041a0105 70
    0xc0010044280955090141103000b04152003002100105c5602180d2290b0003619200b080481048280241c9124460005c0313802c1c00203510700307a0110f1008000408420b0f00c4d44004d600c1004a80030410b0500068580a0380040d4100103041e40c0d03c0007010074000b40e03053b41e8203074040d1003000078640341400048452207d141810500c01401441c1080a940010800da8006080c10442030050b2542d103d50700300500041036201c41c0904620401d41404038018045160010210202459944910b80f89040c0380308815030b100400d844d4070110705140610b5000c02d45505000141d000b4441010a51105005616000300302a00d02e0004102c2142c9070030007481c000130850f15240320103501889509c3c0e0000001485c5604105d0180c03110000e030742c0e0860181c0b4645480740f50f000c04101c5140100c0e41c01c100300f01c001d1803c090402000c5803191040b03104840400442002044880c0c90280d5a903260680700002c403011503841e03001c1016611400e03181180c002035540600780b0740d8402040720070b060398030003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 870840953 1250 870839703 870839707
    0xc20090106081f0b070501110f043c0819210201062301090b0f16080c03040e0403021c0206131e0506040c0b090d02041a09101a040506 59
    0x100890700080b00400070b0b60142448101c1802c0b82c1e4607034075444020211802404d82c3d0b1411442c02c0d41c255508043d8450440030180300d264a0944031380c1c01e8500303840c0074010481c0c45400c8442c009858400ea109212528a00042240c00d44c055041100d003e654009044607400c060340017003071034014103500010309607282c04064070b10a141d9500815051441a10001c1030854940c0c0480400c0103400c1e94030621078000c1c0d0110803031540c222040c1c00060598205140c03c1804518040300d06128207441400c01c0c200d030180840801004105988182c01900102c0c2d80341c2e502d070182c103100d12405a805070054403602107007400455498040c008200d002c0e40c0030740700c0c5031640b01c0350801d503007400d9900301d4000780c181c82c007400440205401c00008500440c002c200908207400c06100c1c1d2000c0750403440300c01c50100050851500c03044608800c083d410740d40040c40020a0b40045003801586c911560300010940501420181a170070600955110030484011090a03a006140070300c964843c00360082c6007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 870842203 1250 870840953 870840959
    0x210021207080307031d030a02070819021002190510060b030403090302011d03030c150c0f09010e0a0305011e0e030403020109050d021513060f1103030a0e1c0c200901 73
    0x502c00c003454201103241008200c0c0c911000c103000d214090641e0400c1d40d940081140c0d50f030315034100100070051010f14003914032000d44960f08007415643c43c20203405200095480074501d4420000c02441c944030304c00385e03502c2e4000d030f14100d44c80340400c0341000b0000d81841c10220321420315070204ca0040360305484030741d00b191950780150b03102c1c1c0019195854455002010303000985051000341b100c0720a0b2405051842c5102646010f5120041c2c6000440c80044c802c941034800c1440c12540300140900b0080101d11a4400183d1114111b4000034000d5081ca51004007032480400707200e00420401d5000c0c0a4650004484c984e00d00840c1b2000c3e0002e64600003c00450420442e031603d05070016001d420310001501e04032016500201d13407014032a08001c8208401c03517010b0303581c6105c10b1083c41c1408120310740760001583c80c0000303811030380929561441450500b900b04111401500c0d800283c1814800b650400760110b00d1040b019194490f0440d5000d90b90603801c00800c1400c0e40040c883c14640e42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 870843453 1250 870842203 870842213
    0x90605090405040c2c07020a12050f07020a0806160305060319080d0504030f0e01050f250213020a12140103380420090a110d05130210021207 62
    0x24000c1d109403481d030313a035403408100452040b9544001411010f00348000c2ca242994801070300c8030041c418400c5400c407100ca40000b4604030090a03c8404030b207072083c0c03201c510700d140380c11612440900950101d80313600c1c009468800800c80b141301d040402041186540c24881c20b40c20381c0c0040740c1d020b41c96000b4040c0140080007010b200700100b805609414244095660171900311501681c054001c0f95201d100d09030769031b900000c13202d6103403400c0ca0002e0800129070080c103024051071541c80300e03008411a000e11a0200c20313068008203900205880032004071900003a0007075000110f1200000e0301040d5604010016000c0c41c50709500e088810007182c1c0c6140c464a1294050809200101c0d00c4590780d214000c070700e194a12400c80320055010780c1414a4a000703031000800308500500d04038000013032402e50b5a9508041d9011103580340210f00c403411f110100c9100c0c4144e41618410600e010248215992400d01404040348240d494030300c2840407242c10baa98252031a80d1040542e810040c0c580064 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 870844703 1250 870843453 870843461
    0x608130510110f04170f0a030e011b05070303080115030605030304120206120a050708330118091a0915040b0d06020c0a02030712020102120c151501080105010906050904 74
    0x800b402c0c074400c1c10b14000080d40501e541c03181d409010001d4450701e110352480c00a010030724200781700c0d6000708003110b40365902604403901e802c9058184102c03003d01c0f034000300c00808208040b6a0040586018035143e180180440078203001703610f15a40c280320061000c1d4040c0c850041036540c010002e5041c07a14003030410321211045030080383c01080601899920807010000035004004c81c01300410180f41c5910024500d0b40020f00b100c58884004424180c03001c0c0703080c00c03c1003200d4540b404252360440c98005890074a201d0350592000741440000041034106036100241141c50b411050700f200040700104142e40605036000b1902c0c20540100000c0b500d050352040e440d040014180803044945074942e041243c010001031030554108000c3e0304214501480481d001c0d051500300000398804d02d8000035035440c0800c400c5000110000790001c503202040148141405020894058500d40301c0c60300d0311216160b59029020440b0600045007940c05400141e00b6035000d56901c1d802c040c3d94200f04800340c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 870845953 1250 870844703 870844721
    0x306210b072607140a030209040b011407020f0f0d0b150a03210c14030d06050901061d0a030204110403170a12021b06070323010b07020909070e100608130510 69
    0x44402000640340c0200d00e04041d05c0d14034817586005890704201030922050320701520010381000008010f50aa502284d03062301c406603010b03115204074985103004140e0070038683d40d5050340f100d103151380402001086031146209041c024595002203900d02d00f030120094250000030804005105518020700351030400c000f0380c3c045032810a015103441c1c3c88584241d05007a1100001c0d410020f803101701c1c0900ca004403c02000103540481f1198540503005142c0c424202a108200c82c180f08203180b503036140b800c01e80141d0740050080119010303003078140b079165000d880121881c42140d08405001c6241c40151f401d020181e8540b1611a860300000300000e51001040700505a0024640c0102d21420800e4901c1000c282c2c400060100d07500144880c10400025000740c0b4105e00302c011302c543c8048105940820340d050700d0102d8151038010741e25050900680290340840b00800400540055030620074003102c115454008460700c68018030704101032150000f41141c0d000c105d40714800d03103040c2c0c841405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 870847203 1250 870845953 870845957
    0x90709030218070f11100213031403070b0c090306071215090501090b030703050c0111120f0d1a030a120201020f1602010201060e250306210b072607 65
    0x20544a50005064074580e1044442ca0004001003040e855001801c012003003403d4201240e01250101c0041d83da1400c1d90b015102480d004280c070f6001725000c2c0e80600c06141d004500702c1407c00d10180041d929040004140c40c0820640041000d08850108072803006c48058050b226959441d501503456a018140107000c16a0341d0f036041c0840941c00c0c0c0c0c0c00000d4a00340c440440c81d549001180c90582d07031070200a500c2a0072110707041000801c001074021440000f820a89100300940c3c0035641026084403840003010710000700798404074002030043c07000c1c020a0b0010000c44082c0320903001c03000d034140710380c5415a000708050804108205c0300040000300701d1002500d0184141401041500005c0754080c0c0c0b500e98952003402c40da02070054102402e500c0820306142d10b0702c0040103000c0340c200600250b102c2007000d00885614403c1c0c02a401800c1c0910319025030ba6000c12100b21002071018056036441c11b0400856603051280c0301000e54040d0740880401c2e0b0040403200c004054178003404401c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 870848453 1250 870847203 870847217
    0x70801140906180406051b0423120706090e0f090a03030f06080a050303060306070806011d130c08180613020609030a02031c03051506042d08010905010e0102180907 72
    0x1060f00c81118203100703c0c0704020116482c2845200407410300c281e190035111b0450b06200c14800d101d094090114100d40500046207507411a03004204007000b80025456180550361010903001d80210004d001c035001c0ca0200101030b9208410f00451a0094514410f80d4110351a9940030a110f50043d107902e11209000180075070390b03801d10750703e800120340707003143e9540001c01007086918062040c0d99100040703051402e80c82c81c25200080c2100303154044102044400d01c0c018138103445401e5070005da1798011004100c40503039410054050340040b16410600c01452100da456000080b0383c1ba800313840000504285404a54200001070f00802c07c010727090b1081d6500308015903810410b074940518000414049528606402825200c0050962001d90b089a00c000c0c4251901003c94003100e100e6150000e10803c24400d200040c20446c0d20b401905280c0c1801007214003043d0b00001150344a50000c0003140d05849509090707000718030b90024441501d00102d0703001c0c00c007034507855804815450485 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 870849703 1250 870848453 870848479
    0x5160602211602100905070302060a020102070501020412210f050c0f0303070f32030403020f0f1006090501140d0804080f060103020a21081303051c08070801140906 72
    0x2207584035048902003100d900d940c014480c41c64060224651842001c44103003c0c200c419180e8695410305488000d0082d50001041c2c0450380c400c0d41a28031031381e81301000750350300c968586400b50088000042500e6086036488542034449d4180e41070702d40d40c0c644d81c9620500004009054485030410302d800c20043c000c60700c0c0651080d005200031440364a01c1e072280c01c107800289070010002c50541d840c00c400328119080d080100fa0000700310310001840701c800749549940300d2800702d0614854003800042e52040b113810b00041039000c21205641c032403510080014a40c0d82c5011000d4400c01e00c20310f4060700444a600c0302c181490100715107200d0066140900d85a580c1c00c036540707408012025841507030030000050046150540c9004010001460a9240b88500a5544001906007800200f010078001244588694808d410200664110003a100c8105138000c0002102c01d00241420000714903100091510340170b00100750507540d40e005c4280c0401880030501007a08006001513034800440c0c024a = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 870850953 1250 870849703 870849757
    0x902030601180e03030907050d080d0e0a020123030a111210050a0e150f0f060d0204150207062703020904080c0c041802190e01031a010605160602 64
    0x1600808840c2d040d10207072014042000300f00c480301d0b030514046820400c18015040000900d480075501d007194009049189443c0681082c031640030801034043c100780041c40b1401e800300c1c030411258000c3c1c031103140b060138201000c0c881c4841400000300c00c800034008a16451075580c0404d082c00340d44031400b45440c80300c040c40030490030202c0e880c1104080ca51001c0c4110f05203108014000c00c045800d03800542401800d140403511420340c130501582c0320190b155841d81e1039140701424100b01405081e95080d20f10f034800c02a500a00402090303103001000d501c0064800241c900807901c1c590b8454805c05600e122408a209500100d02050100003001201580d181900c40b4011407040c500c0c2950741000c101e545040420b60414103201c0e0707140040d034030014011405200d01641e41150b410107403440d41c44a02e6514442a0030018072240f0100002c400c10884070201041d03440070300c0b40207c00d40c3e601e0340100d0780d601c5500780d03d00c04032201c0c200c3c010001c1c0054001d404c4450b5516440b2245140707242403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 870852203 1250 870850953 870850963
    0x90b0304081312030e0a050d02060706060e010602010b040e0f0a12030e030d0912180909020103020f0310051504030c090c12090b060a1a2a0d020d0e01030e1002030a090203 75
    0x480c5407269124a120004c00d900005d07540c15200c0240c51050b0076600d4440080c0500c0c0000101a014031000100c100030406a40e005002030074100004011958441e030000303008007803454403d8081c519191302020030420000e01054001c01c80001001c0c1c288050742d6201c0000e020616802c207140e02e4031078820700004203201030a441511b5520000d450403107401c00404041184a10b8000d10030160b2030f010040c00301c4400e8038203441d280c0d40e010a02c1c02c91f51004070004c1c4a031a1504150040100c01d0121005080c80703c0d00840d0003c071441c0b081441c1c8515404a58812840024000d03034505200300300f64861134000c109520381906120280c000810140800c0d00d0029a003164021162003c02655140c402c0c1da0802501070303040512550000c5e45142211807103820740d0991600030f061801c15000e001070500301c03c040100c405039840e0403140381c4003070760303503060b40c0c0c0c842011480c414902d921070b51103842403001c580c002000910084400c0e00d0944000e40c000b6200c0d640e40354842c000036016841c1082 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 870853453 1250 870852203 870852209
    0xb1b010608032a1c090302031b0f01110c1c08030403031e0606050f030606040b0408030d06050f010e0906030c0d0305031807050d030318060c0e0111030a090b03040813 73
    0x1441e6110380300c0441e51854200901c0c2e03c1c0000a03d10b0603000803010008990b074402140b03c04642c00e0416501003a41c0c22000c07a0b04c000d40c94402c09107000c0000020040c1c88180c40c02c182da15242401c40d40006441c480aa0a98100150303c0410710100a01d08602d4040c06148044100700c48210541c4900683c0da0013280c0940c0441d465000542d00c14540c8035803060b5900d5810b170300b003059034103060009040b031007140c0c10000c0121022010071084d41d100e004660080640c03090b0280d8031035840c0300c042e4403a084075070a40201c5107401130001d002d04081c808262100d405a5851840039041410003800072000b0700031030341602c00d40f9001005911000144450b0383e00a13281e458903454103418031100200f4111183c00c2c60707000354070204140d8a407400d10484995140c1004540034440c1c08800c000d100c03280d440541f90508140d503a074002d60700300c800707006192000c1c0d0b10308424038824010141e880c400c0c0240c0b03200055000108100c24503d400c0616080f40c1b20300805440d180300e010041103a8401e41e0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 870854703 1250 870853453 870853469
    0x2a0f0a0b1308060601051e090603090d1103030103020f09070908030f09090117032b0f0b0913080a050f0c01060617090106080304150c060e0706030b090f010b1b0106 72
    0x1440c941a01030390701010000c0240000400a6240c85030009240d4000d84202403581ca111107080c50000c2044010f03541500b8002e801c1c0d0b070710b0340360510050b651640021501e07000f18428500c212009900401164180da0b0081c088caa0740403c0300052044110000f408081007001030311011603115400e00050180790007140031143c03030300322201c2041900c000c103074015035804107511000e40d900c0c40e0100030f80706d42207252a40115010130640030280134070064100000c0b00d51811002d02c0c940e128a41c030003d2240400d0f24141215581c2541c2c1c1c490401c060b00c0e0213884202c052110840c0507200d00018914000190308840c20030109105a60070b5907819045503000c41d4641003100c04e56610b02c0542c1c0d82c0403000b0802444890b24010b030310743d206e118038054001c8020005e4201c50040d4041c04800c2d99040c2d0055042001085122405440d03011601407040002e0070480160300c1868040c05003030042e00d51440c9940036901e04100c085003540100d18031400322505054030341c40c6100038451500100341c48 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 870855953 1250 870854703 870854707
    0x50109060501020613020f120619050c0313020f0d0b190c17010501141605011a030a080f0a03150803070b070813020f0a0f1e06022a0f0a0b 61
    0x1209441512096003205045500c15810442000010351110440f40d805882401c401d8400e0408210683d000d800854000d10400040c401007401c050390100304003158400030400c5e52076202e0060150310040d00d0012004241103000d02c00f500e001d15254103250340041840121078225542d440111800f2601010600800c104407104a002e40c001c0440c0180c07549011501c0ea4070b100c100c49074105040c02420304000c000420304c6012001d4400316200d15070090184048030a980c60b0050103445d03a18400c4059945003501d20865050010340141e02d542e001d10718600707190f41c0c040340c50403540182c4000c8040640702c0b05480d038020706000c00c44002d48242406599111101c2c20a90074504002d4507503c200501c0f1010402c8076001044807108441c1c0c122aa906041105000035071082a240c100c028000100c0e003002840c54000000660158011805181c00c581c0c2e5010a07600d80caa000b42c4200c00001c01c54005c0c5941e9800c011048407420010143c0318843c030180c000c2000284541c200c1c502030742c40 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 870857203 1250 870855953 870855959
    0xe0106080a080c160b030c0d0902091602150c12060a150c05010c0c020a17011e1e020a0207060503090f10020306040e070609090b1318021e1525060501 66
    0x420300041030b204e0041c400e12a5002c4c03408a10792604d1100a046000c0080b01050010380158150400c20046400404641e400e050035400001880310464501016102d03210085218528020340c243c450040b1526180c101042d005846248400040980703034082980c03c2d010441e421000070000b241222913803a100304207150b00c1e02c0f0b421104680240d505006079105084016540c0d8030074002600c40141c420764200c3c4628500e50701415060501c01c1c1c010401c0c484c2d804211055612042d001094890000e60400c03040700d80c0002c91181410010050700040c60600020340210015504520014101c5084603009103005043c01841900702c1140303a000000d02601d480c140c00760040b4500048090300c011450030002600c0b10080d0701c50741112a03141ca9240c0d503555036130343c80c241002c0d04200040c0003000d903441d500707a10214a44d01c103d110b184030b94819441d1540890303d00007003e8020340182680700c00c40320300441c0e90300300c0026480c8500c404030a0188949140680e020060b100f44000300b61941 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 870858453 1250 870857203 870857227
    0x21612110d0813021c0b0c03160e0306162309010e100f0f2c040524010509040905030d0603030e12060a09050c030607080702060121060e0106080a08 65
    0x6a40d015a608012100081c0b04824120300d8003d4000c50b0f040300c1c0c440f6011109006413401c0d034001d54016100801e0b039800c2000740c42c00d02004500c5540d51070303880301ca950b0700c0c0b68050301c8160b2160b0748503405134001c3c00091040d17940c802c41d10113100354070709000c8484000c41003c100d12154200e0350f413401c0c02c008610104c4958200c58103100c2c1d40030846170080b210100c41070003042494066492820000c490311031822080c02a00007250488600c07110f14094000641c1c800c0102c654400014020351908000840b8805601c4020042181003e015407440000c000110b0b205c2d0031009000398002e80e0b691040c00058000c00007480c03215042c01c000710b006031171410b01800c850941c560b218041c85001c1d580f006000300105031260b004101c01c0e0005104606401e0840c64219840801c0e90540302d050300b4040e105030401c040a00c02c001c29402ca520980c1c90318008508078184481043c1089003121441c000500b0a400010400103240000100e2a40e9207416610340414818107858244002401041d469 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 870859703 1250 870858453 870858463
    0x1c0206010e190f183206010909030e040e011a0a140402030a0f050903070b01051f123209070e070c0302010b040f0b040b0103090209070302161211 64
    0x31a003240102440c00240300842c0404800810503000c0d501e4203401405003803540464800f80785213110b501400828642070708501c150b18000c02c800c41c1490011980211100d065903030f03048000c400b4080591800e1610000740c0001030003101800785180b2025150789540c4030f84125042d41030004145842d0001e0200090b08201104600402500c0700c00e00c06054072101402d01c40d0360139500180e4036a01c0b000d480004064100300c101e00d480c2404140100103030000041c00c49a401059031618590707a030010405003088000d82c0031148060b6244482805010320000d400c4012420408520003419119440100b2035094140c58070800b80e101510b03c42c0c1d00460701c00c0e440741c589030043c00f103113040c00b80850310700500401200400501107009010540700f908038400c0008046c20a1001501c80c0d00050003a041c1c403190039024501d40b0701c822200758400c0c000c54030601d4010303058801a49a800040380a03501241c2c00302140c9904860040000300501489102d0303a546030345042d42201c2015a050500d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 870860953 1250 870859703 870859709
    0xe040510240503061203070605090705120102070b010312180807080d08010e0412020a05071211010e0d0b100e04110406080a030906030207060b040e0c040516090b18031c020601 77
    0x90070400c541095699008022240c00c460100d52144942c010380b20482d24610030248010030007800c201c1480350f00003000940700c0942c0e4042310a5851102d0355042103080380142280649410341101c010070101e04140c00c120318001c21741c40e00e000c4146c800e6441c1d04152410b940050703a079600c006000c01c001c00052114400f07014042c902081a5403402d01c1c801551580070308040c0401e0200c034580c2409900800c5080440d40d4070070155041183d03580f40900c8a120300c1c0100f0f544001107403004918540c07080d002035102c50760040202c40d10401544800c2c080400040490383d451088c09000703c0c0031101c070001584030b01c0c8119140341c0501d2682082c0010395865a00004c45c076407002008500007500a03c40c813041e18200d1a00503200c880768245a00580b50301022290001d1404140c45d10041c0c01080061103400107072414442500d6509000406c88442c103000c0b80041d02c203003001c1c000b180c03142008007032400c61188580d02d01c10000b000682410440c800c026000703c0c0b079454000174560180b28075801 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 870862203 1250 870860953 870860999
    0xb0a0b09060f04091b1e06210609061806050603040203150a020721020d050406120e0c090c0408010b0a0617090a240b0609011e0e040510 60
    0x45505160110302031140240210388100d01102040c0203d03100e0b03070300110007103402c40f2025031203000b0f40c9a09805821580140602441a88002615a288041c5410481e034255461b00340c809603a107484045008508104420503854840c000f0790811203028020145c0301c24184899400540c3c508602110610750015000c2d400600800002d03035004241c01a00c0c816200c3d5480080d654181d404000b031150882c01003c1242804c9404100700c8000300460f04c00b070b0b60b0b408403000d9410700c0f00292194016481140005002c10521005000d01030704209140c0b0076a40484800301541400181000c008694000001001050030406410240103030071100302c0680d058420282004001040421241e008200100c2034038040748211008008860103150452080d002c8201c008c1e40603044900c0006403501500c0c20001c020550f45060012240e0f00320058442140c15a01e8100b8a00a14400244401845201c03c000c80454485010f10f61141188500000c2c0541c2050900c4041c11102410414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 870863309 1106 870862203 870862211
    0x7140a030c03080f160c02030106031a041a010f050d080c06070e01110f0303131a010603020406140a140c030403080711010e030a0b011404020403060c0c0b0a 69
    0x1407958840c2c2d0781c41280e0707207801860a41c2e1040c01e5990f0303449421028041598070380241042e01c1c0861000d070001c00d04c15a26152501d00c00200710601c041c1400080400040100900389603001080c3d58024078144d505010701100c03d03040b0f600580740170352581c00346541030000500030384009450308400ca80e804c0c0341440008103114486070966011a64544110340701351408505c1241c441846402182190340300c5a038940c421454200075203a0141401c000e100004550b04054080d0505450140e5914640000180f909401d4400300f40c40320000c3c03105540c0380798091940900c01040030308464940d490090300380d0451069910041406100259903402c00c141e90782a0852603800340c8a0b00503500245040c19100c3c0c0745402d00900c02c981040040c001c115800f0611004142d01800041c241601c3c0d6890b0000c864610a400d404202c161461800b00306842003540e47c09440484280 = true := by decide +kernel

theorem cover : BRFrame.Cov 870683453 870863309 := by
  have h0 := BRFrame.cov_init 870683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 870683453 ≤ n) (h2 : n < 870863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
