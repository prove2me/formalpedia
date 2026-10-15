-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5015
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:27:55.907874+00:00
-- url     : https://prove2.me/submissions/5ecfad13-73fa-4436-9703-816cf783cac4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 901798561 ≤ n < 901978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 901799811 1250 901798561 901798571
    0x2180403052b05060d150504080f0703080a0f1b0f020703060203090d0e040b0a03020415030609030804030314010617070e0a0b1804060e0402100c02040213090c0801050306010b09060c0d030905060109 87
    0x1207107040103141b1060f0b805400229240c1d503030389447e00f036a0285041b50140074401203040f0f8209034001f8642842550b11900c00c001550010f42100103841c1d0f040b01110440140032520b01e0010711840b42c05100c0300450040b9421300707680359201c80417030348101c1d40e103151038200882140d003e65111540303540003d01201c1c02e100030b03145030000580c901e90500c80284280e40e10620126218000000d003001982c10440c100100c100174140a0100101141c04400291a050780300c050014881c4015050310400c0e620b0a004c6410070341d40200d0000b021b4003180a01c4219030100000d81c0c0c2e026040350140081c40042034854414000403c003000080305028803031400c2c10014409210380c94600d41d070240d0111120103203810300c1241034403d5224818007a4229000040078207204004240c44000c845d00d41804200c10400104200c0c0d80810a024a952641001004200c5a4a284080e003d1094014105407070100001d050501c1d140c155003a14012030b071070704001c0701840800e0012900500e820401440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 901801061 1250 901799811 901799813
    0x304060c0f1119030e03070306061a030c0403020108191e0c080906150105040e04080306210c121e01050a0b150f0f0706051e070c02180403052b05060d 66
    0x244400b240c0c6045903201010f0200c01007418480c01100a82220160a0319482901c1f070801401502d00b600030816445852058203400000c2001200c0c894980075059905060441c3d004454442010740000c1340c80c12080004059419540b01700d11036103100050550180407074031000e4041e22240780c0342100741b0a460040084028008c02c0c229805907900034500d00450b004c02c0142c440f4090398000e050001413200c10801000712000065000d01011249900c821071801d035009810b0744c802e06020302c0c50300000c014400a00340102407038140c40001c01514811148480700ca1110202c80175081100e0b919001801000e104500ca255548002500c40619651a8107100c0903a8442c8400c2c4207031f00c4000181d001625904001070382c000740c1d84418244080c2c02c01e54424007401c5007201c5c2c0040070300004000f14504a004d50040500e00d03901400040c0d00d0307440214074030608130300180140c09010003040403004050351110350720402c10f42c3c1003030f00e07400ba070750920100101c640050400d80118840800c0c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 901802311 1250 901801061 901801063
    0xa0e040e070e060607021e0a2402070b040513050c04050d08090f03010b031515090a0b01080609070903080f0906070b09070b120117010b0a0f09051521030c030304060c0f11 75
    0x46102d00307a90440c200b02e607d2180200305003100c0b50380511440040d01007007940761a8031807030030a0089211360807240ba50343c0311400594988039604c191584101e80d0310011740007a8443d00030b50b502c00000c202c0c840c00c0079603400104081c85805901240c4903440000d180d034140c0340100340c003100c400d400d60081244242d0038000c030380d841c4040003107104c015044800003410096891801020b001000d842c1c440281080c0544101030420030000901040d90031002403050b00b4042e075058031600184c1c0d102013080c2c1c0f454540384103a600c10196121506401c200400d4103807106401071070360902c070301103d0410345800e800070340c10311510390403a902c00c4400300a140d2070340318072a4500341510118500a040d100c44803c02a0042030f943c03a180c2c0d084841312800045c50b10501d010503088501528051010350b664654600514081080984c0d018010452400d60480d480e0030b0090036091400071249804880c026841c80c581003114102c446c80d444490079032a0f01e6020188040d47c0549080c105882c56401c1e14103 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 901803561 1250 901802311 901802329
    0xf0e010e04031b02030a03052a0c0f030f1209030d03420b030702010c11070b1c0908280828090506010501110f060c0a0e040e070e06060702 61
    0x1800f04002c461801d00c400781040358040c1c9a540c01000c59042c00c21515000e021900414a51068402004040c8401200c03c81c11408541c64a8001e040084019420015201d2054503c11382500c90118080040135040014400c100000040a0349039081c0800301407400081da108032b420141006000d0302100b25500003c0c011040b802002035500501520412183c594030340c003001800000d00b03000405212a60045014541980c001c0c000280d0102080c0c0d0302c901c0e61071407075425504c500010007158400101901a203800074640c0501088030b010883c2c1901c0c07000c181510300d0100040c1d6180320b05080b880b58010320030281c440c1960340b20641c001501c40803000300200200d000750140c02e400180c40303484c0c0701901c0d80042020002d101013810309a030358001c02d000c1d0f0b80c0459140840700c2c480007000242c0307a40345180302004062980e038000811002e604100548804d1052819a1074555130744c42c025046031414000050030301c0b070b2408500310040c0c40042c2540d07000d13401c20451000584c0750b50040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 901804811 1250 901803561 901803563
    0x3010909050f072909060a030f060f0e040213020f0a051305040c050715021b01200304080f0c0307020d050c01120b0a06031e0212040c0602030f0306010806010c05070602070f0e010e04 80
    0x2507030040c1c509644c2001203520171680500e034081c1c4000350030700b0300a402d50b0140e0001c502c492000c000c920f48626140f4030014040c002d014090308014006001032070045049501802c4003000941000b00140600d040c0740c001c00028004504007103040c0041034a40c41540300104800c4905110341c000c02e40024000e48100c020107405000148200181004075404071010340007502041309102510f4084280240b500401020420b0f80541044164000c9201640c3c0540c3c0c200d0607403450409212040d04403940310091000349400140b1030407001d42d0b140c800143c4201c2c014005017040e001e901000422041c0b082542000b07161500c076a01c005030716042c2c1c810b41030325002d0800046203441001e04c00b21104590641c0311101d80002583d02403820f40318540c501a511a980b041a02900c0c0c0406030703203e004070740a40a03000000d000041d019840341000c0c2e03412003c1030411004039501500c4142c20028640c2240c401750340062001c20118003030a07030f100010b00728801758074540d50410703c0c55243d03030001408c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 901806061 1250 901804811 901804859
    0x7050d02040b04090507090207110f150c010b03071205011803050a0c02040b060d0207120804050c010c0f020d030504140a050a151b0b060103050a0c2001060b03010909050f07 76
    0x50010b003682c4881c0d0003584150382007000c841041ea51500e012000c1d6001d00d10848400ba90b42c40800306504040c10400001440100302d410000c5104080b00401e4016003c80c05841d034885151140685050007224058568400e40c140c1a003040d04003607094990300040480d40d0f6082800000c0800c1d408419142481428584586845890300004010f40030105083d64440030004035240c800046500400046201c5c9400d540603201040007900c00031030403038001d400c503040b903111102035621808000d44803074032942c91006441e041ea0042152595803072021808200001802d20245c174170024190702c1c980b02181c0804215003010041000d05105109490043c002c035545014000c1c014007002c109201e114001100003e01c4c3d04043d01181c1041e111203001c031b032424000c50306902081c09241440103058403003400300c0c3c0c500680b09a17440760482d00b2049655035400040390083d14080154001c0c031000c1c40129812581d824094100600200354102075070022108001c6081c4510300b0000394885c0007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 901807311 1250 901806061 901806071
    0x3031a0d02090901140c09100c08030621032110061d2e080a0207020306180f1015090618020a050d020a0203031911160804030b070f030e07050d0204 65
    0x80308503015090006080d02d12a50101c20007a04560b51400b402041600311007202312440c03150025129024201c0d80906940750400c00074003d820090f6448a07540703182c844408540c0c3c0388440300c5007160001d403100c0100c036000010f1400460040c951064028a100ca0054011440c021010f026286042c42160840c1a480080750007559011003104010310408041010814500b2241401d0b110b00300c20b84011594060201e00680040d10a8031140369024005212545070078064408099490035030214600c514030110342050010f120644282d40c101d00040b503010b903500308810050030a5007040d22883e160010400031030b858040c843c0e10103202120010395132800d43c01c08444034031039a641c0500c01ca0000400b200002d03800802544901c12920228203100050703950720094401d9580312540c900024045d0444003040340340b01c03030034144c41200c250740341070307034035a500d800c0540c084810502081c805a001c840094041c080d00b10104040005840300d10b0600000490601d61410040c5c0519611 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 901808561 1250 901807311 901807321
    0xf0f0c21060b120702160f06271805060306090c150903030a080108010e010603080316051303061d0a051c02031309020301091109030d2a03080403031a0d0209 69
    0x40e4000301c0a0b1204284640c1c0d603040c0341d19480000b61040d603c00d8018401e4039210081545045c3c00c0f401641e01054902c80d04525043c2c040399007507440c022210301d441000002d0450741100c0d180300c1e0010030001a60f042c8054a025000c022644002c0c8458001d800403400c008007000085140e0101c0d00c0f085448030901610f01a10f08124003440c11055094030002030840c0c401900300070320340e04030b5140b0002800341e4140000060700b81c40c0544001441e450052012464103003100b041d49c000222189009410302c40160418401c000050b4015100d055507100c550301c0d070700c84501800e92003102041c010000000c5690310b0658074102e0b9030310088410326140800900d18803d1040300d485ca80e26034048408651108600c0e0000e510a00c90150709524040d0030940400101040d41c0c80c019004001e030122005000060b10340d05000c81c0445e20301101203540c500110388400282d20214000d96034103003146420314028044410080401484005004554025960b901c02034951658140c80390104c588031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 901809811 1250 901808561 901808627
    0x40b030318120f0f060610020a20041112060a1a04030809181017010908030a0c030914010504031b0209040201030c1e052d0f0a05040302090106030f0f0c 67
    0x70441c003c90083c0c000e00074211000203681030040400300c0e40c2c028500241d2209a030307142c988540c000e0240f1010310007028540019486180c041070060400b18890f515080010005c0e405034503010340308c2540c04203100840c10202c0e100009000c00c5050b00201c400c404048654074000d0b4403000b408180e0000f1024402c3e190b11300c410790082c41d1a03080c50300c582405160610046550300074041c408034806032042c01d2010500031101c50a41100707500d071858031207511101c09014640e540c54140340d00c41b1030900008544511240720010781100001d03042c2020710f4014080349048941845808160074900007580d07c0070b504640056090800103200b1403441e10655a502c80081180000016541403000254004006164078000800481c508a140012081d4034148603040501c00e001c090003002d03c401c0f0810018180d460f05803c0003070820341c1e6540000c0c4c540c0000d8200c2d40000380c0390381000d0b449030858001d501c0e01c00203480c414000c88803010710003401e202c1100300d102e18056504420703140020f5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 901811061 1250 901809811 901809823
    0x9121303150c0807020c01091e0b13060e01030c0f031a06040602010b0424060c050111032503110a0c0c0f0e04120f0903021011011a040b03031812 64
    0x107032100d105003025103403480d00c000804010385030401041da62400155000e102159400241c00c0503113560219505103030b00c8950215140c3c6028250700d001c0b010210720511a0b82c00742031035103044a284220541044002485d4401040255043c0f5040c860311340e460b160090a41c0303240c1c44145c50001259042c01c10803840e43c040d542d0000c0d4200702e000030003044241c0e041d002403101c2e00d001d85043c000c0740b00e07460002503003140c0c41400e61742c12406210f09000c1c1a10408115031245e000b44004504480c0d8007594003243d910541d02100c0c0c520040307900308890440300d5600704002c82282001c12800c03030b07a000200070921a9400c0b072010800c101040310b080040c1050600003030152000b00018154848030154001e100c03d07141510030380c003459039106403141b1440807046140002e9a54405240c510b60911500020101d151810301c00f031020b5203503812109104114070007018003043c5045400c1081803104580440300098040c0e00300b04a40c1d00580c0f50452807000c0c8810549480070714094803511142000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 901812311 1250 901811061 901811063
    0x170c070e13020d112407031b1b0302090718060305100e130606050303041404020a0e090907170c0603010302130e371101032703020f06070809121303 65
    0x20f61070110740307018003807816403040610300182d03001c141d551500ea00c0d108040007000000084064100f04a90021703200f4450502031180526000280d07080340da64580e450310201c000741442141914041081d80792254a60f90004444d04041441c8640301d070201d291f405603802001c040c103440d040825001c010a840c3c000c000c050003101480e140c1801710a85035101c02d03160058401c14245100030030140380100448044031031811100c603060387c0d48410700000e508015054002e2114003450408152900f40d030b868824055400038203c210b0402d1012080740c4140f40382840240c2c040065005181c8401c400c83e070549070112061203181c442e0200d0032014200740503240403e03003d116500300d100104034058030050202d5041d0450152000700d480451102c81e03420240c0258a071142c690640d50003940603040f41080c02945004a1035101a001024000c0500480050340a00300e01a84120244600da81011851901c044542401c0744000d660720310b40d410085202c1000a86048150020f50700c80c4011 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 901813561 1250 901812311 901812319
    0x3080615030f040c050d060510080102090307060c0f020a080a17091020070b0409060602030708030a18050303180609060405061605120703091a1b090f09040609170c070e1302 76
    0x1c241c40c47c0100140009035021006040001004070380108180203984400c40040d000f03082036460840e003101c00800d001801e8910405180c04080540c4030600b129028104100042c10076507030034601210143c20a015419455070240a8042c0c580c0e950b9003404600c05041c504052013844400003001da0034481100300d0a1880748900015802d01e444e0040c20442c1d006507000c0018a550700340a0b6200c1c4201c2c4402450a90104009045c280c140d0348601c50000400108030806592a07440c10b06d55441035588880fa0180020340300d81d8008200720090b80244140064059401c1c165500c1d5070310b0324003404010500d5550004d00c100c1c40c0c0715400303641e500b6004410201c03182c145214007500520b181c040c00c2e100c40700711405156015190a400d45d02410303154244100740700304a0400001074104480f4031790700862080210003035540364401d25004500640000602040b01e140503180172040191032002024140b1410a66030808510300c0100d60b101d42007400540d07500c00c010000d01d003400c0002540 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 901814811 1250 901813561 901813579
    0x50f12070b09121b0108070201050f071409120c040b04020403050601091e060b120a0e0601090c0c06020304210c0807021c150e0d050717070f0f06020703080615030f040c05 75
    0x14113000300364880107541080e00d8031480c548034908200d0907500200c1d0b00d158a15100380100c1c01580c80f0b80d09055501321034083c00c030308002c80480010f81c00c0c02c088940d81302561154100000c6440e00e4443c612010700c00320340840c60b141c6075a4070142c03901014490820b0340e40e51070203000391418042c0059040c03452703d110700304080c50301c5070540d04a030741145034403010032920400010148880d074440c0600c140c142d000205207aa01e05448039000d00102920039040041d100d074804002651030000c1d501aa1040c00409150450010803106c044d80d1103040d502003003000c00940c0302045d4054100c0700762540503100761542011052241669190545008000868036011294184501d07440450b580c0400800c5e02c18943d08584125054044c04038040d02088041507000032a000c00760040c82203520580d443c2e0102c19464a07011019541700f030041ea0b241d070b00000c000d8201580071090070703800801110089040c902c0704c6003c00071030100501d81c503404007124011606008008540c00001c1000604803e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 901816061 1250 901814811 901814833
    0x4d090604030f1502030105030a3003051e0c0f030402030109020924010908030a0c170a1101050f040308010e090f010c02030d2304150f060f050f12070b0912 68
    0x50540d800860030390f4070010301066904241a42e0080728121040100240300c0c1c80c0c0141c4440030184000540411802c0044d0030100540c000704103802c4c5141e0f410303240018645400c01c1114001255000d030001947d65140400169020880960740c202e580d00e0301440e1a0745e650710100f0b00601e00118003031b6200d441c0034200507a140d41c40c1d01c03900c010600b40c140f0721044a01d1000543da40400f902480100f50814800007240070300c10500d0711001800b8280b80340b0207640007400c40d00c1341d500040140d40058000315a00b03110041c00d006007500142c1c840000301d990320702601c0040c5120410701030301c4c401d0203480740404d60080d0f0400c0903440c0100918001c100352100e10801a6990740010304e0002054180520809801000c10001d4106400a0300205040d0395030b45e02d42191406018100c0c002c0755541d034414020402c0741c0704941c0585011b00310221080e060a0800100c003990840080c8124451100441c44150104011080764402c680307442d00c401e100e0740080c80903105109504400c0c400c41901034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 901817311 1250 901816061 901816073
    0xe0901180f0201120e03091003020d1803090602070503102a0e0a0806060306040f0219080307060b09042102030f0c06040c0b071a041e064d09060403 65
    0x4511140b00341c07500c92000300078240010965070b03100840b0f0a960401d0105c4c0001d0f080010064807410064600103140040310b14038001102c0d9a14404c9100340d440c1548035040640243d65074028108034001000011f2802000a076a5003031310704038505240c0c540c0d200e030048103048051221804c0c000c60120706100300b542c4005140c90b05100c0a14852050340000007190400130803090700400010b03015200c40c4d0740341d403130342d141581403503400326004000c4444880008098481040150014074041d41d42c9404505011066a07003d1022501c10540c0000380400241080c00140400e20041d034054007840083c0d0043c2e0540c020070300040400203000542074414440400e44904c60b61041c01005007071a103540400c003403805920310061410868251403022210b0742824283d0203841547c0144291101400c10018072824160445070152105c82c00313405500b5070103800c08400995025043c046030751802a4105504134000342110700000c030847e20380080b0000464401e80b20182109076200c2d5207140003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 901818561 1250 901817311 901817333
    0x6020a0201270807111c06050601030506100507030c08090d0302160602210c120d050f06220519060e100902130b180301150f0b040305070e090118 64
    0x100c2d074581006100d4519481a9600001842d0f006401d03a824418036a8803008000384201240da4403100c01c0d00310003512031026043e174044510605012465041400015080d01e10160071280314602500e07801d010b40740e008050b600e000b900b500d44040700c0001d0742010003ea00c10003a0407500512050800803c1c1600012044112440c45002c142d2041d40d510003240c81c0c0110013840b10b8883d14203031114402c801d01c50007800e0449246070503212040880d140600c03995001450240b911074445c000c001c15000c0503809154401c40680c0c0d21280010454125004641e1507507544c0f005554038400314401050f626464021920000c40401a940d10382d80c4c60b2030562422079041203050030500012030405058000d40d0760035480700300c80d00c0c3c0f4103090142038142c41e000712800c0312410040003090929642d00340114103850301c002400f058494142441915850501d0b006607850b48010042040060f10010382c10381160000e070210050b075143d4000f810301400d4200c202100c01d0750b07006a070905200e514409 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 901819811 1250 901818561 901818581
    0x911040e0906010e01030f080c1603060f1e0e0c03030c010e0607030b0f04050402030102130f060e01110a0b06131a01030b03150604240b03040317010f03080f040306020a0201 76
    0x144910303540d80c5008080e5600d200340180184001a03400410020355144905401e0a204600090800000c81c42a03071500350039880305645651a41030400500c80d140c41900d698004034541800340c10051300d4089a110340305410301f41940d50300c0907990419041440000359001c3c0040549964610384c149007400303401980c1c21402140545400f0130703c032034003070b1054a13950700001c0d048880b00410f0208100043c00000c5c810f0360195001c000c4004041c00c2c2c891414060006224a2911541051001085c00d000b032040103042c0070103048005100c98000590820540d880704100406568030800b24455001e0102500d6202e4201119941807400f205440302d507900003030780d04000d009c18038020580c1c0c420302441d4036107211803c2c1001ca6442c0c10035401c070100383c0f00c440c00300c104041284400341c01001e0361b9a1102e24151b001000340010190720840c0700281052a9101e40940d50415100c00c2c240255480001c00641000541416207003803d405e45008541101c011916100350b1507029028142400c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 901821061 1250 901819811 901819829
    0x6130501031a180601050108361011090d21020304082418010b0a060e0a0b07050616020c120c0a0b0a050d110706020a021b0301020f070b060a091104 65
    0x1000031640180900080d14803010240242400d1b46040010349448501814108590002c101d40502d82c1301c548556050464000350310802d00003d5160482c148941000d4240501d41880001074a0b14121001da66030440201d03031443c5100d520b4640220089802d003034410100c0c82c9000200d4110b03401001070011101d001050740e03d801d41420003049080d05080b40944825201d4011030304a403845408259039100311400020000c000c00c00103881000340340d00410001c1c0740304100c0d00240c01c040315510300410340780e41804e003030401035a2159207540000b00f0a1390b1030032030320918100707080c802c0004002e07201c4040c291400d008070340c198007911000f043d040580500c445980010340c0c0708048040f6501d441343c0d81e13502824401800f00340c501410007240441000e00302848000080f0700d4a20080001003010340040a056a604681004503d40d48080a2080c2d01c1848500303d00516041115075259020341004a0f55031403400140010090f41c00000050b4640002a805888038800600a41c0c400c84 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 901822311 1250 901821061 901821113
    0x1d0106030f200603070c020a35070605070f0c120b0601030b010c0308071d09010b090a1409010501030c12090501021b210c030c030f1c0b01080f0613050103 68
    0x70242e18191007204603400d42200080000400b864819926075044a1000309030300c00065803071845142e4007440d811085038a02c22a2032240c01c0d100c180e1801d90b2108120006000c3c0e903890f080000d4141d0050f070202401c0034000440740e07010804503203480c2001e095092100e603510680313824142e00543c003c480103404a8a0100207200541c01241191112035140d80c41103007580e03506208030364007403440079a40080c2030b45e00e01c8004039903114446a4043c1c010103a02644581e0010200541c02420782c0c8440910901c0c400280e4454507000a2141550001c0c05c000c03070403c2000500300c415118003008620b00d2803820040604114041d001007a10038440c074074550039820506030064440010318203001040c180c0c00000e51040c40b07804090800c1c2188401583d080c00c1228402d14210340c01900300c010741d100d0004500707030030400c400864241c080c0c003d4402c1040c0c001100c0040c0c41c0c0880600000c9400c21410000364090780c0d01e4048062149a1040501c282c1d41d4a1074072408048a406075484040498 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 901823561 1250 901822311 901822343
    0x17040609150f020403030921060b1206041a0f100b0a200d0207060905090a0c1404060314014103030a050d0f0203070c031805090c0702032505041d0106030f 68
    0x526400402c01c4000e900702e45001022703070300e060007052412841e98000340b1610a070a001501444968407660060f00b0b880f0708001d400300619400d4900030700340c9983e40d03454402e011250400360341a04c262146080f4155549400c81c5081e03804200540070881d81070b4500d101c10800c0780700400c0480520120b502102c412980350070060322112a940141600200c080d80014150540761b00304120030300391400d040c030105000c82d8011003036030b11503003150f40031035107503d100c0f5074206031810b10600500ac1c080c800c0d5050003498030324510742e4a4441c08185c10307000c0d201c50038685601044220202c440700034100c95548a0040d009882c94000c1614115400c1c43c108058410003494021a88030b82a07a03950800300340030686d41a01c80810000c5101e40700d80101401003020b489481c3d0603406000e4900e101da458410900c1010315089000b48031002c030400c482c2c070101c11240c2c007001d054165001140d000c0b5000790118a403180300070040c1c0e0701c1505582041d0780003041c8401100c400e01e046010f80301c559000000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 901824811 1250 901823561 901823579
    0xa0b0901060e07030f27020d0206120c0a120908070f02010215071d04060602030304020d0602070803010609260d2712051515120102090d051c17040609150f0204030309 73
    0x2100c004070104102c0c0040e120010f15001c1c523a85c02e000c0c401001c10303081c001c04000800061204580c003407400c0d40e00003140901c3d142c2004054030000300c010014080d5480d9a61110041e002e00c41c40104101040c4c0803400443e8000e0000d42d60080c4000d560a102d40f6050038010064050510300021564800f07044800740d040502907681a504940c00451943e2190303070a12031124012103042c0c6a271982408640c0000e2190b0b4001c2d0300030005a59840c940504150324100c0d20b10031054050b0240301c03d46110402d00320003085c0000030700700900700030906a86030b80004085402100c0304890205d0b4104000c2001c02104084801d042c0c060001c880d08544d10030f501441d09201503035045e40b01404e9603c180203502c0c04405054038441e4110015046c2948003021840300b8040302c0046500d03400503401a4403249003140d2403106124149050385451004e0443e08500c51805040601080e480d4680b42084c03001680c240c00814116100800c50030034003c2d1355000941050000b10006014620001007410b1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 901826061 1250 901824811 901824851
    0x40b1f0302090c1c0603050703330c0c0f0b041403030103030e100504150201050403110102040b030a1112070e010201050a0e060a2403030c110a06020a0b0901060e07030f 74
    0x680a0290b1903039440314100d500c1c2036009180f034060a03071803a803400d0020000900620008500c0355009100150840c509003000d0844018114044003440e070501d1061071000c1855000e0500e4a0000181284100f0080741c5030011005c000d4607070701010700b00324108064030600d83c1c0f0960143e038a003481d045815464903168403081c480540082ca032240c2041d06480c0800100d01c00942c141885880c1980d55903401940c240300e40c0240d800350355128104010f00d03420a0b4404510306540e00214909420700c49a208280805000904132580d80d01640400141d00310403903003441a403c074147e040d1b142000009101903001c0f00c41c14019401c05011841c4081c00b805000c403840d00060241a15946062422009290308014124080a42024640188501402c000c01307140250f841d68441c019600f030281f90303d92805862406000115400c101082e40401c401e110254001200c103000d0700d440c100140034010a40106010007030303031000e108526802d07610886203d078900b50184016280a980c00210b04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 901827311 1250 901826061 901826063
    0xf0409050a090b1501020319020d0801081207170c1c0314011d042103150b031614040e16020c0f06030a0906110a05092b08031905040b1f03 61
    0x115504012401d6194080f81c1385410400602c100c03420310802c00700282107103185003c0c0c80d01580085a9841a43d81c2c44240c10340984100401441ca11202600020780c41c420840098000c4040b00480d40d0304500d1007085a00b802034540446907001c83c1402c03405624105a400c03003000ca840c240350058614003402030141200c0340c0840c0e110544070700703c3c442c1583d0f05008000316882d0502c00014400c0b0300105030b030358202e1030082d907001071441c454009285282140390842d401c41c3c80103004110b00c4540c0c40150000d8440c503440c091070036080c1800e64500e103004a0300314040c3d510b803410800594080c0d20f8400d807443c1c00c955084034014030800041c801c99504480340d031604808104002030782c401c4035400442e18107100d0440019050001e201e480c60a41061400c4000034000140003001858048110111581c0403400800c41d00316030030003454044968100180061004000500d10054460075021b10400345042400b280c50700d4a8200a0700c0e504403081001480c149040004103006409a01c0c00c3c1d03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 901828561 1250 901827311 901827323
    0xf060915030216022112030f0c091503011409010905090a020108090a050703050c01020607050309030316030e0d0305090d05040305190c0f0b07050c041a040e01110f0409050a09 77
    0x1003800510110080d500100703024003445030301c1100000503141c0070706901c204103400e40d03114070f82c00440c0c450701c1c145007007200519082070b4107209004038964407060054001a2000500b9030303451403034000c07840550a001201000c4840800000b0b4128080601b00a08040031240c5403242c0c0e807252203090484034241d0f106042548820304900040d40101f0032190000c0319401118005406940d071545841d1701f68200f1941c2e504150381d079600d030756010003040b90800400d0606a0451404400c400c3d070700d000081c04000d0411082145100060182c0c0c48680131802c1c250a913040700074641e4000c2c1c080d103c10780300c1d0a12481000e1150814030b220380141c40c1501e50110181078041444c0c03010040c00030344414140d0f100c4d500b00000040900c002502003000f0b2a420ac20281c4491043c100141414654440745010340e003400c0380809401103d4400c1c0d094154100d40c005000c200042c3c14500402d110001c9000c14507001991840810506016004440b082c040520595840d80107540075500055801410303 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 901829811 1250 901828561 901828589
    0x10c0804290f16020a0906030f02030c030309010c0314070c14030c060306010c02060c030c012a020a080714100c091a0906090603041e030c1b0807090f060f0f0f0609 72
    0x1860269514204481d40000c00c50500300da10341e101c6c2c0088903401d5204456154030038100c2c0045080a10283d40402c008801039800c040080300043d1129401c46d600504000e07000c0303d010300d003114980a0f02d41268001918842d05a22000078400c110700085000d8804d200d4404103001c0c51400a00301e0384280c0040c2e6620040c0c90160b403c1c0b01142e0441400c41d80540414003c92000040920610350380c11860100402000e01b0081401114081c10344a202190031203204040030030800021034824039408004001d1021301000f06900f06896821a1603a050a0040322140d407980509060166070005900242820702a483c03c0304520800f10f0080e000003050001480c10300d8140050359100e03001d495455070300f50381d1108070640340c20820310441c040764000c1c1460701844070b1910700703e0700030310503440c0141070b9030502c0300e026035900d0688100d1866a898408a111a00107034001a00801ca810780d110305043e00c03001642d202c0c0519014540404110650004203544200d00c15000c4407504030f0b80c2c0036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 901831061 1250 901829811 901829827
    0x9031a0403051b1e03090108010806090a030c02030a020414240a12021f08040b0a05190e010b03070b0414100c0f0804051309030f022a010c0804290f 65
    0x4401d550303c91815581c01006400318051080b1441c00400700000740145584c0d9910100140c417180040e00f00c44040d80c451300070040c801c0c030700007032020046805080c03052411a0510000c1c1c644001040300075081800d00f00c40b400507101c07242015000341016084800c80c2d080070542038010b01902202c0b2135221051103030070031124412923151070160380098003030401103840300c0808251301400581d0310b000030009001c000c00d106c40e840450b900030342c0040e001c1c000390814001c2c1c103410b125099218485c03140c2c1d440d100340c1d4085007540183c500a00140030b8500c0b0b00e0351030144014681180c8141b41c8103d00b07a082d02d01c01741ca412007200d007000c041c2c3c0e11100f074012285d0f1142c194803403039101704a411413401c0102007078640d101400864201216807011070301030a00e1600600b510707202001a002d550094551130700c944492003101074181c24844616450f0481c010040f00c800c1201d540c0546841400103004c601c01d4559200c901400200c910120491401c5c9481c1c424144a2100f540000c0401881000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 901832311 1250 901831061 901831087
    0x1031202150610110316050c010306060507021912240506090403031a0604030501020a020115121b0b03070f020c0a0b0706022b0209031002030103080a050c030f030709031a040305 78
    0xd08843d84a1a00c112651090030040746158030200b4521030101c50501d6000810808000300348140c2401e00e000c0c07000610309440330301580a5000001c1c450444440c0510045008814007801444800d8a84081c1402802c0c501c050340300742550f8401d004500003580400a000c1d009060048201030880341a076505c54404600401c1c0f50030510301c2c0b000b90b01d1000c1c84540d0300c045c05040a0f5014030001661080610406401c507641e4103100420182c1c01c100801050303c0c0812001d00e12a0003030003200c01c465226094002d08182134202103000e4402001380001d4550045401500744099022690301d00d1101e03042013000c00d01803049420103001041484002072217500500402038943c8803551000e01c400d908422071110118846420984c01f14615016141c20801104c0130700000604502e907505646039800ca5105010510042c0040004c894141040030002c981c5202c54000c407003512401c0082004080e600c2610090f511241408c490410f11301d8020311290096606448082c60110402104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 901833561 1250 901832311 901832329
    0x11070201080c07120905030d020610050d080d06031b0b04080c0409061d06070306050d02061905040b13050f032406010c0c080c0118120b2805010312021506 68
    0x41c014100007800140001400300390028403a000039151760072094280303001d00d868075803061140ba04644c003640a01004821a00440f01943d01c00e5502880ca43c240d030400c8445886140d41d121401494480000244422100154400d04403005216842035071556421210f0099026a8040f900070322050117462829070300040a81780304503804141200b10541d4020a16082c415004090b00204104220310754113104000242c40f040301c044000242ca038020500e14011048240580450344501d1000d803801102070b50000c00034081151340e00c202c03240b86510519014850075000308400011800140307004600d007101044104034850b07d00340301d941c0340ca805080141801c3c0c14061107840a402150a00000d41e01030812000204070b12000d14000600c84c20040e660320301c2001d000320040c000000810718421085400011224094640640301c1407046041c0b000c850312440301c03200b4a0002851900024103c03070140e5a1555850441c4400f1307610342440c1c0141e42052101c4070300051841c5010b85e15 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 901834811 1250 901833561 901833571
    0x702070e040c0509041b0f06080406051008030315011805061e0f0c0303090c010c02010909052508040303061a0703051c29010203040e27071d01091107020108 69
    0xba0641c00ba030345001281891106490a6800360b050706844400380c681004058020480d02e050303808101d1070100004c00400d0080d00c0101056110400728007941c1c400410b11000d00802015280e8904010507800c50840c16084211b01007181000c14000b0803420b90152411034801820281c50401e90006c10981c1d6024405055080c017010b2044c0c000300402c92028000741c1c00300d2030055580f400c159088900d1300c1181e41d500c2d0704019003407207000c0060742d00040701d40c21100c0d1590f0104031600c402e4880d50340c0700030710900c454030700d8064801401900c0d48545454002c5010ba14200013240d205c0210b54a611200350840d41c84010030450000001d124900425480303031330103002c500300c00c039603901607080d60381618030886030800d407021010300e0000d88034050485134024001185410714004414800043c010a00c699501d0214800c080041004521401010314107065905254a03440d90510346100660740185103281c19001090038043c920424401e01e005042d01410703c0181d03401180c0b10400102 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 901836061 1250 901834811 901834823
    0xf020427151403101a010f170a09120e0a1401050702061216030c080f04020d0203010e031c020c0601210c031203421a040504140702070e04 61
    0x5400740c0c950021400080140c00020040c00301d009201c001c05141c0921840d664800d5480c1000721021145010701360101c2c0748080c00c008000c1903848a0985036038041c0303d802c0c0c1032044c4660400c40d0400a580c024030301c040c441ca1281c01003074802101265001d13028030b05550000505c100a00c514a895000440c6240052400700d00c0c0c01a964003180321604a0300d00c2c440480b40401c1030000f0400c01e00e00c4401d40703c1085c5420056050450b000800c110800b031311940e641c000c10380c040f070309544560182040b00c41c2c010340280501d060301e40020ba926400001d01043c1c0008200c4081c901d8003d034001c035182c120400004200d5030b420240341c001c203074100603002d02d00101420150f00003d000142c103800114040c000110b50284003404c013500703584101c4820300081c10000001c0d0095a00d803a011801840241641c5000e88800c3c00b0940701c05040d6081030014144066800c1280040100200f05482d0259000c1c0320051010705c0189020f0f10681d44440540c010b088184000c110903507801d41e029008413 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 901837311 1250 901836061 901836071
    0x41b050d0f0b07050a08010e0406020c01090b0103060605030d050d020c0f1002070b070c0f030e01110708070f0504090b0f04030c0f0308042609011b12050403060f020427 74
    0x100003414014030050100c80103010712000006001004a049503c031480c3d003421454036403615001840d1500500840141441d03103404102031121503030544103110404d10081200c440303581090110700c4000d1108484090030404c003c925410040780440d610080f0791280c6007440b03588080c100180d00200b4410302548900c1100508900c01045501c150161071000182c1c2d800042c00c103120780b0500100702005004590309041c1c0003a001c404c40c0d01c052034041c50003554400d18039004903102c2e2610303010b0121600c24108003184c0ba92010600d0012941108031132803266039100140030a0390311034000030f00710000040004036a0b10b0b03000c141c0c5034403d00c84d140190109180d69100305000103044001d400040c0741c90204010024200041444030301440d18410301030029a4400c61684180190742c0c2c101714040c80001210090300031700803403090340300c3d420800341018104028082c3e003141c44140c030300c03600306601d0030b24032800c0384211001c1d10341c04420210491014014030798540c81c0c411044041d6035581c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 901838561 1250 901837311 901837319
    0x31e0a230a0c06022506180e150a0e061018050411040e090705060a03090f020307080f06161d300106061e03051008060103050c18070206041b 62
    0x6000803855680b00b004401406400e01e80024a0082c2d41050b2007600d118052140f18119584103207001150860700d050300c0c8505035003c5c4164000e60750380c003001100c6401414807200d12880d0394202d2072000150303034200040360b407000e103007201000540d4040d81144480310000b0405105072000301e04c4103400240b902e080c40c2e45401003000c070b80100c0c50a1804d000045401c0c41382410b12050036800410000c0140b0025003008000380e140d01c1a0000c1c0c0043c075944844030b404000c20301c5501c0c00c2e07107500123003a1501d440d60360b88202d40303580c1c00311019610703800340303900086210784044503000c24080190381c3d60301c1906c2403105800580c91308401155002c0d030b110000c148403071034100d0a078100d20b4071038000c00041c001550040b401c0d159641c20585c18440c0c2e0b10011136a001d0038031904456103a9500d00400c042d15000340500d0344085540201580c4d000ea41c0c004020302000003208002c0f40001e58802d1902e041e01e844400a480d0140c40100068001c20081400315400074180050184440141901c040e07403 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 901839811 1250 901838561 901838563
    0x80c03070f0302100509031c02031009180c05180a0b150a0905030712170307170103053306040b0f1809010f0501080a030c03120203010b0306031e0a23 66
    0xc0038411401030713020078074580d4046664014290000581c6c8000c0d41003000654031404100520f000f0035600780d40c04800580407541d000c0356600200b04000c1e08122900480444d0304130055403a00598180c512484006010f080060305042031400142c404140d68880d0003805019040350400d05034440c011044401d00743c4001001080d0100c601d0701e4503e2014900000d00d070030041c1560000c0101e0107030b40810000b01d0146007040051011188849941fa62880c0050703460fa0f00b140841c03480c829140e0004801c01c64000307003030b040840c1ca07000c11507610b1032020240903082d0320000080b00058014801b080d083d06007504600030300c1d40300808a00c01c5600c0e05000c104411403680700c081d1050600d000b0311203900710038414168082891b0703100344a07540c1030408480d03940606e503c1c02000c000d0000307005400e06210740f000e4030b07162111400555036565656523580c0990400d035842ca00c07030701419a1031149501c90241407203050031400c014010030540b079140e444040c5040c008010045038005486041490 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 901841061 1250 901839811 901839833
    0x80a0f0e0a11040e030a110a0b010f0e060402180105030703060801021812210705011401060509040e0a030914040902042c010902130f0b0d060b2b080c0307 68
    0x100c01001040c0c180d04504000c03a88110741c0103218010352814400814403600801192280d82c12410112080c00301106100e203080c400c100c0c00740500c5918000461a280920703c020220340c1d00c004068490b03210f5034100803c92080b070410801c5a0b0b411140101c0a5005e4006140c1c4800d040c100060b185690301d4406081e43c3c44020b80c002d401e07020440c80d035141e103064103840002c00602802004580090f0804140c010b501c0301c180c9000c64401700c0e0b05800c1040c25000390000194210120045503525800904181c01000c41c152080f070074010310195100000604c1844590980c1e103c3c1030440c580200c231010071506141003504192109103041c00340e2120b000f141d8511690740e241003040d24280160541140d034080700070300c55905011354440544d039600040b00b8510694140010b05140c0514850010b224200c0010380019210404005210040d404628510340a40d0040d08900c00384030307014421900504074242003050840c0e20b801051800b000b4100c0404044122840c20705036845101201d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 901842311 1250 901841061 901841081
    0xb0d050d170402091512070807030c0605070510020a020f010e030a08090d020c01030b010c060e1621080d090213020301081006050303092e112803080a0f 67
    0x150011100d180c40d9644034952080080780c00c484401a82401d0740050f1400b4805400600b00060014111030316584000007105c040306d90300105c610050b5501e5503203894400611003516240c4840c038001034894006c50459000070b1b8800d01601402e80d83c0c00c4444005e40003091008214030540310b601c001213074244100586510590010b5031945142a0000c0c44010010080c4c5160381140d4140c5010a13000600000600c4090030b021a4081c41c04004072440100070038090552820b02082c11070107a000300c1c900e080408000c04141c5102d4540c00126400c94103481203c0f07803100001c40e0103000c203031b03601c1c00f07040e45066210012894100d0740c0c000880041c40c0001215145078008010854010100000e144140314680203110003442c01c00001e440340500b540c1640144103d001c40b140b0f1000e10380c3e580180341004640b5079240e40302031703200030800d05085102070b0b80c81c41015803050246104644e0030240004c150340b50101f0f403000b82c3d03080741d41020140002441a4440205014014250144550603 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 901843561 1250 901842311 901842313
    0xd0c15090521060a05041509060e010506040209012a060c0504080c041e05100312031a030105040f02100e03240f040c1202030a080a090f0b030112030e03010b0d05 71
    0x181448108814032545203000c0d00e0001d40c0d00180314200c1d502090f0340f54000c44690001543d07a48504180314102002122030811524283c1c8080c10860320780d00012142c4465002044541d60740c000b800120711920031164003180c1004001d40500c01c0c8010506850980324845100d8004507542e210251601c038221400440c0b804030f402d00001c8020002c0f007041c01000c43e820302038070743d402c03203045030040038400542036041e190302c002000e4031541c1200324000c550200c080b0301c40f010305000007001484c644000c0c440303490340c02c041c0b000d003490140210382c000c03034100b41c0300c1c1c02040656080107682c100005003242400301c41e1800302015682406400d098031000c01c03100f1078502401c00d80c1c0400340c10003070a644006044400388008142d1200d8006c0c2561550900307040c00c1d8905000081c038041c00d1480c001d090800c0084c4041140380d10800c400b045600321401d842d4103540f21020342c10710780824080c0151042c50300e500c41000c070f881060351001ea070034081d000280c00c20300f82c804240500229501078440f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 901844811 1250 901843561 901843577
    0x13140a060506012613030309020910182703090e0114040c02030328090f1a060d05101505120106080607020318060d0209090f04030e06090d020d0c15 65
    0x403560002c3d451350038007004480e15080c00118101001c0400700c09010400188400b000c21401c060295110580f440c1c0c004000001525244000a818a10b40e004400382c9a03055400075010505500401c518045100b12a209503052590f40b52075024403144203408010b80c043c00058203520000c101d5020b04081c2a0074030010005405000030307221401e00c240e045500400c1082102503180b83c0c0c03c2c05204200844500310b0000c00300c0c10000e01882a009014001d10075040000c03c0040c59800000034025800e140700c9a840c68200941c005070440040c10680050880000340303510fa0b80300011030303100110801d000b180c480010458841000004000603036507014180450002001754a51082c500d20003545407082180c45103d0280407010000d002e10740110710f95140b0302041c0c040d030342c0049024001009610f048105200203080945017540491840d82d018031850800c07008075018024040c20840c10003e85038284040040040b40a80b40d91004800c041071000d48880da0340d43e11695270369290700e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 901846061 1250 901844811 901844821
    0xf06010c02090703051b0403050c10140c030c0c04060806010b0f0d06090c030b04051501031109060307051c2306121204090b030a02091b0712030207060f0b0913140a0605 74
    0x40c0c000443d800c018085442484100006040061654003400b02503480002860046408cd030704003da1071551a400100410f000c0465a0008054070020101c2401c40b9211503031281404226401400b403007050b500200010300040062000038040c080c8030843d8a4075180503284040c003103034056001500000e4135000801c00d450b41c10700038902c2070b190848013040242080c800404403090140c0000e4103154841c481000c207100e021080e00c0d490034002d0f00c19507680c940200c00808540c00a424040c0000d14400c03030050503a5203205210b03441d109425034007503205030380d031908085010040543d0b038040d01007299925417007820b00600503046a148809621542421040b2090324003507041d10b40030350700850126026035203588a45410085201c6c030303d50b100e6441c804084440c811840d016020155002c0b0b0071001e04d505500804a079405104100456900945030300290f45a15606580c4000c1309400308944083e01c12102d117600d881502898030780d1003041501f07820001d5004040d100136654404101c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 901847311 1250 901846061 901846081
    0xc060606210a05011e180e0709060609031506080a061a03152409151819050c0c330a1413080315010e130e1c080f06010c0209070305 58
    0x240c55080e0004507620744908043c03039510320001444040003110f84503844010841e505010f041c8c0a01202002841001c2d10ba550180400b00144011941c0130088100400d03a960207202d44800d03070303100d400074000701075503911004058008003844004200c0584203e82480da410044440c5041c5c0601c94162240f401202070700001c01d01c400f50700c84015031046282459a03030a0412640601e1066803007900c00d040d08040b604407420036802e0000106200300f84001500c50000c3c2c00d060700910182031000755181019801d40d401034080505a45d44100401c0c07640e03040781210355200d800a205807124988404401440080050b01c9122a0903540d43c01590009030341d4078207540c00044141080025509540d600307506200040908903102e01c00030071889141c2c414527085000c00e400400714604803038940c0d210380c0204144001403800780308840900448900c1e0001100792000f90f41c0b10041207039552602d003070381041c0003030900d810441d040002c000103075140c0782418060115079030009410700d0004190 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 901848561 1250 901847311 901847339
    0x9010f0e0c0603130c030807030206040c24110c041509110a120b0f060c0d030507081306020d0204050301090b070e0d0804030f1703090f070b0c060606210a0501 70
    0x229125000310416540302c2c0c4810049982200780b980100f4007401d002d007094880d444113600010108100060303840c09069002400714050350080041150203075a484810ba52051840c00700c02d0448400050300e142a4081e0094800c41021407040d9080b000702100050704a50f040c0851500701c2040400a000c5d41c402c51040100b082d9028030b42074a400080340003c2c084a000b980b1a1101d5138940541d62069100e40c9040b044110004d0819a2a820300a0a9585070003444c4a2030303001a141000280016100f11070040c098400e000060101d0281510b42d003000e50b01074407034000115000c2000044644092080b038a00a01460444146060401c00280303921408071407503201c4c0781c1e44020380c0c6c0800d5001007101c2c110790b481102c40d20b103082c4624140003205204400340301d4040c3c01104011081c00d0100e980d6440c1d20145040c2c410550305e0398856402ea0090410100c084e07400440055a0f41c1007010060107030104541c5820960301c815003045a220310225100a4841d13218401003011813549100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 901849811 1250 901848561 901848581
    0x20d0212030c1c14130503010906020913050106082a0d020c070b1809061801291306080c0f0a050d0506030a030e061b07080102030105010e031c2609010f 67
    0x30880f003000850001064403d00f40103c401065000a52104e0710b040b03c408500140000f8009101e0981e00b420048020740000407510700810045032007540d25602481410b0680702ca54641299503100e6401c82c1c02010701d4000c0c2d00030303070b01151f139010b000c4045030344050040d01092010251361401220052400c201260f800414014003d002c1e108080c10450007c20b400c143c141d900250954800000880c0c0a090303001146076141c41c500045001c1449041c1501e056070401c3d8606601e944980b018070780b034856001201e100b852020414044180b0074032206070440411203000d402c20b00706040010003a80440f80710404200b001500c40e111401501070542e00c003004602818191565840241119040300d41d12441140001100a014040721079440c1500801e6012580c203240c881002034001e50081c020640894042c21201000b407400181900d8105040d40c031003040f2010604080c0c40e01203443e0310440040c100d1050a043c9082c0000d0380901c690114400031071850080c2d4a020221025656 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 901851061 1250 901849811 901849843
    0x61e0b0919120203160e2a0c010c02060105030a0309170106150503060f06030f041b0906090f052211030316050604020925080a060b07030503010e0f060d020d020d0212030c 75
    0xa0100444100141d5080e441504080240c0b100e00804081f09540c2031510300700c0101c590042404d4100410550001d43c0d00c105a400b201d10603600d8408150b95440d80450007400986080700c10302191f1700d0a1038079520384000d14000b0507802d481d42c00034035030300f800380440500061011082220f1440d262081021804050f240c440c40c46c101240c0f8402013a078020009040d44402103045d082c1c0700e1f2214040f500404d400c2204002e1103032129400f001400020000600680c2407402062560808120306200400d4582e000302259005503125580240580c3e807155050000b4054504024500700100c80038500c01c43c05841030b8646481005001040500080c3c81401021004411606204154010513006007412025503031001a89400341080ba0410080381c440403908104068000000d103041e00c180c1428602c1943e9090460108840103d50326513000030b204501c8000350610140c44860f190000d82031210081560b004a14100040a40c400d8690320000304c00303c81050504c1055482c2c00c92113 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 901852311 1250 901851061 901851103
    0x4061d01060507080f07020d14070e010f0b2d032805090606040e030c0102130f17030a050d0207022d040b090f1306050f0a061e0b0919120203 62
    0x921010a18005c071140c60032880f00000c1c0307a07030542d5180301100302c0c0b00d540710302c00001d0a45540e2101c2d4465000e07120f44043c0f80305820020400c880d0280031401940e40c80d01006051941b09040805424940498680440720258981400c000800002d502c2000b918800c200c0510328142d070304001c502d048010b102205e2802040c4800b501c0c0110b1801d40114048501107508251014094212311400f00610031542c4005600d03c94060016526800c0769500035003040040d07074404041c000c4151030155803007250810409600640c0c090001b400410320114001814a29243d020643d01c040c460001c468011090600d501040d00e0729054035034205064906000010454001c0340310f1100160041c0c000d6888134002801c050041c0e030281d03c1885d040750060105040885a442d160035040d030301003d40905080010544001401048036181c0300300c02022401c41c9010391190b90303600705284840d8170008145050441091041410300a0007414445851070030007881050b140c558400b01e403540d40d400403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 901853561 1250 901852311 901852313
    0x302280513091401050f0604050409060905060c03010614031503030703030e0709060803030f040f08070b0708060604031e06020915041805010f060804050c091602010501061b020402071104061d01060507 88
    0xb810f0141120400c0d40c20318003503951440061030500403a001a600301d45407034622002e009880e00040c50007402002502c4242d101e103a0b01032010b11090003042d0200d0010480c1700d0161814100840d0702420b0107240d040b40a0b11080042d0079580b004100340c0c0087d03101c66024580c0c00c0c01b400300b10001c004085c81001040d1500c8052a00c900000b040c08100307440c1000028107100c0301010001c00290302c1840305956040c10b10700f09010390000e86040c2c00045d82040050b5071401d1441c2100d05998001e0b0340b104400d40b81d405804200010000b044900f15000d03c581601d6032a1a00715100101900c09400c0d01c031418641016560010900744140250070b09004219840003489048141e440519013980c503507907107017401403800e07804240007030b0072041c42820000300d0b500410a802e0005404d5000384038070390761090100c2c3c01040f000c1040e1161040040c16500500c2c0c954018201c1c14464a03000c280903070320320001400c1300c6141d8400c0c0c1640b58a00703201c1c40440c80c40302c0d0503405890241030040c00d008035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 901854811 1250 901853561 901853591
    0x80105090714091801180b0904020112240605040801050a02042d15030209030c03060403020d052115012604031b21091212030228051309 60
    0x1603210000760307900b0000340700061901c44038102d25006a0380101802c084d65920b45440300d51840701840344e2504d141001000d41498400c80e828000c0b90140d6a003904c81e410216008000c106406429440540c0e6001001d54070341c8413103100d0018852920741036201d0b4941414a0300b0340700e00602c61500e2034030411060020700302034003101e0007818504004442d4a074400b422030250301403a41040c402d000305488405101a41358001f055a4501502651424056003090541e600f0007514000c0c0542c0100307c4900320030b032191028000d04061061603e0003031001600c1c000d494134041d02e081d0f1070000988410000c2d9604900c8061482c20180b200c21000d1519080e010034003100508024208003440c6070741c2500c42d1445100b0742101e9006092003ea03000d00b0b05071080910102c0d503020020400c2c50030005904124540f83d8402550003402e042001035180390110b0003540b0440c1010003030f0048100c51039220900e94005003c507155921a075954160f614240d9009d442c1c06c1e403010351300301e09284654001e50320b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 901856061 1250 901854811 901854827
    0x50f0a0c1b0b060a12061b03090f03050904140906100608090d030504020a03051006060327060207030324030501051008030a0e0102190c030b090609033106030c0801050907 75
    0x34221100b40140d0303c501c0000350070322004e80c1c440c0400d0803680c1170200a10849902c0207040d80e40300502135100602c40c181c20760a540d5001d81c0941042c03031340c412907800301e40943c1c020311003d00d0042c80010b1498501c001003064040a90f0b00000d2a4000001c0002d68140b028511003e4503150400c1007107490700700481917540c43d000a400c0105a202c20100d011526182580303005158400c0070f544500c4140540c04006021031300c60000002d00301041c0301c02c88101d05440b00d4106020190b107407180250768896401a40c0107100c21410196241c0c11a00c241103035005000c80490b464040300e520f1807550614a09449004c0d00c681441548918100181c00000049416014080c00e11a0301981880010307401e00b142031b0a000c48192030503001d2410002c9020707011082d207101e400c035403807241c480e607141c41d0743c64100310b0b2281034030343c010041c2d40c0e50703140c104020031101c80b4504640c6954a168200b00281180554046d0b4040b13501d810260503420381000360140940429280703001103140404000345506 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 901857311 1250 901856061 901856063
    0xf0311030f0303150d0b0403111c0207030308041103073b06011107031403041a0f07021e0604060806041407050f070809060a0f02070b0f1b01020d050f0a0c1b 69
    0x48004c07006005540c90318101c224660f5007005980916140604000d170400072100c22064090180310005045c07101142c288010904055008220042c1169801e40758058080e00c1a22281c4911048e01d202d1b40d4108083d9014101045e2108180000307294a081d1103c41c4a84c0c891035409540c18000d0b05c0b06642003c5030b800182440c0401480c2050b4110383d0501203d034101810503d0307014840d1220140000c0140304840803003d159401c0d00002c1007000250113060160b0308041c0741081054007501d4103681034040130112246091150100c0800035145900c26803015001c02c2050342003150501e41840b441083c0040c103d1006928685001d00a104d88907550403d01c0c1da60001c18000180501e10b4155007241902429050b62118040c1011b0990613140c000c80f001442031100c0403e00500c000180c0e240c1c4a104100c090030a410100550400d14540313851182540d8288400d41030b0200300c2c05000e0003426200c002c88400c0c14550660300a50f5070320792003041030100900b0100522111249000101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 901858561 1250 901857311 901857331
    0x5190810180b0411040603140c0d120f1106012303030a0806060a170405060603012a1d1909050c0f0f0705150c1809010b160501150f0311030f0303 64
    0x15691481d03c403030f80c540d00720b038015049860901b021080201d0b032210b42a594103040708440b44c240503001080f07a00618003a000b0300141a03030300342481c000d02a00079640790a08a040100c031540865890500e0800241d00c001d0140788010b03c002c0040e01c900e52600c4080006601643c5011002c20340906011409041c00e0301608000807807100c800c0c40394800c049102e404040513542030805040003562094181d912910075460300820740000a255210320702043c95020500c0e04e501075622003030310b601c4000b0100800507011008403c00964490007118241800f07000101081c03401c01804008850300100b00e04800078040010254040b002815680c0a040548459a03540c41a242840c280302018000c01c2c0e4004200050142c000b10000c090302007402c07000010380307100082d034040040703401081c8221040103000308420400300701509122aa4030340100008540311000c00003c00c00c008446d0322121602032107150500412013049242d0143c483c04400605c181e00e11006007030f80702c1c88054150901 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 901859811 1250 901858561 901858583
    0x1d090613020f0403030203040e0705190e04020708030a0203040309060503061e04091202030a030b0a050a0510020f030a0e090c03060f0d03020106090f020d150f0603020c01060519081018 81
    0x101400e8044544a1080c01c0800fa100c40d40c0345006907481e0040d01079040700304030980028452a100d20300b0745186141c10350040a403c0d0031440e05440d603c064034502c40d00903030200f2000f000304098900950182caa010001030342c80c03605050040001c0036680180c01001810000e001017503071841e0300324100340012200c1544418070ba00002d00200843c11004180039584404401500d80100c060550b12441b62401d218242003142002041c083c640500c5500100501c800d0066080c02c14408603607603201d00403100d018141200c0e052554025081520010f13400c02c0840c00d460800c03800e403d400c01e1803508100c2c29400c00900068440c504941014007580031070060710207141c403d4100c0c2000f012058000c1202c15500350303c001c060361042680004407401c140440d904000302842a10480e00c0c0604500100c5e401c20038101c029500100c1855629902c81002150581e103030b1b007034a440b01c2c0301910007040e40303441d05006078100b81c260540d40b00901c5c40d00e0462098003a00440c040c01e00740d4000343c0508 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 901861061 1250 901859811 901859839
    0x90609060e04020d0f09021c24020c120a0f020f0303010512160b07120e100f02010603172a0703330b040b040903020c04200a0f1d0906 59
    0x8001d02507924010f44c520b080080203d56150f00d6801110194001d0710041c03040d11020780036040d02c401070034000b4602c651034290040d00802404004100b03648000b0003500e44894984d01500c0c0480c02e5030441881e02000a202d03007090b8100d100d09040c410b0354000f8010081c0d0b6084ac0f00e031a408140706e29400384103c020382c0e00a40005120b2401080b88600b43c3c51b91941d15840304921540007d40101d8141c00b20080e410383c030a0051503e07030340d100001000081c06c0d00500300d0031290403205294600942d0b4864002000140b007148900804000e6013120315100e0001c81e00c5070754124900c6048003000c03864034100c484d9102001c1410700c15241c1003010010f050100700c10b15500398048000054400009400607030404c1540d030032071220303440211802d10241c407000742040102c035400040100580c0c405a00381d085c40c02d00e90480b00040b800e011900c20200c0407020451200e6010101c02c00001e00f080149040305034100860b0a5800075032520036120003041e2010840c1040701501c2c0794490340304412888 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 901862311 1250 901861061 901861069
    0x1b090c07080f0a080103020a06082404060807030303020306040c1815200a06110a09091d060c07050111130b1c0204080d080c1201061b0c14030c01090609060e 69
    0x3030202d48442c016666558000100103101e1402800128454280000c0002c1c856224190040c003030300003e8091005c2e421062150302591402c516440c0d0855200c2c10000b50020f010701000004500130348002d0b94a1508a0800003252982c1c41700c0e1041c402c4a1a0400c030007443c10643d0000e87d030008401d00d01f2810401419912924090308919040003282c11413502c006000c01c556020302d200b104103100ca1103a85460850034006c40d0b580400203030700c0b16000c1209111540110f512a105040480205100a204035041141c11034400e03009100001e910f83c10000240300d103010700700181c20406e003840c0d1a8048003403000158803032900c0c000e0000c1107042602516141c03001440e4900e900856a8640c2c4a4845465804500e05600840c048000083c6410821000c885c1114005180780c5907503801c02100740c82c182c041c00019200d00c02e4103c81100000e0890301c01002900c1e80040b149011510b5808052604442d86452030411040c0e80b001c002c440d4205a400080d2a07950900d454a42982c2002c5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 901863561 1250 901862311 901862317
    0x60a09050901060c020111013c0924111206011b05060a0e0127030903062c1903030b1201021201080c0d05073507081b090c0708 56
    0x101c0d4080e400600000d00c298215060b607403558400c2c0c0312140f070702c0d56040d9494202d82d4441c44114801400101d4126031918042c0c200311145c1c030403502c03c0c1403290a200c0385000c49041250803144580d50b800701507500390b64603500200c404403040e03003030240744000402a50140140f41202103820850004079401c5ea0090801e095011610388024a5040d8a4100142d444c002607c2c0e5507101c03841c29032030000c100c00c1070144400002e0742b5126030300800703800342882400341e0781810141c0c100200e4540c0403000a90074044d013600710194550680d5024610540f0103507408512854612070741c481c14400e0030040e41c031070010081a41508001a0540301640414241c94540c0490300c2c60b0351001903100b0841c003081d00014165075443c0c00f152a1104e0100620240182015015010f580a942d0400420206c030340c030340300d2025003950380d5071a44c240040a0505001c072680b6080440d040001c0502400d001008100c45084400110014010f035036004200a002c0142c50841c1c1ca480015011041c040c0c3d010413 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 901864811 1250 901863561 901863569
    0x408040323101a0a080a02090a021b01020406030b100c02090709150302070507080703030504032a1d07050f090103020306041b110607020304061407060f0c02030706060503030307080402060a09 84
    0x1a14010400b450444008101e02d0b014181000303900000d010250034106041000e65440400600103100c0940802040d51070042122703441a40030003080d01404005555141400c05250002d82ca440c1420400b5081e02c4140d00100d001e002d000b840404e0300d50384420082c0a903a0107941c0c0c0751094a81603002c440c50b00e02500b2a100106000121400340e03a8940d000344440e502660503654415162440d1540701e16042c031000e80000c90500040c00851040c0d4402004000306040e07448a85d40b0303024882040440d6684808294020804440d0264036100391255009407140b400601d450b5841400250a02130514520304066010001849549070340c2e05c05484c0c405058001c4a100c1e6258400070070048503207908207201d004040219042d18000800d03076050311580d0712a41205200400500c01540001206481850b200c13210010580b1a40c0303c1c10501100c0769015590360211410030105407149540101d02a9000700f081090084c0c2c454481900554100d440503620103d09a04513480314881d00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 901866061 1250 901864811 901864813
    0xa030f03171e010f050102060f070c020306010306060905090a0210030209030709051302010f0e012c150a0908030702131e0c02030403110306040c0608180102040e0106090e0408040323 80
    0x20501c440000c02980e0804401c401d904480000da813070341106090b080d014418a400760b404030b1301240150010f800501d5000c425440e0841c0d030318100303400007403801d20700780e205070340083c1d40d000c080c0147c203018055154000d507064024130f409a07059000c00d0145100384001403c0540c08035101b02e9a540520940005100c404400e00044c00e0034a401d44070840c0e9003804034003240c0006600ea44550180c60030034103001c016180e2525003071400e00f54070a50a500c3d500080507603070180c80c3c00059518913409420108080800540300e4030004000f402da0015600182841d80c070138003590340160340301040400c502101c14804204004031200072020a189212100992130a1450307026030301c0d41c000050004c41c0d0041445d0300003c031068040c0760303c0da8401c0e034010b40a007040c2c000034040075000d01d440640090402c40303180c14100e000c1c10180d08907005a0009a11100142d004111503a444600c210141c991a141c3c0703400340c00c2560b03030312043d0b1050303200c014511450b898031075200e12550450120750752034404c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 901867311 1250 901866061 901866107
    0x1e0f0f22120f0804080f0703050408010203091e07050303031803091e010e0d020904231006030b160203030a0b030705040c0302070b09010e0318030102090d0b01230a030f03 75
    0x1240010155184103500307000140301da90400c811601c41c2003858000c1e40c0015840d407414040d2040441c0b6640250710642c00d01c1010040014015024401184681c101c00050320001c0345000080c0d000000303003c0c1c614035990000e04248040e035408000c907070300034a5586040ea1402449824075040d07004900742c0d03541c00541c0c9812080e003030780290031034600306030240e9401042c40d60500400604191040b8041d400100902c0000c000629008011004240201c1d2400c0669001421185010a00004401c0f496214081041000f001c82440764216a07245081c0100400c0d16900079603038080140625440340e11848541015202031040074064500980240301e10382a000c000b501030f41c0075002c02c86001101d0400260300c80010301c2004000a03001c4081c52400d01030884c3e04034440e20400499134955420042c1c01450364850709203284403485201d6514041d0b14103100c0002c01d8080025070201ba203140c030742c0d1150741e64900302d00c101540d40c0a10072000105443c2004c881d04c0f1100028150100390f00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 901868561 1250 901867311 901867313
    0x60605040b0f0910030804231c020d0f02041503030206090307080a26040303020919033f1e020f061308071209151403040605090307050a0b1e0f0f22 65
    0x220701c040298200d01c4061150307448c410910100030700d803001c40204001c0a40d00d0400500e060b0b9000c00c0468054110050f0b07849003a00000c0403a8020b42c443c0034000701001003001015018401540d000e903451002d542081103e171030310b865920034440c11204000c00343d2040e40925422000084040340001c4d80b1414501d41458060001d5102c07490543c41005040c08a0040380c401d0074181d8241c0780c0c0020449a05007400040c034410750f9100510700d8504403046696849443c110031200c2c190b080a50b6181407900340d14031010300300b800039420001150041078041a03150b00010315242c100c1041c0e448a0f0307490007d42006000c0340512031008242c0c0800c8400b400740b2590055041c0c0580c0e9280c1d81c18015890300032030582d400000c180000010a9040c000503000c112181c0c0007540c04111003094074549409540e90a040c0341e41c01360111060400360381030080015090031042090005c41c00b080c0c1880c1818500b09001101c0100b0800b204801c0d400000c290382c46680007000e0020a10080c04028001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 901869811 1250 901868561 901868579
    0x70501020c010213140a0608060301090501180c0501091d071106091f0c14030402060403080a0504063b120d0e1503070c06020a030b0a12060605040b0f0910030804 71
    0x10051040307540f000300c130740d01207410507000503500c00c003d000504000c00c045c90000e0654800c0b8005000d0780e495543d440400d40404e90030f0050007510f40188041503081a5146400082c81c0300d182c10150400946001c01d00000c1c10100202114009000c0711070f00356501e40504440103c040d01042c04280121303024003004880c0002c0183e8103003400748000d2485854803203210304032410707141d10700002442d4a181d98a0028140c0082d41c02070300160a0f2458a5129214192541d000240c20800150001003c1007001e40c0300b20352400042d150441031320890030810340182500650450720302c11071107110300201c0030740d40c44d44c146462070124010355005e032420300406081085c0f2054420b02076802c0003040c07048510002c1c00c50744070b4401174503a14a1080c50780c58400003900541502e03400c0c9a45d60a000d0495542c0d80110310060040c0485000c40d0b1201e0b00e020b506031152a400035000740c0c103000c014581a034a0090000d0214800e03500e070041030740c0e2040b00048035100d0394000751015a0000300841c200c28 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 901871061 1250 901869811 901869817
    0xd0629130b15040e0712052202120106060f110102041a0904060302100518040504032703200316030b0604110d020f09180f0103021005090907051903090f06050c070501020c0102 77
    0x71554640b448100c8428032010250b5104230340740c0401c8661800181542010008840c0c1e90701d00291006d5084650418002d0854041e03400003004a201c0040c001c40d038a500000880f07140030050000e50403d490003019601550340315030ac0401000010410000340d40702c4e40d100200554000348113115401920b1806040c41d4030105002101c940064428100c505107801480d025550680e25400300c241c1080c2207980d08680714122606040411394000040b4000f050000da140d182c0e8100d410410f200d0004043c5040d1154a052030004603882042012070445e0352090740c00001660302003119800d0030214a550311920081c00851071001c52041d00038620b08020308040601540c0900c0701d00d44200c002d40c1281c0701181e00203400c0401100610050410ba44512440c00301d80c10300d41d00b0180c501c40011041c040440380d041c0000c00100355014010001d500300011110b10341010445808151541c048070140c5000180c03e180e00e60002c603455441c0c103003c940280d0342102c002c6446151418025010394 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 901872311 1250 901871061 901871071
    0xe0d0609080c16140108070c0501020c15010504051e0907030c0e22050a291303080c1206150c030a03060305070504050106020303041103010b0d0629130b15040e 70
    0xc8200d0700e040f0b214031098890801a20076018100c192038200b40011102c40b40010300d0442040440450140040c40900142140380c3e03e0001910503540600224101600143c0c440c500c25818403081c444409600c4500e10000740418081100503947c800c0c40c1842c00f0000c0d8002401c258690740005211803002c140c86004644201c0700d802c1d440b0540d071103001441710001d00a03100303411001052000914520701e07114104007403001c0025036403004c442100c64460458591800900314009401010b034000c076829440881e01c1103486c1400c0c141e00342c18034882401081140103401142203500c00f81d66480944600c2a641c3e01101d940d240242402005085a44030440391031041d00c2c400300302e919080c01800d050b0f0300154000c600319075030340e100c904e64102140f4150342c0655a991815100da240d00b68034520050207881c0100f4581c00c1900c032100c400c07407000320b03140e003216003405401300c0caa80e11410b0030b040168800c800b15543c21907000091a04004020b50750102c2000100041c1004402429511031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 901873561 1250 901872311 901872313
    0x905030c1e012301061d060d0506032b120f020c0a060b0103060b030a050a0b130b090108010b03061305010615090918080d090c090c03020304140d0206070e0d0609080c 73
    0x14062520710f092944188104600180c1c0000500400d44036120307600c1c01c02011242c0c090005016804544030b58080d50b00040ba0303540381c00821920b4101080110108150b440b00140c91340c140f47c4c1c940403451444406d180c00c1158892400e0002038031303500f01700c4540030f05400c03c665a09410910550b500132049003140d285043c007040807529802845010308481c1058002807450303940c0d40050f001031200801c02402142d6903e200702c0b0f01e4036140500750640400b00b0000840d01042d400704819008168400c1c80365038100300c4241d00300d0b1004140d55030401c0940f000c3d0700140c0340d2803802034090692604031482c80107140c43c54100c1d103548110a00c0c121a0340c0c1c2410464110159542200004410409005240c0412102000e4a0349900c002422406100c003103201070f85800ca090180c5103014514800642c020043c8400e2001c03001e85100034041c00001404510625040070b5145c1d54028441402d2152103008e100c0c041e100c1944041340e4983c000000c000c040d00700c0c600416150440640b803215 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 901874811 1250 901873561 901873571
    0xd060209030d0809120309070501050901020a0b0f0105041508070e1e09031e0915090f060301030605221a13052d0a031403040c0e0c0d110703120905030c1e01 69
    0x80f1740b0108201d074040c3e98140041c0c0811810f04005444d1030340b240301e0490452103800301e403102107242d02e460940540000a004003055240c0402c00040da00428a0f0903a040f0412400308400d030310004425080b03c902c551840100e50302c02c46e44102c038030340781c42494150742000000c2100c070180200080924900038a81d41d500168240380451380c90141001050300314403070b01c07510341d041c180c0c00001e810014001005a0900c00942c00860001c0d00300380d00448040c0c0e04c0c0e006102d00c004e600401d0f6101104409901d42c0c00c0c3c04c054841d45039081561000040041900d00400c443d0a01050342504103030304902180c0c145c81604140010f11040c021a040a204e00c10020112075140407500c401401e0701a41e40ba007010986900c3c442c0389031300282040350140c4945000184402c4440071040c0700d0800b842440d500c0f500c4200301071301a21104241400b180400300b001e48002508107007018035030061140c1c0003400e17079543d02c0d00781d1451081241c2c480c1e10340300c1c030034540315240d61404803128130781c021a0080c0b203 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 901876061 1250 901874811 901874833
    0x1e0203030f0f160e040e01151a160b0c04090c05120105030d050405091e13110a0e0a0f0906021306021b06070312021e0705150103020f0d060209030d0809 67
    0x2e00c629050310303080c1c2c00c1d040c0000c94a400030711400c1d1000d801e5400802c00a000724a5080090131070b800098100018003900b00c08010415991412045110010703990701e05d40041030038921504000d55100504e000f50040c00b01d84249500c4c4141e6000d407000310420490036100400181c410303041260616800c242c1c03a4008191818046100c503d80030a98481504183c2800104a42c954004105000400e50400d03240039170540e2014035402848800f50b00c2c203003507101e03082ca030015180052030300780645680c07081040110f00c0d40c1c000300c7e40032030580000070f0800c0c1d080c2c10120150140d007101a05981c00810301d01280c030200b914260480345907408a44440184122681c0940d212280700c951020080c80b101f404a401121903110840b40d00f40010318000c11a1085050030581071642c0140c0c150205c0c413642000320401080448402055010119624580c00180d0984210031124012300d041c000a20800c550341e0141e03a141d0f0801025940c0030500c18400602c0d20804542c00170640c070403a84900f03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 901877311 1250 901876061 901876081
    0x1b0a1d190f0522020906130f1815050c031501032310050102011b050a0c12020109030306050103020316050a0e0a0905090601050d15050c0423130e0c09071e0203030f 72
    0x3251350162000e03080d82e43d40c0c800c2103c40005602e1740c80070b140c1c840b4480c0d440c6418500c030303054280714121244651a080781c01c0030000c00c108458090f10140c0f4100c01d0281045000d01030f40d6020b03a00c40041640c03002d026004031701034224800c00701c1348040c40b103803100d4465840c05042441540c80c5c0842c0c0035013030780d0355004900340c81d1612254491081d03d41e003003541c098801c03802028140c00904210490080b1551440502c4e2520750074800107175542d01ca248201989401200003c00d002d02c2d00750b045003000c0c616840702c411084a000e0522038000741c410041c60003184c600407814002044031240300ea039104a03101800381154007600c0c50141c0b10001c5030b03d107800c0070f20546c0d581e000b002560050611807604801490094400456610180300c0020640c1813560b1040042c081c0b066400030344804101404120406c2e881c0c41081581000305861818800143c049244c8001722454103c0b80c41c2d810003610003901140d4441c07000c1104004c07050126030008011401541d42c540040034030350780c4031b60031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 901878561 1250 901877311 901877371
    0x5060d02370e1c020a0e07120f053d17010c080403050f030613050406020d06061b230a080301061d13020c1501081b0a1d190f05 56
    0xc2e40c0c402810361400c9500d410070140c4640080c400b420141c031486c2c41c0c4420482c0031200315140c000240e940f20491a40018034092040a035401030340034045810080c124260908038101e01400d07003410380e030906903c0101480e940c00101000c05a2594031078503001048040105040b244105608000d86042c41a100d10842c2e8030980e019a501c40c1010006514840540e0010702840c0d44458180010b01071300650344505409a449141d0050713480401da02c80741d00f41d410b030368080c105101a818003144081000103000001d1688400316044111844420001500740c501410b07505109032842c2c0e6040100e0400218180c41494666010f0481110000c200e8001c00308a4a40c1107219040581070703840700c903000f800c04000040140c50a0184a001106080c1070076840421640d0016a03040511050006148039085055410440e85410084100841c1c01803000c21a40481580c000074942120070740d41c10b4480c103c6507014001494844072000c00341c4410750390b191120354100050503c3e0f4440e907180f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 901879811 1250 901878561 901878587
    0x19080105150307030206070c0f0902070b0907081c0c0507030c0618060518030a0204090818090f0f06180403120c0203070201022e0608010c141305060d0237 68
    0x3c100041c10750b400d01420f608204812030b0150103043c00410340d900c00c1103c0340060544c00c2c01c01a202c80c02c504041c0301d10724000e815070446030072030322040c000030401203640800800090b8030203164008031141214091505c060150243c00748d02c002004000b25007080d5000c8a2007a0b94181d1240c03440320305e00092802511505010070402c02094114080064100c0c00e0000c1c02415281c020344c0c5138010909840b03060400b00c1c6c40d8140000c1030b0106032941048001900c9007551030408603d4680214400e103100a02104c00c1e400302d41000a0035a41c440c194045c040d000c0031210086030400c0d143c05000f1091407180d01e403800f8200744812411f14400800d80d130025405900824a2a08580201540d0755020011130000140080003207200e0308907020302c10083c900300c03000041a032244003004141444c1c0303552071003000004205103050259050000c0c0d0980b0000c0b100c5913502c0400501c01070082c40b0300303079a2981000c16856010b14450310180d0b0f80c00c132603c980a0b02c0206494415088504c0100490 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 901881061 1250 901879811 901879813
    0x1140f04020409141b01031b21020702060c0109050c090c0a03150b0f040806070e0303120712050103120210060f1205030f03012c0c04090506030c190801051503 70
    0x100240c050714040e003020158600130840008085080d06000d401c2c00031100461101c18845100c1500650303140c0306803d54016103040ca805603148104000301a2000205800742413000031803407045000325030b411070300901d80c0204515540c410305954207000c1c000340c4409440314000c4003201000340c01e04d121200e10598200b54801c0c680b801c205001d800030030400d5504950003c20020203e03903240c04400070403d00e031482c0902625203250002842c640100180480108641d00140c850142c900005440e460484009805d142e0350325040c0499150803403e1a2642c0700742820000800c1c020a100804511001136094507220f80401075040b0507600d051042410001c14004200000e500f0b02c1d03c4408014800e005880c68184260612146a082a00104064440c0c0e80101154241441e450100303000015803c202510303080322130081c28012441180c040c0d5441d1800610702d40d50905c80c00c4200390000f842c0b524008240c100030030b030034034a80c000c2009540ca0a0086505811003d0581c801c40500030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 901882311 1250 901881061 901881091
    0xf0d0204060c0501110a080705130b030702070f050411070f061413021c0309060c0c0306050103050601050a120506060f04230603100501030c0b0a050f0307020105160c020906091003060e0f0114 84
    0x12384210381550110f060503000c9900e100d40801c0600b0200021030180d03d00e0782c002c013490307410301d0300340d8070a40882d0b40001e1060b841c04052a05841c1d034001940d030403d400144080b03000000b414040d001d0600702000601c4903152808000300c0d00304000d0f142103c02c4c011e44007400c842e455443c20800c03000b00130b4805400704654041c20485c5a11aa131003940d042d100d07122114195a81e95200000d542c42a001192290081c2005200c0c40c2090181440144407000c0c40e094501440c1c0c031000d0f02c61102910160003038403018040c81c900c2c0c44030b4000c1d0906000019484040c8050488055181c8500307880607486405460002c417140394150051506803900125440000c510700707004050380341d1081201c0e2090001c1446000d8004824101640c0300e48141c0d00042100d01c1d2070301441c206100070034100c0301070160120720b202c0075031100c90703141d175004200f03880850305603c92180e48005400f05038001060542408a41c40c2d4141001c43e000d074040c640d410003804440301a550500070b000c000c40350801080007407 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 901883561 1250 901882311 901882321
    0x60315050f0904150e030304060e0f0d1e030b0319020307120203072603030711150f0a0518030a0306050901050a03030f08070905150703080c030610050f0d0204060c0501110a08 77
    0x5080b228180c0d59513540003804140d000040c80c02c681003280c3c01d544982d5500c0d01181031040c03d0102c0342e1040d0180c0041d08404c0c00b0014050118020708088080c0007019a42c00d0000a000b0b900001070018001d00f100c2020011030751781c82c400e4203141c0007207000e400f0b46417001502d650010381a80e4007640c01005044100d0034001000f00c0c05511404d0f00321220f001c9030420151a00901c0190701981c440d40c0c84c5040d1140140010780b408040d0442c0c001c03a8220f42007040304a01c502c01c0042e0b00319800c2503010071107403211001c0a12036014124481d081d80800103000c1000c540542c0442d08441066a0310030b002c0c0e0703842080107210440d038400940810fa51440b00c0c030100341b0a00e40c1c9d99011141e42007001c4100c1c1caa10200f4401c0441080c084e0346030710001010002d141d003214407039900000e0f41809500d1407030614040383c4a42c030002e400d01c091010103d8840a0442d454080c2da1750644806e10443d04c4507a41d42d402007180c4082030702624103502c1c003480c106181c42e0600803038841d0099038403043c1c916222 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 901884811 1250 901883561 901883573
    0x80c0a1e050910090c080610032004140108010503210d06090507050c100501150f12020f030412020f0a140f010501060f170f0a0507050f0301060315050f0904 69
    0x250000300350292200e090101c1c055540d4908a0700401009100b43c03580e6050031406030440d803140442c001407055020400c0210780d1559898108421117140204600304200b80e1211000c1000d03801a0300707134034081004144522126030401590a003641d4544007a42c0e070700306140c0c8817042007281c01e480c1201c120780010360fa54820000d11190700c00c0440003c66940d621a254200c45e03045d01c54000083c1c001a41041d02d0707904201d40c12400c1c0031260100080d502d000380041c2200c00c0101c0c0b11092218910410100354004c012035078000940303440556603600100c4440f26960700c00c50742141c01c2c2028000114800340b00084611524042c40000c2c4202c0f01c0384d85038190b440112801c222034074494100b09a9041200303000751802403e491325503811007a041080a498030312010f6000f04001e40550800008854035601180c029280c803a0015454440348011140c034803584000d8240c041002000180140c0c0c180c1c400c4c400c44400410b4200040c0d290030420a501482c1c40b44036501c40810300c082804990 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 901886061 1250 901884811 901884839
    0x809011a0d0218090c031b0d06110d140417120105040c02160e09070f0b09010e040f09390b0304020402070c081507080f0718050d0f1506050102062d09030d06080c0a 72
    0x31000d04040c284100bc1400205072803803819072100141504080c132007080064418500c0c4070320007085090410960000001548005104403403099807180c101d44c8000d4000d00618101d0420350b4551a41642c44030344044800700c043d40c0110041c454160700040223103401420109696040c0b04441c5404d074800c0c01141d06058408400b64001d0380c91400f406220321030b118507400544549400d00c05c408185040d40150864240001c41c3c803e003488841c00300d0081100b4100c1925402054903480f40c8940c00810000e000744c0c800109040c640c0000880c101d00700040b00441d071092100c02c0303189030341c0d48801100c5015098420a00201e42d010106074094021100900508140d000900c0c070642c0d650002260f0308001d900a0b606880044480170500070b0000090103001c48903841442074a2034100001e5407060001c003680025048080e80055400d00d42d448103108801c43d8514000c2400e1403944951640d00c00300d0b01900b4180350900000300020081003034291000000d1404d01320a1a1803041c0e00c04031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 901887311 1250 901886061 901886081
    0x70503011401200c03010b0f131d0a1a090d0912020312180a0506030f13060e07030b06040b092a04170d0809011a0d0218090c031b0d06 59
    0x1502c120b21094403d1492280b0600c09520000300840e2089106240c00c55241d007683e2409020401e9614109846082c0f00c0504541806000514042c2d290114454420807180040c6240503658020040c00700621200a11007030115046040391685040070740d1b150000c000040224940d800d0400c02c2203004200728100500250941d40303107001c20401c080013548501c0c801c000e0002804020070003070610a58050280209481c0d152560401d2010305d081c0d5107000f0148d10341003102080c3c07001000f2007604403031a120126012152240d4807840d000c0c091444c2200d48a004500d40b441a50302ca2400c814164003e500c1400f03401c41d0641011604008070301b01214041c03421204200c00200356101c20346500e40205e0700e001802d4080e00f1400010400e4001409941a03030f81071565800d4881200005090a580100c9420440c4191031010070501c20900440b9003c0041500401c90000c1d0041483d0451035812020b54030001d2403111208840031f245200c25400010010601001504661040c3c1d600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 901888561 1250 901887311 901887317
    0xf0503120a0c12031a03010e10020307180602031c0203040b150402160f0c06020706021216120306080c010207060c150e0a0c061b020d0b04110411190206070503011401 73
    0x10070302c151141c000f20030f120318400d00013039031317500807105549a5406081a0403400300c0090254140c01c09202d99240c80004a009100354000081994140038200710702400c08641101700202d030760f400000e526900003011020f0850b028003220860703036040d80308480c03003a03070300c440454541e4172007004010500c00c5075550544c0150b401c02040d04145900c600364003100744142440c0020307282c1803902003a441e019070b204406550100c44207111594001c101041d800019504041d118101014400104a0743c8040078100c95401031170300c103220344e042d00800c041d103a040c0100c880340780402d8012039a03248180328520000307514003080f000190004070003007000c0c19000d80c003094041c544840c8504000c805078046502d892401b40070041543c01c2100c00903014000d242058074000c0a40202c3e86446082d00c00a00d01100c03c0e0004082000d10590314101d0300000d8400c2006811541160289911007500303502441c58102d00300d400e0354800503116128448a59485040d13900c2c0190464084d400b02d031070b003818 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 901889811 1250 901888561 901888577
    0x20105010510051c1d0f0304140102151306020415031505030d0e0103020912120c1642110105010f140d030507080a2a120f110a1202070f0503120a 64
    0xc0341900300901b00c00048868095603a0361306d0549409070b407000d00c0103a00e05642180c400610705500404001e903014005c503854821051032807610200911658100c0c0345401305459101c01500d625901000840e8489035075160300365142d108056407031a0003a0b6a400080055100e4241c552103900900030050002e07055526801080c15014100021007910003024400410070510381c42007003180b2620b0105981c020b6800e02d0805034100d01c1d0080500c02400d8440d50b004801c010000c01415280384900c0103103102500740c60070308004003042c192508000c00da42c05c120000c207103813068018032800c542c18a080100e20a070030506000e00002d20640079004d0180c140a48008500000c3c010082801c495aa200403001c0108000b40c3c0044500c0403c41590b00020760200022806c06640d8000806170419080d030344030b00341d0203c800900907009800b250289042c104100089800d000310401c10603000e66a130f132074031501041c4664116103e003a925900c100020340700c01c43c0e03880082454056620b84460 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 901891061 1250 901889811 901889861
    0x130908032a04030f03090f050913030c0c06091a03090d0309020a0e071211030702100e1207151404050c01050702010311120403121404120c0c0303020105010510051c 72
    0x1a400a601c02c0c0e80480c3c10070115005c00d60300c26050b50291109850118202e401c110104000b203000400c8031268040210280c020300d80503422503864961700030304005019031640b40c02014034800c0e11506030005035145c3c902e080a101d2000381c1e449000305038010300780424142411005094450010b81e00441d4461021800d014141501481004192124040c90407120742150407510f1b01c000d04c4100b120140280f203100c079404504071803840780c1200c000c224007a0b5442c1c2207080c2030403d90040a0814000795110402041140340c40d80c25502e030350100840403031b213411440c06c0d02080780d005041d9003044004050942c000c1c4060b20000d401032400040c40403030f518010b5003a5200c207200420080b80c0c03034200010103611841d4400442c1241d4000d00c148a007048071503200070000340c801444000a90000e030b95640c4522242505650030848141d680342e500d04010f4002e1400b0b0162a0140d607602010030105800341d401c40c0d0107c1d503100c0c080d0001c5d00780c4007a0100208510703064001c00c4000346400c68 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 901892311 1250 901891061 901891141
    0x60a170a0207030f0504030f020d110a06030b0f1531080a02100906050706020f0c01090b0f06060901090918060c02030408071a0313050c0303030a0501030213090803 72
    0x5104240c00d01005070380e00c86600700a048890f400480808108040009000090b010003d18442d19030546901c0d20070b44507841c1c01d078490040c040302c1e20741110180c078002801d07643c1034010952602094403e40e102c00c0d45e000c180040032440d51800c1c0d1402908200000c00c040c1c0e148000e003500e1918480d9103c02101104a11001d06502d40c40a0515800070300701605602d00354407413103a0b000e10342c1040800f0038900312014005014562010748495030100356812a62900800c0320402098000208038410320751408a507a4002951140e0710500c00000241242c10310000300e8203401c2c816103400b000d5510300480c46010700f4458402d9421120140f50101c0021101c1c001c90000740910780203940c48904004603246420712961120808070704071102c0307030381946c81d880840e5000b1200120821070b81c00c0c1c9007066850030456640580d0544000400c00200000320360040781a82d00c202c51309002c1c0c0d0b144500c1101130700c4540d074018200442c20808034100150081018680c44c0300f8020007403003551065030034 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 901893561 1250 901892311 901892357
    0x50f0f090a030b18160902070201020f061008150105010c02040e0c19090b03030f0a0f1403151201091101082d0a0c09030b0103020609060c1f0f06050f060a 68
    0xc840350303450003003800752604281102d09289000c602c002c1172986140541050b040d078843c803a42d4161580040c1060a59100380507821025043c08202c400341e0401d918004a0030f00c01d849801ca40f405141c00956034603003401565070403610143e607450700e0424603408100c0203126400304610144109000362500e03459010710280c002d0b04c0f41c0001c820040c500402c00c3e05454500c500d4512a030001c0008004825000e803e440851802d480d041e129401c0d000016110714540700351303000041001000f081038460b11100075511070401925984184586024498240c0d010b001c0001c280705d11404842c007082d407180c0d54090b0300a40b40c0307c0c0003e001c2c0c2c0e00245683c180c03d80510a01309141c1a02c00c00444082d1406040007040e00b1b86015410280307161645100b041040c00022700c50b003400140021955240002e40c0e0040500e8819540c4030302e0b41c8410901d0301c01550400300c4070a8201182810442044d100d4841110070141a41049290560030000c03503622641685080c440e4848411403481040c0d000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 901894811 1250 901893561 901893563
    0x160801150b03010323010c0f0e01111e0c0a141504260c120a05010605090601050d020a211e050c0403111207030308010e090727091506030c050301060501050f0f090a03 73
    0x140d26041031702d448c00500a64280d000c45041c4500c082c1400ca000400040f09801c6440b1400d0b502e40e080d0b26483c0c101e0818004e10600c55004620703d00100b0744540030031110800b00000c88229a44901044000a00d402240f0a03001c249918044040e03901c1c10009554004218401c107036100d04040a00142c410300c41031290101e0703940415a01002c000d003d105d0440a400105e4492400d442c00b003000a00350b110b201079880280e0b40201c0c90b480c3c0386001c2c0f030420a1070000e005080004010141ca213100414084200e01c1100311030440703040301c03240c9074850380b0700981c80711301103034501804c3da100c0d0700109200600098101900342c000146043d024420003016501ca03070780d05502c0e5450000050854000580381040039040040c0c00c02c081b0f0480162014800412880f000481d401d019082004015010000e01560400c0e80c0f84201c058042c0d00c2001036034405d09224180340d0b10f420515088034801d004450105034200800d0080b544814041c000d00c2c081d03011440d1400012070040f030360f40c50413a40 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 901896061 1250 901894811 901894817
    0x9010e03071e350703050307030305090606010804020a140a050d121403070503160c060e030c010f140f040c090908030712020309060103170408160801150b03010323010c 74
    0x2d450152444100c94030001c0080d81c0c0b2403030f101030494640100c0c50300f0724844040c070f9200b0112180d103929003d2102c0401141c020003660b4854034a401c02902074481129808168001c0303200150103917014112060045030082e218010203803d10ba000d409410079520714581c890580c5d040000c03559940c980541025109203407a003142d070126000640300c2131012001001e940d80c2031081201040c0c2c002c050b01d43c81075005180410600c0107540a8034010b249000c0642441c0c1000121464105e0000081400e44c4624008114400d11440b860040310442684001c40b41c11072400300c0d00c041c800c150420b0300140500a0a180b855894210354200c03408458121411031001c4108001d09400442c4000c4020607810250701d5850007240568459805000062080c100c0c803ca5200880c016826540030340f041104481c00d600c120a0002200d8905105c2e4050b95801e00a80011340c2e24195164412202e440f0311450070759013180e0302e03041d03c150380c0d41000e400313202100c800c132400310024021840d0240c0c041d1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 901897311 1250 901896061 901896089
    0x3120c11030f1305030d0c0609020f040f06030309060f080f151f030b1503060111190507050a0603023a1121010503100906180308090d091a09010e0307 66
    0x20480986491203684080d2007600891002d0041a07004021f06400d643c4c03100000500907010720001d0866481c4c001c1a5401916100c068480ca0500f90f10180903203020b6113448032180d945507002ca50000c04c08010030005210303640420b1403042d083e0700094110107069000b04907040c0400110319194a0704c154658070000d00480300c50309030307050301c1101e4580d0340035244242e030510314164140a901c001340c0b0150401010381d8100203c200b05000038138101d101d00040c20784160300b40c113103507070b4a90362401014851070342d0740e03800243c0c1402132003100c0340644070340003c40320000d914001142550403144010b14985500c1000d0034441c401e446510307030b01c00b99003100070744071200904c41d100041207080c5480d604000d4400140455540080d650b518210502c8000c10003d0951401c9405040e480c0b04520200304000f680000b0190440e072102c4c8101202411a4822084010111070041c01d5100300e68818151a19142c0c0c50382d0910000e003500303041070400b807001d401c844011a00d0501113a00c00002c0c520b00d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 901898561 1250 901897311 901897327
    0x30d0c0303050c04030c03030828020a03140f390d0c02160b0f040b03070e030d030b0a060f05120a0c030e03130501081008010c08070908060403120c11030f 68
    0x511881e900943c501440300d05060856441402c02c04482c0005000d00c41d2400005202100d410f0860000c5d814040e2902c80007444051141c000e504801c0350080442d090810321811001f1150741c4520034200740c800e844a6460323154608407120607081142002c1c603d00300c21000b00402c03414101c2c15051201800340d45d1a0a50030845084845640540c021074001900d1808003060074400070b019141d890740313556500ca8900c4405038051156030702c16001c81d20003008003c0b441d41c225400c0c22000000343d0a03240050381c0303e441103044030507400c0380c654070018401c0d040c27050b2446081189034075141750410b82d260451120004811001c200c407030b11030316074a03135455072a0f15526005188250711518011420701d403100340859044aa2406994104003241d03001550ba22000c50306000207254031002007140c0800480e0003480100112151004125503e100240704000095414031030358242d6a4030110b094038440c0c17400901500d1009004000c40076001801032481403008250760b5400e09022507448200c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 901899811 1250 901898561 901898567
    0x50f010e06120709020f0d060803120f041e0f1406060111240703060506031302041503020f0111070f0b09090901020309030318010f06091401080c0d030c11030d0c03 72
    0x10050005020b240500814034030078000154060540c1c0c59048050f1300e0700303405050440c60b8081d05001182e070a04004002a0103100400185011081c15403c3c19480c0d03244200c800d038440c41518010b180d07403c0350586140e03001c0c820343d440182600ca080c29107100d4442e5200c0c3c2d14003800501e20181c07103400c9034003400002d60f040030108088501820191600380500c800001d2980070800f18a407266510303c0000c0c0c03d003482035100c10043d002c010a403d45034144008228903140c06170300f0884c060341c9450301070054403010803100c40841c0c0e8024031500a45052400446920681c80c1d85c1c50041c0c441d501e004220003080a085501420025580681780d00034a001c1100d00c440103032110701240d104005021000e80044101c1740d00c4481114032805803088414002d0051144010314282d0526004011680e4405504400009001d81c2466900e60342c968040300e031610b24044107107503c40710307012922000174096400c40e9000b50140040d9a410070803040803a00340240c041d40c1c1c0000525128500f010150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 901901061 1250 901899811 901899839
    0x6080309010914100e0d0204090b0a0b030705150d090507060c1e0b0402090903040801060603240501020c0f0409022806020109050303012607230d020a030204180501050f01 75
    0x280f11082904403182004204044210f03414001001200551100c00341c0360000805031696014004005040c45424000700958055505c0381784c460a204840104d86400a024420380720020f00c03a89070900390221950180d84000100c0d586c8688803a8120003081c41032001c08010000c580310f05d070031004030b40b0b0950400400f144e11688460074020030500440d01604003103500980c180c038062240e4603a586403e195001e40c2c0d11940e030560038484041245549600034850340d0010a00d085c00401c4001e085040302102e50003a6030040c0e00003200080a840c0200f020300f14004040c2000032640625002301c0c0d40c040801204080901440300075020078241008000d0080c078162000304140d0061741e98a0f038582c48184107442c100003000282901c50181c032000e85800b1400c110840c2c070502e586003081001ca1a145080b20143e101c0c4003078112560030b00c1c14281804c0c030b500400d00f2440d50700f142d08120091403c1311623089585151040b40d80024002d1088070300900140b0703810000c2d503141c4103840410319 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 901902311 1250 901901061 901901069
    0x301090617060c09120610150206041104051306050405011d0a1e080c061501081b0d0e0304081e0111090105180f03070e0f0703060303050d0902040f060803090109 71
    0x140e500c0c040041c1500c004079696401090014500e6556502140025901a040102548617000e0fa100340401880d5928a81007100c0b1905148000301030001c1d816626032008580207043c4149031101d031072503072519610044d44030b01c1c04a4003081290041d284c480403900304950807607181c0e55a081e80c203c680100b2107d030160500d114000c1c0017224455803112840c01071040ca1031403120f42c101c158010850711409440e0081050000c9800c2c80c5070110b6807030600c1c0807000303016001c5201a8045150200340802821205101442c01c1e464050360b181c001c0d0090442c1c1c1e40381c072034600040c0305c0403401c00030a1011094042d481d004000740110761a09a508640b54100003040d070322030070490716030300d641c203e000e8581c0010724003442d2030030103500804a03c01d0564011003079071501510002050114029144600410150356480116520504203901322003040c00050b001c6442408810110405600300d9003001e44090804501e0f0001d03201d0001c04e031001d6400024498001041000c41941d0145660000f8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 901903561 1250 901902311 901902329
    0x306170d052514030304060b0a050d02091009020c241e090703060516230f370e090132030d0504051c050d1116030803010906 55
    0x10080c0100240c00e501c1100a000102d1108980070318211071a010316081d22a0440b00650205807640c6240d81c4945c41200c0455045117040458180e901b8445513044c240c0f030002d03015101d004110303001c00124170300090003402c904c0040e12000c200d90b482030000c2c0920109260083c20a46680042042254072880110425145000402c40401a0080580350000010000702e250b5101c19141c035040c9031640d04050480c03410102440102444214072a04100c01a502e04c688580c0c130300100f803040aa100c42c85901010180108084455a4001014114045070031401070401c0d01904a120034004488440d01104a0130020400c980215a580c01400100c608000c1d035814408040b0b8014040309918201100c40441c038007800352448000000480001e0480b0304282e08414004d00c036a00074040c9501955008800c22200b011034801400d07002c0d4050085c040400c5190412105043c5080d92116144038a840c907c010a8400c00007001550003680095929070406c0b5407070050391195070041500c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 901904811 1250 901903561 901903573
    0x70e1611030a050c010e07060203180d0c050f010c17070204050a050708150102120f030402180c0f210a062904090b0a03020a0f05150703020a0b0714040303030617 71
    0x310031001c022900c140c0e880c3e050803030b250800c106415005103a0381c0d0954945114800022408035000009485c0581d501c0700100c840030809818000d598948060041c050700556009001601e06451208440346042c03515080c01c2d001e544448005a0340b100f01d11000c0d680010790b2409500f45402a01e51003d6525024400f60034030840080038401c0003005219408006809080c035a071080c80702c4885603541c60f18860312046a25002c00302e960003582c00302d202d0720310441c3d0215006080041d039031161000c03a0b805401d000700070100c80056031202180307001425441c0710211042d520801c240740a09035410b070004a0500b820707a5580d0000c403040441d400070361360144412400ca420001c82e001d5503c112000b040882d50b410118492455a40009512031516003010542c5a80300030704004941c006c40d0300c000e2001d00344240401c1841210005001038200707591001c0803a03d20008150050610710308440480c0c86040918041d41190700101c00080e01d954041060402c0000d982207e00a07100103021 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 901906061 1250 901904811 901904837
    0x10030b15041d07080621150a0f060303080408090d02060f0310091b0c060e0a03020a060c140d05090f010f060e010e0108030a080a0b100f0f3b03070e16 66
    0x101c1d11300828151041c20210324802c48604048400410074181008a41007440d0315039812290543c00c860700302041c2d10f070101c40b00f00c0343c1060043c81e08407601a111413806869a03140d585107580182d00c2d03180c00200980042006840d104024080401c00b040056140d050081c02250000c0c1c0682c001c002c55810304550f02000c1d514000c450100741140e00b41814541081e2a101d0054500301c02e1241260041042e08010706801040c0b0100c90351140c4410403078106100c4c400d403100750680f40101c00c3d280040c8a44000d1841550081d43c01c43c10700d108803107914010042c0c80b800d40b0392540c05c1200464446008201c0510f1720100507000d0000e811089106606029200d903890058044003404c001d0444049148141e031580301600c0810081c001d20b03002c0c0604107016011010304003115000034030700c980e000c1e651445142400310701d01d01401000120070b408105011f903800ca46044202180c60714000b190340355410000100109040301842c1010b18102c8602c2140c070742c1c00311452007032200d0b92a01311 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 901907311 1250 901906061 901906067
    0x60302032a0a050a11010c05030717071e2304090b0109051c02120a0c1a030405150709090218030c0105030c0304060c0e0d03090807050409030503010510030b15041d07 73
    0x10b03503908007914040da22035062440448044e111075040701915441c0c899003511241d4440c005610031600d13500c8800c481c0b61911200c00101508858040c0040c61001844e1282000002504980102e600d80000f044404040b50054000d01600351f0042000001e002c01c00500b05005990b413081d000d00b489040f0390319010114901491700941c1040f03c81410320004c0456864041e010b4110f001d000444400c01014030385482c451189004a0113020710b0b80c413210300c7c00c4116400b1a4456544078001d0225034509aa90040511000d0840010302100c840d01090b0550780d4409003480c4c510300d012919407400480281030400e849654002d04004040003040304074521541103a0b00241c4c00300f800541141824000c4400c5045900c440390300030750f201d50040516521000d25410b49941000740c0700420307591130130801158204030005010030824030041003107240c46c0d08281500741803801c020a41034080000070390030500644402e840220081018007481034000c00743c0b4125840780048a400742030044001d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 901908561 1250 901907311 901907317
    0x1303051e070306050903040e1303080622050c0d020d020702040c0f080f0903121503010b0a1512020906040e090c011409120f01051003051204031a040813060302032a 72
    0x1403d826140e40200b40300300c4d401c20841d8000c2404000190060601c0c855000e40144059400c1d0000303001c2c00e0201ea140e240c881d000882801c440011801d415010100010141400a03d0b80c00c114009004214084650303000914002460b8540160785014030300c10001140c1c285035410f420400055210081f031500035549d16042050001c3d130543c2580e890407501d1440c03040c48006000e22080354180a0600c64110700820004800c600030b00140a648060100c19070b5a4443d40d01c500c1c00d921500c00c0e460b03000703007903203004c00204000240c9410f1020300880c500d5400f42c3e20017810b10080d00d0070007603d0002804118440502444c041032600c40c0301401a120780a84000c0070310500321460302510481c403c1060515a010001c000c1c0403d15281c0f110911201241c441a00c441c01800341508141316460111010303607500405142160203000d400a501001c001c0046032101000c128008006150f442d682c00107000035600580d8a20300300f600d102071000d51840340c40245a00c88807100d100c0140b44c080d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 901909811 1250 901908561 901908563
    0xe0c130203060a18060306090f150903020607030e0c031903110c0f1c060f020417120409050408040e0a0f0b010219031407020a0305031909060f0c03141303051e0703 72
    0x1030341800204c002d03000e4004204643c002002249000000d00400640458041d5014020a01000e2010240d4104001e03a800010001c00582256000400140c06580300074080200c810440c0c140280110101e4a8402600c031200d05c9070102803120401c159001c13001ca4142080f82c006015010038201c082a80f02a036901410f1007a40c04ca41d110070020a600e01ca051184d4001c5414011518000d84000081d4424090910b0811409048080f450000540e6034501c0100c1c1e0b49003885c0c50b2070310300e2034070080001070400c641d212403c02c000900c41c0e000b41003582c00b406c1c103c4000902d1810010b0040b0484841212090540d042079458008a022103901805140d402d8103100220108000c0c1072580752040401c000d5110134510004000d00400001400c0d42201103860700074825440507042c2d170903d10912030800094458114001001d116020307141c45d2502c03d05000b012139403800d019042c960080502038100f803001100c100b0030712004000781110a00c014140c01d481100c18846251903040a000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 901911061 1250 901909811 901909829
    0x60b0a1a030a02250311010b0604090c0201020f0705010b0901150c0b06010918051e0603100b150a030b011e1d0307080604050303040605010b1602040515040e0c130203060a 75
    0x40025509806030301103884403080400c60b9070340c00c10003a2543c01c1a05804100b0780002e100c9400000b1b100205105104501c03a0081441d42030520b0403045a000d1700c40c03d402001155000d00c03860300b04507050340207441007030702c42c00c0046402000d42c1d0510010100591008030301d204001880c3c03c000390011003446515801525007541ca544050040c0c0d140201c981c410180416808508980820310b903010038020f10b80c1e41d0400d440004001e201c03100d00350090314919031580181030040380d042c1466000044e0381201070b14a01407581214841e10154000e06d44040c00701e13031585118a032560380030000c021200e1054142110042841d00d004000146010f40074001641404103812981c2d01005400e00425078181122100d01c1e080c0307049e94883c0c20548003240d1190074800080b80d58048802510312440c00c240d1030a0030a4070300d03020480a8100901000d01106400a03651200d4450f8040c02c0c01c51a01030f401403060708002c0c030900002483c1d1705008107020344148140480c941d140002c0c0412030340092 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 901912311 1250 901911061 901911067
    0x6150c0a0b090a05070504090804121a0406050105041409100c020304050406030620040302031207020f04050c03071b0b07050901050c0d03050714030f0103031110090f060b0a1a 77
    0x8050900d09140440058a0380c1015002c00481c8440081d48490759885001980e070480da4030800d21042c3c60703c0c94401441410140001c5c002d81c480d1603603a40d0306600035070403401481d00482180032103203020360302558045d03101d00042c0a10b01f81800b500c074205124140c881c0313032451321419442d15104038600380c0702c80039100c4441425441c42001601c014000082042100716543d2070800000e1041c0b10001e21410114945020300b92034030070994048a4014014141c0f03100d2001400b2101c0d44122012039002c0c02103100034400f9281c62041600c130b0b04915600341e030b8a080000c4094180c40c0c00c07440c1c002e000f003502c1000313400040521688903049407250801313644030f181e0307600103035168020b1030900b4030144a000480b4071141d50540016003e15172640b200030030320f01c050f004400140300803608900110b20400042002030710030200b640700e911802090300c10011400f801101030314960b40050300c8035400441c0c800184030140c0324889080030111100f1500c107181c040080c410f90200100604424008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 901913561 1250 901912311 901912327
    0xf020a061716090e0f16080f070f110d02070e1018020306040e03070c1e08030306120f0f01390c030201021209060a05010801060f0302120309030d05040e06090615 71
    0x3c2d1070004050b00b010000f8002d94581200c0140101c0000c48480032446000200d034001107001e00c0109001d00010700c211002c940c0e81250903940700b00740814510402c1050580e103004554140441c082290f0183d02420700c2e68a8000c10b84105040078000c102c517a008000200480c0c0302194050250f4041c4617405600c90381c1d00c4000a000703002d164480002c5000000c1c6200811081d1100101034a03220400b0841003022020803e001418501504001e070b4003c00200e07071180f802001c81da030040300c91000c032613072210008042406c02403d2500101940c1d190145a584520003116084c06440e032038030205031030080e220896004522000d600b0040c442000ba80d0400d1500c00c0d01215500080e0343c90002480c2080503550740d07038030382c202c5180380018984800401c005006008410454050b90807500c3d070f03141145c0070040c1220744030614000b20b200801140300140c400384200000b8a4243c1c8a0b962120324002c100c1a0341e0500400c0e07075102c1e10000c01000742030b503240c4552110003002420215100e000f0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 901914811 1250 901913561 901913567
    0x3090c0405150d0506070219030c14121b060105060936040804080613050d0e0414071e0e060d090206070203121c1109091f030f020a061716 61
    0xb6144680e40c001101d0200039090010014417180280c1c0076030b007240c10118019040200c150350300040240041d401c0146030300802d43d012100700301031080a0a441410300702c1405460a544821030100a003408000fa55a0b00001400400d00400054030360f58503204105002944045440301804086520700c01d840d01240034001c07002200e800d580011040c14280ba041c9800c4ca50080d1180080d2445008001070380d8080310682c2c5804241d0100007004521107194050b40d0710100d003d40180c210340d941d4002c2a0311400300e10f046014500546170040c8503030fa9540d5000788802900303080c20034031050b005424030944804040b1103074070207064400110035a151001810601c01c500000e9498441c94502084415000008180e048004041d89a00c030780711340301420a80d0004029600c012000f40f0808902c2e05240c0c00456011503d5040c0740c81c00d0741038600308050900e03582c0003920580300c010004130450070080314190241000d0305104111418104c0319990380080203000b1031036110140000004280 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 901916061 1250 901914811 901914841
    0x212160e0117181609020414060910121112040203150f010603020a09080d181205031204050120030402040c0e1f020f010f140105060901080a09020a0f08030711040203090c0405 77
    0x40351013284800a1740d4510042c0650014054240182c0600c81e4824103031810b401100c0040ca0083c01d003034504204c013075040d940c0503030b04c80100d03040c0e030f894441c4071a001d00c59034010024600182801c18540c101401490f140c110b0960b41c3c2085800700c1428002c003148c0c00405503044038010725025a40b036a00744011259010f150f40541d4240c032a15594101d2507030000140060103030201842c21809a45a41c0200e8450b50420060180c6c1c10400103050400d44c003054056016004200100360002d1201c10001451055003100441010200503c8118a45409003602015180c03600101c005407040c0000c40d81c907000c001c5012810f002142140d030090080c04407001102c00c0b140200f10f035601010340080a00740242e8a000300c011001c00214240c0f5140040d60340501041c1d48001e8590b4a90403000000c00c0684801da0b0b0004c1c01420000706c05c01051712010180051740003540d190303503e514140819000c890b06840c412401031040003140c00740011030b8a82d9100440300441c03117483c0c0440741d6610003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 901917311 1250 901916061 901916083
    0x70c02060301030501020a020c01022103100e07120b03061e091c0e0a0b07170304060b06072301060513021b01050a023a050a0212160e011718 62
    0x18030044000024080194060b10107111160261140c0d0000d00004a071074003452040c0104146901c100355000c15102c4000c0c69000c400700603c1d061564851412200e600c4003292a040007407503800803500c0075095400b920302812004c0d00280654103007003c01c07803400c400d48841003119030380010000d40354641c104050428a900ca0341514000c0c18080380050641c411401142d00450120030001243c0d0020f0088450184d00400042c2c0714444281110540d40e001900c251515620b032200180e5694608009200745403103000f111202c003803a4044c1544410450078481400c0c0d151000800407a1645600240d0041140b0001a52403c40c0d180300c4090710840303c001c2020f5032170314040060150b440e41c01440495403500e001e00ca03e101203040000c40ea000e540d0b076134420708041c0464001d0246075400040c0c00404900c005800c018441c039117403020240460b00720021a054038001d13444d0719081101c000f10614203103028007001458a4051401d008003404054109600c148103410010b002e2181d14841c3d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 901918561 1250 901917311 901917319
    0xf030f0603060b0a080304030803010e0702100e0615041404020f0a230102010e1c0509010302073309021804060b120307050c0a03031b05100608010e010c14070b070c02 73
    0x201c0e26070905800a0080d6909980107610034900810b43c488000240c0e000c41e6440301140f49103078200b08034149100000340c080e409622174440c08083d194420701400e24203103400002818989001e40d440c0608030003680e01e0341d0140f403900d05402c8004071000c10182e402a010b80f82c504003130910704041200c0d001d8580c014070441719000c41c48a1024000107c01113083c42c01d90080c0034030016032440c15140c1401c2030310815214035a03c8662401030246006d0040100305040041c10a001600c84036000a2102201484500c5507080684107405219401d40590403001081020b03c40c1036000c9980c19001c0441450a80c844c84005010015960800c0f200e980020781483c140c2c4415030001c035900d07040b02d441203502d400f072060494440d0a00e00784078400c6070b800d9a20f00d06c0c1c200c000740c0081d8a40744000019240b60203182c80240501210b4040c0b4401007a804000048e40c03646c110015003111018210582001441c904a50a00700c445099407044c5d50040c7c500a504c0e182e06005490706005c40b4802900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 901919811 1250 901918561 901918571
    0x210b0f0f0a120c0e07030b030a0b0c1c0903023c07050303041517060a030201050711062205190509071704080408060609010807180905070e100b1206010f030f 69
    0x80100c2d00c0c400e03d003190ba050001d00d44a444128068040d9007007240341da501030380803078001c0d40492060780c903d036085210a0401d51600c000010707440100a030b803841042900c0d407980b20b14400c02d0741c10400810802c1c1c2c1cbe035001c01201c6503c481c100c1c0c0c80f106201800041d42c049030290181d0400c003440588002c08005044035500c69680290841003101c00c4000408180d1411315210300d6000500700700c4c8240344c001c082c0c1c800c40d421036005613a103030050b400507600d0360b0707541140800c1a10b460000348148042c40d51052545454021f010440c00159080745004031a11000401203040d081201d100b529400c580c00341c900d540395803040303d079440e81d01442102107020600380700501c107255004105403890b800544603295030b0001400700070102032280c8541a4000001000704d041a070980d2040c445480c5004521107000362111468014241c002d0038128841d14107110b080400d03080c200c00100043d2070414181240010490320090008180c0c0381404443d41146401038404c0e030104c0c003524150365003044 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 901921061 1250 901919811 901919813
    0x50609040e010603110909030909062e05191716140409050a0f1a132d0b010903031205060406120b06090901020f030615040312210b0f0f0a12 62
    0x41c81c11145d0b000310307008100d02d01c0418017204010086941c00031010309149600d8441c1814001d02c400407100748150795419001060840307800340380e0f003902d035191541d503192240a030030714803d2218103a4101c0d1007405420001405000c0401c00c0c815403100318001e40e03591354401b0700e4040e101b642c81c0e081c00c6442d04000140204000585500080c01001158410007480043c40e0442003202c2c80606503603450310700e56003155a1032401c0a411905109140340104000802d104051050313068020310300400440c0351039003141c0004620501d040c44100b480d00158151858501400100800c4c044041c980d8440000420980711a003200c001002001480b58204189081035240c20b401600c2d518400c540760404141052814002d030ba0009c4186805185551900d604010101d50807408206c00070605000000c040f8070560008410701e11b01d51130310055550300d0f01e0000704180d400c4500d41c414a01d8941100b0300740c2c0392440c05094540c019148003500740680380000d0400e8280d40d000d01544011880d03814 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 901922311 1250 901921061 901921073
    0x706082a030c030403090e190906020f040603020705060a150902030c040e0103060c030c081b0903070b0721020d0f180305120705061e070c0f12080628050609040e010603 74
    0x94404d40c0640e658100d655243c00c01c0040c40f01c410350303880340e680384941c8115000200c03a9000e1b2200380d00c1000b0052420898402c0285a5041035100c140860f90208508052120a0020076400b510b59081081800400c0c144559002e1150296010f55030340400060032038040d040c1102c000d068070220f00145e540e0343c0c1c6800030140c171250124a001900701001000401e014010040c0070301c0d510031016a00e044400f45110441d0400c03040c6542c144120600081d45400860007042040e00414281c2c06042c40d00c1084050080f00407510021540110a00110164444030b1030705401d2030b0389801498000e2101c90702c03115200320b42004c1d009004440d000e9038000310078402407004a01c41c000750303821030780c0d5222030040a000c0e40740c80075a03004000e000100d8051243c007401c00c03014403c0720031504c0c8018a0310344400d0707003010801034030202d101642030140701c0c40c041008242c82d03c82c000403449441c40e0103110b40072180383c0f8495140620340c041004d5011355995003010480d50324060081021b0f564a081078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 901923561 1250 901922311 901922317
    0x1803061508011b091406270312120a0c0e191401050c03070807030912050c0109170a020919090b06010f090303020c06091f03090605090706082a030c 65
    0x7100080d8030b04a103219441e4a0345804110036003a980b07840380141d1905041c204442424840258420070810002d812401d420b000080c014031172052850840d080002818500440c03c0600f1044c24001e00c01d141600001c0d2150981c003085068011401c102e403140e040d500e0310050070f4000d0f8003030400c004440408446998600448245041030101200d0080040d0f40900c03c005a4400e940c0081000ca0003280d041130041110318402d140002c2c140d503171001d200034000e500c5c81d0115040c0d0013890600c001c44da404241200a032900000174110b80b0315818003d03a4035960000024040d00609000400b204071060000b51500382c140814094490356181030413922404907403041c0401d03c88032a60104e03c0c81104840203036a49500149003c5540b00d082210070340017120240e901c00b903903c1a00f0341e0441211700c45a08501151004502c20320149444805da43c002020110540d0080000300b068540c004105074005044840c0000300d010480010108441035001c44c15001e54000103200070700d4404002 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 901924811 1250 901923561 901923569
    0x1009301a0a0c0e0607121815021605061602040b1002010504020301060e0402150310050604060206060f12120c15070206010f1212030528060302040f1b18030615 70
    0x41003005007160380040c1c981e4440b080303c5580240d010301c20007000039100c011148075600f05080601e4080c2c02c003414000c0507101c680080412500c0c00c0d041021168040002188800e040c94000d81c1c014108004140e0a000d0340160540d040d001e001d100c1c06545565114002d102d402408151745c60041007c0680640800d4504078025840c2030400030b00320301006000350040758020448030313420144d9192400c007600007404800d040a24400b002910ba80d41800900c000c1100390050881890300c8400c001c001010b010031180542d0700c00480d01901000480c40920301d245807181c840c5c4030b02e0750300b150501c2d20380c0d100701402c441401101804141d0b500014082d04035070f40d81ca14020016120994500c00d1503040303100614040344000d4183e002c0b03009400043d4801302025400500c006401514002500d5001d11419036036070f08c1d44c090041d420306000380450814000424041c20f442001010340701c0b103402400108202444140c11608901801d4440045030450300a028614160309945040b403030a00c5 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 901926061 1250 901924811 901924831
    0xc010c122a110619050307030e03120711060c0a03020d021605061b0a050313030e0a03080a11070f12150c02010501170c01141c0501141009301a 63
    0x24041c0b00391500b14222500b101c04922a031809003240641520709410242a040034980c0710400d003408490104054a07501c8a8030b0164800c500307141c030024210290322008030000d600441c08000c09080342c28110746c0781e80303501d00c1c006940b418401c480034001c1c000c1286240712028810f001105200000034154020f40b15800d1503851104c6c40700300402d0382e129101022000c9031050000500c1060042442d01000780281010400d6106060024540c01403580049030038203c080758004c05541e10400c2c150000541800130920300c3c0c1000da40301790001213032040ca02507124a410f1002080002803080c041d101e202d510030b000e18910a880a8040c001c00d02402d158400b44400540d04607400040c441c2d94010107850717000419241c80c03c18030b07250744a1246107041a02c6030005d495800454440c4034000c0029540e020038045500080201400700305030400100f00c41c0b1b2100b84440c2110007245180d809100b002481210301c5614a810342c01c200840251020380c1030341402c00c8000e01c0c1644203210b501c48036 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 901927311 1250 901926061 901926083
    0x12c0405040c1703160f031101290d051e0109050a03170a05040803040611092709010e07090506041503060c0e100f14040504150f080c010c122a 63
    0x916450307642d0080186805c480c958030400d070001301e22100b5003142058080c3c6017566601658170740d50381c25117401c0700f0084a05080b04c800034640d0001111422030f069001ca500c003c1506094071604d55070884c4800f5410742c002c08284680e44820f0940c00350445940c4081a5403c413202e904000d802c0082c094002960802d08500040822a0302d110311403182d0751100c0c0e598107540300c503140c0e0700092904159000e1121020410902c1aa60706d40ba03840c1c0e0420140390b2180140401c1114000c3c1181c05015042c2d16810724408032540c90001c24120146d404070140003070555641c00c00100644002500080d180020000c08070511001d600840740126480d258040c3d0909400c041c4200c103144c0360402d000240490192100c900d108006030711000a000b0441c50816855000203070458122a8001d03000d07a0f8401800c1158640f48074884004040410262407400c4800002800108119800400b1400c03503009003200e01c0e00800200300c00b034034040e4244c0c0c0d40781d800c161031071945d181200d41640c44403000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 901928561 1250 901927311 901927349
    0x1b080a08071401110d0b0409080c01150905130f03021c1e020f030418060b0f09091501090e180d020c01031802061605030f0705030324012c0405040c 65
    0x14050304c09070f03c1601d1191454840030b1011300b070041c00200d030483d50168450b09032300081083c0030003030807040303032000e0002892a1a0001a920f0711410350f100501c0035050804104810386002002d01005801c4010481003400601d0200d05000c0013107601d80c590411842c0a145444c4d21868101c142c5030b1400d210041d155189100383e03943c196840010035160320801041c8031304040b40708002c480050441c0046002c7d504c940401ca07290700400d03200004810003244521007480d000868030f422405455892850400e2500000e1006c0e40600400b180c0386120404641984144001000015800800c0e81c1c3c0c802c4110000a403585205001d6900080c1007042e8025464030300c3c80c0c04410241d000f402c540c41c100040c1c02c0300c030010180f42c1e0213503000d000510100d40791000000081001a00c2034002c1c6540385491400c0780c0540b4048000500c15410000c501e03c426608081d10302000b20b45207408110380c01160126040961707030754003500e811074200014030003001000303d00c05041e16400504072801c2412 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 901929811 1250 901928561 901928563
    0x604060f140613020901030e1c14040f05010c02062a0c03160909060b13050106090e01080316021207030f02100f020d0c061103070806040c02010e0a1b080a080714 71
    0x7007940c0d082c0e484040110300c035506210641c000c00c0611018140442d4500d8210704d00340c02c25400e0304400c00500131034800c0d4400a0750161490400c07581540c0e4403401d1504040780400300342c10340d01070345040c0314021100f0700945d56000c0541c0d100d80074242055030f24189081000000c000014840519882182c0c442e040d6460041100d4403c50902d15003001103502e486400703405880c0500c000d90305207a075021804056141e130700d45185030300164800031400b9450841c00810240007580940c0700c0c032082a0043c0003c81021003141d9601c000103020540046150000450125155603181c2c29481240000010001040709440405000b2258015240b1000d00306a4074250407481250040e0481c0701c8a00c0c2c07043c001c409034207505004110000b500d00e1249100690350b8800d5503108c0210780303c5400c10600380740900584c1c04480c1c5602c02405242001e0a24540c0c071041d05000518000e0819806002c8100034442040200f4400d4100c81d200c0d10281005041a40128402c2d104042411404194500 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 901931061 1250 901929811 901929851
    0x5040c032a1a070201030510030b0f2202060910030e0304091410140909010905060a020712020109021003021b0706030c170105010c0f240b01030c08061806060c0604060f 74
    0x40c6042050b40340c03c5160740110000c00d4020840d0080d1054401c011010402101000c0e100e801084031100b12410700c0b411951007030b40d20820540012451906a10068403503005450080c1015903c441050320360f07181c01e07800b401351807402c11903c0c031011030001303100c80c00d41d0001d1092000182c0116515119606100410845800743ea03840003807501628a850910f000c1c0b4070390068801d800000c40c030040380c0d03c4506040c0141d540101542d00403400300c040c401c00d000d2a60149202c3e000820103801550701041c040d0704058402c40c2810341c04600f5403035181d500000254046840d809455407951240b901030010404842d1550000305a61101c0c880c0c3d1700186a0320741a140140c4560100007515a228040e42a0180f4100d808800c030713050414101070a041038074030500700d4003800304203441014001002ca13020607150608100c00403043c042e40781c8921114840005a0028031010750b43d4040215610b44604030040c90741d886241d08000521010341c1c08100008a100010b0015070b500f40342c4a12950 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 901932311 1250 901931061 901931099
    0x16150b010f03060b0909092506080a09030e06030702010905070e0109110307230904050702070503010e070b04050f121020030402280b0a0203031806160305040c032a 72
    0x180d010401c2811034508440c100d1f0740007602d0f808882c4040c400c21b4810b444034a0000c101000e0080c0b041e01070004e19040960107034040780c81c4401708000c02050701d004020040d8000c00c240241c0f8000049680c2a100303400048426410008907444990354081081c0743d68400d00c20000064a41a0400c1200c0243d504a900400a0ba5510b01d444860720000c05120b00d11814a00c800f803d0410400d03e8030385480c090944103603840e13000f601c030721403a1100b0326082d41c51040340020640c02c116802d000040b0340c03000355002d8030b5003614580424070f00c80b00807800d101040c502c1e490052091002c10098803500c0c1d0005800701c1d00c41c40540e228002407907414a040d006c1a68000e501c04802001e05c001d5030040c095202c0403420480484071043d68803807072505250b000000c580c005801c0042001003840305400020140040c0500421651400c01c0c0e0944810403c069080209130300c443c041414070540c0300d0107501130745d000700800d5051260b07801d035820500b400c09103040b002240e000c0001015001c1c01040d403482 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 901933561 1250 901932311 901932329
    0x8210a0e0d0f03020f0720040b01020c1e030106080102030c040312020c1c060b060a1220070f11100c0b06100806040e07030f030806031204031716150b010f0306 70
    0x4680b1910301a0041d412000080400300f006003e0400800ca11800544800c1c10103a400040900d00c80c05200548442040090655101c03280d40c80032600c07801c15240c014030015224050205c000c0c000a409444560b000511a40c00070082c49540da0f950b10081046901c602d2444202c0152602c041e81c07201c490340300e1705521407132004203106c6d608100e900c402c02c09440b94000041d04101000041d0703054101102c442e000503071200c00b500716102a881081510403540702c140c0b20030b0a949441004900c01d002d00202010130018091003007000c0000c010000305002000b070030841c1d2075140b0007085019013030070940b0030303100c2480418a00c1c02c0080300c4d201c0e0000c0780c1d920100b560781c1d01401c0c800030301030716122182c00e0b20500d4800804a400d5000980c40d03c0d1081d502d542c10f60801004140c40d0958100d1000c0e0641010032013000040c0d800c6900c3d04900b01d040201d2512013861454488000c07800c1c1d00b016040209040c0d0300c01e2524141d9101c9000c02200740c8a80600000641c005c03000c40f4964065502c40c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 901934811 1250 901933561 901933577
    0x601020709090c1505092d0f0904020d050a0c120209071b170405030102370203090f01090b070c030c0618030b100f080a03120507081308210a0e0d 64
    0x7003605056801c0010321314901706030345000070484c0892030702041404080301d800301007044c0e52540c0d43c1d180007810b1100d1048910a80356095100012050700380900001d1003051520300000070003100740f04000e089900010822041c9a65802c5038007403c2900400328411018140003030382032030040e0400fa802100032035000c4201000c95a4019070840704c0a120050071005000c00669a5024001000304045035200c5035544845d4114040010311201304091070032039801081c10304558000281c480181044030329401c0215003d00503a41e211541e045502c0c0054009001401d0060401d43c9030100c9105d906104403060b1754040807694065004001801011059002c2010031802031145070032148114602d44003942c0c1b6007511030011602c3c0e0041c10a40c00c070400103014190040711940e20b256110a01388998500b6150080000d0401040c4200f40e24500c4010380501880d0b5041da81000315480702c001d6100c8011031003c0080c402190421011402c100001c410441f0115050904c54465181c03810 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 901936061 1250 901934811 901934819
    0xf05060616020d06022a0f0f0a081e0a02060402030609070b0f0319020c1c08041509030c0605100f150f11120a12050a060b0327010507080601020709090c 67
    0x803000d1110f01c003030300c4464003400300b060006010785000d503506110044201c09079001901e02400d000c0000c20310301c12500117501c0b09003000000f0403181035143d8007683c0f55641700540d801c02d5202e41c00040d42c0d410610800710726030203050380001700580114000c50854065a40358400c05507100d0050045850000b0140402c01000711001c02a40d000703002450120104410b4080480803030304040c2d01812240d10034901c080b08116241d1010b0190840303885d0140040c54182c0382d20410644440d1800b084503910f00c4a00c083c18414103004400f00e034000014481ca007800803407013070480c03090700810f0101d2224840c00540c0003c0d188511fa128080d903120101a24451842034a0f020940503003000c96000c2d8401e141c40b205084002400005003503210384000e0f10a4484131003c903500108150400c600c0c101c02840750380005401d072540000650028409040d260b9201c0e4190705d40344100f42c182350b0070003007071080c0c0079000404213220708420303400c40e81d02d180e40b440400140c802c1020301500c54041140144 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 901937311 1250 901936061 901936069
    0x60b07030e0307240e09040f1a091b0607020a09020c010609060503191403030103060204030b0c09210c0904110f190501080c07080a030506010e0a08060a150e01090f0506061602 77
    0x40400c0184e0f0a000f114007142d81c01081d194601110121480c15115248408000c0b0101030030384148414841007100b0303d0070f180403ea0b941482e01080300c0041c08007090f050907650700300c2141c3d0a20b90280020400580d0f03002d21802a4100b4004221035500345103022840c0561881000100c0310020020480c00f41a40440501109101001d031800000240c0410800a00300002d5000f14801ca0300140d80303d00c0c500708400f0b100c1d130140a91141e080c040081c3c813425507030030080b0100c4000d90411100c2d6502100d9201e4508868152425000f0795107504100030f010500342200f040300c50542e22403da440010f000c014440751032200704102500b44600c180000c0d40705032045544405c0c101d943e00c0c0360040719240c0c403c1e40c0e00b01000500003c1d482e0400c000795560b016000254680094801c0200241440641500c5010087c0401842d82d51101d10040090348540d24000808007800c1405265844424060140550620500303556003442c3c0840c0150903d842280c108844c4414041c00343d90301d030382c00c08c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 901938561 1250 901937311 901937369
    0x602030a0e0f0604120f02030706030b01080f0903220f05040605010c06020a090909050a060c0810060302090f040606171b250213090c0f080d050a12060b07030e0307 72
    0xa0341141c0d0511011460788000000700740b251b03000d42c0c0d0b07a82c4604001c4c4101460248640c210f0342c1014140785003912280d130030604180d042505c0c0b0403030b8055076035030440b860300e18081c041e030302d20304003040761006400141407000042c180c401d810300b8103020980b40c00500c41580c541d4441c060000b10034401020204d02c07940d011300155040c2d4074081c41c3c440d81da01001026104c00100035951900010034140402040344181500d449103400e2069032841c080000007484141b61240d0b0041c103400140c2800983c0d1407402000803004000d00822505403522070090001c0264410188100c40c0200414544406410350b2138260401c0300314549065801040f4500e09070301c2c01c0401020713108494840b401660380d00c403601e841d40c6400c80002103103e000d00f40584d41c0c06040d80408901d62940e4001c0c00640e2000c07900340c100046500f0180c2d0754090480d02140d404824080300d1204514104003c9900e03a050760040c4241c40c003a5071100030301c05002041545071307081403207512221a40031003100f040a02040076 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 901939811 1250 901938561 901938589
    0x5010605041a0c07060306090507080c160c0e010b04030b01170c040b061317240403030b121b041b0801051c0c08100e0d0206011e031a100602030a0e 65
    0x20345081c600003d000e20b01c1c0100300c3c0c020901081c0c0f51441440344000300e20403560300a51358039101c052403c003c01305401500c6030714003d1410b000704500c40d40900c024007403400014040300e83c10b21415039441103040040e400c9400708a669401d0107000040c2c517107030010460003504030b00d006811100650410840100503040f8225000a014450301a0560802d2001d02c01002c4c4c810342c0c800070704403101c640c900304400e10600c50140c002013503441c0c1250000244840d031096040c1000540f550403000002e00b4482810100f4046103d0000484410000700c01901d41252082d107003402242c20300305100d0200744c1c000d03444400295180f03004204c40e07d441c0d909840b025a40d03080000340d42059440c1d40200080640041d0100d500000039410714904522420a11288620107440e894481040003900d81d0b070188102e059144e505190302c0e5a0391521180d0380003c5601c61458880494944110032404000310307000780000c81030007800104140040110b60b918200769943d011481c01c15403c00c81e0030480120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 901941061 1250 901939811 901939859
    0x501140906180306090d02010b01050a171302030316120804051f020f0a0503040210080c12150603090d080906011508040f0804030f060f1a0904021914130501060504 72
    0xc0c2c00c010548041c0700d074034050846003004d0414400c419001a080d0b07480c2041481c100082003003103028881d489010310340030b05032410305090ae03500c3d060a80701482c041802c0c041c0d07241c00005007500d0340011485116401c580300d02000c01090b003030a601500c10020442e00a4540c0d00303c204070b03a28156184590035034001030290700509048001ca403112030790308154041c0e004900d00200b88415403511150121540d421072420440500d0052102c1156004250f000702010f51284082040c00303d54101c10000c4001c0500405c0d105c0c508400c00555039036014262401154800010482245001c61694140c921101c2c0140758000c20400c11507082d40010001d6480c03007001e5000d0700c001002003005100071401007040000c5540b107801e041044420062407180181d14240c070101e81132400da0042d202d0f203001161008019034490001c1414607000c0003810302401d800782c8000c64909000c1d840392030760980988041a65004020748001101c00a024201c00300d5000d0001700502540745942010000b1408 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 901942311 1250 901941061 901941097
    0x5160201090e07021b03060106021c030f020d09031106040308280507020721030807080408160c06030f0e0606060f0c1c0e090f04030809150a0c090501140906 69
    0x900481d00004141c0f400380040c0c1280b440082000e140b03024600c08504110041c0c54994034102c0c0107981c030140c02e240f40e04d000704200300d02c00e0800c0c041e61003c51142c040b520195604d003107002002c001030036403101c04c40102d112151180105500040c19030700c00d070750607106ca038000d440e807081c00001c18401e4400c800741c18800325000017003280305002d0680900410303001480f00a0500c0000c095800300700d181c020300a0801c1d0f19400c04650300c00001c60700328046003041607294680381003c180c90b10030b40c1c401403410b4500590000800901a0000f000c44001d40e500308030b400c1d440c51500c41501c1b0414801049540000082040c1d460a0340c001d28000f0b0045007201d162008161240d2b003400c01c1040c940392380306e049008803618203800500d5665164812110300025140440c41d84100150242c005410482c1d0880040c030001410400c1c24199502d1399080c86140c0340000c000c05c06080b10001040c00920001e0000a26501440700c050150014401c61400c045005080c441280c000c051000d004402030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 901943561 1250 901942311 901942319
    0x8010302190815010602010c140307030b0109080a03021011040b0306270f0f0106091d090111070525050d0b09160305060a0c180603020d06090c18090203070516020109 73
    0x7044480303016040c24a5500d015858054060300b15501507d082c014410440440c100e007402c030f00c1c212b0364400782038200020608421001210140f0682d00f0841c010720071240100145500082c629548081c074140070700c10b4510b0058800841d018a1043c2120301c5801e101090043c5440030075101100408400900e4544280d20f0b00d420224090729000381016521007070103400d035251440c42c1e02401e801e00b04100740b58a4250400c0203c80d10488030b000c4440342d071010541c6c29000f13400100b044d0702c1c1e4054054950195040c0301b529200491510004d25000401682c0c0d82950200c81c03500300c580091200b1260806501c540c2c0100c00c0c000c00c26021340c0500660b108103040080700c1d11020314040d00080106280c18030000d4111114050000280210390b409900c400c1640201501502d4803490056104e40f85001401c004c4d042c90b820a848903070405515100040c3d00411090006903840490326000b030341c0e00d0020b0101e110a0b6001e400003a020402031f14601e85404c44603110b180f0600d004201c403552 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 901944811 1250 901943561 901943563
    0x30c040f1416030b0402090f010807110706020d120b030607120e03040e15030c092e090207051c0207060c0813061d0901181d071d16080103021908 64
    0x200311a550554500b501060034426898031804210850585045251504440003c1e00038900c09103844c1c10080001e002a450314450030f5241b40805002d011102d88a445c1c00e4042e4403501102c0001000480c401801184215075001c1d1041c2080c001c0d029100c075031103000044807131401d00c100c1c8001e402c3c2c0301c44064103498000c10062000b0a4a030031440300608203c40300040c0c100b4940101c600c20760101500c2d0080341c3d82c229840350041c150b101c1c280351821030340380545030307030030141540c1200c0d07a284500c0040e0348141d03030b00248081e501c12420354503070803d00c803161820a0340c0307045078500581c8101801d01400c1e0246100b1142c16014041a900b03151803400a01c4074012550000e0001404555401148082120080c0700400c02180c04040c1036040120302005c5025000e07140107640d0700d40c209003d600702c0701405c0110824401381562840d580341c0348400c142c014460010040442400c00150b0400f40c02c1c020101d100820b5605d2442c030341d20315000c0202d10040030400403506030224100040582c4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 901946061 1250 901944811 901944851
    0xd141009110c0a0303140a09020a060e040f05150a06050c061501030f09060f0b12030f0d0209100203090108070815010f030f15030b1509040f11061b06070905030c040f 73
    0x4445c0d03502003210b030003d507081541c401d40a04405841e03401c100c2413100507550300404006403000f501e4182c3c104c6d100300002401170801c1850020741a40362505110004113421280413030020f0503102c004040d5543ca4040300d05100341c4202a0064000a0108074408407401e13121541020524000c00c81502400d07a8108441a0750700c212116683c0d031a482134400b0742c1c0c1c0180c00010408880d000488115600429100e00c5204074000078284001040c4001ca02558140c030a03650000d407542d13562490046010b0341e6035022580441c049100f8900113a6811310445106115100d001c00c0500300c229001e005483c1c01e1040080101455103e44a1601703943c0ea51150a01c1000e41c282c00c055003a10b035040110101d00050302c100300e1110949030000c02ea0312030000300d60308598481c81510310354906040c03080c65031390008095680654001964010314184003800f0004220010580c1c40a840d20034080e1420389040c4540380e059080a0f480c1c0d074161600b507100145803000da44010498607c0780780354101c000713 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 901947311 1250 901946061 901946063
    0xb010b030613020918040609060c1d0d322a03030f04031b030c15030c02010e07061110090602280c0816050a03050d141009110c0a 57
    0x46012003003012618240c002c000311002c030300e10214540000c050110300720041d2500c1c1000026030031400315040000d9580100036154028070100a003040d2604003d105110f013452075601c100b40078046880c280f40c601c586104041c2c2c00014030381940b00c001c151519040320940e0355080c954140544201114084c40034601100c610040c0302a0f0601380200d9408240820414034042d910030700401ca01003403503000315003d0700c2e00042e0300070200054080c02015034400d80c00044c12103081c0440001d107141050281c00710101b0350348043c0000640000c08078200d5004a041803260f500c403c070100082d42c0100c80c0784911410035402c0e2045d00901d4102e040a030348183c04221205580040d450003c1e107414601034030130f2042280391941500006c04024a032003c444070240095a0018800050900704507002422903071203000c0c0c408424160034050b01c503800004650b88281c0c10310030400d030b4440100105620641070020055040e40c140594180286000b20709a008000d0400644040c072004100b424412 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 901948561 1250 901947311 901947329
    0x1c1208011806260a06020c060f010509090c040e010f0e07030611030f010b0906090907080108061b0f0d0908070b09010b01031b08101a18030f06070e0d0b01 68
    0x503514180010040105044181907514a811000d200584280c0300320415008000304060b4900e840381d00f56030505804203c0100360620004520218480100352240324400000707100c61141c0ea6030060004080701150000030782d8100700e0b1411140d00c0d00c2c0d40020407080320300000151032002d507860002200c201300e4441e01c0f1036214a4040007005218050a5103960075444c4803411420100c500841d8050f060040040e81240440c80030303c075403204000c1c1c81d681a00100140220f0400340b0000d8a00002030003000b90500a0000003200c00c0c1a413405000d09031040c8078400d160800001181800da04500001c480c1a030b194030201006c1386019018081c6103019100c43c003014101541c0090031113605070b6041e41854180709140180080f60341c0c1040902d0401c0c00c0403410342d962601c1c0400058107980005280c1d610000ea50940400040080c0000300448180d40c04061000b00405659085102401e1910350019001030318240c40342c0c28445210381c3c09462081c1100c4103540eaa000040709070002102 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 901949811 1250 901948561 901948577
    0x1e0c05041a16030806010c15020c1b0312070204060f08061006030606080c0d0f052419120f020d0f03030b0d020936010504021017061c12 60
    0x1000c508118040c0e00c0c0190551802e140c001541c40e9400031540200014007400000400980c01e42d001c1c0c508000310b15440380461002c0d04800d04a072000750406c04184030a031185c04105491009488040104100c0c010020024940070326100d0040780d00103a81280c001e40c8032071001484005282c0124041c101043c05490301c0d107021602101800d1240d4005800c0504050003040b02c250072020345a0042c030340031400e42e034450142c40100c010701098840c510046140400b003108500c132411400c00180d00ac00300001e02c84c00306004010103e28285107105003680c5044041000f003000420050000e0302c9001807071070400705600000c800340c00e80c02003900c5020a00071444105136045c0700e4004140800c8074017095071815500072601d491802001000d84503002400400c5200c0140c403462200d4541200140c080e03214400c00d2030113000305582c101c1c0611103911000306650b0045043c2d0080c10035600d1014000d9407017034100011885806003003030a03440b50040c0c89000c00d459240d00da400e03a110380c4400030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 901951061 1250 901949811 901949819
    0x2010617060717071d010203130f061103030c03130311250501020307030c110a08060406020a110a03050706150e0901090209130305030412090e15010806010c0203101e0c0504 76
    0x988060154200664040c104009040d50045e01440b14550080181034000460303100503807461040400140c0b040403c50340000750000000c00d40c100b943c400d80e844600900031103403000c0e40d07400140e1f0149030900d4188000f4001c0c9581e81c00700c541e0300d4000e14010b000c3c941000e861078240300c003040c0f00484600119039070000604d03d8803090700041c8030a10080d883d00d043d54070000c084040454009001c40d08030712444900d0f943e40c0c204140640804030071703240281014035080000b0761080c070168010510340552000c98400c0801c0e0510070070340544540d440c5c0003803503882100510034100400c4074603034801808106482c1e222000351007041800300000e43c003005401002908078000346414200c00c040419400040d5110b02075a4220354048288107a03454062025142c028042e00183d4a0030915410001403510700404807091510a0f01d44000c552a00001143e80400c071080180d003680c0001c1d5441d240c021554010408030004250740e03002c4007004410b905c00c0c0c1c0c64021649001a4011a00384 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 901952311 1250 901951061 901951067
    0x1f1701080106030c05012f120a20011404030c06290306060402041404050a09050307150506060910050a0e100f02010b091012030203070b040f030e01091406070201020106170607 77
    0xf401400302420940d080881c1d4a000d0840000310986c200714600c0d40f00010507c0000800c000c5110345062100c254840305c04940c0101200f800120380a100c804800b01280c0b40031040c49002e020314155403c2181170342d511b440542d000782d0030380380480d1a59a40c032004031200d03140c40c0503c15481103c20000340741da070b2100101890b01c0000b41c1043d11861041204200507002c1d00380d8030150f80d1040d03c010a83d84e032401890ba000b4031001c6000b600718040042c03007204000c40380c4420500310a2401c4104450384510043c89128081c045129802928401e000407145000718040c040f00303030661610701080090385003c07071641d1103141000c10106490450710880950280201c00c40e940d41607806200601d414042c080310b0700d41a01c21030781480030200308030701891710901c02c9407440742d00030300d100c10103052501e000b01e140c1090420560000b1441082d0385010741c0325001e0101141e00508142c003007090001e0030003401c0c0e802044100c0c1035642c2ca0038002442c21000340120031084100000d0440d6143c109006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 901953561 1250 901952311 901952333
    0x207081203240906010f0926065202030a020f06040503070b0405280c05041a100507060e03220e1f050d0f030e0109051f170108010603 59
    0x10b1584041c0850100c0d9a68540e071070b420341d01074000d180c2004400c50710942610443d00540107881c0302c040c003c100300341e0a440c6c291505001c018440450300076030366505c0d141c070102509820b02844000203901c95202d0451218071403102d111000400e10a070f00d19226400c2d000442d007192180560004030700b811265805104441c5418810009881c00c1e240a540d0039440703202c0d002c002040002584081802d0200410030a070600e0700e08900c404c8128403541208481c0050950102c4003020070703020200c0c89041a00a545440140c20b034100a00311511081002441448800404002d014401c1202240207405010761035003903072002d03584d10b9a0280c2d1140c501280d0141c144100d45001d101002580e20354105c4983c081c04040700044d0591380300040c840385003c160b111070740c40328405001c102401848042c83d010b0b280300c0d848100b4003840c01d030019911580e4621039164420420041c1031450140d202a60319169020b280c1401d681e49208440340800c03a080c0c100e08000c1c0c1d540e0f0320900c04c1110800c02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 901954811 1250 901953561 901953601
    0x3070504140a2321100504030306080d0908070f27020913050901050c040e010e090c060c0c0a0e15061c0c02070303020c03060417090f0a15080c04050904080a0207081203 74
    0x100d80c0c0c00c84e8952416a0398a60008621143da68410005050500c80d50000300540664400e5508000302886c0051070b407445030041e0f4840b070003035041c0000d6803179481c0301c01d100301d03007038680c0d81e400ea0710520041d07021121040c800880300580810042029940d03225100024003510240001c9600b84000142e0844000404103060000304000074014002940b541c80d044805080507000180d6030800310310b0801d440e10038507540000c0b01203400803100343e0205e0310090180042d07980007000d599544d46416010000e5581040012081e1070b8007003e4100000100300400c082041c44a40301101101c1700100c48045a65900680000034140101a4140680f5144110850040c980360401d07882c0c94610343e4610f10340e0041404002004000b5031580c5010b009030381402801c909010f6580c6041124410b0080c48900004200400040d00c00a40b01d05507002d40d840035210a06640d5607a0b60541c00e58808003080003517101d240d00c00200344804100b0300c1105011010a16101e0801c4144682c4d15090a0a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 901956061 1250 901954811 901954849
    0x31218061b08040b0702070f030609060c2d1701080109050d140301140d050a060e0f07080a0602030c040b030106030c0f02030a0c03050d0914071a03070504140a23 71
    0x40300c1224168031110307482d00250400146201da44642405071f16149103a40070020040d00e02c900001400340700e50207509003500442c424408100fa4540c02c0303440c8076400e0205002504003a82ea105070080951070071481c1e0109040c107001c0300c5403003408140c481000368070150785a13458500388000c010050255486010300d0f41841c2e0700d42e03141c2407220341440c0014020410b6803542d0b00b8201803556150005001e5043c0c100c41030342c91071021400c0202c090031040d41c02c80305501c07400603080c40044000901408403500c41000d00844482079882c080a58009852010802d10034031001c00c1500e12200111300a0100c0c1d1030004072000345a002822117683e50701d441301590010700100149581280802040315032501d4405d90700c01d20190007034028601820003502d40b02096501184494001a0032419078100d40d10400c46245107101201581c0b0007100c4907000902c09000410007000410812180040d005008400541e1141c00580000702d848146004000c0038040b4a5080c0c10403400b0070005c480c907a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 901957311 1250 901956061 901956101
    0x5010b130b12061915081f1d060402041e0f06051903050415232d070e06030705070218060d0b060406030203070b0307090602151303121806 61
    0x81481800380308000d000130701500e000600b405082c10000c81c541d0150160804842600d40103000003481900304558020640300200c2c041c5017032030300081100f0211018440e49556010844800d095521006010366801c15024000410302071206040c200080c9450020500c2c070070310340a00b040c8400c0c02640b20500f40441080910140c030040f20707206105d00b040d802c001c103032900c452402001c407159139002c50300307543d00e40980c2c0d51411f0266445583c0d06541e0202c0351034103454a455204809403480c150b400704400c000d2040184880103921540d00a2242c208071100e0304660000c01e24a600c02c58070700e80051000603800c0214074016001581c4011080400000340c9001404a40c81d10b004400241c040501c034070020700a60b40740d070000c1014590241c29a01c0c03003a91104d001d13510340c10a4541c500425103001300441e0051000500c9032240542189818050321110540c2c14441041e100c1503082200000154404000e11301524485001d11001c0744603040c62814004119210400d1851a4020380707 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 901958561 1250 901957311 901957327
    0x31c0b06090f0915040516080609060102030712090803031006030e1507030917040801060305100b1005070f0c080c030118080901051c090b04030e030109020306011e0905010b130b 78
    0x20034145003001c00c054404203d9a1909050b400311200301c2c00205074170504180070480200d0030440b401c81113404d20780b46c54080340c440804101c5075820440c0c501c1e006034014030900b0003003000905046040003003401e005442c65181d240890442d07100700d54461001c0000c540c00c1100c0769251003202100d241290103800c00030b5040c0710400350600080c002008144e02c506156083c00b0220102e075040c4901ca100c8981e0782c50f603c2c0038050103801c80d44003d86240c088c01f070f00711141d114079004000c000440109517180a8400d5a030695103908650015201e005072160314070700282c3c020b40018081e014130402064a07103240700c201420348070320500c40e0b01600c03410300340c1c20001090380301560301d0080d09080c0542c1300c11240c06955001140008407040341c90912000b8010310166200030b601840c00799407620340c070038010030070701d401c0e200b1a1600a406070300410040081c0d500d1b1404c00190512181b112019059560a031441599001c0c0c0203e40020390005400b0440011990541c0080c0300d9120040d0070300f019 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 901959811 1250 901958561 901958569
    0xa092313081215030f0d032705060402012d030203071202070f1209180c02030906030c070c0e06030a020d2630010315060b0a0c0b0601020105010b1614031c0b0609 71
    0x10010300f103411f0540300c82c1038003002c48200340011241132045150070704031041801e0942e581e05043d01c040c1d0100352000e01c088002040080018a0f031814490344802244d920a0b04400942c4010701003420400c80b4101040745c881f1900040203410700411a444403c4e095040824020000107083c800b4003403900000c01031040d0901d010084111003d0740066100d00707040c0c00341c1c110b11a030144a50300203000000c00190382660000340c80f03001d0203807507562480d94944582d03001d100025503c055050340080c0c0b1010040c5042d100844040e4810340360450b510035070f200c045625009203030040440c0800400c0c9400001500c040d084140d21491042e180c2c1c8080c2c0e088011808001808050040038013034a00010400705900f02900902d506114240d4400a601c4010620b80b01c0900031212a1360346030116441e580705000340b90586000d00c900301e280035800c0c03841503c46886040c0440725030a204485070900007007800a000032040c108055032f100c4070440f2042d4100e51402e04401d11681c42804200040e8230307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 901961061 1250 901959811 901959823
    0x50f030702030d0f0b120d170c310527070c080c07061805090103080a140d0608010b040519090c030b0a05061207080c060705100501080c0a092313081215030f 69
    0x700728507400200d0b8481000181c020700c5600e0028405151140f049041c0000100c0302c5692b600600c51120300803a19139040084881f02031050500030074402e030550310102010840076400409a00300f0605014166030340e0006030b04101b888000c240c0041c04100b0100d6040340c1c00e0b411000a20f4140c2c45200d0034680003030f08008046c000601907140c04240107240d54000c0103982444100303105141e86448001c80a00086c1c03c4a0040704065404c0c4244201d250030030b401401c0c0660030f8011880ea1041c03440101000070510501c060315038141e944000030118440c4a96540100100a000f00c1c180c50994140031007105411400416076201500800511038040747d007400c1c2110403a0a203170780b0705450422515007115002d0a5400c0d0f403411000155082d000030f1181c03814101650780d0070305a40d552a0400c103c48107014a04107108000d140188101a1241036960041c450300101d96600740c1d42d2902503031034010036501c0c50801410300500070006141c003c0c40c610700000300c000740320b4050300544540c2c03120 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 901962311 1250 901961061 901961087
    0x310090c18060503122b0b181015141305040506030607020a0602130e10050a0b0a0c1101021f0e01051315360b06030d050f030702030d0f0b120d 63
    0x182c04120149a886c8018011620950040c54142691030000010b00184201031200d0700c80d08008513102030700700441c4402c0713104419003000650300c1803908003e0740c0354500540320b010070860100c020303540004102010b80100c180041400c2e80c5a420041072204a40000e404a40301b64090b10030440c8440d4009240880d80781c0c0301002507100c1c4507010780e00c4950001038010340511043d00d010802c1c541110010641180c60880382c5201042d541c00d00080e1a1180c004554000344d5440e203e000450b003400d80e901c1c5e50610610442e51032007011014824000c1d51200c070100303401d40750340d05c1c00c003822804d000c1d0942144486400907202d55013656821510075880401e8100c440d2641031036164180b09061890405000c10b90343c06004150070707548640b846c0303840b500301c3e010040d0381c010074407030300300001c40900601468442c0c5141805060341c00c0c59a40005003200c045101c100200c220001c1203000e20b2103d219080004142e03030304500304002c540d103000312612120340e00159001c1c4016074081ca40b03107002 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 901963561 1250 901962311 901962343
    0x105062b020d020a0b0a1e0906050304171207020c0a050d060b0f031002070201081003170f0409020f0c01050a0c0e10050c030a0f020d0207150e0310090c18060503 71
    0x96100d4804582042128040a0f511040711540003c0f203140080061581038040d03aa0700490300800c500e911281400d0650400004000400070301881d0f029400554005006240d648200f02c2d100c1d94011082d4810380c4480d111800400521040903010801c0310130030602103e01c10300140c2400d012544110701240d002d040103468240b05100e50b203074004c811603001c0000c0c1c29a403032804400a0f002c00b1f54000d04089001415101c0092600400a00d480080d00d034480303000c021055182d00070356100d800c4401d0030030020000700b00c006401c151510050050a081016264071076a503c0107036403c481703009000103202401d009440c50003980c096080680e031002191408201800741c83c00302c4040c003a800f0b0512141c400050360384070454124442824041041c2c2c01c403140b0036001c0074103d8079220301d403040315040d200d44030310201c10354013840092800c0700d809001c0f203000c000001400010384110392010b88005090540c240000b08922204481c1a13110810a01c9858500400305ea40c40040c200c03c0303920 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 901964811 1250 901963561 901963639
    0x703050712050712050a0b15030606091203040e040506040201030c03200c070308030109470411030a0f06231c020604030c0e0711030a0f18030311010506 67
    0x31801000c10b02207803884e0020130012858401c800500403e000d200c1240b05811606a12601480d01c5003101d115038400340440d41040c202406000300044110b0203184580800c0c000480c09040424113031384594040c000500440c03c281c0005412180094000c0080604003031f000d500440c440d82c03000c00001580d241542d41c0b9484c41600070b052881d613400007811030380000000901c151890304200e0507000350f00c0c1c085e2441d40c400d48100310842044240b88042c24480b06900c0420000c0b030403610300d030b44c0300900b000c100d10000a00000c42944100e0381040700301e64500034450400c2d180d00c0307007101415401c401154500d0b42e1b48520202d003865401c070203110740c03001007090f150382006095001c011075001d01a103480710744034500914003a400380910110b003070003c0c00103101203200b0402000401c2c01d04c80a90701e0b004182d00d080b42e079880404981000d0101c039440040c0c100c1c0100080000550003951a03480c40e5840e00b02c00d60a603039025000e80c1c810440e20000c24070305003d15141d40007169000d045030350 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 901966061 1250 901964811 901964821
    0x5041112013603300f0b030303060a0e0a06051201050f070f120e010b0a0b0d0b04090206180307180c0206010506120c0c120d060602061e19090606090c08070305071205 73
    0x892040f00400701c2c441c1d450502c2e41340908500382d401c500006060040248002c0c41d00000b490b40c0ca02040b580e00e40d00c5800240100680003100041c03d411003108440482c406032620049806001180360000c0f00d0380d95101040b000900d08020250071040e00c3c83c5c41111038400e901c00508000c1d4440498407000d40d074400040d040350b425441041d15030f001034070450f4203a031303580e44000c030a030010f49201e90f800b420403030600e005181a10480700155030080c00b643c201717850000341c0c4600c222031000d4141c2502c1a008086880702030300c401011208507291010030f84100e4010000d04048060313000074080e2000f40108244d40040110b115070240504d011152291400818986051503440795155110800180c041207540544c1010741980d0407034084900586600031861800c05c152003180e230407114540040783c44020160301406119001003004100d4600545404d002c543d0320341e1206d01c09540d1007020380780d141c0d0000c222135844622410100200c0c81c0c1420040c01c040c1421164408441e501c0300024 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 901967311 1250 901966061 901966097
    0x311060a0e0306070f0207080105190f0b0904060e10020304050c06250309060306050f150a050d020c070504050105120d0f050f030f1b071505041112013603 68
    0x3001d80300340141240d00d14104040e0141c1200d18486541c0c0044c014604c4c08100100c050007298040c5030110200490301d401068804000c007401d540091020b5214031165442c0c0e40d80344c9030a40590b029610009440d015008140d2501e0386c508a006000c0c3d0052042001050020503c10b2900000f035880d0f50f40d45031000700d22104410300707080003140c0c055030785501018945c0c080d00034415102662820008683c41d18204044c0206104031164042940010b400100d640a000b0b01240205810814240031a511507413041e40c100c403c03146000e0340280010400b07440e00d400b5441c0104001d503000c04a482400160b179403208000e500b450144111f464118030064861300071128031204a0643d00d45034240013919603c02101506d010403105028803e00c9087e0807400100c40e0b41c10b900c1981300d0329581b01c030180f0b0409810700a00540e24440f410a030414251034241039501c240c11600f00009050b2070b910380d94644643c2c1a040299000c18680803448100e0714541d11004958140c00c2007640c0c032283d08258 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 901968561 1250 901967311 901967327
    0x1e1d1903081e07050d030609060308031b090a080a020f0406030312021e070308100b2a19050703200607080c0c030f0c03060c07050601180e03040e1f0311060a 69
    0x44100d0782c0000540c0030900002140d0404c021140780c5c1c092015075070b51051401580c45500001d0160102040440c40c02e00300904000032007481d10074142c2c101600e2600242c1641066801103009421031201002146851540140025001c440c100022410745e100189071482c0001c00029156001807144041a4034582101d040086482c2055840c442c601d0020100c4070251040340081d4854900454940e0405041c0c80191801080d0764140581d07640e00c0c100d038005150001e00b442e00404452100410f1041c2810010030f0288009265003841c520304054420259007890325100310280f00034845589950481c0c07100380c0c001d00c045465011440c6481d04040d55552100c4e4544520020060312031408105510340308c80440c02d0b104182e5a030a1060f00a220b0340710000e166821100043c050306101e20340300782200810170000103c6108003907802d4590b6200760040018021b00386c0802050080c2c00c0c0341100c1007903403034503030000071490350b03886031030100c0400e90040c8510030200e0b076501c203d0b00c540c1031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 901969811 1250 901968561 901968607
    0x1107151205070827010c0e030d0815060a110708030c10060f06030c3b0f09010e0c04090212060901050d240e0118050f0d0206060d031e1d190308 63
    0xc104440d08020087d09082c04031724440e02030b0180c800c44620f0b55014211880c403c50499100c500c1a040d00c00c05c01400d0340c468000c10b07052102d00c1059000000c0c0c200b10990280240c8401150b03515160701d0300d00e15201c0c40b1010340075410300305030b8113104034410313106840125501030038081502c0040c903500760b40140c22121481c0d040003e40a1119610700c951800c410508580750340840100c417030509018001c0309000d10349800c002c94100400510788220a60381c4d00c480b00840850609880380c2c4030310140d0b8045900c2001c82c80340801400150308d4031081c810300404040b40c2101d100c14150740d07054010000494204080c0c008010043c508501d40d40150003c1c182da03200030040f620301c80c02040420b21756594241c07114880d04400c1c0f0348510300000c00b038404154a800070034880e0b44020410101a00c01c010480411103103071070000c00e8017298141c010f1504034545624019214150000d1032080c01a44014800c5d5002c02880803e04044401381c0c081e01c1e0400c045550b540760007104003000d82001c0d21 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 901971061 1250 901969811 901969813
    0x91c050d1d0d030b010f0504050109050603040c0b0307020a030e101d010e040f15060804020328020901060c03080609240a0e130b06060304021507031107151205070827 73
    0x210b40009616a200c0d03c1c0c2031a0980ba81c84514585420071511f81c0180e000b40c90100e03480325000d00c828500203000c0d551161060b15140c41c2c0355241c006990300307a082a22410f001d0786c0264a81d01c10150070070000e508400381034600b4103030b42c2d11416008001e8201000b02e441c1e030301c11000065680c0d0340b06241884124501500c10300004070490101401010190780513014100350752400b01c1c6141c4904502c0e80240d0b0001e0040c501044102c40903500d12944640702d240c040c03002c03200c020051301d0380d011481c020701448e01c40002045060501401e01c1400601035449405440e04005001c4003103c1d99460841b212070451b000c48078140003280882030503420180320b1508101c10000e0051074101e40300c0300a03116035102c915688800050103d00d0005030340c001e50000a0503107610096000030041d020480c000d01d0042c14100d50342d5202346c02c15050750084090850001d04512115402420b101290000f40404001d545000c1c40c005040803070141202c02064a58043c0c681c1c540748140c921101c4062040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 901972311 1250 901971061 901971073
    0x210c0324070314070903060f0506060702121906050601030c0215180304090509070812090a0501030f0216060e0f15041410050a0221071413030f0803091c050d1d 70
    0x1000117885500503120454a00d4102007258002501900945005000260101d41010b01d540e00b0444541c099015002c001c7c413a426074901025082d20510130000c1c006c1030002204d0030301038001020f5a03c6080c0440943d17110740038071800300080c04c8005038440c05099021100c40d100105603420752045030f01c50702a01c1e0400040c455440004107600086602c0c40044030b260322814420303802d5a0003080c0e00d00fa844130407250104001e50081d00011460010a0070041c80c000c4c421300103040d2002c0b4401c007612917650740c001e4009000010018808038100340c034020302120100880c0d03d030150390300400050039641c940d20b43d1a1000c1e0f0130032810320a8021010148228a480002d0348025040492042114101e01c100002260118080c541c003500f003a9452184803030002c1c1000350749a0100c19240d0a4000e6008001301103800d01512a11282c42406083c4c2d480c01e0504903581b81c150156071a40c0d104040c2c400501c865500003084a40381948250003150100003000e42c174590a401101000e00c0740201 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 901973561 1250 901972311 901972321
    0x9011101020d0c09050d030918020714150a150911070c08010905060c031e040c08071d0c0a080109090f0c031104050f07020a020d0809210c0324070314 66
    0x140d00001c1d680c0f2050741e140c0ca0001d45e280200b040a1406d90382c082d004c00c001e0002404a00c0c409001d01c0300c00d1101c500007620b841c00350340c0c40340010658030b140f2074055042030f00051000c100c1e56049907088440081c090152050f00e800050f410305080c41510755090740c844220005407070742402d40e10202c0d00300090040d49a681c1103058084e00c1c10308011034141c000c1c00d00281ca82509541542d002e4980704020a140006030380d89241000f03400740080c3c8a20350410000030b00340d4020031000d0301518020500d03054031400c1100f01c07000c1c0c00003e040740050710814490b5060440e0310280b02411220f800f070001c160340c1400d082c01e40c07a084401c10050411490f08801000317000b020400b1409150040d9010072096407440d8000092a01c00c0d1002c4c001078010f4071081d005031420320525502c860180361818a0b012100000030800018407151006060004200110245040c010b190010b2000d4019024600402811b46444140792500700c01d1070b0040d002045180f4402d5102114881c03003048584860300344 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 901974811 1250 901973561 901973587
    0x809151005090a180c0e010504020f03011509080f0304061209120c110d060519090201270f12051606090621054003260c0d0623060901110102 62
    0x1d83c0c020b08400320f10b86d200004407030515100701c070a803004207420a429a42084001c190300040c11400800700141da00b03000c5000f81007400741c00c2103614581c0086903202c0c41c0c00005000c401d041c0c461035074240c1c90031100d04040350941c0c05404461030107181401000c0d04a16211002001751984583c02403141c82d076401c108000c0b0b034072042c061140607520142e01c0d410122500180c40c170144009000819112020080c0c54001008000c4880c0d1004405074075a00c54010405c542d0b400c0d4011248808072050613000d02005109800542c0b0222041540003814074001600c8084140b00c5c440400a02100c0198080201580407490148075a010300160034459040c403800d021900c500e00e098181d0310111400c0704007642c0b8007800d040141040d00f00a400700e8070140d5032110411401d4200403040310046410090418265100303a100e00e030520785880c0300312151800c076020b0b900f0604141e088501b807000940c900100d25a03122100b00c230360f01d5554400000498410700d0103d016010782d8000b1913000300e544d036 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 901976061 1250 901974811 901974833
    0x619050304020f06130b0904020708032403030301030327031a010e0a060f0b0c0c030f030c1b010509130615030204080c060406080703051b0a0809151005090a18 70
    0x7000703c4a014010980d541000032900c1a0f22820341c6650746040d0421100d03282201606400c0001880181014200d482d030394115881111510304501400f180110b0b000000c0d041c11502d0a03007680114290b60541d0741c0a00302d480600c00320803140c40c41c00030828070038101440e000d0245600031160210303030401c115400d40c039480030300400c5440040b903800900c01d501c1c5485010120341904504080640c0780501e00c8682e980904404106070203003500d40789580c1c408202d140d4506040c403006582d03450b041d5820905000c030781c1810310f0303d585c2d00c0000311010743e0344003041e20410002110021990415141010b0041c801075000b00710401080038214802901035000c2c208a038810303400d0320f1407501c5003410018180318a01998022403d40004101f5040c0700e60b00c00c0741d1007003004180c2c1c00c40022500d02542140c126141031000581194200074000000384113521120040200208540c1004111444001103c0c050140549802000961404050f401c03548050350902c00901038074025042042c2c03091 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 901977311 1250 901976061 901976063
    0x15090f0209090106030209130b0a1505030f060603010e070e03070e0a0c0e0616290a020711011707110712121b08040902070f05010c050c0c0109180b0619050304 70
    0x1850b0b48000124107001c1d008031005c60720003d10b0f00440000381c07282c01c3d008000100c4803581003a501100032409401c00019180341d84610780382c451722480e0200c1030f20310401c001442d5078082c0320305100400000c42c42d4185070b500b1001c103041181041da42440481d25100166020242c03104140c020301030780f100343c3c0e44220724056090b038412141c8800d25050010500c504c03840d402c5003035105da00704404074440300307160000900506401010005c5054090201110548410300c1c120750016006040100031a0204140340007070800c14034046404140360f4404200525100600840030141c010b088404d0180e20003816040c504405400c0c9a070400001c2c843e03806100001040040801c048250000515000c0e0540c0c4070001c1440c1900380300504000c0d4000420440e41501002c407440c00040e020b0142180010301682c94984481312861081d140296070f84005060007000e0b01c0900c2045240d00c4900311440c0b541034081014035070680415014460b540c550300903410080141e03080607501c41e000f10f00071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 901978417 1106 901977311 901977319
    0x61b03050f1803121f09181709042c03160f03171513140619030c17011a01050a03050714040803031006050702100315090f0209 56
    0xc1c1c041d034045101204905c0041c280c0c1c245124440f0044c44c1421003405401d55000f07001f5844503501c800600313000300b10802071079a24581004c807030284102500401003101c969a40c281d1000404a4403003900c521501010306824000042d126002c2d070f42101034101e691a941c443c100707000c800c0011401d225212a42c1802141c40c0d0004920904151081d10004915042004000300d0b4003103504d12420314040c046110355034484005035002400360b0320f585914020308500c00d40503045500042000c0b1000c0c0021503a01c000945001e000440d2100a0107000c1880080005006440002a001607414001c0c004540d2194100782d40101c1c19040000a84004a4950100f40d11681160030141c3c00041400140307411000e04000601c403d240003400c01c8103a03400200442100c000d00701c00c050300d0700010b030582030543e40304d1001030400d80010011a4210300f50032000c7d4000342c440c2841 = true := by decide +kernel

theorem cover : BRFrame.Cov 901798561 901978417 := by
  have h0 := BRFrame.cov_init 901798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 901798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 901798561 ≤ n) (h2 : n < 901978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
