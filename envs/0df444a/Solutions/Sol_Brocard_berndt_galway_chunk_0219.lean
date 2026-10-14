-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0219
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:32:47.159602+00:00
-- url     : https://prove2.me/submissions/f8092895-5b0c-4965-a89f-e3b35f023d7b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 39208637 ≤ n < 39388494 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 39209887 1250 39208637 39208649
    0x1061206030507030623010f1703070f080f13090218090f010603051003050312040501060501080c030a0c140a021c0201060302011d0a080a06021201060e030a1713141801 74
    0x4034050440d100d80c405800c0e5518214000d1500c5003141c0b10703a00c82e0340c6e103d500a003a150030306114241072081c51608101e205100d2540b0358011300c0007101288041e5440301e1070aa000c203595030f41d54000d0280b20114025125640c0c0c0070110044000341685540c0c00074a080c400d00401c0c0341c5242000401c0002140302942c03548111545a0b00600650b8000d620094100c000c40500f01b0040f540e0783d0304d240c6998042d205041d0442c090f8018082041001d00404001d0002400c086410703280c040301c042c6440c000101140a265115182001603d000300c0c2c0e98640f0744c940c40c1c4d429a851208010103540c41c0c5180e0601c80030503522140c4000720a2040c4961416a6416901c810054032081d11400741d410030881039540c050701e0391000164281042142c02d00492254070050380324105c0303400710807409605078008410310010054200840e074010030b404c4401d9a00c01e52003450040000030300421800b51608013450a6400c040c0480d035800018588cc0c0060800c0701c05040190351000040d500030820f00c02e032 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 39211137 1250 39209887 39209893
    0x90602060c0309100509010b0a06032702010804060513020904030c02030706050f1c1410080c01020a0f0b1b0408010917070c030f050c04020f040e07030e1b120a0308010612060305 78
    0x511344c0d6001c2c5400680d040344010f000440c1101041c00003c103509020303031010340800e60725403044110080744294950768103e81c41551301000f1342500040c141d004001c0c002005680e903803001a01000d1011064004160040c0c001d05651410f07180207400da513030718075040e40310f8422582d001903172910440840e8101c0140c1c1c04850300344100e004542d82007045c06040c400589480348090011803030545040c503c24400202c80442462410704d031642031841030750682d41190840c00704100030072307109681c641e07250368001e41504c82c0b90303503019000384420568501c11207441000a00020b080030150440360300d2501a01040c01d56244c2403a1a41d0144185c620042c031000da80c000401c0482e46c1d40707624510560145050781da0000754580040c08036440b05010b44400b46012809205d84140701e60f2469101c810f40c02c04000c850742d04460580d884032034414036031152050218235030780c41d241d8550044e0350303c41c1c510860350301d04094907014001d00004d006480001e4100245032601585030b004407003c0326042006 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 39212387 1250 39211137 39211153
    0x15031a030f1f06080607020303010f060302070b1b07140606100806100c14010e01060303030b040b01140c010209041803021525090308071109070e061206030a02030d090602060c0309 79
    0x481c60105a2102d2800c4040d5038840c00000c19500600030203100b00710642c0555529030504c00e0390381080300d01e0b4009070b0403d40306110b24000030781303090082078101d9140003264090b50000c075000400b034031402d4802800c120110352440705070240011031501802c0100c4480f16000b8007400c003107030301c0441210304591085c101428401402d02840e1001000c074012100084807220704c1c00140d00359010040c5046031695544410810325506120b4001d1006040f18180514100000000c0c0402d0700355038480081e181c00907080400c10b000b50304417400301002810074810540c400440c0c2e201d01c80800300c240d000d4002c1050040c0340c10022040c00380700e01d2403050405011204c0384240305c0002420141001840703055080407005c81c2c10b8102070218180b0500d261101a4030200a00c4030708400030b001d01c1c09000008040400503038806090362200d07400508020496038595000a06e044440e600c06900340c0a007c1d42812503541c00355450080c0c5001e40c003201c45588610102c040248012202040c40c1d07000320380 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 39213637 1250 39212387 39212413
    0x70b01050904020303070b1302040f0216060e010b0d0b04020a05040b0105030a0b031908130905090709181a0108010c0f0e0f0a05041d1c09060c030915031a030f 70
    0xc842d80250000d0200c0303041190740e540307030300405070f09803039000000c501c1c120081d00b1850030303009488100c0800007096040154100c00d2075091069408000c080a88900c95850600c4c025805480001001800e440e060b12890410310340a00c030a80c0d0aa018010364140451079007041e0068124806040e51154030710380d01d5100380070003001075a05556060160500281030100040b41419907240903080c200e40c1e504410340c003561020311070382c0504501030404c41004802c03c00410360008407040c040300811070350108105a040e01451547c020542d60810300035800b100c03900711486061b68060802049004909482540c440d861252510002000c001c05401241040d1041d501c8242d406000c41840c80c0e1520000f0702a201040902e80058040d18990948440c08101000c401c50001c04000b0000e001da01c0d00400d220168040c4500703211b0205c11000402d4031820399800205151030032521880d042c90001005000e24140d80480300c1104188003d00e8071f00418203807030b4054500c3c000c090301140c6003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 39214887 1250 39213637 39213649
    0x5090c03040809060706020901030b0a0b0d09060e030307030605010f0206150d05010207060c0305070f080903120613020c01060e0609151e04020309070303020f030f0f03100305030c01090c0b070b0105 87
    0x1c2040320100300c24050100a911241d01810000e4418040580c07500d48040c0010106c1d4002038500b4812050030b01d0820201c42104200c0719809040b910110f80c50546003080405840c109003891102d100020406c44019416804102502c2c4241c1c0c814040f20b034510004c981c1da00c0141d54003401c0070300400c9605042c1c9000d0048809680c4035800250521099443d110100c418900c24800426252802c100245170b1082500b51500900c0c140004c19042c4603d1036985c0b80240f2020f02c2e90018042c1c04504180c1e6034100ca200c0c5040140d200f907603a01500e0740c2d00c44c0039015900c1010ba003e035000f8040341c031a00d0300401c2c003440f4252842d640d034a84032040c010040283d03010400aa0760410040d00e46000e6251400154410b46003a0001c0030b582c1d14503e0001e140400140b0b100100d41c0003803081010741d0203864100c5050419400b60707180c89484e040740c1c450b40c00401c0d5000801900c00018818124981034000d00c030154000c03c400c085840d0f0f58079410301a407050340b1008100340034460040c000c40c9800 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 39216137 1250 39214887 39214891
    0xd05091203060d0c0803160b070201090302150406060e0a060305010b010504030515040303150b0c0601050612041407170d0809030a0c03031107060e100509012309010e060a09060e0102030105090c03 86
    0x44d5880032005070b0368448142950702c51000b840780c070162804802c0c00c0c44900342d1a0b0703070010050b1008120411a94800a4440300d1081a150261001703a01250601c65290040d03000360210760321b401d07a14123004038940028070340c5110841d201e50038054010501e600900a5030103d0b42c000001d020680c4119455850b11540144124280340e6110542c50112207580109030207010047c09955641012880d150f14101c016840603104040802161522107010203e9135086a808100c01080307800c080e40c4d160030241c81c0d4001c9000c1c0d80c0401101690b2800019400d1803035500d9854001c5140c0707030075489a44074482d2a2340400810078000703204000900c80e9008401042003500700500f0482d20790340784801c7c1c0300410700480465100714420071503e1150321a0581209980c4020040b404440901428401c8072080200c84500302d8800031311010700a4011909180e090b03070546505183c000071240c01401e6903001aa01d052414807031210b075074014401c80307042c2c501c001e10050480d6114031940b0010313800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 39217387 1250 39216137 39216143
    0xa06030c020f0d03090303140c041707030506070504030201031a21031e03061011060a0f02070b0a0e0d1403010b0f040902070b0f130309050402090a0503070b0d05091203060d 76
    0x1040c1010491010078801c2d00f0b1460311036540414140303c1800c0003000e4407181800d40310240319000500c843c030b00c0880116802c03038202c49081c80c101551103a156081004136170029080f0302031403081001d0f00368008d000f0020349100740c90812480700100c1080d8007503030801801540004600f0100540b21402e00414456003125404603881c0540400c5c50a001c042190a40e8540090210a02c800707450302d0300901101021070f241c050303640f2800e42415075907010081d05034052076646510301c2c88a18500d8040754100360b042500c5100d0307410608401d4004000301208848240105060388040c81c3c03090b00440700c120203800d80300c0d045908040561001d54014801d155004034108070004911034140060601c060003024540c0584c58482d41c00b42710100002e0461a001d034100640000281e008000c105c2510700603200140c403420001c0200c1c004982d150812035141c49824400501c07400000010b06008004103024881525102051036607003406d4070f4070114a180a1000400c2030400055030400180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 39218637 1250 39217387 39217393
    0xf0308060a0506160308090604080901050304020616241404110307030506040b06031b01020318010e180a0e03090a0b0702040204090e010509070e010f0b030405150708070207090501050a06030c02 85
    0x561080003c0032580302d03001c8050f031001004d503c41c0074590007403419a400681c0300060501450300c0c7d65900d501c5d100300c103841d80c14050702002040c1903407240400c1d541404a110240786000368682070a52030401c4c070580009000c1c0011100c03005988850003110940f14802a40303080c140c07150b5440c0060a8421103109805108603500000850310400c00e56009600503400d03d4500d04003a801c0c5428080e450445c5d25068940440c00305035644e000080f01c6e0f102d22812110800c140302003004850a000301611958001c18910041170a0190001c44038000c0003281820444008003510180d00d030300410710043c3d80100004070401440384000000d00a01e84014001403801e510344180b6002c4070300300705550704a0ba55403403c00c00c11200400c660b4000e410b210031411225850800940e0b5001201c1c0141c81030400044041001c00c0010000c0b41402a1b170324002160600d010340740180603110881e0783d1350040c811040c0008099105104140c103a407005060618000e09080c02074001d04442528482144 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 39219887 1250 39218637 39218639
    0x609140303040812010602070308030f060a0906060201020d0f09020a05151612020d0206090c19030c0b210f0a0509100608160f12030f02030c030a03060e0f040f0308060a 74
    0x1814030080d8400c500c1620a552030f52152403d24504850507000b810556000700002d001044255058980c401404072003d580d41e40c2d1000841c02c118072135401420403a003080c0c0e0105440d90190058010340158010030805030300301014900585d24101300117900305440d204280310b142400300800708204030340c0e105c040c42c1100d20910684101681e1400780d030b40c8280300c02d0620b406a03060003c0ca01c60020741c4010025820040c03406a2503d41101181d8820403175150101d1200d000b44a60000454018a0080300036075070788003500d1994045450911282800c03a000c58a50140c030344c1c242d009201040500d52a0b071769800c21240101409002d8a4491082d05016170310324142e40200c0740a4a0351030050b0907201034030112040700390300c580c00501040d07403c100240702425105044050a94061030441e004000b0304070705a01354802c03e212071840b0300001400c3c0f845190150840301c122098010b04007156540e40c40c800443c3c1806503401407005548100b8140840d21402c2602e8100100610f101c60350307 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 39221137 1250 39219887 39219923
    0x91104031a07020a1b0302011103120f070903020301061403010506030d0801030f02010905040c0306050111030408061b071e0302070f0509041b0b0403050f0706080405070e0717011706010902090d0609 87
    0x2c00b49005005c0c0b00340e014403051085590143c01c640b9a43c074003200031b50810400b59010680342034020801e0402e1801e500015a40780e02c50700c0080021034005d00200011504c0c0c0d00d201010316043e49505000358200008500709082c000741c0c1ea44ea07080140c2d5035000690a681c0c03901c80c01c1903c14400e0707040210201010030150b0f142d108104140103981c03000034a0501c2c0c4400505102c0c0e900140e00800c0e003050008100003140424800da01c403000c80e03029100e4540d0040c0c1007001e401819406000110880340e204000c1407080350140617103000e5000c407121240d4403000801c01030154040c042d04070502c1404140002c01c46410341e095090640244160507442c2c0400191541141c0e1064401e98000100ca0700742c61814003244025040138544900a031038141c40b40d95482c0745c1e600c101914217404400003000f00b841009032000c450410710501c245175940e9051321040300d00000c41d00c0d80030f0084000008010545208170b0302c9400011701900d494000c10f898050041c19005020f56170060f46040c01caa007 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 39222387 1250 39221137 39221153
    0x6060112020a23030415020f07021507120804050f160e060409020306100303110705030304060f0c0209040311060708100504020f0c0102030c030910020a0c060209010215070504091104031a07020a 85
    0xf08245000359a512485e050a110001c000c104d6610301c000380c410051290290014400c8800d120f4054508400070b040580e0142d410b8030546e840908542c20841d150003030150301458850195000390210ba00e000c202c810b841b5154071b01d01109007001d07500d114040020448442c500307640010003d1000a81c5074079500400d0400b40c048407542401d100c1d02801340209900001e2800c074001030132008000702400c1c400425543c3c03103240205014813140e00200f918080c4168405402150f0141c1401c8180c2410325002d040f0059403015281a40100b0000500e1588240c81c0070740f140b00344d10305018185240006010007540800100c100d098810800c10603064024001180a40164040c00c0d0b0b8a1804a40341da08104201c01d16034030003030040004005d010ba010756040001030b000320006998000c3d20005034546044070382040c0d112042ea000300f001d41c68101c030281089801d030540c140501ca007669440c0d100c52089010060003132606104001d60054101041c1764440c00a00417542c060f0050b48078101 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 39223637 1250 39222387 39222437
    0x607060e0609010f02070803040803061507080a1106040c03080c01090b01080a02150403080315060c0f0c040605030106050102060f0a0b0d0c0602070504051e0408091206100806060112020a 82
    0x10300354060014405241001d100750202640c40980440c1010481d6603402c04500c40500080c100100100114801340d0718501150700400350300030b0340b80c1d48050900d8900c400343c000b900c42ca40031451107510301d6000c10340810407511071a48129600c2c0118207595680006420018014119640c1e4044400002e035a07414194040c15401004184005403841002802e2a507051140c0c0341403400e210400c001546a005d036600b000c03075046000805030311940440d140e8000ca40140b01c80b8410f100301c4018000001c2403941c25802e040e1014000c20352544149400d840301413040c240141d028034000fa006800d01c01c4c0903500803035001d2011861841c0c00000460140a0b03090642d04a80b8159007006603580400040d8010b100980d001d00a03890125505420381401001e41c2c41c07000300381800141000400422101001802007000706008210100107075101070464014111580c11074010030700c0800050313030a124090580d5201208100954035202940103100c88400348079240c0c1102d041c01c40b158043c60 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 39224887 1250 39223637 39223661
    0x9050f070311030f07150804030e04020304030503070306080d0507060b0a08070b120a0c0e040e07090f0f0f0207120513030b0103080c19080a030b130509010c09061715060706 76
    0x1500b040d001d40e0401d800c10800c201a008103a000040c101b1101c0800d00044841c3c03262801c1092003580d072801c060322246941b581441d4030a1000007003004040e040f030007450103078120f66010081e05456514440c0c0d203100041c101004a88103110840c0050310300e8011100007603004d4001840d0740e5907068614030380702442c2c2082e4261013002c101c03241c1c481e00c111321496020081c00c01c140300b41d000c0c1d004c001e03189511403104207001e80d80b1040801d0001320200400401806100010811a855480200010100d0015540040d17003040d1451b00840c086000b034a104682240982d0312103c1410010755072513110b12060034005041e41000404100e000c04018002c40c0141052035440d41d80c04651414040f07007052a0403240c2c036150403440411201c43c103032040200c1c035090009803941e6000010b46620103500c01c44181c00c2c180400c000d0240e4064206c080c403080d094880115998848105990300001c10000d44015441c060000f1108441501030011481d4040d2610303290280586610060350380c1003020b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 39226137 1250 39224887 39224903
    0x60b0304170403020d030f020115090501081207050601050415030f06020a08061906120e03030a021b0316120905061206030c0f03060103063206010806010e0d020409050f0703 76
    0x481445040341003640074000c00c000e21840d040c21980041d60002a1078006030800180e0303500054594001d5000f02d020440b06060b000441e6501d15550000d81000d00400505004030414400c1031000c001c1a02c071500d5010010341210307820102448020800001c2d07a41d0358016840c000004110b0f49002e0a082c20300590002d640c0b190420340203401070b803002e00300030700a111101242100105042d8420180c03805894000c04588207002002c018010340c03598411240400018421500156401000890300c02807030481001d604d05840340d20782c0103030740581e00e542c3c040400110010f0041a04402c550b031682c2004900d041d181d00c0410204c2d00701c07203000c40c680c06a203003d1080d589030400504803041ca003101c44104403e03481c40030a44426061000818098581d000143c0e00440d03d25100c40d107100b0318242d006542841082c20b2202c5600795499408210140c011401c203500c5449200ca81c0031015222440385a1039900b03010003002a07080c180d8450080d00304040300c0f0042800544001e5001e0202e03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 39227387 1250 39226137 39226141
    0x304060e0901060203030402010c0503040f08030909070f020303011a0d140a110a020a03120902030d051819030b0402010306030204050901020c010e010902010e1009030609030906020c0411030c07020a0504060b03 92
    0x4098031458004180074403410307101e001000620350010450358490790a29002c841480c41d0300e031040c650302480c0c000c1d402c0040442c0c000701e4041070010151840c2c0c0300c1102d10981035203443d041991210555080200143c00030801807003503507000c10b0007151310014108510303e095003940d6024100ca02005100003056901014801000d910740110b502c03040308258001e03d0b003850190065a83c81005500a052116030000c1c1c004001080d8000c5441603000780070342c0e42e803e1030080000c14560100c2c1605840400da48014200e03410031b0303840110107006250080141d0390840c1c03034a60b04104000c000b00c0c1095110f08011005031500c0c0a0310340210001000582c60712074500c3c040b82075901c1c0704e0304d85d4440ea14044004001d40c0c1e00c4032450031850b80075900d52800305403806048603081c11940010302120b0030002251304066004031400d0850b0019030990740001004000c00082d140180301941c00c002040c008150300f410800c000308078403440205284d003115910401305007a1070340d55100031408030000c01 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 39228637 1250 39227387 39227399
    0xb010e0c130f090e0d0f0e060408060109020909010e07200f12180402070804090c0908030703020a0309060804030c08090307050d05060402040b010c080307030f0f051303020c19350304 80
    0x340407413100c20b0034041e02c0b00d0304074944000c0c030300b030300b19600c200402c652201441c12075100c00782100d0140c142c85055540940c1c4402450b4040e6221352038070740c0240100701c000100070400d641041e002d50300c03c4c0d49c0c95684661220340083c0c00100105d070491103000303c044070000b5a0f410440c9055064407240380d152620f0004c040740c1c40c44009140184c2c0a1070040041c80c0009001784c0c100c8040e01c4171030100040522186004603800d1985400c80b4400d444002055000c1c950000703003c0303254030301c250b84500c80c050f00c40f101112825019180140030a032410b10344800100303440080d01030007401400315821180d5a200090b980c0040e94800e4a1079000007060106604160050a5034600d080c20b110300d20b04404c1d41c2c0c80c071302c0b0700c0001c004508050380c0d0040628400b400c1c1c3c00003803848400308014411401c084040703803404240700030101c2c050310806400e410030382400200c01443c49241e4900c9840c1c14600400d0360b00e0007032480350004d48042c00c90000407248100c080380542c211100c6004541f12400d101d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 39229887 1250 39228637 39228641
    0xc030d0207060c0609050102160b04060b010c03050a0f0224011503020c0703260304080903010501050103050c121e07090906080304050a031101030e0d110c09040b010e0c130f09 77
    0x440898115005000140065904141200800796202034001141055801c0960081c0141d07429a1746110340f01443c1d1041c0401c0c0c00640e80070354003c11003000307101e41100064810403075810380100450b0f414002d540e200342c061400142c01302c2141c019100040703402081d05074020f020004600041905c41c005002e44510140c041240714001d080031844c02224110f0719a0340e01282c40b000f0401e41221060304462002c03041606000030b000740d40340c3e482742414a00700c80305410031001c1034041e40c604400052150f2090050f640656120741100349803082c0c540c0200c14804008000c01da9022100300c200381e20520603030f50b1a21450701651045030603418400000c09840c0030303a001280b940e2060009000542e0ac40c0500011264484000d202500c81600181c0140441c18001400c6006149003150219000220034100c206804103580c00c211103030301048001201958041d080300141401444030000c0403a0003500400341c89202070911903a008903c3e02d0a401c6e0b00b254004100e5640c04202c41c01d168 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 39231137 1250 39229887 39229903
    0xb0a020a03120b03060609090f0a11100206060109180608060406240e0a0203060102010902130b13060b030601050304170301081c0518060d020405060d0518030f0405040f0b030109050c03 81
    0x14841404a43e0121002076510400500b00f05d101d01035000200300c03501d80400a1070035860711981030320090113440c00c040b201c7c46528a02e0900030560007c8468080348040f984038864041612001115807c1c8101c185103d502d0002098110355620008554000f0412520b88500e10501000c691101e10203104007640362040400c40241c8030320f01d814451036120310030003603100c123803a440140c4a503200c1e40100e01500300a44003a400603908110780c648400e1a40040101c0035040d1001c0009020300301c0e44d8000c031841c5100d002480e40061000c100b496108600030f42e0801c0c01011401d42c00301200400b40c88542c400c0c0d0101450b5481482c3c3c40b09040c0681060f10401505814030fa0f0134041807004203400c4142802d407040c03242c175001410381009109036055401a2130090700b400d40310000180d2400081c14155041c031007540c1440c8901c4007051001040390200c00e01e40d0b0341c03242050b1606090002514500c6108021180c50704000d44160310f00748200804c0c80e0061000741041d5085030709050800140c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 39232387 1250 39231137 39231167
    0x80f0303090604030e04061e03030206060105090f06070303020f0c060603071401020a02040e0f2505040207020a060309030c0f03020c0906010801120308060307090606050a020d020105060a09150b0a020a03 89
    0x1003802000000000860b4240d07000d40c150510304c106805090028004003010381020016298a0180f41088900e892410064038421340848055454420044d140c501038640021b40c04a203201d00340e5100d003450b201900e815031103401c0242c01c00700004c2e41c10a4a801042d81c0c129141c1c010b03010000700740b800f0008400144240552201d442048100003500d440319600043d00460301c0d45504184841c00304009100b001500c400c0d07400b078290780c0b210f481e8040342000c945283d0208031000401d40345454421141101c5d4014003104120b4034280081d800341c50607080c2907040c0302c1001405c034007040031060344103a414844ea000c0e18079491078908003d0192406030216041081700300c010301c09070461207101440960141000310041c0d88500c0040d19080081d0888a10507082040009140303403c00c014150004154003610300003880001c04034222a4201d80140d0700002c060f5003049411400d9101c41320380c81900e0004440c0c583c9441540c103140e800381d054080141d2048142c02c0c14554415207070701600b05 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 39233637 1250 39232387 39232393
    0x1c060b030103020604170a0204020c0717030405012a05100203070f09030c060c021339080f0901020c0a151104030c050111070e0408040f090b0a060f0c021801080f 71
    0x10450b000b00da8540a03a000342000191000c103d0755071b40c10200301c041003450b030081040d5a13171941d250b0130b1034951384144a00041c4003031561190314103020100c1030f5407d031103040e56402c402c0310b5880c00c20302ca82d00751940080181c02e0640c1042c40810014000400241e076441c03000340e0b03a400c14400040804c0d11010b14502001000b03001480011140200c20040324028546203482d903501d800040e1000d15410b5450b01090716103c907945001070384a48208442d00c00840c0405418078072180803010111000b10803001412b2140080c1a00a4072406150440c00c15000142001c14001d000740c5424943c04d015034482d41000c505900a1905004040c0341100994000d803c02e499a1b8407240c00c50f40500800b41809a542d441440b10901040018001c1244984412041c1068280300f40e2545c01401010700c0040b4000000c200200b00340039034a020900582341d0f0084c245007081c100c0d07070a029101c0307003030400c400b0022150140c0c2e10500b1030614981494044500343d49030496152400105204299080d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 39234887 1250 39233637 39233639
    0x10206060f01081f090606020609030c0309150408160e01210803060f060703211b08190608010506190303021b0d080d1b021207020d060e031c060b0301 66
    0x9101c80741c44042107482800c16103516119511002041c5900d49880000101e104000203029861500010111451a020303035850351280c000294603441280195205d5600130040d09049041c04043c0550044840d59201c2c1040e896000981c06c2c0a001030f03011032407400780d003814016400360300c410500500d000304014107514242423000381a06402d0202404805000c80003804940b242d09a00c0c1c12a00300600159880c802d51038041c20010000e0070a62005050b0000c0c545640311501c2411000050460607201c0000c00d170200f02e5090f20000d0400080c41c444140002021500740500005040c040e0008a140d00d818070600103151251605801c0511004030304201180c4c01246020035000ca4034601c840131000380300420310001020344028410280007076070003030252450748040e92892040904030903007110800c1c00c90307440d00c900103442150001002032000510f040304007200d0040c0300715808141d5803000039107c1e0030350300244074030740000003015203561080da15446000c010300440d8041c94215 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 39236137 1250 39234887 39234889
    0x1603090e07020a0809060f12070801090203040b0c0306010c0803011401020c0409080405090408120103030c140c09010b0c011b09031403030c0702011d030a0c08010f020c030a0f1b0507031101020606 86
    0x900c603200c3c000c0c1c020383c4005800e0b400c5071602c0b81240c4504640007284c0d5030340c02d0a02c07168030b01d0380701c11105240011041c138008101c4800d18002c503070089070881c088030360036191079001d03003140d91011f0007440c14400352032451000a1103c10185008002c8980d048185811742c000280c140400040c00301c3c41a031400300303442c000a0042007907500386c5400f030310002c1c119910b030301d04900c1601c243d84200119182c07040c0000700705640b260f07045020305c0c4502c02c2d4078004c4920b07484c0b031030780e1304013119415a1003902c40b0010300c0407260440140114101450003c5540e01c010f5103c0c09040c054810715030300191000b0014420311005044c0c10140c908004002c5256141c80c6607110114000e0f100c0003410028200c0c14040c2030f84001360030204400b4001c0980c0c0042140c0d00c1c0c05007e2850038803404205500300818860104042e10a03181200a220055441c00c1c40d01c041c1103484000202003078003440952036a06000c01c403c025008031031441003008020b030340d08508164505480000306107045501000c100056 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 39237387 1250 39236137 39236143
    0x6030303041e050102070b010501200c101b0803070219031b020409060e010609060503160308090a0b030708040b06040b10031512060212090105010b1e040b1603090e0702 74
    0x44030b0340151801d20540641c0c02856a507800c07220300601070b0340c000700d802d00034040100c0c3c00703078101e58003600c0351442c442e1203c402c114103000300e074400e28090304404002419418506000301c46000c903480c01010002031411000d0800200d5001a204001c000c0704201d071040c2c04000d807420444c85000c1d1050240c41d81e82e00100b8030600049900c05070401d1030006000c540301c3d0741003080b5850303110005212895125204600030700d080e00c90007030914184080018542400300f251032185c03a1006003001030a045480d80a82a40301e241c1094100c1d2044070001841d42c1e803e00514010f1410b95140ca4440c10181040d10060030081c011034421840c000c102c1e84166502c0600c0c2c0b41099540c2404503414103c4550389050448542c000007a00c0d2400600104100d4503500615a000c4034001041e19a01c03140b2040d802c8417402d008400c05060304111003803001c2410b0700d28803803841c244981585030a440d000d4284094000004281c40500310400703280416411540d080040c007201c505980881c68640070082d6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 39238637 1250 39237387 39237391
    0x2040305060406020a052104230c01050c0c06030705030129040e090106030606080c1306052d040c080910090201080c0901020c0d0308010807080c01020a020108060102240702010f0506030303 83
    0x90f103500207042001c05001d0300030b854100e114052403c100c4800842884d205440c110740449103010401e1006c0c0c0400c041c45085950301c0030305401030078001040303001520300d6072295003034020702e00c21202e82c40c20b10f0340e81c20011407040d01c090781c40715202e52400b499048440502d424002d08200c410707003041103484802007a10201c4d00d1030100411540c07034a1007294010030603908050200c0e410b1030808030381050001196060010103450806500d0580d20f46181203813103c2c040c0310740c02003880390035400b0307460709503040c45800525075240c884c200d0f000800a01140c03048040600860005010420060024042400005040c1500303000c000700c1940001c01c801d40c01000001c09c0e0101054103130460348200102100303004040d00014a15083d0b040c0238224410920074030001d1320036208042407250011840b00c00710241a0010f06c4103140340c5d0b0041d11b00c440000e20240c1148500c010580d410090700581908001c0001c018104c681081c02c402400c0d1405c407620341c80217600706070a008040e1000070031a6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 39239887 1250 39238637 39238643
    0xc051903050c0d03051e0c0f01230601111b0f06090904080d0204080601090203060307060908070605071e140105100f0e13150204051801050907030c020f0d0e03010b04020403050604 79
    0x25508092405481c54011b200083c501d82412842d0410005d089000410741c1604000403155000ca890202d9401d031503000e00d03c4a100001d03100c1c101200c1c10760320821908041e050400e458502d05c0010000d140407030124242c00100040010103425080c21034211110304019070740c2da072408029030301184000030302500050146200190b490445103250b07040d10054602c10050360f2071940d41c3c03400000a134106a8180f032081c003035594002007080c02030080004884602000d003d04030306d0840182d5198101c9a802d454450080341105161080800d20f015001e00c00c1440194804a02052508644d4014940c2c0c419211031001480607008504510307013195403200241a05039124074007160840007880c030003060204650103080e40341d800b940107802941e0041e40c4041c050014000381c40d03200c40080c4681c9420660010100d012a8825048407002d8440d9004854000741c081440c1d600e003070404a40c0100161020414121b50b03d028054171000e00011901036050900303548413161901c0c0c000d0001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 39241137 1250 39239887 39239899
    0x30c0f11030a0e040f0c050913050f0c0f0405040e030a030c0905010905060c01020405060301061106100605070807110a0b07060509011506050703090506030a050a0e060403050301060309030c0f0c051903050c 90
    0x780200307544640040c00d401000b41804d1121030701d01b060240035074110941e480d219440050508c01c40101a00c1107a00c00d820111440c446500c1c3d1645441c0b071a4000286003c0c080740c10000416503403924054007510002007002550b8460007040000c00f102c89195090781001420541081240c0e030182c0404241d80c003c40e030199580c5000c1c11818024440c50340a980c000c0b601000004500d070f0001c4282604500392010341c0e0050750307402c812800e01100c1d8021000402c1083c803000c170106460002414910340b081b44080d0000c0010400078001c0d00007640b205e94011400940d0008100150103090342051600c0000e000c0102100d07841c0080c0c024601030704013007003401702d02d2506040c400d40c115401400047d00c1c0c140d50f07003041c2c00094060881150450103180c1400101740901c1c00004855100b0b0381c0582e602c41c250790034000100c01600102d00140c00300400040440c0c04500d19100c400c0819100f81010103040e882c0c1310038080d0407091501c1500803406649010008074a02103110b4214075411945 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 39242387 1250 39241137 39241157
    0x4051b0a050d1802030f060405061803070204050108030c010e010e0c01050c070b1c0c050715020d090501050c070b0f07050a08070908010f050907090b030a080d0b10030c0f11030a 78
    0x845090290b00d007002e406070b04010480c1c5007801c400b41d4480b038032802903041c0e03110030004015a503950801640c5c004c08a50040000a01100f00c1301c0d5040407565429040ea0710388003490300003605440081e00f090307455800029400590f010240f24503101e9a41040003807060b4000444229280c0d000304010301d06002d40040d0440c15880c050102c2d03c090300d010800e55444001c0c0c222141d00031050111490a411318080110b2501030045d42070361030310380d44000a15004040404003401035005200c0910380603807200c2e01d80e00000c03800c0c002d403440703011180c0c80300b501d8929504080da2801ca0203481c5401e1544c00405100560794444121043d40c1d07201c2c01d00d203219444184084070003030120342c408020341d46004480c4440e801c9541016014040d50301c1110441e0307845a1852049440c0c000441c0d03031592000142c1310024150401a20140041c0c2d00700040a040f4000810f4031104003189860010b642d501044084a03084145840d6078241031401a0b9981c01c1c0d440c94541d0703071181c07800c0c800074024900c0c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 39243637 1250 39242387 39242407
    0x605040905040c0302150c100203010e04020409020a08010603030c05060a05070c06090f0816030f030c05040909080909040c06030e06160309050c060406030c08060f030c011202070602040f03060b04051b 88
    0x2010025a8090b22001404a04086c54801d17074205104800c0c450151070110981d0010a0083ea8142c3d0140f04800c101c82c0c82d107170b003000001c1c140d05504036040007242c0c1c000580444284240c0c001107019860b489001c0c0254600300d07007407404c01040c00d010306250070280305010340c0c040c15005015070711030400991000036061005081221440041c0034400029201500624546000380c4840c42911103403220490040e0560568510542d01400520180000c021002d0960407528010b07020344041843c040c1071002081641380200c2d01941c401c84021002c200b9035070b040c0325100300e0031003c0000d04150305001ca850351030300c55480003000c00c250300c1e0199102408001d00846d641500014001799849a0341d10307020f005050014040b0340814020b50000d4141d040440c95415001001400f5200101d4980700540e11001c00c0c0002c2c0c01081e60901038080050420300c0101b001d0b10b600c5040c120300901d50b19043d0256440402107034099802e290900c51401c10034102e4807050b154040d034540c2c4409810b4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 39244887 1250 39243637 39243653
    0x402030106080f190f021b0a03140a030b060a0c031101060317070201050d1a03011508060109020c0f0327040b1003051e0a0902150a0f0c0f02060c150907060504090504 73
    0x10718540e00500d005d011810800c6039900070800c0e07000c1017440c3c0e6210210340150702d4642085003000b82c0881c81d902501c81441a81400826600d5201e050000d01d80201502244958200c00e0702c49000c5404080d00d00181900700e612000b2010b03c480003070120358107582c0d0300d003401344008844034160b400120700346085a014105a0342c54080041b810400c10046076001d400d0b0138072501c4058041c0d407820700c60040854440c2c103101c085e50354410050080ea440c207d10303078000f980000b100301c40340c3c09501c40f03406003108148010900f455507803840c1d50315290b07243e441074441000280b08504c00d518001910b4540d40f03400c07040b040c02510a050001d586e548908000700201000b01d411440b21504008000c103400c040d0f800801d80700c4c001d4410400da04076003092141284134518207080468503420905107420311071142428498032528050207601c0c443d90101d08990082041086c142d0040301080644040207007070940d005800c40000d090680c580139014005100d00d0007803400b51501c4100090a00801c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 39246137 1250 39244887 39244921
    0x20c1e030a06050103020a0b040605090613180c030b0103020a0e150d09050106080c03030c0316020303130303050306040c0e060702011812050303010e06090f070810170f07050402030106080f 83
    0xd000d5840e000014034103070b40100b6090004170b105010801010909900401c16601a00d4031522440d15004800082000f80d402041038180200d42c04480840d044100d00c00c103841301c210b080b00120f40080042d00207000c2d01c052218641c1054410b202a000740b5034894044013152805a4100705c800d1501407840b401b910810503c2d6038600e05000c079880412405603c80403c80f010075083e034000d41c11740c0f01055100c1c8500381c68034000c0d600902512a420314103a4030540711920003011649400031180c0301c2a81c90310250b105401060012080000324106401000000000c9142031082c05821b900001d01c50b000b09400a0304014403c4101c0e041078001c003c02c5e0024001c811703440d01703401e8243c0c81c1040d81c941c02400780690b00c03114403020400600707040d01e6150041c602d60340d035807000d80d0700c078441100c3c0c000d0010521105d96500010010b0700c41c0041807050403842c0010301600400c5d14440c3c4c014a071048e10ba015600661041004000d0241c0c0a84010b421803042c13260525541c0b00d02190304100c41c40 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 39247387 1250 39246137 39246139
    0x609020301151209030e190801150305060601021501090b060d060801060302150408030301060c05031902010501050a0506070506060108040507030c0b0901080603010c021b041503110301110a020c1e 86
    0x1000001085200000c5400340082080741d46030707248180f80790040e0059948002006003c01c1c142c07541140185480180724181504c4c2d0130b0000311051380e950025007540d22051641e602d041d0f8012003841808000e00038658040c200b8001480c4400301c169140081850500c904004940e8501119406903120002c4441008001b003040c45036680307039020320b030003802244001c902c41c01403108422000c4002c40305036400c80710030700084e41c00d681c0b030080151003031580a14111041d000c200090100030f05880c25000001c5855800010b0a604100070b010312880d064220510130310301444148006200080c0060b0b01100c2071800300e00743e8403546016442c0090a41008005407041080805c5034108000548030041b001d80e94008151528401c0c90300700c0e580d29082400503081000b0020b00c100d0003254000010102901c0045e40d0303000110001d2103440a50030845d1040d0010028828600d000d0003142c01c103080d84804185486002e29010390b8500c060745841c1c5c054440c0c8054002000e00303280b414809004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 39248637 1250 39247387 39247391
    0x30304060609061e09020306130e060906010801020702090621071e0603090b040210110a0c05031605240d020426070602030d020309010e01060e0703050702011406060d0609 75
    0x2400d10308400500301c0740c0140300b4510310b071400c00141c0112030300c59076a001d411030501c10a01814480b8640281d80001d00c0c49400c440b0700c0c0400d400055a80c41a08032026004001c2c12203404c0c4144528104a4103038000e1150781c0c01885241d02507901d14400d25085801180d6606008021800341c42522050500060b6640190305000503800d04012900c1e950040f014030544400e03454030003c0e011100d60a41c041e0030500e4800003d4014141019100070203070b13131410024881c11110703140c01e00e00302c04a101102d4076519502c0400c00390400b0082c172004c40b585400021601c0f800c240c0801c3c1408082440e118800f98040001265644444110360103000c02ea40150b503941c2d200ea0301002003e462183c1c8135095460044d0021700c404001c9500c20690b03a0941c080d6107084000942500a5000a000c00040c0c0d5a61001c85101c0309007441908001c00101c49601c5644c40d21380005011140028210701c2564100014511403504600000b503008078200c400540f601c2075021050003d1501c0d411001e0040c0c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 39249887 1250 39248637 39248641
    0x2115120f05011b0c0303020a0c02060a09060305010e010b1911030d0504050f0601060206070e0a120303050613020313030507051504050610140303030109020c03070807032a0b0705090d050303 83
    0x200081900540460107003000f404000126514003801a81030703001840050030714064000040e1094000f0f1000004901d03003c2d0781c0034000d8000644503401110001d010a0303001c1d00401031103415003e5a801001c1c090210ba00540c50002c200e452440b03080e0030141c403800b9010380a03141c14007a10a00105404590407291103951846603500100402c1d1340035100c600c500030b52001da0500000c0c03028180c0d40f056002d403c1079210120180c50030042c0f1243e4550000e8a240c000c0342100ba01d480780841180a982d021401e0704050091058016142105048080c01041001250700900e58410610b03581850705a4bd10f2605050080c1480b20401c254040340c24800140f106000c000103080e4002c1c280e403044101c3c00c554504802541c8075001d0449a0190003c2c401001840259806040f200510805480c5080a01c0c2d644601c02d511065044010840e03018048480d10001048044600c4c4024401d001802860b22800c01259008285008002000038440ca4988400ea100100c10b944141103c0c0c80b4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 39251137 1250 39249887 39249893
    0x602030a0b0f040c090302010f11010203090304141206040b0c36010302071a10030b1f0501170a0504110a061706090f0414030f0412050d211512 63
    0x50903400740124460404050601010b00c0e00e80700300e6803a001d0a84a0f04182c40c0795070700640d40c007d4800b842e4001c2c40b808091480241c4003e0008511618024000d1a5150b09020851814081400d125800b0b40060400e80821180010314036411942100620081e5a1111311000051050310220f82c1068000304030648049144404032094956201d951524000541300441c01c0380260000a402c0e0992501103081801c60380e201d1541112040615201305501d948840311805000d4582102c4100252a4000c00141012540015117030919104441c00c05000e210780c0801000b1341000c036403e42d2000030408014841d0446d0198410281c10203090b40d55402001e04070020054400c02c98145000c0019058a0702001c0c0900c210154407813400306482f5912040c00000c15600004035620003001035154025084020340001d06880030080b0094a044c40d141d4204101e144500c010700402101503914040741c0e42c00c140900030741080c001100400c032510504000c159502000b011801d0f0320581d001c1c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 39252387 1250 39251137 39251141
    0xa02010213170c0d0204020c010606090f0b12010e060d06050c04060305010b070206070b090109020312070615080601090902060d1404020a0806010311040f0e062701061d0c070602030a 80
    0x140c0d8a2910410500c0c0707558000c00c9608120303802c00c900480e00f105203072840c03500e00341414820581c0054401810018094180c038210303002900b224020650408080001d2003444550401603d0032001c424100007104c23200395105001805001d00024035480007820b251a840c0f044a02e03144c11140900090800c600d00003801c0c0e10034040d0f01c00003428a400071409904000855001c1076025084500c0c210080c1c8604040c940080c144280c2035484004480140c0d4041182d0360300500d240300e01030303500c0c3c89520b0007804652071244500c4c280c41d01d801c0104222140883c07020304590150300082404c445510000e040c17031148001c1d05940350f18100306403091407407072003103144114400d0700c200011139211590b007591035009108c000e0500ca607002e0711082e5405c4c1a041816040c2f0030100101362070383c0c0d03400c415003881300440d040090030002050b0042621704003170007071214041c6807000f00501d60400c04079241c281244542444528101404203500111042c21030340700c107800003021504c07810b0034060140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 39253637 1250 39252387 39252397
    0x70609090c0504030206070308060a0801020406030b01030c08090c270a06060216030804260a0b0603010c0c03080c180d14100b180c040b070804050306070509010801031113020a020102 80
    0x44410710789208006424051011036068903001070003641441a1640d08640c07649000b844c031034010180c00300004094809001400280075661404070794000d500000404803007000203010100944201446a551008500c1d000c1040081c0c82c0c2a8228440707481c1240080d241035208400000c4a90030030240001c16803101c0c0640b00c00e507096400d60003d0201545550395075003c05052242c00301b000b003028030203140d0603c02001205102446d143c080703241090500c3c5002006984406c4400100402071074203100d40c000142c102e00b0004541d4601d61001802040c001b0300e00500381e280080c540030104508050145090f4005042001440480c0341c0a808210185180310b41d511030101c400ac08010382c0d0042a43c0388901801003210300114100804414802420800d01c1c3c200c1080701103416006c0c1c000410100b40a05503c0713550741d01d000185440d0402c02803810041240900c05c6071020fa038031031412411240c0050f01440740c081a0400160035459440f12900f9091002400d1300303140c1c0e01074000e00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 39254887 1250 39253637 39253649
    0x13032007050f0409080f03042306062e0e040f1506030e010513060f0902060307050705070806040b071d0306010315050f010810020d0605090109060e1b071211070609 72
    0x60340c00b8201e1028041610003820004050500501080400b2174004005d154414081c91244100002c65490310036404908485c0e604550059400c100c400c0c101464640091240440051101c914a1041804c40d00740c5000000800c041c026040c1c046035629048a00780d201c8107801000301d03038008142c0000d8401e0381e00c1848007003800c0805c1d140c00e0380d1061003258843c01c0341e4080340d5046415580c50300010301610b143c201200c0c0d1b0b250394550141e110030018500c01c00541e2034140c2d0ba20094101280780410303903481180168000c40801c0005610b1000741d0f50404d6481c2000802d1081c40c1042e550009207603090941c140c80f6140000040c0032200c0c0e04904500c82c9084104665198a480c9040301784090054000a601c42888200c12940030350003032900013a9100c00003200c603250300016035148001c2e8440e81e4090385400050180c029924400d5400261002900c0f00c03e0503490041c81142c003403507030050004400404400c03000b600400c540d043c580d1052080d54507032a19000301a0800305580110 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 39256137 1250 39254887 39254899
    0x70509030613020a05330309160803070204050408160b040204051806011502010e060a0b0307080d210902030105160e010c05030f030a1508010e010b0103060308031303200705 76
    0x2c244007108031584021115009042200c0a504000921541c0141039020513505484600190044400740c02201400700340c0043c011b80da4202546140e00d8403841c08141407100d10001020440d1b503000104440d44544d05680226259407030b420800d030345010f860122001d2811a80d1441c04100307540348102c0c4914421201009107844215210004a0085c242d90f6002da00c50001809034240074139400345003900d14800450004000b004070303400c001080d51900075090b15078054948520701417200d880a005c0c40402041e151f855401e006002a01c8081c4480480d041000b030250410707480c1d001b241324142c0160090110303051505080701a02d1400280000007000c802c582003040d8401e82c4404100c5410000031030038024030342002007803540b01601d110141503a13099a102018080400c1e10001c0c5000000060040344164259003540d4142100728105860110240002180c000950390011450411840c20310031510741610b0112951112100c007660300400404a2900020300509480d01602d807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 39257387 1250 39256137 39256141
    0xc110d030506130c05030a090507091109030d0302250204060e040f050c090106020a1e14250f0b0d06030804270e060f091614030f0c0307050409080904050705090306 72
    0x88804a40b4680c0000c000141704101082403903c05030819030700c190250096421065a40c0c1d442000c07994148007110710400c0100d540d07806480c0501c103843c00c106050805529100034607621003142030400221035001d81400a11f00c0554840d0380c03014014003448c00742c0f140c40c3e081c03034184282d550303813040f4044132a4820880310010a0034041d000c05d04031000c58004000041903036450589100d21580c0803030b880800c03614064085010075580c1c1c004910030801501e1900b80c1100650804400c415064100c13806040c41004084000024001103508081503da29082c0854804014040766400988a01c0d000300340886c40511601204100118508240450b01d10040d0200192042050b03c10300a400c40c0c80028103007400112226071100040040c0c40859507d4122414800040e41001099900343c7e544402c582c10100306125000061100a0406000c4040001d50301d844030f00400340103940710103550303081162070703002da602c504c41c01001070200b407030120001421500304006242c8a1310070f501c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 39258637 1250 39257387 39257419
    0x41a031807050906040f090209010b0a110a020904030c080d09050309040c02070f03020d030221070b0106110714010c0203030c0a032007150e0d1209270c110d030506 72
    0x4140007110030140188216940e403000f000010240e41981c06d030026211451200181e80303078200c00b030103420300007215034403200ea140006104002c01075044403123034030070803404025941d140d095691155062625044208151401c210305018007555071181c80d003000d18103810004040040d02d1010000d440410842c090702070704a030740e10350703902c5440c2001e40003900900150904101d641c0e0f40f07a000c6d0044075030f0784542c03054078650300700c4829001001c1f03140400d02d07000300203000f42840d004124901c0c100c0d046004003150140c03034550502c00c1c40300407031969a000340c050b40161407014001e9002001e80e6215000080615200c0340c0c1380d02c00301d00081d80300824014030306443c442d0b410301089981c01001c1450910071451204080c00700322009002d018089044075075a0300e004003030020703ca41164100c614482030042e0089515410000c900f400580346100308034840c40b024030303014000e1000803400c442800c0e020b07948440800b240340c045014402a904686805401403401004142c1d860041c0f600720003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 39259887 1250 39258637 39258643
    0x6040318050d170403080304060e120a0e040c110f01021b070b040905091203090c03060604020a0e01030506060409060312230405010804150f0f0b060301030203070e0705041a0318 78
    0x80a4a0352280c2c02d0844000821028601c1400e14000401c40b54903003a01ca48075100980c00c1100c0440d003858682c0b110130001b603400d1159040000c4100101d90078444020009040640040d0032140550764070f600420209228180c80c015690118040d11001041c1c140114042d40c8003c510300da11001180c0c40c002c92311800116242164400d0440c103040c42d0509190780091301c00609208050b20400300a0341d240120b030002907001d1802203006007205600f02c000d040c1415001001548200d205009205d00180c000070b0881002c807007482c0009140e0b94400020f8a00e0003681c2100c08918070303011011007000f03a014002c03100e071805600c401c0d641c207a0b40083c90310b200d545009006111241480100805c3d4050390007190841e1141e03030358100e40d903501440082140c9101c6001203003544c5030384820101c60000e1003458640b01e02510510716660441d00070075924400383c0b0891042140032800502c07181d1107034050342c1c043d04075262950f42008003c003045410f0780003583c41201e43c119400b03071103050308800 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 39261137 1250 39259887 39259889
    0x405060a090c02030d060e130b0702010e160303080714090f0d080a050301050102160303020d03050c0910080106030c050903060408160b07080403080c1305040b210d030501120f02040207020a090e06040318 89
    0x2030300c004002381c44965180e1032843c0000e0885410340d0f4a034071120503174000a104080080c41c9620200d04841e03c2c6080c0204a10000340c81c01c42404040e90401020200c0303801150000315003a0ba520014201880101322190385440015091350000b0804d4040964881d0085040b16800d85c00ca840611400030010100c01c81844002d001d640450b0320701d16032a010741c01c2103500c4040020382c10300302011403000c113200a205422000004032501c00611201d50148100718038098585019030401d001e00e80800e80c0e030180030744060000d400101d407900001c5480c00106c694180d110114176224185100080d01080050f42c0803408109444005240d150000c400c3e03800340500c01d408030003507614003414000200501c0e80c00541048102892010301035180e000c0c407000c844000010700792550340c42c00003070031140180c01180da000b20020410011992050403500e005404a0700180d503040107200103000c04840b6480321410600b0142d80341800303a0b000c0703000c5115a00a4a45540780341c084008005c01400c5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 39262387 1250 39261137 39261151
    0x1406010b0331030c05100c091802090607050a0605070503040f1101020705030304030c05090a020c030301090f02070c0e15030303090717121611090606090405060a090c02030d060e 78
    0x2062000035481003150b40c2c505500d1600b440000344203400850010030380c1801c0b8905070046403c0c4c407000030070840100300d00c41149046040030420300c0d41001e03000340300002038861580c1081c03030110080390035901c07171b811100780920041c481955220b007032510640303d0a0403041514098074103000203034550b021710200ca10455000c18800c40b261400e0b0764078440040c40540c2c15045118000c0d010030144c1f0b0810081001e98040d540d410031992400b0100104100014000380f9000e0042c000c1c0d0391070031000410307a415a100307440045803e2103d008484000d0082641c00307086c4d0030021000007095000b9000c401e0107501e800c407201c65000101d03004c1c1542c0e448283c40701141c0d640850400c102a05004030f07511240e140c0d43c0700792210004604602c0301c2c4c03504489103251080826a00c42401c0040c1031100d4440400191a4000740c0d25104001a038a400366807151401103880d00e00041c0305a584900c00d10250450090801241c125108000e549400101e00000310620f040000300c0c8800603021200e1017110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 39263637 1250 39262387 39262409
    0xa080706110a0b061905130e0111040e040311010b06040308041e0308040603390908010c0801090b040e070e1b0405090103080a1e0f090902120402011d041107140601 72
    0x5842c1c00f07000305d0904d604c083d40c0e4060400b407000300741aa00c40f80401c0a076802d40750041100d041d0000c10508403a005140806070001c10442081103211100b500c1d5401901400d0000307007207012113141c41c05001000b01c80c0b984030400240100400800401030b02c1510060400d07182c220100300d00120304000e45000250040c0000d110801c074252007a003000841c986403460403d14807540c14800d85c1c909051003981000103c040c20713110002079000b2412001010f20382c0c003d0004d031b050102e001d042100103010b01200c03070b5210301ca9038241d0b44454011501e040703d00d1040b1038a07556201c3c0c020107024015a000c2034020030400400020355000e00c01d540580340002d00102480c0d10310380c4c0b1803041c0e520502c00801400b0214403c0025410050401c016030082078035120394044205030014884802c17604803e9000c3d02c1401002c07203011800021a81c400e82c2802c080403078201ca60b10301030741616404011548a8101100c041d56110404040c0c40348504c0766814140c1c441e141c080054840b40e0074012914168 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 39264887 1250 39263637 39263641
    0x10f05010c0c1502030d091202060619090b010c02060a120b03030703080f060d05120403150501080a030c03030f0612020301060602030915071104020a02030714010507050f0705010b0a080706110a0b 86
    0x191004991030016880344c012245850042440b00003070310740148013a250070a894905c001c14079014041c0b01c0c2d1150f401c072103880c00a6480f0250502d01851401201c400c1580c03180c100c0320b88c0e402001d060f0340c1d50b44c004194039114121007100400c140890005801c2803800c4c0004800703107040010686070000c4e410346a03c1d4469941c000e005421030401000ca9030700c060708016480c01718100340890980c004409041070340d83e50031810803c042d011a0110046035501c0c1c04010010314002282e2116101d906d85442c030210890340c01c0440282c0800d40c0322600a6181600000d05101e80780725100009100754000e02006035240f40907a00c2c0d0080b98a00c5800003014680031112090800080080ba0701c1003114074100c1e1688004603080340c206840d000c016070300c0000c450060190490b030321510990707140000e024500d40401d0041072800b6002900940e803001142c1c100400c03000b9000000388502c090201c01c0e500e56503600380b03035440a0ba803180b44082460480014414880481c076103403e990000b8050f4216 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 39266137 1250 39264887 39264899
    0xa061a0406051305150d05100f05041d0303070f020c040203070e0603040606030b13142a01120509061009020f040b09010c05010f060801140114010804140a0308010f05010c0c 76
    0x3d030720282c41d50b0a250b0aa800224050399480180116120701d07800b0591240040c80b482812101c0182180780c3c0440124020805848190714000540e40d0a0b1008103886000030842c4606480100e40f15886000c04400c00405545c010307291103031803c00d84e08803000b0b180074006100480c40160303000d1000501d088050303450390901c10b0040d504148195800205590f40f922186180242580c41528007840e205107641440321403844101d40c0e84140e03005d80718000310f00215440c4400d01203008004101c00001c4240c287e801485446101c01d840c0d10b0600c00c030f24007421940d40b18902180c0c000026101580041403020b42842070b02c501c20b00c4621800e240c1810807030b103120b150b04982c202c1d6041100030325540d00050801c2c081c1c41d0821a0028000c501d0382c0c20104002d094641d204850003208030700c2c0004004500240fa03100d900f104d400e08241e6079585072800d040f803140070941200c4000d4070442102900b05640640b1480c12101c0010b1412407960329200111600041e00b04003500c140f030001d00900903 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 39267387 1250 39266137 39266147
    0x306020a1d0d12020a0501020c0303060901091a01030b060405031f1404030c11060d0c021c0309080904020d060e010e040506060f030c1306090f0b0301151805070c020d05060a061a0406 80
    0x4500f5030f90046810644066917210b003a40d00481194901d50008414410b103800c0071800300c0c0c00350541e16414014505840030702403c01c20070400550405031120342d020080d40f503240482d40074110140982e060001d000c0c00f210b42d0b080310410b0100c1c00501e09a0f200c21030856280c10329015583c10380d11403031220000d0310782103035807103450440700c0d4400403c110100740c00340f140c480d00115840e903402500c0c80b041c541104004500c4019400800c1c1030420010b00c0028480c40121207409008440050f00e400304268060000c050035004004403401c04400844c5a100c94000c1c0c6208900c113400311079881d590784041c0541c64009442c882d030540d0086251180c2854083e024130303c6403200c000c0c0050b4440e03403290301d0029581c5404400c6203580e134598220400e400c0a001d06240381203030903500e100c0e1a11388151002c5c0852501c0344004156a1000425031152081000f035002c3d540050001f0720460050408503100c1d4429503110300c0390b41c40c00400080b80d50a040040320403031400e81030340e07041a2a10310b0540b1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 39268637 1250 39267387 39267413
    0x41e1212030225050c090c0406110a02040203041b050303090109030305071b0609050406090b010e1012020403030801051002060702101d0a2102071809050a020a0306020a1d0d 76
    0xd05800b40001c51203000c40c81401545681403554483e001101814194204010704081034014403032041000034011100080743d041b20341500d4005180d17100b028005042000c6c020b0001d40c003900000030f1109200070040b2110036512501d0030020001d035135008142d540c2c130176080c10a000c924a68170400120f8068005000800e00909003031181d45aa100020701c010465002000403070410b070b00601040c2094400d1002600d10410200412000c440018058a08a00030144105100c0b48601d2102d03102c2c0004102882170704000f503455a0326882e02501401007401078a0051404d14500d81c8070b20710004110f030080c0c003240c02a00704140401000800303019071b43d4036080c0340307110485050f403000c50070009902051701648108a070864600008400d9a22083c290021548411001d20082580900c103108000140c080000c0380724103464128140f09080c000a540810301950002c24404c80760024410241d039a40c8641d05003030b030b6080b00c000103054400500c0d00b0020070300034800001c2c40806424 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 39269887 1250 39268637 39268673
    0xd03020901030f0606030606030e06040506010302100c0c060807170714160f05030a090501020601081207060b030307030c02040c0306030f0807060212040507060f140304300203041e12 80
    0x89512240e140e003c6040d181103034415000240d862104001490b4188101c00da54004040500700504103911401c0d44c0d0401030001070310507540441030280d098013658002003030315849030f009410303a50f0b1048054400081140c0117004622041a40001454032420180c4609041d07201d0780d00150101c0300e540c1c3c46030459154071407440e4528000c240800d25404200300e0140c811401507640b0308590400424502c91544000d0556100a00600001e00d0100b00e900007804000100d83d2121100c0c103101004d000300d1040c0d2605808000741c0b8405042d0b002c070f151172005000750742c2071001c3e00e403200c3c040742100c1c02440301030030403003031039030341e1000140410b0060a20a0083c60007504010a070303e1410300301202903c04488aa2220f802000241e81095041c1c9028229050601398095401e15107000c5100c0107100410010443c1ca108440c440d80703282001e0004a504800c0d40903201080c4081d5483d4001d000700c102e9100b40403a8200444810020602030300c80d250560401140319644407580f40862103200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 39271137 1250 39269887 39269891
    0x2040216050309190510080a0914060708010b0301060909020c15010605041502060112030c021504082803020319090317070210080702031e0702040204060302090a0f05030d0302090103 80
    0x4440c00c10000d8406200940a4009181c1d07034000201046200011828420a1000c0190341040140d841c03120300e96001c98641451444da43d20014050020485001d009185028450300d00c1034601001442501c180c1440d21211800e0b6281c0d500300c40f450100748100c8000504d10700060084503a0358024050110000040b00c41194030100420240c00342600040005480880c3c1004224441100ca03085030040b80081d100c1941051154002160410b80c09001e124003101d1600c215207680742506a00207070180b8964507951281e40d92915800444d080c29003c4030b462341840d0241c0306524804240039416001146030540c62500c2500c40041140001c061040c4190000041b842c00000001c000c0c0040c030400c0c6d60741206204020a400600d43d904042200318410030042c41c1d0008216106903902594040c80e10106c0300c4004d00c54492020000d41080c0085000501c8540580191050100c1190001019504d1b4040316400d1003c1e481410341c1030b84650316030340f0305500980c01010300142c10300d00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 39272387 1250 39271137 39271147
    0x90402090711160e0702100b010914031f0515041401030303051009020309100c03020a080c090303091201060303020f03070c060f0528080105190b0d0e0f060601090b0304051009020402 80
    0xf10b414400d0041d40220811080c800410070010b40c1485400301e044900034041010001c131500081011800740142050801d400c10320469a079020005d4220245401100b040b0007180440c01e0405440c0644152441141010795080585400c1c01001003955411006107800d0b0303e1510120058500603000761b000310001c120218800c1e4403030004504c0352070004014001780342d911b40d03000110303000398105004140c41441800c9003140d0018506400c07540c1c40d00c207162521095000a41540300c2c001c0307866803010009866029902c010740006080307901079003d0781c02050010000e1500c80c818214020030284060710705009607400780b252001c910845203440760901c03550b080c03140d140c0683c9107900d001c0228a0001240c1c1a83d0000400d80074003400d507800301280710303207165400c900d442134090071860400c045403081d0140030740d5204d0401090b4480854a8243c1310300840c540380d000540e00303540000c0100b070021a49809000440e0b004e1984040240b240c0190040c0400013405580800c0342d0041d02001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 39273637 1250 39272387 39272413
    0x323100c05040e130b0f0c070210030f06030c30120201140f1504020903030403080d090c0308030a0b0303030705040e04150e0c010207080a0b04030c0305040b0301030b060f090402090711 81
    0x484140300740726088822640344414100742d11005401440c4100206c2141e007084201c107401e030190760a565050f100e12601d00ca03410341c16400341c00c2060401455515041001003400340d480104411241d03e9a4081c3c9140e20b000c40c0914410034002c1e0308a42201e01042d100001041003401c1c2c1c800c60703064400060001407203030300c01404000503a0040c1c0b03480030340b03030500110a0304500c550092a808480841c6020681e40c003190302ea000c0c40c0310241168a002c100f0000c1801079801400040e9170011f0600c2440d40c407881e0403078060304240c40b09490b89107000c0b50ba03140d50030000201c07801007026440e80c03810145814061444010010b00440312000203a404141c1441d841c0507401000309041c01401c500c2c03492400080c94070380b0690000d03008e40e0110a0000110741498580c41c0c100b6018980716007034800c1c5060664003807040341d001c0392045030000000010702140b41c00b100e000f040c0c11100b0f407660b161014108480f4260030360700a544009070301c011901090003280f1100c85051b0740d105445141e94085 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 39274887 1250 39273637 39273659
    0x201111504110108181207030e0306042306040812060303071401020d150b07110d3c11220501091506090303090504020901050d02030a060323100c0504 66
    0x1d50219182d8010360a401c21541c0c01c401c4940d8000141c01c030300005410070b458010b64a0802d4002c410500f140040c04005151044540300003002e0098102c802505140ca4074a044c5010010407035103030070a008010f8800040440c0c0180a180c01c00341c003e080c802800c6540c0d294082c054030807540352000b0000003001807540886427100304160000140c446403e0b40307044007580c000340034003c41d240c0041c2c4203210456608041c0c4810541000a9100340c07000d8101103100c26144290140507100000e02c410081c6248800d550a05070b41c41c0c1d5050f004100f24011240f442c00110700040c400704610b66503940b0b43c180340303038525075107201030b100342e80007104540d44141252802c2e04030b810401e803030740c0c80240145100008800207100304d00e001c4109600d5910004c0c06440680122446980c00040034200b0ba031040f07003990707007581c8502c104560301c0c1018601d40000f04100d00c01203600c082d003100d02c49000300c41c0d4500080c450a243c406013001c1c1e0041c0400d20f0042080f140c0712030910000340004107007441c4071 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 39276137 1250 39274887 39274891
    0x10314040f0209070c02010503041b0e0c03070f0c03120b01200102040504060503030903031e0405040606050901030501050103020f07060b060c06090607022b0810030503030a060311060705030702011115 88
    0x1901d010310700c85040d070040c4081c07128024071400070b000030141030b40d0050740d01c0004c1f240c3c440d0704411446e00640000d180ca0500303519a40c04405154a548144000718a0580007507019096a403140200602000011f4901840e07440c4041d0110310414920344448000d030700102d80e2660140741c60b400d1040242e285140b40509900c81821a030b501290a014a04003441000050701080b8010350030102c10400080d5a4400d48034040a80c2d0042d0610002680208040e2070103810018024000c0540315403008025400501c0b00a001a0030100001980d5010340700300c4000713011442156150113159101c01020340380c13040401b5007050080080d0b03011200180802800313902810007402c12400d2805009140440401000c40c0d81d1014009240c2c1290800c4d02d0341c5a00e58103410a00c006503101e0074850b01c1c0c42c1d12036101030a540000801c010103802e1980c000300035a032081c0c1c0800c014821580a1100d80d00590f01c008100d0b0380704100c031101540c041c155101c052807560084a8110042405410441c001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 39277387 1250 39276137 39276143
    0x130518070f030302070e010509040f051002030415150b04090b06040906060206070906030605030303060d0609050a1b0b18060f07060c0509040f020a020616050405040e030c01061a0a050901031404 85
    0x214820b00030150b060011720000c022848100025504080c00a505902c0103400100519070240c200d03400c102060200350900c880301c8804644924060500c800c648104c8064440c4881c90407400c04010507480003118203542c0c2e0300f01468207040c184043c10b0000c1c02d01032400fa90260040c800018001140e000350740141119034080c12080c18901400340160031241c02c403200381410084244000c2c0c8001007a2030f4000c600716404c1007408814200003005040c0c605014285025058041c010700c0b0ba01c040b401528054450310707018555880348030007080d018840d0601c0030b0412200c25500c0030b04c2c0c0dc0c8007802c502500c41d5010f52400c80b480d61840121146200b49402203500459502c0003880d0a220b031603010800003a05524104d60710600a440340c0c2c0c000d00540c810450940d00c003000b54403c02c02c1c0d0340030f0300d400343c0200085040032112a990381c00800b80c0d50802e600708900840c13600854070107220744140d2640910f080000c01c40c030a8400f50400d88c016030405651309015207254a4080e045400740380 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 39278637 1250 39277387 39277409
    0x60402010f0e0616030201050108190204051b0c1c0e01080a09050c06040306060608010902040b090108100506070303021909030f03050f130909060e010b010c0b040c0506070b090601060c0213051807 86
    0x1c04c0d10300a400e5440503400710040b608a400b042c0700108000482c00e5000b9411200001d03555541c00400f0304149080b80341200f070b41000f161104a28100150f41404400d480f802c0e4088400f4180e003c480d0100e0111b6950300290200021941010842e0880090b29201e40b0540311079403a1207021544d0fa80241d40261190f0303898030341c20802e1039081010107000d01015a0107602d001c0c104040c40340944100e041c814100aa818002800c003030750b4044038001b40900500c4180c1d64030013810000c000e0b403ca0540b001c3e45064201c03000711070038007441010088943c03001101c803d01780b07241c1341a90982c203d0008614081401c0018174000c6883c008010041c00208400003880902400c0440458a201804044980c0750508440321a0b070071105401400c1d5004c01058440d954034540844078640e2940300680205000c1003000030000e848403071a100740c1e0220200e606603030b0b807480201d03040804500041d401c01010790061141303c5950700310720391042000464240c40d0031030b813240519110f943d61204030030103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 39279887 1250 39278637 39278677
    0xf0708070303060605030f041506050a15120209030c0d2103091a010b0301090c020a020910061205010b0403060203040f170c0106080304080303070e011b0b0402040c03020309060402010f0e06 83
    0x1d41c051240c14060f00c2d0a107081400c528014110100c10b030800340018001c4006002007150320000c5805c664090304000d000c0b2811a03503110742e42242145040c03400c40101d00d4034405880c0c020038920a079803020900500411188180c3c01c180420003440741015200405181d251a07022407628490300d0340100c00e59400280038801d82800c00030035030040400f04403498801c004102074540042500d041d2200113100003214000c243c0d00303a140c9982c000000350400b080c1c104104072010100d1a100840b825a15545c0882d00c0e001f044c1c00844800f4005c000001e4018071090010071150303409190b0091040d020844c80c1013860310782c180c0c0007c18007008081420f00003036015040d0030078020f0b0001885907000075402c1c141000700142d00da0000800d40c40400c250b01c0c806600ba81c0c07192400851007045602200d049580c1410000300d1000b084a090b801142001e2040003014800e2003120b1042c4403100c0905150b071150381c01107a28a01541180b403c203ca141ca425126940b00b00060803009142c0b41c0410b140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 39281137 1250 39279887 39279893
    0x190915030b06010e0306040b0705040e010f0e090a050a06020706020403140601050f040b0109050f0301060b0a0305060301060b0403050307110f040e030309070906050306040825060902030708031c020304080f070807 93
    0x2400104201c3c1080500059028141c5001544039007056004007808a59654031804803901d0040d50b0264801c1c0361003800010340442152030040698013204866056030f80c41c1d0300e082c1d42d1003400c20300c010100d42c0070b00e8600c008650583c0c05849903a200e50400f500e0240c3c2ca46075131550048407079009505801c01d41c010080c7e0325151030082c5824a0960f42408051500e10029060300c00d544a03950180e00104201e125907902907001e48040d1464103a86501c500150b20004c00812046414174025860010f02082c5100ea06080d03900b107a901400440c584069603440fa180e00703415006058206104110807401030380c0b240554013190188c0b1005684a10700207c3c2d8518040d080da1011100600c0e05406201c551804615650b105030044801030350790f241c0307901e5004584c1c5c1044030b40d4000b4010400c02e1080190030b4219600041c0210300303c3e8607080e1100e2000d5241d00c0713028004ca407040c184c0c0803004202e840d0794021359409030140708141c0c10130803084583c0030107901078141140c0c440400182c03c410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 39282387 1250 39281137 39281153
    0x20613080d110a0e0a05040e0c01050903010f0c090e090703080a050c010e070602010f05010e01030507061407020a060903030206150901060f030e030a03050108070e0f0a0506030a050d030f0b1203040519091503 91
    0x141807c517400c1c0142c01060242a44554540700b50f141040f100241c44c0802c0d480c2508002240c0c05c1c10a0708001c40c107460040202a400c90f4050b102140a810300814a01c2c0c2e00007803c03805803038005115030b2a1444000c0140c0e05030f48a500041c140c0d548070319910703000700300070701680d03000740f445400100d56200103c040350220754058019030711605142005002048000800000383d0307186061841101c1c10104a95040c0d0184050095200a10410101d400c541c00590482268400e8080310200e03240c000e1076041d4400520030950700803504c14010480d00d8480d0f90034100140c0740e400e0010f40801c90000843c00d66010030008230110740c480c4c004000603403003005148010719580324030b4445810904450031140001401400c0300c9a198004a26583d409000c0c0c01103c41e4400100d41e4900520030000d4090111500320300c560710700d054a641403a04140d494040030020001c003441c54241414100014030111540e0138646810081000c5000c000921074145030042001600e07011a00c1c500d08001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 39283637 1250 39282387 39282389
    0x4050304180213050405190608030714011a01050a030f05160f0206010803030a020702220e06060102070f03020405090f06090114131e06180c030b07020613080d110a0e0a 74
    0x91a00c100b24459411540f080b01c181944c104841c04642a25110703a02121381e803107082562502480c244001481e054000014040e0038400d4203461003402c1208111400c0361540c4502010f040c040e8001800d00390311038001410103043c82e0a00259800e2010076900845074112140040c1102d0080c0303000020703800400300203000d1074500c000c000941c1000005a2a8040a40482c0c01207801040c580119a1036a80c41030b8000100403240c02c1120b103c0d5100d0000d404052142c02c0140161008103045500c04140d00741038400302c00900b042c0903c0d560921008000c01041c0c00e00b00d0040b2006c07024121800c0c080180075855440011401c1040d0700b032001d0900e0000747c51138204004280348900000e002d40001900c1c15030a500344a040305540c2000c1018004c0a4210f04440a01e240c4031801c10484d603804600356400360682da482c41c2c2d68601d090741c0e0740e01c054605001008401d540c14002408100c01447d141e48140c20100c0e401300107604903985904038a111401281c001e40e44840c440c00c24041700c038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 39284887 1250 39283637 39283679
    0x120708060405150405030d020d0b0409030f03060b18010503060414040308090d08010501090b090109081609050c070203060402060c010e030406110609120a0e0406230901090509031207120504050304 86
    0xf0755608099403400e5484c4125180d060302c01d41c0119018846501070350185100d0b54002e4800d0000f108545002848a074000c1329a9000c030303140902c00308003010b1110a41d03000400e0100c41c0c80340006200e00543c0d45400c014070103540291244500c43d00a00070100e5540142e1203902ea2080b58148425030a0610380380b500710104110080700104007a0381d12041c2c41040f02d1b0b045040700c0d5100d01c007d004940d102c03501e0f080903d41c0c3c421010045138400c200031444048402c40d6004001c1c50312030070303200d00c91440384040282d4103600c807101003005450300c40020b00000c03011100004100142c04406800d581056110002241e142101001220341c24032440740d1000404000c0c200c000e80001148420340204c1480030200b03c0c545601c403260b52941e81c00707070300501f41020075110103000c641d00f5045143e5803844c000d405802010000610000c4900504d80120745501c007850401c18481c04260800c0001482030342000490404401100c05900c580c0780100d0040300555a0f86e400e021210704152800c0c0506 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 39286137 1250 39284887 39284923
    0x3180a0f03060e061e011403010e15090c03010513030503090304031a0a050604090317150409050d110601060c02090402010509090f0403030e07050901090b041b020604020405070908030a0e120708060405 88
    0x20861555410f1800703410f54015128200d0404c2e182000b0900600407400ba8911600c10350304546030743c00c152f295541c4618072640032640307005c84600070b040c03d035601130320720085508001c503a00740002c0c001c5001d554481070b840c0849090590787c0e110071071240900008452101001c000703018401c2914094140c1c041c2c41a2814004100b055600070180141d6208006104480c10041550728807109001030342440010300602c2000303514140280c480d04e11286c018007080f603049c036050005001003038890407207200f83c45a03081c0500503008d2040002004204a0400c8030400400020382d8500c4406c0d809070305400d071040500d00c1c0500d009811108440c99002050303100340410011a07a6a403804c505684105c500403c20b0349041012501a1039502d03404684082c4130032103014959400900c03c0e11550003150184002d0711404d10036101d007803582c06030001640040201c00800c0f409008800c200c4013003d0b100455102146001c02d080c990036400003980d9403c01c030140018000100021802e0f0801c0c0c100f5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 39287387 1250 39286137 39286171
    0xa05060406080a050601031b02070f060305010b031b070803070c05010b12030d0e0a050a080a03050105010309020105040b16150e0f010213051e040c0816030b0303180a0f03060e06 78
    0x1000e09504002407943c600b00341c8410009445074031030740185100e100c22940059824294107806502e030b00f0140511032581c00041300c0042c0c01c5200340203840c100d07065600700b9499038450a011040c04c00c25000c4102e0101805c0204038001025400150b104001d60340d1f0f031702404110341c540340e421b4035017040005202380515010082d1030309005c41114140c50804c04002036036181c42c4015814000d0603800a0300b10301401005109202c100e500038240c03403a4170f9604014907a00e6800560885411010190003d6008d12041c400800082e00500355070014500c640c114180c0d030795614480d0f01100d201c0c0407505465001d80e0946010400c4402c002e14041c8009508100e1000c044c92030041c0e01d0320a5a103c5ca682600d101c43c2d02c24100501d2254040292080c8000135a0800282136203800340e840020106001340e0175001c00c0e10130300c124040c00c4001400384d407601520190002c4800d00e8107401a901c809004400a40c0503030800b61384008600c9450301261125601004508004005190495142c00740d00 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 39288637 1250 39287387 39287399
    0x4050103030f110f15040209070309030801090203041b03080d06050604030f021005040e040302031801080403020a1713030c052e030914060f01080601090204060203030c09030f0a0b060a050604 84
    0x2800d802c58010b00e28002c8504140d81082a140080c8040710760031600400161410101102d40e84a01c501d0083c2c60510386622075860482c200c2d5101c1ca400b50004042200600c21036102d071300110340050081840c0c0011a41c500901c0401400a910032078882800087e0f400d440c038014002c038070040030103d804c4c1c1d0405142d504da44000b00e01c0d45038000e00c683d420a004204443c0260306540141005051a4040340b4062070040d40e2a4044010512283c016207800300341d56204082c0d4900c1668140d0141802c0c1413266500f015481f02d04401940940d018041c98981594011900005501654000800528102c28007034086140000c044030006500d0b6840200c82520485c12580303441880c2c00504440203080064a03d650030040b052103006d0760051250351890b032102c4906071612a4155030007a40d036540040100d102e00e20402000d81c2043c40091080351545005c1c0164142c054140c1e00c0340c9840c0c10540e818800200c03001c03980700310303000140442810424290406004103032401850141000c1d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 39289887 1250 39288637 39288647
    0x406060212041502030403080423090c0a0c02030718050a0c021204030803090309090109050717060109090506031009031d190b070311030408030702010201050c030103020a050d080c0d030501080c0405010303 90
    0x40140d510080d54108026200c3e8400c0045800940d0092820380d107503a02d58100304032800c0c002341c0e9440c40e11040880b8035100d18003401c46a000310550a0040d250081c007210580e5508518002a603250141d8140000c60840d00580380c1c400000e0400002180c4c50300900d100200c40000c004102150311030b401c000712466291088070103503608010751546035590300740118914440c400e00b0f40e130011450307800001d070741b211604403900603c100d85419400c41d4440d958044035000450f02c00d800204416001c100303500ea03e5001c5900903070040c007900c901001c01c030303011400e9811030181100010900305444061072614107816400e030720f08031030003003108050386002c17403882c0c3c03540c0600001c5000005100c0101401003940d8176110909005503501c6d1541c0310006034407600008000c3c1d005d5401e01d00021000360710303402100c0c16240e0080c04480f070316080006200e116008280116410742e810001c3c04150441000b00000006a554012843d50305100000d0308028548000f41d0065040000510000740c0103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 39291137 1250 39289887 39289889
    0x1e1302030c0d0507090903030b010e0306040201120b0f10050403021507150c0203090a0b03060a0918080306030f0105010f06110d020d050a1202030a05100503030301030803070c1a0702060402040606021204 89
    0x803502c09030781031250306107542001501d5020380415407a041d0250109a050b4101d850034070030903200d511001944000b45a21100210340c02030001d810682c8601c107007600b41e40300700c10b40390002d401c81d03242c482044042041d8060200f481300100300042400c204514110f0807909101006071280c1d82840d8407640c480c0d40814071820b910902ca81c5420f141580c851081060b10000c180c02000d01003e21b40d501124921548280c65a43c0100400e40010540841030301800e03442c1c07002240d401c080d801c0d07192106d1140e60406420b0f250305014031030344400412024080c0601070000c4403c560b40a6183c03000c05002084410700021054201c41140110240c000c2500c05600060303003446a921030345520110307039070b2804201c681034103407011040c0040b190499010030700c03461001d060014015140c1e000c0503501e000034880100007240c01c000040d04182701d03640d1106000e10410700946c050350600011f818109044616000513031014041100f580b6141c05000010038090025281500f010b80c450641031180b = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 39292387 1250 39291137 39291139
    0x60a0f0507020f0607060c0e0303040803040510180b04090c0f05070b2d090d030b03070603020d110403080910030605031e150f0a0b04020f09010305060411031e1302030c 74
    0x41200070654540a0012858410040880341d0340c20281c1740400080c10088100700000d200c4205250003030400104850598031117400550605250004201c03140740403850080030051a80d11280c2c810b1b01c41d0310500c002c1c0000d01080c1e504d5070304091601045a41070380010040040d484522500240c0003001c0745d80850700041d12315002e56a11050304c00034141105212910041842d45940000325003203443c2c000c0b90403405a80019900340e90807815198081c6900d035140d004200c04008140c001d41c014008520380800c08a50012078286112194000303500c20381d000d10300002d14017001d05d0500c05540b8100741d01d090030000c060409010a640c2c5503100c81c41a21408840d030f0220407031104001a40107184000c4542100b880d00368102d480b43c10b01554000c04060500342e680206240c40d000b42d0b480e04a0141c0200e06289030f0500440262070007500c015001552409002c1d0741c050000011817065040241000300c94026101003d48601c000305010150990304031240d0060f50041040056414 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 39293637 1250 39292387 39292397
    0x10801090b0a15090602012a050a020a1b050102010f150b09010201090233210a09050105010e010f08030408070504020702131b030c0e030a02060a0302070602040f03060506060a0f 78
    0x250001144010182d03810095143d40c00d4041d00428552010602003910203da0090020182d110890b6200103032900e00b41381c40d040e0490b541d003500c0e4800e40280920070014411100300902a840d581050081210741c0060b100c04c41327a0a010302e50302401403046101200004214001e5a041a840002803501502c50030b1200040c0a2449038800d400155901c2e03001090b1006401d03201207001c000d040b0a034021500d80409410181d000107c150a554101580e1481e20384c07002255034041c004500000d02a0078829511003000d00862130900c1858040c200204125005504103540350316824055400b400d410750042106108180303002c154041211815600942c03214190304c00140d070444184005841d0380e2428002501ca02d099210b05400b186da6a02d04004140207050220b41c20070f814003615405070700000a0030010305103400201206041850b00604003920f81c0e591500303036400b5a114400d0034240e00010b00600080d4811140c2000088a490745400c40c810000f42c40c41003031f85c40c021b05102e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 39294887 1250 39293637 39293651
    0xf06050a0f1d090a050604180b060d0f0503030a050601030f090c05060702040b0303030a0b01030b0915094302030301060804030503040c03060204030503030a1a0307090f0b191404090201080109 84
    0xc10902e1044940d180d00500e481d4061400c0e4101000414003117414500c41d038204401d5560001b0301c41c03884040c0a4001405c3d4a05560b03e50070b00c280c07810303a8401208c41c01c403c1088a400314105001070360040c07991540224160820b803000500b666070040d009080985002c00c1000010f088502110446a0640c3e006894003440d000103001424000e08054040c0000010098950040e03440013501040c05d0303d0801144807554144074181b0802c03a030400103483e62804155851416096181d1301c04240000b070801c01480c07900840d0030103041b03241400c0380001e40c001500e09840004d0007804190f0184001c606644c07411800420950000c3e20160a00000001040600c10500740300c10103140c100d0000c0d99115580d00d00301d503695004030344403680c191a00108030f00b0042c3c25803020f00c40c0d040c000c00410080d4108101c80c001025140f07058070950741d032240f9020290322481107540d0900703070080341c20888a02e030850034503107207204189032840341c0e140140c0000141c1e0081501415100342c2c4400140c54 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 39296137 1250 39294887 39294917
    0x50306010521120705030403030206010e0c0a080a09020a09060302090f0c090904030c0f082502010806120c0d1b09020a0801090c02010216060203090705010305060f012f070f06050a0f 80
    0x43c1c3c004155040da900b00103801c00074000004018011030340b081e400c0703c0c503680c3d940c06608040c0354107440c1080228000c1000000d030781e10502e0556000b4070341410001d410286540021a03490650b403050b04003603110030041040d0318000c00c18039408011040d2040c09480e004484600500c242100701f1310a060040203c3c2c141031003203040510390b5502c58101c4800c1400ca08000200b03400001d8009444035000da03168086810084603c145070341e0684030540c941d2079007000c1100c42020300c8003002551046140c040758a9071001c50650360140921404444030a6915403000d089859400071103805004000c60b10407180e011419074110790a40900084050f0450b5089002e40310340002c824a000c6400c019034240004c0f41d0042d070060144000300e03101143e4640040d000d8680841e081584100100e02040e82540500e084090744203c11401a252000d8100c0d440b030b070410003c000040c2c6600030803040c48600c54001180380500b0b801c0c2055820a000c19000800c92804015071404121074110704040d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 39297387 1250 39296137 39296143
    0x140a031104090e0303010f05180118090501020d0b0f010503040506070e0402070503130f090e060a09020a080a030f020c011707030c02070f0306020d0605010c0f06020a05040504020705030c07050306010521 89
    0x19001000b0144081e41031250394039600d4000b80a84803080100d04000110791400a00c51550040700b20008810f60b8070304100c1012041c00410075034601d80c0c40d503900c00b00141081c4002e006022a01c2030008042102e48140100c3c0c41518400d127061120410622000c141b001807600d92001030351801c0f621140d07401000c280a030042010080c8580300200c0c914612010f802d845406480e1074424108406a40348a503030181c88005010105541041001c01c8555070700d600140c11550010f41288000d6660394505031a006000a007900000d6080c40701c81800e03079040c41744044101d400d10781403c48009542150111103400780c03103031003891707070380c04c2001c40f018001d000c00d100603c0000c1c40c01d181176640341402006544801540441546041001702d010740c01240050070094001c90500c6034041c29076201002940440c3c18601445818031000959a5850008200c0c551044002d9a260036000301480d16142d20713500018429000304005201d00c0e2610312110618401c6000100c0402c0341c281c5003581 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 39298637 1250 39297387 39297389
    0x1608151302090a0e03071e110604150c170a12050901060e061201142e0f030f0303021603030b030c0d0503090415050a06020f0f06010803070602030402010318120f140a031104 76
    0x100580c001f5141a8102070070401185403607000e0013048070818030720b070200702981c4a6030080e40445410141c1d4100201d2280750020744651144800e400441002d03d01905981c2020302030b800011281005400714596070b02400760801d01c200000e1000f03c0c00d01365440d00000008011034050307403050314501c503000c000350805e140b140703103940410f00c103806c107200e2650118004580d0440c6190407031401c10354060845800340704442d940c0480c190668110784e130340240004820802d42c2016021704c0300501c3d0f620884881460f446c401e882c0007072403840d21002e040c02e15035500d500350300c5100c0305141c3c54049803010040f80c03e107a200700c40004401e501441004694034030303500b00039004400401d02141003a000200b1040051031101203401042411060596038442400340411540042c41000c0008109402a580041c4141008114507860310180b040c0c5c0c0350702c5001950202d03100c202c00300d5941d8000641307980d107031000d01d40552000010740c0104100d205001c0300700c01705580c035040300d00380340c4448060714 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 39299887 1250 39298637 39298643
    0x602030408090a09020307030e0c09010b0a0c0b0a0606121a04020306040207061b080105150405010f050910020106030201120204030b0f04060209060d14070507031706031608151302090a0e0307 84
    0x1003d0582c031030041c0c400a40040300d88501092405540030700904000070751400c6450010701606440e805e103815102c0e242c21105c4c00320184500d400340c0000140801c91440d200d001070f84800201c103803a00000a002111944803a29010318100002400d0030b03440310761110705c40c0146c40140e034a448800105009104e1140f014000b14540005400d80305008807008090304001ea40740366007a6250000c003e8052481981c503a0207290411003040f480d4040c6509010072400740c10480d051035203a1011800d5002d880241400507595880d0500456801c01c1ea0800f40d458021011030600b03055940d401003030070018040a038640f0445000904200c03860701192107184024000a85031651041800050040054440801e0070000700060101384244241d0712120741590312a5110300001c9006811742001038030064041c010b101103401850101c854a01c01004500010700700d021100000024100380039150003042d18030360b60030801503a02d07005c582c2d400c40e082040020f42c0001001940e4a5171003010002 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 39301137 1250 39299887 39299899
    0x1501110307050304030204060e090307110402040314030d0507022802030102092205090102180108040302010e030a090305010506090723131409090a0201020d03090804080111130b07050a060203040809 87
    0x1c20208440031000d0800c4a1003170f030341880401d071030b6644043c40003402c95031428940c1c428041e501c0814508645507051b00c102600046c507258681c3c48142c0c202004194019580e800064600d02c40600392007101e03400b182d5880580545031103003181040d001d00002d0726003203582e034642048003595000c1d411103400100c02410a04941d0100110541104a0320458080705150000141d6082c006008544143c0403940140740c40d10b85000041d10880405041a01199640e242d4800d60180410040142c840c140c1c80301503a03a4a503141660a60382c00403c1d172402800c8000501c45015040752940c2401120345924807505c4060a00003c41400f0b6070883d40000706e4112400542030100c2415841007000036644980075560300418165101c09002e030080c0103078044021380300c0c41807003640504103203881071035141e18040c0d0300c01209096501e01030b41900225400124844001c643d403818200500b0034009403418410241c9900b82c54000d007450140400e41c0020010f41004011422209041070007024 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 39302387 1250 39301137 39301147
    0xe03010b0f0f04110d050105011101090305090625050105091911091b0310050a06030213140a080a120201140f010b1308011401030318081f0902060c06040201121415011103 75
    0x4031704042e100a01c03405020542d055034110002c00103000d801442c50305500d4451521540000f03008460340081c2840d20b0a04011006145551042008941d0719000b0341c004915403e19021403420880d0f0b801344454140ca00c41c00f141c0000d06030014805080500b00c0700034213a035980c0301c084028602d0a28421401250003c204155001000708075000d40b41e00344c6e0090411501e51034240c0c01c178071a50780d81c1c601640c810702e403c0201070341c02490420b4a0001410003071903980e13150301c01490800e402c14100d40c0e036031310045038003442ca90901c00c816021b505c00640e0041414070048401e05410103014030030101e0b00c00141c148100096803401801002100002c00010301c80e41041c0c0120a0207010403000611040303980d4070f51845000c10070040c4d45030280548041c8100800b05054040000c01c40d4003956141d0902e0070260703072660060001c2d02c10b0310b0090141481d1a1000610f6100d82051001c102c1c0c1c0b40003c2600c4922020740801d0344200c1041041035003d50100c0144c400214454941c2814800010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 39303637 1250 39302387 39302407
    0xf060918040f0605070905030c0409080408070b070209070e09070503041110030e070503060709060309020a0b040f03030e032b0225050415060804030c060204051003020304030e03010b0f0f0411 84
    0x10000b030314140104020002c9440c0c5081c100c4200721070f0300c289035250340000304850140c94180c0c48034407c80e1245402c1c900c0c013a5114001410082142d000e4111180041680e40035800c040d810554030103181c1c036146c0110100c020020300b01502c060012402c00001200150401192000c0d07100c030079000801d500c9003001030490040142040e0801e8103498010f16000007441d040c00240f031402694207440d84403195041080c1100101034040b816680900c100307200044040c20800203101520003200040c00d030b14110308010380403075540d802c158040d40c003501090700b490400040d004100070320000c604030840090b4500f00d180c10300c0c06007058000d0540c85c2c4250101245820651300322802560140600e0070f803140d40d004408968850500811248000500003034420402000c695115410050400d516500440e21801100b840f4a022030f50002c140018541c00405d4001c10300c008400901c511a802d601240c43d01c034007084824001c1c0d84074981c480f240d0b9129006208400d03044240c494468216034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 39304887 1250 39303637 39303653
    0x708030408072f060c070b07080901080c0a120c020a02090703020406090f030b010e070210020d050406050105040b0a0303030e0f061501140307090b0306060c0a110901090b0f06091804 80
    0x5442240d001c180303407180d644520841c80b414000716200160074042503540c0000d002ca145d0045070741071071500840300042030b0742d03524901a00358a4009c00d001500c03014a02c0c005010b820000c0c1c0305410440f0107000300c3c501a54400034007656010100004508503034109030581c50000c8020000b54000700000403c90440e03410340c060300850750640e0340c1d0440e440d40d500c039041441c0518003010700492008001401404404583c00b07070025400e1040b0303400c018a058001080386c0168507200111910b41e01407200b401403d0040d6405013504403401c100c5030000c800051001003140c80014217141d1183c0c143d081d10035060000300040ca565006a4000d481c000c1c0c9044043d00040d5405808900c0d02d54003e0f82c04901c0a05480c4511016104e4900f09030070400c500c015900010006648818200b000b80b0106005000c4499554403558825000341e00003000c105982d0b40580080c0342c41c0e45044c407001050b54a070110403010090684441c1d940c0c0e078520002c1780c0c02001118003005020010424030082207101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 39306137 1250 39304887 39304897
    0x723040605041d060a0603170a0c0c030302061906050607060506150c0a0213090804060c020a090603060f2906030402041401060f020d08010509040803130510060503070902040f060c05030708030408 86
    0x50040e12110785d6004038040c1100d01703074000034025141c40c18a005403100484000c012000b214200302e12006021394078650fa8001980045005821500030b02161810a59042c82400c0290100380326443c140804585207010302400035104a464001180721525035a4442065990070840141e4441c41250704540e01c1e038440704c0c220301030f03071403000c1d000800e54180c8981c00300d040d84024000d1a0511303158045520419140081e0703400035401d080000c0100c0e2034420b540045204583c00300d200c0350004040c00407211281401c00c8212801017021800e01e240300c01008035030b2001c031016601c0f9140c0c1e00101c0c004000129410515a40c0b5400118150350452194604400c8a6003140c0c0d001c4034106040b50907050038400c50360455107000210f0000b0780014091a4410301c03416107088040c04540f511031500c0c418034031003520681d4541042c041d07801c06001101c041c00ca440f00642c50946000020504c44481e44a218100b00f040800541044400c2c01111b803041d0300446c00684a040030700302a41c4a501c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 39307387 1250 39306137 39306191
    0x7030605030d0314150d021002070b0a030902010206060306010303090611193c0201080403050706150609050301020304081209030c0a03090e0a0e070603020306060c070e010303030c02072304060504 86
    0x35420016031643c5c1103040c0d00300844000341c207140b02d01c5499403d03c000ca1752511519420342c050040007051400f03100340500001805940c007c00c540c0f8281c0006402c210002c1c260382e000760441401030020941102d00e00003181c441d03151444000c0000c00d5500e041c1104849040810700702e1030612020700805a030440c00244400221034918191200035141170312032500740480c0039a0303c1c600203000d0340c000d40c49ca83e8440d00900f0032502c4e009050361400129003003c41c2c05013900b0101002440100d47c000c4800c0050b203000e800031850341c10182c40d5488203004207040d540d951007070040010b07030002d400c2c0b00755a21401180c00701c0f0303510b041c2464080e100800340c0c06504120340c0a5000179403080c01307500684503180200000b6003886410481c045000e98801440c00e50081030400c00d003403c2a004210700310080241070000000355041d441c00406030b9201100000455002e03960a003c0000b40b50704400c02144044d489040380c56414004c18094105580450307482032406142280e0300d01014180446105 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 39308637 1250 39307387 39307421
    0x3080c0615060a02120d0b091006030b030c0913050a08030901020301090b06040b0703030b0a1805010e0609160804060f0509030306040f02040807030b06030106080102041706090c06030f07030605030d03 88
    0xa01c4040c81454000c0086010050380004024003004154400800d07064180c500c0c00f01d002c10421000c03409441c02030300c5404103c03139820402c00046c1d50501c101c0803425400c074060300710f610103000014180800a4402e5115100d076a10b0784042150401030218003a600c2032501e912841c208603c203000390824400d4840f034604090801031b4070b24040d0100d0f03058400400351141030800c603480c102c00a20190403059001800c140000c501c1c200b60920140034480000c801042560400c0300ba04480c070005050907000d0030324101404a16103841d41d0741c01443c44185403100c1e49a64070304142c80074200000c09850350a00d1b0030b06000b01c03101c1c044011072180c1710507038060007000b5083c2e014804912862145d818681c1040105000060b5140d043d141c0000c401400031820b1b03500c9411060072a805640801e145510070054140c010501388011740e8041014800b80600007156808102c42e1701c002004600c8400040001030826402640420060440902251401810711802600800300740b0202c0358a05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 39309887 1250 39308637 39308671
    0xf0307050f0c0d03110a150b01121a12161502060f0103080d0207020a0902030c07021305070503150d0b0903030702160503120a020a20040501090c021c0903080c06 71
    0x1080020400c0701140c0243c03100c40000602d450448803901050301c558003500a4180e844007080c1a82d0a0740c0070140045800034107847c0745000034104044107803544070078600b4100b101a4048543c04000c40e20001074039414542642c01c0d000d141031030030140c00030119000d90704c40840c0b80c1c101034840ca024968a40c084640c19100c404801c004000d00b440700801c2c48004204142e918015500a4071007140b01801d080701054840710580184d80080b2003001d01d6803408103c0f84194581138000c07000c00380031902c0c200154100080010b0452000500300700b900344404c42c4c2003080ea16000006002c0750340002d039000c4207050041d0450b44a60040c0c99960062043c08955000008036007000d008982c0000e000340300020f460a00440c5541124010760190f008040c00d18010595081c0c48010326050400d41521074142c210411003242d80681081d24410318003140a180107030000365100444404040c95141c3e50f4004100300e68240e500c3d04024400200401c21401c003460028503e1300600441101003500 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 39311137 1250 39309887 39309913
    0x60102030c07090b0307050d05010b0103060605070503030609060d050109030c170c070317040e0a0209040c0509030c1315060e0307080c10081009020f070b0f010609030818030f030705 80
    0x280264903a40410b6008140b04204030b050301d90041a0700c8a02030140c400c1c0640d00c00004007060220b4800f40d030b042c3d460310034200031503a02d4030440c4058030391420118280201e585420b0360f2400b00500d118019005200801d45680d582031505000340d82c828001c1c4250f504500d0028040504654122a0340701c0c1d4110640d441c5c404002522001203035440206032003403a54940c00040c200a03908034060340c004200104140b901c44135a103100d281031075405039880d680d030030512003200e03082c15100007000b40c244460303c865900440c2d484050131089410604138500600c4201c001c107440800744200d01442400061155041103081e80c0080080b001d41e070040e07a0311000d42d41c6076030042e56880d03800304038a9040e40c1414003912455411070803038a141040181c84800c00000caa00100184c060b240d00450120200310350381501560214144191020035450803401511408417800300602c1030401240510105100c80c0b042c0420380c1005013142d1880390035605070fa407aa0f000b007500342c1d480e009684070701402d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 39312387 1250 39311137 39311143
    0x100612030306090513080f07020319030e06070c060f09050613061101090201021203040309030f080306120d0801091107062d0207050606010c05011805030c010c0819050405030f030901090b060102 85
    0x1c0344c1c004e000d6407801040761ba40c0700400e40e0700104000e804404184000700150700c0c1000780c062807450344682e1140200c0359040103400000390f90042482144c0401298001414a40700b0004a841f141040300c10181854000d5519038011b422150b00031308003090702529080198440400c4408a444e18284421124220740c00d84008041c080d016a101880c0c0002c544443c00c01160302034007905e0b03d4005191203a44000c3c4600020074256015800801842400d00c2d0294201d041ca84c1640c0042010028803000940841014411032030900c1d40c0d0040125402003100c00c030356110358400710400612640d8000d95140209900d61341500c0e100303102c19103940700400c1c07088030701058000c402002ca41d603800004641d5158a400200c0303055481e46012228620600c12030b0b03e1103403146c8095034803034070144d11890841d00d881c0034a00800207a1014840642702144179006821038000f000300319950b50742031041c074510a41e555000441030000802281c0c0c101035003e1000d0f41d100e0000707041681c81c0c40e001280d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 39313637 1250 39312387 39312391
    0xe0c121b0d080304020607020a2c07020303040201020a0201120908030c0705070501050a050d0b0d0b0a1b031107020907021e0c1005090609040c0e0d15050907030c0b0c1006120303060905 81
    0x782c020400304002d031400a001e400150b02c010710110140c1c2d1511400b00504030944405602540d5402990125211900c2d01550000542c401581103180c5a00000e5449800c4100681801448141d00302072070026001021001d401c40e003400d60300d003401540f82c00e46503c0041e00f951140076254000c02c2c82d41c8a80b0072a00c292a180e03031000d091828021882c03005080c1c1755106984008194040e0340001c00002070300d841484488400a907103460a4541a806070a0444140405140c48030070010840f401e4142c03901641c05443e10354540d40c555805034039008140c03001c2840300ea10701d10000701c1118006600c0c1c50101c7c09440080c0d000035020010f070b9460081d8419543d0040c1c0511820480d800d10341d0202019405134586031490b14250b10100b0010300021800781c0304610201d8040e0b00e042d0340c60082c0340c0c002550000905500385141c072031402d0004030740a909058040021a100e000c2020040300e1000c00156204005041e919146103204e00701040d03040700480c1c14003500003000c003070a1017170754 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 39314887 1250 39313637 39313643
    0xa0e1503010806011401020c041b031b0c0822080609070602031e0d1103150405061002031207090509070801030b070801060f1b14030403020a08010b0105070201030e0c121b0d 76
    0x4011642040c5c14070000d0207420410340d0440c403403ca00c0d07806076500c0703001e0000143c80100e0340d850110f03d5100d00500342e4142d8803103c030865211841030710780f807988807540d54001500481050744642041c44c05001d143e520300700984d020415040d01080c496004038149e401003259500711041c582e6981410b903281d0007111702c0c40100d020307506215111810300f80d00410145104117000140710b0301102c0e10348020741007076907030004d0080b82940075060f0341468443c01d030300b1a0044603140495850440c00940c1c5c1c3c400e81c0359007001c80d00d1400210b86a180504901405080c0040585071245010000108500d0003480240c9030301c1011804140e20034066101030341a9892070360754031030f2804201800c0d00c241380c0d084c1400800090300740c0740704c0101744403900000242c41868085c550f160300e14010405401c0c0e440c0c000074000c0c0d1420303000b26616a004400c076440c0707503420700303000c5020a640f5000d50304007521030700e00d5900180e07121a80181f141021030805442880d10011981c0d9080c03070401d10002c40301d201001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 39316137 1250 39314887 39314893
    0x50306160905010c14060108010e012003010506070f050f06070306060c030e01031a03030c07090c0f080a05040309030f05010b150a1d04060302060c07030507050108090a02041a03030a0e15030108 85
    0xd0159501c070301110b01c400c4e400f80c0c211805081c0e000308017a240035402d90005805964481402d041d580d0280500482c0803a078188280c079404e0340400c5001944010300c40e041c4154030004141c0c0812007511044507004c2d400c2030503140010081c94241d80c451300c0072070b1440d002070710307041010801c180038a841c2041d940d05070381c5840d140c211440040d0028001d00750180c4005036400c041080d1a41e0810044c44400140c5002d81441417034640e2140945070082e0702002404024085e8061315940111400c1d44228510000318490301e8a0600395002510303504050085031b007503aa840300740303e0150031618248106603103191289405544000c124003171440010001001080602c850050a0110101e82c0000400006565a907640068804e511046118400e40c000f000308005014061002100406003030800505500d01112426150a2503c0d002849142d489512200c0b8002c402404598601d020707080300c1c3c2d80d205180001c3c003403021904080c0e10400102c40c0b40701c030724110b00b070a582c100d031040801 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 39317387 1250 39316137 39316139
    0x10515090925050d060801020c120a0909050708060f0f0d0303090c120311011a0d0212100f140a090b040b040305190503090c120303010b0703050706050a060503061609 73
    0x104038200d1805002058080302ca50141042d00c1206600030251010390b4642c00e075503004443c4500d00351a0981d004407002e910520a40041d98804580c00090394035000341d1a0790741c440024240e901c5c038102d03044510380901e400304100354250813450190140e10304076011a90240500308001054050b015400e4100504d042144000b9020790080c5251600c500000810f9a44406845145c900301040070f9001409490a8181030002031085100202001105002c8104440041104040f20807070013801600d1000824004a8040c050f1040c1c0d02d01c500e509010824621035028050003031003907443c44103c890760201e00b04440621444450350761001003600030303966984032904250780040c400d80034404100300c80e803564007480316004c0c64a422525415200d00303021464501e4020325088450149e410105c11441c006c1c40003055a04480e008040281c0c2c03071001e40350480c1d40d806038800c001c1500c1d0038001446841031091f000300d020380c0d01c03d40031510b466640c04000903552203913100f800c000c103100c110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 39318637 1250 39317387 39317389
    0x30f0e190606080d02010207021306031e03170c0405010e03010b0d0f030203120405070f150206010308130518041106070c050f040e0307050a030809070602120c010b06070303050f01051509 82
    0x128084618050304000904940d1010602e080413000210440142d43c00600d2a04500d0308a017001d43c03510907180c0030400103095981d02c82c0003d11031048201c8540041d9809810144107090141400003c0c00c0d640002d800e120b10f48203660740180c024107020030032602c180c942904051080402c80c507001803115040840c02c0e215181c1075942c200c02902140002c01c00030311003281d404a0140036038070500007031071110724059603c1c03143d40c00380c0c2100590f140c02d0a24040010760006415040d00d07040a247ca5540c170a001640b01420030941c003094016583c2c8a00c035407400410010107202d13901982c1c44200042d14001002000c1c8101003008013050038100702072003542881c2c13006890f51500600005030300c1b00e6035555a469a040709108a604d0382c400c40711002007640c454080d6810505010003051500d0070513070041d494a415582c854100c1c480030070650300c0c000094221540c180000341c070140c4d03035401e07500740200900022944141201011000012a42840d03030242c0c000e030152050660400109030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 39319887 1250 39318637 39318673
    0x60301051905030303071e030207030203030f06190902030a050604020c120304030c060603050609150c1215041113060f051c0e010509010b0418030905010c050109080307030c030f0e 79
    0x2400140420300c0307200c0c0810075840410013580984140e8407480c84900e000c0c081900d082c7c840c00102c00070540140049400290008203903908403001600802855036031102281d00341c2e54522124076009280080042c02401c164002c6015540840c0d0a00c0141d8031002844180d1140345088541a40110705201070154160007440d00b0500c00c0c54200070920140c0c5407181940c0941c0c200b43e4141d00b000c42031180c4c02d0700c100958498100810a00d107542c0c54010506482401140c40001041c08040000b8208024044001c841040c009204001d402e03040710909402d50000c6078402c204448403000814030300e00603c030a0400e00c40301d44c1d929107000000221140c002003160011040c0c0c0d51651001030125071300703002d194840c1103c0c000018803000d00f84104815246500800103080204030014004241d1040c0391405583c404c0c04d10140740c070a5031925500400b0381e0340004d841c92601000b80580540d02d900411110710013940c05000da601e0712150311046920b410940f190039481006c44084911242d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 39321137 1250 39319887 39319909
    0x40302010e01020a050d050a110405060c071e08060c040b1806070210081b040302030a060203041a040606030b010503031c05090a0501050406050103032705191e03050601060e06030105 80
    0xa20011952100c480301490998100641d0380001c2030001c03d0f400c2d000003480c82400d0744a01c0103101400303441e100c0c100d5226544214010075016000000365100c1031101001a0002011030f40c41c2003a044118030341200b003070150b50107094824007a110103e0782c4114004103843c01d43d4040c8000c2c620700150b00308400f030381002d885c011035040a000e11010002d42d80300842d901c80c0c005581c6507403c9078074005110001070180300c0c8565205c00014481840562000504118882d500c50710050392900c907410030b203107068000e840c0848846000b00801040144541002048a10500c801c1d055640c030381c2c04040c2c40340a200d0043c4020203525143c10084c041d0780d000300b904580c41d68155807003100c02d51107050030340340c080302d0954509407510300410030140d0289108000c12907445000c04844118034103010341608520a05206502c00c40300c5c0c410b034900240b100401482044054440d1440b03c2c1102c4100d8511884182d0f540d005060000908a010741c4000b0040e003c010300315491a0b0800f410070001c0e51103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 39322387 1250 39321137 39321143
    0xa0309080c0106030302010b03011a040c0302040b03040507060201140f0f0402060405030304030507180606050406080c0f04080607080601020c010906051c020f07050c010f1d040f18020a0509070e060304 88
    0x4400142010980820090486480060003c61501c0c11420040d095644160b0614000d80c50700001c5030010200c070160540000b130403540440c000362000000c030080d01484d013102400e41000824801007010010b100d43c00c4410540003402080421071181c046803c00304d0710a0001c3e41c1000000e101e00f100f03003c1981d80140b0080035203040c280c81d41c0c04a40f440d00150005c40f45503009600a21520b0340309840c02040307002c0e5140a05c813260804900810038003803485030a090002210103c0c054207098403d4030303039010441ea030f00c9803915640c1e0104ca40c0c0c0d182c244c5440700891710440110b00710f54404900300c4c1000806844501c0c0d0585007090498a650040104c101e51450712005008450564002011800751440752181ca406031424260300b883c1202e41c9050500c950040c41e4400340d500b00c61605000c110480440d8455801040030801070070a58120f180c425150181481a003426004450040e80c0251106420070303440b00c05000d0080c9041e9041f0340410802000785095203001c000965120748 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 39323637 1250 39322387 39322391
    0x40f020d02180a0f060b190807110a06020901120b1c14011a030d05040305060109020306060702091f090519050717151503061302130305070b090a0503061504020a03 72
    0x1c4000501c0700c0890503110010096140c107000e010000700c0d17002e2800030742050030102e80307001604995040c002d0045140d100030300081000090b122800343e0192805500b4010a0350420006858017000940c001e00c09940032402d01c1040d081008003d104801c00408080d22046034655084901505040c1c080400c07110641140302620a0010a01450300c1500007259035007a07007485e50041604041480d8051010000140010004903070001403150450700c070b50f44016a25110300000c0b880500c91a100690130074844014002c40600b41c0000805144501034429074035a01c5030300c80010350300300307441c60312000700100000c115040d090f500c1190001d1170f40c145540c0701503500010380c03507804086030010450058114502d000d41011299103111035501203559255103050070004032510f029061454074181e0210b62080035801c9512500c0185411604a40c10b89a648140c1e541681c06102d0f1a0701526030090001054180043c0040c02589811081c42c0c2811843d41800000c5d08001d907110308240d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 39324887 1250 39323637 39323659
    0x30f020a090b1e040f060206070203070b040b0403051b0c040509031e2206030f0b060301120b040302030408100204170a0201020d0509041b0305040303060501020c0102031e0d0c0f1205040f020d02 85
    0x284841c0004c000400c1014100b100441c07501602a0400c1e100920000a640081107400001202107031b004da406540080c1306181600c0d2801d00321060b014002c000c0880100d41d150800804030001120588c2c21000c03036051000340d540301e0041780c49006405542c44100507106d1400426920140906044500f40b04001e0003610103880910680074a54031110219541c6d18030314201d00e4549c001d1101c2c50100340c4546165515003900c0080320b9810a002a044a01785e03804203013010306c03d01c1101c0090001e40100c9d1404104800020000e40c854402c440c4109004d8284602c60394002c1044d20380c0070b4058004d0031354014052425200c3d5405000e400c2e9025683d00d061074020021484c0c2540c0500309680e0000d014a483d1601400310303101600914150740c000f2034002c00c140c0c0d0000c12070350b0b1080c031000d02d162000703500c4036145800e008082e010700c0045d08046011040c1c40e4489a03a0f03460340c0c1c0f640e50700382921940f0089201114001e03203001e460304980e8040d010150400101c1c01070300358405044841c004d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 39326137 1250 39324887 39324937
    0x304050615010c0b060f0402040b040603050f01030c03032010060e25080a02040801090308010612050402060d020912330c07030507050a0c090b040e030309060708130819030f020a090b 80
    0x243c9c02034002c000c1001d0041000d103d0b0961510542e6030089811084a4555045841d83c4031103550510009041180d00c0d0554003125400152500d42580c0b04003c80d60320a100c2031070384015200600070303000da9800d0f000015141c1520104590781e80c0320682c000d42e8484002601c12100a40c2c001d00444c0c4041e000c200c0091000d009202d03855130140260f94050b02541451802842e00d20030340301071030350303103040c18140800750340c41c01c0c1140c501102000c1c0059903000a280801c10800303a644405840740918001400398101a40c810504280040c51a2814205004056810100582e41c00c90f84240034440400003a008a0042c100640102c040f901005140d40d0341004148158003c40700300c0b03455604414090600e03006010700a481203018504614008411641d03c2d0b8004001c68108003600c0080703100300790707049020f040e00341c0c12905c0c9950301ca49070540c9444450180d401100042e18004080151160b980300355120100c0039a900e1803414644403004019810403210021251501d80d840c101ca = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 39327387 1250 39326137 39326141
    0x5010e06040812090f010c03080105011d03030c030405100504080705010509041b02070f090b090f250201050f010f050108060904080f0706090c080619050c040306020f0304050615010c0b060f04 84
    0x2281103c401c0702d80e60328841414480b0030a020b00b003690600840c1c84841000039003210b40780b07056400a10f4202c02c8020003a1a840e050940300d074066406000009088019480110040003644d10550381ca0b00d81104410044507140b0030f0740f00740c000075007000c041440250b2044000700a03074680140041414130f40700c2540d8120589406020300980d000e4502000b100c0002691180101010001041504000c4010480340d13840100920500707804000060420703a105101200d25060041c80300803000324824020f030003804240e4407041040410f00001800000d080486001c2c2d80c01a03541c01c0c113940303812050050b01d1a010300700321014101072181c41380e014174190140c40d1080c001c0f20041010002421300f4000aa0709070485903650300094204007080c48154281100301104110000d92607580c6864801c290040740c1004120b180006000520f098441c0d000d5400340e4001c400b911600d0725071141418542100642140c085040c030380b090004903513031000040e40200e02034418807006100c040041c007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 39328637 1250 39327387 39327403
    0x904170715051503010203010f060507051501030803010e060604050d06020304030c1704032604060c050f03040b0301031109040506060105070c031205040e0a0e030906071a0109020a2705010e060408 86
    0x7281d80b48100300d00d51404030804040c8240603030003180b441d4109061400e80c0b1016008100500c48001580010080100040f0002125011940c81e01c0e5840f40f0f40b51226070f00a11403c480d03407088002040c2180b500c181241c0840b81d000341000e0a05109584a40c040d400060042c1c0500103402850385c08159140032103040000c481400d25611415440c0603907125040022099000040403100c11501d0b00b11021034003601d0740303418403182c6019246000b91400c240c4a0b08010f00e4040420000b80c00003002001c2c43c10f881c490103181903e050321a00344001c03850300300c1e0003a10301da01c00408a83d00d54061300040220700e0188407003170049034803519038405161003600c0c01c40c00a2400107041001c0703080000d802c2e403c460280001d0000652440410383c0c0e0340140707890240324041c001040d40402c0508440b4011559191114201c1503955450180003500100201e401140401c0c9400c0280d2505000d1404420145203040c884541000d00441d003034007101d0240c40e0064420000443da00b041003004074 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 39329887 1250 39328637 39328673
    0xa03020f0f031911100f0b040b01170402040e0c060c06040507080a030903171612030c0e0603040602160b040f0203070509130b100b070b01091a09041707 67
    0x4200280c034419528904001e114858a05810a02900c80184044000e411000b1858542108a00e500440c0b0350309080ea00c1031101c1c0365528007100380302c4110f410b800520b5501c004a40030040100b281005441505141091600320302320003002800510701580700c9810b00d074001c03046903800222180881d07090740c03213900414055440001000104a000c0141380003030000355000d081c06400341d03500540f4030f1707100e400003d280840c500e6213109010355400a60b00f0601d40300c14000d65a0070b85041c017803110003a81d0090f078006401c10300c0040c00c2da070081c1a070507223004c8003a0030185580c2e565150f0400070b42048200903d41c1d5064003905000c2507501e48014021805465144510307041403042528099996101600416030300d03003044101c5600c041c2070759815420810740713556540c61154480520b035131500a248e0413000401d100c0140701c28200340505039040e0104c104910881d4000454440480d96882644484480005170014007110702882d807203c28000c01c5810000706a03a9400c1003401c0e82c00720 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 39331137 1250 39329887 39329893
    0xf150d051015050a09020903070b0306030102071707050601060206070903030c020d020a060914010e010509091003050319170c040b070507030209010b0d1808090409021c06050115050a050a0804060e0a0302 89
    0x10300407458131000d510000c00d003140046281001c001c0219855038914032034680207520200c00a00240c4081d011290701c20351007869400c00b8118506061290341000c1e078150344510403007002203040383c00050028060380b020340b94050000c0c17940d27a0880320512107101c00c03a0001490349a140050b181c6040d0200a09003e85452146038101721744941080003401c0d4290420200d01007008440e41c0000449041c50300c01d881d5040141c2d01c82503921806804e6900013001e038840028184004100881888200159030383e502a1440d52400c07030208a15084d14290000300b000c02040005400c044005c081c001d1156003500d00c81c1e0703030360740008003c00310991010740c494400180e200356042080c400c150070000140781b60700b1481c0b004d0300c90b90740c0e50149412884c010b0356500c0480056550700c2401322225881304010504444203441c1c0f00000e01420311807d4000103c16075a5241c95014805032281b1144950b55a8100480702a007200c003001d0150054034440c3d80c8540502c40d4200a000c80c80035907001b9002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 39332387 1250 39331137 39331139
    0x110316140708040b09030f0a080a03060e0603030409020c160b040302040b03030a080a050705070501020705010b1f120c110114010303020d091a0906090307060201050f0f150d051015 79
    0x2510002444140e88402002004404005400041075600fa2850300c03400d030792a2601c03440441d142c0302c1c1240d554003191144694860800515000030800e80803907130b0b01488010b686203905c049181f0150b0b009581904144014000ca9040e80d014084030390304442112034103603507400ca2107030281c101e03005402c81450004050056003070030301039000074600a4000f0343c134048540000130300046028050115581c0ca036008190058450f00c05e9801440c1c01c0030085503690000e00c0c0090080c1901e182c070900032680184c2800324019402c40b031842550150701c90ba002d0301c2d80c41501d170303004080600d400c41c2030101078084404071050074403404000100c040501d5040f5415400c02a18240c00c0c000e0080030020040d030280403e00d0034407260740d12032044143e00703a12000c41070002411030203051082c54261203180c1001540e40c0d41500800d00400b103003812480c450f10740240402c00300c1c03000c65400b4104811f0011500e0241001042c50907001d00560039a0761200e5181d0070301041d940d81c1c00880d004040ca00710 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 39333637 1250 39332387 39332431
    0x91320031507020303060111070503190605010b070312020901030603080309060415020406020c040906110f040905070e090121050303090309010206090a050a1203090c030c06023702041103 82
    0x4004103a541010814800c1c1c2e10301075030003d50700e102c0200114100001056a80c54111003005000c006e014010103694142c05004a285002980b0003000ea8581d400d0100018510120408581c1c402c2e416036181d041c00a013070380c1144065403050b00da043c101903851100101146d685c0c3c0145000d050781c40082e01182c200b074200718101c1010100e4000800d803040000304441e90f00000d0b49401c4440c1500c000c120003605062001c01800c80c107990448401000946030040e070b510384014419108040c03030401613500c51110484000003003150483d00446180014414500040c145c1e45003100030000d282c00742d6220f43d0320b641c216001034882c25480d610129240c0394940c1c0610486500c200803400600700c04a040d103c2e59070b90761451802600e4001500c0d50741c141d6038400d400000d4800e130003580d00c43d4096582e140a021005107449004010f0117070101000714030074a40c04120610740194041c0c6524980104124450101401e00301d902c50b82d11000401d03140c610b0005140318042d02c1000c9401114036403 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 39334887 1250 39333637 39333643
    0x516170a0201050f1515160309050108100b0405060c01180602090f0d05100b06071a01050f04050f04030302030a1805010b09010605070b01180b04020706050613060f0509132003 77
    0x2415000c0584d44002c1001411101c22280c03070304150b0122070384504041000030890042c401d200c0d0a040350b0007141c8481c41416004021101100c02c00e1740c0b6003080765603445284510303410b640150107010108110810085ca06a000b60900b2050030700005101500a02d480c154018041e00403100030390045a4142e041c40e0500500304650340a803000654407210b07a4a01e5203801b013201d818402c00d0381d1500a40180c3c2c40c1c02d026101c40d00e07441040c100080740c10008215100360248034a40c46000080060b500d10308050103110300800700c0303204908842d2981ea5040d4080e41000340f603141042e80d034598903881d45410340c564001d5203014400002d201c0a4150a01c889110141c2240c82480410420a80050700180e0410f045810200307106803a408243c46180c0a000c0c91900958094004aa00700038010603500041c0146401c0306c01c1400786829090341001e1b1442480754014072500400d04200c6070500786001580108001c00302500c09040e50b94900410340307002c0d580003c1c15006004107000f41420 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 39336137 1250 39334887 39334891
    0x1603090e040609231c03140106030501140d020607030c02060904090b0406060909120f020c060c030c0601050102160b0f09090106080403181203050913020a030c0e041401060516170a020105 82
    0x5603440644c08680c91107126a03910038070a400d83c0e26011a115240c0c028401d61081020080c1c6414200d07465940e0304000303019080a00844c2145a84d249040c122480c198048840c1260b000d0a29030500c980c9807825542d500d00100181c1c0c1042d01041141d9450343c41c1e21a40c40418450781c104c12007801c09007407540480b8460740016580d00e1500a00c540890ba140180c520f04c14020700d000d40c65030031001412400c1810742040320780c00000101d485880c4050100252004041d40b208440840e80d036500120780e500c0460341c411a448184050610168806500510300f02080381c100500e0280c004001c1100c03110300741e22100c0000d5443c0103200c1010ba000c04c601e41e4030304894507046a401d041000c0d01040d0400a68014140200040c40945035100c901c0a01d05000400c1021074480c940701a024002c0c1031060713601c07800282c841510b4846403a0074442c03000540c200304072500f000c1e0300744403050311698400f02c8503141030013003003488100044c41000b02241081d002c440b4144c4480200001900351400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 39337387 1250 39336137 39336173
    0xc0a18050606130e04080d021303050d090b0a03020a0221070302070b090f060904420e060f0a0b0a0513050306040302060a050709080111090306010b040b1603090e040609 74
    0xc01201034441040f000746401d03a0000c0854007800e03240c03890006418807403490001d000318000310b000e010f1206c00c2a9a14100c0c1c0c01741c416240f1001c40c100382280d00000c5801040d40344082400701c010340612a80c081c01c510045070045980306d80b02520840580d400260b501e451034000010140209a41800324800512a00f0032039810031628500091410740c40e01046800f551000c211203076a0381d140d4100850021980041102c81c4c405c07800c510411516004c8640000007000f132903400c10304071400c1001e00b150614546640b0a0b2110000c00110b01448445254020366100020a54401c6100100801c9803151921641c0d181e0360f84a0705100c3c2103940c01144030381c02240402000c40d4010810130b0b400100207600091a0383c0b90003056600c040180c10202803507103426150149074203c0d80040c0201e200440c1160031607a82c61901811500c250701030000900018044400c1d04440d0070600e1558074400e040807000c154450b411100c80c0a41103170b095601b151280f403200300380314480b92400000b9003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 39338637 1250 39337387 39337399
    0x2070606120305190c0212070509060d0b0a052d01051c08070b06130c02010e0609161a0712020616030204052b0506090f010e070f03080c0c0a180506 65
    0x4020789014142d80034280c204c100d240800f0155000191048007001ca440c1d50003484d00000c1c0d0840c20540b40e03145880d016aa0140d40a00041906460301d9280744004a82c04040c140495580945007009407801404941046c80412415505c004120242812070304031500e180d401585088100000c1c0203c0d91180707039122071852030340404a00250704540840d41c01504101858445002003220403036082070011119140080781d0030090341c19000309404440000440364103450b0780e07882c59101c01c140c0b01046084c1c044030200300b00020030000809295252904030904010150302e4040e44036020700c3e03409005070007680400c41e0401c0003c4d014000601d682c0780c210304081c01c04021a18a900005424402c1117440003e1001110312101101a16601600b5194942403813044141e82e5600219400304550030040c82c0303040d55100080031000c80301660601d1302250310b141c940343d0aa0348112440040c40c0038201402080f91174080140000f404001c1e14000130390308030341325541111b00140c42c041c1f10340 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 39339887 1250 39338637 39338669
    0x20f0c0714060d05060a0f060c060f0e06012d14030d020f06071202130e0601080f06180402030f0601030308010609290f07060606030f1112040b070309080403050102070606 75
    0xa00c4080c150342155118003000640b03070f205c000000b8181c0003241d10040c0701c198400b80100700964840b23890740c1243c1c4680400c2c0702c442d40041c001c00a451744159048481d0b44207000400488005d11516800424480d0b02c00f016494000e241071300300c1c101ea41100340c4243c0d403804101d001d800c0c200110811901d051029060803680860380c541c89103009414442042a40c0380202004400da46c101c8010b145c152007654801d40d56200641c6000c101143ca080c0440c100700001040e40024618540c42164014803000d5450310125031454900d4000d8026600740c800c01c0002610700c0c00402041f07010f10f02944500c81190314100d0b00420440c220f40000043c0d2150181344802c585995415030030f22015850f00b40c0d00d81c58102090405405046000b414060a10310005603c9400d98403090600707015000c14001d108403464082494815480798104a412440c00039000c1258134640c0c58001000c2c4c6000308288042d40c0743c06a90390000d8000b5100b6941c006400341c104601481000c0040008801d036002d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 39341137 1250 39339887 39339889
    0xb0705070803040804060f1b1103070503010203042d050c0402070303020d09151d0601050d0311032710020a0201030504020301020904021216030c140703020304050901120311011109040b0a050301020f0c0714 90
    0x23034440103400424038041030001c01035581d0240311840c05084064000c40d2030740707010f0500d6400c507207510100c2000341d14544124030507040700c8041161a590004000d120002042007880000d5000f200240c0815909121082e1a501c180c00b808003103500810480750b00d0f481b03d078401070441d0882800380280082c03030081081e414201003003803411030700c0403034031080c003055242002c0e103030030448a030300003070314000016099185030480c1030141903203244400302c1449045c03820500c250b0143ca80840f40159011f04519001984260011548148090000750502ca8003a02040680c0c0050401c008400345c21002c2105818601e482000d291200d40340a102d0280c490318082c0c0139080070110a00703820400030b40f0354241802001140e009000c003500c6126a9a942d0f140c40020035080384080307000401120524888000501401c003003011b142092070319180c4c000c1e0030080208000010545c0050903510001456a030078806003604070460740540359121180071846062242540000c030885142c28518082 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 39342387 1250 39341137 39341177
    0x80a0806041a0d0f050a120f020c0a06080a0b0d0b01060201090204050603070b040e090a1a0a0e010b10051b0304060c050f0d0c0201081806010305010e1e03070b0705070803040804060f 80
    0x300780d4004c2c1d2410310b10320f02c908103642081721612004c3c3c00300c0009440040241d52081c0e100c21600800c1d8255202c201c40d130000c00101c41910312404002514040100b40745000b140d001c01255800184000350040c00d030341c3c50081c440c0090f880100540d40d2100f0a40a41c00d007406043e0f4459002c4001e0401c0c00d0600500c44400d00407401000c0b920780384680040c401d1507003040076104003a00510201c19811040011a030b030210201d561113503160030700c00044003405050088a00d4014010040103014002d041c2c110703071903000880b02d20a000401000d4052200c8144010301c041c0200c0d030780c0c1224140a6052035458a6240d01c22908942d0080040501555001d10700f0503000d80e0910f0055056201c0b20403070395420018226250131130107060b00010400c1015403040341c02248010079141a680413424080300706200d1249100e440c5c0003088000002600c24a800c1e5000c3d440341840d41c10000f580c0c0b40d108094000b110304446c00c01000131306011058101030400d11030045c138600418012401d61070340e20 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 39343637 1250 39342387 39342409
    0x304030e0d0501020f0301050f030f1b01020102120903130506040f0603090204020c1014060d02010909230103140c040209010e04050402060d1a04050108070305070b16080a0806041a 79
    0x400650444040d4541c1c1e8400516038100d400c00000e5484521035254a0310540c020b00c2194400d02140020602c41e040129a0040408402000e8541c00810400000307442901483c0c0904655080004640f540b880e050058018034010000716180c1c00c40c0108041c020003940c0183d80b1601050008008481298001c0340545030140780104401184d440420041d004000c019000360041c00c4c00c03141030740f210f80d2001020243c1c4e515090119180d81d01440314030140f01c4006400510580b0301400b0002d410342020318600300d606642d003148102a52500b920380d40a0700100d5113603482001410041e541000520000c01c02203d003140341c051482d00283c543c400c4c84860300e02403521100002c003035541308400e07200b03152207800050000c41d600d00d0040000e280c10001c460710440c589400403071030150029502c0b0640340c2c018001d151450508920b001c030f581200d9460759440c0b13154081c0c5000600040302034036100c0c2450f1544c007a2410514204005d403a4818405031001610000f171214503540c00003120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 39344887 1250 39343637 39343643
    0x30f0a090204020d020a0e040501090501080a021905030d0f0815010e041e111e040305030f03090f030f03090c04050403020c010507030203040f0b030f130c03230709051b09060304 78
    0x50103403030324030205010f4081d100a40f0f0384507201240d0034034900d80240406584902c2254100440e80e00c80e01c0e60380c2203c00a0040500c03030f600c5a114203005044c0030300c209500100b0402d01e800c850399100002454221001030b6500007030005501004180d4102819942005082c00107a907400300b10320000b4011604000103d2086845085100d04034040c2c1d15442e0100d06000020701802442003d1030102e40d0180610140c60305152141012840d140d8068409880d800400b442c41c0254000c0100307510340020b8071407802805091070540c01114200020200001a030182c03944903d8101c04c198100f510100c6014060b038140020000000e0707000c82c00c0c0091501c2401c0550f00c0c1c020a05003249980601c0d0000759201d4140980480c4100781c07440510b00ca0311013884001d04641c0d40c80055221080602d400a040030034941d42880040c106003406641c1c7d954420a4504041000c1c03d26840e01c3c07031607805803400583e90000e00c8841c40040e0b002170a0311202c40744451929040742c0103d1110310000b4805 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 39346137 1250 39344887 39344891
    0x904030e040213080c130510051908070e0402040b01030c09051005090a03050a060524040504060b0d030c03180303020304090c020703050a0b07021506090a0515040c03050402090c030f0a 81
    0x340841c0d456a0645a401d42903c070304404007612205241e982d2410f0351101d44c480c3c41c941c1c40804148507070b4021a0303c6020b00c100010307103103032801c010310400301d10714001e4000124182c407004c21002c03810000358005000e20301d00d0100d5424a8010b0000701c58031140c11b54105400c200e040134410350007075074960443c1c005641117500b100c0051001c49030b030702540c5015a802490038500009000c0d0003c2c404d03402600626042005072202d8a02d42110720329085d070806544032403009060350389495849207602c18020700005c01c0d500354407000a4100d0900d40c5003240407401103910394090503403111414100c0300785451120601411074038041d5684c0902d106c2c1c0700d14241c55584602941e80700b4007402c401568403c0c2225401c00840c0ba18507401201221500c006100f10b80125844010300c0846030301558000e00990b030141ca80e280706c80701a15005100152210405103454000d480d00d21406039040d48540c0c0020702400c0a07c1045600702c030241c0f01030726150081c030501038184510900c05400403004600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 39347387 1250 39346137 39346157
    0x100e01020106080d080f0a0b01080403030b0f060a030e0d021209060304020a2c070302031314011d070302011e020312040309050604150f020f030a0f050c030409060510020705090403 79
    0x100c0c09007a0940065003140101e04404c000f850f040889580210600705111602da43d1741c807804412140c59100a5000508002c04140841d020341d00200011102a08039001e521034100410280c3d03010118060009030b440c51550a0a001805102204e0b007103840940250083c0c1c000f4000c0a000b48002c441c401c00c0000082011903039140703000c00040000b400e01031003846c01202d20810743d69511500c0c0340360004060016900754070900c2104d214820b90a14034503141d20507161204402035105255006668481c400a40c41491041c000c000105200007051403034150310005050310004070712034400c1038407590414a40d540200070781d42003440b40c0702304900c103a0b51418206c529408550003941c2040700000e010400200f40060540c404000e511081664001d9480403a540c02059400c0794142d00300340162030429106031700c559040c1d100f600c1c0041c1030601c80d40f50541158416480781468517a110010045410301c6d8915400c0503540d40041d0413501d2800f804100402c0000308010b04009440702 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 39348637 1250 39347387 39347389
    0x150d11040b07030e031f02160203010c0513060801030506040303050403020c03011a01021203060607080a020703060f14010b030609160302041e0302010e0607120c030516050703030207080a0510050405010e030c010b190302100e 98
    0x84200855038008001303000c0007800ce84050410fa00201880c01c0e048081000462814002d09446040f603a00500410302640c41d0b8074114010000034004408501405909103080e0742d0074000da001c40c80340c200e41c0e407210201031000640f40071844a840c0e4143e080c00d00801801c0c0e660384058610b42600440081c1d5951411a070072401c006c0541c00040c03d09161001064112405030700c505c05401150301c104115907219a601d0303819000882e00c040d0f00c20719500c00281d2014030760b5007150315920241405801d0581302c98400c840400e50b111a4609840d40b100308000f507613440307a6264480d20f82912602d01c2c00d4610f460340048000140011010f01034000c0b050b400f0540b04170112180707070301c0804411030050701919006441c3c13911484258010301c078141002c1b0302c504c4041080d200c40c80d8084000c2030003070320000c481809050000c206403255580c2e200b090303010010510040c00303050004000010b03952111410800d6030f5480c0c01070301c01d19041401d002d2006803582000d26a006001d41403001c1e03400c0c5a50 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 39349887 1250 39348637 39348667
    0x20411030a050103050601060516060e121204050c0910030b040203030417030309070806070207030209060f03070b0d0c020106140405060406031b05130b150d11040b07030e031f02 78
    0x5694520144000410000c15988035801030341030760322541c1035400b075076600c0000b00c4060160b28422000100300c42c2c052030010340c81390702c4808603820410076280c0d005022485080290094991030034043d41d00b004100070005e090200f48207090041301da1640a04000e0040a01d20440d0b000042c0300701220300c04101559000c0003502c0c0103040d80140c0341c0c4464035414007603440360800e590816803071240c10f43c0814410400302d1150300c64940e913802014a5072650702044180b687c05080c050b0003040614240c0003684060180c08060100c141003a6500c030503500421013180c29080b8040e0459243c800244482c1d4503410ba0781e24050750441d404111a101e40c40010000e2240d54402003a151800807000c102529034100300040302d5046500b18205000714800c04162804c5030045075000944074500780710800002d001c4d1850622400300060003c12504095010703501a4100e185031300710210381d20080681c4212041500402500a0444072420320020181e446e100760007190240d03004036618031054044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 39351137 1250 39349887 39349901
    0x50316020c0a0306061809020f041a030610150906080103030f02010e0f0c010906030902060406050a050c0304091d01150b030a020f0409050a180807020d0f0219061e0504120204 77
    0x1445080360035901e04d001c800030140c07803090708100d441d11801805e02010364803c8001c2d01d40c000d000601801d59410400000742142062140000e602d00c01840d881d45080107598460311081c0c0d00281c3c8141041c2a11025910001b00601000007101c001e0242640c00804141104c0c5d050070f1620034007000ca58281c0c01b5024079002410306100389004000c50308400145001000001e8031022207040d22440c080b0161030b08428040e4021900700000c001b200d21070300007003241e11080e260042c1058017100850741140c1c8035510811910b1380b244001360b080c110403e5030b6212072241c1002000029002260403801e850a4800e988012001100040d51800c5980484040b1306099400702c5d611a200c1e59228000c0105840c140000c500d0807042e42221748140841c903034400e41003100b480c01c0c04070303c0d400c0006030486103c00701ca80903424010f400041c0c44a503036000c80e84903541e040120380d41c1804401017101c0b1094910540c00c10501c10032000f403d81100444059401d0090080440c030101d0010502410f06 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 39352387 1250 39351137 39351139
    0x3050a0e0307030f08010609080a0f02030712080c10052205100c030501080706020c03121303020a1403060901020307170a020714160b0703050405060c01060329060907050316020c 78
    0x40002c00b241010340c03140e001c2c8031410301612018003036601e0394401c032240b034058060714080da03109007150404201e1461061000d540f0003000c850311203846021071816414451000c407100f0402140f441c3e11110180400c14a0000983c0204401c1c50600f10030150200f4107010341000c840f410f40c11509100050008010445040c0c0d001e0012581e44500200101000d00c00c094150040c550041401c40c4046061004a41c0040041c00d454130903070030b2020b040d480305150025405c1d18540020040c0c9803802444001d21030000c100458000300c10030300d0b00f0010000d16003021a441082044107645e00700c007808070751800f0f42d8203d908030b5560242c21030007480b070108050180327201c10444448942c0005a03082c01c0c203100c52048144145d17110007802c4240180c410060105105010600071400c1440c060300301c1040c1040003050707403662526540506200c0740c070680b55408a110611000c0c804403070f0346d99000401620b21020b50314000200400b03901010f404410a80c1c82c424030a0a20381c0b0812855440e004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 39353637 1250 39352387 39352393
    0x15090a08030a0e01030b0a030f1410110d14011a070206070203031803160612020a1209080405012304030b09100507050403020103050c0310050f042306030c100e0103050a0e 75
    0x4a010000c0d00c5408121000e134000b074142041000c45007015036650f422030b513018001904440080c0c1c1c501c000d090f038090495050b8480d000110074942d40c02e00840361482051400b151351014411003142c155008109036a40184a610040142c18010034050981c500c9011549854207030724800540d0030700c0b0b0040d0207949807001188034480d0840c0f5030709660038030b40218200c0d107607040480c072940404503103441150041481d40c4204124200e1503001024a00001d1400a00c842c0643c06800d04883d460030094035044400b0500780f03c2544c02515030840c11070703049000240c1034400c0303c174001c2d1403244e404001c00caa0038031400704400140c1003180c141d141e00421001d1119142146000700b99800c00e01c8181c0c0040d08203c0845c0202e120101160300130b211111612002506103001e1013442a000c1c0142500582c1d22142c095a40316503210030803a040300c03c0501005801d0410400d0301e0407003034111903071040756a0828041c0070741c8c0080401071404c60a0030003180c5a82c9015550000b42405103900300c07240 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 39354887 1250 39353637 39353647
    0x9020d14100503011b0804030f050903010912030b0103020c0619020f0a0804050c090f1303050d0e0c1002010b0616110603040311060a0608210c0a050a06140615090a0803 74
    0x20000300980d0540b1429030081210328080c5001d8402c844907601004081002000030401181c072070b5071000003460a5091962410701648086821a0b0440505803100d0021403d115640c6c0d81c580151000c05109203415810007442d8416a42c0361480582501c20f01505c01ca2904c1d41000709030180c0301041c05c401d100f5622513403a101e001e4031100045030102d9243c00340c00e103030240f149001104240985035003002c03100c080c1c0d03c0701c5c16440c1d055000c040036401d205081c4046002d10045e80034421702207284002401082c2a802d040c003141400700e1402d1415641822032a104940303e02003502c500802d80f41e215011480903007040d41c0e603240b2858038075400034800410401490340282c1d207101e01b8840d500807a5015070f03c10307001000b1205540140e0030244c1202c540c21540070000034807808007400c503030341040c034140c80c01e840c1602e801c258840840705600107488107800e1203000d204a1348055082920480d41d0320707005001030308005420b40301c86003115001c140060207480e51617042c0f000d0302049045030399030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 39356137 1250 39354887 39354901
    0x703080108071e0302040b01021513021f05030c0a090306020a05072a05010f0201020c1b03060c09060301180b09010303050c0106060201021206090402010c0b0a0603032709020d14 78
    0x28110034062450030b40300300b00300016141c051440380744600190101c0c039510181598200700160580c000010b0461040381c212000100c203144450b4000c1012812494404256206110b0501001c540e60040c0240300c05008489039001001c407035220102001090307031050042d8098a480344160800f0b004903101017112446240c1200052044600401291607072a44003400c00210300c210701030071920012540c40c1005994021900520301e2001c5000160400100581d92450050b22500b1004080e4050441c10464103003400700e41d42110b40c0954041c9881c003d540868214407040c407401d0804510b0780c14403e0965200c5c2d20942c1c0c4410020070081441d60b40703041c0108030350081e148408141d480c101000660500500c02c5609842110b61004000d5071183c0403c2002e120080c026410b10007a248214001001541c1c00d03881004000d41c0041d0303c070305505004140d04603008180d10500c00d0540c5002c0b52180c40d41e80300f03088841128015039160b1000401d00c000c0c00c0030070140d091104a900c00c2c0058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 39357387 1250 39356137 39356147
    0xb04060f0e1b0603150904060501060f0f021209121506040b0d030903141903050c0610030807022209081b3415050304030809030415050310030204020703 67
    0x4441800903040c00154030310304250b41c03a40c0c1d440011503114040100c1820a50070101e000d076070701c04061180c64524400d031101040011808543c00ca406550790300052001607008200d9076104640c9103000e40c490400c001d8003035076a40006030b1440003d1b0740070498113060342c2d072154414510300650b000e072040c601007848007480108080c0d940c0b40c8943d0074400d075002c0500b001140b10f40e042c3e416640d150901c0d861a03c2d0002031810741042c105075801104006140100c0d4501202d068a00c02d41e01c05079a000c0380c021090900300003500c150301c40e80c450b02c800c1011910700c00c2540c0415404071000b604501e969810300701031944102e07400c40c41d00e0502d1046014404d0400140ca101e49500c6450780c008891b42c0180c54551210a000c4010380e4000c2040001c0030a030080b41c01c2c00c048034021428401511001c508030100389240e480d900041d4000300300000c141d8085080b07504200644011030600d42072a80048001004240e0f000c100103012000403004c0d0741e0490000021078000e841190344002904001748 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 39358637 1250 39357387 39357401
    0x1b0408061005100e060304080f0c03040609050a0b0d0209030a0b150a17030f07030207090204091a01080c031501020106030f0606230307051e120c01020d1403040b04030c0b0406 77
    0x3100c0080d0101c00545418201e440220b45800ba6450320402241c2000f00703c20764101074004e480b118002d1003103001d0a0070b0b0100520b0250001001951241d00d0064003c5c0b9aa0640d00224001c4081c4c0c1c3e410410400940c00f82d98041340819800b40e110301e035413004030789891491080500001ca071107003070111880ca507c40001e6492429034410b021280c65048170784216480582903c41c0b640108081e00090300341c24050b041462003403043d81c42242e0340e07909250030fa030440d8201c0c14115680d0142110b100b1040e002c1b42c606d5031428281f0280c03034503060102605500000f00001ca2410314000103030282d038801c0d4480c0002d19031050528450107050b040c03541c014420380c06060004070b43d0603600c15240c09580c0800c400180c0050042607441e04050a00441040110105558642c20b0251020642d2014401e00841010400600712400c2e800002484d05142086120030b0103600801d40c5140314a800403a54402d8101c03880806503107881c64102e8051034000360140114032000305100c1004004d421043d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 39359887 1250 39358637 39358651
    0x70806040b040b0d0807020a09051609080114010603020c0f01050903090102061e070c0c05040515040501050a1805060a0312080f010605090d031d03030a11160302030709051b040806 79
    0x12180314820709001c12501d460300600d901c04151200741d400104064010b08003284045c0001e00380c16070321400c00e002d0350760982d6202d9240001228032100a548080c8550081000d070000740b1018400692100c1107001c10b001e16010950001401540d4000400c0918009902a402048585012240c594a079040302c04040d00602881000c00e04641030805481c17410b10a04101410a866510702a18803c03900131003102c1170341e12a00d0000b0035689030300c00d003446130794012521240ca22642003048219441600014451b0042c1401403024901003041a06200701026000455840e0358002134103034445903200800c07200c0c80d821010302c00c1d54051445800341d80c401480d880c0320390701c9440c02d9038940030b21132456420444011001011034400c01c00580321074190b0741c14102e0070040401181c25980000c10f0840420705c0c2e40c1101103804010804500b11109040c0750180c040e0841e80044e481c1c140a108601903d03071501c001c5030203c0c4404070380c5142149545042c6650b90355a43c8501d848407421503180e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 39361137 1250 39359887 39359891
    0x90302040b03010507050f0a031b020d08010902030c07030c020604121b050301091a040201090b0d0204210201020a020607111c02030f0c06032a04030305130909080405010c140607080604 81
    0x501c45810140030302030040599481d02070600c10a40d403141506e4001184002c1055160884440c501e01020b21749070f6046000e501800325010040d8000d060b0b64410307802590158810020046074030000c0c1300765624180d1603d003155400b03030280001690f40c0190313080304041003100c0e0310030810403c503441d041150302040c0c01024162582e4104041c00c070345103000040c06e03601c1c5c2011700c290b0f002c10f000c810342d522920504114101039114400028103400030064400c003290f000a0520010180d0b240208207a800442c2da24488841940000e407101c21140d4000c3c0101004901c81c4200002c1a601e011786400103000c1e2105038900c845250345210215030164040e004150100e1424840400c54807808180038101c00d00e135494010380280d251400b028454001c1101d0201e010b26810301c50001d200a600941d030703058465600305004038484603141c1c0142d55540ca000451000100e07400196802c0b0740003424401d03201589400d0602c007481c0d120215090034002e80d010826882d1b00407440e180285400c0d201 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 39362387 1250 39361137 39361151
    0xd030504031106010e0415021b010509010b0909031209070902030c0d0c08041a07020106050301050406050103020414010f09021605010f06032904020d02030309100207080d170f04020102010b0a0609030204 89
    0xc2e40c94a000703000b41c50083c000000042c1c0404e080c2c11504029401c6900010701e003082d800700d01d01d03080b0360b007107052600c1d65120810310000f030109024101d00c50303c04039400650390602c00c0da450359030302c1880c1103001049001700004280100c144103800082080420944d0750341380408a03201182e0043e030048041524140110704a14455030500384240d501c0204080700a40c0e80a1400750301c0d800404601c1150340311180441e003503c00307001e0a400349101c0c440c0410720707504510401096031183c40503e1150103000004014559204640000700d644800005950780f010341b03059100001c0d0f560000d0003940c2400141d00c0040701603070141045a000341c6951039000038224004516040c10701048800302583c01c085030241c500040084100d034030060840380f804000c04003003051041c4182d51200544c002d03150402100320140f00e83d140034078072440c060210100a44060881d040003078000040300081030000740459000f54820003030150700401070b1600030341d02c5000821080701070004070b014905040f4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 39363637 1250 39362387 39362417
    0x30a05060709060503010e06010e06090a03060e010506030307120e0a12030215062706040609050907080705030606100c0c030206030109060f3003030902040609020a030c0207080c0d140d03050403 85
    0x1d586c1070b00c0c2000c012805c5a02c40c900112a00e0392610f060305da100200700b00300134990f030700c410058005510400d000320302d2004003003056084441c02401c1d01d02a400c104049400103010300c1611180d540c003410f00c2400000013402145030136095070490740050601102603c1810b8000a00c0a0201c0700c10300003108507075521040c0106540030180c101440c041c25840d011003060007441c0c266014034080d000182407a91040480c0c01e68000303a034945419040140140800d80d0240000740203020103078005d1519050407004100000310b503603007001c10049581c0c01301c02041b1260000200964000701030f0341d01c03961517981107001044940309140007507079244d20002c1c11203031031401404500240b090743d484c1c407080c1c54440982411004012001c06a40e102268010382d6a4401c141c054040500e005865811240016040320005142c41003503500c880003c1200000003e25160403184c103503a10512240c00d840d2114401c1c60040b605031003405955050130005505501952140d8043d50780c500e01c83d10001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 39364887 1250 39363637 39363647
    0x110312030a050703111b011514011806051b0309120709140f01090b0a0807092003040507090c050903031801080c0a080c0913020703020d090801180b15030a0506070906 73
    0x2041e00c20743c85d500307204012583c4085020a440342c0c1c0701c00f002058007606110001510700503a00107485040f07020070040c040c1e592152001b0002401448050aa5802c01070090420300a0040d0404000f003401240e80307044034188107503504101e000c3c007010f2014000c83d440c0c6c1d49582447c010740401da07107490b070701d444114051118507001e9056886100c140340d08282c200000752400312200b80d0000040d043c0007c00301010001940100b185000010329031840c024506400000c2c1c0001c841e20740c0f4248240004200081415001c4401424002400f191011000e6443e8050306981662602003c00d8000c039074420140001070286003681c2d03203a059510025003c20f0390090b610792000040d0900000740c0030500b4003008104001004003c50000c103600307440130099030b0054104a0050f00320381441072010b070304130402c107018082d244020b0196950070300041c116420311200280100d4900340c08158424842001c005242c034014054855903085420115981c0ba01aa008400900c2c0d80c10001122441345d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 39366137 1250 39364887 39364901
    0x5102102060f03070215090a1101030c1b0201090902040308130501321317010b0103180201140904061203080c070b060d05010e010f0609140105010e010c110312030a050703 75
    0x14280d500b09074580c000c0311401c1e00001c01d4842940b080341c019080c68040341c101548113000007002441090090300e048141e100005560328185402d1481880320542c0142c031440a848014481c0080c110407800100c3d081c2503143e001c000400c0c4000350103c140b18060008010100c015a00c0501690782d42004450503170001030402804c0c03541c25654210a24000c4003072a5045069280c5030a00d5051108210125017a40c00104541580d001c0c4010041c403c0c080c1d800d00d8482401e04000f1b600c18600c40600040300300c1750090400101100101c050508201620910640600304102140c1c0b1514400e403540704540c420303404102c42c180040c1814041a00b190bc09a030300200000c01600e494050090f0613070303241c0081300e0075521114010308611003481500a900303401c2c24003080703140c60302513450300301d4240700319010004281c80014490350760001101c244405080c83c002d01201a0f40c1400c10300c42c240c0c0b6400d0340d0706015440e10700c06a08211000b035401058840300400107a1034100b41a0110380c85 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 39367387 1250 39366137 39366139
    0xb0a050108061302090411190207030b01151e080105010215130f02040b0415050a0501030207050c010e15030403020115080a170c030403020a08071508091f060905102102 74
    0xc120000700503040c141030070f000f8040035580150408005c07400080030340d590110400440b84000c2221401c0ba40741c000c5030b15062050380040c256807800c9d61030b441c250700c1050140c035100c07424101e100d050251060800ba10340c4200b10342611003002d4230000081c5807820038452140184a84175280325645810003c4902640c050764240e50100c0342d81d640d407051410690002e980c40380c4c0d5600d40640507201c42c000c036000c01110041290940d410030040140c100d2150304035904251040c00010000760b800540e20440c1202400c00401014111001804184a0303103200291001c02000340020076405400c980403018140030403c0d001e544809180e035495581c000c0c050800c0002159850641034000c004002e003902000941e49459145d40201d0940324655100a00945c0070341c2040001c0c4000c1c0e204926448490700d812600c60078191405559600d00100050b400380091585030103006c82588800c0040c140c2c000d040c8075520f099000c0c6450702c406131107110702c00144148960f800c107440517500e00d040b80c0c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 39368637 1250 39367387 39367397
    0xb1e09060108030d0b0a170d020708010209030a0609080c0706030204090605040209300f0705180405060c090a1a03041403190e2b1a060a06050705010f020c070303030b0a0501 76
    0x40c0305440003000d0100060500d03000140680003003a800400e01a47c06007844141c014000a204004000d180c1031032603102c0c40250340705001041d1665404500f0f07071342150700030303201280e006034034240440c05100e00e010440e01482240380015a00303805030050002c130b40d050030041184940d44c3d000e010503885404801c5602501903c0214680c4a12138603040241516230036042c000440c024000345001c020002c102c0d000d52220204100b5842c09940d039203440e10581c42c0748601b605140e0381c0c2650310500500b20783c40d0a130340461760f00c101d41c544070004001050200c0340c00401c5254040511740030f5005880070744403072400354036054400c5000011034090046171420038411000d190004c86594201d002e2555101c0340b00041d011201982907030030713400b1840312582260440d240e860300f07509003010b204800c03c4d10111481003017095624003c003e802c40e01981411039503450f4500c0c1c07140c010001442031442203840440c8481c1040320000b01c050942c1d1180e1020400c2404050030008105824882c00d40050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 39369887 1250 39368637 39368647
    0x21c0c03091e030206040b0904050a02130303120e0304240305010e01051314070302032403030307030515030d0503010501030e0c060a0c1514040b010b03070e1009030b1e0906010803 79
    0xc800c0b254440400d541c00a00c10020a45070741c0000d201da80503504c05511500042040e20843ca050700c180c2d5001005540b00f1440d103a84100d2543c0c51503141d100c041c0602203040c22003606161f040d00013421384146101502e9895032204000b440e91141512000305600c00f5003d030a811038024840c4505036100110300c2d00d42d90313181008110149a00010a03c01031344c807112841ca016020050b81401070310f05480c0562030b844c010924100440c0307081c3c480d003103582040024409a031400700440360031804600d0042120794802c202021550000014181c0610507551804502540030b03014606844090b641881480c0040f40520303074034004c8180541d40004104140004a401084d442904d14404c0c2c0c520b07002c48803451011811141d039a8014904d07603442c0c00c00c200400c8500a60386025214082081d420340c00d08500080803443d01112050203822500c0c08089694051304a0340021075008120804a10305500e0750107900103c41c0702d00348454a80b03030100b81c0001020420b00d0603a401400103509203 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 39371137 1250 39369887 39369899
    0x509150108011d0c0117060f04060305150606040308040603050a02070813090b010908150702281a1e0a02091e03010e0a05120a0302040b0c01020a0e01031a0d05030415021c0c0309 78
    0x10942c042d0006602021072550445230b0f456a000f00c0000f10f02070009414000d1078203800e4800044010040f03440752004001c180006030365a020344c0c080c0e07103851500041039914140504c0c020f118841c07019003100c00100395181040341d202420382c20f645a6210500c40702c603a1000650311a0840d0140c64015041070f010b8100440090726040e134000128411604090424203450501d8070a161950b202c0d0101c3d105203100748140100708203075070b2a07080f00d03c201e1071404441101c40030b07100c482100210141d01020421808554050380c3d0001c0d402455223405501d03d1407081019040000243d00a500701032147e20420300100d140b9401c9a08a000380098004080b0b60044a50100c80881f0502d5400d00002c40c20b600b0301c1c0050010034002d5000180e0350a80c4c40d0014210100400846042608000c2c0d41c2e205104201004402e21000351124441c00004d4540709065015940040328502c00d00d5003095886540000c880800c8044000c62540c10161640c080301d14002c000800780103c1c0c640c0000b040301c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 39372387 1250 39371137 39371177
    0x8060f011101020708120106020f0304030c09150e0901060504050603120307201207020102010e011b031503050322080f0c06030612070e0108070b09130509150108011d0c01 75
    0x200501c0d00001458050b1942d60a6041d410460300c15540800e2800107001081c0c04201c20041081400000d50a00e8915a200522150240943c460040c3c513690225034680c030030b55569010340003080c00b0744250f00d401d034841802042c191003400d11460415002c203241d42008190540460321000c1d0652440da902071007511000d00d04d80008090254541100c1481d42c0c040c0840030780f01c10980a980d0b030b41c48040c0002425900340204021159150481c00c1d141102c2d10784e000358685101e81004104003840784142481240c007a8405070150100040070100311449201582c103000c0e060789500900d607210344440380c7d10014100008c0141c0e10000540a00b40b512070084c5071300a00081c102c05c0082c4000c2c581e00c1c00e0103a075a000c00304298603c001408100001d2111b000136140200c0c0130341c10f011940c00018021600340c0c2140c51269039800c00314072500d0003485a112141c050400301119941c0d03c52650307009011280020000080b00841d420071214082081004841b0594440c8003180b8900706040d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 39373637 1250 39372387 39372407
    0x3030702010f14160b0601110c100c060f06170703110108060a05100e130e060f041a0403020309010207090c0e130204080a03090306060503151504020405060408010c0f08060f01 77
    0x20a00c10300c105a155814100c000501325020250b03801c100c800d03068075000c40720890207040c1d9414070000c070200807000c83c0000b8540b02d6840f0304844080014a81b0300f403c3e20a40d2805001910407401c0241c1c1c0a000c2d511900107070211032024488030704810b0344800f159149c82c2d4901000340b10f0260840745003410740c82900e441d90001c40003014035202c5541c50380095410f0590035a0310012800c0c0c0241d1600601c2c200c0900c026020140f14180a0f004080991640f1150005c1c084907204080401140501011910340d04464240c0c5040800c58142424007039902d0b084024461700605c104c0c1d901280c3c8001030b000d1000d1030040c68035902c0d103688003c0d04101582441c2884851184d41c203000009040e5020031040140714002d45409800d141141003903420303500a5080a4080e5202c02c04602c6103018090403d9400045065100c0340158804000340203441103600050b4071403000701d800f150b4000198844103c0d5481c40d1906605014145010742d804841143d03410380c800c59011003501d031540a103034005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 39374887 1250 39373637 39373667
    0x209070f0f050c0106050d1208090d0906031e05040803040b160507030507110a09020705010f020705250302090a0e060601080c0901030e01060506030406060503060912030105010f0210050f060f01030b0303070201 92
    0x100705103454030041041f00b0300b0004140c0700401098441540c0a82016050707421400c4103015205051800b40c01900d600514030801040544e58104006960f1144440d1840350407080340600181c10181003a04a540050b00c003075880c4d0340d00c1030108040c9201c013019640c1e01c01441d140e450030900141c40c140c03460b422082041c0e402081c9400c0b00016a40c031420848060100c4504c0180c561350f040c2003d0342100c6108a20f070b81024410000070003c00c000007081c54510380c06203403134680a8a2062039074030304000b40c1e000035000409001480504c8045420104070080003400311480c03641d8110044a9081007500c101600e00802c0200c2e01c425480794100c61290001c0200100e03015036070744e011802551045506941d400c0c0d071410244803525040c0045da4100002200070714403d014086944a80d100c10710890341484200d03111034190b540280094000401300f070008014a00d404501203014910840d1910b108000d208002d1581e58005c1c440c012812401030001d50420209070f00540701e42c80a05a04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 39376137 1250 39374887 39374891
    0x30c061611120a11070302091f0801020406050a030506040504021f050f0d090506010b0301030c0b09010912050f16180213150c060b040504080a1409040609090209070f0f050c01 77
    0x40511440100811040c103032041540ba656548501c8000741100300801c44140142c100c4401040942e403404801074000b4408014005e0b10340420303200603c41c1c00540d02c00314155002081c001600e94000c0080c02101c03007191000d004075903402040204442c4210b6000750b11400aa80038401501d08550b0b0f02211212418090b252807000f444845040d0070100d0f49040041d28cc0310b1017802c110007804280d00408a000e9003034110350456072440c481d0724403400356000e00d010109403101c0741e070711900102c0000c19914800150385038640c18201e496218010b803c03406407044403d560360085411804000300c4404d40300003c81c22501c004450080e50009528141c0d4200c6140301007400c003040040c441100c01c40d41c80e180b10010451500c1350030b80e0100c00c4c44601c66840c0c201000003081522084841d40c036240d180a04140c01f40903a2034081c3c2c002e6203095600a441e000307000c5a014565840030000c1402224009139940c1c81c02c0b400c5030f01c60b000b07a0b0140001688003180501c0a4001d10140400074004800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 39377387 1250 39376137 39376157
    0x2010503190e07030506010312090b0714070b0d0b040b01050906090402031510080a0507030b010504030209041b1e050301020903032205130c1e08070f03090501020a0801031202030c0616 81
    0x241032403c0f44540042c2e03042d0704010010010800700303c100c415110054200504414900b842e200d802c2e000d0035102034100c40383d03c0084543c0c180b082c080071000d4408841103a442d00c1c50034000384c0040050102e168096440c1c0400e01401e58041d038107444007540020071581c07034000c00c02c0078003010f500080c02011030340b100002461455a280301c0c1c2c1c00244140355860f006d4502d800f443c100c0035914003400e4142454502040c0c594141d910000b11001c0d6034040d00d44e0882c03600c6520700341c0440c00342c2250100c40c00008080c045500c601a00d441108250b468103014000368942c8101342c200d10550304082c0c1d0551003040f4042011040e614801442407101b4440c1c0d005940e0f4901180178288030012598100f5039511007504410381120544031030140c00c202d22080008580c80190100c2c03070103070200d81400400c3c100c1d080b0300c6201e078205450f40740e40000255103e4116110107003081c803082c0002c0b503100310203108200c10340344004244d0b00c0358030310f03040280303140d443d01c2915204401e51107000d05c00300821301403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 39378637 1250 39377387 39377411
    0x30d0903022406040906020c0d0e090703090f080708120403020f070803031012050f01050a02030406061401120b04020d02120604050601110607050307110105070801150309080d020f040e0a0603020103050a02070201050319 96
    0x801009c15000546420b81a0401902080741214004103a00149803a00204030085117520840180440d803003140607903518124105000c141c09603085889045480104000416038045100d001707007600c00c0121402280c451061589030b00007269002c040c4546001d04001144071b4401d0240d61500035420f4403100c40d03000740d040d0f003942d2045400214140d0000284400c0181030f1088100918a80740c0c00a07a41c4503103070000b030281c0b040030001008203403038802210103541d89504035109079015010441d51401c0805039041c81c000b0403166144254903207400a4590f50140340c0b0fa1100d001814040c2815640b80c0768180c541e90005080c1c04100194001961201c90003441241d000e0300103902d0b0101c041d0300d46810f0300c90811181d4010130030181484d80440c005a0350070195600008031354409130710780c260302500c80c006004a07401070300d41c2e0a5280a200b9902242d90025042d00e0007aa0140003640d6100300c104141c0c828414028002801000010305134036400c441d44074242c2d00610040703402200d0b11 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 39379887 1250 39378637 39378643
    0x1060612020f1e031e06030a032f07030c06030509030f070c0512030c100213060e120d08070206010522051003080a02030c0c041407120e030d0903022406040906020c 72
    0x714080744100400014005070151250101d80c041e80c1c05005d031501c0d407805e8004252121401c074402018408920251141c1c20300102a02e942448038a60101c154040c2042c040d90300c0c1c00c0d52005985440500c440030410911078001d0600c51070014004518010410ba80030000340d11490381a07c4000203040c02098545e50000c1c2090b42410311401584c442a56203003050500c007000c0c9150b070078584100550705201c40e00c4a180740c101c4403d4103282d4450b000c500041404216480300b01400c40c025140410030306a04000014028040d65017101c84581e200c00034003078810746004510003080b081002c01268080c450704455402424601507043d1596240e8070925140c1110000f500940c00200d035044d502c842c00c000c114282c01e01141d003800b5034040544019110f00300030b0071600400004001c0cbd0284002c503500404808045002103980c0c5075600d200c0d0b980208200320381100140038180030003080c042c080541003000d008a071001c0c00540c5030070301040010504410102c0c0c45a80a003d00c1008507028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 39381137 1250 39379887 39379927
    0x40203010f080c10081f0e0f0108070608040510020a02030c0106060801090f06050904020402071403040f05091e010e060d021f0801080d14090a0e07020f0f01060612020f 74
    0xc411800e000e98181500181460059040c1601910303c2407003044d89158000303a415041801460310602c03400114846040300d2140303030400f90089200d84103101035260300280c0e040c103e80501c02580c4405481c1d0001b1603000b001550003801d1039014103200c52500d81aa40108000c1d143d03801240c2c680203c00710102c0c02d42d00c041e800000031800c00c0c4010000ca0046001d400c8190705d803400c3c2001440d080800181ca4070001a0003e401554003042c140c00b00903242c0544a04c480d5107108a07502c51790340c2c011419040d082405039500806035403000c039076407078080507180d044030924146280c103e82c204820380158040080c5603550000d0300400007800740e120061b0200f0903850b9801c0c0c04200341303441d64000e400b1240c107a002601c0c0d41c0c406c540c64003615600c100440720810f03e607448141e0b268a040700080307140d085900b102051b114500140003030305030000744203400c60400006135400ca8680c100c0e000d08a48540c481c80000c00d0703500c0b507150a10034440d4020711420114207121800c1520055901e13242c1c00d07030303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 39382387 1250 39381137 39381149
    0x3120306030501060602010b0303070f02061e040f0509040510090203070504090c0e070f0813020d0c180f0203070f18081507020f0303040327210b100b12100504020301 73
    0x40c038901030060000a0040c0701c007a00c014002403160000800110b50f1301d129a01c1d01500c2e40a01002040440d612101100c450551002c001c0c0408905505d00c50082e502070300c909584c400d0349403000513807410440460741c41150000d02a14200480110410103410600800ca030b041c00b90304008122070796070b449007030f0400380507030443d0007442d00703081c0b501480110203020780b8280641204105509948800820750100e003001042e48030b07001500c0454030044e2100c000900f007600c0b424001c80d1840d402c1891301e000020024091100d60484000e2104030b102c1642c030b10303000454240312828a00e0007075000f24125120880e0805800b03a4812041e82400030f0800d032840c0c2d80c42e07880140700903503504100c1c2071a2624010059403031824195000780401c00b81e890242720300f8152031662024031440840303100080c041c80c4d13088003030784e1408603000440360034124088a0746801e103004101a00112406901500d001e490580d2420103c0c20041d0b9000400a0040e4a00a012030b00410b25844070b0020354001c3c26 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 39383637 1250 39382387 39382391
    0x3030f04170304080718110f0306130e06070f0c020310050414010c0e040902061b1e0105010305061b0403140703060f0209030703061a0301090809100503010b030c0d06031203 76
    0x4140109585801c480078410280c0c0d601c00d100078007a8580c046102c03021903450b6503007200c1016000f6403d0001d002c0102c1030b50400b4902250315000d1461040080d842407804548043c1e00102340241d900459000b000c5009441c1d018100280015009095800c40901ca80c04c14071840340e0741e50700080c9000a01c0142123251611801400108041ea00c0ea10700e07040c010200038400f190b10401c0041601c0c10007100035100340e0b1202c00d0b910954a4031012900b51500130007000c0d1344520481c55190703a503a0510150441305240c901000c075400e506210b45c0c2d040e80d038031501030001520b80e426114100501c0b036840c1429684e08120010000c1c0341016100d81e240a42c5001d0305d03841d072131400d000b4102c482c80350240244030300405c4a81441c1d60045640340075030b980010300050442080c900306c0c444030344c59601280c2540ca00742c1d144003402400406000810821617062441c1041c3c0d00044502d40020310452440381402d1010803620408180980390425100b0800104240c0d20344078010403040100540700420f17 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 39384887 1250 39383637 39383639
    0x109050415150815010305060a0e07020f07050a06050f0d18030e0315090d080a020d020406030207120504030503120603150103030806011808030702120f03030106110c0f0d060203100503030f04 84
    0x3428821124420b0803d05014425142004556018503450910035042540d180c001401c4d40d81c070412010702416102440032102e19045002075907030f054208800b00580309030280003445140141c0c40c0810340c1c00030343e2060304010118460204640055862016a40d01c0d021480c02c2e00c0500810048400e0082d41e694100c0c14200080c9403c041035000c0c84e29000e5079683c00c0109a0f400000c0312001280c01d0728242d541d590b10020080e0007806460000c082207800083c0014402d030380350f00600042802480d0302d80d00c0f011184000d0707596205501c00140641c00a01c5814001a000c10305554801d40c09000e45820018403407040c5030360ba00982084022a10000a00c0243d581c8400c00c906c2100ca11081da555450034104420396078056100000d10442d414013510021040a0201c0018030030340a04480d160f503190180503000843c1c400c0c1144851281011b03003159032803c4084908403030b81c0030b040b80006030b60546480000c1d50004081e1030850029600016482e00e0030001040c103910903002090f151 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 39386137 1250 39384887 39384899
    0xc010204080d0c0b1b12040203120d060602060c0a0e0d031e03060e0901050601020c0f01020f0703031e0509090406020a050c100e070b030c0a050901020f0304090501140102011a09060109050415 84
    0x13000003415039154a8581d5203107140d1031544030110f80020644203c944100d42d19440001c2c078090000d00344800550012904c004c2182507500001c007550307021b4080d6111a074604000702c95a004006c2e00d84d001815000f800205800c181980c0c1c5881030103850580c0700b010203005c611343c06400c06c5030324070b00083d55904200701c41049103520542148545000340000d0800742d0000355a4800c0300a000d1060400e4045e540030350317008002c040c0030707003804206850442e9600d09024145070040c022203003000c0c00e81e14902d909903229a04607180300c200203000580c1600c3d2515080003e4000812400c00e0107020440404d4140d0104801c00b921640e070b80d400b044005910000506103000d40d0f01000d240314052050222106800c0f041e0303047c5a00034900261110000e00040740360007000d000303800040c00000303008035414503140c000d00e05840d0001c461100c00130801d4012422100d030718010103644181070100090618001d4040743c0c212074140b500220030340d1280002000c03112030001a00150410322820000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 39387387 1250 39386137 39386153
    0x1b07170c0a08030903060604050601030905060103060507020f07062304030b090a0507080f060c030408040b0f091c02010203071202010b1512010503070b031603060e04060203060108010b0c030f0c010204080d0c 91
    0x1070903544025505062001d0086a1b40741c2d0040d1409106170348070000610564400d40c4a4184c13950442c0031184556542c0c1040380051005031030302d000500503003040352580440082c040b001c4880503524050404d0a041003030b0f0346170442c503010300f600385802c0100101165003842c4060044d40740f1006448600581c1c9411441e14140381c0c03100c50b00380c1101c002003843c0003000c50050341c040c1d0052109a500d503550f01c0d203078172148100e410020b440b42011454540301d00740880a00340d09407094504d0342501c04007488819806010901c028010307481002650001840d001010305151301c2c40c00007141100006000031050f0105501d00303955040701107040d012070240c0c1401640144401e070b028280d51b0382080780071419884010040241c107402c040000b20030038400d81c0040020164450388030042c1c289494a0400781d481078402a000500a40021603c42c141c1402c40700e680705880300451600030345c100b10704c800e41c012100c446802d540c00e1000042001e82030007449919005640e035805000458900450 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 39388494 1107 39387387 39387389
    0x904020307080f030301090e06060a060513051f03110901080c0c03040f0609080c09010b0d091e050f060f040c03060b0d0212010501060f141b07170c0a 66
    0x250f220b50200c059810f075442d028062000304074492a02ea6140f409a5409522407506002002054010001440a507503060304050803c3c0d510b00c0021030205800381810841c180ca0141c5528207549032140c00e1100103510745490a00281c000000e021020003460f1658141c00012280c800703c01c01c0082e00c00402692003030031411521810f0007000743c3c8161007007504c3d5200d1082520741c18074182040b85d0503680042206400e01d07118042200281508000998580c59400d0200492990b0000c0d8900c40b540524003e114400b0094080703841c010300240042c0180a00d40248000140221456022a81c0001d804140c40d040d140005a080112401c000e50120300d040b0341e441c03001410b40110f030480e03201ba1200c00440c1503000c02035800307107206000760200036010444240c05028201e604854140c50b102212411500d515050725244400c904104090340600c095140621302480700d10 = true := by decide +kernel

theorem cover : BRFrame.Cov 39208637 39388494 := by
  have h0 := BRFrame.cov_init 39208637
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 39208637 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 39208637 ≤ n) (h2 : n < 39388494) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
