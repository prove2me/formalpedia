-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0239
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:40:08.788758+00:00
-- url     : https://prove2.me/submissions/4acdd31a-19f7-4f5b-b022-5e74f70f3baf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 42805759 ≤ n < 42985616 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 42807009 1250 42805759 42805771
    0x902030c0d061706040b0a0b0a030c060315031e020409150903020f01020f04090b0607020409060c09050303070507030f0804030501150518060109090c030e030315040605031c0804030e03030a0306030b 87
    0x40e55103c10320062650b207500181004103420f0085000448041e8a9400100d003080002c0921502642d6420010884003d030701139000024100703440030310a403039400014000c07aa03000d080601c40300708100355408601c00d0244100e07480364a8102ea40b0105101000c02420711144010014126070707180b80181c904006810b41c440c41d0790051049441142e00e0b43c082d0381c101c420f146001305440c071002001070141e104010b0000d42c814074043e1038000340f114a070701640d003600c01c80d01e400f0113481c3c4400400d540ca02804c80d00400c141d200c15402d2000504407002c0011162090389010305180d240d6552070309540001c1c0d500c01c8944812101008a840c020506034082d4401c0c400c2e20243d0305100000a04100312070140f01d0301d591300d40301c01d03240c2c01c2d2181d8481c2d45900082d50990f600ea080403400304190010301c0c00054403da04011002c61b0628021840102c00c00c2110000328203040d043d00d095500300c01c0104140c05114589034003c2d61520180020f00c41e0a0003a680003441c0b5040d40f40030041c1b201d0207400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 42808259 1250 42807009 42807029
    0x4050109061805100912030807080105010201090203030403150b060a020105060301050c0901020d0806061e1308010b010203030718120b04260904020706110a09060e0103020703080115090902030c0d06 87
    0x1c20030859a0194150702910f000740c401d62440c801042040c0c90925059011243d41080f6101500078154442d00701801940c0c02d030742d91107140c1d030384100480c01e8440d06540654150010003042000803000c1400c40e400e40250540400d40c90042d0000a00c0c5400c07051310075016035141c3e41008441c0c9003c4c0f1502e82d00035a103902e00380c28040500c000070750303079400204010144079007000444c501da6545030950b5010303000c0c034014040071862440700070440d4210f0b03101c0119080c40355501154100c018010424114410f030300940c1540d0f6059011641c080000c1024075a4036501c1d04046005a070700c69105641da8041c00e03d140d010b0a250fe007029a034a00015031200803443d00d8081d0f4204043c1000b11110304c10115030142c1c45000c142002c0700104501c0ea0442c101c018002403160580c0e80103c050070031a0071940390140c800d01c0324401075041c1e00c40c01e4030040c009400c0400602c801c00140301910743d07031226864500e540c541c44580c0c51382240c0c41aa019181e40c540401c0925500c603003401090050a44110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 42809509 1250 42808259 42808277
    0xa0302010507140706360b060d03020c1504080102070305090909070305100b01120c090302011403070e01030915290d08070305030603160b03010314010b01090306020c0a0206030c0405010906 83
    0x32006903d80a90307480201070503200d082c0e140c400365206d094001c400d03802a2808000c2c0e16411022100c135268030500f15400c80d141c00019941e49001c07040c4c5c040b80c0d501600a844540d001070304109058103683d04030324520005100108080400348003a0841501ca626460f41d2000712008000c6410001008400140c6c0301740c0007800094008101394805a0b401d800c0880e0044403800185d0340807103580c4007400f030180303041c5219905503400b1440c401224002c0e241c1401c15911030b070759440c66220486500010821241650310035510a601c2441d0743c42c021000321007401d82c1c482c071000659111189010a40a0350084100d22850900d034242002c907085604006100241e82e4a00c0d89009403a0041c060007004000a00b05440030f100710040c0c0200015100905a110090705509400c02c3c00242c880040e8500b1000900030b051041e041020016140c2084507483c5590b01c00207584a43c01c0811303d40a4039002030010b031601c1c0302443c015003120540c0c40d111420b01000400c603210a40c088410010440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 42810759 1250 42809509 42809537
    0x15090f020703020d120605030f1c080103110904060609021216050c060402060d06032910030201050715020c01020703120506030a02090a050c1204080702030d080610030509011d0a0302010507 83
    0xc1c0780b03a540d10709170420902c0c881040d10410000e10060f0301240d0180a480524001c2e08404501c5299001034510b0703c00380014241c07400c840c0d1a400340402040110f14500242161411003d4070303600c03034801c6101052480c0c45881c0b0700c05a0f0410314401156520b20001d00160300c0000b800ba4400c40b845191990424007200d081c03907990b020252019029a800081c6c0402800c0250480800b0b5038008003402a1264682908128240d0110b076450100410702c010070004024008100c048a0b0142d654034141240c42d00c1e802401c1254080f000e0314181e08000600b02c2c800280050010b4900a80340d0142200c0405800d005a0320010b24242c4030341c10541804005984040030359400001c48400000c140d516400f01c035032607214003912170701628524010032081000040003840417503c281c0c1070b0381644040c0f070001c1c2c0f02e101081c1e80155101d2040e01c0e17072064244c8a50301865002c100c0310001b080b0319460130740b100d8840e1096016040d0a80100d4000418550240100c1d6003111141c50110340d454052 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 42812009 1250 42810759 42810763
    0x110405070e1c02060a0819060614030a0603060501060c150507051b0307240b0f01023a030e0f0309060a0503041b080105060a060507020303181315090f02070302 70
    0x10100c5140719841620b0700c1541a00d51503007040c0d1003503020304826070711166010013900010085800c20315074801000e0010203540c0a0040c0b0085803c2600c039103681182c00514140ea540008111b5440e00d035840200101240716802224002c01035a110179801c00980d042150b040203041076400611030809050281c01940141100c0702c0e4100c00361a940c40785400c004190942c400c001c405000000307421031102c0c1d8003209042c1903a00540c0c0100c10440d4100302000d11802d10b405d103103443e0260b0403510002c1035485140c162041c90034802245295027080c503ea040d1203081074400d1050000e50307101c000c045a68000c000c60002c40803440000c6040005d002e0024129101d0440d18000300726020000c5410004864050b04182030b407110004880340c2c603072001c0e0b030082c4012950386210302800700c0300003056405a4201e07203100d074020f0003030740c5003034600b568040003951041c2c0b0b4150440c0c032000a02002003498407490b0600301800103055045894145c2410544244140205415104011442c002600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 42813259 1250 42812009 42812027
    0x706050a0605040b090f07050a090308040e3301120204050306010e0a18080904090305091002010c021605211504080a031b171005030114060a09050103080717210411040507 75
    0xc0b91038100d0340e4459100041b2b4203810103a100901503103002c900400c100c00070000c51442501d1003d03518882c0690000e000701c984820015400c3d1411038606800b880d0b5110300c5036208501e1340d05c0400751801d0b58902c00f003458103a09074082c003040c2ca43e14040c0041c2c084507000383c0c41050021255400703204001e4440c1d01442c801c80141c54441d6941e080d02c9000c01d0300a038256420b4913001010042c8a042c102e001034064220700920f5030050040000542611600303213807040c1603c030003500c01d04c1d202041d40514505181ca41910a801d442841409500d80703800c4511944118410f0100541790140d90901800b070b107500000340301d1500300c84400d8421050384564403a00d80c018103d04042c03191201c012100c0643d6a0b50042030f0907500b450f400030140d11201c01c10900443c000c1e1400382c04240e990038180c2c00c80e0428040280ba0075001c2015002107100c112244a003000145143da1038030610301034403240c24030204115188903104004010502500c00200c500d41001900e06002c58540080c0091815034 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 42814509 1250 42813259 42813271
    0x403080a0b010318050309031509030a050d0b0d14010b03030313020103051b0f1206040b010c0f11091e060405040b01060c0809060c0105180a08030406050406020706050a0605040b090f 80
    0x9640c4410300070aa200f0b0300009100401441d51621105003801c00589903404024094040d1040300d4566549070600c0e24030350320900b140f102460400100c200202d42e43d40c040e82a00741c01d02d40f02c2044911503903400c0391140c1403500c141c907040101c075990b401080c20b483c90524103a00c20f810600c100301070912050242c640301542441d00041d5681d419a044200c12a8659222015100031a600c43c814140c1401440c1da036922807003944450b038440e410441607030100000d0354001421308680c107001a5840543d800414443c0080c440034040110106580c44000c0759810000070895180c2c2140c80c18100010390000c90070342d414821490f094035221050501031080c1420007400c0c0e00000184188030f41610010b800080000ea903c80e045640140030340029075801c0c140b06503419880814140010b0781981043c2d20001013802c5a071a030b11000002c0200800070307903501d502000702c80d00040e29446130742d22404c446000003600508090a01045810042c001801a04072005000041000d00b00e102c6d4005 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 42815759 1250 42814509 42814511
    0x1b1703030f0114060c01050c0307120b030d2105040309031103030a0e151e0405010207050102191101090302030a0b0103050111070c05090405010b060c01140a02040b0901080907050307091406090403080a 88
    0xd08100032a0040c410380600c4c20042d41b0b407e0502040821803c015400b449040d9a10320f0303d0f80746407242c84121b4030b945032159230640c0004c40c1c0c10f141c0d1b4041c00d16280c0400c80d040b0200d080c1260b0b1200d401c141c1d40100c1c0d044000070110113003401009800c03c450594064140c1c003c41c105903601c400a0b0128803040381c2c4a01c5204042c0030082c103681207408803451442041a403401c000b07004102030b04c01d030700140109030150207a000007190079440041c4481c421400a403601070032034116151000c80d0386085116034100124041c001c00941c408000c0e01070040c4c030a5030b5443c065032460801508507110aa1442014901000380b9408909540400130540301e04413204415500ca600c1c18500400c04440469000780b0042540088070707606521010b50403000d04034800d0740d0340d02c41148204a04c00c0f80140303d1154018070010409511032590a035024031510201c801150301e034000289824000e07400b8017400394445e41c425180003980710800340c000d1400e03903841c00a81020764000c1c0403141c000745032202039 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 42817009 1250 42815759 42815789
    0x6031b04060f09060302040b010816030504050c21010b060906070b06030a0209010b04060e0108060a060305150310020a091202010c0323040b0901030510030b010510030204031b1703030f01 82
    0x540e1564061001000b103604a8928030f95a640b91601a04545c0b000b80e214510b0010104e0107540903400702ca2194202d51078600001114500c16401008050820348481c82075000c50b10081d1100d50321020191b40a0307080e40d1000d0100c030601801e40302e001015501600e01880b040c84541c403000252002c0316805007180f81160340d6003010030720b00207010710b002c0e40c4020700000010300850404002d00903550542d0740c50740c4240c82c034001500c8040003910f18540117104c208007007101a100c0c0e80041c1d040800b00c000130b00e100981c46e002900c0c007000e0071031603d9903a034005640d900080d00605103000030407440030309580303460381d075000a4652052008042e09208004007030303640c1100f0001001c1010b088544000d621203490307841ea210980c02841c1400e01103860305010403c400440001042140e40c00303221001503038203280500581c10b2001443e4006d05801344400700001c1e5040c44070550b1040d031b0006040e07403e460100b6449070408000608481d41e0400c10910031800240c0c80340a0540e1941c0301c0745090 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 42818259 1250 42817009 42817063
    0x207030320100c0302090321071101030e0109050d0e03070506251202100501120b07031a092e0806070309020d060e06010e0105041104051002070305060709080709050603 74
    0x3450560400e90190918103c1502c480c6078059001e0030700600d055046900c80603080c1c17030104902541105c3d0382c050f28400d001c0c0c1d00001c1c00b8003c10548210041c0b402040ea0004909a203003911503102c005c413501d402096010200b0355003c00034035180a4114000c0401e1490040071451500c1402c0e070480009400d44424000054000540340150703078040c52011104200602c0292200c241c0b81e442c01c011401c0c50000a50041c00c01c58a010058000b01001c00b907072034440050707008024000d07205048840c1d0401201456071581d82035072042d0780e6a104140540a44050b603c0c481c01d003880c01d00110a00c0e1801448111000214564000b15504001803903100c1400051981c11000800034191410030720043c009260108005040342d402e04240d202d03d9807110108800c1d10b40d55011404040010f1108000302c3c0b500c4101d40c4681202401550742071600c90712001c0c02d1420440f55034000c034042c0743c41084000005c00c2014006c2801aa0407c6a4140440000d480e070800011541d60640003224401d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 42819509 1250 42818259 42818263
    0xb0a020703092619050d0f0e130e0c1203040e041106040803090a060201110f030a0906020f0c0c03010c090605070302011401080a02040b0a030b0106180b040b12070207030320 76
    0x240c00e40c0c0b091014034243c0d56410449403402c0585807181c034011001d101304602c1091401e19480ba0703014026094246400750125a8401c4003016041040a1522090b0040d1164601140e07909100c6401185131040c81259070324110b5400c4100f4011100c043c00c0654035100801640c007030f04c1c1107116801c1071761950300f0005400d0050880d06d039400b41000900043e5524000028a12044c040c0c6180200650311a0203900f00d0710040314000c81c051003000151000703000d030b90085520540c42c0c00000350b0340c28241c5400c3c2c00c0b43c0045058221500d8002401490460f04101040c020b00c0304070300074443c04036031110050885031544605014468040742100c205030003904402400310f4030103102d0b15150b035100889a5a007205920590180d482d000500c0b1480c00d14100c0b503010b880e0001d00350031040c0d05c0c019084510360007402c040800a00c240b0000f2a001b6002001000103220724032aa54440343d40c0e040c0c40700841c1002d4104025940022400c000183d00406440c0c0b6103140c0e0150b0040c20040a00c0c458 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 42820759 1250 42819509 42819527
    0x103032001020c06070305091e031b030f0c0a05100e070306020304030e1306050a050111070506090a080604030905090105030a03021e010e01090b0108010c0206071409041b030e0f03070b0a020703 85
    0x3c000c0e03005400411a0240d0705a2010f841410078804407000103285049072090120317482806e41241d0010001c04600d0340002d45a02c1e010b82491003140c0c44c0c424061800c400b50781140b005800c4a03000385451405000e001c0095042081400904005034542c10722342030340e0b4100d01d220041005030040005020715004440b0034803500341c060176400000790403450900050415010b56441901c2c42903002c02d1a510540003134a083c14024001c155031400e1504100c1a41c20100c00786601c0083d2440c080341d41d1000740b100c140aa4460b1311900201d609000030400051016084140603130f2020359014086680002e110350030140e00070b940308800221203941409090850a000c82c2582080c0c0c034102001172036800c3c5070407a20792500030003e89071450b0341281c480b6002e40e844000901c03900ca45c400c490134200024104100010000215803440200c2c1508c0405502081808203a568019813400c2e0024402c800020032602c1c05946400903130307552030070070000c01740406401da64042084020035006075441 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 42822009 1250 42820759 42820777
    0x4120204020d020304050106051c03200c03030403080c060a0e1b040b3001050f1b040f0b03040312021e030907090204240905010e040e0c101106060603010303200102 72
    0x665403485d20f03041c8030703000c5d113564881c80f40501540d10a0304030004504900c5100164503a0307a01050003183c464482d10034015550300b00b1680222480c1014071340d400c10052000710f101d14285611036041d459441d003030083c001c0031400503e0610f08104503e81c004070302c0510082c4060b103c04080440c00c40030034001c20800c081e80e034002d0001000fa0101e2403602d2480d07013400500d401c448944100c11039065081c0e4005890510302d1318107050215080c80d50021402885080e0030300d00c1070600340d651078901e04d00304041c0d105001c1e80703000200303100c00d140d40003007001504c05415074192301d00030b9090301151003007403d100ba010071440d000c00464007120040c0010380081440241c291345568503440514254450074441e02800064404541d4040b070140c02054101e0700161102015403000d84240005030600e24103031441e40c064030990300e10395900d01504818111107030340c0e5420030f0a44481e40c0d40c50014007070700640c49100e09100410001e903102c0600780d15010000300600e020032040c040175019008440320 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 42823259 1250 42822009 42822011
    0x106030f0b030d0507060f1a011b0204090c06080f0106090b0708130b09130902130e03130e070f030209090c221d010e04020d020616050604050a060b060c0304120204020d 74
    0x159500f81d030310001901110340030307004c01c0150a000d00429070403580841180d1040883c0e11007607200c0c96000c1d03804c0c2c1181d2484003c0a41c100119a400502240c0c00340a04541c0319903803450074050254080071855000320040d4044400d541489005440032085110300f40841d180019448204070343d80054810510b2800b4170a03280c1601c440800c0101c2d04002000c9004d0824041d8038541c141d45030040c0142c441c0c02034080d62108540d0f51303052001d4102510940b51034803041181c034200c4980881c8010060500000308011070400d4032004148640d42c40e0130604250050003014519921140101d80200c03800344000d945101d20359140c1c1d41c40070f10441d0499606000351000513210004c25055850003400440200540c0e02d49054140c0e512055030060b4008000e2400100141401c0d001000c83e19a120081348440c1000d684a500d4036800311811070300340e00b103011800201300c2c40f4003624440c400c00f00e45841c1040d4803c644107660b80070300e00c10030040030341041e5101e0a64039a0b9044030342460811038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 42824509 1250 42823259 42823273
    0x912020927150a110a050d0c090b0a09082a090402151318020a12050402041107031d010206060312070804181401080d09031407080f10060b0307080106030f0b03 70
    0x141a201002e000c9448106590400c40385041d01407071241120294000e5444582c103040c0e0511568004180342c0d0440340620003905408900c039442c0c031016007200000b584e40c013070035282862140c0e8100320341303201113081c1c00c41008480304508191076480808807105a0b0847c0c5990b03601c1c00000e0302403420300000d000008000914807240e0345040b032510140c444080310041520712000040b006c920824582c180040c80e1565149040c0005801c0a031b0040c0c0002c1c004513148110345480401ca6004100c200e0120f0324000320019a612001c1d074540800800740083d104e03c0c0b815002194840740940d4140b800c41d0800070f000c200f000281070070b070b401412104c440e0040c4801000104c0f001800c10340542d82410b0b00f807900000d164034000518280203402c0303940c1c411009242d60740d04044070081610130f44450013403c8020403200383c00c2000c44880d40300da5009203a4200045012012910789411184440230304000300a016600414614110b4800b8a0000340c075000030140383c1d00405c0003c1e0311540c54041c80e5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 42825759 1250 42824509 42824533
    0x50a0b03041a0906040c0608040b01090209010315080d0306080105040b070f12141905011a0d020d020a1808010207021809190b070318020d030302090102030d050103050106060912020927 81
    0x3070310510a610a01c054200c1b42e881e0030003070322348440c100c900500c590202c100602100c48180c01901500d44107045c085800650b601c1c2c00e450016542d044611103500c401c0e800311440f6418092a0010410480200a2070a1640f039040008200421040c10b10440c8110038184a10811140d594030610178020010040940c00c000c00d03041003a00c1040c88000c40c01240007400e209481b0f524120380400305040d1800c43d01c00e030700d88800e030403801200209550a000102110915000074620181c15948030f106c0c003940084c1103c1e032180c10350084203041e80705105540040e00c9107900b003400c0342c0f000741c01003c0c190783d15041249400000c11a0365582210b507042d400421460f410031501840b52134606103c004c0ca45054070540d41428070020b94080b0780021084003080c00b036030040c007a0000c184107603442c05602c0d80402d03042d514203900c01c0b68507a55881041010369800317900070010380004085491042229000680700400140a01c03601d040d03481c03c0c1888801400340000850341e152020748508030421 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 42827009 1250 42825759 42825763
    0x302030c1201030c0518070e0108060d0b0109050714071109180109030e01020c01020a030905090426090f090717060f1207030b090312041509080f09011701050a0b03041a09 75
    0x740c170946002d503045510010307200962540d0070b031091460ba907803041c0a0700c0d140c0c01103030901d50140000d03400440700303021900442c140e54101c0e4060041c455010625080400d001000085424060000040d05010200008900344034903510003000711884801c5403204404545660201255080c2961034140c11100f003542085180a1041c4240c0039a84031020b041e00581c2c945000c0c020090005007015014000f030f181802c1c032150854054010074041e20f16000e00038880c4160500e04008440d00803030aa0032134500601000c081c20010b85d041c2c8601e080550014040e0604034083d0a080ca400600181d0540c40e24680200c43c83c40c0204000e0f010407a8035109a11040d40d4041a54004071010009459280001c112140c80030715030404040356172151a00072084281c1c49a240e032003912601d094000c180940c0141540043c400102592451315000140c400b180c94489805c284421500411042d600d110381d0004075060364205a07907941d254602047c2655010b02e100604801e803105002501c440 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 42828259 1250 42827009 42827033
    0x50703260601030b0402030709170102120108070f080102040609121103011e0e030403050d0c060b030a0c06030e0105010807090911180711010504052e0c0302180d050a02010302030c120103 82
    0x801e032410030008213060f0501050748021101306001c2250360703004000c0c0518444980340d195280c403000500f02a1900e0381640d0051081e44078012036840304000780548112801c0f03107801400500001c6142500d011701c06040c0410501c9000580e481c032801c500c040c4030a0400014601000800030440b4413813404241c134003400c101c0040030044d40b0700040e28403055400000c40342540d406c0001807502115030042140c1580ca01d500896195072642c0c0280ba03503450400c0917001c6940f14196000415052a40040c00c07118880f0840c0d80581c1448010403050340003090100580301c1049010a6060060501d030030030281031614a9002604000002200800040498010880e80c2d86900a60131a44455800e84800340d80c05455600081882410440750510301017240701031144180303c0b490f1095095045a0081c0c108101003600010454003030b02d1b110070b4030700100c40d0440e03800c04206800d44a442e592908024001d042c90360000218480324800c0094445854030344802c80c1903980c43c0e140170941019 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 42829509 1250 42828259 42828271
    0x120703050108070e010e0c07020316060314071707120b030f01061e0f15030633090e010905060111030703050703090f030b070807050d0204060206100b041505070326 72
    0x111100411040c0d400c204044c102c43c6ca0b4000c407865502c1e42e0304086065400000226418801c1409283c00c84019544010003418203440014401034500ea04100e070100003007001d010010009141c0f018405001c1c9030710780000c460301d4110f01001c500e01d90b00d801000d00d40c0380c5a50610400d040700c00300704c205401c0341094030654000c0c113030321504840b10764081c142e25008502250701e070300c3e0040c42000a4800b1480000340305103808215203a075043d29000201d8000144040c090450411000f100050f0250007200e0690f803038501041e614040c10001041d1040c019040442d84940124025078800d8043c4680291082c040d207690b9502460040c220394003c441c2180800d4803810005801c0055000072021642c002650074241e54549a0480e1140c0008001300705100e424014612039103900d2000d40040d02c0b043d00240b881c0e0804c0c00460035480010b6005032400e680812082c000380d005134a00031600c1099082c8030341ca40c62245400d0b21409e101c0d07080c04111140b440d034484486110201407030700541c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 42830759 1250 42829509 42829513
    0xe0402090a0308042402030a0309020a050d03030e0606030c1c051e03031504020405060d0902030a080f040305010b090c070b0403020c030a06020405010f2a0c032001081305060c0d02120703050108 85
    0x40718014004664a4245d8000e202681007446810310003400307a00401c2c1030710310080400000917256000074060482e1032071b054000990301c1221034400b0b0002c202264100303004070003c0146042c8040000d40b0005403417001101d442c00302000804104081054107004030441c01c500d010b04014505032507880e0811100d0400388603080c44075000901301842102c040e120007500491400728403842c0c07407002e4200705070100d030103200790500c100c0451401d8015000c0049007540c520741c9c6c1c41c61420401e007954a0704910b140b0810030741c414040800100320444211590081d01000f240d40c032410f090b410300018203011600341c0512003024003008a00d0340108242c0720241c03034603e50319426240456070201512030712445a20510014440171945007454400720744101c0c40200010b0300c0e603480c11a818200080603c40e80300310140f8071107568001d801e05900c0140c1e441e0306038256042d84c44413562800d020300444004a000200b540f80d0035082d030102d8090203000e144580d014142041c00500a10707013403150341424 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 42832009 1250 42830759 42830789
    0x10314070608010b161103010f021806121302031005070816020d0801060e03070909050303010302040b090408090105071416030320030f0307051908060405150904030e0402090a030804 80
    0x240b4014410326042c2caa131021540d06005048212114500c0000800d40d0a00ca101601c00b4080e5003d020f1115441c01003140543c0790180e413141500b40c1c07803070060342c41d1090006001c03071050350015171f650035880000400440c0c0f01d000360b400440d04014420500c400003e040104124a0f41e411410150103003000000d121201204000c0c00c90300c4225035070002000808035401080120711990341101250401416034a1031a9503103905011503607001405c9503140c10100041040d49058400c10210020075280c00f8000d103460760f03848003c0d1007541c0e0740d6414070101042c144140712000000230710010300d080894a0340340c0c407010b0207500c07170110b48400c0340000c03140c240c8044480386c0d24800c00500c941c014010350400c10942070890060b00b000f003130081003105c140944043d50800700c0d4100b08942c20340d00c5941603410400103010644c2c5006100081070200341c162104c9940724404001c0e0f000703070189407043c3d500402c203001902070701c02d43d08401d50240003000d02000b03000340c4000030022603000c801d40c403207d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 42833259 1250 42832009 42832019
    0x9090606040608040219080a0b0108060702010612060509120309010509010f0209031b030307060c1e020304050603010b0a03090203010501170114100b0a090801050703020703170603030d090501090b01031407 90
    0x500c0c8200c2c001d00000403100404900141812110307210450540140d090301d1680340d07013070940b070b0070b10040094a044000400401901e80184200f58000c05144000c0c02041e08080c1180194116050b0040c01340b41d032000001c2180106018403a02030110109980c0e4a09055481a010340703026a801b01c065442d200302e040c00030401d4421070b0000c84000d40a42088405c0810134002811041100e03a018081006000c000800714031404800000ca80c60351100c0286000c12407814049403950342056500c100800c4c021641c0341d00a030390466211041d081da4552800b48224050700c8140c40003501341d82000004654500c80c20541030050441400800a103005c000d0606241d90059a000c0d03054189641c05000b10f80c098001842d241040303007400c1288556a040580c212003080340c0342c100003580400d481041560001103401208410199001c032428070b080042c1c0c60f480740c001041403e6640c1d142130010880c0c01c0d0084100240c00c101c402c0701540c1d40e414007400c1c43e41e055400342c210b4000c003071003ca4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 42834509 1250 42833259 42833269
    0xb07020a020906040207020609040c0503010f0602030901090306051510230304120309081b210307090e10170105010e1b03010608070c200102010e010605090a0b0a03021005090906 78
    0x1009034000300700c0e10b00d54542d02c05010080d400403106a030004001c00c1070608a441718001c401e6104900c0c0da0f496030300d42c5000b00e40210b040b0180c001d41f0442d04200402030003aa8441202000e40390049400a01c90f29544c1e028880041c0b03000c012608416800b40c0103070400c0c0c2081d50014650030050420000200d60444040b0510045034000e0260105a8007a50b4aa100354050000365118030b610038a0811922039404014140c0c1d4000c0216520950800803410495034250248034020004241907041c0480b014160540c6c0e030089141c4540444001510721928038003020062074083c030204d100707030050320941d40030340001d00a038140340c03141201003010f090035a090b105001021ba0f48180c21a402c000c2d040b0342015020300184100441c2e103110a001c01c860290242d46550310030825038021140c0000a030035903000542803040703a45007202c1008142c84900859600403a003e10001e440c5c01c2450004171071494682010350014001e4208011301500003009000781c05044808400d0b0b5a5003c040117 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 42835759 1250 42834509 42834523
    0x5010f1b091809020d0b0103020a0e0702060703090221010b0f030a030507120315060507030f020606031f11030708041a1303030209040b030105091b030f03040b03070207050a120b0702 80
    0x4001410410304202800b0704010202ca895401c640105500342e4a8002032046200140260b5030380094400402c210f10780701f51f0b0070000f006030030402c50980ca0040340103901c400006007031009060b1110003000031035492500da03150100d00c068000c10002107224016000340352080f1101e029000030848422907250001741c0c0e4142c60390603503030344d131504d811903071900f024556641e00c0805240c0c41e0400064040d01008841014010543ea49610b0306558100100404261090001550050424040646c4001c1290008045d04540034003240c90850b411900170980303544006900c0a010051148950340800c40a00aa014007000103040040140184d09210700340c0f02040c0e45102e40d00008002070098021300100c4500400001c0c0c1c40d124800402c0c2502d404a5045803c0d4205041c0c91042e00d030800400f81c1c05010075130050404c91100b900d02c0b80d0320701c030364000c10752b02c41e2005c070014203107034420002e40001e001c000e0f1040e5211036450b00e81c1d4080201c3e440c0212150340e5034000103802c2c1840043c1d65 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 42837009 1250 42835759 42835811
    0x1912030915020102121807210c060c0b07090302100f0210020d09050d020609150901331a0301030803040c17101d0c120a060501140f0307080604060b0103090f05010f 72
    0x70f807651070301c4d2910301c030b91041842c123641034840e417114203010108114581260080500c0e072200038031b0107442d10707102050443c000d145009218150f401840036869603000c0c14024071280c20041800960a282640f0300104030604252850001800d4496621a500141d1820b4460401c5030090b0b8510320040e03032259000c403a13161541d40702c00e1035142d144003101180c54104820000005040e00444030720070002900f6400d00c1072031800300076090307066500480a00010301481034101c1d0222010ba50b4450fa601c010f04c40a4420710b00031010034140710706107061800030000d0042444000900c1e03844145c90300743c0000f06041e01880c0c41c107242e000c2c001c190011402c2222407005050b000c01810100410f241c541000e200082c801c4c1443c000000d4a5072090030701901c0000ca00b40d04081b112400c20110680d041c1c009400780d0084c0d001000140400a0b036146c11645c894070100e140c0c50184012001049540805400d03404d50826070401c0c40010351100c0c4071305032502024481505034600c10007a840114800f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 42838259 1250 42837009 42837013
    0xa090b0c060f0615030411090108010b06030a110f0d0603110406380a030501031b12030c08091518030118031103130305070905010519120309150201021218 68
    0x80c0b42400310414440e40140001c1c40400c444c0c0c5038401612803a0811201121410244452908540f400320300443c01014204028031940c07180d03c02141d89400090003c1940d10307159074100040b06002c5058580cac1549000c50a42c580c600501803e010f400684000da4999038190074400080c21b0501800702903c0035400d100d0100b9410450000017842c042071450303044641020041d441070306010080c80503003000d583c040344075411810040c0501080084550440d012401e08204072405a503502e42080e406003883c0e100d0100c14107141c421449907002080d031042c041d2182d071b4221aa034001401800c011061051005000d1905242c200d43e9141803450740001c401015034002841618146a070b034102c0b60a403410451110401e0340340000036041100c00da005804148600c035864401c181c01000c00300e650304a60b40014544100c00905806410400701d001c1d003482c02854044c42d03010000380101d48071491000d5034460000e0003500005c0346022a654110082200705030301c084500e1080b000d03200 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 42839509 1250 42838259 42838261
    0x61204060b0627010e090a0b0f0d1101050703050405100c1a0c1e0705060c120f0105010903140a0516080c04020906090d050f0604030305041502070f060216060203010b0a090b0c06 78
    0x890f80c00b520a40f4224108402114044860340b24402d500e4046c5480c800c010511000b080200300e0100ca940314024022081d5841d2480031880740c1c2021100800282002d81c0c0d43e5003541811103103481079400480d000b440b0481940c0f071440d4401c3c492200240600303502806440070b5040c0207014101a02d154144810500040d004554284805000b14601e845050b1418005584039420100101c1d8010719682c03002c80c85000c1440d5200712294880381c445a0000c41c3c0d070400b4006408070009004c042e054003001c804800c2041420860700ca15075410400f11040c03c0810301d69001c481c040c40c0500d8060340202c504001e0709003018003d484d903640001340111f04181c1e800c0c090003c0c1c6003203408191000d20030071b4000405802c003441101d01842c002d59001ca050f140c582415641a2590300f400d110862040100001003040295403400d06503220ba0050b0f903444440500c0300d458034045801402280c400400081c12008840090040442d15210a19002c0c0c1d5085070108500a2411071f5a440e00860 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 42840759 1250 42839509 42839557
    0x506060603060109080105040b0108190b0403140d181b080a110a030f0501020a1b080304030309050304080322060311030c0702010207120302030c0708160b090a0302061204060b06 78
    0xc000386511500c1850081c40441c0e81da80510b003914419102690a2051400180030307114080c014041c410003038602d0b06000010a9440301004d0b400140003804202d42c044802010f80342c11800c6500c103492428040c4914200212820a10342e098403088558186841241d410040c4d06503050044410b00700c09005051456190b1009500441d003156510400c0300e903010000423450580b07c04668001e000058540542c2c4402900040d00001005600780341401e4844c00607031001c0c220380d8030652602d4007080c03e241605d48540746000e0b03604101002d000c003190442d294040035040007998001007070020502d80c4d40380d1302682110520b207810224100b0802c00245400da00d0001071070000c3c418412140302e19540c1d0000c84114038203900c1100160000202d26818803010000c08000d880518040c011038083c0c07001041e079584540c802c0d03402d141c4000c500e400c0c0c1039840242d03500c01590050302c8640e60b842c003001030142c1e1030700c116000c68005241c840f020040d421301005946c0d4600038491072940c0e502001e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 42842009 1250 42840759 42840769
    0x10c08010e27030c06191a1302070f050706020d0311090307170a0b070806040c030c02030901030b01030b090405030703020601060f0c0206030a0f091b0b09061801050c1f0507030207050606 82
    0x42d01041c481071004108800c4c1c0b4800c1041414030400d054412510b2001075082e012007a144003d040258810740c0f5122072030380d0303654800031780411008018016507502103464103203400c40540038003500601680a00082c06500458a02440b460355a030401c05104984443c0802e4001d96410540580c008001400310700030403030124440749480d030116141d401083e50780d00c0300140d08607580b0002640c0d08040c402d69040501444201c00702504003030041c0c5800a600a64034001c03420b000341019103800c81a007441c1d009a1116620400281040c0c4880c501410720303da80343d01851040700103105038000010710318852140e0250030520342e40c0b4a2040c20075502003010540015101c4a004c5030340d14a01c110350b070107038071600408500c1420484954031950b1895003002c40c0742d50103244103850802005c4040ea503007008a82d04410411580039101a41c00300484881c040c0000940d1240310341252084211500442c041c2180c0300c8140602c002d99034081c003103041e401503078001007199102d8804038042c1d10789 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 42843259 1250 42842009 42842071
    0x31803030115200105090109060b0f0102060a02030a020409050103060203070f1d190b2206030606140a030204080a050a060b0a060503041112030406090e06040b060d05090a0b09010c08010e 82
    0x746400b00030f1a224600090840d031055404a003540e568000a000b0005180903082c1425021603c40420304000300000c1c1d1540c00080c8185e1890ba40080051024009581560040c042c0c840d010491582c507440d25500940c026144040031410100b02540f5042c030425001c814103c0105000d0b0000c840f00041c4010580d40589128018031210800314407482801d020f48a0070000b1051341c80c01701c40b07044401c94412390325004001050708007001449642e80101c20340d00300006190301a0b9491120030310482c024019a00034101e00d00400715500d05220000907420a450f0285500700b0010501d08104020304841e41324690225405000080210710f1100c0258003400002e032681102005820701d050039648660801300c04a00101e00600001c13459054040e40000195010001c94030781c480019824003c5002000b00c3d1a26100011454030b024171007106c499070701080e6050281885171f40140607040744000c01c0b001030f011000000740d01d00c103030030b540e40510a0024400d200e42c2c1d002048d19040310b0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 42844509 1250 42843259 42843287
    0x30803060a03020d0b04020111010c0207060c0f02040903050301180203040308040201050309010621050c0f06070b1b1306021506090615041a0c121201060c0317070203031803030115 79
    0x4400704000002d6110120301d41c03102442100d1914180c84c203071001400400c10074513040d2017071380341c03040740002c660300000c000c0c09903886c9042000001080d0718040b4070100030110000d40250070407064404042d00600a14103941703d075811800800c0d500c1c00500c04900040303034003030b0000e0491408200554003d41c01907400640a60011610546036840e50b040706d0302c0c120190040002000e0480180003040c0043e10501c94200d460b41c1c2503002100011b481030141281c0580381c0100503000c10128122142c0203203c03244507000c500e86030441c0c03240d0111038050030300caa100540207044401d051500c003c9007451140b40c3c01003100d006174a4807070502030b0040091240c00a1800b08002c00301d0078101d40402da4590340d800ca14241c0e5540410b0400f9810415a1105440003940031300003440c00b880d0a00b004c40c1915401e140010b11181542000c84030419240b140d40181c40180007030050007540407009510460343e034601300d1030494a24021a80c1d030b1100740304201c0c041d00c4540c148025184654074201b2810 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 42845759 1250 42844509 42844519
    0x30409150b09240702030a050610060201110901080702070e0c040302041b120c0912050610050111030406080c0d18061104080a0605070e27060d05060712020c0d02030714030306010903080306 83
    0x4c1d500d980070030324100e516081910103921a608100061080101c0d000103081184000d001200381402184114062049142d0501c08603d00041c00701340f08001e0b0800905c041040328017a070900820701202030340709001c2603020b2403c1021102488040c1c0e03110310081c0c103e50b42c1d5207041080e480d6507c00200f0095024000b00000b2400c0080c1c09481540b80d0300480b806040a081c0c142000221504290080d1744543d0501249503140000300c1004005d58040702e00a081520a590b150b0381c421301e007407041c1041c5507201480c01900b41a00d00c43c410040240d40d104034001c001e18020441102c3d00c07070061317124002a661229070b00100090407074008c60f81040c0b00b81400d01024100c40300280622844401c084d411500c1c00352500180329074242d280c1c1e04058265841c0160b20803139126581c4840300100798405104061030b480c00e4140581c2e04442c0060884019908070385a0504025100d60104800303884e15802c03200d411403810408422a8000c1034143c640080b41c510303503034801407250030041405a0103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 42847009 1250 42845759 42845767
    0x2030615011e1b03030509010c0201090b0712150306020c010507052508130e070e0105070b060108040507030804060509011412040201080a0605030604061407090311120f030409150b0924 81
    0x43e01e95041452054030980303010845241484665085078007a071810801c6a04068540d0f0209803d58807207904841d0350314004d80c07401d14103001900601421031561a40d00b200400000c203000c45231303000e03121060602000f03010507100c440049030b880c0140b00c1004070591500c550700f48c00d1203400f07000c1d42001e442001024207080341000c3c0307202c03103880e141c0c446005540a401001101640081c17003169401007403e1050500c4141e8a4880f050f42d402043c180c184100c400200b01405410012032004680c401d400598498a8440040c001d82054008901259040c100300086000c5042605c1c034600036410003400c59565500110f0b2880d001900300500b0641e42d00300030505440c14800680300b18090b2801141e01481d480c80541c15a070020655001c01108002c2400010459464588000003c407003108210442c80102e505140703416a403450507200001c0c0001389c0c428075800914801201c10480c40b54160395442420041c03103802d880a0344107100d1503c0703250440c03640d040c031407011a0101c13240e410 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 42848259 1250 42847009 42847037
    0x60711030109050d0801090c0e040902210c010306060203030903071e05010c0e010e010c0209150301020f07060b120f070b0f0409050703061e030b0406090303141302030615011e 77
    0x31a90b10b07000944181d0048041001c040b030b0070028090042c00b412a00300305e8070398007901c001d21000500840380c1c440c40d01ca00742c090956070f80030000047e2a0006110100c61700204850340d87e185800302d26103001c28200b03c40060028004405d49200e80005005140380c0000c41e034500c60b1003108400301004e295480c00f040008108244110b0b0119207050b11102c250200d00000036000700703c1401c005040000c0d400f181001615040b90990f0401e00c0601c3e040b806070b5008002a0282c01080c201e8244044080760034000d1121681110304950402ea0f400951000b06950194072441c1c2d50203201342651243c881040045101c0d00144104580d084055003480e446070214410f503141039420744002501c071071042c000f2060680c0240040c1043d055204003d6181d584e13280860240100090005c65a608020040c14001e8010080484600300200d10902d050b50a54403111080e980070380c0039116040c00208603000c07c200c601c001c02c0e8140c5403d100d0502c2104610318102900c500d100c20015041c0b0b81c561 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 42849509 1250 42848259 42848261
    0x509060f071b0f080613050c010e060409020c100506060c0607080705090901030809030105060102010e07060e060c0a0f030305070203032401090902031003110303130b0304080c070603050411010801140607110301 92
    0x8083c102540a40340080c1c03508040b24501039001d04004e0b4036908481503503001030400143c0001808007070034548000161000000c5160243da0f006590180c00001d400094140108a9011803542c0200070400781d100c0c202030103c14022501c403a54150f210001040c12140a08c401581c070813040e18000746050903103c0400c89001c5d082e030080701d18010104803039403645400e000d082d90000080c4020003512900c00c4000345d407184140704034000d00c042c0e181603040c40d4a13030a048030014040c01089034403212652916000c03142035000c050f00001d06d0940840d030344510200860340075041c2512400c12003050f442c1061396552807003007623605000804500040c101c0301400994403c2c0c5401c3c140882c958030b58100862444000f0318181e2180c3c0041003d1108062210102401c6c1ca0012020303503165036952801c4d000900c20310302c0940c44c51181e507900050480e8540c010500c40e920441c4008200c0f2504401500c1d20b09080c0a4003159a200000d20105801c2c20000f034800b0a02035440c102d503c0480c4030100e8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 42850759 1250 42849509 42849563
    0x5040c0b0705010b0310270201050a1404090c05030f0121030e030a210e090103081210090203090307020109050f0108010501030c0e04090c03020a06110a080a090b030a1401060509060f07 81
    0x849155150701c04542e00740c0407c0a00403800008a03c2011506840d500003051440f03100755040034402c3d80030120035800c40d4482601c01400d131404041113840402c070300240182c0c000312038880680c540d172000400c024100358040c0c101d004106034000654102554141c030511190b400180d01032091a0624010230140c0304080030b040c5050140c0ea0000c0d010500080c03016480202150090844034010000100d20004a500050581c11441043d4032a50a4403aa028441c0d008805050010003407050344940400185007042c803d0321041c404694403000d0100c110850b030051804506800300400c1154020b4020303440a5038113140100c1d034410f001c400141110406030054030441503a16043c01181091819040a0031306420042040c4c000c0850650f40c43d0300d04c8100501c031280102d50b85a619000c1c14002001c0d20880220030780f030b45050041680103000030180d02424184210000074201c1c0107200312010860701904e0386161040f07da548a0341030f481658101d8a00c1c40300f404500000403800890 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 42852009 1250 42850759 42850783
    0x9051914010302151206090402011b03030507020118030e01080411040914060601050c0a12021c030e010b04050702211b06040308010501030b010507032f010606110105040c0b0705010b03 81
    0x80d0352a54154010b00400001110900c1c0c01c004c01008040004083c1a181030b81c490001c03500505981e0390b5100417a010201c8003002d02420707038400002010540c15400c158480c40b119030080000a0812003000707041e10300c41c00081d01054812a2000341c6522a400e01c82e031090040750004103581d5010042800c85800e144240c40340c1046c8415080d0200d0140038280c1c101c0b0007442c2c81070514265500345501d032000303844000d00d5031540c070304050440b40c024441c8000c403802c00204442c1c084c000301d00203000741542c19040c0c0929442c00c0c00c0d550084ca80b6108180c041c0701c80da801040e410f244a40401c0f0300008102485042034002e0000c80c80081041e552130400c403030090060041c90400380b402904100c010b800c124181820070036840060703644002682c0000740c0500d8500407246e5404501d80001d00910181031074030040c2901e03a0210881500501d0441340382d0390b985140d06181e400c2460803210291001464200120810410010700c50007620546014000001d07100404c60700291a00c1419549 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 42853259 1250 42852009 42852041
    0x5031b0c0705090a02030103050d110c030102031305061006050901030c03020403020907020c131b0c0320030c07142103160f020a080d080a020d200c010510080304090519 74
    0x140001d05001c01c3d80d940007081101d0540c115411036442640f5649a280000c08102d141c42105051517020404030b000d0140140c021980c80c14400a814100c2c11600d9007603410340b045070041100c03034044150b40c1084815903500d181c01d0603031030740046011344450040003040603000d110100241e50340003081d070301410440e0020a80c401840703050124251000c08100405450400c49400c84044244210039508280c603055600c01614641074401440b40b1950541002c0c00000740d2050701800402401e600c0440d8040b921301c142e030355021090b0741ca20440c010381c12045885d00c4e1440320111900d040601405074040d2814503010800c60102e00e00314102c15182c01d2040f80300358007035080c030042400180c4440005410b1507981c1902c0a1b20070800038101200c3c01d42d00040500c0300c40c10a6105c203070301b810004004601c00121102d03210490308415505d49055107424089502130017030752101c0d411982c1c4400514209464008010b0060000500307045200070007642407901004030340300d200000598498 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 42854509 1250 42853259 42853273
    0xe06070b0906071b0c090f090f0302010905250b0306030111030c090a0e07020c0d0203010b03030d14010509010501090b030411060d09060e0c151605030f0d0506010c030c0305031b0c 79
    0x4002c04520303c58588022000c144101307500441d150303480140c20f8650078038000c140072030102290301c01450800d00140c0701d12094841c0408166042d000a00ca03280520304440c0604020001c010404d80802d10103048884408400c04c15166100041d5034804002070000035008000f628440c04d5500c00c4401740142d980008540d045407810103000d070003401151010300354030301e0f2258000e9a910690182c951189a84a035120f007150303000d4004100b078182c081c0c00e50740c8840c00c2003103420150601c0120070520170b480303000104107800c110300d83e00d040f140c0513555000c2461514030050426031020300181c50180085100c009607494040051000803401d050024240c0242d0801c00708480042c40d500f2a0b0b80c0004080d4280e0340d5410305160b0b00c00c4460b1142640d5072002c0e2050b01a2130008003001041c5000c04241840c0c000320441c042c1c02418080032060100e0364404004448000c5110300003000724500c8200c1c2e00205c1d210f00090350b404210341c900084607004229400b003042d04401e0780c08941d43d100366 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 42855759 1250 42854509 42854521
    0x206070c0608010e01030c06082823060907080903090301061206050a15090f0e07030308010e010e090a0803070c05150108010c0507050c09040f0c08030301050906120c010e06070b0906 80
    0x18568014900102410a05e50460341c80701c0048460344605010040100d02003681c4400ca42d000320101c424408010101c4c850200150000d4050a402007511950503008080700009400702d0622528009140a00944c0c802c0070541e040ea1028114110500c03043c40380c00401d8409110703450180c03804c40b40620a24207180340c190180d07880107050021031410914104e20b80c49460118000782c40741600c000c5280400648884002c1c1446038021150740302c0d0700f10000602d030b04038000a069640504500d0880d03a02c9840c880c40004080d580c2d92505e40c41190080003060550014541019541c070b0304107150105625420b00c0c00c4aa41c03040500e04030385030010004000248074000c1c225050b8240706007002d603162542522500c49154403805921060300040801150842d50302480e54800541441141c40e600419a43d80090041c24001c0c541040840d480c0d00e010030589141000350f600821110452000459881844691054014000344117100004072030b40c0d00c4502c9149ca0100a20f4039141030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 42857009 1250 42855759 42855767
    0x1b080c0307020909030c0a080306040e01060f030215040608071206030605160801050d1a0a0e1204050301140c0304020427030203130b03070504090209011803050a02030c06130e040206070206070c06 86
    0x5401300c009903008100c0c400c607107580450302d400002e030040a81912680c03030f07002240162400c1014402c06500c1e00c04081078180300102c603034054038001c0d107609022541000400d00e152046004107400301e0465000507494500c0340c1008050202011008142c050340c2e0354841040d68400d642d00c0200841c9007420f0f01c03d4580c052080d40c0102402c903001c40621005441351030032000040c020914044c03030040007601c015042e4100800d040300d10812074490140412088520760003500425210754245001d01191150640702075014403071503801146952a80d03801c010041052a4044e003499009501c01604000080c00c0c2c03c00b103034001e401941e910320004190100b6101e11fa041011760340d41c01d005006280750301000351002c1c5c0f18210b8005139107240c5940181d404645820000750f4104c201c20b0040100000840c5004200d80f0a40c103c80600e0091400c110060180321560103001505240810001413142324454100740041c01982c5007005503000300b022035015050039140082d2201c4104034140d44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 42858259 1250 42857009 42857011
    0x1f030602092b0b06060c0d020d0807030605100e030f010c0309021813080a021207060c0201050f01050f0d0201090302090108011b0305041e021f0e0f01030603121b080c03070209 77
    0x1102c5090081d840d20603041c5400804140000e00025607010020742c040d2110f40072203051001c1c0000b22401c2c0110200001d54611000d001c8900244409010a901070300078000c3c0c8040d0381c0c004001c0c2d003000010503803c54101c100d551010360f05200301794008a2440d400e228400d003914440d07802107040c00c098014055441c0d0101d5580d000b26525804010075001c5500e0703482c036202d600c00c104c550364000307060f402c91500260540d940b844150019480c010051554801c4000c1e00050300280700d250390703114005048003030900c01c4e1900580d0644101c12280380001e402c400c5144141000300c007030f5407680c000c100031180907085000640e56801c40070f8420301d5100803100d20550305150901580c501641e443e04040785070256812007101a04d007040442d5220070295280c40d502d40d56011042c0751b003500c0100500916203040e0f0048d4a0a0400c81e100d51080c0111003d40350040e01315084030510660450307440b10030040ca00294143c040108000800003c000c052a1064100450715801140104824044 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 42859509 1250 42858259 42858289
    0xb01090501050a080307020901171c0e0406090b010909020c01020d020f070b0603030a0c061d0303070c020405090c0108150406050307080d021218090601020f012a0c030503010e1f03060209 82
    0x2c0280003442c016a940e1401758152a034403403001210b0025848ac440c030b001d120400d00c522000d0a00d4800e0600c681c40310724404c160004403410b00c4020340e10000305c411141590174450000f00100c1003440904001c1d0020943ca8040d0030006144c00c07980182042281c03c102e5a03041d004100061040612400700901034018400b140074500c1d0017813804010740380a0046100410301c90f11110f02d100404800490031880c1c1003142c003136075981d25001000030605024030104a10a5181074040b600c0080000703866006903030181c58400b00782d1200c2c281c5d01e2071040c0541201c1d41c40340c3c6400020620380c03402c1c01088000c01280004146142c6400c1c00a81040340000c4903038a81c0c501803194802101c40001c08080300d01080d41c002101d500c0307681c0101e04051400d03044008030340c00e01c02000c00c2151013108802088040c60031040115a2910341103800d40c41c00800900050000c0c0014860300b10300a203901c1c2c100c44116645240c0b8418031160808100165105444865012800448a05100b281864515 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 42860759 1250 42859509 42859513
    0x1050102030d0b21100c080105061c020f040b1e0406020a08071704080d0e040b0607060c0207050910060e04050402031509101a1908030313020105040306061502250614070b01090501050a08 82
    0x260412000c14500c1c006d0007044c034003490007540fa4a00301ca42f0b650407a11000e41050b8010365035600d0302d0031819194807070a00003d500414803442e030000c0342d0303180944043d911f031a40070301641210b81c0c40d000040e400c002c0040e81c1992618004510b90b00506004100500d118009041720700483d0742c0190404440420050040e401c00c82107020740d0790780008890008e07601040c006001c20340400200d1510280c0c8c0c0019421603d080d05120010348910488002c49415540381c0c60081014018081510000c6d01c00035019448140182600401c24442681c08800e0600729203000040b8040703076040d00d0f50a01d009104a40d90311840007141441540c2d8900402d03200c01000c0700600e130031151a0381340f200502c0c0c44c01015920250307000b160b02c9103046400454009c00184601d9803103081d43c81100400c020030303101520942c0707201101c40460311104120606c01e211b0b1041090b151030f40503100c8240341c600c59401030008105c11000509064a800d0181510f0240000d403907050105211442c08540c00002e0b2035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 42862009 1250 42860759 42860761
    0xf0607030b010507150f09110a05010513090203090a12080105010f0810060f120608060901150e04020103020304021804030e1002070e01140d020306041b0b0301050102030d0b21100c08 80
    0x2660441c1c222080541d00c0041c00016212185c800001041546200910541480c800e0814802c0d0031515044411084802801042c0da90f8015605071003054a1a12007140404040118454079806154007001c500d0942c1c6030206680e44181c1d032031b1620603200700071410400c010b010a590061030440c102c102e038103007995207041c2015665642409841f4400030040034000254416120305101041079540c410103111154807822159160001158580420340c60551140e00798080030483c0000c95010201400301074540d5001100a580014000e80c3c01c2603a0714004d080001421810620a030b00940c1d0b45034800710201c040090400070094100c1c00c56114034028040c609902500da41164902402402c0c204124804a926180400d40c041d6150007034008000c2401050032003260700040200c5d503003541c20b0b20740890042a000a00840e40140e20078000d980c41c0448544c0605420000200102201482091080d00154400b00010901c1d003210004030165103e900600d4248001c0c1d007001030607 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 42863259 1250 42862009 42862031
    0x60c06051e13051c0207030b090309100c0f1a07020d08070f03150b0309060a11040f0e0601120f0e06060301050103030c02130608030d050702100603080a050711030106080f060703 78
    0x110750002d4614226000314405030010043e08108140100c0050300080740c2c00d5699000107902c884482c401a05e8030040c200000300090404421540390040080c100c8202c0a0300c802c00701d0300499405c000712240e03010b042500c0081241400345044d1805002c010742c45500d82031100a007808021040103003404402000d02000d1500841041007400e131502d00058080d000a00c0c2c0100402e00342c0c0403900288001041c042040808507140e403042440c0c0c0001d00070242d40c0a07408810344260b01c0741c1e08042003100030034820440407403203680e002881450140100303d000c412401c1141c003800c01c810012581c4148510070304400707000309940461704600811080d0b155032005003c07000c00140003407042400d14080350b51101154041e1001c0c007241c0088a0300d0300c10701c41c0000c0042c4010f56444d130140c810551201804030281c0110307400e60f503000e00301c0c504003248010162190341209000729442005140103040e580c901b440b074003001b48200c10060410780d0b0000095800c144015008508048c1030000000e1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 42864509 1250 42863259 42863311
    0x140c21010303080a0903050735030f07030c02010e010e0304090b01030207020d020d150204030f0b060d150209010c17031b030114010c030c0b070801050411041a0703020a050601060c0605 81
    0x1d403244e075030807002c10100f60510f030486092180d04801040180d803041c034588400e10310807502103c3e4510403555031400c114440e1107001e500044603540c144480071000039210501c00d400c00c001e10166030002141c003090040400382581c0c8143d040c009607600100d001c201b0380d95240075000c040302d428241140f4001ca84c0d000f08001c4007000c5c1010f4000c0c4162a11102000100110656421340c901401c54a80b900ea01e440c079142c080080c01690810b280d400441c03070ba841d00c20b404074061f0768080130b250314a460448848000c0e40252015506001d0b0348480d003004580300320780034004107040c1d2150039502e2a00000d840341c45500d02c0c114006161042c4014000c061010714440c49116007420441e801c2078861400b12248540c103040141120040342c240841c05402c1545030b4141d0f50212014821007448491f1048680120b00c100f00c070070020440c8000040140c0401000c4480c0284140c0d004000d03251151450500207900210014100c0104070741800414403c1580241c002c0103640e00040507109451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 42865759 1250 42864509 42864511
    0x9021309020f091503040209150f0909032208060109060b0d0f02040906060c030f080907030809060408011e2706150807091d070602030403120201140c2101030308 71
    0x55003041e030010320b12402c0203201054521031080103251031101e424000da80655900151070403400b80200780046410240b0780c000d12107070300d40c010f40104044500174003005403080d000381520020b07001c100041c84440001500c800d0445000d5000b40703480c9880e016505160280503070040d03010601c4c040e024084c0340c100b80e0440702c40c0c3d02c68450200b11180461304070002071180707030710081510780341040007d1a190407083c03e6078154040d803512000400310890030380b8015011213890040ea04a04010701c0040d1010015140102026000034180340e1990700c01c90840b0001900881031100704518140303601620f01500c1030711048840c00340b410740c1403038132224100c980142005054680b100f00c60602502140c1c4148003c000b040d0481e03003965920361880c0010140410a01906616150a48402c2c42c001880c10200d031060790055160030b01e152100d8090b0152000904115502c030000110f03ca103407480754500544142c82c1c0c40e9034940c2207641c591171980c40748018408450684004202103900910b0003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 42867009 1250 42865759 42865769
    0x90c03210c0109060c031a0604060c0305120a1409030f0901050c03070f06020d0b040902060702040b01180b120f191113030c05090f04151802120604030306090213 71
    0x180840c480c010608041a000c0c071110140650700c1c0c4a840c4003481300c0c940210906600c20f4800300000c4182c40700c559a5a4104c405e030f540c01510070001001014440c2041c10701540c0030703140c00d42c104a004001244010000d03541ca0009070b4840b0a2003c400c00c1e100049074000c4e100c103004626042085240c2c007614040c1d044a94188400403400444008041c01100d401d250300c1080d0b034004495904d054402504201c2146c0d0840d1319105044006d810240304850106070000d00550030025560b08010161142c0402241006840340c3d0000d00000380d8a0700700701500c0340c0c00c941502d031000c801c0909010040282031440125004040c807007104031450000b00441085000032482c0b006c0602c1420042c0b103219000c03030b4901d003000e03400400d01039481c51010580e40c0071075001145844007090341c0b0b0a240b041e500602940c10500306402c0c8400641d004144100390500c0360a82801950006040e00f08013032004070164001008000401d6418403aa002030441c0d00d070118103251300001d42c0a0f40709094090 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 42868259 1250 42867009 42867043
    0x307021b0a0302030303040b19020901050403080307030912020a0516031a07030213060207140402070201122004090b09090f0a0f050c060a0f02010f05010605030402041509020d14090c03 81
    0x1090660725840c04003406150090202d0782e503403d040ca404441003e003110340000c41007a9080740b0361b11a09500845403c04016503a55050a046072030ba20000c0c3d00140c0440305155070741c05018001240da000c0c4407010703d81600031b0300c00c2c0c0d40c0078100282070608490518813018201d12007800044c00014940800206c940360761500c1d540c80200503002440740b49e40c0803903407442c060700000f06544d00040c01000c1c0da41c400d5511007103412010a2005901640c84024040b442d0011038090504ca154006111500100041982c0c40c80001d44108650f000d41c110443c400d4490008200b170303081c041e80c5903801000420051440b1035800b40311544400c51520002c00944d41e409165050040030002003d0f8207000a000c5030ba0f41c06400e2002c0d2000719425030440c050b50030502e12031030081840c480e05040f038a241c1c41d120b107150703a15802c01000788000f400100e4a000724490120710b140d01840030304a0b80154900009103104175011220480704000c0100c89103501a800b080c1d000d803000710b006e5030341d0841c082c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 42869509 1250 42868259 42868303
    0x100f0303080411030118110915060f09041b031d0d050702031501060c0b09011b03110705060403114e0c031218071e030f0503130803030702 61
    0x2030034103003d21040036456499802c1c500c1ca8800100e9441c50202c945101c0c0c0d00c21400d21030310b88144840024111a02d02c0411440c07689040107041c00e03401480c0403452440c10310b00c2d20001400140071500e42c0b6080301c001c9a0b02041c0307001c1e01c98240c824070f464030b00703441d041460041c600348045940e41000d4140e5401c00001050510854804000d4550f0407802c203590402c0700d6840e060020321aa811031000d850760004040420711111042c89100c103504995412000078291681080d0050110561320400d03000c4100151804940c0601c50039005521070350f9078490040d84580c0c0986801c4100c201540a03079585a81a844018400d1048955040e24181014038140c410030540c0541001900c03011503050004100e4908603001c0000c0030498003581820b02107482d60540017080700f09180c08800f05a004410501098220b01e505400200e0b0784810300d0040386e00d903554640709034982e5400310780540c0046941e45100c0e000e0b1404902420082c3d00550452134280b100075921003026610701d01c1101025 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 42870759 1250 42869509 42869513
    0x16060e0d1e1502030f0601090e0f0c1b16080c0105040e04050f030a020f0d03050708041b09060b0408010b0f011d030c040905030304030815100503091e030c06100f03030804 75
    0x4906074041a0007060400001c15101c0380030740a035100b20f440c1412101030400080c080d60061040d201902c00b403410304500d0b0780d990201e08490040c081c2180721803d009000074074400e82e0700c40c0c1e24100d0b0b481f030b100500201442440311071085c15254220300c44a030000c4112034809d9901c0401d9400702d411020032010a1344440c1012400c01404000f098014040090302201181d000a042c20f00d0040b11411900f031344610710822021a58140c415000041031075000c0307000b0590425900d1800200c148070411003d0396007034640c04464039640301130344680300494100080c0c1001e108480c02008140c400d10040f0f0010000240200780c440c1c2c10081581140c8400507060320304000c80441d600d0f024104101a10840c100f036035803a00308440032070000702c032000020500402c0082441c41c800c1c0c050b201c2c8844c0248520190752a800040860780607100d40380500003114050f11030f5072100c00002025594070103280b2051400d007100240000c040c8081100c08014190100c4120001c07203406207025181c1d07480324 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 42872009 1250 42870759 42870803
    0x4020408010606091a0a1b060f0c1205010b0c1f0204081204140109030215070f0b1303090e04032309040f0b0406050312030a0c05120916060e0d 63
    0x95044440c0c50342c40c2c020041000d94000c10190140c0f07070344080032601c944d900d214901c258816098800c00003104043c2d4406100400010039040500c0b40f0743c0842c0c00503003a040d90003224000400d40002801c05071001130320b00030b40d1240e140501001c012451800d40a4104959100680801c80b189408000008800f2040d1941690040c002071425605014070141c1e000d14150060301a186e04e2061021800b000c07980143c580c0001c9a40c081d2035481d01003c894043c0790309801400c01550b102c04a04004d82c00200c491080c180b04544c0d848115601c0d10060a00030a5603559421402c2c0c10464a000d2002203500800400002c0b10700c0f6005010b0018401e88008460080608203600141491b845001081d1342e5040380700c410ba800d40303007080700942e44c4d4101075441e64101061500d0960420203d02401d00a4001d8000503182d814400e01d4070746003169034543c010003191140ca80d42c20407150100c048850b000b50200070042e914040d00303240040400500201882e00b0300074685034403500004055485 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 42873259 1250 42872009 42872017
    0x21b06060d020d051c0801032d02090903070503070602030a0c020609121b0d030b0316061704062004061b08032e08030304020a0501030501080607030515040f0b100908030a08060402 79
    0x690301404680408001010b0101c032028001204c12803a89d0a034643e900b500c501d00c80d6040c0d50184080d03840f8000580038410390110107402403406000410115000c224100018040c080c4641c00041c2c0c1c918100c0380d114200c682c040d581c1c40440d00304900b07001c1c00071800660307402210703c402c4000303a458003004d000c08a40b100c0e02c012010075010b00300300121002d805072f00101e0710000035806d4a9032000c40c4d00074446010700a005020204001118100c0308101280c01781c1c1c0d2103441040005842d264140342110072401074666000032805c00101444043d0b481110342e443c010fa81001c01c031480d500360f40c444481307010040801c4c20409052042000b00e4410b1590075404441019882c441107880b201115120380c42102c059000b0160100001900e512074410207040b034850101400d03032510b88010480c0a450080d02969201100c072441076030641c0c640c0300b04480036824902c00a00712516500b071054550306002c0e40300910190100810680c4004030450b19448072a180510140d503c60002030001e0103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 42874509 1250 42873259 42873283
    0x106030c02030421060f06120312090f0b040c080604020607020f031203010f171c080405030906030a05070e040504050601060315080a080c060907050303090d03050c0f01021b06060d020d05 82
    0x3804a103401c00241030809849145c0100c0060000401d000c1601d03096600d28411107800500310509800801e11518010440b0300300018003040841842d1103070140d060780d185007900c1119422090104001e080042d00005013080c00c0a00094909900025461b0180703c1c0c1c080d0082c00c2c208014900741d5018001c07043c142d20202c02c0365850307507165004c9007625480d500a14a0314007080032506481c1c800001c0e4001c41c0c4d1007542c900d500100c0402c10407914420003900847d10b034401400081072a42d24079000d503100740c000110005061500e920018100c2d00100001d40c000ca24047c1408082030000ca0100c1c1590302d1410041188581038083c2c0456084640c0a501e9900074610410308120b03154001b420079103002d400f12029070300e82c610702d280c50701000e1061030b0345940104020425070402c800b0102d00d117800b0b402e069083c080c04101081c100a801114800e80ea540000e4096081e0a011500440d1480e114000c04103441c103040441e012017000c0c5030280c4900c0812805204002c0c0400c003150080c6 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 42875759 1250 42874509 42874529
    0xe060114090d0f110a050406030c0504020a1202040603020a140703080c1606020c03070501150f14010504050414040c0605071502030a020702120c0117070f030b0301020c030408060a1104030203060106030c020304 92
    0x2440f40d061882c80300e078040095601c25504c1410003e21803605001e09000e581c3c0001b42111450319220802000354003210552080c0003201c14031350703030030003079131000e04000c01140c0c0340907a4030100c1030710082803142d81d01c0d0a4880301005206001c0825841120603611070f129218955482d11005040208400c5010000301507070300004042c00040d4000c0701070700000d0720130002480b40030308482d100c04038102d0070b0140700b1090050b600208039010f0482505000340606040040c03406842d4000f050513944003007056090103016030240301c01c20403841003c200800303803441d01c5070800b41c0d00e59402041b000a0700c0b02c26500c3d6008808241c0250050f41142c01c0640d00800480c401103a50f0610398594062104031070201e0030301e08281c950704590300f452501c680c1003aa100c4200d03008903003003a130041482c1700c03c040e0159420f00c010112100c00300010009030110f14020046440c003001e0500a481043d1100c0d00000b00600041005131000a2201c6c192071150902141d05440d16a0403031950050341d018010103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 42877009 1250 42875759 42875783
    0x905040f0b030c0a030312050615030103030804030228020607290403170705160321061403030a080105010c060b10030501030209060d0506011403010f0509070f0e060114090d 76
    0x30110030707031103655205402c1d8165500038010030108400c040750b522000d00464181c11088035218407035071005a000c00000c014800001d4602c002200d2030700700347c00490100d410b0005002c14180c0400490160742c0d40880160b032502c002030902042248250300090180602180c0c1204010841d020704001032040d5450002c07145c2c0b409400d8260981c2528150040744041c0d00ca0805500b055140c0c92080130142c40703480c80d100e00040c1000300744c015801300b5010040051280c000e8400c2c085905520070303242d640c001c20355a08000309284a140ca0046046c42980104400b582c2d49030800e814904450007420003110f040da01d4244840501002c040c410360220602004a0000f605130b400541603d009484641c0a81c0c4c0704001e002401d85010005400d035072008004010314075031400078591920000d4004500c044000d00c0501c165282980c400d206d075007024806000d1079030703812007030002408600f020f00030a052210007c3c10341074151604100c0c6480001342020740b0b8036541c00c01031542e544242c001c101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 42878259 1250 42877009 42877031
    0x903030c011e1104051e041104060201110310140102030d0c0f03050c0c0c040f0207020a03110102060c040f260d020105040b06030f15070e09040c03020102100501150f090504 76
    0x914040071010100d0150221220048001c3e02c1086495000c1c0009980f403e4142010010884000c0d4400c1d40849008010401c4a80b1540240c0c203648a03d600142c0d140ca040c040f001c1d00352040c145801c2603855052041042c2c000b030320034022040b0341d000119141c600300a080101d00b0b520940c034000030920705000304180c1040d405181c66502c000e01d82e40420540e260500c64201d51311815007400420b51040b070700c0908518055100041000e10110300520b804e400d80c1c00720320440e040342e00c00d54030b01c071180c800700f50076507014082141c3c02840c03140c0701032a007400d0020406840d506801407400305202d42c60040d10160081e4003240001d00b400089400b128010a40207020302800c41b42110360048140118a25080000c2c403254040c5000c4e000e850808840c4455521410b00140210100320000151154a0b207074203034001d0246020300441d8541d1400c3d4000a45008a2185006070760b6241100401041e0300c510355490b4141c0e014580403407216112034003204e40580719003049912a2400400c80340d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 42879509 1250 42878259 42878261
    0x11011b0b04030f030506011d03070504060b0903011803120c02100504050c01090b0f0406050313020904080705060702030a1403130803010801020a02070f0302061606060312080406140103030509040f020903030c01 92
    0x21250b03200e070303540410719203080c94118141c9509486e41d502081740c07224036107840c202002c40f145490f20054122881280e5402c00202541c810780d10400008900040e814400c3c10203005440381c0188940d070440382124299802800e008006ca00118056503810741440c54a10078440505200b00c1e516090101d0709090a16580307030044002a0303408200403550008002c0055015581e00421400009003414507103c42038500350300c014524042c41c0d1140150200603038600c1540342c01140203032400d42d1140360500d4032514207003020300110705640c000e1101c0c0c81a29800781140000249403030400e030300c0340c4508842a81c400325461b40100584c5010001050345041540030b03000b0350880313600700d801c40d903a0742c1e100710450f0340c40d408040d40043c806c0106e44220213a0f520700d6841c03a449004000303603595903500d8240c08003840c082440009054603061005021050061150210001c01d088a07a94075581d4050712910076928800d004589424803407502c3c2104d54155005000c0c06015282e40c1e00e8108001d038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 42880759 1250 42879509 42879511
    0xf051e0a0b03060f090606010e010906120209060a110d0503040f0320010509060702150c03010e19020a050301050a09050906010302040c09030c08030d14010e0402060d02040312080a0c020d0c11011b0b 87
    0x401745100b03002c0003420750340c0300780c02c048520380040c0c4980306801c0c184002103540304104d11521034259002c214808040d10f0341c000801c1d540c2010307555008031002d8080f10300c0c20501c40200d070104100040c01440302043c0c2524561800c40ea041c10100a8040c03810140c2003000701a2000c0c450303035482d14080042c003e1000c210b041c131401d03d0303a0941d43e26108080c904607961030141d80c80007400006000511940c0a01c120280e04000c09a0f031621441d481030180030181d90000c20301d0000103030003000411180c00c116050074050410ba840a2285207040b071006562103005200180c1304030b071109003008005006906850146421100f559915615007106958a510440c4819400340ca040c007a00d8055103061030041c1651002c3d0701c0c880b1161100c0c2c0030807aa0307820881c216042c440d4204000400034041500c2851207035640d84a25816203000107110013120b000c1c120b10720a6400c80c03100011000d5001803c543c035503034440310035030158158800480b0003940715079041100ba6200203498040c442050405 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 42882009 1250 42880759 42880771
    0xa0b091801060501210b28090f020c1c0e03030a021e0a050601140103021b0c030c0f0f0103020c030702100c0c1d0103080a031b120f051e0a0b03060f 65
    0xb884580d0ba200011624201c0803040c514082c07110120f60704803048140c1054811500c01088040446180c0d004440e035080320303880c0300d001c910001004106400103070040074055000400210308100b0181011916041810f417080c098496051503521040e004054080e2150405011aa12070540780b0019540745603501c41c00328120244e4000b8000c0c82e00c0041d0594400d64040c000e06061f03480e1603040400c4c081915211418140c00780000f201c2517051150403014100c0d1400100030340740c0706405041c10003035003864071400345110786154425520703000c1a08400f86404c0c81c0042c0d44417400701d034840c254040da180007980300c90b40313462017101035500410b40503c05009030010100d840c0d03560070b003510901959140e031105622100041001c02e005a01510f045e03102d5060106061912400040e0040d0682c04d1071400b2802810f0fc40000714014454881003642c03907001000075081c088164280b00100c40d80c8003442458800003d20b0710852908032540103100038041b1407440c00c2c10700494821100440e44 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 42883259 1250 42882009 42882011
    0x61303110a060204080709151a0d110d0504020906040e0606010c0f0206040308030f0a05040c03030c030513031b06030605030c0607051f09110102010209130b0d0f050105160c031202030a0b091801 85
    0x400054150034003000d08541a80329843d912751a028001c02103504014102495039907a51000400710309824024460b101c1c01000c0082c44e843c162040001094000d0596170080e440c00b84100f0010800140c915040902400c1156643e0382925050b14080c01d090002900981d0118002040042e05c0c1c02440c001d03902c1c0b40032181c155603100c4044007110030854014041103500b0500300007007805203001903d02e5000c0c1ca0700c9031824420f15201540c44801d54030848603480d2090f5401c04094080b1041e10281c00d15103404e000301842c020000380d13200d03000380b51244030b03801c006424070420800b0080c542e40070070070904d03602c01c415604009030001c1040080546060901c0c071110403c56106108899000308010142c100000a42184038001c01d2100d44058220140040038404a0b040b10450b200c2c40e0322480010449152101c244610260310741148014070100714100400240c04c001d51080707405100c900161a59606000030026100b0300d00415002040300040c8912241c0010180f8000009140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 42884509 1250 42883259 42883271
    0x6080105030d050d150504090f02041505010e060c0708060f07020106150206042604080a060b0316090e0709060303020309090601080714090a0312110c03061303110a060204080709 78
    0x103240d110381010302c4034400200100881e40f88801503a100d064440074540c8001140758480c1d020800b102c41a11003038800b2a5031186c1001189400d000325a04040a402445800352800d00043c1481030000e224070f00c01c5002142000c0580303810824000201101400c0700d581c1d00744900c003400076807802d2741c810005508003c070205580c1285680110302a22580c001d05290f6526160030f02e1104249510034030104801802849400d1810080c0000d05103070006030150110918240b4101c0702e416681c580240c10042d04c441281409080c0c0c0c2045802801000c070301e40411107003c40c1000a0b6030070039548145058008014103034008003400c0052000d441c981900e440da47d005540a900446503540000e0788001c80c084905c01e41e1001d0400040c01501118003180c407a5150351050044644880005151440d005050b4004200e040307600d401c154082d21450600c60070411401d1055800a020f01910500400d80c141c810003103e9810742e04158215107498450342469110042ea10603040d16604000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 42885759 1250 42884509 42884519
    0x30b07090506121303030e030c0c010305060405090604020108040804350f06131b120506010f12020f011704051f2a021006080706030e0f0604060b0d1a01060801 70
    0x11044941402850f14078254640e100000e1000d030300c484800460406071503214000d40000204090446141c071000070744100104040018201d03000241414032641c02c0c44140041c09102140c02a0059028646060305030790f20300b800861441036501070b500b00120107170107143c100458410134819440b040000880700c050800a0742d5504c16a5000e82c00d00e400035800300d847d518900e04003441701d0744220401c0e90000c0040c001c00c400f030050343e48a003d000440541c16000c004090001c2400f400d01c541c030750440c030342c10480e60364034500042c0c0009008402d0145c410085a000f221806a02800300c40b094000d0318207031500a884031510102c0d003013461001520200d00210320302404209071121800030410718842a2580184000e0510300d50560084004003003034034040c1d004117000f80640000400527241340030401000c45406080c403e40e550803002c210050920081045a04580c01c400049003808041000980000c001382c00141000070403900851610001c00000307040700c50a44801900d82c1c0d0f91 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 42887009 1250 42885759 42885769
    0x501030e010b0102152e0f0609080a0602030c04180b0a09090203060c0d0b0307031a01060306030809120309040e011b110303040312060902040801020705011d030d0506040e0601030b070905 82
    0x2d400064050b801140d00103022084107920550b0001102400185000c4c0d10320031648001440c031942e6100c40411b0505010018180340d40d40010a01d51070604d2800b4640402d441e2034149440d4000c205940010205e130704403417084c0583c0d020b0030310000c0441c01c100211200b4130080c00c9814190780500c40f0f071031002540c0d5155104480055801501503c600c1d0703127601d50720001e0783c800100c00b100e07140c1d9030032011002e03142085218042c42c4511009400e81c1a10f003034440800074142e02c04e40c00c01d4141501400014445c00503a0181402540c000e0955650495858210700488601c640c105d803810f21225003101301500b15421101c0c9200c1009401c01c4000c204842d003142010150500e5131041010800203445022800c40309540442c0006440f911910407005a038016030200ca500e079004124401442028819200b81034145250519800c080b44410313a100e0140c81000403515a80381c00150280e155500500d020920000030340b0380d9980c43c0d161480c0f1a5409580d5980003c841c0500420107040c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 42888259 1250 42887009 42887021
    0x15040807030f06060806071814060708070203070305030f04090b090c090d03140406030507020c010e010906030c0507060203100e09060f011215060f05010221070f0c08070e010501030e01 81
    0x828024011407401e58659410455401804807203950780c484000455020070b0000390300030743c4180e803843c514620510f4460402d4400303401000311141050001c03000390381c0c0c190803203801e103a00c08885521401e00340002400c1180741d520103031032408002440c1c0b40d80d421b03520052041c3c0720341c694200907003401002406401402151035446115007086402100e1404104030008a8803c0c682044d00001101c500005504144e00c0752300460303204d80c02c1c880629014070039500d1404c8286065090341020b00c00003000b0b000d0500c620024140c0d40c110714000c0c248287d04603100e040d0072030815952410b1001400032070362000c2c450300e0f0070800c140c00032401d00d10002c511540501c80e0001e10100d540d09000c844501850703083c900b00c0d140c0300b0303040a15501c5d012500900c0d005081416103003140e14500b00019062607000464000c00000880c0b03001d01d00002001035414803500440607010103070551800c40080407642d007000405125286000995000c0d58198506031002030b6014800c81820b08243c6003038942d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 42889509 1250 42888259 42888269
    0x3070201150b070602090a03060e01051510080708070e060f04050f06040b03041e050609011a030a02060409020f0c15070210060b09040b03012315090f0a0b0d060c020a021504 76
    0xb004000c41000b280094015090488008080c17400c190b9407079859604484800414503416515201080b00100c50f51503582c4c0103030740035100035083c901804001020000010998000e000302c140116009501c11540e4400d01c24000c2c01c420364132009030340c002e00d10760002d00c58640308100b40f0030451201d0605105481c1280d665015044c250b0315140c0d1a0002050507c0c0388180104001c1e00a9021230800c10155000d00035a00001826002010f080d0390359443c811403841c0a58032040c110703001602c40300120740c2100d1320384000507218107884000611511900e42c031070005100380000c28084410101c1503034000d1881740c085034196202902182d00350390551207041110132082c422501d250070039800050100c500203000003a43c52034102e80c0c03180c0c2d118210b80440d804420074104001d042951844580d0048100c402c01d08904c3c1031140e00c9140c100041c001c1c64250f4840058240c1038641e56013910826901401c00e021852051900940c0c4040c04801070744030b003c0e1101a180301428113400c0700d0680b9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 42890759 1250 42889509 42889529
    0x4051201060b3c030f090c03030a0305060a0f0e0f010503160e07031d0a0212010506090103020d140109060b3a1502070803061806010c0b0405210307020115 68
    0x80038500320701c2005401101c0000003070086041c50591159002841c200e8242583e00c0ea07103a0405000c0c450300c03910000c10a91103544210700892150354008245c40e007901c3d581c038000c1003583c0d034403021510a202c00c0d0701104141c8000100440e4100d924001039205504641402c0002d03aa5041015920380e61352027421030403907807600248030f40c025005040e42d200035181808904a0a2107407503490002c2403071180240354122520560441c608102c0e42d00c807030b00c642c80c001e2145050440001d41ca40f00f041c400248141803140165040100300b040c2504c3c041c841c04000c025581d80c0d030030100060516aa1000d106070100c841d070703a81d10740820f011800700560396010300780c0c01c050038402d200c0c000018001c20340344594041c0403003441040710f00080899901c0341710071580300e05254052014444d20340300c00000850100042004690f408100c015903150418203042c20380e12181007090400d003020301c841540304000705132002050b450300f00030b500400c0558001c1002e92841d001c00d80108002c1e0007070740a55 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 42892009 1250 42890759 42890767
    0x9010302041d0604080a020f0c090a181a0105010905060c07031407090204150201110403211b0309031106040e1302010203090a14040b060702061207121104051201060b 73
    0x260a2a62140b2962900901420701407804400305600d051002c6400f16004180040c041d80d0195050040900040d040c400410b66061103400043c84e82c10010132003005595101441406101c100d500721400e1038120341b41c01107070a03009204a4901c0804d00034036010400d6030340001550b04114044818546a21020340800c4c1d0455440c268602566600000320b440760540110700c4130600d1006000a1000200340c1c00030103017590002c2e094174119100d0064500d000d000400c0030a0b0491215207004060011401c580060883c09591142c1c0a413044d0f101018034081960415802c1b4940c00240c0740500329050302080c1d8202044500c0c1301d00d024840008681c1d0700420852501c2151400e44548140166400e22101002003055040700d47d0286451840104880e802400c25208070460800300381c44c0c42c1d1078010a5008581544501a164003010340b11074006410715200d21001940e000314620b00b404055640c1020b03040e03540140c01514412425141c541c150800c05201d010104c801c80f4800b9414 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 42893259 1250 42892009 42892013
    0x708060d0b070e0a0902030f100f030b040204060902032701020307020c04050c090603161202070308040206091210140c0702030a0206070c0b1209010b0a0b0301120c0b0c03030f0a0506090103 83
    0x1251601809100601220b83d0110744140e8401072820085d220f000c000584904e00420075810b900e00191886980c0b0944e0350050000410300000b18007030703940055282600d03840c0d40c03010a00030019540015a060301c04400e01c01c0c0000030400010941543c0725010040540782e0210500700d120a8410b1405a0300004520b070140c2840d8124941c009003d803061400c00200c01c003c540194022203d203c81540c44e80c42c0340c01881c2c6c125041e06640c4450700411400c1280b60b0f41c01a214010280c0081d1280e40e020500012650b501040440c018280c072080c1d0307181d103c528640d2805442c0110801c05001402c1000039032440040c1e043c2c0c6d440d81d030002c00034070b4030046640a100345035010f800117407843c8800c030b0004241175204100800d4075468100c0840600c0c40c002d04c01c82c1c00c4541d152001c0d0304c103211140041042c940c05500796410345040c01030105c030b0f006040c900783e1030303400c1d5541c03011100301000700b0110b54001000c000b5610a6102413040c0580b41c4c1ca880c180c0b011038104a45080d4401c4030300b001400 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 42894509 1250 42893259 42893273
    0x1050316030b13140108030708040e090c030a03020309010e011b021203120106090f060201020a0e010f0c0b0933070c08071b1505041413150e0a050708060d 68
    0x1400080d060006500c40718001181640c144484041d2050380c5820b8a5400341c40204030040c01000040c001e541008d0700c1e50ba4205961207140300d03054003120031402064400d10107100a10003034400a044800c1d000c46460301a40382e810945102d40072540380502e000095020703107600d00d4503120000c89204c80c260795074204800902c603d9050780b060302c0b050040442c01c0e02800144c074041d03c2c0c1034803a00035440c50b142070030314038030070b10b800c09011a40103015400040b80c01440d003078103d240c00d08001d01c0c11a2001c204a5044980d190080c2810542005021800340040340c3c070b4000b600c120081080d4901200380034440d03070210004c082400c100801c0010010340c42001038091030352280900a01e00403503034484003c0c400c111024035505400d07060007004007aa2001c80184640d9050a00368241454008e00c920750082d041c444030700401e0444410a90a081030b480f035191f4620b04498110041d032199030000f04a8401c6803a041d40616080200b81082c0c01400568442c080083c4560380300b000c2503460754 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 42895759 1250 42894509 42894541
    0x90405070203090d08191d01031a0303180405010602030405060a031a0915130506010f0c0602040b0f031605031014040b0301051303090e07020a030c11190303031a010503 74
    0x40c114081400100c9090741d44140080d021400b41d1076040e19241c10803580c00703802d0341100f0403101744960841e0102e800000744c50700c84103455090800040c0300f0050030511168004400d40c1c81d81c03501002580c0d12950381d5404d1901400d410581d010060740e0b80300e64050b6030b240700ba405059030080041c41490400c900c41d420400000c82c00070b4401d02e0301d00402000c40d4181c5000d80e0300744620f041d02684038642d42450888180f030b2407290b80301808a420030070300191070400d0401855040140c074500c1d010030f000c010740445005111520008c0c0e501c840700d100503212500190f4000d84c0080c210b05d201d0303800901c5a030a0307038007031031010030b0000c40e0b640381c0004d010442c0d240380700d00c0340c0141e2186040780459400380326084c41030192070100c1100426614005200c0b00701a006500c04403050001d0141c035aa000500c0c05000f541814032460411042c00e1149e1121911404240d0260110b6000143d0480c04901082102d1190702c0034480e6202c1202040d5020501281d410300050b014000102a000310130420 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 42897009 1250 42895759 42895771
    0xc0d03020a260a080108100605102303040b1609140913050a06020d060806041a07050c01060b07020109080105091b040b1504030b0c0c0a0312060b0a09060801050604030503090405 78
    0x162200e4140b442c815416007044401c600860340110042058080511545080f400a1041040300ca82040c001558000b0689100010010304000d45c46040c203c01004100d40d10000303100340e449103000d2a004004050840b01c1d4507221138001c410000c034074044c540c403030705481e451807110f21000009401d04c0a900402850368a2010240740510b0220f90b0901407d02c440d40220009a5200c202c021032000742c1e51503901141081c0d000f9000c01011a5050340c04803c295144c43c06031625840f000c00c01c03030f003500424000d4061940390601c0018101c403442e000300030b124800e8a800b04515900c0d84a1030072624116080030b203941140c00250142c04048d072403200600001880000c030444241c0210b0701c1c2c1c005690702928000f0380040c09106110040303806640c00f424421080d481d1400e22440300b86c4802c40000001c05014081444844080d560f800401c003404107a10302c1070701ca84031010700900c034596510940000c0b0312008000700d03850600c03504540a07a5080740045281030403940510001740f00003462 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 42898259 1250 42897009 42897053
    0x60f04020d11180f1006050702040203060406051c02011202270102030d0c050304060f020313030318080a0e040606020705030a02090a2a0801080c01080c0304030c120c050c0d03020a 79
    0x282a002c0d40c1c81081103608058410b001400615110456803071126016000040f001c140d4101041030390b0340103007101c2c80c0f0740c0d06940168680e00e4103804a00940311940003950300c0341414203070400c40440c02c88445070541c001d0f85c030b040c0780b000d03461001e408a109105c0310500608000950a09510388000e98001501040c41128642007030001070070704075041300d03600000085002040c8401d01c040d80c0035038240030040c04411807035814861104148180c08040c02020315498120f101d0030f9425400c2102507054000b540b01f55140c8104100601c03c0140140d00341c416072070508003007140761000643d1800d0390390103002002ca03102a82c00700700308280c0080540006c180c0303c001c0448104003c205240695000800c904100e812860000c0c2203d60140c119000c182d210100c0c0b01116030f88102c030725030029445104240d480c4c540b030504540455030705501600034034045001a00f902d9100e1200100540200305403000007180c0420083c00d40c0d408103016006900c0046414081828140611402400608 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 42899509 1250 42898259 42898283
    0x11a0c100c030915050906010e070c020916030f0908040b0c0106080d02150c0906030403260403080603010c03020304020f0402031027060b0702030d050903011e02030403020f060f04020d 81
    0x8480c80503036810308601400aa01c41c4071200800c0712180440d0040c0404440c207100c0e51401c442802d95400c4144a101050601c10002c03a4803140640940c110554010b40a20003a02e040d080c1038407001055240c03d40068901804005003180710310420b08502e900c40511840e0ad441c0200e540015002440001020355903100b001444100401545464000355009011480f030340c940c40740d40d5040010700d98000c0f0b1204010035002651075004499000d5410b082000c100002c4003048a200e949500b0204d030a5031224040c001030640041c0c40900c101802c40092125220802048090f4001917400035000160700140042d28070300382c0c01039a0b000300302403503015100c0d0b510014455404905240b07a0310112020884020305107080c090300000d00b8000a40c14523001c081d901080c0d480c92228000010451302140101d411307078080d0440303080c01d1007003c4500c913040e02e920b85c00fa000b0340c02950100c001d40b00700746180070014004030350180b242e400380541c0052543d032502401400c0c002d8880031614029500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 42900759 1250 42899509 42899533
    0x30c0f07050c0f060304030c08030c0c0f060a15080a020d060b030a080d1d25150201020405030709050403051204050109231204081f15080d0801060305011a0c 69
    0x6411080e0082008100700e040c51003d0082002d14104098041c12040040002080d0480036240720b080e40b0100681d40c0795551071921410740280d10340340060f406035200700224844001440d0780500796036081000480c140c41c990042d00f0100344182446030304250050001340c035100f84086074550103400e010402c00450400207060030a502e030103c0303c0c2e000220704d0b980040070501ca442400210328580f1184c0080d0110f100782d450015036146180003e120010b02c1c92200c4180c1c5040080c40007a035207460040e00d02001a020f5002801254001d1268507400602e800030bc1c042d1600464141c0c4542c0d10b000a01c0b810594240d8008005484564030b42d40b8040020341c03929400d016510322486034000804c20003070100d081c010002c20308009501c0601003840115000303d4000e401044150029a24018640746180074054030081000582d6407030311b0003d40704001180c0402030220982d15280141e80b2804250112381084c010340016105001000c070201d80c400c00104025040d440896118947c44 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 42902009 1250 42900759 42900787
    0x207060f0e0304031a040b04021215090718060501140d0209060d0203060906030106030818030a1202030a020d0309050c0108090a02041b0f05070b040b07183003020a0206030c 76
    0x1141ca88060362000804109000b003003900e124a420304240c0d541d6885c20a529051881c1c031001d440a4802e0302000003440592400b00070240041e00e48580450652400c0790029440c1c003001c1c400c00c040e01071084030f401c060820301e105100a403501612914000310300642400c005070440074046580b59401c01118526075a014090108010307451005640c91030004140b1450740d001901082c001d038180f400501c00aa401c2c4262020451103491301d0f100d00b000c050010340340070009403010340785130340540010589585c04002003000301c40580844e280d801e10340f80110304a034100140038040b17400011000c54150700c2090038641102110044400c14522a00000c0c102c43c00e581c41c15500895091180000c076810440d5041c2038501c2c0c0c14020300781182d030f849418101200910040500d5003c02c006415580074140c0c00180c3d20810407080d08290300c0d1100200e01c2c10110598104504c9181c1c400c1d61040c40031170906010b55072582c081c10403120039a00f80f1010742c001078440a20a20f0612090400d010a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 42903259 1250 42902009 42902021
    0x10908070b091804030c02010302090310060803131d061302190f1d06090603060307030f06091110020d030f0b0d030201091a10060509010c02040c08060a090213090207060f 75
    0x1125481c2d5650814081041d030002001c22034182808410404c40820341090754046000e80a0901580e990b0764100040d0500c040c0c0c1410601551030301f07202290030040000540890f4003200d4050102903140d218000c040c0e003a0380b08885607010706200240250800061145000008800140c10002800c1400103220414660340b00010034115a1584955000140c1000700380c22800e032070400c140e11008190a841844800e80c02110000f01003002500c0c2040808011030700702c1701c0050194414134248000c0e00c000c0300305980e60000e480705160b082c540b040130b01a0803161a0001c009030a0012429406825000304a45a0a540d6103038045a6200d000c511f41c51944a036000080e018240e01d040c050703100c000340c0d00d4814200c504040000740400e1200003030039036406042c20354440d426240101d0302541c06450003034100d41401100803100313030841d03241030003110300308c462151250b100e00f0030304201e008040080000300d480804c100712802442d4000d0083d540502004107941c40d2415201c425600 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 42904509 1250 42903259 42903269
    0x4030f03020a0309060e2409150d06060302030105060d0b0f3304080a240603080703030509060603101a03010c0807091d060918010c0503060f01020304080a030e01090807 74
    0x12825402c82015800245074003c0c10345400c060003c9141c040110340c56040e06d14070000c031400103d9a1508640040060301d5002000074403110380400c240850317040e10307007081030785400b03590412001048079070090080c1d038160351002c1d191500703140760f00d0faa050280c0a901a140e81115034500c0560041d00c8042021107840c5203114a950158150031400c504580003030744131030b09010248424800000702140c21000260040440180040001e070048010301b042c0c6842c10342c0c0b520b42000002004035040c0a003410900a860805c0300d9992507600d647ca5100480f5042c0d8107411848000310440d200307902c468443d8464107480780031001c404003c40c0c01c6508480d030a1021451000401540560021300c05000e800011024485c400030503103e400748803400b4012074458001480024280f0880840b02101c01104a00a000e600040d600283c856401600c0706806400032051000c9513500010403a002c441e12040208440003c80d141191240d0346610000d04000071590000b512500400400010702 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 42905759 1250 42904509 42904513
    0x2040501060e10020f0d0305070216030c030212060613020a030b1801080115060507080a030902040f0509010f06030f0206030c09030f060105182e090603060501030b100806070509010504030f0302 85
    0x1c90b680402100e030f5205902d40c0300f15030007a00032154030700b0042403604084009040c0400d0640b6201030a81c1091031142004007490050040003080c0200010b02c07500b01d0740261001d417030542d00d0388003850701c44108490b425006084044101d0042d0b441d9030080c24000e0452130700198024142e00006e86e0341c42407410210105c100040180003015080c49050403025007039002c1c5031046e1410760050030a0084c03000140000101083e084000740c069000b05514541c0148108202091405851f008103c1510500300640c60180300110b00600c82c4159400c0c1c0e070300004000c401482541c01c008503540000c201c84480d040070300c0620710350744040002004480c04800a440c840d0b0400c0c007405040e00c00d800c00d407044c50440c2c8007804107800740fa400c400807010480311001900707034007414954070aa00c0c60f8085003440749001c0c000800d02015a00841c140c2c1d118802c55145601c40790303000c16540c40a07018805041d0020000329a10768000ca0007030658103810b040c0503003002d98a881d034003c44401020140c002da = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 42907009 1250 42905759 42905777
    0xf061002160b03090d030b010804080a031103040f0b0108060105010507020409080d02190f03020910030903020a2009060a051807090306060b0403050d180b0717040801200901050a03090204090204050106 88
    0x135024810301e80348401518003000050343c0d52000038940040544060a0b8074000108465480c0c482c0d00032440d080d14100340c5542d40c1c206498010f1483d000a0300540b02a4580400410a040c010800d11b0489405030340b00c2d0700300145038007080010104804211030032541001100211003090000d00021400f4408440035050800006008007010031011801c0600c10403050071903a890007110381c0f204145140c0024000554a02a441c2502210010b440b44010b1440085104160303401c0b500304c85410384110350305899034820b129501059010352940f2031541c440f181a82030f00813101303e510991760321f045981c83d5926200d400440305c1030b400040402c0340014045c000c0c0042000740c02d0340064180b8004007842501809810040c2460040710100400055400b003800044100003003507562051400d40d03039070b0b40c1d04240c0d40242441d018403000501c00d03141d48445075107014107031280520180c681b6840e118000ca021070081035440022644250f49411080260300d035071280038040e00d0b0b2500e0380040d07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 42908259 1250 42907009 42907021
    0xb0d060204030c080712060e0f1e0c0904050a0303180f0318060503060f061602032d070e060112270b09010207030519090e090303011d0f061002160b03 66
    0x10f04049401c1241036034495841041b01408420140d900960071010000e602d07802c40d01028200043c07807846a240c0c2c424a10025468580365062103040700f60361040720403810b030b11010300601070000c0720040d1440d0855107501c0003003030094001e070701c44074440884205141115a24000d0080030050280d0020b81c851804140982000050002421b06c5080240c2149007086c00500881101204140641e001003090410900c441400c08180b550003425a40d41610280c400e0307003480403440004040804049070b8854426004c120003040c2c94015804440540c0e54100540b4810021500d500889581e40740f0041c01402c13044070903800d1030744e8442c484a48100340c100804140d1b40038102c900c032a48100300e044006a0800b00315191822040c0f40002640b040076015510b80685034420380b6401e503031004115284034080025416580640c2c144a00a661401c04900c0100d0407a1043c0000420001090491401c103800000c802002e104442111544071b803074400d240d440c1d52064020080220034845 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 42909509 1250 42908259 42908273
    0x206060f03031c0209060d0504060f050603100c05040b04060810170c1c0c0602030706050a09020f0111120a0c0201020f03070503030c0c070e0f0411010804080f0d0b0d06020403 77
    0x500200122150036808500d440025101d1050080e8040c030100094400350845030184c0646204400060103180c50b103a4580c04840541001c403003c961103032600900069a20035846002e0040320060010000a0010410300005042c401e2002d0184041070200041081442008102800d100c0c0e54503030345810011414100099541c003c140e4164680c00c40f010807880c00a42c3d08011042203030100c40b07a0b40000e54640103c10a903030007900c800311a0502040540d0004020002c81c0e2007035200304040d0340c40888a02c100d8101040083d440201540a8030040d849003400d426402504010303030700c801261000c52505640700c00c218101280c1d081000c0e009540c1c05004040304107041c0c40c003943c0b402545945094072403000502403252000040743d020000d503410400b40c13014080340840044103042c12031325108040003c842c21960b40d0300d102d2400d6555407044040500407680164440d00b00f140080e42c161282d04800c2e040c0420503603c0300a82c42c0c3e030b90703000300c075500040c00380000680d205d0543c02d01d10 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 42910759 1250 42909509 42909511
    0x303030414010c090e07050d0f0216020306180606010807020102090d05011d160501030e030d0c0507110f0f040f02121003030206071b0f08070209071e09050d060905120c0a030206 78
    0x441400713122141002260015200c9590100c404c2c45c00a6a64142800220040100c0c11984070250b10100b41409001441e001c0502814000c80c101c415990b1981d0962010304080200c0b51640c0e080349011030490b50248400360342000b01d900000d420200c0c3d484c08102118441c00c1c084c1c94981d1501a000151700c0d404500c100d511206074007030071941898119903805c8003414800d480c1090390b200010300c1580d0f8244180c50388001031610901c084c0042c001c004044c0e4000c0c00c0c05030388200e2440202c03841c915003c07928595081d405418104400074000400c001003080700210000184c0030803400220701d0807540300a214282c4014002081030460500a182140050042041c8904c000600522110700150401210b40c81240001050081d29181039140136933403009412410581c10300c080c4641001110803002e101001d6000c881000c040202d640708a141700e0701d07130840c032585440008103101e500443e0039103009c1d80c00c407040003103039100d0207403640e128081c6c0900c585c1020340340b041016818040a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 42912009 1250 42910759 42910781
    0x103050a0209030304120206120106050d1107030c1211010f020318010b1e010309170306031605010f08090309060c030c06010f0b040612062601140c0301180902030303041401 76
    0x1c5081000210200c0d560780f145000760f040f820143c0d05440219500c0e0b1049840541a90030021171559407480c0103007040d00101e4261050500304040c140700d10203004281c3d06140e406070f6a100c5074000d207440c1c0c214180c03849810182044503408010414503424059219114403442d00140d90b071910300000c98004050b21302c1814264103240040150b035649038025020600085545003a030300400c401030307004110703101c0024401890040410201403100000d5845188260140d5103032245038060001c80d00540c0c003d41c0d0100c1d41001071000041e2085003115408480350b0b0450f841d2102c0240082c1454003e00c0c102001a8070010b40b0400c860000d000e82030040040c03000032008681003480c201418011809008104940d0b4042d1019903c0c0c580c001078004c09028a00c01c1c2d680ba40160728000168a425941e10300b0f47c01d02c0180c4000c0c0c4d1203240e40c28420b04a51042c1c50669003003101c0c4242400040700d118139a140c0710000c14015030360600042d801503206040000e040e80d03468840c1e81c29182036080d8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 42913259 1250 42912009 42912011
    0x40509060a050904030f0c0209011212082215060902030103020a08010c0504090b19140117060a030210020f03030a05040605090d08040201050903160e09010608161203200109020103050a 81
    0x10800c00c2d900d40114003600294941407150340815103240440d0712141e811006940080005c000080320404c25081d10551030042c0b2131944846030700c1109441c0500260750804015120500071301100d00c0b50740841403120721607000881000c1000c040c8906540007600400001503001004004621740a212280100b22368802071280318516134015240d401144504181141c50f540c00e108155181c3c2003000c81040849406d08103107440b0b83e841d404034200308502a000c18581d41001c4802c40202415610941005103040d11442c01c650a100380c240d0f60032490000d5110308200360451000500256208019005001900e49003034180328007598000781100c6a26044001b440b50016400b081d401c0e4440c0e0203007000e0b5a42d21300c010100345064407102c80324034107d10903000800d01131f00780313490396002d511194001c3c020035440380fa440d0f80b03c04c9114040550841d14a030100301c42c60000d03908002c07aa000341028813160019040c4d0481200040c22262140d0750340d401060119a01441900c0d001300527110 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 42914509 1250 42913259 42913279
    0x80307080612030405060d0603150902011b11060c030403050d08150603010311010810080304080a1202010b0102100f020d020313030809030a17130f0b0103050d0c021e0f030106060504050906 83
    0x14032a02c84c41940181030003103a000500e50303140c00d001e4000600650f480841042e801100720b129400a101e1210202d0002c5d0408034450b6910500b154218038454000c8900d41c00e4000c031604202056110141c071414a020a01002011990034000d1120940390b48d00c402e489464805402c000c03000700c074508280308440c184018404100c0d6000441075426080c00c0c0884c540d10b42150781c21156a460b03000740075501c030010700400d0040000c030381081e1492156402e010716000843c0168240c0b09552845030059100c1d50103004c00e4a080c2d080000801402c40b801480c001e000a01e00c42030b40c0c8200c07105200c0e06081d0740d810b410994003605656002110401660814000c070a00400381005201000120149100410032007401980b0294165a020004a14800c0540350010501c042448150751030701415031490069802240741110050b0b00601500c140c03003807400074888100c03081c88000e420110006610200d902d00b4889d07100a040c003511601e46403440e040c03c0006c0000000e0869002e6003120b9 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 42915759 1250 42914509 42914539
    0x161404060303140c0a1b0501030f060806130602190c02120c010203042714010e100501020606060703110d02011a0f0303040603021e070803100b090f0108180105040803070806 76
    0xf00c4801c440d01c461000640d600d00300c0a0302186424008400904403502c90b1600740d0b1540c1002418808035138081e00c0034030218907416401d10488006100301c034100d03000040042c5500a2100e070381c00406101f5000103040036a0f04e1690803030401c841340c582000c100c03885c0440c2d056140501e8002c1400c580080100011210400004d4585c021482218214a01001c403a40d400c03540b10360b80070341c03020140800c010300d19408110100c005020302c5204628200040030502c01842102034600350340060b0001c0107103454450608c4400d50040c00241e040001020b01558104024442080718014130b034004144121509410080f041218074014804d40c5003100194080e100070055400f02e6400b42070041c0c43d40071444902200003a400005140a8000160300003046015406940502a00b1030040c00d0b0726121101300e580f6101d54440568400710200da03c651540c880c012850b03001d01e15800c01000503010020190a491042c0c80c1101c01c088040200601c05e584917103480d50120048031300c0741c5407205074 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 42917009 1250 42915759 42915767
    0x1031113051314090109140d020307031812050f0d031a04020a021c090609050d0201050d05040204110a030209040b06040e0a0b1c14010605220e0f161404060303 70
    0x38850303180549100b40e501042e072202c41d070040e105031041c1400c400d400e28042148600070855030f002110b408011540c0d0600e0207400241d02c031020041d98004520b0302401d510706841e01000501021702c130340411040410904809040e1200440c0b15100801101cbc0d002c020181c108010140000200352070085141c005108200000440a07400d9500503034074501048100e040481080c1580d80c402d00c1d0000c5921003d40c81079690040b59800d80c0d620700c4041d12001009010b25850304040e00040c0c0c00d0200c203400000d5540030642040c801400054003410705210032425800500b20705020030b6020070070310b0003403e2074000c142c0398140c02c480d101d16150904c58900350010002d000c07904070701e079500714608040c0c40e031100e00041c1460111078202c440d50316203010300d5180702d0f5000c2003a041d400d0460014083c204101c0c000c400100400040c40c3c44840c4261141c0200003400c107040952041003880001030380144900b0710030301c030303070600841c0c1007401c155546036040c0514039007501030780c5401c008002103940 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 42918259 1250 42917009 42917047
    0x90304030f03170c1303200a08030a020d0e0105030105040209120615030f030301030b1305010905070f17010902010509060d090f1214090307060c02060d060b0c0705030a020f0d03050409020d0209010311 88
    0x440101d00e8400e48118202d540d001104040315078011962310804142003074008040d255222441c1d080b0399a1650007041201c1d1007580620960100b032041c00188a42c2c81c01d40c002c2c2450f0b030405800c244559409140c8a45043c81c01d5880075000380c4083c900144600342400056030800c01d450086155501d1a5038003007103080d0007400b00000f4540c40c601101080821f401404501d6040400c503000c0031b481d98040700e902c0740c040c420400311078200128010f855406008104c40650161100d50800c076561050214990060181e0941c00341c1d25801c070307000955a80c045003a8640900703001e280001c1040301c0a070010081c2c0f00c000d00ca51505001003401640e0024000086d100c0c41e15005050740b406202144d201d001e0010b1507404607003000c00210b260004003020b40346c20320b02402102c0c4c0c0e0b03990321018141c841c00700d00d10194124010060400f280e040454031614114170900d0701a140581d00d1340302c00c0483e00450a00c410b059000250500250792500403404521101c1c91039900c1c28503220070500140301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 42919509 1250 42918259 42918263
    0x170307150e031303061a0405040f030807090e1302010314010e060d0206040509040312050115020a1205190806010801090b030303040f020120061b040b0307030203090304030f03170c1303 81
    0x180701e40329961015001d10584002e010302e0008180703110b860740b40810142080328074510951070721a8690445240600819004540140b500b10403107070b240e1422a2800e1000304400300f4045801000500c0b0302c0b0b50410180702c0e119200b01d028034003415200040170340d032030160110300b070610360801488031200c25488540c1081c0c0440c0d0b848060900ac0c03000c030f641d0b030180b9481980c5c000c2204042105058009100500700e00041c02d0412140e0b032111404480a10030300c01141c0182e1024603485c0018031a0f44c9110000142c5081403403c10b41d4072402c408080310380c0701d000000113204005000555030050080c1c0e01420712450180015101c503000b00360750340001400941580381030318040081d640191a642c2d070341128100f403150041140da070003d650b00c10540e2000f02e060062005981010129419941030700d00a002561840e250208110007941014001d007515000400000002400d0300e811000f03030310712940b1840040c2042c00d14204610390014402c1c1d6031504200055031240002d10f1801003034036 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 42920759 1250 42919509 42919511
    0xa06050408120426011407030e010509031905071a0106090305060105010e011202090109030804081b09060307120512120a1803050f0d0e010e070302031e0c09040303150f17030715 78
    0x2104010400e405441170f001906e40d0606400e090040c1158182c01024103840808001e2005886403850a5070342d100700100d00710005240e03042c1c819260311a00c002c0c441240100303201c0001640200a40340407003402c2e8010303400b040a030481001040001d01c8042c0c014038003402c0c000e01030069030780081d040088006100d401981d0025064035568015404480596013110349a5102c40d101c003080f96035500d0f06c00c04185a01c0c1c108144480c035240100d10303c4e118040c0540900b0700d0701c1c1751440c648010f0107050400c9a69001d50320104410f12410b101410409010f903901c21030754100b400864040358038113219881c800c85070503400c201281d0450220b95201400030300f40b66440c84c21540003002401e5203103050046508050740d15690540014445003a64021401d417560710303501c080325100c0ca140c01022024280c0022240d50094908041c0e101d82c001d0003810302141b4640f44122180e0524115040507074075800001d0244100c05480c4002d0f400720030454015464038890340c5420b030600c42c0180c0c11640031 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 42922009 1250 42920759 42920819
    0x601090e04140106060f0207091a0904021c06050609071115070c0c030506011a0319020f0c011b02071502030d0902010e09010b03061c0b060f030106050a060504081204 73
    0xb0403a00c9494900d0720b0200000c0000540700c000040214401c2a03001006205020001c07910700392900c90000011f01911400c1c1c90b1034030340400d01c082010f0061003a80d004034282c64052074180c0d1a664000c03024400c038000075541c03801318200000310700040d10410070014602500420190300040008035001c402201000c41c2d56041c504580341012000020510702c80070344004100311000420724140c8092034200c40245032449260b411502044400300c1c08880030784205201d114140e80140341d004003005d209032600b43c18110706400d4400386030000ca0000841841c0d200c100e41d0500c4010050006036001c10f142620101e8000e581c0d006801c130886d0741c182d490740c0c16011603008480c0e4200f90340b806024450745e90b030740d0041c06040e034004035035544c01a4030148484044621003045844040d40c0811005040c0c0c42d0002030022130415503503815003540d42d13580c02091566940280b40000c015aa44403075645e41005126401c00819800c42d0340200400d1000307100c0549103419050480048000342250 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 42923259 1250 42922009 42922013
    0x80111120f25120f090c030f08040504020c0604020103060803030c042c04030809060a020906030a0510090e0309010e0d030f11070905010b0a020d02070302090a0b040609020301080a1203050601090e04 87
    0x628070b42c11980d2600c0405075010351030a41c0050f000d0980c2d140c0000c040110888120880060f51301e2800000d1111252140900c000340032050b0100c100c42c02412002c1c103158403900407508983c080f01039104070307502c41000c00085603858000c000290005001a50030350500c80c1001400740114050346040e120074038040f2005c00c3c9501440174506040d00341c0388036281041c0c1005041c5000c1543d1401d4180101e5000916981c598000c588185001038160f510716074070207940b900140406420020241814003001544000c0e50044d510141b8440002d9980c40c0781003400034060102801000d070284602c0920400802d40260841b0340b04a81030618145011842d6101414009180c00100032710b0314160010034643c03405400703000306260640898008190000341a6035409842c0b0000f0b500c10b01e89400070780708000d03075081101c0b419006400459055100c24241c0240d8100341c20065155000c00f019134140f20201c20031400c0e0403d00d00b0100703e14100803000a00a88084c0074002c1c1401045c404201 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 42924509 1250 42923259 42923281
    0xc120501020f030c07120801080a03030e01021c060f1a030402010302090d060c0201090308010605032a04080609060f011205060606030c0904090b010f080c01120b061204080301080111120f 82
    0x240b04a0250b1070b1030381d901d0b191507030100302c0d04550001d884c00140020240011405883c005050b10001710003800341a400d80d900310040c00083c0000c80c8155001e109046004600982c03801c7c1501c405a00890280d050201c0c00c40c0d48501e0394011b40f0800408503800320031040440413250402d4082c6800360b80d840c03000c00402ca0f416903460004052500d003004600721140e043d4062110307a03100390f695902ca41d17a1400e0461b06804182c5084015551041c2c080d0001c542d40b0100c035042108882c685810243e44185660810800701c42c0d20801d034000b6410865842105050f0901518840f40c840c040030241e0b858066940758000c15050241c08008040340c440080107050311191a0020000d001c80a6946012140e514083c495801040c1c1480130111b00c0d8800400c0780d000202040c0c0d00d8000c14155500818090918200200c2c0c02000801c09820700724605440d09226a016200700e075625450701581034211941c0100280d0851014000d05107080b100c040000d42044954004401580b05c1c10711801c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 42925759 1250 42924509 42924517
    0x618010201180602090907050304050606090403022a09130b04030c020a030803160f081509060a09110301080f0105041a0907171006050f010e190e0a06050405070c0c12050102 76
    0x41d0401d084002c111041003203d80052000304011703628643c96842ea00010b81c1d0704c1c04180da009215070415000103045091140301790764418000d10445100044040ca6141900c0c0171110f0303403620020300c1481507101d08041c1800c40c0c024403140140a4011816241c2080540000c0c200a023008950f0b00c5c0401550742c0d4411120245810040c1c2950b03d0a20300540c64003000881940f1f004900c4003001c1440c0c0f80c1c0105400c601c940300041071100d550308900c1c00c02489030401450306a0054541d40003044900c0c6501c21880354080e0408603583e04c3d41001015403418001c041c00680a070304020801c0300180040e1400d65005181051040f0a40c450170110b0f800d05545402008900c0891100611103000001d240a0011f001c036200b084860340752024426411071f903d84c181c1c045106240040349504000240320315101059918014050302c2e48980f4142d2a41618510041c603280c400611591800e442510340104590416080d03a0649a844007100d048510034003c80c000e01c40d00560510400313404031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 42927009 1250 42925759 42925781
    0x302240c030a050703030b0108060307050d030512010608010503060a09110d02060705011e0f1506050a0c0f030c0b0a0203060906040e0a060203011205160b070602030a090b0403030c08060409020618010201 89
    0xa40c2c0c4076180040010a590050182903000a0502c040740c40654001c0403100e0003600090701900c0901d00709030a2005641d6004022000c10004110035000c1844d000c55103030103403809986a00441d45003070101031406002030007d00d62589803850036000140303551600c1c0b1940d8000d80e0364049544042c00002c440e8010304001425075400d001a01d0141010301680400c241c0c0904020004501383d800400d040f14404d041e4190500ca9400060048600650190040309280d242c240c03840350090f6503498084900c9041203001c604640c0d804000c00c6150302e00280c1c0500c0e000000c44c10352900c01d0005e03240c0310020781114001d680c0d50202140d80401444001e1071250026015552540d40c3c0704805080040400e0a442c01e0080c442c800b092445030401580451383c1c40c00c106814070750715071180ca0003940043c12540d11559140210400901101302c0244a64000d0b01e0000d80100c1c481d0016002d048001c7c8094855452300e81d1b00001aaa0801561844020200b0007000c26550400507801002105d01e2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 42928259 1250 42927009 42927013
    0x510030b15010908150402040b0f03030a08010914040320030f0f180102030426011506050a020105060405011a0d0b0a0f030303060e060604030f111009030308010803040302240c 77
    0x10480124034409442140d6078003039941c203c026031341d140040e460749011a410320b581c030a80310100300507240c20b81060709070322001410110340059040002e80b66601103000000850001e01c0100840d0010340b04072800000400101c500350300d00795400601e40c0c0241c90f2042c010f0078140d04a050320b001c0c00c000b0b075507054500c6451255103a00a501c4174440e40c10041004860039201301c2040a294400302c01e4804a46100300105c0105a81803180001c03400700b01c0311101c456681c0c40d4440180d45500242030014511a110340d907072500c14040003800d641c001030610b0b028a04241c0100035103540e0034042c0000822104100e030301d0f00b0448500c10003814049140c554084443c0c040801c0b051011a220400c4038802e031410000e244d41c50441e60812003044070001ea1000d410300082000c10402104607046072300c0380f03c2c1c41d43c4590034100010700c96440c8482c200700080340309805008140d00880b0842c003412200004500b0030b4a168000358480a464244004004030015100706020f801419101c00051b1002 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 42929509 1250 42928259 42928261
    0x41805163302120c0c0901050d081902030f0a0801031a0106050d0e030714070501081b0712210b041802030c04020a11030d0903031409070504150f12030201060b0a0e040510030b 77
    0x48119a00e030707a40d2514a11a101c146d00008540c0fa00101c0000041da200f8410b6003880f01620a80480c924005107540c25400100300000880d90840028680600c480d2520030281d41941860f41c1080d4040c0c0e801d002c94181400140040c940003002e4030600383d070801000c40c104040240490a40c0550400104219034601d003e221503400400c1c8142681d100384e0319010307559542da0081950100b400c6040c21404002c1010b103001c5201d410071140341d896541001034000460780b095001c0307070524015118040da0b45030080c03062480c103806801c036541100310100e4500c46542d00040d8640e1048562188117036070000310000800d0190340090b10428401c0f00b640d4407041d81c0ba5012000e0000007508600191910038206250180110710b6802003c0d240010032142d81000705020050681c04c820402e284030042c00021140a50281c07000a04812080032603092001d2501909585141c1c20200c460003060007a00c11a6030300c00c032590305010044501280c0380c1c40780f04600b100b0702d035603800103006070403510 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 42930759 1250 42929509 42929527
    0x302030604060b090702030a2102120906010306060f030c090203060f030609060a050a06030803040f080d090303020403050708060717060d0f06020705060609060d030e04180516330212 80
    0x743c0a2440e400c025682c2e004590303140401240c41c1d11968405d040821b88181c000d8502001c0b440c1983e440003602040103140c0303483c07098030410801d821a090702086d4003920043c4200642402000000d02071944020f80c56400c42d07a0b840e00d21580c6000c2c0540507030340880010860354030390599040c0c0078401382c10340b132490a00f01802a1142421196040d030541002c003c920258618414507003207941043e0454290349071a6103440c0c900b1420402503681d80740c14440040d0701d444500c1681c000c1c40c440c0c0c07801a6543c1c43d51070114200071442d4132400c041e80240c000c102c2c20070b0300102582e1a001c80d51800c240d09541c2c1d480011002d05201001505020840d2009002c0008640c01800b10a00900c121105503070b80e0b01c10000e410314221415600400220603e9000178020001c100068900a02c0854600303904c02280c05041a405070a6070103a100d80b400003820380750003001c000a420846a072a0350950f581c4541d900030504420f044040e015016000420345100340801d0501886494100740d03110410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 42932009 1250 42930759 42930761
    0xe0a0803130c1203080a0504140105090706080108030c0604240f0203010e09010615030b03070b030406150e06060a05071a0103260c10111c0c030b010c0302060103110109030203060406 80
    0x4a400b102c0e0b16003020700204086152030481105203034542d490701445e40c0c030701184902074400600222240543c1c40c03071183e1204e40a010b0b4601c685098070080001c5450510010120a810b074440e20300c6400801c18022038500105000d0f40c81900003d680030600700c0890100c1c0161001c80c02c1010161078062480c102501a070002c604840001003c46000d0311a040d0071070880f0094850800b0703004484043c55003843c003d401400c000c010040c29584240e980b6084000f060340100c60480381240d03102216400604070444030400341c1040e000d507000600d0440c001c05c2081c4203003500c803024000041b840d4000c021309511601c202403c42c0c011900603507500d1400850718201c04c64036014031b111f20300e0f40b034101100c5a4242ea522074540001071034003984041003a0300900b003541070152440c1c4200b0031070480000c0500030000074101e0000008410f0f04d000001002c8641c0044003a0410140038004408207032b0015003181540d401000540d443e4940c100103035042041940020740502540d4104010700045e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 42933259 1250 42932009 42932041
    0x306031c030f0b031914070306050109021b07080d080a020906070309030606120206040332060106170105010f20121201060504030c031e0209040b160503010f05040e0a0803 75
    0x5490103000144801c41015140c61044100700403080c0503070f005c00d010030800c0541a01200c150416901d00fa601c9480781815250240c00800b20f16800040100c85a110500c1d68041200114054500141802c100e66100d0000a0000040209400126103041d180d5411141c8030328000781101d40d9100a4600500017881921042d60210714001700011a0300c52210540744071503005140b641703458150340c0d07440001d028013442100c0d02c015050b484100e10403901d140d030304522160001003606625204d002440311544a00aa5082d940030004001e40d0742c000407800148400303424807602100c9030b4140ca210500740a07910420621403c0380c1c0d0000074410000a00140d01000b04840c80c1e80e803031f00401d840500c103900c4020101c501684c2e040000c1180a01411000e030a03c48020090000c2500055082030080d00c0c151103035104101884002c4400303007890070b10080389003406030866160020100c20361400c0d10400c3c4c041ca441c6c40605140d000d040c0050603019900c0310020340c407820095100191080 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 42934509 1250 42933259 42933281
    0x117011508160509011404030204050408030f01050f1c02030c030d0c0c170a080c010f15091b0f140904060303020d081305100c110706030c0e0906030705060306031c03 73
    0x110700c011900345906042002c1c03410100781c4660b86071608070b00c0116000204d0710034141d04d0305018800400169540c0c018030b40038901078641d183d1281003240d5411000300040e0321281c0303d4412541850300988a2101c1d101424503003c0d00e204c8440071a0002c04d0030403c454000540c10700401400d510503941007503450300b14071f00070804449110340315044215101a0005404000c0c0e00c0241014001410301e0000c0814810001c00421102c007103036280c10a03075061a04041384400c02d442e090080c2001c0d44501d40c6084031080c02022101d56141000d0f10140302c55400340100242c490051851840382ca045400c60800a4000c00009a0b203090007900c1e020024140340000350100080380c5110310840e400c3c0c0c0780130340120180a0b030041d1020280020328101d80c04a00f48001c990020202c1c0f40b09003c1080146525280442c2c030030500b075002010700074036407852485100c0d620240071030f42e14002284800ea5a042d1001c82e0780740c6860300020304c1d1052641000c1074030341591462040e01079054002c049000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 42935759 1250 42934509 42934517
    0x50609100b09040206030109150801090804090507030c0e130902060f04030c0506030106050a0509010903120201150b040e010311220b09010506030c030610140f0702090a0203010e0103030302070201170115 89
    0x7060603030420201c0d1100b610084d40c005c1043c0300521100040d075101c2c6141c030f19002074403400f46980b881240c0c01d403008620283e80650003c2010400407170a80110384d4801c1244c43c0820a40d840402e000e0b003e984c0251140303000e101100c10421200b80c0c294001c243c2c080e0020405922840c00c0041031145034400c0c0011103900035013040000d214240718081d28169125601c2e010f0421002040440c2c15400c40f4400030f04110b81400000b020600304021030746904800e03030000c5680348a42005c4420100c0681c082441e21004000401940101401e4641929403041183c90b0890305100011102d21060700d40600360700d01a120040109aa5400702110010a03200c4100f1070380c1c0c0e803081000da030004480043e800001080010414500142000140d000c9030400c0c003080c0c140d1103000c80403a00543c0b0745141c140c400084034400c0d403600e0900e007588124000c9055180d036040c0900c001901c6418840141450340100d038141c11a8041d1302d86012501001c8618001580c2d0381c050104030b040c03100e90040c00300f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 42937009 1250 42935759 42935771
    0xd11071d06240a050309070b03070302030f010b040506070b0901060f12120c0f0b0603070905091b0d050a0f11040504060209130b010206060607030201090b0c0307090905010302030703060b0d05060910 87
    0x407504015a80c0c81054032010b0701410301100600c1614107610040c40780c0304034000c0740804545240d00c1c2c2c001e14016465503400680b6840c051401000e1840c060f000b904a004060000700900d54401048810441d80003c038408913844150307203680900041c1d0424030702040ca0800220340c02c0428050440c069000d586000d103200c00280d0181d581041040c400b034800010824448081005103075050303040030016040303868480e034030409007044a5083c0d5864240b80c11120700b060080429809004407107408a43c280078120150b0349840e0344000e00303a070041684030b02103044000d024284212544505014006002900d800d1520307500950010104511038195119204980307844c0d441100683340040c0c0040c030040e25040204000c0d5005001d0071802c5640740d5a00300c000075000e0206e0740c010300044101549900b00f0510103818050103400044103c0d18100040000da81d000942d0350480e5000900010101e60076400b14010000000000e4014418241801030401e00010341200f4400700c05010009 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 42938259 1250 42937009 42937039
    0x50301050105030109020306010c02030f0601140916030b0319061b0c050a14010f0906050103020f010c0b070302030a09140d08010b04050a09020901032403060c09080d11071d06 77
    0x5000a0240a00180082c0018444450203500071901300741d050405910211996000a103442201880701c0f00395040440100f005005042c083d03100c80710100c8010300c082c80c0c40c108542010300143c124004060f101c107a5048140c5052142540001d00084a900d901c00d503414644050484051030500318045600748107005403113002d4964042d41d1042c054140703c0c015494003041896164a00c8909541ea10003034032215105201b010742c6a48034070300c04901076145004201000d0031004900781440704005d04c450000d070358501100d03403000c468140180c598454140d52001000100c00c001e00c3c400c6003008002403c80c2c005400d25581089035540d8100d0303a02c0c1e5600e032129004621415420800410040c0404201030700a4228008180360018401c3c21040c49900303c42950a124030644903580014824480b040c01240c4041341e040c1032601d5107520700240f6503521199100100100016419040c040e001c06110b014010b1a02c1c20050b11081d41e01020500d96400598113540720380f8465403803c075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 42939509 1250 42938259 42938267
    0x3030910050103030c060b0105090a0f0510020c01080112050c060414040b04020a020d03020904020f07080304060b04020a1d011707051c0b0127050301020711010f03060305060a0903020304050a03050d0807 89
    0xb050300c1c1d00d5070301d404800850f96103004c05880600c1425051140030303c24100c0d25180d200d030180040440b4a070004540b4541010700000c201010005000c5402040086082c0d980041071181101c21441503546c0c0400c1301e042c6030f42401c550504265104030300180c0000d03801c1c01c2001000c8400800c0f035040000030601d038200012480340c441c0364170258100440004400303021303501034844550302070070251400c44120040340f2036900c4250103d030030039404028803050210501c0f9a000400c400e035001c52800c03803201d40c058002c528650308440058994811007100b0703441400000342c400300d00e40b020a49400d1001000d04990440f41841d0b1002d1001410701010f40414040c0320400501038480d1880e44030b02c10315412040c45510302e03103548124402c800041a44091000b014003e008a15125218443c14001400311441041040401d0301742241030021a00118116821000a51000501d82001e14003a41540101da0046910000441d00001800000301d600b01c1d14841aa482070007555134144107403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 42940759 1250 42939509 42939511
    0x3020f0d09330c0207080f0f060c0f0d02070609060c0207140d1101140f220503150114010309140a050706050315040b0a150e10020d021207140304080303091005 70
    0x30034122039201c0c030b640150311a07000d84869425841a90001a01c5004942c03070552a84115903565010035854804642d003130201035001103403001420f00d0140a401d4600040c05041b0004413140c1e400a484400c0200d80d45c4400800c0340d0061003801103900d8980e0180d142c940034820b40c90145100c11002045140a400078074429510080400340c01d007030b40004661401829000503214a01048506034803041038029103441006034501c3c00441c0a50304808620343e00c1640a18060313400030640520b2031000b000d10f18103445000540d0186000e00400407800340c1040302c80508500140c00300308030346000101c0d5001c0300c140150100e5060a80c2c883c130840e02440b0440c0e182131030400f17000c503840f130324986504101c003180b60042c440461252030359020080c89a036200c401000c030340440a807540300d0a101c00d150f400101c03e030014003041039003c40043d480f0f40244101c100145400181034042043e48400b8050070040305040700d496603112400f2139900d510036525003140b403107518064110b415280c00381e2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 42942009 1250 42940759 42940823
    0x60d0506010905040c05030307050115091107030804081605010b09060603220302030403150207060b090105030d030905030d050708071701060c030c11090a06050f03011401031203020f0d09 82
    0x80034240c0c40c210004008080c050401c4400595400d000610707641d0070030103003a40500a03000080c03918074203040482d0b100b605078440c42c01c0074180a820750a2400000589464503058141148640d0315894006441d106540001c10a00198480c400a00005500ca0014240306171003842c1e2907101c00e410050140001c0380d440754045d00c8251100805003183c0000c00c42039201b401102e04240e00c6c2e0f51194000a500a41b0343e111035408a0b5140902c8114043e0f4103134000180c1c1d20708202d5040030007080e160380c40b42d980007003415100c42d44c900030000104111144003011500070020750074000f030f00800020081d960000000c4184580100020421b05002d040301d20a80741c40303640b80903656041c0d40001700c55a042c8c070060002c4841011546960310820710a00c151000014094242410880000e580d40030b6140244c1c58031400e554019a000d20301819660011491607441c4e1000c14128068801c4030400e0410340c02c003107901c91901041e03401c000d890b64810b04283e801c03000400510a030040124800e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 42943259 1250 42942009 42942013
    0x20406090b090a0b0a0c0203030d0c1709070b07020a0e090109140607050a031d07030819030e0d0c080705121209010b10030b210f0f06070504150c0b0a05070206060d05 73
    0x10031104c3c0003079000305500c0c01d20742404141640305130006802c0d40c000c82a181041a1640c0b036844542c1e5001003007008990003424098518103060301100e5440c107250052840d24180011b50005642d950b035900402042d100b841101c0c23b00d82074011074081e2201150454900d0f0505a015818041c04106288200390b10382c1d42070304241052104070040d12890461900601d062154190b04103004e11242d0061030240074040c1c0e9814200c03000030305044c00009a10300b003525205403400c0d04500030414000b030310305603d03001220344000c1c24101505d10500000506500c5006104003521b400c0b0405003210700c200c84001a929a03420251600744d0701d10500350b9034442e0b000000150198001e5110000c01813001c2c241d108000f843c41421403142c41e80d401c4103185903108a2800003214800c100d0b1901444a090242040742400c0341c020300507028030b02460701d502a40100c901e56107803040c104210420341107003004089051a501c803070000c1a05460a00050081b800000c0190801c080c0c241c1ca44e50740400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 42944509 1250 42943259 42943279
    0xd03050f0304030c06020c15060102030a080402060a021e010e010b1c0b1b07050604020a090b030706031e0504080703020609010605011706040906021201081b09010b0c0f01020a03020406090b09 84
    0x31002100380e00040040702070104003002c0e8001304000f031014080b8000e0b8880200030341c0c80d0f007034403c0e0b00d400c030000d08103411980204021004203038040301c2c1942117941034440e540c440407140400ea0400c20001403044a868500c01269080601500f102560700440002045041d44010901550301d00b41c07441f003100444003041c03000019132008c090540c0304078150f03a49001480c0d03070b04901c500380d4403505047e52103a0040703045c001540350a5441000034840740c4001c207c0742c0a5100483d40b10903031407003044217240d95405148030542110400c65a521803e59003000149014501504587c0000b0b5042c0e0040c4103840c00a842e60405210764410749070140c607075104c00107181c0046004180b00601c0c05030030944403a40c000002e10b0a001625440300b003804041c51642c10840440c0c42c1c2510b0554017240090050000031180e110300070214192000c0001c2141d540314030344001481c00c4001a41c83c0750540c070005052071001e0345a03010f00241c03029640c48007640d1f81d440011551601a072540c00754490000300d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 42945759 1250 42944509 42944527
    0x20301060f0806040b060a0504050901050f030c060c1c0c0b0a0b090109110702060d05041a04030e100c02090106090614270a0b04030506010509060102030310030204050603030c031b06060d0305 84
    0x480c201c0d43c0410f00804c0800c842c24008007103901a00007038946c2000c190b01003030500c0289030020202d405003105403001ca42d8050305c02d00003590703510010881c9020b481d00003458802c2200907c031100c1d2050342030480300704c00000244020044180c00506803141550280441c801518601841040020042c1010803690070003a10300f00400c00032182c201444020440140185c844601428800c40030107000205407525040c0007020440c0146400d00c1d42ea030420812001039048915119841010341e4185444118004281d4103450001e0b8040c3d880400703d0000100d04d5401846401502c5043d5194042a0f0840c000299103001d02c101c071460740d8211078045184180c0b084015042910000d00c01405d0a44e00e1054843c0f43e44140c000350b410382c020304018071260274540b0b181900300c202880154030b14900f4244050b601d900300d00009114684943c00f040036a035040068503881c0c0b5406060307954030f012683c0740302510704000c0300d02d072550701840300043c20f680350003681d070060705802d900c07a1441c00c0011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 42947009 1250 42945759 42945767
    0xb061c03050c030409050c0c0d1403070e0f030a0b10080f060c0a05090d080702010306060c021c112d01050304021302030702070b07060b15030c0a120e0f071404020301060f 75
    0x2c0c400301040784400c0c0000201000d503030290714000e55601980e10b41d43d0200300700107030800e00300d440500d0034003610081c814032002040c07007121340c002c00394603103004241d10740400543c2c42c0401c1340c61190b140c440c1c5403441c0d0034000342d046007900999224503e0b588203076803079141646449250a42d00481d821082c005582c0d043d01c1c42c020911010703103150043c580818600002c98046525034156108600441d00000b1940c1610074a0090240c2d4100b501c00300000e580000c1003060822032403900c41c8a400242c80400c08a9100c4441400300140141d4003c50401c2c40b808841c0c0d1941d15032951102c8600505526502500c1201e0013140c0151109101c1000c0c0d0100001a51015103620210f10900b4000501100503401a00680d4419040031551071070b86030030001d13401060452210740d144100140f004c00c94004c0201d540000840c10104080300300210b049004051404a030581030241c1740290803004000714801064400342c0e00c07181500d50760001132008034002401900042101c0c0c0e040f00d000d507402 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 42948259 1250 42947009 42947017
    0xd200a0510030209040b0405091e0106050a0506070c15050705060a020304031e020703120f200309040906062301110a020904030e03030d0f05101a0712140301060c0b061c0305 76
    0x3001c0c0020541e54072601c041012100115440c21403a000201c0300c800c40d05c80ae1901c1041400500d00038020743c1c1c18000001d408072400d114641c410701001801800b00000c0344c064000610281c0c5800c0312400c0000400340044d840325004807100e010b4000090034865841c403d4030b000d260107960350000314803020714102d4518003a4210fa81035104402e400170010b10f0b140c101820302d00701a6a905100c001400000c0c200454088540094510303152000020100000c15a9035001044601040fa0303a0142000002085d0a07001070480c0e00f00e00c1c0c0031a100802c09040500313096800e07a40c8088250361024015180c000b80b40000394444094008100420f20400107103100d0740c801000d032480c000d0300c46410703001c8680c000625045a40c961040102804034000d207000140380c541c55003802801c001c0d0f03c9403032920840b1401018405c2041c0660b42c50345c45500d203a007511401429550796540c5800025001c2101c2c10f00c101c0700d03105400005500703400d02d114041003003000c0d0441b111561055a806403682d0700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 42949509 1250 42948259 42948277
    0x1605060c030c07080a0c081b0112060504180c0503071404050406060b0d06030203070b21070c02060a030509010506041812020c03070603140a110409020702010e0d200a05100302 77
    0x1000b403100c00e02c800320038840c0c100141030000080c400f5020390300e808900342581d540800b15941156041c0000740c12002c41341c02c0207550901e8100c28400b8042c19500081c4040c4d040301790400d1030103d011103031010760318802c1d58141c000e82d48646029a00c0f02055643d5442d40216070340006000101c04440c2001c0d040345803c584211400f10311640c4492a08556401141001000a031648010001e6003800d22000010b40007a6907040d1802c10341030341c40074806c0325048800510720b038540c0c00600c400d441003000c666250b6004004036038a000f007550050240c0b409442c1e2860a500c4c18003c0342003490680b103201c0c4550307440ca0450007000910744a030311201101e0100d0f9415401042d02c008503a560074000b1340c001e0002900c00250714240d509a0380c6001c1d50003811340c00b400d85070009821201c1d840c1c1080d1811549644c101517038602c21440100c402201d0134112a40081e0042c021008200440c40b1003000121408140c41d80382c20140c0c20026a02103500c91a90861400590038250600c46e400400f0130b01e0f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 42950759 1250 42949509 42949513
    0x302070c0504140402090a06050d0803040609021203030106020d1805010e01120501090207060e0307021c03090504021215040c0f030906140103050a03020f010603021e03010f060b13081605060c 84
    0x1541d9100442c06440402d844110300020000030401180340410000350030a038401001c211580c204004285c034a00d0040c0090980d030f40220002e020040300f50486c40f425640941294600c00441c0303145903403a0820f000c4c02c1d0250040d8002c1d0481703c1e21801400300f07001c400e10903080c01c81e45414015510300306280301d4941044426095190041a2400b541c1c0c000c0c6002800140d40e180300b42481c004441e95100c04207119002000b045001d681c2c2d42c6100c1c0c4001c00a2000310045a80320b00e42500d00e4504c0343d1019800c80d0000ca00e8950b101100f60b2401d11480140c5102590103211070f0400003214820f00b20700f40460000c80c15504124425407140e140070f84281000a04002030806070441e16009a0045403180d100c6c5c0d140ca0209541841035805610b2041c00134440c8a04503400602900301c07400000080e0f02c030b0500c81c10256902500711407100d150307010302000502c1c5c403500c480c440e80e80103d0404030b040106d03902c00920020f0000302080c0030242624141000e506000800c5020360042043c4040c038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 42952009 1250 42950759 42950783
    0x20d020a03050c0f0d0e10051617070f0302060709140a031205040308040905060a0f03050a020105161209060e03070605030f041106270f09071101151409090d020d030207 74
    0x7550130001d520740c41100361039080d00322900d041008411552001f80004001c004c1c040500305206800a2400095120b1900e103070f10311a001c1c1061890042c480094a8802200300074418141c0204800d40500c12030359503940d4441c1c0f5a038072001074004c10384403240c105070aa4000c002050344c000b0300c10405041480d00741e14090b502d45079505181c10a400c41500d941c0e440050060034601000704200800c030500a4901261031a241c4640b0381284000c00b80c1071000c002407a0004070100303d00d4800b440c0d03100844c44071140c0c01e0000180021001c0c010880483d030301481803002803800080350b808030341866491a18542d5013085640c070035000540126000011000440b49558071a0060310451035121140d10318501ca8610302041c58003042e1440f40650051010180107403118411b00c0d5000710341e828005405e014031440c950050500c101c8202c400054010041020b01420410000b070714400c42e07092550361a503814564407050061030090159110328814100580260050203d40d802640e000e004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 42953259 1250 42952009 42952033
    0x30c090702070b0c03040905070c02060d02070c030804080d17090c010c05070e0405100b060708070605060d080a022a10081024030c0e1e0301060312030504030f020d020a03050c 77
    0xc40d41040541c04c00d540c2000c81c0c03e112030b040b03900c14641d00c444a4900072070344507500c1d008110310344502a040342c002d54000070200244010300c02883c009580c81000700d5902c2e40e940044503220599020320000140138031503407040c0c43d40015541c0c1d005480305000b0b011030720102e400540e40c2c2d070355080e022100350185000008242d0072a280c1c0c14412030141e4041c01d448030102904004031181200001d08c00d06051041070081029802036070405a4400400140c6488a40001340210b4800754000c3c03c0394000110844076685c041060810107030301c00c000f1164110148840808002c6903a00d003908000842030801e1510f00c00e04402d50010848107516103000c1d01c9038401c82e40284640130011828007200c40340d40180b40d2500c5030804144051600034003040052000800040070400e02102d60007451030000541e130383c29400040110750000540b140140080f5020340601000c48040c0e01069010409410300b500100d4841d6a8840c0c40d4064200ca00c50b9640035241c0341c019201c036840c03d00c20303540700300c00e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 42954509 1250 42953259 42953279
    0x90a0b040e0f0307022103040b0d0b1e0f010c021309031106040506010509010b072a080f0c010e0a12020907122f0a02060109090f0b041a01060806030c09070207 70
    0x552000b40d500659a521914018046009904540c14110384071174400702e9540e80c408801d07141035230600d00071259600d2412070044007a0800003a2150f0220180451550401d43e4000c00e4903c1c0c4810340782101042000801952201c2c012800650086070322208415124501d500c0442d1080c443c0c280b1034901c3e460020400d2501000300c600300c4540e170141c00140010b00c0d11045250040ca04016541e02d001b400b80d03290304e142e010381d00318a1204c2d4140e80d6440854200d0402810151031060100e0b0b03449020318201035603035a1003031982d501052115030440b00741c1c1480020f80307003980c0c840b00b4400e082c1c00076070b0700f40a440d600051000c0c00300f165400341224024158001c030424006d40500300103010032111100650320003101c09020100f40304010b9001c01a8020442604503030103204005040446420016400d0200640003011907006008110030030058182c0d55451140140b19000b11383e0303c9080070380b000b00c1c054035140e41c90b40c00b00b10102c446180041c003403548110548141e8010036681c4034404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 42955759 1250 42954509 42954523
    0x90607080c0a05040e09161202031203061f0e060a050310050a0501020613020d02041805060604271403040806070201061505031f05030f010f0e0d0e131b03020705060702010605090a0b040e 82
    0x1001c0301a042328841c003507150800c1080d48410840442d28914184180043e1084204070500050b01051041862055010f03859680e003c240240410b580e17560021801040c41d03004550b150b5010030b16940100c3c203820220442029684c4c1038004040c40e1301d40a94a80240a0261080703900100103420580141c4507405202d158818403000e1022082c03403803801c9405c09000803c460f004074600744070304480c0160441c16a000d5076561904d4a813200c0c65040c101112011550707506040d1200040002c0c0003400042c00c80d00c00c840c2503000b040172a4803a94180d203141082204e00c00065818404294250302000382c2da14840d0038000c0807014140e40707401180c1050501c415802d240c0c0d54510340c0b02c800d60028000c1c0b1541f000400060b10f000101c10b0005040c4d48038210100e0f001d40918140080145600d13403004820352001c0091204101c24104014043c1d44005c500300c4c2c2c1c0e0300424001c50b89950050059400f81c0380c00030103000043c0d0ba01c00505d801070084c0c95440e503016443c0c0f0405805020244580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 42957009 1250 42955759 42955769
    0x9190b0a0e060f0427020f040204031b060c110103110c010c260603150907030f080403031713080d0f0513060b1203070b040204090b090607080c0a05040e0916 69
    0x10500e002ca0800c100d0001c01862580554102641c2e5503030090040f403111580c9003c0184030344841c10307a001140c0b03030342c8842060304e8100348001408418429041c80350b00e48844040c6000794101d032281070880b040da024520040481d0201a400d001560117500b0045a140000054a08000404000c2c1e8250381030f032485840841d01c0c85905096050905c1038a40d1058031040341030328541800c002199a502c1e005091b80504861030000c0f1311740c010103104c0b140085070010200f400c141c0700703401c010000743d001d403108034040380c00d10420060303060803850403d2080944d0452894101800e4035201c40070b6002c3d01640b01010350f20b00040507400000d1003800c0c0680d42e07807003c1e10000e144a14010048400c0c81154503c124004034003044c59030300002c11511802c5c0e0018101034180c680303201141c081c042d0318100420190300d030b0081180c107200002d0310902c1100d0701d80d2040040c3d01c603420001c3e000c0c455542c000c0009001040305024140e06032007026041481d640c122201c01080d1452148c0e40c68142e000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 42958259 1250 42957009 42957029
    0xc0d0c0305090d090b0306040c05040308040803040e070e030c010c021219020301060e01080325080a0201020a0f08010602030417150103050f0c01021605040c030603150c02010608060609190b0a 84
    0x2d108000ba01045807110030040b03401c2500c80c40b8203100c40d118050000410051240303880b10392048000c1e100380c041c0c500550740318180944941c0c95240340e94490f08a4064001002c91820005915a21802310f00d1b5144402401900c41084424011590b020b03030484160f81062140c0351014205804000140c80d00b4202d21400c40da144135481003600b580c1d80d43d44a00529101c00d0014001144003204a42100601001d0310724004021010340c2484e800045026000c080e02140d0400425010740080901f0a01c03a911087c1224500c4415144040f0a010790001603100380410b204000e80000c003a48000c140300c080760958610300c1c1300f41100c1c0200747c104840d10307001001c8010b003d40e410841a000c02c5c40c00d0000d829170b1548001289c14910701441054801c6440d4103581403440e0095010b00301441d00138001e070030a980090072160141c035041d40f0241c01913281c80b100162104020422134001d2000800c0c250007911000321580c603001034400d160800ca0b940309580501991450071400003440302d801c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 42959509 1250 42958259 42958261
    0x180b2d01080a020307020705010c0309050405011401080f0103170a050d0614120d020604030e12060106050c0f03090603040b370f0207050a060507020312010905010302031c05040e0c0d0c0305 83
    0x1012414003504102c1942d00500030300400300c0d00462100f05545085ca000e8071090000c1c04c04448040103580020340151a00c40003164031b460100084068a2007a00c1d102010307100d003000812015001d01c401340040c02c18400348141001200000d24400080d4944903040030f0003a1030300c2048a80307907032040b62210700e0300b0a02030709400c1c45008074844120103009000c2c40700070000701940f41c4030014401401c011410019494650700d601c56a000c50030701c24211400c43d82c407000c000d059984003206110240c400c8001c140c9010300e0010031245404809040030342162500d54840000710b00240100c100d40c0c80920030401da141086400031102a62270b41440b078148a10001031003100c01d0003102d101e22500401065000c00e10004a40c01940d5211000107026555940304a041d4010511a14009072280c03000048040c000d80000341624001c030180ca400b10b103001100403c0c4400320100c8000301e481488100b24410800c0303ca00d51042009000910b801d07142d40000c8225442c071300d010070102c0e40e544 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 42960759 1250 42959509 42959599
    0xf090a0e01081c0f050a0309050d0c020f030102070206070221060a090303060e0105030309130f021606060e01061b020307090507030203160e061803010609110703030b0a180b 76
    0x2085403801c0e0f030320040784031403002000140303101c46000852040c05000101102c0142c803903444501c030690030a080d120400c40d1401c0040140c440410305074400c454541e150a050b02c0d062003107070303102c5074020001803400c0c82681c00d02036400402003008445003007001001d4000b6030240100c0740700c0e609034400010601500e140103021640c0c40d4020b6514907000d0b030014003007a1800001c45804143c2210704894160900c2c0506024200743d07004400c1803400400c118150149600b802a8074500c00c9800307000c5541c0b1179440d420039000034440e06000451000009402458500f9090303030765070014083e11201601c0f00b6000f4280e400135074402001940c004200141d0f007032205d01c1c2c2c00b15680c50385000b8201d40035000010320f0034001c03041c1c90240d845030014060150b5400354442b4004000440b0113000c007880355000e1307003e990090340b42a404281010303440403c500e001680502510800c0a8018a02c40c10b622448010305c4a000c825812140d880f00d00300b2040301d030751181c042155a46024a0b410340c194 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 42962009 1250 42960759 42960763
    0x50702030406080c13091806150608010902090109270203040807110102010501030b0601031a030d051306090812030712050a052a090d03020a0f030518031b060f090a0e0108 75
    0xc000784a00102404170304018003440e10702504507241c0c0000420001c52001c0e00d441e0003902c00304014001441c00802c40d0403a862807202e101110b05a454402e032b5a0f82c3c94a6450580c864414030a00103510b068003880544c541c40c6885c0d25030400014158420b803480164401241e105a07070545503a80c010489008215151701d842d0388a0800384001d1006502d1950350340f801c01400b40046040c10b407034600664543da12508104a0b8102c02012181078000c0c1040c040c00550091103950701610b481507000c5882c0d4010504941129498001010302c000000d41c0d101d0035810161044081100d8000701c032030094513030300409010340c0c100103000a0906181c0c03d42003d01c3c2c0c0c103c0f02031034030b10210320307560000140030b800b51030110b001902c10000b400010314040381000e600301b074002d01d02c0d003842d2024400e1660140103007008041003811000b0022400707040503a280182420196128140c5c100030035282000009001c20b100c85000060401441e8030004124050b80d80004105c0156503004021000701 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 42963259 1250 42962009 42962011
    0x60619092d0b01120b060c031606230105010c060b0d120201051311040504081c0603060c09030506041104020903190605011202101103090a0e0403080a020301060504060305040804030605070203040608 87
    0x1281e03800c012071260100080c152240c91128100c20301d58408400a168441400700c80b07518200300e00743c03540e034103500303802d00e182107843c0300180d681e40c1c038202080c09082d85058605040c0040c500318260981e103006c1c011a2800446142111025103507810b00c243c42d15036081421549118105d0740c030030710900e000000d08585004041c00c10078058048200c02046205244140e40344003500d000c1100d503524248401c0501c0390800c000c00355004104640c0c3c5201050f842603050702c1c480c10060180c4840c004080320001c1e51400098680e4001201290000b5403180b0070094040f0b01600150a0801c40e00000303003440300000f0120003800c4480014000c101a9100701405011551450030504120381c010480c0a181d2461550620111400c1d480820804000750b402e03d540040c11710a0254654050102549050ba0103c3c04203007c1c10106803503c44a00030303a07040ea007003079460030308142c6440c1044010380005001a0b542c032008020100104803d4000c0c54481da880d500156600c030701c2c040c4000d0043c64 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 42964509 1250 42963259 42963341
    0x160e060103200f090604030b07090807080318010302030711030c030403050f1b060304030207050d080a030b010c03050a0f090f151103070515180f060a0c1106061909 72
    0x3018000d07281c1c00b0160b04040d903440c03d9221508544400000e800f00b802485550005803680403a0010010001e601ca0400026078a40d17100741c0b109580c4e0b4062031a81ca005001c401c841501400c1100503c55100b60302171984060f4600e010012107003010f22080c00e50380142200070160708005030078024040100445010a400107008096015820904041e41c4007e00242031292200101050034184200060005444000e00b140814a068500710307403150721071003003078010038140b0810cd56150b028a00f10407900d074150301c0f581d1034070018000840700103404c403074003400344000300d000400d07a40140b5803140003410b020a0168181c5071a0500030788101c0d007102c800d180c25030003040388100240700481c100115003855203407035101c0d071101c00441d400001c01da4a0f030340441c81201035241d444000080c015010f00e5042c5001c206404080c401224034451100e41464140c0c4008045402410722184c00300c0844002001d0290780b0b41c0351003540c419180c1500b81c0b07012820021442190f580303400c903c0003032854 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 42965759 1250 42964509 42964541
    0xe010c0323070305180d09091a0d0219030b04050d02060606161203020c0d020106050f010903050a0807020301021306110c010309050c100905100305011d0c0f0309160e060103 76
    0x15110450000100e40002c0035801019110401300c0c00f40201440140c1d4104c1174001038885562001d00c0041403100c40f071250240d0316040c80e8809445243d0241c100028150103050304001a510350288880403032960046491001d85840020201d140300311420300943c444c0e400740000c0d0b28032030030081c079180d80580090706c900c00412810005400001e078141d80558404130180c8614007181094000380a82e6031640b030203001c0c044040c06800d0303065104005a41040350709041e4080315030011540c032002d602008240380d00003624400402c02500190610520042c0050f1800c1c1d00540050311419480d40401d01081c0380900b4445e03514028000b60230800c20a18040108441c1615400e40d40c1c000194098001e1059201e62008240b140f641e001c06014054140f00c050010990700400500c001d02c04c541000404141403840340304c052011500640680c0c02c00340c2041180c1080c0b6005900141040b8030b075114030285038003a800309610b064001c0c43c02d807107804554a00a03001500b41e814400d0756040e00c03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 42967009 1250 42965759 42965801
    0xc0809060105040e3003070302120c0c0a0b0c091c050f0102070b070804050c0405011706010506040602031e0409050a09030201050907030309060c080f03090d0207090203040b01030605190e010c03 85
    0x10400006581c0400c101000a071a0901600d080c14120300303502c45e9046600350070000c104a14503825030000c04103488035907046181a17949003140c0d501c0d40104454006690000c0e0219400300344009589500641a92940d9107440c0803c4001142d00c05020004542e090140118000b405414000b502040b10084002e5251621075603829821704c100074241801e008050300070805010042002c0c4c16140400361040209503107600c40c00c1c2000e150402c500c140b07440740c98004a11410204255021150301d0703002941049104001080030141820314404240b405110000d9901c0d400e000d0640528805c510000b4100440e040c001c1c07d44000805d0403803e030380400410000650f00102541c1140c88038906840e17401118a0604071074413811040b020003d8011003440358542000c04c4c041000d650b95002c542040d0303551030404040e40412500505010032607001003010540e15001a80e06c08040d4400c07032541c584c101121403c640c00000c0c01405a9903e00e40032100d40d40501c41d0000495050241c4554 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 42968259 1250 42967009 42967031
    0x3062514040324050702010e160b0f09011b0c1d0402090a050703020d0203041b0e0c0d150810050a0608010603051207030c12080906070908031911010c080906010504 72
    0x41c800c51200030b141207280340740082030581c0c40e10002400110000c0c203002c68180500024060414800d204105000b42039401c001c4517511200b100c2104c41c0d100e00d890030000c0050780480c06130020007100d418441b00b00391036044010f403040c82c142c0c1103100300310600301c0506121494400b41c0c0e03c0d04640700d1000c0e4030000d0201598030305d25415405490074901240076680d40d4000c8001c2d028800700744050034000b0081c08200180960744160440c803403400004602d940d041c2c001211042510019041c1c0740802c8540b502035030a0300050b040d4070181c41c0d800203640d580c18445103070042505442203c1c80d542e80901c01841c8a500031070000b861035400910506040d600e400b0b0b190042041e0985800100140d2881018099000811000e070801100240b034017860501511808045501c8605070154038000380030710380903070b022000340c4030810000d500741003100c8a249006541000c501040c4258a4015100003000340034403554141c1d542d6034410135040c01c1100034500181a005580316500706049800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 42969509 1250 42968259 42968297
    0x150204030213050c1308010203040611070b0109090201211d07151b020d050303150103090309060f0201090602040803071406062202040902180f0d0203101a030625 71
    0x12014040000054135129000381e40b80512403c441d0389003680c0c92180000b805201980507611a84c0124424032030b1400555030440b103886404c100030444240c000051150090540c03003c01d4030b52041c1003005d011071031038a42d8282c0643c4d1001c4051000e45801041c15901c094a01c100c03801802500185003042c2005400055048408000c0c001c1045100e24806058011002a5941500903100b5965403195040c5661a0b85c42118802c44410640d100b01041794481d00c2a000c4403a00365540421a030f042181c120f86c2c0a00a80f20704c81150340300d603000f8021a046200501c020300220000b55078031803040c50311290a89941501d40001d8014900700402d58456046070460310068440c0c100390b102e00c1544180090140d908045441840494101038a4480c0d4840f11080c07030040f44c080040703422003001c1201900b160706000307405801ca0700d5003480528041d0082d0a00b4034540c1ca89411032005d400c0804c0c503103d01154001040450464440000d010310440208a400c031031030300c00043c60500c44090 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 42970759 1250 42969509 42969529
    0x90b010212030123130b090c031308090607060509160503070e13051e010b010e030102090d02060f21010f0609060912060e0604030e0a1706060f03190f1502040302 71
    0x13680700d00380c0601d0f200354450868521071000100a044500801c03007a0728400003040040d090b50700031004180443c4060300040103072803190361010306d285e620aa441d03540e410b60707422660300c4070380054080c4280b02c0002d2550080d070703200b4108113004110214103070303442400520140c0c0c80140280c10410090204520508007981d0101c4400c0740030404503850301e4600e10b00343c0392484800d611002c403140b51040702019000382064020990700d07411400b5006003098200d05c100c01d80564080008410b080042c00c000014240c10581140707030321b080c00d44412104100c0c504114941040d11916401400482c00c0026980b02a01051078a40b0707055042020181c201227850203140d0100368200820410041650011400c408502068641d141405c1c50041c100644072610b0900c940c01c1c400300414800141d603a0400c108415100504140e192142131058600740d40c80c1098260186860716900c14041807284c101007031280c2a09903004060b420700007141d110359a003064200d0300400081000d17958403a280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 42972009 1250 42970759 42970769
    0x706030e06041e080f0901020d1706090402130606020f01050a05010503070b07150e010b01030c031e11070804030b0405010c0c0209040b091006080102090901090209010903080c010222090b0102120301 87
    0x209912044050f15a21192086900a00012000131138082c80c0500d880900b103140c0302a0215446008614000d03565400b4190f10700c950102c080000a441c3c1c43c007a45010b4000c0d002070082c0700003c00501481c41030302e4894011401690086422100000d0b0900c0b81542c80f80149904200b2941010300082e143c909601c142e543c21134000c200c0c2c1082c45a90500d404019900c08010094480080a40307400781042c10180381c04039150400c0d011805020b8081d1500d25404606245003410a000040c4020501102849507600b01403104000051160000380081c0d40245120b019510301850b1941c00d5a0840c0801000c11103810822401a181d01c410140c00a82c130800b2150310f0395620400d1868039000f0849105c0311400e000340028070703030410343c000c102c100c1007501c07017158603a21800c500d410b0341310b400c01840c001500e092081011a0381c65010f400c80c2c0b041c60300058038080b2510501c0040b403004070703d1203c1890000e80c0c03c011020641c403520480080c02c0c000307858401c035a04500d4003540014450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 42973259 1250 42972009 42972023
    0x604030b06090c0c15040203300c010902060a0203041802120f0402060706060605041502030f1b0a060603030905040506121506040e06040501050709050d080a0f0c06050a0b030706030e0604 82
    0xb00703040c50ba100c429160301c2d0038494102c441003029540141c91017401541d00780d00034041e0040d40035103088142c0d141c221741010341803609034200c0400442c030095485003101c541c4555854a842c0300503038913030000380440f900603401140c8650414400900482040c000c820b0f50034410483d0051a052141c5920352218003001b54407107580c0c850010501340d119104004204d589881c8022448a4210000e0700c07d45100c010741085125110006030fa480c1305502c40442c0040c0140244400994154100d613024016102911420301441d610308d020754005030030403801704117554414412814903101d400d610880c2100c104071342c03105518000ba00c0394240e0404440301b610710070006180c0e403116004110145802d6089903402d14160900c107000344001e0701d10100141c041d6070005843d1921482c000308154001c0149441c00030203800a07640a101c003129842800652101c103404a4020b00c10103100b00b40e4900041208246c0804050418000390000d000741460500381c28298040050116030055029203 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 42974509 1250 42973259 42973261
    0x2060702010903060f06030519020117091e0c01020c090c0702040e070b070609020a08070b040e1b07031805030321251206050a03020607080a0905030d050c07050604030b0609 76
    0x4035000d44440e08007030600b80c00c01c11a008a018140d00086c1240e01560565100211060104a800c50500740c007a002035064010b103c010b00555084540040c241c40840b40034801459103440b400b034500c0c41810781a080901c0c0e040003960180010105542c0c05c58250101c0c2c5800b008025681c01038a50290003036070746610b4685900420080c0c078000d08007a08000b5102d416a01d0000086c0226a80c224050380400c40009000e140014000f03040c1c4640700d03815400d00342040d81010201078028410410705000c603504840c03a805010050010034082d0744c03a1180d41a900340064600000740d44407500079401003101c5915519011501c0303a100c011100f0349801505c0c0c6074030700548000f03d01604107004203d018101c413029044001d2a00340700c0009001d00400f80d456080186003500b92001a402c0007041016200203440940207003446103803414a0b0031002e80ba4004249002c88904029022600000c5d80084002c2e00b0000c02000b08411181140f60034199034600c41182e20251159001700a444 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 42975759 1250 42974509 42974513
    0xf0b01091401121401150911040b0405060d0209040c0806041b0816090905070809070602010504051002220612060e090d0c052401030b09010c0e010e0a030f050706030e19020607 77
    0x1070b15000443c480c200240902082c00740100b241c1b1555100f00f1504a01c0c0c111000c03108a03205064400319207141801c0c1c0d00300341c03821086c441d059101c0c12619081913400c004450303540c0c2d910301c10044600410360303d640e25443c00c641407204075205040091039960380451240241907200408a5001c05401002c03071000f10142401c1d200c460b0150050b02c1051304080800054603400030034580716414034001c6a0440365114016402c0f1401528042d000388c00c900b02000b140301a035001402c11103107101a0282c410410004840c840c01d698005500064001840794545125400b9240203001c40c01c0303c0005a0819070050b0f503489840c01e15101c140300d440d450361400d2003028031403080440244040b401c50350030300250484001c07501b4001110038480c076002203211711005104000c3c0e402c19644a12086081c02d90055074040314010042d0380c84440f03294040300043d9400c00e200f42c01d51042c0018541c042c201080901a10140f0000041c50352040700b031440c1013007400802d1011590141e4207595140414 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 42977009 1250 42975759 42975773
    0xe04060b0309010c03060e0103030206010b031306051519050a030b07030213080c0411180f060405030a0503040306050c0c0d032703050304110f0a0b0d180f0b0109140112 74
    0xe0303200d003a4802000c800c0018030141074204181c5808195010000181c6a01a611194a0078000540140d2100c401804030140d010300464110040151300f0802605644d1500305841e81290a031001c03084030000c00c04242025032104d618102c041d2000ba000b541420082580500c00d0700c405048542150041a1814001e60448103040c000440d400f00d0715444444081d130f00e101d09401d40d40107500c1c101c00440030250000545e8050700e01460461403008115041080060400b80d2035039002c0020000000c107aa010424080c030140308202079610345103913003041d10031100014007c00e010365040100021281d40071614805d014041d003000540e00a41005450074103071880369440000d041455280300b41504140038500c41e07480ba00c1300320002c110810501c90965807c418031a08031407256400e20101b94203001070180386a082c80c0c0020807903a001c1c40c1180e00041910706840e0b00404100b510306200d4240c1c00c150152a25510a100b5005151256004042c0c1403007048420159210340104201d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 42978259 1250 42977009 42977021
    0x90f060525031e050405150709051507110603130507050307050303030601110c090403170a06030816030c0f12080a0203090303160c050a050705010f11030301050103050c070501020d0b09060f0d030e04 87
    0x14400c3d08020619261410503501c0c5030200401a16000400020780000d100b180c1440c15614080c01d1040c0103d10706550700e090b5046840120380254a100820f00c050702ea80e4003852091810443c1d1030300d0400b045c20711034200100c68004500030380186a0602080d100001200d4000300c0a28140f4200c5070781c28252410001112a00e0707030f000002c0011701c03092660101c07680440800b500c48005807522030711194800c132501440010b1158405025038a032828516182074960b500900301070049a2140c5e80e038500002e9003402c111030f00346407100f4244065502c820350590084070610114030b5400c0c80da6078180d484c00700620b00c900345645401000b1510744102d44c4110880da00408640c4000054903055031070350060b004540c0050141c10417200100e11a01c07448a044e0119801b840c590b90a0070011070141000400d00c480e030100800134840007900900c000d000240c0416030004040b0011400c00ca910b0380301601c4184280602400f4a042d81d0360700e07403c0a4580d6040c100301c0b00304003030300c008039015043e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 42979509 1250 42978259 42978311
    0xb03090a080a050a0f0e0901062106030606090b090708010909020a0504021306020118080316140708090f0402030408030604051f1215020c030307050304080706090f06052503 76
    0x1e010941c030424542010180c0a07150300c64a505541d400b22030800c481444180f44083d5010f407044004000c254018526084401400384440000b05030308803006054640a0b401181c01030356a41040050380791071b1061203040b400480d541910b9052071a8018943d45041c05420422680e5144800031507585142a000408010b0029501c4400707207081d0f048030600d0b5102c0c460155007002404150030400c0100601c800c0c3d8890040c5086486287c40021000916540761040c40105842d10386104002400740103021703c108a140d90303440d1550117101422500551150256005105000c001002e039400e903035000c24103480004007981d076000ca004420884a2814407904400800070995035540503c80b01e0540c000c800000381ca514031035180c000c034032401d506045103070414004202518031400007580c1090040050074204007040d05c4050071a00c440304101c48400070b141c841002c21155000f8540c0c01134950301d40140c0504102c1e64002c02443c0400c21804250317580340c081410400004001c12004 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 42980759 1250 42979509 42979523
    0x10314010608090d0206060102030703031d07180b03030a1d010c0215040e06060a0c1b09110405100f02060601050a11190b0c03040317091c09050f0a0f0b03090a 70
    0x25079115400703050450241da5181c01401030a414041071800000c0041c000c0d03106074000d40c900070032514106d004240440030000984000b00f0001d4141c0800c1124201500320001c29001710848040c07250b0849182001144c003030380060180e6456160800000c1403165100c01074109001302c51401244d0395600b001c40298000540040d541c46020440082c4c4107aa528462003060b40d29940200881c50199120744000580c01c00d51520000d135104840101100340b0341c0a80c21003513203c603606000d40314001d00220041d007011800b040130f071030102c40348403524205041c00c08099a006100a4135200000c10150501100103040e202c490f10a10200c0d05030094942610340c0e052400c01e0002101141040a480d0b51b06001d020500c1038183c001100d008540c90345400c100200c2c1c132403060f600014000c28140c40d40c004ca54810303000e00000c0841540c00400c0380e135a040b0a500701006c02c4031a07010102a9405180c2075031042c04052a1644800181c803a901403481d2203984c1d00510b185000d09500d0010004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 42982009 1250 42980759 42980761
    0x602060c0f030414060420010201020301050d08090604030609080d05060105280c05030409020706050105061c0c050c0303090a020a0801060f0b16080f070218090604030305040305160506100b1611010314 88
    0x7107c030030f800c100e2503803010480c0d0200d400c0104004900742e000a005943c6c3c0300004000341c0d0006020b0b02c0003451401c101400f442d041c9035984c1c803020304540922006907544400052052007001851042c140e00582c242030503410802c10405503810010000392810541003080011042d00340a50402c41c03013164880112995141c032a00c03114044e401c491000c84600e410400046001d2625109445401c8107001190340c0c0070648007030000142c0303d0517080109001e010444007544250504c0114401c0c90b81d00700621f1800320034814460141c241354049981c0c1e900d080c2061291004005811049172201d014964481c80c0030301440e40c2c2854400c4004000810000b607290a071020a800341a01500840d010710300b940c1c41c0d4508020a14040740e4034003d80d00704070300040029000717034000368100e802444c0c03448c240184140803640701d08043c101075640c1c0d07125004008903109980140409001c03c140140d04040d001c15403000d4150880e000141444064002590664808d90183c16014100c031051146 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 42983259 1250 42982009 42982013
    0x1203120b060d0f05130314090126060a1509030f02060d050414010606050913020a0306080303091e0706090506031803030f04031b05071e05090a020307090602060c0f0304140604 77
    0x1e04410b905a1050f50078000010b0000d03c0801c840000190152509501c40005400d0501c0c01d0f0320002442c0d050101c40103114002c0d0004040f204214048042c03e50b01d14204031007003049030a565408084020100d800e200c450340c1d4884e44850440344e0000b43c084c4010500d20024419000e410608060280303040100010f00c02c481808181c1003207040c0007003020548075078049034140710740c0d508540c1141002c200b54801081560050443d0700c080e2a00141d030076111121541941d005171100e00440d4400e0311000c2c111000700f0300c00640c40302c2100080c101f047c60018080c0c1803040394030485102e40d0000c000a030144240014001942480c0c03801d482d960b1808560203200e400c000d6900303134002403041c0c40308030004410b00e0300048400e800074000d0840528044107081c440c80c1d00c0740d0a06814203444c40026640c0c882d04011401070a40c2c0101584070300d06508014200e09565000000719030002c0d0030300c49245240d10441c1c4298028854641e625075540c2003030b0100d900750706032030820707446100700f0041 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 42984509 1250 42983259 42983261
    0x621020c24160203030403050c0a06110d0c09030507031205190207030c080d0905040506040b03010905010603020f060403080a050901030204030f03080601020f0f19050f070e0f0604061203120b060d 86
    0x1e190310101c600024540703900710704088400c4101c1050b809070748104003240206c0d0084d4050800c80f20803004560380c10035507595030010f980b03050855062050b000b04034095506c1c0140201d800c130500c5417415000b210b140d511084c0d5107106911016054004801d08090b00a200b9400c03100609450001c2c0c040150000600a556860314403080e00c64503009500403510b043e01082044050351a44e4454840c1800c3c40b0801c002458007030310590f031056030b4620800c4203440030f0081c03d408500503000014061325500600080400705d0b50b031544180c0b401c001c02d0000407001801c1d500e43c020b032844c1c803a03100c40b1a02d006034000d2145400151041d104480200708069011403214800d11003a403c0d5110000100fa80c0c030ba49401590400304582c110094203041030308140d0481020500403000c907129600c0d070055060901406400005440c1111001c00c0780d405c001548403904030b00169020441d142c6401d40720326920121250040c200b11448a151030b4105507600300740507800005012640d9060b0070b0515070 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 42985616 1107 42984509 42984553
    0xc040507110f0c0a05030a0206070b0709030803040b06040e06130f060f05010e012108030f19020c03090103150e0402010c0311060c04090b0a0621020c 66
    0x380080c442009003842c2199500080d0801990120901094007a2a00164020b500948a1000589170401100c070303c0c0303030403820b080c616894090b022a00c85507103038000381943d01c0100502c01840121842140903483c211000c210201000300d120f501c41008541c04029000d01c42240c03000725030f0103818240e4039441040002106a00400c0100071161b0a81065a26071074010050000c0302250b10311701e11200c03500006068114641d0b07140c14507440000d1010303402450700000300c0c0c901c00030b5807140382c4000c901c450150b445400c2a00740710342d2500600a09800070b070504038010029001400303520284c68205005418950f40c503001503c2c04104201c0c11410417140b030b0140075415000b405407901810100d1003c640d9903203030021070800e58021880c01441000b080c1e0041114039000403c41459200c0100401810503c11084100a0040d200014420b009401180580c58203084c02c0d9 = true := by decide +kernel

theorem cover : BRFrame.Cov 42805759 42985616 := by
  have h0 := BRFrame.cov_init 42805759
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42805759 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 42805759 ≤ n) (h2 : n < 42985616) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
