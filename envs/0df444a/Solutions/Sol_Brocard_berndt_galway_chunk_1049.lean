-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1049
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:00:18.988992+00:00
-- url     : https://prove2.me/submissions/2b0fff8f-a64b-429a-8f85-883bfad81a76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 188489208 ≤ n < 188669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 188490458 1250 188489208 188489227
    0xf0e03070609140303040308040b010905010803160c0f060c0c0e10060305191b03050a0c09032003010204030812061f03020331051002040303090b030c040918030206130206 75
    0x10222020300303d40580c08800309016400741800694411402900e440c0e0b00c91801e40741001e405203058009615640c900401070007282c0000003a114540b210711030344820044541404c4407482d0182c2d00c24500f0400e40040820b03a0f41d4400c12031001c1da442100e010b0052501e95400083d582005c0326140d10320b01d00385004115851081e0070550f0000d00c9440348001d051251340710b02c0203858045901e0800c3e202c040d99480c0c2c0041c3d02d171040c10703441241e078001040b211040d00001485500f0b00d100181014404200301400c16000402031640c0340b0004000f1582c840e540e1500b0001d035003024074010280212040085e00509041c032030f07154041c40000c040160850200001c0d4025040501412003000b9180c00c50303400c10840d8042d000a00e051100781c1c3c0c0d221412403904a15004040c0f140f01140c1d8010b0104000003508080702c00c00b41c0f40b45003141030b283d03982e6000041d0107000702e40c404401141002020a9145200540d240e4601e01a81c00d4440d542e40d00911680810040c1c3c070002c0d040781d0108001d810 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 188491708 1250 188490458 188490461
    0x20c0603070903020616051605030d050a02030408011a120708072303150a060f081926040608010b030f16020f0a08040e100f0e070c02060d0c030f0e030706 68
    0xa201c14a070500c1c404082d20307134001c12031941210103680901c0e42a0002d040138440100702c00281106001405224641000c0102c3d0311441d1050141341400390218100140da40244142e81c0079141480081058840b079404007a4a40310803540140504040300e1402d00742d0501141907401d84200d440108000c038503090710311500c1c1c42803080a5208210f1031020480e40d0380c0c284a582603016a4060b142c07002d080000c410703c12503036a0f500003103100c850010200004031011400c441c4525401d100c008040c827150a1008482c040d030100741c0340310000402e80749004d142103005801916159541c80305030742e0b01e420110700144000d881e020040a00803002403180358884400d401800fa45105035004032b814410070f07034901054494100c45150000c281481030303016800803a98001c140034800c4c00803070300d0204045100210b90141c0d2014100c0600001c22090007401c80090f01e66024001c0c1e0795410b2650101d000402e840d000090000c1e0074104140358900b141d004513242118a20701541c235040803542c4120 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 188492958 1250 188491708 188491711
    0x203121302040e060105150403021302030705040305120309070f0e0a0f02040503160305100b011407020d080403030f02070609150804060f020705060a05060301050411100e0a090c1101020a020c0603 86
    0x103000410040ea41401a111400388a0103440e0701c4000b4441e55042000301714000510b800440f1a000c0c0510003000507a0352414800d0100c100e03442e0050f03480c1c403005c104481c54400c94002070400d10401348554403030552800190b209801e80745c1034510141d00d41a0052045107103102d01d13403403032941e00e02188502800354440c41190103850f070014a403540c0d5001003400d10500c03403103400d10640300403010810322000784403800e4900d1503080c0800104100b10006045899100c1080a520b28040b0748201151940e00d00e009600d45c000080700e407a56581c1c130303004024610b01d404c5403006009a000004072035014105e40401c0d0b416055000072002e40f10b001c12220044000c0081d070f046074903601680310f060118401407888030f0180300a00036a01d0002c10200070b8420240c0030034006d03031415003048089114221103500b070040854001040501b818030461b9201412a8059400300700c002000900080d10350003006511043d490382c0c1d00c0070390140040c908074029403900e031015801003000304486140450066 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 188494208 1250 188492958 188492971
    0x231b060a3f090302010608010504032c03060103080d0c18060f23040e07051206041e110306040b030307020a030b130804030305130e1902030c0909090c0906010f020312 73
    0x401c4001903003882070072001c00c80c0c40e499032441d511070094050507828050000a481000000d002608059500070079201c1003031a404045110404810882c038410f160300d02c42658018200c1341d642d612414040c90a6105403e01c42c01103140c10150182e140c054018040254880701c01d1004551424109407000103603441d0039810402070641001c40c048104503d50010407442c40103580b101e013411000030084002030040e205011042c414143d1114845a02d2030b48480156000324103201c0501c101d005081800b00d241100c2c0342800010300d0013012138400381d4403a13082150140104003054040c19128450003402a4101b03014a6050010400c55410f0b9074010903452041d60f190440c940380d404090f040394100310700050300000c180c55a510000c240d18040c11109011502c142005840d03051401702c200c600c00d55064000c03000818115030700d400c0c1c070000342016103d07120381c1c0703803141d41141c40d40f206440d464400c603400d001103562948a0400202009a25001503241ca0070040310f078044644000c000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 188495458 1250 188494208 188494277
    0xf060d020f060a03020c0613120908060a0c0c0609110913050a080918010312090509070c02300102030f0106051c0e030f0f0306091807090504231b060a 66
    0x382144c01b900300105841102642c5528882100520b01440310703110300400b480070042e20404c01e100c203117004600c19805c640030f04030020300240109002e80c0c0c0c06038201c1c000340015150110b503109002d075082c07240111394070490f444a400d648208100100000070300c0040c025600c00c000d00c00001d0403401c02494107040c002c00144608009081e400d07142c0500360404c0340d4100100c0c8070b102c1b410b604a9150300180004451075011840c1c51140100b80c0c003100c440c0a80b0843c042c444846a0a13280e4a071201c13200b400300d080c0c81242611441940c003035072081c0c41e0100b804644c000002030b420f01c60000d5940150100000080d4001515807280240c00c00540c3d20b541c50004100a4001048090090030401040300301142c4a1078400200414000c005040d849100c86038824120140404178903201601c2c000c50001a00c0e41711418104042540c0020079215141d403a01ca07503102d103070000745441c14079410401e918441c1c8440c10600425025a4000c50081150790b05502c0004445200c402d91000b440340c0e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 188496708 1250 188495458 188495467
    0x20f0408060103080706050609010302150d060e0106050a08150d170d020304030309050d0c0503191b05280c0314010209040603120f0207240903080307080f060d020f060a0302 76
    0x5241c100756080c0d10440d2001000981c40c000c000c410b001e07165206d03204030741c49807142d895034022400100780388110004001c4005140c00a070801a440440a00300c50070340c400f0750b5a15110050800d5015140384400700704081e00061400750400d025035078402c0c005d80940300301c40c02c0756282d400d078009001c1c41003490380d8240701c050b2216206101440c4940d009607404514151541040c40c1000c0405850b10100900c8026030f501045000084916104000c1c0f4604042003001c8002c6030070720899141c1c854203088001d02c4dc02030080000703207981d4000213001d1118190b030480402d0b2040c3c0501081c020118120401c042003c03425101d02c08400641c407074005860440071000140445d00590030440c1c2c240c03031828400600b140d10840032419101c8500003015072501306415481084c00d007480307071140121074011003081d03148945800360080d94080c4509483c6e05040c00050020141103038003582d0b07280c3d080006075092a080325450340030fa07005030101c54143c888170240304c02680410312840c2810780030030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 188497958 1250 188496708 188496719
    0x10f0e3d09030c120c140d0c08090307050a0806070f051e070602070b0f07081320030304050316080c0109050d0204090204020c070306021b03031012150e01090201031518020f04 77
    0x5424400341c2050342c44001070806880d00e15907101e5001b2901c02103034401e409280700f841e00280340039205900801c4c099140c0701007800192800c28950421600211160000a0540380004003903001e0612a04c07140340d40000b041c0c044409021b4103250003a8510195940300b8480440c0300109040c90007500c0151401d105516444400001078410080c1d050508082104030f03030b8001d07030641d00400d040007410406a65900d401232205a44100c0400b04030190f440314019990030400c85004240150982d00c5000c9102c960f001c4140c000d10a246cac65010303001300d001066104200e64800c0c1c804c000e00100c02c2882d80d130244401800441ca003260455820404000b00741000c2040400840c89404050f80d601c40c030720302024048850603400361584d40b00303205016015042c03051980940e6021040c10340c5110380d6041c111002d03514000341c292071740e10b411107021102c4019000554418002c1c1c80501030131030000e410582c030701c0c03da120300b07012843c850741e0388980c034140c035002080041511969141095103c1c0c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 188499208 1250 188497958 188497973
    0x80709090903110c0a12063c110301030b0f070c02040608160f1a030406090206070f1b180b010203070b100e090109030903030e0102010f0e3d09030c 65
    0x42040e0302044144001c582000c03c03c0000c409203107002d507000f155091519680c0d900c0c82c00c01d07810003040a80c450b06500c9180c42080c91903074940d07440e01e500711010440805000301390b00c1168061010142800750040c500004901200e049941c40707211400c040d84c030b802d41d8131640c0b440500705000300400803c0c0e03a030150703840b409980040c0040c05c024046200ca9080c5c040b02d5a034079076001c3e10101218070020400784214040080c0f045a50005031f954035901d92070104c0090140040003540240045410420700412080310680790344184040c0000581000451039528014440c14541707204808951511042d950050010800107004690600343d04d0b07600d545203c00300b101e00b0b0f0842ca08142c0108a04c51036603c3c0d1642214500b0003c100158a41e20010400380e014000034040c0b101018809249174401d40c03200c0c841c0680c1d4981000304090200900c2c0e20703001200c80c2445041251f007100880007407a400407541820108108442103445984414085c0a514a003501400641916000403442d003 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 188500458 1250 188499208 188499221
    0x110603091609020a110a050a030305070207091401050f120604020f03070302040504061a100507080a120507021e0f0a0b0604020f0c0102040911030903070f051c0509040c020d050a08070909 82
    0x950b0090703143c10700c00340000c001051900030411700340e00502034407001c6840400c1003070110750035140200e0a50794801c0240d2403d40701b076211501c0035280c482081c41c400800707405503058540884440344c0900748070042100c01000300450b8400d540091004c540145071440315400070f00b1014040d41d1400c2c4c0d680d000541118001c80b020b895940e121364026034203071031131543c00c1116241110884070110700c08100402501407000b00500440000030f210800c24005d4842c2c01c07000d51404413702c118074003640000d4a84100302a003515040440c45a032140c4030340441c405183c40c0810004000b0489591504040c250002e003c07103400950030400154010b008000800004201d000003595840c0744c081d161085440d02c42941201510a01c03d109006030044222100c00ea000305007103001c0051800c0030303402c04003d800020700c181000e102070380b407103a0010003400c4a10021202003104441d4980142e880f0310050000d00300045041041c1d25009008a61058205220b0320300b01c09001d44407552101110107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 188501708 1250 188500458 188500469
    0x1633091a040e061215070c1203020d06090203011d13050715110a1e140d030b01090b0307090512010b04060311090702070608070c081317060109091106030916 69
    0xc00160034016500e4819225401000565500e81440d44102d2555200c0141030034031040c842c1c5003004200100d214007440800c040d00600880c845040301e40c0c2c00342c000d50000100803515810000005040300043c42a00d0403508001c400c20000e50b0141c62510f48140e004101c40c0c2e450303c40da01e101e8013007542080110080d006021040c4241c003003261000e020020301c0324500407294031001c1700c14000760314030031500b41011081400c00000450b5242c52101030f000320340d125429200c0c0300c05419070035070306801803050300c402030b05c4450b880d80c0c4035000b00b14a4031003121600302007004d60030100501e080c00351070200e43c003505400010700120300d031000405850b2542c0c010354012a21301c0c18142c26203042e043d115089101d0f40020100c0b503203802806000c24000410400901c100402d0401c14445900219012084c25110302203480b81c90380c4050440d070611a4603000c052013210300200340d04216205400d8400c0d00440906406a110020003a0b50f07480141082801d0003214408035034181800381b050040c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 188502958 1250 188501708 188501759
    0xf050f0103060b0301030b1909030912050f0f011e060326160b04140a021011100203090d020f06040b130204180b0403081e13111002163309 61
    0x424140d8043c100c408c0e05a10b00d422440e12601d02c00098200e66400119402400b20100c0303581c403070520f0307410500300c010502403034010031009101e24207044d444039418a0703500910745007910001a500040b100b803404000d12461904144a1030010302c81001c81a000b0401d00c0c040c070300320900601203c00215180704841e400c501c8018081080081110705c40b502104a00900b60301c10540c0000b81c00110080100090152001e1f0442c8410810b01c441001220b407404159500e0818007003031940d40e00305019442c0107000d805600380b0003100c0400d00502694014400030303103c0d141c0340124a20702c10524012a8026640e070340780b44003c4201c500341c0f01058001c400698491519050140403058000c0c5a000f9020311043c2c0020140420482140c0040b00001d45000342c003c41d1815820724140d40c00d141e0380c844400d20320070405990004511000d40310041a00a480d0b0762035074060070403180041081c2c1e0618070b400451620f2480362180c81041c10301403a100c00307031658803900b03081c0c00d69904e80344a4880 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 188504208 1250 188502958 188502961
    0x90102090a090b0a05090c07150b030d0207080706090b1e0403020901180b0f01091a09090c07060c050a0801050105092814030d020c090a0e03030a060801050601090f050f0103060b0301030b 82
    0x510f07205155100071310060720030303a1b003619003104040d000e882900c0c1d005003c0c201c0c00c030400320001e036668480192132a02400320303003286000f0000655182200d00c11541640f048071004a000c40c8100b000c0c0c411a10710641c21400c290811083c50030001c4010560a0b2103201131000101590790100028000d00c440f0840e07040c2c00f0901c00b45c030b109a4026110305401100301904c0811940d901200f0300048846500e182e1000c08500707402169544540400903074030181c0b0400f407043d1002240c0c0100f036818030802d4200440003003a5810355440c00b81e116440042130584004202550084005001c030b9031009001c8420450b801d4041440c281051903c0d515400749513005001481d820840300c541c0740f0302180100445100c03800025a01e0992080107400f44c00300b200498105149500b01c0c00c3d0b0141a038054944034501018081e00504c03440c440d5009542c02c2402281440d400703141c001c03041d40c030410240d086590910040c00385055100e1915410140d40d071000140b45003600028501840c0303c1c00ba08a5a03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 188505458 1250 188504208 188504231
    0x90405012d0501050a0c06060503120a020d03200304150e10060b04080303040609051501030303050f0708070c0201030c09120609020a051903020d020402040503031b0601080c090f090102090a09 84
    0x20301035040a2a07600300c03030000600540ea048010303540705201ea07150690301040b840c504039000d07103525400642c0610aa80078200341c2da0740d0f0005015010200d90880d20280c0e11a007003201a100501e001080c880d00c1004400d0714aa52013004640c8a80200602e02c48a81c10103452011100b59054801c07070307500000305d5170003918814020100100740a595132800c007410051265100e20001e00001c00e11039660b40800304010b010300c0703500d20b4005000205c1d1441d60b5039003400381c05031404035603040c07407400b940300007401150255111a000d103440d41c0c2e070351002c500c59038015402010f00c404284107100800070f0006012101c41900d2442510400010844d400705106012080d006504202d01c50341a05081d07084c42d90b8001e0101046a40481d200030031803c05001050080c401e40e080150503000001ea003070440c5e8900e0100b8540940602d0480b401aa079504001e91944083e17110035510401900108092001e1010066002010000010714000319100007650750b175240d502014400f40c0700c00d040f000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 188506708 1250 188505458 188505509
    0x6040e0307061b05120105040506010e030d052203080711030c150c01110c1b010311030f1806090d0503041109090604060c0206271234080405011409040501 68
    0x4400c107040c01d1960403c1d88020380e00710243d805000707d0b409070341d54000081707107070380703e040200c4c8400300103416a81b40030700e9230700000c0c400e50011078940260307240384002c496049202040c02c001c4a41124070710b030900001d651503170050444000020b070b01d44152805203006136101401d2074429654079131810343d20302c84000001c1c02c5d10700003c00051883e400303009d01c440700140460007010440740c068100300c4a182460050b0004c10042070b2841c000b20000c01001380766041c000c1d02030b000d01a41180d0960b6071941404155903a0000c40e04007440d604490400030003280a5030103160001c2c407036900081011450800302d4181c00d0211000381d000d0f070001050100b80442031280c40e410600d10300c042c103224075004004680034805500078400500044c4800d060041003840a2208000c0070784008d6581c1c8903040c14440341c14115001160710060040725441c000f02c108044600c5203030300c00542420607103048010358082d44440400e0718110343c2000036200307a64451060700c2c060000701c0c0000f9444c0c40c01000d80031 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 188507958 1250 188506708 188506751
    0xb040b0306010602121c15051c020f0f0301060312020307031701030f03050307020f010504080418140a020903070b03090105101202090a0e0a050a05030a081b040b0306040e030706 78
    0x502076046140103100d1542d01054418011503545803071540c0704a44010004683c10f18884d0365002407070140c980c4034101d5100500c400701c4100b2500c0506402c40c100300307803401941c0040b000f540325500c0401c03214982090681c2010304a001800003071030540c0d80e241c00d0144074440041e4401604006418070800d070300b100b0701c41c401c8501090340314055030650342c4404052000d0b05000e8180b08001c00003c403581c2c0700300501d040312503107a4000c1c4014245458107000344c0d00580030b0910250f40d8000d40403940071040c440c03e01b20504003c640340481e1500e01e600780081d4070a0708015094040c1e00700104001a41d10000c50044249000000d03451800c0c00380031041440c45c0c0c00c20810049001c0940780565209056550040303804d2a000400b1001c1301c0074145000320b6a0306c001c4c40c0f400f03103503007480c28800040090801c514490300c4640341a9204408000058030391038003032001610034030051000c204540060341d0700107001340001a04d07034849000186180c01c040c001319031060b11070481c501102d821944c0070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 188509208 1250 188507958 188507981
    0x60f181204120215030c0a0c231c050f09040c02150f01030219050f1e100504030b0603010b060a0e0409140615030c01020d0c0c03080f0c010506030d0c02010e0a0503010c030b04 77
    0x105e0850a00ca28040b07082e100d0785003084200f1100b0010801481000480c915400c81c8081540d54042c1034036030340c2a12244d51041c58603a0074512500c40400754051000c035040b182d610031400d813800441c20100310061004801490452150041800081503da0384850081c04042d00c0350690758034500c100214034840d0100316505002c202c5080140f602d50000d1004100d104440e18079110300700015151801504524156018541c0e1050340040c07600040100300780e07030140700c905002c1d6031003c09260a0300c00c10103007a0740203201000340c3d0340d8181c0b05081e00000e84000030808554280142c440c7e0039110a04800c2ca032498002c1c0b014001a906c0c0c030700d60f8080c008415005041500308850000c0c0d03c9606130a641c0c018402c0e000c2040702003101c00385503507020b07540c40700e1342980340c0c0c02140203aa425004041c3e6070160b0741c42c007400b1800340d141c0042d542030342121a41e924805c0b81002d40c01120000343c96101c4a400c0f80e104c4002280c83e5400703004138580700643e80d07400901c10000341c0400040d584203c044 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 188510458 1250 188509208 188509249
    0x10f06090f03030503040213050705071e11100302120103150f0c0801150306030f060e0601060203120a0f29190302091b0706051e0702060f1812041202 66
    0x402042a00c03406840071283c0600300141c0740d6030f0b24004585110324481d2003030409071a0800300702849420002401e41d060145e42026001080013608901320540a04042d01c203494440440d283c130b241021450409100c949005070030b00207440c01d90f000e03821080e0001c036000c2d0380440c603c1c01244142c0c031a2072184d0601440c240301003620005c010b46801d0040c0a40c40190b00b507004204802800f030f82000c001594800c0689032500d0a0303003000d80003031028144581c0a401a01c2c0000768003071000080d1504041c4204d0401402e8558142d840003c0036a2402c0c0e0305c1c80340d11a8002c1d81d001d40c1130614500001d03041007101d03071503001f114200040715a03071950b902c030035004a44007400541c03541416694000d0300b00c507011480c2048040464028042e500008010900b080c003084050740d40314041410070403880500d61302300e4039070070402d0f610ba0300c0898085c00710301541000207044121070310001d200b5111010581d03100303110070000e0004c0c50348036400003a02190545240401c60a000389e03580455000f4280c0d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 188511708 1250 188510458 188510477
    0x90303030c1b110411030406020c0601050625020d0b070801180c0518040902060c01020405090615192318040b0303030f0c09210c0303130509130515010f06 68
    0x80820810304038840c05889001c4500c1104415144c3c0e80c0050500340f403030500c154603450302d49040d00180d8018010143e00b40900c100018160905100382d07603d21120403d184550310726400b4800380b801da4100f09a0f8494600c81c1940045584055464041d00013a9100301c410341c1801c4820300009801c6021104007072401c0ca0306071140e0b50007405c1d03404550804014061244a100015000c0c0c05071580c06544102e000a0011046070305600134422298281c0741041b041c1c2d141010010b41c0c1840c8642803081c05c00401c114071081e00100c406200d01151030819003040703040350550441031005211200b5072048000b8840040a0310b910101c040d204089405122407507050011a03264000500f0105544070503401156008181d20241c407039078040a132900f1021030146050f502d030749a0001c00c00800340910780301d19260f41004011039240007071401f41202ca007841c02d0203200c0360034001000702c588548060100400103009005a45a401c1481900c200a50601021a002c80b2403640040240102c002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 188512958 1250 188511708 188511737
    0x203070b0609010612110903010e0a1202060705070f03110f100b0f0a150309060c030b1017161803050109020325060503070e03161415071202030d0c090303030c 70
    0x1c02c2c0300c001c85515000481c0841058210942500031f0680d215459400c040b0a05020b120010320030070801c1c007503600320040660b0300c20180c0e101d030301c180c0d81700001036010820310010030340d0314041c429007034417a01d001c9a100e144008074906182503000708494580200c40303c1004001c2038040c11106c00c4040b1555030030040d40da4000b1710600003510034564000050003a120005000ba4420220683c1101c8103121031030180c080100100345110101d4850401c002280003518031500300c2501c6110300490241050302e608600311214900389000b48100590074094440b1400440306290045200c0c0002160101c214030415007080145400c0b203180c040e690329084005800002100c049070200d08080b41d80351210481190101c403080010398051181c80c0d0000380da1648a00c0c60801c4403160344945400e41507400401400f044000c00c41170540c80103008450210f8030903461110612100d0045038944140b130441d40b802d6030f4042c68a900821511041002419018090b01414100c10700e000c408446251 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 188514208 1250 188512958 188512967
    0x81b090403030c140403050601060807020606030a08160609050303042117070c0b1008070803120114010e0a06050304030212071a0a061a03060a0608010305070608040f0b01060203070b06090106 84
    0xc1000d4205600c0380022503206004581410500041c006041d0741d6540340c0c02c00315901c070070a100700c100044103c000100e03018404100b00340240c10040280003061300b5519603a10316084074403c901404c00004540f0001195445060201885a005182c4902e0a030a103003480c3c004500040c2c0e40c520342a2001c0001d103034090003100442c44102080300030f0307813181d2404407a141c0c24800e0080078456080184100c01280188a1088a0106040b2103803140c0707451001da260302a071003e0514903c00d40380144070300b03562860340c10342d50030061500c80d1181c00203000052842005074441804280c001092005065043c050081250b0100f4010340c80c040d055941d8103000c03d181c425012500203000086003e10420303130132004c02071422a03440d031a2002e24206080300c642c8103580182c0720704040c8074000350322805052014100c94010700a084a05e00c0d00c40e003030f00c0394030b4004c000f102d4903880c000c01ca000050540b50418041c0200341d00440d00c1f14018901100054000340078240704036240e10040190b2a0f20 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 188515458 1250 188514208 188514211
    0xf0d15150804060c0c0b0703050414070521010b030102121b130b030a29030f0d08010b0a0507020a03060f0e060907140a0302040603141c0807030e030d0f0204081b09 72
    0xc81c0018084810003049a00017040d031801880c2c072808a0170703c00d100360b040d04900d01443c0645000b101e0002058402c0381d0f00c99243c4200b641002807280700c04c4500b4100c40b0740c5a091101c4100202d40708100310300007800c990046254407449000300e000e101000c100c0004400c581004076501514101c241d52800c041c001903841411014080000040c40803101504488581001a020000c00d41d180c2e00341c0010b0b00359200c032020f00074807504c03c90000d61080040d8801610340d4585440f0715603424411700c6625503200d03455102c24004204604030050300c4201c0410011401942c000401c010f00107080c0c025a00d000741408050360041c2c0501404550100b240421100400ca00f090303001008008241070410691010f0741c090b140c5500002802051145070380f6003609a07003580ca00001c940f41d520f1104100001c001c000640c0000000d11050082d4000c1c403441c41220304403400c1904406402090b60f0310490003224054000c074003086000003c00c01d44d00445101a00052440310b0705000c41d040010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 188516708 1250 188515458 188515463
    0x20d0503192613020a03140c04020f1909270e0a12050a0903080c0f0609070f050d0c09050702100b0111031c02041502010902010e010f0507060e030f0d15150804 70
    0x1040e50100c0c01801c4510040d040f100c0c2e010b89100c920f0b9981e81081c400041210f0408070040c05124a80d0074940303458800c40d000022480071481c20504410a9001c5946800043d00d0910602d4031010410f91211a2051416040304c54004c01c00d1690301d05110990f02516a9081558000c500000002d220a641c0305400b041e20b00c0c11588914400c4000c80300c41c0c880380e0015007101e80004614480d000d0101d404081500c2c1c460844130300b5150071400340d5440c10140700d07000c04c2c4461100240b04502e0030380070051006001c0c035298402c060320780c2050342c2110420b070341110259014400340f4184c1d01d038078015080c21f02d43c242801d82c940c2c0701301403101d0303228031031a0782802290103541010019040503605607000383c43c0c2c4441c0d45415410840b0080d00030320b400c039001e0b07020908540e12400b0300c0d813041e15001040511581d0359400c100107680e58001030326040901c18550f000c180b04402d482034601002d440c40788010b040c081211860205905a50940ca41056500154030501a160603030008481c581050703 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 188517958 1250 188516708 188516777
    0x9041103240f13060305070f08060415110301080c010e0a060e040b030106030b0c0322020a18061e1a1603050c0f01021b060a0501060813030309020d050319 68
    0x101c0c900016a84200707858000c1c2e000d10032403000301e29109568007078400d4912a90486010300c1d00e440014120b861144035000a6510000000c0c001629407429111400b64010000c1080c3c01442c28489145e00241c02c0b621280d8004445d240341c0e90717800443c1070150f60050f41c60420490804400424841000042d0741c040c1c0c1d2103040c03513000d584096220b00000c42d0012200030313450030208004050b952003a50004c1d0004000c0603101c122600d00c1d40581310150780140304c0d1001d10b01d018841d201e404c11900c0c0b03014281c3e565400014070900401d0342050b842199400f6220034908026400905050490f1106404002841881b05d110300700d41481101640600702171f6250744510260610f40722008456142030350021407489001403a42c0c24504500101005a5a040d6500c00054003103602c02d03c20100080c44041c04030762801c04054105041900910300425031a8194004c10034860980c40200c800f6407002450303140c010250a1841c04000181c5002410071140d40f100300703011480200700e078075010f = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 188519208 1250 188517958 188518021
    0x614060a060309033f0b0105190c05061501030c03060f0e04050f0f071508060d03050c01020702030109110f1f0302250c0e0c12131109040809041103 65
    0x1401782034038414000c0a50502003041c8101072440c42c4000c0602e20300200c00e0045111082484440d009208503c82c0c10703550700d42003030054510003000c05203c0d9195010312111080003008103d042c80054811640d00f105001102c8120000504075010b030710003c82010b03d04802803003001b1500204004540e4151880101074542e030400d41d05051855081c041070f841400c62100d540c01c00450342400310317542c602c0500d030310990b014030580300a0404c1703a8450b40012044001030001e4020b101410189d8102000141030908503400701707003140c00b56501525100082000c10200e450440d00744001804295040190344070880d0107080c40d00491960303130782419004900d900c62008005050104a4201000d50010140b9420882d00e5003800d03001e02004101d05000295104000e001122007a104031401c0c11600c0d0788038461810b40034003100c021180c41c00c58180002d0103954600c1d149006070701071008d0036038032855107041008460000c0644140c0420600c100b251511250740210301421800c41d580b40d21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 188520458 1250 188519208 188519213
    0x2060c16050a180506010521010f120b070c03121a040e010606020d0e031629030108071a0d0606090806060907050304060b03010603050d02031201050a05030309060f070209130614060a060309 83
    0x450180c0500300d211441507a540965100c01c48d44a24107d40200000010143e10382030956a00440307458050010a00c0001051446100f4443c1442e0b1074064640422244018400981a502d01d4000c15960325411450b2083d1494103200d4010103412100080000340d140c145c2c0170f911154184001e5050110048414010351170902ca001252090704e802c0d2010300e919518804426041031401191040248250501803a0148100c9041e2920701c8020425240b4280c2c1e0404280e581080c890600e80041c01008880382d90790042c0310280440b0740b54444000c0c1042c1a040c0f51000041c0218460017122003031046040e00101141d07001a0070003004200d56032580c005c20701500056200425038889c507900b100b005507020008c1c100e105d904003080c0003141d985d0300c00c120002c103060160560603001081203807858540400240301d210700c2d2208942c2000d0190f000070f0502d40b011161080305d4500044440d0411000b40310327500c01c00c03d28000e469207a0401201003000c006e0103003c0c190a141e542c0e00e42c40d05 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 188521708 1250 188520458 188520467
    0x180207050a0b10050307030f060b040e190623160e010801050f061b0102091009080309091b0309030409050f040c150507080c0309041103010303050307120902060c16050a18050601 78
    0x20b05130103000c40c1c0c01641d0782c1c03800000a5000c0002981d03400d02c1e02c03090342c0c0e462070107020340304106407244018070844a0a88030958101b41c11141120b1950f0f95280910301303841013616110289208486420180c50b09051451031041080050801c03c402c501608a5a81c0c000503020305490007030fa055404116004013098040c8298110310706107000f541d40d9041c2500b0150010141c0c0401582d07040008130041d0740c10786a240ba58001c40c0403640050040030950300346840303010790081606104802404145070906060351007550052030381c0d080020309202150960048582184401c89100c0f07180c6080d803a0b80c0101c403243c2c041c10000d4424440310498152190041e191101e81050038035a0b259412a3340643c1d90780000045802942448500c10020a5a00035a13048076015100c030f42c9159100b04044034400f00356800710303901c0342e61140d0142c050784884025181414042c40146090340d56070300a030012647e07550110344542841d5106000303030040d4074904a10007504201c0490720ba2200d00060340c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 188522958 1250 188521708 188521741
    0x10804080f09120327040e0a06090813080f1b0306070f03021e0405100306030203030712140406021005010b031303050c031e03040b0108030a080103120c12030204180207050a0b 77
    0x3d0103100101d100f51021080e8058801e010079140d945041c81c100c1a4284415118128000907698101350381103c042119a005544042c1c4180d1019103030003030b00710000300da469864200705089c0c0e06c00314070380d940140f040081d840410030001419400c5403804000a5607024010f1105007002014480360101da03020390142d51702c940700aa03060b0489030b00c2801003803164003d40308845c031441c160f809000401d4001d20030642070702d4001e400746140030040d8660444034280b2004440410981c0b08a00060604007000341024040342e5000e4800131010100c18001d58006030002000b03081d08105010202c43d0034000080d4550303050404c00d85031a0f0015125007507000d5840c10b91a80c218040c0c44541300c0804074003c603c0303240b00d0b18000203180d1b20b842c0126507d004001c10343c0e011820400044c40071502c2c0300d02c1200f650060307140007811108075175103e400d000c40d01c0c1060341c003103a00030909022000c4c10034010108014072140441c2851516180c6956403c4140000781403103018501003040310b00351000d0b00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 188524208 1250 188522958 188522989
    0xa0207030b010b09040f02070803011e0302040f0203060316150f020c04150612061406070807150c0906170c220e10090e0607030b011b060b010e010804080f09 69
    0x1016250307910040c15801d541300c00341041c0302d41c1c542030404076001000d2080e200390700d03000360425056a08144500164000040500e0230759000e0b1000000140d07a070303000307441401d0001d54001d6140e0070300c47e060603c0c0242016040c61a0324603a4070a00c030340b503941030650b00c00b0100781c64101210080f602c010790502c1c01140350a50000d0501d04481c00c5040d01c08000412114180d480d4035110b20b240c2e074000100c910364050846111495120314140d440c1c080c0251000d540244e0803070740742107007580e40d10142e20b2200c0313406820b0580755501a50030310f82204810300200540d003014100d4040c1451b07003d0981c0e100515505c0e1400001c50800f064030b0318600c030302c600c0403039240f00e046619485003815105400c0440714150b01c1052208041072400c001c0c000c804604800d8001013106841c1c0d0402a800f074800154414100200800402c07005203044a03c1c3d100203002d004005071100446000500d0303d00309843e42414048046c0c14000096440d10407190401081e0452946a42124000238005c00804048 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 188525458 1250 188524208 188524223
    0x318200607022e17240d0c18060513020c15010f08010609020408030a120f09081c0e0327060403051501050415030201030b0406030204020a020303071b0f02060a020703 73
    0xa61403803450781c03000f09216070401e080c0d0b10900c0e901c4441c00c4400094a0301080440182d03840401c0c3c0303008050301c082511180700c0d5100044081c1440204010140c141026610300044202c10043d9401e034128a4441c161161070506c051418080031a450171110382c16686459400203228040100a001d04038141402d04101d4560b540d40300e1030010180e1590180710300c0c81d440c01100161141703051003102d0440e40a03502450030143d02e80002c1c1c5490f060000102c540d952118040020041a44210244280715801440c3c8481220b40e941020141c00d40040c0074031840c00d0419044503400005640402410324110361448152003408004002c0000405421917404107000c000c1040c0440c03811480c031403241c9070400070780c2e0707910822041e100e01c0c140201240007e2901840903510940102111600140c4040f070140c0d0b40b0341c045012030784222060b400681000c020b0245150b030100b0340c0e0524202038110301c00d2042c2d09031030742241040003030b4000713115602c0052040761090003402a400115002201c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 188526708 1250 188525458 188525479
    0xb0402131211040e03180103050402100c1104020a11012004031b0e07030509011a1005180307030f0201020d08040c060f03140703150b0309120306030f070b0a031820060702 75
    0x4d070a940340c0001c140c018800b1050b02d82102503500c00d00c1000d10442c0c00928014180c3c85601c41a550310501107416100c01d884a1020301641e20b450000b04808481555800004038030f042101d42124884201148414003510000c549541181c0039241900d40110001002c41100881854544144e50000121701c5c0103000f0030100c10b806034402c074452500c400080c092845241220822100700541030b83c0c1c4080a11400b02c6030700c1c03003a0701505150303014040b025a0140f640c00000c0c5403100c40e600407154603c07211017020865074144410160f511807030414042e07a042540c2d8860104205008140400403103110040c00b0b1842600702035041130030041d080700607060051006024004000071891a4040d00780005483c002c0c08046900c50400e04014000718440c0c08210050381e48090035072a8140b18043d40d2001c440d0092088a0003400c035508144d903a24100700000d4113039003911402408900c042c04040c0c0100d40182c200c2107241c3c80e81030030510458180c200003169406424000b940110202c81c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 188527958 1250 188526708 188526731
    0xc25080a0309090e030a0c030e0f03100c020d09080307020409030c06140702010605060a0206060405130203073809130612060203041e020102070b1e1603030b040213121104 75
    0x81007641e20000c01804900e8034001c4130b03503581c480c000501d0001441281d48602284c4078051145600c00000d089041d400f10b00c1c1c000a1030010000c08248826a5402621034080e404000c0140415502e003000c0d2841840c0c100503640b42c1c005c021010f8001e5442c3c0842004040c82107860009150b403005007003080b1901c1c0c0c0344c80028007008130b981d9000342d0301e000c00c04203a918260003903a008a89907402018036a072a10284009407602070130320b480ca03205880e40d4400598041c002c00018002d00c0c1c0154111b05150b43d564408482c460020942c02d001c07214078901b03404880811901e41c25400c2d03074941760b0081d10f41413100041c0182d511492000d00405000401c004154000b58081c0e40a190044001c20250800300e10144280c1d000038050383c01000c0c10041c80c850640030707080007402e0b9108198021600856854290f010b40138402403e61001820010103801d40700c0c0c00c28400094501b142458440181c10804103030900940e6000721410520401b00701d40d8022403100000040c00900040c8a0b54 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 188529208 1250 188527958 188527967
    0x201021204030e0a08062a2802071d041101021c120510082109060d0506011b081b100204060804150b0306040b0703020d0501060e0a0b0c25080a03 64
    0x4003d0f1501c222220140001e4101c00028014081d00d0300980074407601e008954000400380c0080c080701c0d40000180451000c50424a102c1e17151040218400000320001030002410079039a600094588003c0b0140d4469030946045c100340d0069002d801a50940d02c0c000c0140c1c980f14034034414295000050b18ad6400c01c60703014166000c0340c501c050b000d0040307842c0c03100c0215102d091802012419403220085142701030b07030110345208541801500c50702c0c059114000c1070301070b131100100f20401600ca0b01440a00d50b0302ca80307441580521086003004c0d07101a0b54500800c0e2041d00501304816264100410700c00c4801d009000e02c04c1c5404500315038030395440c2030150034140c1c201c40645083d4204405040700340428080d51086940040181c101540e031680ca1600c0000054040c5003015401d00c05c1294441043c03003818081e01c0b80c1d0312100001c0c02c0740000c020090380b141c2c01c041e1203040c041c0301060441d600081c00100303107040140404d402107060080007a84150b154030070b590a00c10030701d0240515421 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 188530458 1250 188529208 188529227
    0xd0209180106060903050a0f170d090b06040e060402010e03070b041403010507110304120809030303041401050901090b060d0503070b010909030914060a08040804120b0a05091c030903020102120403 86
    0x1410002d100b070580e94801501c8641080c807010f0002e030400b0f008030780010100858988082e124034000b91184c040d030280260940c001003030b050b01c1e41e0364484455042c41600054164003e0742164140320100001142c95102c2e9409807000b8140140307282041403aa03401e0100740302628200004940395503440c80c104803c94540c0124901035440d003404039041a102d55002003c20b84070034021761030945000c66070a04132400f0a4250b601000901940b038840d079041c4002c50045009402d0307200311012009609085940c080c2c20a90f96a15004018000130181281c40b940488102c9070f0703c02c5a911313810450308512448400400030818400049482c51655100001d460701a6441108842e21003c44100440d050300c0d1032a845941400603001c1240309001c0306600610481c91642001e40d00e0000c2e12050018000465016400008004440415202d03440e0300699050040c50502d924094442d440031203514103504264480c02d020083c5030003501140e01c001c1c0c801c10041e0140c900f904000708003241 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 188531708 1250 188530458 188530501
    0x15010e19080f2506050315030304120303050717131103100e0f0d03060f0b030406060306050c071b0608010b030703060f0f030b0a0b0603060607020a080102040906150206040b060402090d0209 83
    0xc0390303a6210030f0300d40c15010070540d2425261a850340e121800504414010b40462542c148801c00010603401c0020155000f2607100b0340b004102d0b4284804081d000c81480000758140c1e00c204810007a50000030f03100e455219400090301c0315940c0322580840d00341110310012000450a00b00c90001105000034820071521103031041d07410542d4914004c0742600d21034801c05044061104041c000090a03030000c64110303220340d100082c8660f40303940b000c1c00e84004540c0f1034040078001c10084103104e03500203c42e481c43c20341c5485000c0c0380d0074000083c04090040c0030383d6441e15400300005102038000c0c1e0042015102272040c1d0300007240d80f03007105540440940401c075580c500d0b000c0460701d102c0160240d020302d030300020041402c2d81d80d2030013444801d0304403110030390b03002c1c0407250001250703d020720041004c1d0019540105295003810600b1081c1a4403440540455101c03100700004115520751450b000710702200c002d03944440354030010385405120400a580081103e050107180055454411101d01c2c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 188532958 1250 188531708 188531743
    0x303120c130b090d02042f04230612130c030c170f0d050c210a02010b03060108060f060607061b08011a030f0c13090204080615010e19080f 61
    0xc0d12098459201c3c05000c0b1180d070000c00c1284914010310f082e07003101ca4010342c11820061a0407c202e4400d01000c51280c00011113000002c00f8400500148000c6150340c444038880f04002d51000045201c2e132080400d51044190034401042403109040150114581c008104986450f2282081420350000e80b050200600084001c00e510800c0030a00e88146580702c0003426000c00c0408007038501d94403803101d81c1602c0c0191401c030042d440c001d40e104244d0b140800041134982031402000307800c4500300e2166510984c0801d0040100e0040015041d40c00740d498a05000c6039151000131a609008454000700b1060404006900d0300030330703200400d59540a41c2d40c0002907662841015020f440b840c100c0381660000f00000307906101c80c10b0081d9044411858060303e0500c803580d081100c4801604503620007500080e00704442c5004024490f004401c9070541c2c400704686034000b9190b00b0807080c5034ed000c1c2ca0000320100420740604c081c14024580c0d42c06940440f01840807003529a49041d0301101c0c0a13 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 188534208 1250 188532958 188532997
    0xa08030705010b0f04140411010e0406090516110d0318060f02030601030609020f04050411070f05030c010608010b1e18151e010c0b0907030c0b030405150405030a0507020303120c 78
    0x3407174a8001c9035910813030104044229200c54485403a044a00741450781440090502500e81d52201d110300002041e491000044a061110024100c8080799052008104502c003070070120203c041400040019642000191030907212091200851001000340038649060080c010000e0030f034009521480c8240d80c100001a01e0740d403a04100d0051486007405154144001d00075401c180e800b022805001c441d5050401c04160399100303110100c01000c5400da0408908400c400ca024000e080c0508602002840010060000301e0740c00001c00021032503641003008004140c2c0c030744c0000d1182903001d4401001c0140b0340000300340e9410107500d0009001d03100d48080300440341b042d080c84c5807036054143d5511591340d9003512010100400613204811070701a245002000500d2400004000c10304440c5503920b901d01402e00b10308007a046000c41ca40e911441c0300700400240003004070380a900d014101070f91141303010700110f851401942c2408142c2140c890500114190140203000320301444170108804 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 188535458 1250 188534208 188534239
    0x120204031406130c0909020402040f0b040513050915040609060e0f160f030809130204150314060d0206030a1d16060903110607031101050709061409010804110a08030705010b 76
    0x50420343c500605201c0860a00388030b500d03c1034021600030782c0000c10141c103080c0c444100d60513005c1c1580c440e480602c1c001404200d02d06000e9807107030940707040e0107041280345070442c0300075180d9110a6107000200800c00c001401c201c50303503011100c1c15401c1101000702003c02004a60758020180b802c00031403007000a070100045468110400351003503400c5120166246555900c03040d0440017000f82e01100c83c1c1c1007040440c0040c8080c200a01c0ca22100950071941554007500301c03440040c0b41c0d0078140c00b5100f00265501c6070045c9034581681070300c1d50380c0e40e80d48945c2984010541c079042c2144503001a00030305020900014508a5050b61040d0386030720707940c0d0f01c40070b5070405424840213041440000d1070542030b1038500054501c450290030070381c402c4030b82400c00302d084402c2102c440020a4030302d10305201d00d9502109504558488580d4185030a01c1d0b100082e12000d4002c00042481e10a8024201c0c5a1184010b08003f0000941229120742861403c01c0c0a041c2003400e0f2030003140f01c942c51554 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 188536708 1250 188535458 188535481
    0xd0914030a12020c0106080d0503010515031e06270402030f010c0804080a020a0204110712110a02270403021c0305160302090316140f060a020309010f120204031406 72
    0x4021079141c4900c01c44200d400140c80c0a900b2604591815550b190000030300008180446107000f03100d03603241c0f5503e604040c100000d102c01070a591041101c01d000704182c04280c003510b202524554280c41c040d40d40c0d150009a800d55000800c0c407003040780c40341e41c10040500d0481040c0620300c200d060383c4510005c3c00902e0708955542d81071400140820021501282d50340780140035145041c030560340b800003103401140a540160003da980c01c0030010b001c6007400f100f0440820b88000c0340c680300b00d01d4440c900c6016510009444042d10421094120300410b40c030400801c0d401c95500a01194580703440c2c00e0180d10b0325500111855400c91121880b003400d03100748581480382c0003000c0c45c4208600000d000702d0081d003080c0321454041c8242c007421600031290510000040c0038040c0000c002412803028420884905d200e104d010391400d11003a10065004400d91354000820300e050680141411070490340c0242a032580d020305840000c001c001e00079282240c0501070f91040c1105d020340c954510700e62 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 188537958 1250 188536708 188536717
    0x12f0703060e0a050d080a02040b031303110706020d1409040f0e10140a0c02030d05041211061b0a14030a02120108030306030d031d1b030d0c1e02150d091403 69
    0x4c00f2a04090309a1241e540030305030311600078054034001420261100f0501c1c0065205540e10003868401d50304030070070190721050420305403010300d020309501494080c0295981510803003800502c0a40701c0138082c0318580cbe07410388110540091041c41180e280c0024000103084001241109000d10b91800800f0138a5002e00901001c1010091aa41e84c4d4103580310000c00010707150341d00314041000007490300c0075503000721800750b80100da00c4071301004403407405424211400c0c029046038028800f00a5241500407c4c0c3d02d1080030001e19540d102a20941200c0b07101c41071681d250044400f0050001441880c0d024000c020403006046180f40d0321085142e13035a002c201c503400d6140c2d004004000c105407003608850040d0f88003101261b900ea03c0d601006080c852100780d04159150401c01604451034104074010089805081c1040c081d411030311000542d0701d016003030a24614884161504540300c5030305c010341c5480f0030b05215031a070201d00f003080003403c90b0a005607400c3c0c140311144645c0381000710459 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 188539208 1250 188537958 188537963
    0x405040c14150a030c1707080f070f12090501020403050a030507060b0105030121170c160902190f0c0b040b150306061c0f0b090d09090b090105012f0703060e0a 70
    0x342400802d103804c4001c0d0070104842c0c0c0030440703401c0142049001c51401107020b20300303d45a1030302c5441d00a0002c49080c9005000c0010041c4440303032550b4503900184d40e03050042d044070005c240450207050a030301a1089520041c003034801e4001032024564090090404d4603c0303042c1c28000c070343c1c08400440d0540000c0c0507541482d0301003944840090198241c00b01224450b480f00101c052945030103800035009540a890650040841e08154a01c0400d52201402c29498114103008091002c0501305059401c44400d11070510741a42c5114001d1422101380c1c0d0388049603400610745464811041c1c1d50907a8801c0d10603a01085840c002e141c0401d16501c280710181031624130748203821420704941c1c141c14080e201c9820311012000404c4059406038402c140341700c02841800d160110043c101e00c0030b40d01219400d4600a00340c0b013540d890300350a504640d02468815007000038040244001c42100d10fa400e4050341601400c4010b98000c20700c4800c9030b0181404100c000e2a400b41030b0380310480500b00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 188540458 1250 188539208 188539249
    0x80312181209041a04110c011b05120709050a03030302090f010903200f060f0408120427021903050702150c120c1309062105070506030c07020405040c14 67
    0xc100d5410294440c4200d641103042c500200b00644c0042000c4070044401450207a90004012007190000d025041c1006140220107010000080c1700030407a0041920400900e2280004160407522500b800f4000d010018001a507055072440c01030300a43c004030289000d11080c0706050008d40c0a204103c04607504804403c1441c0c0c05052410051020f1500c000d40c001d0841d03030300d04d20130f440f075a018201006000003040e42d290704011300e00340b5010301440101c031a03080401003800165a000802e0000c03803801c0c41c0680204501740304480c0607006a021500584030450a1522811303810b40185001c3c140d03540036103580b2140300007a10101c100460b001c0c100e131942005400810f0071912035040d030010b8114409820641050036100445616034800b41016840ba030040c0400542075020030080d80308a00e11640c24a850b68800e40c40d03a4440c41440e02c01e0101100203003c1001d80402c40e403209500401c104454501403418849030b25541c000d08807050300b5071190079010b040650a4600f10308074401c4 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 188541708 1250 188540458 188540467
    0x30c0909021605060114090105121f06050d0b0709060302092101060b030c190f08061905060703020f060601050f07170d020a020a020f0928060803121812 67
    0x20309000c1e41c0000c0c856085002d4074502c14002c6401408154040d0260340d400390104010001000340c0110180c01031885031085540fa413448000000d0340300d241c0c1549484c0c1c00e00c0c0b9a201a2030fa4014911584596004a440394440e001c02040000d042e1180071580c503a500d450780ca48108404a0040408050b04503803882507841c0410129010004d1680f40d440011803250b485201002d810b130001d035000d545100e03010a40c100051034500c80e10104484030301e081ca00b98a404c0b80014020a00a40450f0007030b1032800061040c182c110302480c000c1d00d80901031541d1000e0b1403400940d076082c6030343c001300300340a0070011801541c0f16100710b6801012401d001820203600d51140e040c00342c0b100001d100b20007030420441e0122909800070f4038100c851a0041c0048480c82d006002c2d802a401d60341c10710401e681000c0180c06412202d2007100c40c40c0320b094001010a0340340b11200200400d0b00000b41c80d101c007280c03c0400c1c04500d0a528443c24903d55152504103243c070f070803a80d808000c1c100c90302c0c6680501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 188542958 1250 188541708 188541719
    0x4051903111b010f050309012a030f1107060203070c051213080606090f0a0f090803010e0a05010305030a0e01050c01050126030304030815130c05090f0609090627071e030c09 76
    0x78007a61f0084a01c0c800000c0018403a41d440031340078200402e40d60902c045c00458070900382c00d403044070009600e04405001c20b40c205102d403074031441001401444180d012003ca608144258814900039520030b084a20480660144580031f400004c0300c28000954802c0100c1d1600c804200389000d1074002c4d09040b030710b889400b00000c0100000381481659565003541840484041c090701001a018202241d80d030350418804203080c11006010700c604506000c0100001980002140c5200d42c0b98078000c0c0c3c61030038007001240c0c03601c600113005600f5070800d4004511000c006041c200c1440030080728602c01e58444c0d80300b40d2240000c17580500410750243c00030341002c1009641c80301030b0700000c00e02c1c01081d0320302c1d000204860000c4141000100e02080c032800f035003041614101c0004049940310300b0f01609000041856000920342030190b0408036200340c42916400da00d04000008201140451409100003055400c0030103440c041c02010041d020307001406440386018541079035540204150815 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 188544208 1250 188542958 188542967
    0x60403050703170103200402070f020f0103411504052203080708060a0f030623090f190f0201080403120213080d02060c04090504051903111b010f 64
    0x10032054050201c030000f10220308400c84100d901070b52252085000c600040002100100c01c00102c0c98040c0c0d104104036000719202024241445504a0710221401c0103900101d01801c3c1480c04015444100c10300102d100500e1815141c0024084c51450366440520240e121100303c142c400b210000b0f01020b0f40d000350b0421fa000030b42c0c400782070394018144012240854815501691040e00040d03024018800900d40c4290aa0782000c41125802d07441030501500040c895039910004041035954031030449841d0121a14605588810899041c0341c07038032151756900c6151842c1074104e180144105060340301b60320a07440c0c00481c1c0141703040810807000d500540380118090415014030458030000c901c0208107000400c40d00e1708054010121a20f40620549005802d61b421011354206500f0028005405401e031411107203440d2000c100740d1181e0a10340e040850407000844403460700e5141005160b0002c0d624050b642407401107401040c110880d800030300d0240400e4500140c109000341c1c034090f104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 188545458 1250 188544208 188544217
    0x230703390b0304030504150206060f0108100611011b0f080105010504120b04050a050610030b0105030a03050a0c030c0c0e0708090d050a030c17070c051e120a0c060c09051e0306040305 80
    0x2d05005d0b18042e21030760400b4941401214100041e4000340403c1000e003494608a005508282040d000700d00b000300d1003202a0005028000801c400918107221a030004d411100b44201c00814069120006240091001c0803040c4410b01144c00b01d40001060352081e022101115400c2d140c1d4030000d0059a5200da00443c003802c207482d680f09501d581c07000320304188a100d0042181102011b0040c4c61460030250140c0140c0c885c5200703401020080011a40100c101c0c2c035001c809140101459000d450140c03030900300d418010b080814801c0700480c0d1100001c038a2401031001e902c66030076075610b10381d400e540ca41d80d240e1034070001003041c481d501c0424040d030008039000d038080c2842c1c1036005401640d9480c82c801101d580b00015803526070002408000e00c4104030601880e465200c0c222030280039180c0e80c04008081d0b9451040019046031a18401e00c5980c0d0216848501480021a82e08000304648400c1c081c051181861070160086150303428050715070900054003a007030079901c50310103840300d400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 188546708 1250 188545458 188545463
    0xf0303020d020f0c060307200708010e0307020d020919060605090109050d0f03050a090306020f0304110d0b060f13020310090f0207020a1e0803070308090114060904230703390b0304 79
    0x4101c00e8a88448d0300001c1207100d40080c0000d10070645442d050f14295046d2080084064104014040141e1a0401c003a070040c0d4060b111001c0c1e03500c800e04594072030a000c00502c6151840c0440203d80d4a500000810089000b681d92041454542c01000260026010020f1075207201407526000280079002500c000412820310961036543e03512041c06a138440c0b207081c800410004100400c012042d02c400303145440c1528012000c42440c0c0d03428074085400f42020f4420110745104058565881c0590010448803002c1503440c0d0901e44402d40020040b800b03240384044c200700012081100910a50340e0154000b0911241d5528220400178440c1d40c0f0301d41d2940c1003011100200380018100010034070741e84695100039051074550b10050840b0101c100450000c091041071040c1980c5002c402d503080f5030040c041544d1035203c0301d000c52001111401a00b454082c01c0c000200348110304440d915074080c2d40840c3c00e8050306482400e80034a200301d020003003051840205100506041d405540c2c81403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 188547958 1250 188546708 188546717
    0xc04080d1d040606090f060302041a030604090210170c0c150402060d050f070305060a1a03060a05040c050702011e0c2603100801180206031f0b040f0303020d020f0c060307 75
    0x1441d0300c081420fa4070240c1100b0040b62092800f08800b02e54500000b0007888686030031400d0604200d007003102500c46407070158503a85d005c400304607d95290350040031060b038024201d44480d42541e0014254040085060035082815000544c8484140c0d00f102c805104d000003400008080000c0c0018007180030b407040c0d800c660140044404c00000744110307801150302d41ea2024207890440001025031781c00410403406590841d8040290f17010707003490450030720010941d4a80701e58403140803074188405948001c1c0d015007408031140b44140c0090041407094000c0e41d0b094228080350030003858042e80d140802000402c900300302c0300400d0100210248401c60300481d01e096408054a681698109841c400ea5038840341a0402c00120240f0980d182200d5270500c04c503104405c1d030000340540c0001015840b5040c14214407407a245085040000138140f14076040e40c44540704c0c2d4624444031500d0000300c0161040c080050103840c0001914400c1e8000c030030081c908001d94406010359900080d10040512 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 188549208 1250 188547958 188548007
    0x50a0c030e060a0e090c070510050604020d11191d010f0c0803010608150f0321071a1512031e0c1e070504061206050405151302090c04080d 61
    0x10360382e20b03000702010240380c0d03a003c40344458801088031551020b000c0404413101000b070f050000d400401c00d10f01482160000040310f54856000c2000b030b214948400c1005032401120341041c0c00084003400170810700c0c51001d660311141031010350700000e00c0102e0724042030782600502e00c29849030b001070b07c070740c5240c0c07500800b4843c40340d490300b005800a811000100b5100c80420100180c00050b90b0142142118441c0b20701402c040403d494500031032a41d40c09400b030054071240440b00324115000e40342d101c446030b095202c1e40c1d0030000c1028410b4030400070458401c030780b00503035203080c1c4100c46040b018071014600c0c00c18550b090010100c01c0803003410500a0902511144020030300031408050f0510080c00d05440351180308a04000c6550070040c07269140201c1480300b0310000c40000040c603800140041c85844c0c47c28090315007400d01200010300040c01c01081181a04040c00c00c018074401d442c0d914868903a2820940c2c2e9004600400b82c0075442100c8601c5207d02c50040c0c5000b4584001300644e00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 188550458 1250 188549208 188549237
    0x50a14040b060a110c010f0522050a0906091a0901060327050d02010c031b0e1201020a0924080a05150a170601090c05041e050d0b060405070c03050a0c03 67
    0x65401c0090440007040c12120a2207131640180f0400140344424a0320000d00c0c0c180100103461030003010348403600040c1203514141044111042d0401034003004250000d080d95482042d005000b203801030794511801c080314683c401d469000d00390140200109201c0a507804c2c590200c000381031b0b040848000c800e0001412034144504100011824003070b4003d030a40f40c4c132641010742540e064012030001c052902100c07081c517503520240c05a03030840382d04d028002d41388007070000b421310100c0f92090540c55200065014400340c115152500b101c98058a10384141d085441604d400751824680c2c4000c030b5100c3c0300050001c040c9502150780101d03100d080140e40745404011403120328560700410324010101c0c954414402081144500500c03a040c0c0602c0702c0e010399400200280114483c641c01030700a4682d0303441c854800c0c00d00201400000e810700d40342c1c1c0b07441e0074004940941616040d001d50b29100c0800c000901c103414001040390941c81b030310700c0c002c06108101c1d03049010402c298104582d820b600020b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 188551708 1250 188550458 188550469
    0x504050a06030b070206060a0b07150c050c160506030106080402180702010b01030f051504021b0109080d18021e030708060c0703090e07021f0b1f03060f050a14040b 72
    0x180c0100d0320004840c0c1c218503101d44410b0018000c0c2d02594040d504000380799803224200c80550f8012000b96407914620300d0107440803100184248031032420920114072081d44000030707001d4190407004440d29611120078032034031785e4081e01465401481c10401404100e0090803c03980087c80500b54030865418507c80302c001d41015204040181d466011078000c660341800303052000703070b0403c208000c030341049001c0300705881d0b01c00341060160b9008546c0d22446281c010101e10a00d00b010001c1c01400441c0c030b44038549502c080001c1907000d01d0310b5007a0024103a0744070b100d1001a400350245581d5846585040c4400014584150b450700c608640410400ca0903c4100e004110301e6a0300e907201c019918014020f00110307080382200950b24420055a241c2c00981e424200d0b507058003640a6601d9141c0c24006001c01400349604624061a0071131469060480480211040d035810801c1580310024000440c410384501c5900c20907012040c840668040002044210001e00001718402803002080 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 188552958 1250 188551708 188551711
    0x60d0204021c0614031f0b030f0307020414062d0d21020102070206030a09032604120f0c080309031315030609020a09150908030f0d06050a0803040e0709050405 70
    0x100c2d0701a0b40204403502d5203541c0200c00c00b0f8090302140314007414240000c00d5842482d01e0510368040300648102003403041c10f5200c1400c03450090191003100d68001840c95507035000b80c80484c012403520302c0200c5000c40c2070207001c0c01400e00a00e4040d100e0340010704086580140184881503020900140c0015070702c140300b2908a52040d44c1c0d100341d00c010300100d0236200f03007017018110070769004004080059548004507540451030603c00103580e501c80c24122f40c00c201641ea44a041c0811800c2c05400559600d03c5c1e0348a00d201d00301c0f501ca6480310b414211002800b1000e96008074800085502c009950b2101a5510010f074030b007200d0900444203885102c40026502020a060500c24500c00481e4103010395006011580ca0542c030b4601c07030600041c80410288110003071621849144d00100744240e0801c0020600c0d03400b1a600d40361100342c080c9840e17006480340700c1102c3c03401c44c0006050401e0503d5208892404000c0e5003007528040d0115502c410040c01e86003088080e03480442c01d42d0303941c4180e9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 188554208 1250 188552958 188552977
    0x20a030c0e04050408070215041805150d0c052e090317040308070f020301180503040f08161707080f3304020f0f0307170601050a1508060d020402 64
    0x30420305880c00015048210300000c01e4020390503d02000302041211080f00c0c56a42e0681e80821160010f034280721070f03030149070070140b800c1c1040100303000d42241e0354101074011a003a025003c4200240400c01603c441d503100010040e4241800c108240e160601d1041203110200c04141034412000b440c00200c90812038020005c21442e0303409000348080e901c040e10f10700d13194107007040c030b0103003151200001c0380103400313008080f000c0d555803210854800390002c0309510752070030f06407654103003601c0d10320745030b402c540140a901c1c2c5e46880f000814410010700c00b03c0c20000c1c00043e540d032500f880420075249401c5da00c01c0b004e92207148000108004100f00c50707080262140054601d920100c0d00c940340e10003801107100c01d005888002c485108165040c03a40e0043ea04550044d030154903e000301d90034003c2d643c03400b64107000c3c04400103203018011403001424030a280c2500c010ba81ca49041000c2c13061030740a00300c0c240d10416005070b15a4001e841017034120703000800c4450406650742c0007c050741d0052948 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 188555458 1250 188554208 188554211
    0xb01020a061d0607080c0304021527190e0c16020d12080604060602100e0106120b0103020301060812040312050d0618051008121e0a050c15100b070510020a03 69
    0x40c01c0e20440900045810804d986043d02480c1007a00d00400325000c0035201070311032130340e030900503103420b020800b220304c07802c405c072600b00044002d20760580004042941d80d9010f454000200e0140000a220341425a0f80340403c0c0304903500c0700400302c091a006912410b03602d40003042d081c400343c0c1d15010155103041c45441181c4480b814190300418490b0040c220b14000c904041081c020a071300400c0e4030800724600400052080090b42c08039002d400107501c074000210712404000300b44441038008034140c9009400a01c07840c0d40c0d07913041a94a07042503000c51400e40081c401403000500184088080035420f1910f1403c1080d10a042000c0354040e50281e92024603681c08000140e0030341c001c0304d034410980101d03002123510780b001054440706e094542201c84c400004100c1c418100c0c08004842241d04482030302d80700c03525001e020700a40e104640a00c1395103d003031008083c1150b0094083d02c20036121000c0c1d00b03c0ca280c01079070210783d04551021500c500520603480481c0d05680301500740a40c05640 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 188556708 1250 188555458 188555501
    0x31410050906240d0204200309030d05010e04080702060a090b0a1d0d03083105010203040201171e0703091218060c05030910020f010203162601090b01020a06 69
    0x35010b07a000b03a03c1000790005000d0200f00e1a1940d01d2000c4885115015640469641c4808030245880c541c0c0040c000c0d141e410100a02030b0344000080645000e15220314108080e0f621402056000b072812600205100c00802012006080a00180c011010141000c41c10262074507081c2809030006c1042c503000072030020346500c590340803100d62101a4029100d0704c1c0e1181450320001d2440500408611030303100e0f83c824501c40040c4030000d0094050b90000410010511032811350b010754001c3d00e00342c4c0019884550a102c811707000d803c0d9805640444010100d80421800720a080c060080446050566401d880c2001c54017800c10340c00c01103215030f901000381d2020f1003240000c041c2074101c0e004010341c031096400091740000c03ca80e4100300440300071990000c1804100d103844d11820b44444254000700500c040388034803900070f0040b03655648510f101490000040307030f550141d4148889002c002840104480141c2d0740c080005450180305603524403120f5240c8000b65549052051515100b070306 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 188557958 1250 188556708 188556721
    0x120f020a0b03070806060901140301030f060e190209060a12060b0102010f090305090906060712121b0503060405041509050a110604060207060e0d060e010207110f010207031410050906 80
    0xc0c09034050090700285905500b05407078010030f092401415a409000300280e40c4000381c1c0181c0e00d010700c90140445495072583c407498550882e1720043e508644107030420441c2034003048007080040c80c00301040e00c80303e2100d00d41d030200018140090a415040080380c0c0020841c0c071403104074038580d64015507020030186207000009084a1200c181c070390034146000400000a41e0204c06c640d07044004403140100c68482400060780307403280c0c941c000c0c101b4445011000045801c00c5c48411f074180b0320f40701008918038608802c0c4102400a00d580005002007000500e50b1806610180c1c01501800d0520507200b0f18441080407920410803e032000d5010140305010400c880c11045910001940c906060514014010395903d225000d41e01c24041003031080002c640740c41d04810280d5801036003d1010b0401c0e04104d6000f540a400103840a1041000c0150542805501140741c18810790040403541d1550721035801c00312112003d01d45500820340c115001242d10b0041601547d00d16003d84174070304041 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 188559208 1250 188557958 188557969
    0x1f020d0609020412120201020301050114090a0e100312090b0301031e0501180204180b010510120911010206071806050a0207050603070e24040902070201020a050d0801080f01050c0d15120f02 83
    0x31642141162300400051009076804800341071203a9860200940302d800c00c40024000303007201d030031031a2944111000c1101c1c12019451040460b40651000120040400c108603030b00c0c821070244445800d010001040000c02c68280c018024905129091108504da0390b150300350340303144890710016602e03110301c5415840c1511410f011000c0d00e40056512080e0b0f543d0360048505d0502c41c481c4222010175103003210300d00030020f1411000c00110708004400041c80d00040c100c2107035001e40d005100b49030028003100d0107074030380c40b108440ca00440e12020349080021102c0360302030100c0394114003e2050005d00c13521490b01a50041e070340d07610b6420a41800b2818000c400c408100388041c03030400c031108049440175803011181511110751015030784501500050b8900b04080400811500c40d8641c07600c1c007542d21440450580f4204415901c800381d41031340641c2640c100307540740744245c481008258891800c90b40308d1041441c40e600b58000c0c0c070b0f5484c2542a68608649402c0e9890f0f02900403150461810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 188560458 1250 188559208 188559233
    0x1401060f0e040c06030b031e2d100507020a0606080d02060709060509010804060e06040b0a1b1403070c0c090507021219230714010e1f020d0609020412 66
    0x76444070318082e00e00340d22054220b4070b0f82c3c404c20050598483c040c282513201030140303400800030b03c2451100800034040907a51449400c0c02d01111480c903070489003244000800000001d0528401170058200a6017118000d1002608110a52141c0d007046c01c00289203014010081100101400b03e00c44040d50180c1843c00c001c040c8020001000000d000060308803090300c04614003131030009019503407490702d04001c000e95045520b00c0d2040308100800c102c041d41502d403140580350403d10100916030703021420350410608010100b18803100390000154010081d552041d0640b03000714200041e6201c9400c030307241907003010060300d482d0b00400c003030a6010400d03036280c0540f01c031610385011005004485410800406101080b0030141e800400810303100781c0c1d4440b2500201d02c555243d4a030f20380b0400c0c071310709401e00006550030030405940620000c201140c07017001311122420750000903d1004000d601140c840460036a035020007049942c400c2c40684050310f02d5050f40b1020700707024100100e84070300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 188561708 1250 188560458 188560469
    0x5030d0c030504031716050303061009081f140106020d020c0a060f032a030603110307081203090708070627051e040212040b041205040b0a110a1401060f 67
    0x86045120300095004084030202c1c0d4029401c0031000b1110013241d510362141902c07142072070040f65101c90a00c9400300065000b4042103540c055640310101040d90083e666114004081c1c009045510069010100c1c484240c0c000001c00501d00c01d4070010701401440c01c4e00708400584c041c00120000540410072144c480c03004440e00c1540500d011030080414140551700001c02d03407124010700328070303141d9074020403440c17450301d081480c20420380700043c01404184001e403540d0044410700c0030700d0b040116206041e500301c1805000742c82803445505d1043d42c00039203104080c0c400c454002561010500180f000b1740000da8030318031035906110161002400285840c030030ba1290341c20030401640c0340c46484c1b00802c020f00d003440d4011415000500203000b0324102202e04002c003000c01040111020b16244503600c10040c2e102c2d510040300007101d880c01913005081c0c905004110f03452049003c0d0515085114108084441c0c030310096450010321010340651004507034442205000d4061142c0c403120140c803 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 188562958 1250 188561708 188561717
    0x606130506060a0f02030c010e0606041107111504030611040608060103020a020601180e0316050111210c1c0914010b061e1b0a0b0604090b15130f050105030d 69
    0x2004070000e0010311035a9110010302c207403180002d800f03a0080c402d5a8004510200801c00e500c403260255803601c02c2210264801d17403800d420008400c40c1c0e5002da40c049500004103042141081c01030140d291303040d052140b03060800b400004000b8203a1f0190000146886140700d1300d0710b2030004007821442014295a040c54010b010262540c1d9000940c6411101802c1241c0d000c01d61410180f00145043c8500490901001550b4860365403c110880790042c41507008100d40204a292141c0324000e0150345046a0509003050004044c0c1000e6a07801c05000340c41c441c5855560002d1040880506001c0729507281c58602200c188800200c1d400e00c1c28400600a2146551103c0003803124440c805083d56601d03080808452010411801c2e500180031440800c000c000219080302d0351401410021a00da0f0524000940181040e001d1050b9050340303c1c42c0c0c0c55003501c030980003d2840d030300840090303044185aa0070800c0301b0b005004401007c9039041d00068294140001d05003000e010514620501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 188564208 1250 188562958 188562961
    0x90103150e0f190c02160501030606080c0901020c0618090612070302061602030105090618070506030402010e0d02060d1a09010605090d0c1e140103050106140c070b0c06061305 77
    0x1100280190342c400408207a003a4a40e483c3c91600d00111003082c014040301340740402d8104400d4001030780400da010401160500207580c0e0004600340c030094007401001a00c0f010200b920251014090920729105005030340f00c0c111188003080541e0802000611071300142503144c1d04a0410742d84032508140305440c100240342000300030300d650708a548002070007604000740d00e184640030f6031848209554014000d000b03c1c01c16520241d504c1500b52840101c03404c0d0401c0324100c4601c0002c4510868070080d0699065036239980055401d01c0504032005d0308020350140c5040182c1d01c400050500c000b401c0c02c0015800345110504640d6024120860b0148900c60b005000d41d50f00a400c0c1da4400c00b045680380003c0300e0030700c0d1801000c2040e5100c0740a0f200d40054003101225514a03581c20b03140d4200c0613003a06a815070044041c0c890070300c101d10204008089450440e4041c5000f0a4180503d00403201902e584080540c401c0e80204090245138001500f4054036242c0314240d1509051001810b101c1d9 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 188565458 1250 188564208 188564219
    0x106030f0b03061b09040603290402150a02101b091d04230d0c020112090b0109050702010b0303041508090d12090c0e0f0402030c010203040e0109020c03070c0b09010315 74
    0x480f00301501983c0c90704015900d0402c0303007004200b22401500060703c00d105169582c6005201c19900c000c140c04c0102030000031051544100d00c00c51300c04ea0b0000d100b41c1c810b01c40c00b13118905640c0444184000c50003015030508141815005000c10701250480c10b019407140032600030b021007501d07080708075801c081110380b5040340c21501c0030b181c0140d040b8080c0e2500d0302c400c1c0c8031540e002c0c040f06003075600d43c000c04500e0b005841d0084903188585000b80c1b01d540c014070400c180c4900b00e4800403401840304802e0710041c8143c1142d83d22290303100109000020386215500002481d50704079600080100b40201e40c005102a0300a61803600120074800400e00c1020810025000140c03005c5500c0651341e4803a00b500510000c0d6803101c0003048204643e81d014144000301c1d030444032040b103043c4d01901c14a00404060751001048070210b0b401000c4103071542c5d003400c0c1802701a5012080c024030b40d00c4103100110200f02c240e04c2d07940c0102a0780714466a1181c03018009010740e050407080301051080048104035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 188566708 1250 188565458 188565463
    0x1b0e1c0512031003020a0612050f090d120e1f0f020a0c030302070503041802071a01050f0d21020601291c0908030c0c01060806220305090303120106030f0b03 69
    0x1c0c549240da18503500c1c0e81d1000b841003400d407070300ea00107540034080b8500000c1c06600102c00c0110010410303000e1155540e00a1072188102042e40c60305101c6c2d00007015000c40920601180e040d10368400070104e148002d40e0006450304003c201501030b0408840d038110f800041911500c900c000080000754184032112201920301c00c400304015050540004a02c0200f05050084401820352004054113412040d82c48400039000640229110100007203040450541529680d04a0f50000d246014038140d1000f4011119a9080d045440c0c801d072880500804c1c01489810482075110b6000f030a15601d0a00e041000d615545051600b04003a40b030300c0c80718045124201c0d0500c000400c1d1007511b4504058980340140744004010b0f04100f004800e00c03040742c0980340100320603480030303000b4000c9a448030320171030711485c054420000180c090f00000001c500076034544d0b148140207040c428101440100401e0540d030210b88100c1d08242c107040148002ca0300740c4075511600003444410400720300c04c517000c6075 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 188567958 1250 188566708 188566723
    0x170901031d07030b040501020d02030708010314010b1005091203030411010f0c03020a03051810050d0c05090609100c080d0609060e0f010315060801020c0c030105070c0809040f1b0e1c05 81
    0x900d0391307148000160a00509404562120f80c00b510215600c0c5401c1d900109480d00c03e000440c1c2c001d4410300c040c2124101402521408480285000c40d027401c4042c0c00d540a130301401c0f030a0380004e030808000303810071428805148581e0158103040b940380d40c03030000102508600400403050200300b00010011a9000508901d000d03414180265104941000b602650807800b00c25075001001078121042168440b020303188042403280281301c1c0044159003990140250511a40c100000348442c00607842e00b000c030f0915a104504200c21207070816103401083e81d0010b170000c03264585074181002600704511502004001e03c0c2d00421440c28940c88140304100d0600c40079203041070b000c08034040c0c840709600001c001c00c03140c0021543c074020140325a88075241e010b54070f41719501c2c104c0010a100e0062000300340840c0d01c101c03020300c0e00308038104100041090810302074005590b007120381f00030800d04158000306801a1500c0304000505000c102400346e0000c648800e01b000389191400203a800188076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 188569208 1250 188567958 188567963
    0x9140304060801091805061602060114010c021c020d0602040305060a0903120504140304030309031e03090303141303050109050f01110a0e0607061d07061e1b170901031d0703 76
    0x4104807050001c2d1500517070903207001425034000c04041c0004c59402c0545000440c8482e001d4a01a81e039450354001e12006894000f404940040046001860a00c0b04c9207900720b06100c8031595000c06401042c1d079440c0c2d07110111901540083d003402403100403c15994003e04181e003d00c441d265a540007064842000800f500e0f46480f980401c3c00c11002150b1503ca50f2035080481c0c0c1c54940d07905004014240c83d100540d19040c40b5140c00c060001d0030f6140c0315107190191034010b10300b0701d15501181c0b20b440e50403403035040c403034203202082052100c20100c1004600a40000c00d40132020305040307080600c542d0781c0064030b0f0b1500c101c0082688605043d22901000d07810810301030703854800825540c2c030890342c000b401c0c5171a080010703004c140f0411510302d041054004031000c26890720750503980c2d21603501071052043c0079802440c0d013503840381084241240030b6206903043d0000a03a60b9a800c1c0072029100d07030704a5000304800c0f000c0d59062107820b6100707518241121503001407000f2280c940700b860001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 188570458 1250 188569208 188569211
    0x10020f0c01180f021c050613020a0503010606200f03040312030e0705011202070804180207032307080a0e100203220b0a0c030c0503030907140618040b0a1205010914030406080109 78
    0x707000501a605a80c60502d40c2c106d03043d074249240c140b001140d151482c041c203c0c4518101c0c0804111400c05219090940e16140c4070b01c1030240381c440461102002038468007240b48102001c03103501a02c1400030304015846804218000c0f40e8462000d41641e03a08843c51403158080c802c100000c0e03030b0000d03d503c101b8035050700050f640e40c02420a66168441c1d50440c410100e01c0c00c850790031289042e801800700500031703640c4003104511074100403100640b80d4521064880e0038811480898880001041110b4181c20311000420f5004c000c84c2841d0b41d43e602100141c0c00104071441c111301504507030a0030902c00c0e100382140c503050800d2005140203c2c03d0b04020800004020400c150082c070408a0a540180440c0e44a241190380580d03540380131700030900810640d50104445040040640e010074141003031801c02441520b003031000601c0c80750041d6600030814800001c40c0d504040c00040b46500403000840c8000007400c04010612207150510050751042104003c41c903070000d50f0360b0548915020 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 188571708 1250 188570458 188570479
    0x606050316030c020304031a040203210906031021060501060c0c03080d1e020406020c04050c030f04030207090f0e07060c080d020306150315012007120510020f0c01180f02 75
    0x105e1460196400081010b41c03c03105401807070601c900e030a032107184220100e0b4901d003841c140700f40c00b1142c4400c0b03070100e106060061060078035049006c0e41e37000040128007043d00350342c0c0e188840d0000340c410b240368103042440180c1060250034001c941c003504071410a22202d603110f030f595203240760b150311015102000100300404e403010103401810b40744800300300304400c0311082d0502c43d000398018890b0380050b00c180c034501d02036802c060003070500c5400181e45580c10356880039107240700903400500450441c00384902c041000d40701481020003401e00b490001900f0340a07801c0080c81c0020701c2d086041846055424030000800500c1100d501c2082c2d11000341c5c690315000040b03140050305180300384000401104004421210724510050040240d9500d0010381e080f900280003503058428030903250300030440134095884803549130412903200b00c0441c0c0b40300c0800d01100c42217810003100c03001c105200080460404c2001d028090150403032204500603110113544525428000480003401145c0200 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 188572958 1250 188571708 188571731
    0x2040f02090a0305030c010e2e09080307121409070b0a0c05070303030f0b0103060305100b130507031407110c090402040212040c0906080a0b07050306030a06140a060605031603 77
    0x20161007489030081c2030400465124074100e07840c0d8000e071260401c55840d02c0400400716100003120200c06a84046002c07070a80b1405180c084261080a00c0d03884c1501e42c075249001540380b0004503c10499507403491030381d011940c080b8090f9640494105014054401807140208011030703d142110940c4003072b207a5958090078192030091413144040c00300c1c0a00c00001080c140c054101403021522594200860301c25000150122003c80c040913215500440807081540d1940d404141c40030401000701492a02240780c820a44404540c00030000740c562011420403030000002d80d0b048401d0741080310040d101c0911861b078030391989062900c1000120042001e54031194110b500b0700140a02c101c08a00e040d04116150440502c1034080380b41c50250000342e91000454074142c400e0f400300200000d602c40050840f080c0d00090441c99140c00f408030000700044e210f100f0000040381d0a88288020720302103d030344044507070a600078000d100e0200104681c5a1002c4141002c0808604000402c091840c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 188574208 1250 188572958 188572961
    0x606061603020a12030f111314132f070b0609070908010e06070906020102070503031302040209060d050a0506011d0d0c0f0b07170403120c1106220f0f0302040f 70
    0x94030f014081420303041c3c82010740f0398150004a9501c5d0029401d2184541d144150b4086108040c4001320024140c4d1050100d40b980782c0d0303403101c4894000c0000170140c00794419001140c5005030980020070740c0104100340c610b408041032520a06407192203003000990f40f00c808100b0401054107120b04045800508803900400980001d003000700000c00202c02d41c2d1043c26561070040d1580c00104101040000d003041c814000c5503882ca074000301560443e200c07002a131840030568201203a00580070700210009454007400f80103881248178021030309083c640e5100b4226403000d0680c40c104000d206107182c20440c0741d18100342009096801c0e00610754141401c1c0c1000e1203d41101799400e42d00000001c0e664100c5002c2c200c41c1d400b40484445106a115001c041c07407144d848001c02240d01004c0c05640f6034016070b0441c0686016041c0c51903200385100000d6901c1d80003035003c80c218000c22448006200010407000042c00c8903141071240d207414000030011058079484000d2040b5250204410700b01d01c47d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 188575458 1250 188574208 188574223
    0x801090b0c12010b030604021605100615020d18050d050307111e010c0f080d06030b010902040812030907030c0308040315060b030c07060603020406060503011a0316030b010201090b01030b010f08060606160302 91
    0x400448800e0300740c40c242d070711203090032800c2841500333011001c1040e1080d01080000401c6c150000c0c940c20b100349000340c038024915081800d05441c0000c000400d9182d100302e0750340e103a12a1010303583d1885185020200c0980315003020303001d5000c804851075591403001c01d20300501424204000c43e4021840d11845040000304001e10307100d0045501c0d250180c098000c441968072604116145030388a605810490050f03101e81070145d44907504200c5075130a4a001141c1054400080d2060580c0341d1711071400365940c030b03803040304e901d400082c003003040c0940940c8165414503114014004141303081c008620f02d01001e0308184146200055280c1000070039031060008580c0500300740034080e034408015010f074000740704400b11480101381c0d03080d00758800d0341183c0c0b0907103000c461415a4050401c04500034a605095036041d5984c948000c000300701c0142c01607000b103214401d8108151b0418008480d1200d5580c40a9050390048003441980e5690a003681c1c00d50030113103038821a1001909049203040c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 188576708 1250 188575458 188575477
    0xf0e01030e012a030f0203040206091207030c0b1305030102090d0b060d05060f07412511040c0c0b040203071205060901051303020c0108090111040801090b0c12010b03060402 76
    0x1c2c0c95616001c039000412004060f6590781c60801c10200d4801d110801c0e840b003110002d501250400050845290014100706015000c00869401c5a00ca80d40c580154506130440c0c0c43e01c02c4041204003000513091180406000c0c1680294101184440898030480714140700400c42d20703072440000c106841c5c242e0389085882e041421034103541020701e001c1503210707000c2e281c00c1c0000b03100c046296604010240c0d02d0340000b20780709410410280d80045904101c00507100742d00144801c10050054100c0d6205024520910b509002c071800e0740b9245c89102c0e041042e84250045080c40d88004a072904626015070554001440b0798443d681c51000070308025003600000300848180720b80009025001562074494111030b00200301c0c0303488201606c40300512101004005a0000a0b0f001c0c05522894989400c0000780300003080304a0620013182041d00030350407100b02c40c0c0d5245809024461030803100c3d60020205c8904038030f458007110000d0448031050040483d2000004003054150f1180e40c1103440700388 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 188577958 1250 188576708 188576741
    0x90301020a030e0d080906010e270607091502030d18050601031b0b0f0f0a17090a05162412060f0323061503010b0a240f0e01030e01 58
    0x1c5402401600a0101500d10440ca2081042c0f01c100380d80030304a980d00814480e40145407683ca0100c4001c0a280000c1284502c114002c680c2c202c10812020382120a03104407000d440c841c0b82c0005c0041900010351721021201c2c101c42032208a0b03680200c1250b0001461030b0010030001c01c0d0042c1020b405901140050442c41004000814000c02e40c0c0c0c81e07600c0500456081d50003903075540032040e80b03006503c1004841c81007000300150f60682c58008002960f0a41002030043c1c00988010701400001c40303440303c440d00655101c1040080c14840082e00354804c03640c5410803810302c07041d00c40601000e1010356440d2000e000a8981c00c2c0581900b4010b0707034000c28140300700754841901c254400344038402219201012603140d815900c00c0d00618030307120300045c002e222a58880501d00440f00b0a10407490f019582c46004141513119941d0400c09401501902003407000a40407421071011051941d43c204189616080c0e16940e1100c85030010400c01d00e000319604c10013015a070700401024035801e0b08007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 188579208 1250 188577958 188577967
    0x70e010e01032a0206071107050a050d060e0d052208060402060705030c010c0507030f0e150d110f0a0807020703050a0201080c1603171501080f04031b0b1506090102100c02010209030102 81
    0x1144e0009a140c401c540b030303903108504414011000d65868a4178000c86a0220009505000c103041c400040c0d85c1c410700800c40414803040070354105040c006a4010080003510005006505201d15480e445182862004011900e0302e0b1000c0725441d400040c000912400c40001d0240a002c0c0410503210304400001c000c01040d40e043c50080d08503442041c040380420640a20402e2840c01b51021240080001e014011682101d0005008544c02008044003913031791005000040c40c01139015100310380150b07010300c2d50789100d41030203008070708014688411076002c00010700020304003040214100c0c0c0d0a0038014043d8031a988142c105005100c1c003400486c40940f505418181d001308440e0100658900004042d111051107a0669405004d0301d40440c0c034003400710b110761840c80c592a501c00e00034035044400f903000e42c44280c152044924140e800611440030711146400300303c09506119411160107140000400002c2e45034412078a607812025174414188a01c54003e40407a40c44140003802195107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 188580458 1250 188579208 188579291
    0x7080301060f080109020c0c10110f01021803010605130902030114090c010807030516050c0f150901050f070f12060e18060a0c052704060b030708070e010e0103 70
    0x100c04800b1407040001d00c1d05400040c641c00c0f00d1003182e44058002014101880c503103420b01c80014085555801040968204900010800d12540c05c0b074240c072400160380c1d01f00c0a00100d010000401029200f640b50407020042555030355188510f9032903005000c50700103160300020307005014402b41d128030740301d0007410001e40310030115048001c0902600c4685040c1c03501803080b01210300c111440710580340400002011540150081c2c03440030b980b0412100b04e40c0e480081d41d42031412080d00e010509146000f4030100100a01609511523100911000c081c40c0c0b07800300610001c000741c080c03020f000340254065142c2d6666044000a0200c0c0c001c501c440f41030100450003410300d0445064281c2c0112808139a130b0310201d0207060345100e02940c03a00d04216690380e20356842044010444052030031210020103d03100d6020300700041403a001074949a140c040005008000000d010404001a142018032641c1c0c102c05400001107083c0380015032840783c19010328495014a80c0031240550755903070401c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 188581708 1250 188580458 188580467
    0x4030c0314030124110d051b012a0309020307050f03100501080c0a060806150f04151e050a2a05120904060b0705030a0305060609040e060103061a060403060f020708030106 75
    0x1035003408144c1180c002c1e48440e00845100101080c80c00b00398020081003174129100c1c03005054140a50080c14071101003100d44c481c00c64070f00e4800308034440b09003041ca103086400c28460515071506814144402c0a20750300003a21600603001c2c4a1241988140d0200d00b40c804205801c0c50300b654000070021540c460426540e1502481d80d65031081004041c0412450300c5840290300a00d0090400c029007c3c0440035010550814022500048018800003840c1142c0099003a10079500392185e421a080781d00c1c4140c00c80d0300300c01d240014007004000b018600c544c880b00410142000c1680301000382c6500c22042c104202d1428060098030503241302d460702c1c6c0c41034802460292800c540402000e036480347c2c0000070b8000c1d4072020340982c005104841c5038034040e800c1903034400c00080181346040c0c140320004007280e411003030200e035541c05a00180104200780c412019414800d03a0040c0300c40010a00007400c0348074500000b000b01d5215001103910060680681d0b000541c4152459240d40e1a01030061 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 188582958 1250 188581708 188581739
    0xd050411040203150f060a0804060e011407050408160b030a0c050408030a120c030603170a02070f030303020703080a15060c02030c0a0b0d0513030903023f0f0f0604030c03140301 78
    0x107205c0c242c0400513101c180351240032200315522649440d141a03940d074503179100401c00109140403035502da45560b800c030040d1030f07a414441c4910742c403100c2d111420700041c94640072002aa101403505100d4040c8184e5100700b0a0b00e03841400c0031b5020030800011407040301c40307000e02c1d44510f07080e100114148000f0360b002602c0c25015010743e0300811024070b503024120b040d6609803101808600800c440d02c20042c0c107503401003400c420940121024503a880c006001f1114859005a00295002c940300c420185d003c1001c0380c1107001450207100c0c1e102c07071500308060310070103104078010712498519003001c42d2424400024841c03001086019036940d43d002c01e031041c0d448450220015031401001900c00400803024000713103509913840030111801c550a0180c5c24040024000c1c0c802c8103004a0b540c0c03803041c0e98184aa440442ca4400000200c62041c64500304468502100c0f80e0807400c0c56940315100041e900da80290145417401081e0418181a5007032003210389078400741440040040f402e45803054050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 188584208 1250 188582958 188583001
    0xd020a080712150c0f05070602280e01030632040f0e0f121207020c03060a0b0120030304030e01050f040909200a05091b030f070e0303030c0d050411040203 68
    0x1c24a030801480e10225801c0400742004a840d0700388000505c0e04c194041c1c454284111001494400d8290660f56a99402c80d02c02c40c0130700465410045c070540c4a10441d180324028201444038030704206040f01c88102c0506003403602401d5041000300843c12441c50450f001c005001000001d01d000c205034041d14071303000c03081558403942c80f80441c035205c0011002c0390b80c00340c5034942c4c0c01d001c0000300031004144082e02200441c400c0c5400d400090ba42440154050243c0307050000300700c68210b00150030700101e0350f10000319454000c01400210000f00499900aa16250100041d65407000685040c0070312003040c0b94621303011038003007980c0b440c5074445095180905160701080300f42490822028141030281078102c04001070030011400d06c0422103801c003205003030700420681c40c0c19114009400480f0181c00c441c0c8501c00b03004c901c5820042c00c2e22641000e4016600e18584000201200c0c0b040541100485035240001404e200b07480e44038540659008100f950780303082a24002425040c40c07100c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 188585458 1250 188584208 188584223
    0x100915060807090f05040b040b040c0c020a050105040509130303060b070524040f0b0406110f070b0106020a0f110d0c0305100605010201060501090e100806040f03030b040203150d020a080712 83
    0x4500755a01640901d01120141c50070f50079454146824400948800344286030440d444081c561040d6a8901400300d04852f180d4420200030f115004002c0c500c0120361120341407080812050056480d41541e0503848038403403801080400080c40c00328000c003110344c0010214100481d100d0100200814010130400f003216046000d0400e0303500c0146400416a0014407841031074070303150001920841110342c440d010b03d00004450301d1001034120660b00c8088003075022503002603501e0030044070210503800741209100502c1c0950341541e400540355a400d4000e000080c0c0a084c2a190380e4400d000405206c2d07109800003111503481c42c140f607a944407500c10b00001703400e0840200d482d5205220755421500140d4907283d16610304403c2080c801c001601c52044a20286004602c1d60420070405004510031982515121308a0400500700c940c1e2101c039612030307401002842802000c2c85080402c004089555861100c450300c0051070540d01940282c0b86030103032240000b090a00d401b1458a100d008454 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 188586708 1250 188585458 188585461
    0x615091e03060c0e04020a032003040b060607050a06090b090c0d080d11041706011a070c2309010f1a0f03070c020a0b120105130c12051009150608 64
    0x180440200c0151041110340300c204042000450340baa00200c0ca00402810054180708141d00800c0c00d9900c105030a502184e15084c42030580e080f440f0100e03102194115009056040030303542c1010009010b8a503d1080c034002c18404203020060090400165204a007004050788920308102c0c10b80c400c44041d4020b00500d201d42e903250030f00610703070440700394441f000c0351810b840d0342030314402044800051030010344140404650000410344413140b800000c0001c1c406903140c066071800f001e01012506410320710500100c0009074130203000303006858850420a02c0030758400c94800b460000130040a40c00080364000080301301c44143d0002c242d6962114007903000f68158074403103592145c87d5540c0307048481003001414a500c516034080c4100c0c03009107036900056a60349141c826401c0110f80440070609840100420711781010407400140e52208148925800140701910136a00d01d111909040d0b25000000d03580341c07402c6002000342415040401c64154803509111640016000b4080070903100700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 188587958 1250 188586708 188586719
    0x40c03060f090f0b07090b0309030301030c060207030c06050906071a220c0504090809090406050a27021005130305030702030f031e0c071d04060c140906030603070306061509 76
    0xc1c404a160b00260810441e510070351380c210a28034002c12000400100900108115031550020b5020f075203060300564070395040d400c0c100b0500ba03171396201c10b0543d84601010400121400300c00301c202d840d5070400c1c940300d00c50f4402040c0302c1d105400303004000c4c09001800c803d004001644950051200d4240e09121041051650041d1070859001078104400c0700d81c2000503103469040849800e1195410504122100003c900d0b45242070318102d5120307071180c0070083ca6040f00c1c41030010081c51f00c40360115000700740810000456866002a0041c021a54155803050146088030a007407034450810f540b142d941c0c140725490303422221003207110713000b158881e03401c0d803000100b65a888090301c8588000501c10b0b0002310b4665014119030b0205010780e4000254100d2103a03864024218148605005841c1c00d01c0c140d030440f8030300c290032403e100c031039401d01007810040d2042e10b448001c00c2c0d400a50304d80396400003e142200550006100798102400840c0d1400c002143e14030300748080c0c03210750b151900c41 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 188589208 1250 188587958 188587961
    0xc012a0807030b130e0a0f12020c010e15030603121b0c060403050d2006070305070810030b01051c0506040501090b090708030304061d060c04051002060c09010c0812040c03060f 77
    0x114569440305909100313600ca03050316805035036824114012540308440a035648241440400380a0ba0140d0b10b0101402c2c086805016010f181442483c00035000328094000610301502c902d40d5038041c0e40e002c800682503071001c2240c02c030304204821119445002c1055480120802c0802c554805c2c0103190300b040c00c0b400c10380c09450959a1101c00b47c640d80f09000740494100f00ca0600e0009083d901582a04c0c0352081881a14015065642d011446103020317900604030080180c51110350061207003040001c01c01c80507641d419142c0407a61145508500d000040000c00140c4015106005080c203001c100b0505500803042c80344204403010440d5552030001e5242e20741403061021275002000010000b80065204490711541490301e040c4000c400d800e4140350400480c3c03c1c6023002000a424813070303440e0081144c8194010383c4000c00862400d01ca00001900503240d801d418010743e82004420040d00350191381490f008584003072518039090078400c12104941c0310a8030000d00d85424070380b540344503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 188590458 1250 188589208 188589221
    0xe07060302031006030902060d14010303080112020102100b030705040f020406020c120c01030207140d0201090201020f240703110a08040303060902180d0203161202092a0c012a080703 80
    0x15082c0c40b0030a1410791306402401c1074480413a070004c01001002100807503440303003040a03200d6030031010700780d811071070003810006068005800ba074140714255070050381c0c0001c078001c00c2c0400d040080b90030390480000c613241c46610b03017080d03070700509000948042400941c05003086880c03590131500040020018000d50508952614007a5041072044549030b5000760000d00406208140760710300d060f411109182001c03002161207005035110072003481950307410001c280603080380384050714100c07030092a8166801d402c910140200c1d50741000007100705000340e109131001542c001c04288e45003803103070000b0f00e00e2400f04c508401281c64030f1000305441070301c1c0c801c0d5901d10712035000025462019004228000e8035a81c0100e07490310400d199040c1c0d102d440203a05004000103500c0c004040d0086c410445207250003080004090b11040760360080c1c007440300d070b000502003001e41c1c10707035a41d9510b014140c007420030318000000c0300518150400d069162a0380624201046e87d031030390060b880707075001207059441 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 188591708 1250 188590458 188590471
    0x60411030108071a07060227040209061204060e0a0f1a04110409210c0611031e180d0c0b1e0601120207060501171203010501021218030a05010e0706030203 68
    0x2010906004e84002d810740d4000002240d0308103814264155180d40581c1c1c052000c4103222041c9445500103150100002d50501c02c00300d8080d070418516001240310303070041c0d950401d0a07244000216052044c507611040550f84144d0968030700c859103043c2482148c04965003118211840e0710481d12450840318401c1c05541c0c000520b02441d4444820000540042401924503012503031103489610b04c2283c0c1401e0206070f5450f0032842d19410b09120742203900003542400034034400c200308000c3c18460390070380c2420030b60741f407507241d41d0f45522103e01c201c07081500b801c1d02107204054015a1403a0000c2803595500e106070a080300720340d1003101d003003003801d07400582c0d000c1c40c8444400701d5a0740d80150440070303205031400c40042c14101c003601d0302c205130b4000703912460003c0c480150001c001c03201842400f0118404c0c06889146502d03200000b1341e80c940c0341d543d210500e000443c0d03003104c200300548402801c1900908031a80300050f0300700f09000704400d1407000c0322032140a01c0051811702038002d41b0300c10b0340c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 188592958 1250 188591708 188591713
    0x90203060708091c02071a07081e1b01020405121c200303010b03160c0f110a0e15090a0b01080c0a1403090c0406090908181c0308060411030108 63
    0x44070610155000c601c064406485801a09003542d034802c50004803841101e0f00d0390080c4440307441c180503020101284408002c807020b0410420002c6030700d50b011921190491149203052014201e4450b601d80180480e032036040087e0300e00c82590310415006041643c00450b007010052110103101da95502c0c0d4081851422414100c1e061100f40c002e6910500345910031441d9449501c00c1c000c180d003181e009802c100352780d54001c000e000075046446444180b031f85007070612507071840e041c2c0c4692138044440c110051003600c1e45200509a515502003000062180b1000e00b5614201600c4000d601c5403a010640c1c003030b2903800c000504140d001d02480300043d806031940c0321151500b00c0c808403107a0040c0454401d201d41c007400d2200c41c800040040d1320420781c0c0d801a0201002c082e040005442c520f50048201c107041c201e02c10003040c0c1440880701c403040d10b00e40813042c061290011501b28582d910f1414003110f10480e4031030505401040c00361050394100c4041040e2103900c0790420003401b00307010b909840d5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 188594208 1250 188592958 188592961
    0x3152c150c13030c081005103809120c01050403030c110901030f06050c09010905010509180126010c050306060a021929240f09040c061209020306 64
    0x444400040341e800920141c105071800c0903003410980c0c4140c0076401104d810840e560100700d0703450140251038082c615100f0030b02541c20000001c020800c0f0901031035186c04804540503084050035410180c401c4c8a01d9500524039129040c20041500301500c030074084c01031048103a503006800304a8511711381c0141c4866003801e0070344c4c1b012a0300d80d0341040c045848107071800c40700c41d16a0703440c90018000e600c075400443e0441070391b25050054a201038085e8030405820b1048407500d0381c0101244081d04c1007032803c10340383c5c0304103400100000c403041c00080140741d4410000c104402030403000382075544010f100c4c03440c9800012016080302d0a41030024002a0207101107401031070044014441c5020b0ba01c11595106c0c82d45035417005c0089007201c119042510307049400d4000d55003094005840c00748081c500c680c0d203010fa4004c2d600c0f03000101c64650000d84050140143c2d65405880303041400c002c0c00d03080907031a084ca40004403000c98000d0704c020441000c07c160364020783e07001c0c1d0f00c00346c1e03805070262485 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 188595458 1250 188594208 188594233
    0x12061a040603020901090c110f0109050f0303010f05130f050c1801091505130e09010c03050105010810151106100e010e070c11120102130905060102161e03152c 70
    0xb07000e1f01032850108984403022000002040040c40700d8040350100000d8203040c113191542c60160751030324802c1d454009200400c000c4501c1c0d2680f030121441900c00c000c080c06110486c50040c150441e000c41c02030303d03050034084101d000350003610314400c40b28200403040c003141005403000500380c820b110022907800d030312500c024401d90281503549050601d6188842d125015850300311802c0350f07602040da41d80e0407030042090703060040c1801490300382442d0b030382810111148102d000283c0120039043c50000a0b660b1030724411540c0c58807144064042e110303907082080c2035134002c00c400e2140d802585403102c00418418241c9000358003da01585880627001520750305e160301d090f51210842c0e80407104032042e154441c001c0c00180ba04940e1265040841400c00b40c4001c12100d000d0806411540840d401d80c03d80c0304046040020380d0500508803e4102c0d03009e0700060050a42d4000808404d071030755050040340380725001103002c9400f410311040c644c4403403401881544080409a00707164408a0603400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 188596708 1250 188595458 188595461
    0x7030603081b0307051b18010305062e0602030309100608030a0f0302040323060912090105090406030f0b090c06070305040b07172109010b03071e12061a04060302090109 74
    0x70502001001d481c18000142c641a061446c8005030401120041150383c503c3d28160101c44180c0300704410100155046845040d82d4035001450308513203646102428604030a00321184540007012419409500d8581000075169001074030030b042076214010000c014001d050260300107451f00300c4004e50800c01111400c07528840683c650301d043c10390802011001c54501c00b42c105809014001c038146029580c01c3c05854840020701c0c01070160044200603140306140d9048039002042441c00e107445400c2017000400030951a80f0041c2070341c1c01e044001c030800000c084070318403484207281a201c040001340140807462007800c0b00100001c4c1c04100a0021f079407101e001e0071300e40f40a1000a46600c00780410000103600c032003040360004080d961540c40b0f505440c000f803980051142c00038440324819001081d03030340311a0700500c00320702d0301200f03458900e40c10b0001a50040c010000e0310500c600b20341c10100f00529800410300d1910341d120042c00400d0603c1d0059508882c1d02410940d516072a0204160 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 188597958 1250 188596708 188596747
    0x2040e041514160e030c030d051b0a210806031002030915011415271201050a0f0c0219030806040905070807210b06090402060702040c0306030203060703060308 70
    0xe80c1550748030140d0002d8491015a0321500d0100032081d254010382ea4040c244007603140da61486035200180284164902040c0c3d02c04e004903d00b00a62035000c4800300c4010301c00007a00d420514030802e03a04900b844040216060000390b425205022412030a204a40b85d010846d82140c166000b440c44c145284030701d030300a5600104900a50b42240303807500100e08080c42c280d000c1801e6940c1a07117000e2640c904010250402c43c0b10480140c03500e41e100d040c4d01c82d1a45400b0950000310881c4000403038607102c55141c110240480c4000304100d1800c420014018408128068415031600003e02c007880c1c0006250441d16001007241c441070b0b1241d507001c40700400010429070b00030352100e030100e000603002c02c00c6101419450004d070440c10b060450401000488134968880101e81d0314420020a140300c0c2901c2e000710050700c10091035600c13400403900500c107104c17009410901d0000351000c5130364154000000e0b640300310207a480a8030751650460545800c0d00010f80340c00c0007000056441d0611b0f0b1a0300 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 188599208 1250 188597958 188597993
    0x41802041d280605220c09080a020d330b0103090809240f070506091908030402010521100b090109060c02030c1908060106030204060f03051003050102030901020a080a02040e04 77
    0xc54040e442d0300106442c0c0d51010140d400a405280603046141c40ea8002e04441a05034904290408e05c2c0c803428940d14030015074041c1c0544040c0c0c21034024050b02083c159014202d140310b50a4040d10010104680304c03135444485003607881e000b401d031070704c0d0700c240503040381c65400c1440241007800404c20030107a05c2c80f604807500c8030110710803600e40d96041e1402030010401c00100d825114122410314604000c0c0051070500740c1d401c010003040000c1007000c456000207401c20703503e548075903481c80165080d1103489070b100d610320384011500201004d418031680c854146024000310341951224000d2080c02050000c6000c608020401d00000e84280041c42201e400181142c07081d840000c08281142100c1603406040d0f22001c1082c03001078410000540101618602186050b00e0041700070004030000e1001010151140d012444884a826410010359000702c000c5550303092800c100742c000e600800350503001c2980880018090052442640c0882d00001241e211507500d5640e076080b10741042c1e044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 188600458 1250 188599208 188599211
    0x30e0102030114041a031b190803040312052a0d0806150f0403080d0605011e020303011703071704140405010b120711030423040c0f0f0203041802041d28 67
    0x9107049941c040010f031a01e201000d64205001f0410f00a0140c19800c6801c14510000c080b2400c000d070890000450301229004070b80141c41503c411000c80c0c0501c64658400b400e1a80307050f00d07450140800355201d09a10810b012101115900b945c03d449c403000498015a22894100c4ca40800ea0540350041031140043e018031440c185e120794800180d50040400c410700719035500d00610a958114000f07403c180309040501003010072400f4001c3d43d9110502520440841511005803894001c2040e41c0c00c0a6004603090203481c0c0b001104055078005124400790420040303400800d90078544103490582d0341e10310800389042c03880340c000e0414846c042d0441007000540f50120548520a10241001d0320054901408000c40c5188941520313500400403445180307082c0304240a02c0d0405842660041507040804601203442806d904502071544800302d110100f00340b0355000031b4168000c109403a21030450400c03c03000d03807100b40c0d0800000c8031015469001010758078106030005c6486158250340000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 188601708 1250 188600458 188600501
    0x8090609062a0715060b0313030507030c020d0f0506060a0503030d0506010507020d0f030305010501030b01050d09170d050105030601061103040b030426070b07050306010219060e0607080403030e010203011404 91
    0x16140c195502c455404d0f03525407901c2c1107158051140c0d000e480c00030b28540303c000d8218101003080c0c030303000c80c1411401400d01c000026a401010b003e034402c250f5590b001055101c0003143c40c104601e007000c80100444041c02030000160310392414032100000d651001e0001e500b082d1140200d1002800050041418040c2c00c0c091540140d8603181c100c0ba5035880b811070180c401081d0300c1c014040e070760103030002414542482000e60840c4d03840001d40c0d03000400b416000c166594075060407450961100c3d41c420406d04005a8480701e82c1c282d422280c101c400070b604a42d020780c5c0c0d458084428422101e60403000da002008100814050301024680050150f0074010f40403081b14040c402d50140800d248460f010041104410b001e4607110301e036405039050902d14a0351622100013902c0341100c04158001d01101d1070300c4800c0c0015075003c000c08603051000c4441508100c50041c1503080304503030481c0041d04005604101440c18002c0ea03049801d81e401026540c19560b00304405000c481d402d00c1d070f584c452030380c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 188602958 1250 188601708 188601781
    0x80c0d11040207050f0105010e060f211207020a080303010506030c0a030f09030e271602010e010501031103160605030705070809030114060f0307030b0103060207020315070f0809060906 81
    0x300918800744204d00400c1c00310101400301d801d681c4168800c510f4450355404010301a282c1e400703a1141400c0448446580d0300c02050b21000c00010441c5000c4180b2940281164942019000705400e40c003c6407a8405070b591041705590320f1200b4055a9000401030011400d03001c070050160103000e00d1405c010408a403500c032500d007110354500003980000c0601d481082d01e070030549800c041c0c1c0e03503140044101c254600d40a81d0b080706406059550007010300c50340c00c0001807003903010660002d800d400034017007542d42c0e0038148560000d501141c2d11a00035040101401c0311050941021541c0540340c0900f143d0b62080c00b580c1d85c0d080741d20140d84040e01009400007681d828807074013102c94030080c0744400b81d061260070301030141c15010a01d0f001c0c1d8071100c0248085081c0812a40c112a0300c20800750342c40c110351010070709080091141e00348050012040c000350350740105851022500300d686000e010303940c41e0b48c0583e0754034095418804981186010541d900c41c0921040d003a50740032801a68012400e4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 188604208 1250 188602958 188602961
    0x2712030324210109031704120e030c0a030f0501060b130608180d120f060305030f031b04090912091202010807050f0a0305090c03060103120e0409020901060503091501080c0d1104 78
    0x50341e01140303503550313083c0c414100354104500214484a02004400500c1c1a5a800c00b001408010000071b0220b07018107003045660800c0301c00e00800f000380900f000c841e6039203028004c9400b4880f08803070355401c101c8086409041d0b08152072a11501e0360b100e90500c0c0c13030a882611100d001600309440074902d42c2058407080020441840100382c0c60361b405501500090050044880e0305404001c203604040e02000030801c000180c03080101e80c2071802c0d540c1d8491030b2034680043d43c0c101c90301100c0e600200c0c001603100d049038032200003e40580c5890249454141c02119140c0c1e00d401000003006103070b40904095440b0396031043e070000040c10207500e030910395001c20409802c4442001b00094036042040f0311920240044180c071201500113003115411652020310385c540c0303420b101003080220802e0282c2685d0f20340205032801d40191080c0c0140d6100c4400038802d500031140c9003494480c1c2481c01c4020500071111030304840301e41d400b0700450555041000b00202140bc003c3c0c0d8405d00c3c0c09480d800c1035131903 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 188605458 1250 188604208 188604259
    0x31303030b180f01050105040612050603010e0a03050304060b091006050a120617160806010b0d060510030603230606040c0507020414041703090304120501022712030324 74
    0x2510b00c200c0030310f00414403005082c0e051300a941040320600c0100031140d04110310030001503645102213495940e050100e40100300f00d440550141c4580c0d02e95005043e0024001e600449c0201d90602202c0000d40c24000c0464007501c05400c00c01240c0c000304140d51145026001c04201c1d880c6c8200c80205110401c03041c5c1d1a250088029140c1140c0c001451000411410000c0da0114420b50000707440c3c482040c1d115881489a0030f1075000001d1354044200071a8000c070064a401006105000d101090003001072915010440f25003040c104000c2c403004401c00c601d48101c42807401050b05607661014400642000e281400c1400010320901c00140c0d1180078050015070b2000c0100700c149407608185016080a40b280e10500c0c80c10801d2000c1880040100c6003640d41c2e030b003568035610f0807a180c83d40c024861049170001315403003100e0780c450418402c0d02501030700c4e400300c5640340400040700106442e0302c0305440c0c902e0b8000382581090240012003503414550840140b007005042c5c01e00352000d40e00c00740b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 188606708 1250 188605458 188605489
    0x10207090504030314091b040510050f0a080a030527031f06050a0e0f0612070b03062d0406080102040501021e01182f010e0405180a0501140a0b0105031303030b 70
    0x112945001f400028050100400c090842e401e001e2401c00c0c0004030400c183c0c030b01130180154aa402d009807103031580b0300c41c8801007000e801202d40540c46801c0040241d00300803480b1500e186009e44508000406c1c0c1070402c04c0e442c008010b01310300403101007854100c584940b034404d021511036000080a603a1851440c00410b00008500750b90300e040311540d848042d0083c1a184504181c0f069800d1900001443c0310546101011442d503944070140003506030284100200000c800c020500c08030314520011a9038410000c2da414000300341c03225152400c0c0e02840c01502e00580c00704103008028920107003034a048030091000002c495100c841e200f44e01e80302051098030a40c20150f03084100401c4942c164258160110b00d000000811100007443d0051041c1420320540d101c02c041110040103024400d24144140112006110b1034a452806402e41c500b451325101001e80c0010328031a402e0103100c542c001c050351a01d01d0741e44c892940141134140108241c04140e590001c0d007009813212104400e0250 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 188607958 1250 188606708 188606713
    0x30a080a0f0c09080c09090601030308060d02090411090a021c0513050a0f0308060301090b010b1c062d050a0302190e01030b09011b02030a0e030a080a0302040f09090201020709050403031409 83
    0x500340800301e8a00b00c4030f417564600420040c1c081101902c40071415a040d2507052030044501c0c1c503802c0001d00e03034540052010354030024000a101c10051045021102c9040544000344d1a958043c4080101d0003174884180072912035100c60044060594407071a4003910740c1120105d09406a00c841703261101e081c1d01111b42003a0a10b810b402c0c5608091107540c0910100d0080c0031304030942d920449e81d40d0b018400c501c040a00400c1260404981941258032074100c1c1c4410088103030303510a400344810078001d50781b02842d941100b0550078a445ca4400082e524040c040301c03003c03455507091002c084040d071404c1000041000001c5050f020951210b4002c0d80644005043c50412001c0a400c440b0036100d01c8440c110440380c41c0c52071a0300031007a609143c0f03003401c003202c0d00802140820b04109031080d00034090240007035050030058041d40a0300a8031440003030021140e8581f06154202c5101a5006c0d003d680541010040c4141c0e0350049035001d4400d140220702c0b4405003c07005901360003036400c000300b074 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 188609208 1250 188607958 188607977
    0xe03040314010c08010f0f090b06070b070306060e0a05030601050d0f06051510020c0a03020f0402160602070303050f070503161b0c090c03230903040506031008070f0503030a080a0f0c 80
    0x480e03000a5503030140c681c0c06c08152450b450031135000d0402005105041106031119410141c50380e0b19410f43d42003d400100c0c04c4483d2038603020040003841503001d00004a500c1034800741480c20600141c1c4c0540e007024005000d0b82e409c0100300001e440d11190225150480c0646031000100039002d40340c0108880b02040c1140020030040040611f454181b240465021103080082d40d92038007000400c40743c069a5100000c0d920b07802044c003a204049a098400c0b44008807401040700356401050312500940d03040040c4e450301150061003070340946442c4001401440810f86d04402e01203103c8010134681015901103a85145030070755000007060a179a01810700000b00301100180c0034000040c90513103020031024070107d0502c112048203540692580c5111000a07001c0e180800c00c42d00076002c001d000944915103522142030a03003c034003c1c1003050103040f000081e0781c2e00326030034102641d100602031820b103041003204840700000181105050703902e50001081650003480344c00801e500903070b0b480c0d928 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 188610458 1250 188609208 188609231
    0x418140c01080f0f0601270b03061804050601060e032a0102061b0412020f0a0b0c070503060f060609040603080a030204061403010510050d110417010e0d0203030601030e0304031401 79
    0x4010010a0710920f0b00408080280392403041942c02d80c400400d0030000c0321400341050781d5603814121900e5100b25030a410f00400e0039050200910321500c2c080b0b80501c01520080501d092402c07007550024041c0d030198005200c001d0042c42413614a100142c1103800c40380c00d004481400c01d00c0c00800040780701c0c052407250001d5030b043c441d071030f441300300001503609c400c003018010501c80c403440c8904914035210034036020855550010000203044014014488a82c452000c85400d030b0100b94003400c00d20607400000b61900700803c8a40c4114251000c0400c507590344004c0c009a54402600700394400d03541c6a008c000140c9034405030511003203a660040e00c036802c1007405000c1c126240780b421012142030004004c295101c0110145101c01c1d450f001e030303d484621800c00c0140ca02515050000c94001c51b0210f0070b0912401a803100345104030083c1704440703085110707a84900040c108000140c00801c002000d55000742c1211408030200d20450b40707815500c4d15013018022a100c10342602c1d9440303181c24031a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 188611708 1250 188610458 188610467
    0x3020405060d0309180615081f06020d030203060609030a05060a18150c1206080a06060b13030b06030705090a050402031e030703030b040603140607080a02180418140c01 74
    0x28000c0003510801502d4103030f5140504648414401c40503203410381644d40c520450b40e500400700600c4903604000c0c00c1500e41e840605800c90031500c1c0d080001030705130380300c0350303039040645107011204640c003c0d1a105400300f100720007a50004040c1034011904000c2034030951400c0109240c924028405048281082c0400c5403e0310205600f4038040103428480f00c0102c1d00c00e065100946002800c005410554000c040e00c0600300340ba481d1903c24504480028924400324562003102e214480400070107840d01c0c481c001c01d01400c8101601d2035090001400081d40d0a07007123940101006049584007580c5030001040540102d44074860303103842e1002d00c821800e0400c400b2426046610007400200f00300c01078541d5900850a000d420180c80381644400d41e1107680c089405950403a2340010140460f0324226500c1400352081c400103000d80f800110a07042034401c3e2682c0308020308015465003808001c000207000d107520690f402d004070f891031600050524200c50841301c2c5c01c7d4044c042c0c49011000241 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 188612958 1250 188611708 188611711
    0x6130e0403080403120e1209031501030c03060606090806150105090307090f0c050a0c0b07090b0a050a11060c040e04020414010f14030c06070308040507050901080f07050d1a0a1b030603020405 84
    0x1d02c8030341030550706c1144040100d4264050162081100d0b03c8040120009140159855420042005200021041c4111140d81c07030152400b80d00103018881d40d0303a5084446841c0b0341708800c0c554102d0004204101640600101c5c91401403402509180c2d804000a0030510540d0203100c1965903890389642280d0580528100c80e406414035074101302c0c0c1d00d040541064800342c0001c003501072040c00100c01c58025100880030384100d8203090f480d041141d0001d01554091000030000c03070500d50a070301d01101e0010343e80e40318854065041d4200382c038084a540710b026024008981c400c2d02d8403842103000c810070380c4c514001d140e2106181405480c051501e60141ea880348698001d030442410b5000c213484140c1241c0d00301d54140b425042c6c3c0e5640b414041d0a0000301d03081580d001209100010324600c2c00903280e03d508000f01c0c26901000d5403402049842204400001d058090464060490034a8114155030101d0150300114040c00c240f16600e07811300d40c0442c0c540201c2c2c1d80e1202401542450310859 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 188614208 1250 188612958 188612987
    0x4050d0f0614151f090b130806070c030216060f050c1203040302010207120512040f030c05012c07030c140a08070e04120507020f09180a0501092105030606130e0403080403 75
    0xc201c1c2401c1304002090442c0c240100c52044074001b40a050f001d00640a1100074074808041d00d45505052500170940d911111040e4018803504000340301303000012107544200c4000f92103490311071960090545481d0052481041c807401200c24603d040c1c40003030002c510440c0320340d00060390341040340b42000780306110035400f00c204802030009581520350b034401590401e0b044503031018010201c3c6011200300c0d18110b8010402d500700b2041d14080c1d90b008100043c46e0364a00c80c1040d0b21034203540082e549503210720004e4600440f800741040501e5908844483c11507019007000149030312640c5640c5420402d81c400c0b00305400100800050000b900200c950440c01440d0003445c000140d000581152541821640304484203404110151070803805418092460703c140c48900c035035410014000d2400704029500300300d00c0441035450440c40c0301c0c0c40c0302e40c0e80c3d6521150b0540d10f4000600016030840c00545002492030b0801107404840c070740d9001c0c8164807d903545011443c040c03a0040809000380d502 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 188615458 1250 188614208 188614249
    0x1170907030f050c090903030f22080a03060306050106050f090f03010b0d0c0807050a05102f0f070905070c0b0606130b0a02010605040e03041e15020609010507020304050d0f061415 79
    0x10310240189e80004160455044070300c0303e0508290807500c00078503042c440000e1110f8000103007191b0194040e0011011a401040200010380e600c14098400c1d21450907107a200f124108003581c00c52401005102202c90040d0000401d44481c60106001d41c111a00030303140403404040800444408001d8040580303400e540782c0d014586042c1c04100c17505e0040081c13000f48583c640c00400402154036640d09072800c08102c105007406d40740202a2180d01810000d55207001e41c083c0854540540d001d030500552980d0b5540070b030300e101c0c1e40701c080d2450800b5080903030040c000c12101c002155444031041c00740542e187c12690310343d0b9042d4040e00b11001c43c0c0c4250302441c00c16002c00196640481541c013100d08156480f41040d9030b5000c25103548000f034112a41138100320780421781150340040c400344500c0100c4000c10040c1c680e0103041e41c1c1c130f0049114032503000c126801d03c0b00c00103000444507402e81d481014082044403041c000d0101e0b10008035854245400003100d2007074246001805480c11603801b100 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 188616708 1250 188615458 188615461
    0x4050405130507051f0309060f020429180d08070206070809102c01020c0a060302030103150504050a060f021b060615040b0a050c0f010207060207140c01170907030f050c09090303 78
    0x480d05c080341c444410100034581d035090041c050060136003020000d50041e5508542e5151140620302000040c4200005050003004c0c00300d044204020458060101902040002c90345100810103c006400b0045440f09000e010b032a0061320f52002a140461080d895185c0b54584101480103c440c1e20064200704042910501051030141d6018080c80d6000b41c3c03880c80165018006034a03089040711040d800140307a02d0000f81d01c03641036000d14140e91040060892a01440c01100250707a001c0e07402404540000217041e0008055600c1612100b1304d00401605010122034030003170f050280303211106203400c1441004103d140080709540507a81c0707522910701f418209070b2001e4003402401a40340c140030000030003100c407000401941980c0401d0700000e55071440300c1d16115020f500701e00002c030f0b090b9204029900d440c40313011404611540060b5540080c0c442021001782008001506106007401044404000700d0503905071040068050f00003000e01d4444402800780001009096000d035800500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 188617958 1250 188616708 188616739
    0x1e0b0c12090109230c12030406090602030a0905010509040f090b0403020d03140a0504020307030803250e09130c0513140f0f041101031b0810050105030910050c0405040513050705 78
    0x70b2118100544c03a46031000c041c44d41c6444a4a020101c1d800c195020b0740c0b540540301304080c000300a0041d2001aa14115a69034444041c1e03a03d0096000c8000440c400420600055224001801051000a20200c1d04460710035061040390900007080d5030b20000d041c1000207041d010003408448603128038040051032054040e210040f20040c041c29030460711840403400b50369041040101030340e003050031142c0c0c2e418500a14086a074880318002440c054042204a40300d0084038a40044000604961810b540c0c5501200c003d000003842124180045840480d160b10703026102ca00c80718045500280d9082d180242c030001a00080c1400c9144141c0030030460f5040c1d14603040f98001740d0080a200c1402000e4006030041c002401d00c2085d00c044403001080102e5002c90300e540140034256860700e056032590011109444120340791400d603880360b51208000400d5034010303640130101030307041810591580006030640d40300b41c0380e46000340d0f8031011900c140481070083c04010001114048190042d44 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 188619208 1250 188617958 188617973
    0x703170712020705030405060a080108010b09070903081c020a0906030b090c0403020108040327050f01090812071403130f0e1302040216020a0f060306090204121e0b0c12090109 77
    0x102000c1c64407a00403c050081010403c20780d03014040080845481303e1810100500c41d5109119014696007006d8ac00e10740c5003000211140210910350740c0105050960311841d0150303004103020104883d0a170034491903000c1c1b070702c060a429102a40c0380d00c0303058a091002800e462064190500c594900800d22a01a0025040b00d0031030b5820300300682a50344906090303c8441c0b480c010801c0c100b603d258191191410101d0302c80c241c4408552000d0082c104c0001145d40a0b298010294030b82c2c0031410303440051120070050409240b24a102c115900c155032410b41c215000303000306030160580b4030300c1807084c4c3c1545020700010b400c04690152080c50007040c160b402e48565800a0301440d07000900b20941680003840310146500540032000440e598000049012510f210340f5000a15020000c6044002802241c007101d8040000c94081419a00c5003c40c102c01c000002d0400c003a40204400002c0599040c1840f40c0e040e004440d8507001000d07100d50000350028400d55060345400781c0c3d50001400c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 188620458 1250 188619208 188619227
    0x1b050301062414030901051605120a1a03070f06030506100e010c030309020d05060411041503120c0b10180204050d03030b0609031f0f061a1c0203070507031707 70
    0x703100242c4000039a2405650000816020350803103500041080602141500302c02d0040c2c03129a8120044d510105e021500c5026013943c0900182e070310000300705001e0464004421504ca40d180c0017010b6902ea1001a282805a030311202003210b4115040090079058400c040d07100206032903a0400d88000c02c4001c05603070305000f0060500020880c004280740c4203500000d6825400342c02c00c03070b0301c20490600c41d9407884116021662107000325001012402e1600507001080ba0b008061010541950303200070500c7c18600310380b810030408000d40f0003c2900451074900900c55201c41881503410801050310b0720b20058007414071940104000c00240c1c603801400c456003609441d000840042ca0740001c0c07414440c02880076494441d018140036040c6c00c02c41840c800b245014001c00c140741c0e04400b15004d507130740da01c1045490420444010b4504036640020b151281c03030f03101d104001070031501c039440c01c98000f9507041f000224007091040805400c0601030410209660104407030345006030740140803500c03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 188621708 1250 188620458 188620499
    0x507061e03110702120f01052203050c101517030f040513141e010e0f040f150903110d0806090a02070204020c03071419030507031b050601031b05030106 67
    0x903030303540c610315604032082543d80096008002e05038040139848440e5888071070102d012210b529080c0800c000c04250300d000010400861502c902c1445180c0b02910301c0d81290f442c082c603e0082454243c00c030500c1d8810f68000c9d09010340003641c40d038208030110b5011002c000c00d10309140d00810000c030600d00314001352000c4170003c44107940f803d01202005805007028200061095000c00180043c00120400f041c0211f076011060740e1241c0e98440304041c00820940d0304da101034008402060102e074500043e45502d60040214801480c0960040c5044849242056001900100381404a0503090044044135005860005143c1c04d001000555608014001d100403036030000f045030440d152601581e02d030600d082d0583e62074000074100344003002d4003554150694010080071800364211141d18980042c0c1541c0e9141c01d00c9120f03901540c04c55811f401c0300c00c000301c0d140c0072078000500404c8064040c52241c2e00b1138481703e0515150010303032501604003d100740d040110500030050761409a0f0b16030507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 188622958 1250 188621708 188621711
    0x28082223040c1101050403030c030b04060506040e060a0b0403030c02100e09180f100b180709090f020d02310302010206040f03200a020f040b01050306040903120c020a0507061e03 78
    0x4486180940f070000d00d6880c00c50715542014108801c6c1600341d405400041e1068409000158440f002c010454000d4015a44e02640c14002880b4020440c1d20682d40320b200604061200da44411038407140c0d4202d80d00840006480700d4110046040c000018061290300342802c04070b5603408130008140c090010031518164420204141848004101009201d0544026038251450040300613016000c0707034909078003920a001240d1843c0fa2021103042c0709510030341da1000128205034408000d03114048205401a400780728401900300c0c3ca02c014100b204a4110103000007611141009604501d641180041d44401c5d00c00c2015036000f156a5510582c00081c9603000d0100d440c06a03083d699070254a003101c101c0f4000d43c15600b00001d500c64816000320390b000e4004640008100035034441e81079042c00120144089451030415030490b810040c071a040070001031840880d0740049808403011603005070300c03441e40c20090042c24820b0802900251030085519200b18841d8511018090344580415 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 188624208 1250 188622958 188622971
    0xb040b0a0804170a03090c120b0f06011e0302090a0b2d0c0a0503070606150e04020c010f2313050a02010f11070f03050613052808222304 60
    0x14018502e410070340a96000706032140c0c02c08034000d006086d16a42140c928030f0780003012800b002c801071600992036020604003601d90320354503503503244031018084606100217082902814640c1720039200c0440c5141da001030710380021008021281c0095808181c4c900400c000c3d00c8800102c0407a03818412694034150001003641e0460b8070424450800386801034090019184100031001c0002d2007110b000308010300059072180111181100c1000c68a13000c0341d000030a0074010b04054024080940108000040440d001034035142a030348580107105072604407584032084000c0f2103d050390828034400000c040f42e80fa580d500c80e80d841020b039010303061200f1580c02404042c411000c3d0103985000c4025078501c0c9030b451618409032110f03400119200c0c054500001c02c031002c50320701c440006070040001e00e036194034411601042240c000c070700c212000c8102a4800400d000d0030003031600d0b64154110300ca801c2084000f00124201c144c00800c000d0058901d0090701801924020001c07007400c039030001d0030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 188625458 1250 188624208 188624213
    0x2010905040228020706020c010e062106130203040b04020411040308040b0304030806030d08010501030f11070f03170106092c070905100e06030c0a02210d060b040b0a0804 75
    0x44116600c2160301600001d002c4012100035500c601001119000140d04003c1580099850380083e00071103005a0141030740d0041c1c1d62040300c11085000780500414540010681c43c1c0c00c0d5154800105248a0794900c1406040e040000b800d69054030003000450071030903e07503206079103100c000c0d0020340700e903444800c000c0e180d10849084400030f40d44a81e28540e0380e0b40e10801003903150012241a00460070603400554141804201000e01264568034100c0d5a030031700300194001c1c59a518a440340320b648001240500c208840200319a901816030880e595080e441d000380941c2c200311200301d841d24020300421000d0341000440741680c290316003801c00003071402c000807101040c0c8480010300c549040c3c1130200d0705800000c1d8000b50380050742c0c0e9411504c0210000d9400760041d28100303801a80c1000000d940d1a40310020740000506441928000010980440c0c2d01400c143c2241286e1940000c0c0d02c244030290b071041030300904480c4001400e10340790561a0b05140503003060041030042c2a00043c04 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 188626708 1250 188625458 188625467
    0x50f3106061e0608010b0705060a050702071716060201020a0903080702031504060504020907020303072012120901050906010b0d090606170703030306050607020d020d03140d0c020115060503060103090201 89
    0xc1c20115015880c0ca01c0c070301c4154000c92040384143c502281c0e2a000201e0600141c00031503000350780110080031b242d00c0d851901c20081c40001d0804003103004d03031140030500c52041c2c02c044c40e141c428003000740300005400f4000d05a024040e07119030150788c41080030351442a00b1200210850350411700094845000e400800e040c000313900051804010301000f08010400c0c80d5124134059402543c01902e10307a24181c041e41d5074402a144800484c204400b50255501c0d209075100c000c15403442503903200c42021600351a65000b840e0010b50300c0400b28108020f00c5824400e89521000c4800200605d501d803200e956208e104d44494101c1c6c146c3c070744081c0414490140c008034000c1081c002c903100c11214100b4020341300d1400d800700710002401c00304001442c0c0b0b402004e90340015002088941180101c0c1e08111201031602d808405200030700c01000e801c004a0406072a03440070701031011911002e801c01c02400c40d9183d0043c1000c547c40901c0500403507174030002387c0f58001001c0c28001100c0356240016207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 188627958 1250 188626708 188626721
    0x370c02010c0507090c20060c03010b0c0a020405040311060703052a1b010b03010c0309020604090e10020f0417030c15060604030c08010603060b09010b030403030f0906050901050f3106 80
    0x80690b4213284081d100c20b070340f0110b40e00741c034002901c90301d407030031b000a034041e80b0741d41c09036554240080d040c8014003200c0c0070381c8014100540d84108440c82c0442d03d0b404542962000c907800e40100300c1400710909011000d000d41a403000c110700d8100314501d8020403400a8421840515a080159034060401c00e203040e030403107400c0114600101040c2d003942c0b0503680030b810b115060601035400c182c1e4000c4014003900a1604040c1d00500c06030a15080162403c01041500030403281c621800300d070348405416a1000b014403100000ca40340d600c9087c40e80e00342c448580a100c42c017999108210b1055080b0000c00c5507070008256a50420b0f054442c0301c00683c06008a80014201070032051000501d46070560090003141d2280d54140071a071000070070020110f10074810f13200310400800004001074805e901caa000c001c1e00840020300a0a261581c20846000321466404d5a41d03900503c10107014400c81c50703500c08a41c1001020341c2c6031164a0290f40f02d100c81200300d14500001c48201004140e82224 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 188629208 1250 188627958 188627969
    0x40f0f0e010b09060d090506101a0d02090402090a03060b18090a030309020f030d030e0c030a03121e0908091f020c12121909080106030206030106050d0e03370c02010c0507 75
    0x5000306c0840307003446515004181c50b0300007102804000028000b25001d521122104190703640341c1811100480c010180d40127643c0d190f40280d081000314801e03030380d104c000c002541c040d0400081002c40c0d41c0500c04616040c0e401c03104132010707440800000303100000b030300c001a80c1d141c540458040071620116001d0510511307810390600a04101504982d490f82c41a250522810101c40c6048442001d041d280d40f00b161001d000140a2051316000c100d42e900138564600a1a590310109a00780044504490500c00e04980d4454001030822051034812030521880d1444001800a0300c0728040c0a540c8005c0c000d0400c0c000c500000408d040c0080910682229060030404180d5549203248000001d442c017a4945010680d07100b40401c054070144144000d032507015109a240d80d08040c82580c01c4d800140c200b203083d9494000c8451407200c107002030001402d040d40b4610450324600354003064203844c2d0180341e070002e501318010208280e100700b810702103503020b0070301c0d016040543c10203909019003070f0050b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 188630458 1250 188629208 188629211
    0x604030f050f240115020a0b040c0e0705040306050a110d110409020307020a050615010801061d0a080706020706080f010e18030a0e1305071d030304170102040f0f0e010b09060d 77
    0x183c81024540d4501c0f0b182400719031880ca43c9a88440341c41901c40829141180180d20110300d000000d004218084e0b0410b001d001d9409078295a544420031100c400c40d40140010707004507082007040000c2c02041d07004205281c06001080070f00072280d45901600f4400d0034419210104100380214a80c00c8602800c0c1d85c107015540c2e031038921406035980908a01c100c842c0d00c1041d0014401e5104c40c1c1c0c00c3c01c051a4140d40c0d040141e440d02108554141050740f40440c506060382e107821240d5110200c800c010082c16001c0c007999442c05c0000781c02c02255600800074000f07003204124201801288003070568501c401c0300c15032510768840034600130b248d070381056001d03100011b60011070760b400c29004404441c1c122010f4505524100090702580d0741910345501048920a02841d440200321a4402480e8094100c9081503942d40b40a20700c003d204180d2160b0b0b0358002414003007524a002c144001e0300c95141ca10b28003600e0300241c41c8034480c051050700d00100b4007207031600069856008998a0000a090 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 188631708 1250 188630458 188630473
    0xa0504051f15020312180f011e02070305070210090315020d2712120204090e010b0a15030c0c02040218042a0e040e010203010803031e01050604030f050f 67
    0x202050550240407410641a00941c0001c0c056400c040031034101c1d541a0702450800e01c000100c0c0740c040801501e014425075100d111220101c008128041b0b1800b00800042204c40d40c004007000501949201e94250900421460010035001402c0310b0380d6070744c141e500d4000fa111340e07281182c509442d604000c00d9807a40842000c80107989801800b00c49603041c0b410001c1080e03855020794140c0d4607405d000c0e084a0502c07100303000300e000032048080b003603894200004510345400e00042281c0c00784c1c116403243e954070000041c40c4ad009116884520005488403070009040401196000342c081d0000401c05490303401455040340b141d0a000c1d10180d000c2e0044d510345103066120101c0040d08001c02d8003a51501c0c00c1d000c5e140744172107444d00034171401c0a030000111116885c116a038050056525400540f6881880780e07051007440154024403109020355101c3c100401908000300c108103942c205c01f10084014000e0796580f0b4119400c42c2d5100c0035040420702c06140503170802c914101c0e00429401100b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 188632958 1250 188631708 188631721
    0x100504051305060903041a07060905010c050a03061e030b070c02130b1305040c090c020f0d030605180c030f0a0f0f0f061715090709150303111c05090a050405 69
    0xc40c0341e405600c00c00660b445a910440c07269681e000c0d501c40d1500803000038a602d65003a645800402d45103005000210307004409458850a440385c41c1d51190000d500000c080180070760621408016000c12211a00a11b462144810004036240000fa00b01c0303000001058050f805a4401104207a000d880c462003210048000e4006081d40c401c0c507406449007007100d08480c00c1da072042c94401e07030b0301040803624281800705800003008650407550551045a07641d031220501008041c00700d00c03543d64049206410001804042003568080c4e2402c203900d00d0900c1041400d1005690348003150700d00309000c0759141c40041c00a4007008045202e01d41c80d00c00e50350400302c02032300802200720043c1424807030b050382d500080210440741c0000344d07599000154142081000155403e03081001d6030212200540c03903104e00030031180307c00400c10300e03c0300d4a1801c10030540c1140c60881000c3d00c001c0a400030503641c07071070161102840d0451004102000480707104e20340e94102175102800010708100031910340314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 188634208 1250 188632958 188632981
    0x1603080403060506010315061b060e07030c0b0c030304031d0603091b01050f040e13051002091003020903150601142208010209060a0323040f020a230910050405 70
    0x18007050300d509040800140641d400f81c0120150111903104541010f80781090449213599120313040c903c0116210f00c2540865954011880c408003900050115a0f24614201d8034418103030344076000ca03200c00e01c0072803d0071401109480d801a01810140c2803e40f07800c1210402d1400044856440440402880104a00041d424100140c0518000341d5208103a0041d10039015179548904c04180c100414003248100d00c15154111140c154400200e0300d40c0d40d51541407440300e40400c6c00721a4082807140003464542250b07a44a032423418118a0070940d80c01003901c500003410170038507028003c00482c5032644120003803100032000815490316180e170701500246844c01c607010041030200020b4049001d0781c0c1807003102c540c1c2c04010081d42c80d000160500341c025101c140303d0b500b2915554031006030381d01c030054007541c481d40c41298802d08141140c41000b00f008501c2e00803180303501c8000246401500482e50080801d003040b0380c202140d545c0d05130320941300c4145400064005081000f80310740c0090300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 188635458 1250 188634208 188634217
    0x82112061c0b040b100f0b0f04030203070605070b0f04020603130f080c0d26180106030b040b07300902120a050c01020709020c120c010209030109290f06060309160308 73
    0x394942000546401c0842d40c0f110540d801b41c0c1e0401c050f042020008001040c00508541e5050110f42e0b007000e03035940000781815443da01800114a000500d401040103803040907500940202d9014040e0078aa008900382e4007004080100d038001940180050012411544001c6a031014049a407203010080c840d8480d030300b100f100404210706c142d0010259032a4071400401c0c01e034806606229030748041c00c0b0342040554030000840e55682d0280400810b00c1031a40f43d02c51405a10301444e24200301100a16842c1025100c82405401c00311403030744160b981c2401c4400200306900401c071040c03203000164084030540d8401c2c4491140ca60418104040400ca0b0701e0951003d8095440041d943c05c0b40506a00c110550242d01d500303d00c01d41c08400f504100503010500390f100006040090321004282100c07040181070311044400007045910301504c12005103002415400b0b406a0306054822504c5d140c4041c01c081d12403100071000840d4001c1c10003030810a04030f9500c600c0e500c940d903401d04d128154003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 188636708 1250 188635458 188635463
    0x1c020d1505031b03030d05071701060e12030a02070603112104061112130c17010b03010605180c1621080a06030506190204120c082112061c0b04 63
    0xa03c02200428428003030340c02c50b492800303405945170044585150006201c010010402e1055005a607006001f080381c0103400f034411030711141001051079040103402c4030200480d50f03181d4400c002e14034482d40d020500004451817401c01007034181e1050100882802212201c2044c0120b071a0486091201080080c0c00b590290342d00300300307003400d0070b0003070055200d000e00c0081c6050914021440241541e100d02140601130740b03810074003503152000d104040e04070741001800c45c2c4d19000488240c0c40c0a20070320004080881d210400743c01504290b2915810003089600c0310000440e4019065186c01e00a251a561040c8880c1c103000001c4144090102c0040b103020010340c2c1e010000300105030030b200300410b0b690044010042d0b17948a9420712606600020008291074082c040059142d0264940d18003442c410580c4ea42100d081030b6030146408401034000300351000181c01e1844c5082d4040446804800c00c4440e151581e07200d0f4040769017444000c1c2c400c43b1100050350180140620039140c24090762 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 188637958 1250 188636708 188636713
    0xb070b060a0f03021014120a0b090601031e021602040203090307260313020a031e0201020609010209090c0c1c0c0b07020c06031504060e010f08120309031c020d150503 73
    0xb900c420700c4500e4440745000c02074004c0705422507411140d00030109000c05070318981c04645808801c07100600e10b200181ca03a030381616100e842c40c40141c03506420903a40940300b071a0811000540381403020300c05034180700d10011203030b0001c0c00400e02d100c51007404940c95000b070000d55070307400e104205959a07404100c090398450810010444050b2149002030f18401c2c035400c2036801c64446062440302c0810101e0100d1b03100f09040d00010000b10440f01c030800d00c407a06050490340200341d000180c10040c004040701d01070791040003240300580e15640501e070408a40010980c841c89103801243c40c0610301e840c01041c200461272b41c00d00710396001c120320001d988180d01e00ea05a4503100b40a0340d03076180ca074034a55441003080c40024031a2864440701c6a903410000d00125072a07654000000700f01c1005c0e00a244640340b121018400c460041040000c0c41800c031882038a149000c080581d101d0240750015220000c01c81300850250b2a150183c50340d0719072066080108021038001030700c280d00c2502c01d040c06030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 188639208 1250 188637958 188637979
    0x918020a0b19020312010603180b090717060f040803090a050f0106181b053a0e0a0308010b0d0b10030c180609050f01140d05010501031a060a0f05040b070b06 69
    0x2d51000c4180c82d004880440302c0001c2e642000003d501519100800d6060800001011408240c4040c003942c021031080014110040c1024000b0b540e413040d1220300d0a040e0f2202d41400024282032403240c0c0c0c05a000312403e0340301d40f03a1691280c02d1441c08031000c1d080d88a01141981491019030200b8101c4030720031a442c10101030070103410240c805603050031003800000c04061144600400081c40e089032a42ca61b44614110f000001d90f1410b1041c10b42100c080700c500d003800500969202d0070400d044901d004210f182ca07166070080a450050041c00700710403000c109000c001c0038982040600c078400070032802c0c1081545400030f0007061040b00c0180040c00e40d2018020745a90190301da801e0300c005d56240c2e5031a6040c00309112449820300c40f03450410841d58081429214110040c02e06403c800300f01062552411000409039005040e86103055949605d10301829902c42c41100c14401d07c9051040c0104600403040c6c440d4000c03503100c0c08014a002608808008408003543d209400c2101d008a15 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 188640458 1250 188639208 188639257
    0x1202121306080a0519050a0e0d0302040302090f040f1407151115010501020c0105070206190507051c050715090512070b0a0504230c040f0b041808040918020a0b 70
    0x25a84252180b86171600784900341850207040e03810050340074500001c00b1950a503800000361500440c5c14560001076800b050034021490700f81c0d407032600030651035904942424203440710110074112203002000d41502400c4030080d0354051042c10000d18604010f40303810b0020500251101403451000c04041c003410b050144a190f4080c00c550588206038024131100c0d00e084019102e80e405040141d034000c2c0140241d160302d00c0c0a4103014034610b056074a854860710980340c9585440003034111012001000c840301010940d00c0340c1920201e03a0000c1c1c0300c00006030003d10600c001d120804001d030450145140c412200d400c242e00a01c00103110301400c7c46241c3d110252a421540c003940c00030440151228400c0e00d0981102d04c0d41d445090690980d0780a5440318000750442d02d8031104410f06a40b6111038841903e810322401c80c101c0e15a02141410545655420002c1c0c460f501600003465601c55007085440c4070300c1003191202d50b01403d28919142c070742c407120003540c00420701041c1c0c440420028041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 188641708 1250 188640458 188640461
    0x901021510060f090e09030a02070603020405030c060d09020a0e0601090f0b0f130e070210050a020702090f0703020c06040501020903060702150109020904022209050a11071202121306080a 82
    0x1140c022102041c0100d41050000c0710b00440d03540c0d00034104076401001091291110301101c0c0180c2d480300c000d5a41d860142400707428404507611401c14144103010401c410f44000c100d4001c00001210210365403495211180010130180c03401a40064403003401041c1d40316055a02405403000342c8546004943d41c3d604146441c00782e001d005062103007803242c03041c13100d00030f006001100c0f07442c5080c660094491a1102c0121f004543d9040140c1c40010b00c00c90012003486215000100318038150b00d8a212900450b50070b00001e82907a41e8040000c0004e669148240c0c19102240e45800a5030701c50700785400c02601030f42207031120078402e001d00c03400300310b0440c00003501040101950003401826880d00c01c890009401810180743c0050702000448055508030019145503c2c1d002c0b080c1c22640e00741a5a4421100000c0884030b10078506400680070301540c03401c0d900d0b016800b000c070f080840203442d4100d051414035021420300aa000c91140e00300225410240c06644591b91554101ea4401a50300d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 188642958 1250 188641708 188641711
    0xb01140a0507020904050109120c020406060f020a032a03090e0603070e0a0203060f100503090c0103050601170a020918091207021e030f0f031c0204050913031b0809010215 75
    0x4007280c4200007640040c02c10040280d4414095000050640303031a8481d502d4241c0450000000111406181011032a00b03200d2000500803924003090340c0c0c0030070307a8041e5130341c48400c00c043c041c0940c0c8400c004102403c2e6559001105074020861003503c020b290260505d903050080190004401001401d1070a000440b201180c00c40d003180b400640391440700c0c20007540040c141a400c12285010f1078965161084490b40c180400d96030742c1d640b4501400c41c3c500f01892080001d040500340010302ca40c503a481855a08224101c400030201511200b40c190000d01c1440c96560b008020f032482c40c0c03a5288241420f41c40303250900c1c2a1202076807281a1407400d4407990724001e5111401c5001e80340c044001040c2d1142010b000b4003224200c1510300410707482d001c000f41141d041540001a40a442c50440072580c7c40c007250458103500b45400c2c90000f40341014020010440e01e40c16803001001e1603c21104c6a00242d080e1040d10a0440107081c40c1c85243d20000040e40503202e10100100340b42c20302500e00c1d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 188644208 1250 188642958 188642977
    0x30c070303050309010b0603070c020f040b03031e04230111071d060301020c120310080a150509030f0a3609110c0708060103030905060c0607050319050702010b0114 72
    0x810096046a07000e840b1034001512481a82d0b40e242c4007403155440342d42c0114014282915a9049056548100b042500410502c1402103042840141a60b10000207440e00503166103c02103208080c00c500710168080c031380c80141d4500c0c01711a4010300c28900a0443c40c3c2c1d100030b98560440100e144190365668405100e150400c4031b10fa81034882c4020000748440d04400c1c01000549071000781520306144c280e4580a02c00c50f0b42d40001407280324001d56100600030449003000d041015296182e00f00b01658218138400410740701e00c0000c100c581d007401100c00903949806840d8442003500070040c4641514260b40b8018081c0c41c404210380c0401c080228091018500081c080c1d90030980d0305405405a2a403120015805003c1311541000c140038003030240100c0c0c0c005103020740c5542402002c0e0612507102c180030301c03402c020b07030715a2007000b06165a01c00e406080c6907540e500c0c1c448076000440c0c01480d844500034544000d000da04c56042d0040460048241d940402d11184c4608546080c40303540543c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 188645458 1250 188644208 188644213
    0x6080c030a02070305070203010920012d180303080a0605040603150f0609090602121e01140a09021b010e1902010305191404030807020c090105090912040f030203010e030c 75
    0x72039901858000f4407100744289015800c045080d40460300303441c041d0b00d007103d101c842502000c3d00c4903401e03513942440b141c0901c0c2000c036400150001d4845034003052410714801c082070941d615010b000700c04590070f903518509115143c56503800c1c000c018040949030060f84c18100350000034985007602440c4290b940005c140c262102d980d1200328020080342c1a081045a100c00002540c0d11907442816400d80c0200b0b005640c900c0c4214100c1d10030180146a8060100c010b55440b158808402410b4103584c0d04021542e4001800400510300c002c040c0c0c8148a110b000003201c0b507210b224941401c007802d05803030082c841120300046181d01e500640d1501d041c3e030480280c042e405584a90059a0000b51040b420400a07000520034000e8078031503480b00020030b0200c814001003540c821001c5070b02240510103400252464800164948818850548a00041030100d01c40c05020300c110b51200751030904065440750740b07002030f00c240e0b0f03085d110981c0709510708900b086000e06c01000725204048003501 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 188646708 1250 188645458 188645461
    0x3180312021b06090705040b0307030803011712070309051c02010f051b03130302030601060801081902011101050f06210d051c11031008010b0d0b0717011d0106080c03 73
    0x1100402904800e6010480010789005100d02e0340b010f0025600030025030700a800543c0c2000700340801c0d01d07950301160f4000c8d800f0303000820100d0700c00700542c1c0c1511007505994500416010f1010724080c5d40e20b21150030384d10700284040805030000d100c0c0d422240192200204403c00141e0061032580449010740030400e2007080518140c4a100102032444a507070742c480410816034009840e40d00200d00103a03910b0003200091041d8034040140074014041481d1203c0030358100210309441f4891040e40c203131004503d5200ea0216801a48070384c80d0405210000c02440c5000d9100c00004441580c01030300a01403088070051825003c03407070100d0b410b482e00c024540a24640002c8a10f607010b00304000c0e505020b0310407401c0082160283e440440c5418445035200d09007480c5840a000c500d6200d5191a0f1400003809125212a41d04008050700300900143d02c0d5121103041e2030321004c40c641070540c8504200003045009840c07503200c4d028a0582500640e80c4e80307480701503034131710703000e84d084040c0400500 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 188647958 1250 188646708 188646737
    0x7081005041a0f01031401080a21020316031b05100501060f0215090c06040f05010e0402073906080a0c050a08011512050a051b090105070204020903010b030f030a031803 74
    0xc0d00f190001890000344d10801800314504080c02a0003a041c1c58000440e02c1d01441006c60321400c2d8a894042d00402d04860500043c0d40c0348519603491074180c001c07216100034140105143c1c076000007409c0300c0c8110007010b89000c948035007124000400c03582c5014004541030b03104103910700460806400502103603101c01c0003ca054480100704000600c54100880c2040d10b07240701510081021a100c88807032414040050f2121040e9420940030b90f10501c01000441c0c122001111400410031b82c1041c2d83c040c000242c4400800ca401050340d4001550300050115030101e0400c0c0b00f5406a203003001201142c401c216001c1c8a000351143c00580131000511008201100303210011106082540da0350640680300e40640d801110120440343d03171101004480811600342c1c101202611040a143c140c044001804034000c0c0380c0c0190043c0d90210348074900e51400d602046c4c400754000c080b00c4d0091422242c9558907800b460040c0b0001b401c00e240a1042c030a5070021f8031070359605454074003c1409a5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 188649208 1250 188647958 188647969
    0x2405161202041a07050a05010e06070806030a031d011e0e011205040b1b070b10060f020106180905120409020901170c0306041107020a0e1e060306060f031507081005041a 74
    0xd00e130582c0d55000302d071481c81c0050801d01c50148800803203c00780a0714544514050104c24008044600a401074415040066030052809000700300011010384050081070040303810b0415180c25800c10100d0560844c451034100141680d02203099a405559130501c81c0030303000ba0391081e10001e09800c00701010038141c11040818602082d50308031230b64101801c54560b090f410746d00303945104100342d21030800c0c410560300c00c01403160300e80140024484149004001c0c51210300200e1000b066965400450702040018000030803000501d924442e20b0366100c6000c40000d500c01003000d4040380704216003c01e0103840c0b030380641c4200b0030100c1070ba0541c0d44500511026044d0402112130f20b100c10403c0b1401661001440c501400f03070140901e805d031402c0c100c40d2001041050020b440d1160003801c1000b03654002800b254005002d0301d6003254402d0480c0402d00c0d0140c220742014203401c0100c02c000702d01d540410741d140b10702000c00c20317010516a607000340421140a481c0542022604030140d10460801c0c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 188650458 1250 188649208 188649217
    0x80318060f1309020409051806010501080c0405041b0e0d050d0c02060904090b150d02030a02060f0c0d02061905040b040609111e03010507080105010203072405161202041a 75
    0xd00d58010b1410000341401c0d00d41d0403468204a600f55800b24052040342c00901c00c10394404410700003450301c1720030480f00c1d0f940d60390140f1401c0d0400c81814001006810840b05031001407401030000e1101e5002001c0d01c0c004d2885450007503000402243d40ca040f680340206551341483e4102014004025927460308440141c14900c1c2680c024504120241440d10f441c820b0785404c41c0141c0c54042c05007000d94030861500c50202403180308034030340c80741440541e0380426901d48095040343c3c10755544804001c2d402580c01040101803150182d5011080720680110f82079100c1c0400e104804400b007485041c84c001c45806a4020740034800040009000400580c44a101c0c07a010304154582c2c00010030004d90304201c40c815203410040421092401800c0900a031030b00420581081102581041c000035507138040c0c0e00740500108011100a00300092540d5504202c01d820b040a1255141c81c844a812482d00401640006020154408078a0041b84292403c0d601030b41c004404410000400c800160407 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 188651708 1250 188650458 188650477
    0xf0304030e030a020607030c120302030c0f0306210d0f0503010e0a050402120303010602070603110702100c0602040e04140d0315050f01030b03060403081611060609040302160e0a0608031806 83
    0x20702c0c950f500c00b50b03403400003804c2061b2213a519a240a0540c2ca00750a0b40c0c0030b50b8580c0014140148207210100c2c0c020002d41e80310600314100242c481d81c0300030010701240d081d0001d03840b4907241504403074072281e80070030180c007a0304564640008210034106c0031501c2e0300c070074468416100d54200c0464407130350441d00426001400180507d119030510b0b00e06c05c5c00c660080e4495009a802500204116601030140023604950444d01c1414000c0540100c0d081042c4454044100700c40100740c0700c04c010340703030303050710041c0504040c02c0040340303070603d03100d4081c0500100010b01480b45142c03100e825442401103500b40c00d100c447d5140464034003c1401a031801481e46941451b8850840b40080d46007008420300c524000d5656004a09103241400341c0c2c05801440305040090110b541c00c6d00360400a0080e40045080d9189411343c0e546040c101e05010b6150a10032018441c8207000689180100310540140b4030110304003d41a0f40b131040903560720030051800030980f070200e420b0049103000005481843e1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 188652958 1250 188651708 188651713
    0x70e010309020607300201060302030d0804140f0c040e0a030c0b0a0e0318040c020307080927070206060913150f0b03060901060312090b0313080d020a230f0304030e03 73
    0x156413020642d17000380f68a001e0014401d0342003a04140c0c01516000244580c0c0000c00c21a411500820b07110400c5480c5142444082004101045104406204100c0740c54050700d20740b0307603610090741c0c41e43d030242652072095041900703108031004081030388003100d9415115030406100e03640d42c00148d10b030018448815582e80d4014048942c00900040414180c15003c00021a0405040204a0303000c90000310455109215000002e50124215003200c40201d40a851190622040b07104001001c407000030107080f20410310248640000303180707004000446005180790b5440c4a403400704c6c11603d4000e000388200880030b00d010101a44050280d0210b51804102011070030042850401c0c1079a0301112a903581108005101e40a0800c0312003068501e056200300346001e10740c500a0101400c1180e581964907404010440c5800c1100c1400100c41c00543d02c070030180b84042c102c8180e9100f12002c030040001c03210309604000040701d40d04103090040b00e041d80c5458500700c0340c03003844454164052 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 188654208 1250 188652958 188652967
    0x40501030c0809100b060f130f150807030203090c0a0806060a050907050702040902060c0d02030307082505090a030b100f080703020d120c05070b0712031109010c0614040b090601060503070e0103090206 88
    0x450b4040090621111b241e00c00f50005140120300020440243e02800ac0e00c2c03c08200b03400015800b5039026040b025a160141e22600c0e42c1085605103118452625030080e0781040000e803a150125480d03110300d00484205101c940c1d031310140001040300700c5111000600c104280c0740186881e0341b119220a002906141c109003075040c1e0140b904043d01303042c0e07016910110070400f110741d01c150300c194060480c00c0545001400809403c00710507004200390103021002c901d06216450342c00340f4000464201c07c0662480c100901890184262402455062001d041010030198400203900c01100c1d40503021804030711036511040101034429610354100040300b66140b0110300100880c6c000b0f0412a05515610040f61034101c4603c4440700300340041c036041600c4075204081d04070036030b82280800c0c04d141440300b04030702e0100c00802c031880400a103286000d0501080c8110801828030903000e00080300c04590300e4802c1510507010071548240010350310320ba502c005506c00d4100160030b5102800050a0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 188655458 1250 188654208 188654227
    0x504050a150b0a1e0917160e0a0e10020a030c0504050d0807050a050601090209010f0206062d0319022404090b18130c0527150a0b040501030c0809100b06 67
    0x502640c000883d00040c0c0c031000c2404044407a51407070b141c4511800c010180916111000b00d00c00d007035071150080c82c4c8020780000c2c040310140d030020f91008ac020429a161500320180000080d013150a00c41e000910344105140307241c0c000d60803502075500c0200005403416042d51400029488690221114060000307080000303203003004003601074941c0a4001d43c9614440c0e00041040611000980c119880001441116110b045c60b800031106069132440584000c0b00c10780c01002c5d082e182c180c0d014820001d0312560b4214289a41034414803c6580d540100780040c00d42d003211550b800510400391040104106c1440c00e6489400c10070300c0030307000441200c4981901d2070a03050481340410108100d0380b9000800c200c21801d400540310440b0700c6428050390002c1c6030204000e91a1000c0601401004180d41c0803c0c80001c0c0c224460080200c14010349649548006030014407a040c042400d10900c40c4005004400103032207407004800a2003216400200344000c3c0949051480e0410010050110f2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 188656708 1250 188655458 188655497
    0x71205070e070201140a060b090d06020915120f010b16050115060e040509070b0d05040c0f18060503071805070905061803070b160b071403040c0504050a150b0a 70
    0x11542c0c45400000d102c854100041680e441e0060035851480c4c0b820a040c0054080072003550203e56003070b244a8a1107501d80b8000b0000c0c450300d6401135114074110340700000f0040c0000108514403800c0045402922400101d008408007030140280d1080300740421904084a102450f80760b6010741d0010031034008064040c6800c1045410450008000080314445400c160044a401420342c10051a605103498100c15060049210907408a0703200c03070205091004000c6584c02030840030040b02245642d80f03400f900081e1580140c14503640c1480b40001e094900415801c04a03124890444804200e010b000001004002c04550038420000e102144503200c850140a00c5104d002d041d101010071103041502d84203065001c4d241c0080200710003084240c0d244408404242e2003445000f090700d402800362a14210b10380011403400c408020001481104204007040f10b4069170104101d03201c2c5d413031110940b41424440060028003503020080e090082e402003060340114a4201c1130282c0c02c000c58070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 188657958 1250 188656708 188656711
    0xc02070b03100b0a080106020f060103030909020903010212090d02061b0d020d0e070305070501090b07110402161a0a051302030706120204050a03060b01030c0c12050d0e01020c01050718030302071205070e 89
    0x9001171050401070103556010880740640113080340c02450702c2d40c50b5a030000c0069403280282c1003a2500411446540e46003501035070000059100700c0c0295107408010981c0d555040e601603c014403500c0d01291350348480003500b40604103031080e01491301c828500c40c440039600c10540d201c20340380d5070200d0402d0f4540c18080c8a019501c1500030f00201450507000501901581e040b450400c00200607100004050b4141e4086c0040c00382c4016858902101c00080340c010381e00c0d400740c4424440c00c040c65500f1600074540e841018a51000c10141c0c9440f5944d0075952483e1500942680c0002428031265004006450308802c01c69800b6107401c0e1244089204024154000c0b0f46c0700b510341c9400e8141e50b0f0140140369801c14540b030b00e1000250180c442e60410a07124900341d0078080005020684498a03411885100c1c600c038000b0f554518200b0710803802454100d50520006410003040307407440d80007184e480304507038060b0b00070041d450420030100c0c0c01059415041322103209013040010302c07102c1c180525 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 188659208 1250 188657958 188657977
    0x6180b0f0103030906140306040c03020702030312041b150e0f0d030c05010c11070611070f03050a05060f0903070b060316030b070f020a0c09020913020d091103010c02070b03100b 78
    0x18030203502d1841c0260441c00d00d6041320040c04181408507007020740400586e584100125804140c0d40d20003c401c2c8c0080c891001c0103034140c08000f80200e40d400060b44400d0049100c0e0054018111032070300700314849249402858420580c1c02e002c0204580705020710902400700600c007000081c1e808000440104c062807044000c610215201802e021080c4034400100190b8240044516030002004d030310f48182d07000d19810300c049c01115859444c0c080014030f0213080d0404051444a48900300382e961420300e8441200d4611481d0700055900b5003498009001d40d404800440c100401980c58406002c0014485501440b0307500c0389a070015100084400114001e5034075107041d040038500100f486814195074030540d0301110700000080c420025050494002c0c0e500161100203220000300c8140c0504011900c880c0045050359070740000b6404034800074072400760713411104881014542030b00d40d00c024031009a00528001c110414483d4010355110400038000b01c0c0054564280030400d410005c1c20 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 188660458 1250 188659208 188659231
    0xe010606020c0922151103010b042c1302010e041a0306070c08030f06010e040e01020a170f0c09060d02030106081909050d050a020703050f1b060705060406180b 70
    0xb0400c0303007080700d00c8680160301c0c2c0149050b411103024404030480c3d00548020700151a5501d41075411070383d5840601048000703032070a40e880d41c1d60250940e50340c21038042d0100c8a43c0c00010000385c8540d80b070500807003d003c081c0034590b0f940c41c1c0b03044c1030011411450590600c00c00d000e0341d0708e06954510500500042c8000b0703a80060710001c051600d82000102035100303002c0c008000d1004141c1000583e41c0c081541d151045140d503c8100494488080500c1c003900a0f050009880321850190040c10b09044143d0b03450320b070000514111a41c80310140c500030110785081c80400c1e803141c0d581d070080040740030150441e40b90011944640c401c980c07007648540001b603110000d000300c110b42d00c02244558a101201807107000741c1915003588038810382c040c240c2844400030360300302e0303040c0280b01c0c11000315085002d072000c0240d40340815861324101445601640702601143e85203140c260b059a400c640c20600920f2503955941d0303202d0003045034226600540409481307440c002100110410b00c0f40000300d11 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 188661708 1250 188660458 188660473
    0x120212090c01020607021020070c06140405180c161202010b0609100305060f0a06050c0706031103010b0306010c1415090325020d0618050c0406061d03010e01060602 72
    0x80ca0400e10100c0035541150400e200f8420b005900041e490450341810100080c1080300b4200c510000a0840d0721006500c00454000c2c2072009041c1280100c411355212113803a842c41103144001131203507001d401da00c40074101c5030398001c5000c0403030395034040d0203d65001e10303141c13403006e40380100b41020394115138040e000c9403c1603403541c3c2030003080c00075101030341c56904249d503090003c0c21040c3c10892020405988a000400c55910007482e04d08030440541400846510313490024615440700400c1100d610071a032001640f00e100e0310a8540410030024440c1c01c503403c004041466038409480141008412811280070074642e40810b0225440c00f002004440d42c6440d980e068071200a01c107880e00c1c1c100b07114040c8011501250450310b90340c850000300007001284005011200b0054001c0d02040c60000c050603803421020b2190980c6000d070045070a4103884400704000d603501400350070b0009101a12071140d01d03051401041c92444000d00101c0e075034a49030b03921821911140d02510044c1c6c0000f1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 188662958 1250 188661708 188661721
    0x40c0f050306010506030f070207051332010b0a02010615170703050103020604090905010f0e0f06130c061209020904030e010306080c0d0308040f0b04030c020a14090412120212 77
    0x44110000e100c103038042c1840758500030018102e40801001803080303000000020385e841d40b013802201c0207404018250625104640c0c0b81d000201544070000c10340d0035001d203002c0142108400b00d2031003900c00c0c0134103441c6a828007909004a0b0010503011003599290803011031507060760001400840340c7d65969188410026007419083c54024200d101418a004018400758540000711029035003488004602ca1405180840c0103241c0900c04117111072500b5800031f0040004148803081b1006141294442e8480d0041c20f5034070001903d004210b011828001c200c424081c400301385090110820000388015180c02090328850202c070110005407d00703507115040d40c0c00d4450407026046040042c81c034800d8020110302c1f888441070b4043c0a001c180c00c005001c00000c881d5440c603031130f4030a280b01c84505140c03a0182244000b008100c0c412015484003080142c0300390000d8549100c01006030781c05881d01c1d1107209200303108150840410100340808005081070740000d08042890031010f040600c1c4c0b12 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 188664208 1250 188662958 188662979
    0xb011d071806030509030409110405010e0111030a03090f0f0c050418050a020d080408070605030f22110a0b04171203100b0d0207020901030302010507020d11100203091005040c 77
    0x10000e4040c0410850180311800c076104040c02501e407207060002d4140c03941e484040c518060359102c0c61110b414248a0322000c21450043d00445d04280c075100f10403c401d40041d01e41c500b010301041216441441641e0380d50340b01e07800440311140108001e00342c45540d41c079201c1d84810304050960308031580f0b0000b0411420702d0702c10b500e40b810f158060060301035200c1c0d44180e00c1c2c022810001c0c2c8a00b01c1121103100b0b004141c0304450060181c88122603006e6030300c3d031010b045a0021260b0000b0251910002440007400e0f0f0804010206041e120354002e00c180d03510341c20764011a10f41c164001d60b402c03030081009040031005102410010103e05400241c68190601d00f258045400070261001e0081c454ad00281e050000195a00b03010025200c004c02ca0100c402400780c098065800040da8000109042c0c041d40481d002d45440d50035941071782d4050300700f511401914260142c0315400001d204141c0c07429a0f000d5a0800045001c0c4c0c0e62506034002c0c0b03401a00c80a503015503171041c00d41000c1200c003800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 188665458 1250 188664208 188664211
    0xf060a022103070f14090622050f060d020c0c0405090a0c1203140a050906030f1503060103030f031d070609171501090b0f0406033503040318030b011d 66
    0xd01200d185540f52144009198211407094076040c0b0403446541c0c2143d000c8041035600290380035145030780322446842a00c008905026a45115581008010400f810169100b01d80684040c0140340b9107130600d07442e42d000307502070f925480440c050341c0c2c0c03030b009542d965019041c058260100240030942040c10079042070215030348140c82c070f160440380c1800082e8102414107020740070341503029210007035404151420b100b44011564442c0d000800c00c5012681da10100b0701500340040100c00a060301014180d44074020700014002c61900c84074075800511a07004a11002e003825041c030385628401e446c491901c00141c0058001c2140c4e484e040c4000510341c0c01a00c40b0303240d82002040c401143e010903159402060003036072545511060f406820352980380c0c0c1c0303401111025104105040e601d003050121101c009818a2402150541d50401c600300c000c4208215100c0b224013524544039a5010b0b6107020380c3c8400300881030500c52000000c6201041e0481c000d140404003900503035240325107203070b11200 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 188666708 1250 188665458 188665513
    0xb0408040f09050411090403140307020304090e0c0d08090d02060418050c03070c020d020a08061801110a0207092f030a050a06030803190e0d0e030609060f040609020f060a02 76
    0x5003404104c0401c900700210a412441a621218a62100d05080311003003d40c0720780c1d001c1c121000044c0091190300100910446460303907002c120340c05074800301984502402d000e407540480100007003408030b48180c00800c10814010094201c2c0d075000e40c04610340703030000d034071040c4462070806403280750b04080e0154592003285410014910700c3c1c03058000c2c0202c46c4031000a03001e0b0f51185540400c5496190301e100c013402c10034048500526000c90002400050050140513035400d182405c00050400400e5a0040445402030035a072800c0c088800010403c003403202611000c061682c134a9810b1543c1c000c00c40903a610340355903407854280d4820341524000b40c02410564685403040010440c23031400d0341d41100002c2079040820720016641000b03445e54481010703140c0a00d82c0d2040720160008058020543c080c0c0c207888181e0b6444110781d407591011560036854400100019000490300d03440307084400d2005111031081d0030300c94007181140e04504000005079103c0c540c0c0b024043c0c400900b9001598 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 188667958 1250 188666708 188666711
    0xe030c010c090e0a020903031c0e1c09140301060e0c03040c050f0f01050309010e0105010f081b0609060d14040309080105180d05090a0b0a0201090c08010e0703021c0b0408040f09 78
    0x2441d102a056010000800113803055902140c60a460780d001c0c81128012010281201c000005031100d000c0180101448a1550300c00c0c0108a500300040812403803142c0d41c43d413030f2080418606041071a002c506288910b5155607201408641040c804110703602a043c1c00030559203e02d000e141415050ba11504820f10070846145c50b44da0690740c4540340343d4030040a107071291b229103802c1030440c05080c0344c0040034495400d00c1c00100e1581c00a040240443e490304040790081c0700700c0d0040c24114020301c2481c58000c40b04001c84003860030510f00508203103240500c00640b421562840c03d0f4401002d660440018080100c1044a00c00074010150003082400f5051040410703441d006564403440891142400004561254140e441c0301072440100038140361180d445554141c000c1c020700c107405080301c4022042e500030403400f10501c01d6000156050006000741c40c215000c0288146052404841e1540403c0c01540054860309040b401030784500a490349580c1814040c040f80d10703058000c003941c10b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 188669064 1106 188667958 188667977
    0x12020607120e10031503030c03021204090510050301151707050604080309032401050d140d0c0c120b01030b13120518011707110708010e030c010c 64
    0xba20222000c8000b00600c0d80103404480c0c0340016100c4000c1d5050742032002078060702c5580701860090048030829112400340c0002544150443c5c2c282c19250024028800c0f2038149880142504030000c4c032140084404801d2041c44511954a030307002442c2e80d01e90524414003021000d008003626081c0c1d51901c0302c440359960741c040791030342d0b000f845120500b8152081f5100d0350614002e000b0345038289030b442c00d020060a8154100c05488049030b004c2d5003c0d010134104140303680541a621091540011410419240c1200b540700010180760041101d0003d1140c010769810b43e5032000c000b00e095210011000d05044501d00003c0c18030480072140a001034104018084810211502c0030704410035000444612401c0200300110030b20110200d100140560f50203c07160b1032481c1118200f5540e402c070942510258201d2070001d410010311540b44902c05c0c041c404021085041c0140300 = true := by decide +kernel

theorem cover : BRFrame.Cov 188489208 188669064 := by
  have h0 := BRFrame.cov_init 188489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 188489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 188489208 ≤ n) (h2 : n < 188669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
