-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0172
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:15:06.059816+00:00
-- url     : https://prove2.me/submissions/c344a1be-9f26-4429-851a-fed6e980fcb5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 30755401 ≤ n < 30935257 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 30756651 1250 30755401 30755419
    0x20c01080f07050f0c0f070905010b0306010e04020c0712111503010e060d0c15111f020d0212010305030c0706030b0901090c03110d1d0f19050a020a030308090124061805 74
    0x6009000440c105600b00e180c6c1140c4203a17a950b40c13610b08642c800e028258084104001041040d072180c1e4420000caa4001c0005161820407101203140aa842d80807001c60740d20300e40c0c28004c0c800d803203030300d440031400c10303100544628031004c2d50348c066110500071038040d03a890a000c100592100355443d4811030b80148244245038403010303e07010460519024100081c50700058404803140410782d42d2112081c103104c500001c0314030329044041d41152803010016582404000030704028140314500845c02680a5130307650702403069080c1466041d8110106040c100701d05820940c8800f4509411200d1900c0c00080e41c03e0700c10411070140840c0448101e2146010a859415100a61140860b10410045541c024280016140c1c0790b042d0a012409030b03400451250580030511104201d6042c03040e415198545e03e1940010380b249010381059000403200020020102800d00c510030f0a45410142c0d000e51040b655016240700255008030000c000c02001d00d001b004d00780c4039140c00904002425001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 30757901 1250 30756651 30756667
    0x80903071101140d020d02040915080601120212030d060509150907050a03021308030a030e1903031112040b070f03050405060601050d020d0603080a030b010f17040201090801140703060501020c01080f07050f 90
    0x6500127029141c2064a00700001124400841103c400c59104ca405440e00c3d07840d20100f0f0380c180c940a04240d8020000d01d91403696a80d090006000300b00b0f15160000720241071005000700d03010014000600c2c001001c6c0c1907000c9075545401540d00192a1401c2e541d82e20a403a400c802074003c204400c101c001c1d0528000c1172418010010380070203011a03404200740041040003581d00c09e01090498181e0103c02c19420100c2e10a40000c0d481c8100d814030fa52a001e098401100d44007030840d010380e00b41404505000402c1c1e4010050340c02d06600d45018000360419031030390740d15102c0180c007640c148a07001401c4020401d064040e2520101c079094100049030352400e02c0750596112083c81c00009260030307000312003036005100c0d00e6490f14082c2d513030a04c2100e0394400c02e090102c029109a0510180990004485000340110700c2402800119403685003086800502a1015900200e041d074015940d04d072a26644202d1700f41c2d00c40d80d16400402151642d40c3c064505205d20030240c3c07120340001178010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 30759151 1250 30757901 30757927
    0xf0a09050f01030603030e090c04150f09120203031603030b03070303020a02040c02030c120904090b04030c0213050c09091f030c030c05090103020f0907030b0a090606080903071101140d02 82
    0xa0031210180e441c1e407004003101d00110119880382c00002e0100703400c2c02d500629400c0000c0c0040c4c0c060102000140340c00c0d182e0b6240c0100d01e1200e1089000161400320944415511240050040480c0c000d8030620b00101c0c0d002a40720300444103505806410082d100701803602c02d401c5203e0646000d01515400c03600c5e810000c0d01d40014040130380c01182040103000403e032000044410021100c00680701c0041c1c02c0f10101a19849400c3c903950250701ca0000320041480c1c403140038001d0b44251070709007400c2801e2050180501031803da00008030b10f003000304420701451200b11124014100d44148165945500160085188501150400c1070400001c410011442200e80c03d40c2d0050b440d20b101c1c65903500800c00111001d0100035040441d4034503c040d0f41c00e181c00340c640c00449900f4003084d032080707960101d41255059848007424a884040402c02c543d004444903030440b941d030f0059031402d5030a0301c586100490070b45605041001620301640210b030300506a4484000d40c2209540d2201403111207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 30760401 1250 30759151 30759167
    0x41506090905010b030a030906140f0d0225020a1a1b0102030415060b0f07080d0c0203041503050408161703040501060e061206070f0306080f070e0106140715020f0a 72
    0x40750190b191854210784e42c907002032541006503041d13580c1145582003160443e4042c00002c110003844809102d4080507103c11000750055200240005031074030540c0174802c140c005d0300c0c0300b103102d80720780902c0d07002c05a1035040705c50048d101032801d892280c4d104001010f0300d520500312072500201c0200b540d61034669040d0001d41c000d0b4041d500c0760340340201c040b5031101115283d12030000080c10400084005c103541102810f10703035000e90320150402091b54008401d880313600f030036500180c10024040c0032a49015485001c603a03254a4100050700d40365483d03041ca84500d5030516007028402c440d6504119000d00c003490741c0d842c416202a12810b052402c940603100c180664103d071114040094001c1c1000c9902c6810311451200410b89501c40e0300060b1400c50305001c61104068039100086080c100420685031a00c01c1000140707002850720719815a44101a00070b0000c2190500200142e0981d0381e00f92051650406200c51407504106c4800000b0b10420420000c2088046040ca0b80c2030740040c25 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 30761651 1250 30760401 30760403
    0x30f0714011106010b030a0b060d05090d020106080d08130804080307060605040f0902030604020f0321070c080c15030702160905060109270905030702090c0310060504050a0506030415060909 83
    0x80c07000c41d0700b100c41e1082d0302e4010034015410400c805100246e00e9085075002910350303d4000d051140f03001d010380100300c1619412290701c0c02d10344c0001c0852501c0e5038244a804018104400546201d079075500d4010541440640f0064145c0711207040e00040c4103058040f5001401c14008980d0b507464246001d0024014920816103d50302d400080300c10035401e40075641c0c3e40d80e401800b407d601c0d07481d54200118030346083c40454262240751038035100850250300f40c89150f0200010307aa10b681191400b48080356003500301351a5500910521520f079100c1510901350342070091601e40e12a506c48404900d012920400a201d070000748000184614803079200c14020502070b40d03115455501c58000300c0c0c1401e459006001144414418071101c4049540040326180c4204123403803400d07015030005072203040c042e0b94505480768000184800c0b1034804210000512107400c1c81800c0c18075141c0010384048a51040303a004590000c0080d04101003a0b801c2c001d60300099404201c41500c0302400c10061041d044 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 30762901 1250 30761651 30761657
    0x4060803042301090e0112050a0507090902240a0804170f090102060a050c030606091206070f020613150b0103090609030503091203010e0105011b080415170f0f06030f071401 76
    0x602c1d080d4441c1802e001a600c010520b0019a4603280c2d902150312180c820030b440d01e0041c03010460018400f0b124a60080c240110045004850750041040c0c0342501d04000264601142600c9440240e480988211248506040c02d03140c0c0d59040c402189100c070f80f81c000c1c10000005064200c2100c1788041d1029040a9003210f49564842100710101c8006840e0055a01d006200181303c1e45080d0006000080300a0b04410a038040e1560710751400100790781d9038021550801c51a00260b0f81040007645c4034070038002131000d00407107403618030644d540b901441c175080d519072031800344a9001390802c201280e407041c004c02902d050340c203009100b500155000303002c03130050080d00203588a0141c150303410394840316121207280e40380c0380040d00c214130032148035a606c0d03c8984e094004500380002078001080c51820010368018003610040510b01002c81c500048060300b01489010400c841005600c99809002c508040c0c60b0380d00000d01e041002425101035100e0020003040007402c039078040705800401c1e2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 30764151 1250 30762901 30762959
    0x702030705120a09060f0c140304120807020906030718051302030303090106060801140f0d03022103040605010b0720060c12040504050601030902030d030506060d090b070807051806090406080304 85
    0x205c821a034000a8501000014600b0310720b1502044000414203804103010040702d14096461010440c526000700301070398002004104401541400151580d01035411809080c030941440303c01c1000c40b01010312406055521400500042a00107050741aa5001002c0ba920391800103c07144c040c1025004400018281d82e00000300080e90014090030347c0c80c010590b5604801000070b100407142e480d0000e404620803100c01c00760030400e959101c6203c100461003241e9a103800c1c2440002e03214103074007030090b51000704803d07404a0030b031014240c0040c40c88014000d400341c071100081c0f01c0e13000389501c00301107004400c0014a0314481c1001401200d0091740c0a102641c0d40c6001901103a80e5980c0180d019042250084080303840781e403002c0e03072241c00103201c542040b20030000501115030b0940c00b1551105607809200354240c0080403d9070020080c545940b911902148001412801d6814180140300c0810401e0082d9110342003980504210b800322600c5507941c1c079912a402601d1042007000c4034101c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 30765401 1250 30764151 30764159
    0x51f022106010f0f0c020103050406180f0606060e0a05100201140c0a0201050108030c2503170306090a060f06031802030604050c01091e06050304060b030f07060e040203060f090702030705120a09 85
    0xd000c2422640d606a145c000a0045540065001c0e10004100f2600d10743d4a442c1403165241520080090a009290101c1c042074180b034843c04071641504034a0034040c3d1401c151189549401710482550001c1e114601000c0400350141e000d88a41c8007035200000724a400c2000c030000300005061403000070380c000d11a590342c40524036181d00c1031a00014454102550340035042c0407850301d1946070300a20038807031300e074950340d46960b2002580b014075880c0382d020000521807246058003140c1d410511204c02040042e10700784400110040b00e20039038003416181c03880f001c50380c0708604a108045802400307849182c50949042c540312054180858042180c10001044500000f0071141d240345509072039480c014104082601d643e0401441268601d03100c89005080b0340b800d10411418142003001004c13100d08003000a050880a01e03581401903105004104060b03880740e00f2059a485c0c180d40303144840d2030f9408101d0441c80b134654050b055101c1e45106080c01600d400007031034140b0a668804c1201038036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 30766651 1250 30765401 30765407
    0x71211010f020c03030705090a0b030702010c120b0d06050709090204120204110705060406090c0308070302010606020f0c0a151b0f0605070c0f0b07120c02060103050c030604051f022106010f 83
    0xc1c80343c10400300d501c1440002c5515000ba0700400c0c0701000140000c20044d62200402d0003544111003c8005035101c11070f0b11440381d0001c201c0e10744a9060f400601030b084150340030800c007040704c0c400034101c0c40d04d42010540c4e0074000c0e00124003600c0411020f5607500e40b00c00d80781c0801c098800040703020b10b00d0517002d4811986c0703400644481c1a4003501804150300d90342c0301c0401802c520310f03003503d4440a20740008009500c46000b0004a4480e8001003102482c0c000d0207420204030246140071030308120b168070300d55030301e548020007512545407580c42401070042c4212102042e5008603881d03e4a446a18018030004000396083c0c00d1081c5012701541d03032120421280e0f4844074000510004040014800040c80c007050960321000c0791a01c0d1450b24131014041003500c803011017000240c2c009000603c14048140648840d03804140d0091065091980c0c4444d41c64517040703505004000c0c40c044034199100c042e0111900e400992100c03900c02d00d0704041c25515490182c07019030110b075815403840d003400c0c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 30767901 1250 30766651 30766657
    0x30c0f06030a020f19120e0601050105070b0a180c03110d0f0b0421031401080706050f0f070602070b0109140408030619080706170702031e0f071211010f02 68
    0x440a0030003411502d503400d125010390845445011203040910000e03484102034005581410595035521006101d5000e00300c0480e285650b41800a0304141c006100b1a40c0103000c5070f640690103880190f90343e07241106000100003a070f00c04101c4920414210b428040202c03207100079240140b003000c0039100030008201c00040a054028000540760b42c5420204119482041c0c0c00750044101c3c440c411444d501070301c0309415118184000c0380d03440440e2910143d1500e5030a000d0300051f001403040c2030a01c1009012406a0f10843c41003410025290950381401c40580364135a0f8408415912034002d07250906144009024006074280f07092248203070741d02151003850185401c00b01c09480c40d103602c0306100c9004041e8402010000200c500011452f00c10131001000f04965074480c4c648185d100112100400007030414411580240840d25850748102907102c80ca20750050320550b60003807500956900e00a0380703409000f00034410710829510350048544003040d88900000c01030b11500684107801c82c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 30769151 1250 30767901 30767929
    0xa030f020303090705040207050109060501080d020120030a090804080f1005060402070f11060c15070f02150105091305060703090201090914010504050a0917090a0501080108030d050703060503100902030c 89
    0x1380c0310300c00c10061828203500601c84d2902840001c40c4000d09911042c2c01e81d030080c2e100742a103502258042010342e5081c811003024041d148100c50740244c08011a034070b240030242001c6040b5548601d1081005100403c41c2d000341002000e848148400095003a12000c401648082d011b04040c0019224a041e2003212881390b0710840d411003001650712505644032040800c0e5030050010815591410010042c1441e090090914110b5902c0d110070020b01201580c000c40c400e5600c206000d81d42100c00c6200c007410344009840c0b21001c0d54400e1014800310002c90b1010701540030350000e0214203503158200c120880d0003a01c80902240d508e00104089964800001c00c5400029005110782d25294005c5500004107020104952496072555231a8071901500c002c81c000d00003074209501d09181d544800100024280011158903040305941c1b01c1c464250101c818655900024a08600a5005401a04c0301071701b21014052a4081c2c0c5000f000301a5041c0e110340320300c542c04120340c94050130354401d032 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 30770401 1250 30769151 30769153
    0x50f01030f0308060a17100f0e060c0306010c0c06020105070801081f09062003040b0c0301030b01060e011101110406020f030f0a0f0e04050408032205030f07031806020a030f02030309 80
    0x6511a480c21900f409025150f581d0101342c0c242c2c00100819082c000711580341c0303600c02038000c040032060340c0e200700c0f2100c10b41c0040207405d0480d288140c04001c206198050b0604070302690366511000100c5410088082c001c1c002014403401150a96055010501c030710096101d4403043c0c2d884030116942d0300e968030418600304030b1482e1480d80b44103254010003c0342d440b07000c004c282c1060740c460158044001c0768840a2002010041109000700b10040795000400303102c865146506540b03482c02c505005008141c01c2c4255074441c030503548d200e141800c40e03414109008220700c480e01c9085203056402403056500520400409000c0300c50040220b03616003084030310f56440c0c001c11110589804424410306024000d1041e110740301503c40340103151080780314151075a5a494204807803030200d41030201c0484d013850b01000400019100004550000510070a0281c5038800f910b011102440c0080c60141510f9030094002030301500010303031036500d601c25120748010001c0400105d0b9280401c80c1c02d1490303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 30771651 1250 30770401 30770423
    0x703020606120d180b030403021c032304020609040c1e02010203010510200712030f0f08010605091c0b07020609060709060507030e1207090605100504170c090c0706050f0103 76
    0x180135080e035400243e1008080c103c09640da8a9950007600308903010307400350f0400200c3e0038004558400001c0400b09038202008a05010004058201801c00c0229000303903000740882c0955030303001c090f101c010f840100140304020400d4801044460b00c2c04182d4210b6003140d2481054034018001c0d213069400141119003040f0100c2c01c00c45644070078801001c0d00700c810030405400c4010038070140001d0500000543c0c44680f141c5001400380410f104000100701c030180440d8010342d4809a542c0c1101e402d485d1460700c5903058030005070620075080d800c4aa032080ba403000001c010080c005144141036a400303550303c0380d4808100e26211401180c402c1e0000e41c00c1c0c5824803445000f20040c20707000e4024900505580c8402d80801c031071041c0183e0800c0b5643c00038500b0001c3d2101c500a04000d0442641e9000e0207144500010b00140141d006040350b18504001166401200b00a650381e2004028202c1a40382000030200103982e10011068400c103080400190110000c002d10710704a90b404001221 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 30772901 1250 30771651 30771673
    0x10b040501090207080f07061e0e07061403070809120408160905060303031308070b19050a02040f03020d02040e07060c060b0907050307030e0a02061b010509010b10081902030c070302060612 83
    0x829070740440c60440f511552074000010712703201a050ba030107021084000203a8909014480f44c030741552507105e03200704000c000c0d040020b40e01c0b805c11b4a8100446081030000350701d03241c81660070700c0350f110b1080000d03450100f0005000d02002500c0c00040c9009030000c3c95094840e0104015540201c0740160076600820118240f4481c0007005076000d0300825921342841010741e60305102c44400e640030300030441c00c06150340c00d00044c1c2c4100e0f0b0b00303c00f10040440c941480d100140031350380c440e40f00207071050104402c070800355100c58000d9030389103076010282c5200c9600c900002e000c41c43c0d180020b69106140000e00c800e903040c98814940640540c7d01d6007401d568540d00201d005d0031480d0321188050190b03105490040e1122000381c4040c5e001002c0c18a01702d00320032074107804c44800402c044004c1e810040907000903211501003403032580e4103150885c0e01da40c5000c2c0101c1d9080d50ba60302d20001c2e520010070002c000360024013502d96148a50300b6038206894540800c04d00e161180c1d00c85541d9001000c20f0340c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 30774151 1250 30772901 30772927
    0x5060c031003060609061d01051c0c0b0f030108070f050d060b030f060901020c0c031c05070302070b0a09050a0506030403090e0604090227011e0612060306020c010b04050109020708 79
    0x35074009000d03552011072903102d941c0c06007030f65140d9028510003610303030304140241c40a100c07402d1035565050400c091958504000544400d00301c4503105802c80001414205010900000b4000b4140491074180c1c6ca0404110081d8941d00c24400c20006004040003c94050035400c9050100c4000030b01400c1c0d5111140c131b40c00020304443d1510356140c464080c409080d84020b0100b148030300d000c0000140c540b074420950a04040c1300d050001d03c81c0c2c00c900c446104002001c0103802c4105002e26000d52208038a10303050749054829081410000b0340802e030440c4480e070140c0f2141c1034850a40c1d0740030304140e644051190314002a90000c1c04943c2c114400d1010075011078a40b980094000e03c08100e40d42e082d00800d104544c1d040c0d071a40c10703440f0400c4400c0300d581100a0a801815003940303116030661041c0c4400480c0d521400345004114242100c00a0b0840c3d0f0341184c0b01542d000f01d0210340c3d84001014860003800d2502e49540124280030000611b203080c1d00c02d50b201076401a5156240007465010f003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 30775401 1250 30774151 30774157
    0x2061003210c02030f010b040b0a06021b03010e06090d031b050703030e070906030303050901050108060c16020301110409020d0c0207050f090a111b07230910240305060a0305060c 78
    0x190040122858000003d41d50400c8500c4881601d54000541d41d400172060000ba241160710b805c3c041c18042e07070304105499001502d10b01d09e10905400c101f8038101c0c3d40000380548140003c480761842088103014151002003880000448075880c100400d6030b00005d07054411210309401408034405100080200340243c102e241c081c07072640706035660310f81c841840c901120b146400079000242e45000b08076044400b48500c502411200006110600d402180403050388585051283d80181034401c0034115202500107645414800798650707101c41d1103020700c000a4004001074a0900e003030035011010310380040745030f1050f190b0103044034203c3d080c1c40d4107000c00c2c0c54000d003150100a590356007a080e1448448091301380743c8078001c0502072010000c0e4800e490450940c001c840d03001e8a44004c540b550300221415000101c05075100c0c5040c1d91082d101002c0120f40b940101c0f80c400500d007040441aa00704482c54000103141c401300055103d81017032104000040c04010420360101000c04c98203000ba4001d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 30776651 1250 30775401 30775463
    0x30f160e011110020d090c090b060306150405030607050c0d0305010b19020c0402040303020a14060c0306040903050915040518063f03040306050a090b040303050702030f160302061003 80
    0x103c42941800d03460481c2240c0c041841d04101031340d104000c90410035200503600050000da9018000c1d0190790f00060114840030704218824a030b2400d4040f00740c0784c02000d450042400400350388040c0f52084000e030180d403040d040040c2030f000f41000f504c802030081c442c823410b8074250000b403418400302c440d5180850226000940544c45400718940c110b545500041009d0b522940c0a86013030402898034000052214002e66159000780041014100d40d00007503d42c440700484021031998000c1c00c09403428841c4410701c580150010004081f03002c0c0d114001c01c215041690301d02c0d0750710551042905012810b1b98000d5015240301a034500742e06488010546030320160084ac5e01d4002c42105040d6018a8040d84071429040072508005101d01803103025070042d02e102c0140454074195581c000300c0c000080000b001d0503502c10206400502c00c006442c0d03018850309005a5410302130b98000c1020302c0450046005106010010b55a036007440800c2e0100d07035000c114421032440584400544032640c0c0c1d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 30777901 1250 30776651 30776653
    0x10507020d0f0311060f07050a170703050402090901060303020303060f1c0303060303030518030a080a06090204030605240a1203050d051807050103020901020706080a0603050a0503030f160e0111 85
    0x95040940c1e6200c40840690348100044084403145150141039200000048401d64005000300109038401c0303c046544000c171407a040c2da44078002c90042d10401400074500040d070400d00c0030030481d141c05030300242c0164000c0b02c0c44c8196031380c2c1040450076140d19000007401a0018000314007142440c0b8020050444024503003a82022404100100341c101c24006a0000303455030410000c0c10b805100f429005000c407060245208445100d00e40d0783e118a100d14070802043c84000b6884d0345050340710070050840342c0e00640daa1562824100003400c8291155414101c10344000080f010402015405841c2c0c0a48a11a4586003084000000e5501c280c02d50502c141008400049819442528411404c0b82c81801400700c0c52585a0b01c3c150842c0c00c8203040c103104014011007a0b800150001c1215014070380003529580300f410540141003998070061551141d5580705040050101c06180f06d110001d98500c0c0556400d140d038020103c000440b4000300d007070041d8107403055208010807000800200 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 30779151 1250 30777901 30777907
    0x610030509010f140703050a060308032706011706010b0a0c080703090803120106020f06070503220204180302060703060f0510051207020f0d18050f010c0503040e060108280b0105 78
    0x11001066130011004c0140c2282068104940701e41c141c401e0542010941408200c080e0450383c414005100140041c0194804a40096580b00c0b40303120000a0310309070000c1d102e441d651016603490031502c01024580c980200c01c0040742d150105000e44040310b1107990b43407500c4039020382c4410340f841d8492103064041103030103903010403220810030003040d821160b4240400b4075894694028200b6000038207203030840e0080c00a0080d074903440b2054a0700b000841a1074101a000c5042001c82540c014000030341007414121403664414914203807287d55030003a000c0d50070320b40d5000011012120180200c80040581741e20600c4582000768162018007458108240340505900100303e901d001110803200613801505003036a10700003403104070f04154150034103030b4068602c1a580c0b02040003500905000d55a10b9808003000e84c46068034030011500141581d965036200e1010035030884040394400c1c040390200f004030780340302d03208122100320300b0100740c44402000c5059040c0c00944408070a59040200034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 30780401 1250 30779151 30779171
    0x30f0c03200a090b01020c010e04090203060901050411030607140a03110d0f200904152303010c0903020d0318051801051203030f011205010f020307020f010f0203061003050901 77
    0x4048103941071101030148084500074100b00700d8109115000400c0d001c0c1000007410050740c00044c0d00700e420b0803d00301000c0f02c03840900860010817400f00c010750301d0b104900074004100c8040d441240100d000d080d14030390b58000030b0281030365200c058410000081c01d070030810300380c4500500600400e8946141c08a080104170042d0031054103d04120340e4010b0b034561400e03001501c41d00c03404000c00703100001500402d8141074126a540151100c05005a40301c541c0c15581c01c8003034488001504a91040354035915002c035501905d650b80d100d0700e50096103001400d82c82240522458011240d0090880c0329410003540c0850b4a10142c0b0310443d204030303800b8004100c950350389a07007051050b040a404d10715036140408005c0015203580d4510040d80041080c0409a02410300c2d00741915140d5a50f00d04001d024a0540d00410340d000c01506c02c2440802031140d840e80c041000f020440c0c1c03800013809a40701d107544200c2288000d175440c951220788541c1e80303030000d4001d810640d0703c80040d50002400301e0310303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 30781651 1250 30780401 30780413
    0x303030903210e0105060307050d060b030304050d1b0e040b014101021501050306040b0c0904150512120306040c020307050106080d080f0c0f070203010f06061e030e0304030f0c03 78
    0x841d2285002d03644840454441902c01d10a196015104900422604d032810307000c00c0280421540280008c1e8a031440c403c031070344081046400502c07018014166a02e000d0400d0007103080d102c7c0c5611a0307800306120005180040b44100383c015504206900b1142e46001a24504070440240b03100c0c003103800c0348001d40300d030441c800300484021038000c200d441e00d00160002800d042103541c81084000c141c80060081c1d8900140c0380340e000b64001107491160b00c947c003048981d8045c4190a42e482424045625103003032604e880c42c4112001a907500c204000d00355a5580c4514000801801c0701c02e05100041e001e10303007508500c0d21440c0c1c80c01540d04e40001c50311032a00703445458003c144540c0c0071240624460307a2107403003141e001c13007038401040d40e03414031b180008030903c6581d600300d42900c4c0c049200c0c3d041d503a080d80003111070046032004102250761454043c1940c1d104030428040040b4200755101d996010340101d2200380c0260380614a001c1c1941d4900d2601d405050b025164444000b0f008000503074 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 30782901 1250 30781651 30781697
    0x30209040b090c040801060506030103050d08060a0e16030606020309030c04051801020f09010f0908060a09030527010201050901090302060f040305040f0e1005010c0f110301020c1b040507090e010303030903 90
    0x140b10002e10b54545c10a80110300b501c0c21903101d640549001c10042011135400714805070b81c00b0040c9070a1501c1d89030440014998000e541001900034840001e011081d540c2540380c0008a042da01e0600103070703503947e000b43c0e120b000b40344069805800c40aa6001217103082c0c4c2c400703070b030041d0554000c0050300107841d030460032a088680c101d00920030006228841790b03000150400f0482c054503040d15601d090030b00440e16540e01824090185417954041020503020b9019241342c40c040129403034640840c0f030104020b100161664078050f510b04400306190860601401070601e405070001d2aaa864146600d040e640000f0300a60400005110100c2c44803c04180c19000380b2440c00850000d04150903400002c1d04241e03c0740303041c00260105203000840011000c50150780043e40306c40440d200b200440e001e48503204400c45640190910450715048000300301070030b2401954100016a02c880066075101d80c68010000200d40304c20040000a00c41e1300903103003040c400d24242400110301d0001100c052 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 30784151 1250 30782901 30782911
    0xd140307031d0f01120e0c271005030d0c060902100206070e01020706080c130902040909060e030a090e040503070203070f080105150f12030c2d01021801030209040b09 73
    0x1e02c04000d40800e1041002c090180c40d4030841e100e1021903a8040080c041c0703100e42110b60143e83d16600c500c00b00c442d0521403164500c202605040851820303004500c0c401c010404108a041c0c5c00c580410404505000f241d800e0701c1000d0300402510f01d01c078100b59500511490f00701c4000d511148007800503100c95104a1244042c2c4d002030500d8103040380d026011038408118941150f12824042003100c1d405845176810441280000e0358070460001c181b840b6107180d030000c2048500010380011400070b55030110510500881040007484944e904c1e81d03840380b003408445400030b50849000c1c0f0905500b01142a0094440c108484ca004040d42c00700c4d04101c8140d200000d80c2c40d86100801c011507080c040d80d0390000e850350041d00c0103410180011100391905980d00c0c0140c02070203200040c0b00741002110890254402114840c1011001070034501950840100c0f03180718441840301c00400500030788688114111190780c51b50019001100290440c00249034001d40f035655a65507501c3d12090a4010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 30785401 1250 30784151 30784157
    0x9020408010b1002030c06011a070204090302060603070807031101030c2105070807020a0c0b0901050c060a0504110307060f1404120b060a1d0408030a020f030702030a0e01080f060d14030703 83
    0x3050541c03c1200c0c440308062140e040d504104144100500003044590647d103103500500c11004001c0c890101c079010310f04000f50028584282501807680001d440761103402e04078201c4d01c039651100740198440005100081040c20f001c0740c65442503009800c0080101d00c8c52900260070391205243d607c0c80400d00815000c1e0301e55820074410600ea02c40b00c215440b0b4698001424055210f07038a402d00e1140921420071414400320304419660b20840c1241c040c801803008503404c600300001140d000701000d94040781e18201d00c0707090315032900740030626000b00d0b0815164a80340d1043c910702501c180c90601d002000d40d100822001c101c4262114401980c3d03401004860341610f40030090050104041d0020415104151024132824200b00556540554050f0505440f40c0302c20804001900407000c0c2200040d8010040010070341d8008042c08600c43c1c2a603840400055000c019101070030b06070348810703c544021000502c582000c503140340c04603100f4011036545100044085013181c001c07280c11000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 30786651 1250 30785401 30785411
    0x20307080f07020d060b01093003030e0f011e0912030b040906090b0403090509060607080d1803050c070f05090106031503050d030f06090209060307111c03060320010905060f040902040801 82
    0x1540c4c004071040c09013050503a85c03482a805000031110340403000010030341c1e0711244070032710080600c242c105501c0c0f54504800c403980038010345140e0b0302801d440c0b11ba06111010600d0b07004d95622050142c0400c0d1a08009a04890303a0040c800310003411454007001d402079225490000000d07103900c149060140a4111a070845c2020320b001041e84030700b43d0000c3c0c40f0b0b1101000b0b00c45a680d035541121061303584648856501d10280c8110b00141c000100784002540030280c0d80300505070424001c0c42000c1c003100039181c00c2034031114050901d05550241c0c9400c4601000180f20740c9019510500360b44404014080605581c0d680b039500d09095075640000190f141d6103442d203402401d002d490f0207030507032031b0041d41050520b502141744e902000780b075213007001585c0244140b80da809204c0c410500c00f58001d940e541511604024018100741e100c200d1301d41c0003104a000b442008001080c0383c400c0e0507559582c00502d088200145030300142d84036110990200000200301001c1d1000300018000b900c000b01d1 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 30787901 1250 30786651 30786671
    0x80c040e1806070e061801180b031603050708060d050115090204060f03110304020607020a08100203040b0906100b0d060e010f05030c0a03030e091503011401090506060a020307080f07020d06 83
    0x82402d1024141000b8420414411507040e40c460b03041e00d0010b0301c3c0049098a20f5000b400403209654031110038110f0781400c003000f1601038001c40007140701e124450308a1460b4584503100300e003150002c90b914070024039000b000c1581032030300c0c01c0084c0040b4050f4002141f100742e400d0260180c150740d03034403c0c1d035110350001d400c208031a00040b0914907924141008c02800d016090400032502c80140000d116040001d021011503449580480240c4121000c0f01c440c1d014006449000b54030079601541d00500c0600041e14000001076014402d4240c007900c400c0340303031030000c0c001c209401c11140c0e403c40e5902ca2801254100900c5182030080c611a000654064a400207240c20202c000f2040e45c040e0b00541d4052000ca40c0007401e03003025040c141c90b0a4102c0d80d03160f200711500f80c0403003002a41542007601205084042002031070590b40c0c80c0c10208842e032101d50030040a44144640000581c0042c044a8041240c0e4405490348000300c2441c1d500e0301d55558000f039a1440d101e17004a41c00c5a45400c03002c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 30789151 1250 30787901 30787903
    0x60305070b04180b04060b030c031015020c120f010c12060e10170703120512010605031506070c0e2e061b020312030109020702130219080c040e18 64
    0x4008150700030040d881c190620028141d48150380d10b09403001c507180d0b91848000c3c0c03501d501080c002c21800b5005500d9040c041e10020103a030041c0ca01c8031140b518a0b0380410142c0c084440b222903000c1c1500180711132200c0400740090800f855007840181c0c0500c8040d44101d00c1c00b80140910803805555202403008404209000c4a066400070400310000f4420004a580032810200a6603c100803801440142864a0346403501d182c00c01042d00039840440d4140c60380090140c20910020780ca02a40b90b80c0b40c1c541191a0b010440b10340c4d107011001403560343d0038181000280340c101e0141021290b115101c881489a108007502c14400800100c0031100c0700b4411486040c00d01c0c03525403000e003040e5107481c000425000c02c030102c44514020014064045580800010b0103150052007225160f40e9920b14410080d04035131400c0e0b024070540c040c044c0740c2000a100b19440b07036600410040d10f02c055100704a4034050000d05070700303000c101000040b403c1d114101c1c0351403281120760620808864034100b81 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 30790401 1250 30789151 30789163
    0x40e130501111c021908040606080313050f0102010c051b030c01060b0c070602010b031c0e03101505040216060908040e150a080c0102120c03160c0305060105120303070c111003060305 80
    0xf45503262040c0f20781241c0004c1249500d01020561412031801c5c0c032903013040380c010445540582030b1444001100026242e0400000d01100c0e400c84591031242e00b82d60042e0b0980d0300c23000711030000a400b00900d68103020084540e03071200c1c0c410070850742811502d0030401c0c00c5510541109a401c90045096208094100590030252100e0f100174040110084082980c0d907040c0f4807070526400c04542250402489410a0302007084010101c44031070000140075001450116503565409403106408241c6090a000712103645078110f220210041958503110010091b120044071004002c000000d028060803901600030b460b521403030703c1404038040c00c02031000c440380e02005003034001041c00c00540c0e070041080b49103811034000c4603985043c05130f1218110322071021205048950a920030007403026040030a410789105000b2500c0c1662950100f0042e030403c1c0d81540800d0b4008c20025524a03c100041c910543c4503c440c211390351600c60028010300c840888510010340e5440041050101c10810 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 30791651 1250 30790401 30790447
    0x70b010806101211090a090f0b01050a060212041a091905030c090403020318030f03040920040b070807150203090307030305010608060d060b0d0203010c091502070b040e13050111 78
    0x41460781d0b00c81d40e403040071140c044c2c1124840d0402000184929a003600181d40b119401480601c1e0f5149920f04030000507070038001e00313019003139a08000c500d00b03000050304211b2a01007448241824a0038041e2070342d05001c4101801504c1c2d00f800b5141c0c0742e80700c6130342c00c0015070416220b140c00141080c090510b00b0103015103441c82004000e09001c0803135004030495280421210712a00400002c4020914000c10091514038500c8005800101d0300c1144c0d22520609100d01101e00b10b0750804c0c22407540c50700480c0144110704d070042150034001044100106030280c0b08100041482c240080381d8400c9070003c841d4050715403c00541501010b5151003503d01500710b03810501d46500305100855040c048820307000b000345a440003078012a950381c040500e5459030040081c4860181d00d14001d003080018400c1400710002520510740d81c50021a90700c0944411611003418140380001540300007902420b11400303070003003910340c8001c290203022721210b400a80c42d10960b201c582440c85100c800007800 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 30792901 1250 30791651 30791669
    0xf12041104020a080c0d090213020703080105090103020105040501050714070311010f08100b0702060f0d02091212030403030507050c0d0203220308070201030c053c070c09050a02070b01080610 84
    0x21012040d44e0f040001c0b42c2d00b0881d4466203d031078000c00d8901c44000d14490b14080d500060210813015110031036001046928031943c1c171503079180d82c1d410074803001d0345003030000a02061341803009201a52060024000403800303a000c07030b098a041e00084900300789103500f007a01c0c0108140030003106560440365034500840d140c0347c21181c81c070b030507522510b4582d554042c5990440c1c00080c44400d40d81e808050741c11034103041068981c2d4408142c40940298044c180090281007003041031162400d0200c0c0d45c00d40320802d107080e80d10319505d0780e404900400c801041c01080c46800e20000c09100400c00100f403144910340c00556480c01d1092010f0304106050f0082c0900e032200520600c005070200d8140e0720511350a00b80420114004c0a050345c140c014002450f80d49500101181032503e440d03c986485015070301132004401501c2404000c0a100d40203025002c400f042000708424182580000e80c4808011001414110310b42d40f0383c00002000ea2101c21160f1204080c408102c10000548000304000e070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 30794151 1250 30792901 30792907
    0x1090605030f06060a0504050312030609180c1003230a060503070807030602070c051503010609090b0d030c051c0503010806090307050d030f06030206070609050105090601060c080306060f1204110402 87
    0x442001038a0100401e43d034060140440c07400b800314050001d480241c9001000d44840b080c40401c40c0501c1e4000300c1d03c04d8442d0300e4503070100343c1c5480c08035200301032094010041c0c0b6003040031360140300c25038458905203010940d87d001c0c000c071004c10440d200011512030b400c003000300b4101840c1e48400d442450300301d148260480f5004104c1000005000030869170701400147e2100b965060141070703410903512554100038040c1d243c1d65030398040c2d00154160313030741a2100a245622100c0743c20440e00380c00c3d40e160300181450ba4040c04640078140c1c4200242c8100200c07801d10030260502c1701000700e01191131010820200040c4070040b400e10441c0d611008201c0214100b07021707a21a180d44a40c030000b082e060507960380c8150101020b44d005000a15000341c040760b510600307847c098004040e03c1205480c99441e00001c240c5100c00811680d0407900300707030f0f21000170000319103452441e030b40080e00d0250301c40320400800d54100340441c05051307030040221000b51980780c54141308054001e246580c600c594410 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 30795401 1250 30794151 30794161
    0x3060d12050703030507110a201012110a1205060a08030c0c0f1801030305160204060605120601080402030616030b0406030b06010909021213051911010905090408090904030c0b04050604020109060503 87
    0x61a05000c1c5d811082c40c27030310401706500d8882d01000c04104130750003403e840c90311031805420005c100e240c1c0d142c0080801800510440042c854003c1d25409000107030900d84c5901c41d0a50703600300941001000f400c1d4613983d59a0040c1c3c0f0301d507a100003103030391207608802c61240d00303498288040c21400da070548003600401ea6803551049150320500000301809404034003000c4503c081c1c80c0c0000710a9016000700002c42c0ca449000d003450700560060082d0301c084400084941d403265807050700865001e001002d96403103150080881100d42d5141504042d039842c015007c0b07907128044c120007540211491580390070b1441c0014a110500d07040074803014010010150022003551085502601d00083e03002000203600c0e240d0b052940309a40110342ca5542c8081030180724940b80c0011000400341c8800c10059911800e21a6544003201c016084070414400e894041c10040213240c1d00074843e26203a10b48078a25526000c4290040d14190303040d07800002000115604002280090000c504180e0309500d01 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 30796651 1250 30795401 30795403
    0x51e0a1e060207051305040c08070f1401050a090501050c0a1b090e06040f02010c020f0603091b01021f09030509060703020303010302010813020f0d02040f02041205010b0103090506070503060d1205070303050711 92
    0x101c0301d100802c01d0756440040c0230701440c03905c4070018110b40700c1950582c698880810450090b940a100c600b810310344090745666010310100c1d842c2c4003841c0c4130152014a480015184c0c0c1d0011031024083d80164049100040c1520b0075110005010f10074114003503041001c01c1c401c640c070900c201c0b00a94000f50500010482411840f0030f02942480c2442240c0102c1c40440c8801c1e6160042e1504500b0100a10036110404907000764541600702c0c0d50401c3c051070200481e91520079000311041d85480c40020703c00c4610383e8203e007104600078200145001c0c8210041404d40d030080341c0070750050708084018421903a01070041c3d0307001214820007084001c184d07000100034003400b4980501c10210040c1020447d1665000f90a8064000800f15100ca580e03a200610014024008440715480c1511900803503000341700b020246038008004001c0c5036a103000945c0d10354400751507244d0103c244a6000006107000029030300d4483c1560b10a9101c540c00d150150585030007400650500ca4050500c41c0b801c44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 30797901 1250 30796651 30796669
    0x303040f0306020a0507120f0e010207050a0b18060705060703050f0421030f050a060e010503010504030e13020403080a0f030e010605030303060411160803010302031e0601051e0a1e06020705 83
    0x1801c070900503a544c0b1031403003d0300c0e948180d03903008000c1003004100703110751394000901d03041820726a01c0e03c1a280d181113004980701ca0440c05941d0b445584141d0038031900c0d01820140214090382c0d035134150041c5625002641ca50841ca1b01140d060340000300700a0001d038540030301500541140c0000a140c05c00f691400c14103000f00840c0700010345000c240e10481ca219812080749030304c0000c2d003000142061195280076000c02c3c014070044806880c0002010f0405108091003142c042e5140b50300003400004001c90500c003003549120094083c40084040380c0044c004242d0090740752104003008080040223000d0354142808202d007645440e0701080380345c13404412261700070021500020f158400528070710281c0184020302c0d4460320701c641d80c04200b20100c0c0007141603c3c022001c480c5d0b0042c045040100151002c6000f5005800c400700401150400203040646040000365600c0d030603030070302d0221300a5841603101c011048005240c4401c04036807200000003504203840540480703170612000c030381505 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 30799151 1250 30797901 30797903
    0xc15020d1b020a0906080c0603060303071712011503050c1602010305060414040b0108150108120307030e0f0705040b040b0109030f06060e070e01120605010813050c10021b0303040f03 80
    0x3003845010031196040340e0011803003007075004080d4540a515500c41138024a05030041020714030030b1015200d00d85c5084002d60744680b400034010351400509a0b2444400c1e0791414403040c400c0018081680c003501003441c01e034040e02c240070609070907000c1c1031401000d07100080c1c00440980c2c404c12891021040365007002c80d031560282008103181e01c1b002c010400038220105010b4000e4410414801000403840d4010f040300c40c1d24040325070880c010503040d40e903c1402e10588245520030340301003202502c1d081c007565110356103060000f0081190401c4a06003074a00c081d0071103603045079106001914051103850200081a24100003c440e8140060450036581c000904032141c50700d001e03000c20816400503403381403a42d45104207402c107a00d000e4121400c841070b450200e100310350f00001c4440188550022120141e4030b04016031103500b02d1044050136602c041c0e65500484e40f041c0d5058541030941c00c00080c8550040100c0c0740c126140208a80001a01078840d800c200802c021041d80e21200c28156 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 30800401 1250 30799151 30799157
    0x60405130e0f0307050c03060105091003030305070c08070501090c150504120c08070e040b150d0f03120c0903050123160215010e04050114072a140304030c15020d 71
    0x259600184182c0303466880c5028000038440020307200d0400c1000b01c0d10b0260b00c20b050b000c1712003a90325034040000004044074402c9a9000c0c40c07108001107482078008541002d13031400c0080801a440c1c40303507080e981c00448187e5a50f91034810b0760301000320817181d550040695401180c605014201f0040c802e20541c8965041d04580000c08002c0c40072f8101d101004090100c111200107984504000b080c1c2c0c0100d80c20341c0d10a0000780003900300d000500c4c640b4042c120081148138400c1c400d50340c1c40005002c414080d0100400c2d0700741e44084c528107201d0302e40c0c0b0102e16111781741c00500d58a80341f425500746400c050b2000116034000781540d03500d112080c1d008190355481041213034891108928010800c0e4a100341540000d0000980c1d030701154842d40583e01410082c064250a000d05504195007a80c0310310000e0443c50401d10705001c06284100c84000c5081000303102a0182c50388801520a102c1161503a00005010000c00511041c0c5c40010700350300780c1c42c07400c425070610042e485040d106811414 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 30801651 1250 30800401 30800411
    0x20a051e0f01090302010506130207020307030609240203060f0409170a170f040c090902010e04021602090903030708060a030309090c03020921010e0109020d02100302070209090114010506040513 85
    0x20000c1801080d100500305802005062610b060090103040e041e514103025000e0300050710301081d0240203e500d2a50007600401201d4503580d2404010aa2040300740c9080c1d00b0b20026140c15500c189190361140484138001d600c1c1c0c01c0c80c0d0104100001068141c40c400c82c60907550500003071304c442503000e100805a446035243e10714148192200c009004060700601c01200400085104240f81103024600503020007062a8986100d00121490510044e0200304414040c01c5946000d070002c02c2c00e04100050100324501e154042800713035105541c0581581c101004000805030303c2441141c3c000e5003111003c00b46859910082c002c91000e00a144400c3d0311940b411b20f45e60700980481e10301400280007480d1082c1c90400072005111200c14901855003000c000c01c1c000c180500400710001c1c6c0081a01a40003159820800c0503c41c0050417418141c00303201003800360b512307082071038800c1e01e0420020604a1201e10713507180e0080141c2200744103840074441440a5291a210a6130030300c503c040000e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 30802901 1250 30801651 30801703
    0x1090b0409230a05030a03060f06050a02060a0903210b0f040c12050402030118080a1206080c0f040e030a110609011e02070c03080a090e01050901060c030518090a05090d020a05 77
    0x2040c03200180c1d0203004c612000070031039135a540c598407000490704030559110025803100403c6403036100b1011400c0c0140d0050001c500761003183d40c070802d0381c0d0348a0304111890018040c0c101030400501407110540c5c560361600320b10541042c88801601c003404075020031080842030300207070001c0e500320800760003aa980d000181c11034a095118003011118904e451488901500e00003419074050322405d00014669580d8a103195428003602c403c0e03070401d001405050f40080705009800c0c0e4a4121203030310544070f401088070381c0310038401051040344903601e41c2c0b400da8500250900e005400b8000901681c0340044a6544a00480030400407040340700003daa1481c031030401c1d010091080c0c0021b44100c800003501295250080c0d80c54045448100c0c0e22891a80e0383c0c0d082001007102417003114082445802c0900000703116000034101d0717840c0c007822160a01901e00114800a1046a040003500d560f00d040c8142000b0410041c0c203038230700b90b10080c0b001180b250b0b28680c85034000e1000125402d40348010700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 30804151 1250 30802901 30802903
    0xf070308070c050a0807060f05280204030b0a2003060303030103151d06070e040e060601030e07120f0209090d0c08090102010608030304050c09251202160b01090b040923 74
    0xb489803c00700b115034150040c2450000383c0d02c410070855845107041202d4110010700d0240610440c68014a54041091540c002d00e41c0005090355a000b542c2c20440400010303030070344200c1d01a1407050070010b41c0480c9495960514400caa41001412000b4010084196400030480c1d06690340445840d210034400720b400409444642089600000608903d14143c800020704a20580c5203a451041140500040c00200c4038a0707070080b9001e40202d0b001520340c3d40030750400304022114030101c4107480e5841121002928a514084601464074201081586041c44e032060708170f460f80f4050201c591100340064070440d0050801000e20750080344115007613000303511100052006a0944e9902c0c80c00e0301c0d20039110024038000c40d1044060704041109039040e12403081001041c05200e181d60a1241d00981c0c090408045d00208a5000c11290703401c41e40d025061907400780301c3c1c490707403c055040070000c2054400380c4403014010b0b031030102c0d5440420740d0740c07881c0707107240d0132100c05544240041c051103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 30805401 1250 30804151 30804167
    0x70515090d06020c03030a0f110a02070b0a090f14030607092312010f020408010c020309030d03091b0303170105090c09010c020607020603010b0301031e0201051b0a020301050a0c02070503030f07030807 88
    0xf81355408040200450303007600d500304802d42e0701c010404204421000764080804c1c0182400400140e000050501c0581c100e0380041021811901b0314045e195a1100c041c04e081c0b285030401140303050a68800506410704000380c6403c01d405041100310542042c51000318a842c41451282454404031a0340b5503803109040301508801c8800240140781d604030003440a98494480e10f1803a600c2c103030340c0210091010041e9000200000e0143ca001040a5001c4024140c07980d42541c2040602140209001990101c800210301c20341301e1013854a86204203031000e060507808540141400b40030095034103440030807148241e50900700000016003034004034030301d80581c00000750440400000401d0080160000d181281d100380005d0030441441c00c4080100a081e9100030302040d018801d22049174500002c010444114508880614204d43c0000c0d0a640b02030300e041d07802d140d56103e0b42a21030b0341880454007815050340190325000c0c140801803040d1044280140400088101103450107101c2e001c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 30806651 1250 30805401 30805417
    0x61407020108060906180106020304051203030709030308091903030902010f0810060f09080f0a14010908030f04050c0d0602031f080607030e1212010e130b010e06120a050a05070515090d0602 83
    0x1b01c101d00d43e19110041d54942c09070045610481001100a80c81040042224400c1006da41c50f10315862440d641501e000f02c001c3c0100c1c4450142c4122844100710a1001c00303840b40c043d50303000c2120010342c000540a28868100c6c001005004c2007008801404d00409808035446441d0221415400072401c8078050065000101c0d1402010160209070078006001c03000f07180183c03404032602003200c1c3d420342203410551004201103010300010b69254104400c45512500480c241c91211121400081101802c80d40440e449a4084103001384520000b0224004100c4003805002030341c1023407210766607003200404410400d500d40c41030040131700e014031006e111642144005600d60b48143c0f0a001808001d01500344421080000600191103a002180c01941c00c20828000c0c0d07400c04c021108802002001242c01800c40c1500c4e10003640b00f04450040a4007420242078044980c3c5400b60410803180c1c001449103060a030b0030703c03021548000304e4011740412620f0000130303a92490f144c0b000c1c0c01a109 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 30807901 1250 30806651 30806689
    0x3060c03040b100806070c060912030518010902060306190b0309010903030b010f0c0b07090f080a02030709020307050d15050603011d06040c020a02011404080a0c061407020108060906 80
    0x510000042040140d4003071485114510030307641c1c860310484666199441241010f030b000c42c4c04107015034018550110014055031012800106907110b2035140180310340002d001907034070000c00c91048081005505441c05030f500901580f2107940020382c0b540400f17024188150040b13100790080401c0b240c8000c0c01041e40d040502d40300d00e07040c0c0fa124002d000b40c900540c04241440e48000c43c0390b05c01d40007403a010716940c0314480c0b42882a00c485031100c000800140078012040804038514000c042600000c0052000804252000d84180340c2011000e601c065015070050090001ca90b41020555094070f5034504005001101800c000c109048240d2006411070030020011805104c0c0d2241c49000f03001c003848140c5c40303482c2d14050100300c8040614100040c2c20203900400190f100e0300c407580c070101e400641d0b581415100c0d240340d030404558200c1100c0c5c3c801400c0d410448030343c0001054030107403d0744280c1400c1412540010742204401000148074000d03280c0080c0e06a9500d101940800403c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 30809151 1250 30807901 30807913
    0x313020405010b131a041203090504050109020a12021806161e05010b03120301140103020d020a0e1914060309030d0606090f121509020102030c1015050301020c0c12030903 75
    0x4032040707a9200040c40f5421001c2500007007021002c4042d081c42200c203c144240c41c247c50b048260f045813240344011000c0003a200000119940c907401014040e001131500140d81c0c0380c486d5030103016050090910300859005000c24100511506040710803070609543c0c0d01e949181d295245216440060030083c0f419220540c58510282e85840c482240d502c146c00170050020030b041010b42d0f41c50100e05085821404100502c6000541d000d811400c00c0d041c103000d401c007450044a0400c0e604480380c41000910304110f520981e25051003240403003217408105d0103034036040481103109100e1403113849021303540010200b070006000304115000c502480710100b10307994075150010242c1d142440361200c480d110701c001060f41c01c801d0038805c90140c0e005a03402d003580c2c040d40c0f030300010702444c113010780c1503000a2010f00c0300c010f018455080e2429420800050105880140c0c8103001d440780c000a0190b0b1040c804c4504001000a0b08905202c00710f40c0c140c50340480a440514510520b004c41e50940a40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 30810401 1250 30809151 30809159
    0x15040305030109051503100c020f0a12090b030403170408071a01090e0d0206040b0402060702090f0f07030603020603131b180506030d20011512050706030e0c06031302040501 76
    0x40a50b05035608840c00344941e40300d44801009007520588160742c141c0000c804900d00140d180c0c884204903401d801034507a943d090601160502c0040c1c10190f0305003040c070903061400c652002a4202602e1030030301c0107045041c9134400401400c104810002040c2d2030030045014072041c10203071090141c2c00707504080c045890f891070a82d26002032196500c084d061a04030080281c0119200568600d9a4000c16082c0d07030301e0301c841003070390170152090341c10200400083c000343e1160317410144900749031180c5110038201080464155100204070504062820000f800141c0e2160b0490f90014a9629000207984460070f22500d40c0010b04560080400383c00c20015011b01401a021a426100002081140d44de402410b4840d01e102c8107401c0060644e00d080d020724a1040c40407085c444840c000002c083c0c801820341c084807225900500741c840e01d46c201d154100142002010003400381c6103000d120f05001403c0d221781c4c7e00d125419040c460030010000428443c404242c4608060300200107009a59403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 30811651 1250 30810401 30810407
    0x30c150509010906140105010e060913020a02030705060c03010e07081005040c0210060f08030724020d06050f011107090903020102070209010e0121020105040605030a0906060611070e1003080903150403 88
    0x141a40444c3d005042080101810003202c165504849061311000a01e40280741080125480b0104503548520056002c0700b445902c0d1002d460704481c503800641c2d58640d42d0420071f19140d001040c012544d60204010300108031101604c42e042400b60070410780342d0f281d4840e41d0a107040d441c0c000582091a2201d4000d0740c650000f24150305c0b0b607200c50104a1a6158845101c10f5003050207030a006a00402001002407004008480018203c040d4141242c540200040a1303030f1107420750a0300300c1d840b21000d211500c0c01c858882c4150509003000301c0010100170700d054407074481c0d01c2410f201c80c0d920f00007481414001e404071000310b41c0c000c0c40e00e8120760710f40c1d9080500c840d0030700a0903005180e80c00000c900800c0c1c0e003c4444c6554058450700d0405290480071251680700401c3d112016407100d503900c000908134000c0c40b001d081d203a00c40800c0340702c0702040d613440c0429a52143c3c440400d0b00007882040107040f0110002d503504541040c0c0d41d83c59020200c1c0c60000912420401808100d00700020302d94 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 30812901 1250 30811651 30811661
    0x17040803100f0302061605030d050a020d11090109050405100906030b0106021c0504030b13020607050a030201050c0a09260706050301030303060504020901020613110303070503070203060f090307030c15050901 91
    0x10004040301281c07916101d01003100071403804004e4102004000b084907040c070311485100818030800440340b4082c841da802400b07440056541c18025070700459014070010307283c002c1c440c5d0040140c00050400010a0008240c10440d224583c011a031310404035440c1d04032130000801400c003840082c409641d90307284c42803440301c003441010014001c04c10035441110350b00601c0004000c042d41c426041504684900c41440c402a01344c0d03200c036504030034042c01130311080007600340c82d405400941080511070a003c1e0035107000030040b20380302800f0050206441d400c07076228800e43c2c4246816403030f151030f031075407140641d48084150b0025204559001410302d9101e00190305803403181c0c0d01400215502c0080c482640620b407481400f680100000a40e0102c218444c44031644c0280520422a0704002c0424203540c02000103945c40d400020b085019400c0400400c0e400c950003541c2d440440c50407419040d00c0340a01da074010100800740620300300b848580005070780384410704a002c0201e801d16040e8640284 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 30814151 1250 30812901 30812911
    0x50d050c0f070f0b060102060106201c03050a141e0a0207060612050708031c0e070306020a0c06140702060103030f09090c0807080f1902090402070c060314010902070201020a020603060117040803 85
    0x8130b41c0002d80a51000c00d01c103041312096120b40f400003020780080346146110341000c480c903214034444030924003540d180242c140d07040754600003854100303145020213861043c01102480c81d0440c0034490461006020b00c00c0300c01c409011303901941c07a030300c0551010340b103142805030460742451404100154003030720b04a0500e1207401181e1805a58042035600c0b4040c410100d0000c1c5103c17490414102d4654221411402e482c6003a00c910b00d4172503940c0400ca07000f507001c090008052142540c20880c540c030810b810003081c0c0c03180c030400d4504001c00a6031007105000080410404054148980e0302030420000600a10031041c030500d95002002000344208494140026101c500400c070300f00b04500215000b80000d02242405a142e209164040d602085030140c000398200a0140030440096400d00600181d5030045002d40c425052072103800d074107800a074180782c41005410b0043c0e070009240051190b040e10309a0701c1b43d55240c01a91281001c087c0506c0e03100c2200c04220030417807070f036009610032 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 30815401 1250 30814151 30814163
    0x20301030515090111090f0f030708031306030e0703061119080403081f030209070203070510020406110f060a0513050105072705030304090504210f030c0807050d050c0f070f 76
    0x2d540d4640d14182038800f00403150994010401001c2c0050600000c040c0501c0000f4000e00400120400460300d418026400304045400211360071401748080700b241001007500b480d044c400100c590b1500e0f03481e50050312000309420b03614001e07581802005800c0c2c031640c8140001c020702603203450b1380140c42c1c640110390031000500342500084084040200c002d000c1c80717480c08420109800d540c00d100b40d12001070070740e00c150f01c41030103403000107041000b0300e200440c03440c2030243e2994507010029042820090f1000555003252500b50400400007400c0703944a22680d001158a0301c0e101c80c0d441d4461400000504a5400c00040003445500420b03800402c0030403140011888074212404039002610340181c80d41604104010070006001d0741145402031f0207a44e5090009006690001c0880300440d44d10020925940341e9072421601403054245030005410304030307030030328042070010310a102d1101003403e0103503904085a03141c00c40300180ca1601c0d190841c4156518110308060b40040b003030b0030382202c50f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 30816651 1250 30815401 30815443
    0x13090c0504020f0307030f1b02010e0d02070812031504020c0c1e0607030c080904060806160203091c03020703120315050414042924030a150207060209040203010305 72
    0x305040c01e1085607807800700b103110307103045031035041044020b07101304140000b62075100ca181c1c5482c1c40303001d040e1107100000c0e9000024224030410807a0300300360b0804120b0003590011031042240003000300d801406002010304030b0391303030b82c0e81e42c0914000f0f600c2000c1225007040c804581c4072425900080c034900000011590715541c24000d40042a641c840c0f14025a0028014880315002034040e01c1b40e82d4829124104840c00d0029a00126081303075060781c49a0640c1e40070a09012540350000740c4817404916501c051880c000c032400200784030700d141d0003481901c0c000b124a04000e06200744070b240040d541c0a0401244c000c0c030408020080d00b490030107540348407840400041e40c0e2400d84691248004002c010320f2140c1d50f2525000b0302d2500704010070001102d044401051008908009032003a519444481c071420000c03025644100c0d015181c40d40240d111404401c00310791800c1c14400318440301d010240e80d4400a00d4044042d0256040e656005400403001200f00303c004034094220a00758002100 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 30817901 1250 30816651 30816659
    0xb07060617010b030712060e0303070c02010f0c1e140d0206090f0703050c0103090218090105190b0906040507030b04020706090201030c0f12050601091d1501050c060a051513090c 78
    0x300300ca12490700244e1561121008001311018400000442d9014030380024481d151150001e080d03501c2152148000350b07400c1c506c1b80c110f40e040440284900c1542c5800e8444010666617510050f84c8803010b0082006062800c10030058075404140c601c0c0301810607101800034064002c0e50b980000d4807000043e005040341011a0180000d406044035004401070071850f0f0b261006400502510780d007070b44c1201801d0450f9100d03014110300c0e14040c201a0b8000680d601d0503401d2201c2c2d81c0450f80018408a0915400ca402962070100f40303034200d68212000a103640720040107030b000380500740041d600130340041600024081c0b540c0c80a1411030003270328140405c1101d844110b605d02d6070f2401403c0400d1043c1202900c2040a41c007496000701c06041841c450703910303042c0907a1b801001f1031402150301c20030010844110140c20305103401000070700b061414201205901601c60900600071409541c0d20400580c09218030301c2600366200001e4540b00c0e894101940a82c0980143c2038150350801e0788600020b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 30819151 1250 30817901 30817903
    0x106030c08010c020304150908030301080601030209060402161103030c120403060515010c03120906110315040605010e01030e0c061303050105130c050d05120c03040905180618070b07060617 83
    0x3c905207590b02542c917160401d603001001d4403000484108004c00600301043c0401c0420046000e0070282c8018060b540c9584100042400d005003100d010310b00500c485088021040c11441da4184d1016040d02d00c00405004a407947c001c10b150b140c40c9104800083c2d01da901844001c01c1624020f06060000d6500e0203154441124090a07090003c0c6508101c6801b00744185204406004584400b18410b46585ca520066408015054040000001c1442046030208903d8403210b102030b1014030072207180c01e0001e400d6089103042d06040c96180da03501701c45410300b400041d00c11280142080c3d212243c0c1c400404502405000440e010b601e0072002c26402d0116290904803180e10500c4103480a0814052090200081204540300d20a00b02405065000c2d00d01074110b001d4004003e51b02c1d107151205501c01c3d6180582501e00a40d15039180c0c202d000800f1680903400030005951103581441d1340f142d2842c0c180c0a90081c2d507080404a8003004020700c1c0d404c07040c00c458041c410400380714040c4101c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 30820401 1250 30819151 30819161
    0x224070b0a18021c1203020406030c0f020c0f0d0602040b031008060903030a020705011514041107020a140a09020a05040509071704030810030204060e1e09030702061b030a020106030c0801 82
    0x50020407401c14291001031a050581813051201c2c0702c10200300090960f00c2d1010f0300c0b11000380c1c1012903000b19060203125458400c8203a8440203150491558074000c0f07020f925844070313046840c010a0b55411501d2940c44405564141e0355110104568880d40c0711969175043d002034922602025500d01c00080d00c4000048407401684500059842c4d40c41d40407200c0001c0d8091042120076540b5100030154141c80442140c005010910f5070300402c40310031b0304100455a540710304240c0118180506009030b114480140c064840e043c0110008080d01e030001041e402e05d0b5032240e0b2100e800042e050846560100142c0100d54050314118a00d484400c010713182042c0d40031007602e03030707512510014010038480d00407940c00495a05010394925100e801190940c1c40b1a00100c80313000c900002d0003004464036000008a607501010506582488921541c0b20300c20003030f01030300c101c502190018100c4c00e04021540c0d9940b02904880e83c0d01d0031000e0290291240e41300984103000026000999201c06001d8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 30821651 1250 30820401 30820421
    0x4030b010b0f030f060f030607231201120302031207030204090b0108160e011b0807120503011a0904021c0504020f04021c11070204090302030d0e0102041208070224070b0a 75
    0x6040c00e560310314485509296006280d0760340200d01b100200340e107440c05d0100030701404440da695079203001408402c8000040c000794504444504012000741c43d0b900d50140c50558005524503031040100e41012860344c024428101403205901c414051a1509a4014412100f0002041c0030b4507848200550718001c0443c2c1b441440b00007181c7d0341440764030400fa104085d0034141884800151002c941d80305640e41d200301201c120000244003400e2200309100c0c0c80c0412103c2c40c02500e10341c18011020a400c491454200e40248085000c03011a40d55070182c0d401408044a10a5610034408030200030b080c040e0303410390040f0718a042154150030700b402101d001070178041c41161112000c80d6402c004020800301103601410601c440301c01030f0b0340d0b0300441c040c0502a40c01184c460024203801d1089a0120303202c45440da00c10041040307401003170b031034101a46402c000002d0b200d21050002c1402c104543c296031a0300c420040b54080d1320f044036800303409003030700810344400d29541e1030400300200e503120380b0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 30822901 1250 30821651 30821677
    0x302030403051c0e010608010f0617030f070501020f032d0105010503150a031506060f08190e0f0106060207060f0e090f07050d02070302150c19050c0a1704030b010b 72
    0x80380718100d00e290f8125600000c401d0500003074150914410508540003600401c94994661014140704011401003501802100c1070f05240c4810421a8a80c1c80c070440001c0c1d1510750003c03c0050901070b0a5043c1c1d00c40c0c80c40d50103e1503607440c041201c2c034207814200c00502038040103c006004e0f1010b11a804a0680f8011303100c092840d144c00d4041901441c80416840d80b00c00c0d001e10103c00209850104000c481182c400422030314203021020304a2103481c0c4080e020040310000304100004003044c0140811a0200c0007c0c480e140d01d110b0b42c0c100300080f0a81220380d030a1000006940384d00042c8030084924698401040c05514031040b1b90400c81c8200ca2503115200c0004140c0000361605002d410402a0a0a44c6070650010091081c2d80000c2d00550140c0c00190702c02070201443e80c20150b01c900c402442c2490b010000850100414103440b215003000750115071003095640030001501c001750095600300c0d083d40e5540e030441361980140002ca441e140a0000000d086000d8019503010342d01c030003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 30824151 1250 30822901 30822907
    0x2030f010501141608040317070f0b0411090708010602070b040305030f090a030b09010b0a06031103040b061909050a06060c05030304080a0c02040504050c04110301060e0105030901090c15020d030203040305 90
    0x10740116401d030104000840700c404204010783c51243d00d00700501242d441001c0350707600c5d01d10b0750905207000d1442c801c840804c00b40412403000021b0303007041c0300c2410503444211200d0540f51418000b840448041d10250423600b200248116960803900345412200e0a500b01c600150715044000518040e03403000400c60307481480b09a103644092005028107600c00307008140d0b1384d41e03251521103030038406850b8940c2d1a55034072a0007501e030802203c1c2101512803400e05101c000d20b00300041d501480010409052000ca0a0208406541c2c6103000480040d00305001c1c0a03040e1581d40d014010308003612580017040c50094005070240c002d817000092190000082c6045072385903141c00345203034002c1035032130108415100e03182d00607501c610899006501507001443d5030440b00307040c482295100769650003111030900c01084890382c00480b00e59080760030719102d0b0302c82e2510f0360894098113983d00e000341740c240700810108008040400038200000f05d0360886183c541c0d240000c0d0100e00c026100079001035010 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 30825401 1250 30824151 30824159
    0x12150a12020103200304140d030506090c0a0c05100b1f0203030c0c07030203120405010e2b060b030105010905060102070b03070e010c02030a1502031b030c030406050606040f030807060c020102030f01 87
    0x992055030003ea415507986103520310801e0001e8031754030031141200e526100a00811003658208a03440c60850710b41010007040c10300320009084000b004021944200f800101060b115101f200510010f5900c8412603500c080e410701d801300a0191055070b40c1c02944e5104144070a201860045200240c05801031440d544842c0c80c580041d5004880c841c040384503e07a000401a1010000c10201001684030203880703d080100052680140321456032041410380542c0b804100c2c1d01c041c408140f880c0d40d01303406100006117081c001070a03230b6402c242d0340765181c00e0000811100c41c5d0030885c4101400d03829951881d07210313800c401203800709032103000c00164500c200600c2d0354001c03001381003d580001c0480c0c00d1004203640d21155058644a100c2009802009000d405d038064114030782d00d800690180c504510304143c60302124000100301400c01c0e80c549000c2402526084120307800ba144030040b50404544a0810903419404400c00301c50703c0740781c50302c9911254418801d5a0103401d8080b203040c081d074a8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 30826651 1250 30825401 30825407
    0x50702060a0c020118080a060605010e01020709050a060308030c070c17030a0309080415090e0603070b090d0606030f12080601030203040f140708010213030c0608040201080703050903090612150a120201 88
    0x2c1c41d5401c9040c0b101c5014540c0003081884a43c10040c07020070002c00c0d000c1c01e10b181100545d201640038905002c2c1a441107d0b0700d84c7c000c100c03d01544c41c1c2140c00200340d40d036804030b440036000e55407002c2c05288001003804242c02d41c03c4002d020b12801190100d5145603a11081d41d09089030b40c00300c0507140c0040c400e010566100e6080580d186004001042c207040d21000f4540c2c0044a88100c40e0120320442c504001c078171940d000466104030100c01400f05075140000352500f03441000c0c83c803849400341400075020001641d006402554210343c044889a82c3c900e412400c401c0d10060381000b28a80350b0026401c0c5d031280c0200d038441c9074000e0142038482141c1e542d01094a566a8a00307407103000d40100403074440d40074400340407030617441501907201501d1810088441c4507240c1042e0304101c3c1d444100400b50343c005040e180c101c00c081c0b5000071156a0403942a085008801c091640b0030000100303041401041142c0301c0c000c8002d203c891084034040d50411513021054442c0106c15030110748640d0140d80 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 30827901 1250 30826651 30826667
    0x30604021c0c03140c040506030304181e06171902060703030203040f140106030b01050301060b0415050409020403030c0b060406030309050f061210180605060904090201110106180c050702060a 84
    0x489042c040c02c0080d12991180e8076502d598480051540c004000c40c0c800b850540586500000141d01852a04e410981440700030041b011070507500b07548036400c0c2d0b802070040041a49021528000c200a41d503102e00c0c4400742c20324840301c024a507106040000380c400001c0742c0b03440d0b40d055000307008030b02d01415560b0517800303500000c000741c40a0f0498a002c0c000300c0d141d280d808050b11445000082e03098210702d400c001c044010781066000b6813408509019840e801002c4500b601d180d40b8000304440742c0480308403442e12658115215580c0003040000c105031b00100e202c034605105c5c6805148a59680e0248003c0b0b50543c840600042c0e907542c0300308554106450060480070010b040b0f945020180b000000580300c0940303007100b503001d402008000702d800740041000000050b00d42070000070f25110004003140220034003644103d41d15150351085a010f0100741000101c3c0c1070003802a02d41c0e98909040051803035a1012a00e4140b2090030042d03407240084400d55507004180505040c1c100705c0407a0101 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 30829151 1250 30827901 30827903
    0x60504060801080f0c0d030e090c0408070603021c09140304080309090a020c06010e13020d05060601030506010c1a06011101050a05010f05030102130909020604080a050d02010b01080915041b09140105030604021c 92
    0x4045400c02301c00a40303030184058030031031070504141c2d41c40e4540b0b5255071605070140d22038010948188071249070900710001400f50000082000710f400562420040c40354401240202c80510000400055170400403000c4e21007084200c034000784030754541c6002e0040c1d1103401400c40342e54100314014007150613078401072030b04000c03a0030002444103000c1e03000c151500545d0000380c0d4268841e1041103419030740342c060140d201c8800e18284c80100613554804a09942103009002c0004907040040e581380d2044002c0310170481ca6100038842800d004c15044010702c802e0158034541500d041001ca03150505008696086407131010300c1e04c0043c601940c91004090111049900c401c04000000b12200308001403000140294098803040400b204d0113405c47e00301005c10b9041c48100c43c10000e500c4c1020681c110340f0510000710f44416980e529004100142200c1c6c000d03100c402043d0007160b020301680c04000c0590303241154102e07990700c03101003541d2100c2c1150000d611982003c2c1c1000ea919a80c0c80c01d640c05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 30830401 1250 30829151 30829157
    0x405060a0807030b220f060803040308090102010f0606080613020a0207090b0f03030f0a0e0307060806010507030e1009180e120c0307060204120204051005010210020a18060504060801080f0c0d03 85
    0x580d50600016142174403982541450003480000c8000354000744a042c1002e60b00a10030003246162000d1030b40c0b24000c42c84007906101d40031881044c242d00039007103582030cc80200c404104080d141c0c4070103000c556085d00e0341c5009146850680c501c0452600c01c64060440c07179002001202d141c5081e14001d40012006a40c10046004886945072020800340041600140c40c540e1100841640282504021140d0714441d40c840310b0b0401a803074218482c690040d00a2800940d07400c9142821b8030404440002144c21403556402c070034a039580281000181d956120348041d4030f200c125140020b40c0c2e104110094142c0040303600b01140c1e4800402020b480c00c110b01503a003003050540741c4038102c2c0c20681c00458080340980d1094114502407051a90044200d06a40310f16800e04000079900c140950f80121413550014140310b0b054001c04c6070109c1e038090100040642d58032060000d2075500180324020103d500d89001003903135040410031201d11b502a5000300036000720f01d000c02609a0117104280c1c28 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 30831651 1250 30830401 30830411
    0xb0106031a1f020f01061401021b0f090a090c06030c0e01050c0c280602010501170102031504020d020d020403050a060506010c0b070807030f020313050d0c0c090b0406080a05060105150405060a080703 87
    0x80304c6400c2c01448003c180710001040700c10013941c00a03052600003490410080130b046980300180d80d8504503005400401e031170b07180007a40d032a11140020140404050709040004200240990703064100840c0b0840310381c0c3e40194030b41c21400564037401030900b6a080c0340c110218501031410818007080c0d00c2c0b00400080100d03410305400c83c18803801e05410000040c3d454500601c1041441d1485000c40300d8054021484c51500500488649032034000c01c0d4407a640000394642c10030020740640341c2d80d11070303450210b548554034504650354404d10130003241c1c2c1d0b5060000003103466005030001039013113410501c18295952000c400f01c0c0c103020024017603014107a48440400c0d03001c905101540c440c607170086072203080d0740c00f90914503d09010507081d00e007089020443ca5001810b00d141c2a401c41e001c0300c00200301412407200003005410700d50010390151040340403e4040c03010003d001812500700365021042400d980c0c07421100b0788203502549411203401c00000c05558410700000350300c92124130300060 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 30832901 1250 30831651 30831673
    0x1107030204110708030a0606020c12211c090c050301091e020315090c01110f0d0c02030102160f0b0601021212040215030c0414091005060706060b04030b0106031a1f02 73
    0x26a5030004e8606c0d084180d40e6100911282d60104a04900d26a0450300641c03461183d0380000d641e95142c0401480c20410101c442c2c1408240d501644e10400e030740c00d41078005942e00c28074030b4000c0401314404c0e128481803000009580c1410311603202400e402500c210300141e2080490b488200750310350126014840c40e0950794070050800000c038046c004c0f001c040c1100100c1c1c80c000408120001070480005e82003a40b126401c50300c00241e900400f1054141081e6071061030002a00902a8410001c4040100e00c1590708100c071030b419400c041845520820403070b48034003004a03550381050b416140b02c0c480800c41c10b00c1e03003a03a9150155000384024001900e59801203100740f0260026503250323820b5000442d050141504240e0502c40b803080a4071240050b02e46030505024a603201e116040c0141e00020b01c0c40c05004140d00400d01410f07180f01d4465441756286400ca6280c5802d12546001a10341842000e900b500e24101960b8090020121a5502169412070b800320080ca0030080942c030600101003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 30834151 1250 30832901 30832913
    0x50f0d02040e090d092105011104080304050117100b0c0c03010903050a1b0b040611041203020a11030a1115090d0b09010b0102060903030a15120c050103060611070302041107 76
    0x240421442c0038940382030a002041c54000d2225501c0140400c205042c86400b040e4a20b88031a140200d41c0c0d074030411110304142e40100510302c002c400300080040c2c0400d100d4030000003081121300aa9075a0182c0d145142c80c00305000b000d50783d00b50750703060b400001c10507906a64050300104200c0d8003604e07441c002c1d800000b405c5800700c010840100b1008030351148141d8100750641c645100301100b0b1044401c0942e00c603800c0c0b410040000740015960151201f842d003242003a030300070f0329900300b68403d00c000c2424080e42e00d005001013200c580104d241030f50b600c1e04000c558900f5107980b0820b0421a450300400304508952480407543d40e1076030900000c2115947e40c0c07400140180105249545c82c10000e02280c2507811240c0e11505540c17042060245400002044a61002c80300c0000122403000c07408403002002d07a90b202080f044081e5a2510070702000356242400c58100341c0b01000155074512003030342c0650114049204680003044200301508150300700c80c00301704003a5130151070726a6a50701d41c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 30835401 1250 30834151 30834157
    0x1404090629090108191707140304050901091a210a0f0506100305060705071b09050702010b0306100e09010204050402070b04030f05090901060e0111011a03060105040606080403050f0d02 81
    0x200503101407501d2034403040c1c206886403c0c05401101c02614001c840c1c0103014a41d4071424100a062100c4910b030001881441e000781c034042039201104d000600040c01010780c0ea5007041c05440d02c166480c00000590020b1845101c102c445404808071040e90103004104000ca40d10101c805000104004990404070900110311741d503101e141203c01e202c0d81c6080c054a0400c000344400354a001d1400140f010030310004046501c040d0782d1030300e0741e034170045403404982550254a001c441c40f4035a00020690701502d802081c46100b095008024242007002010707524601031340c45100c040c1062006200e6002e480c12019407200c903200015180a555001180499100e008140c1e00100d000051000b00340d804000d81c0c0c0034002e07a00d0010704000ea500c0005a49680601c242030501002400715501640201044540700d8401e000030010343c801070700a02d05030914120070310310901400b00045103a2406100e12003e40c1c40c0c80d0b41d080990380e01c0355029034042d84811070b86600b40780b05001e00d02c0070003128001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 30836651 1250 30835401 30835451
    0x60c01060306060b0a03060e010506070213230708060406050105030601030908040b0a02071a040308040509040f050a0302010b0f0105041214031c0b040606050c1005070507021801060f080114040906 86
    0x40b585d0390804c2074401400c80d00c181e00328512502c0c50500400266440030306a450301074045901048540c9002c03c040001c0c1030031181714010030909101c0f09400030b80c94121503c146120388590825588c0c213000c02040728101d009141c00b060082c004074030a0352080c0e00040c1003070300c1086805c0c43c007074450752110303817640040007803400590040c2c106200c1405105400d582d848070f540300d17440c1014210760301e030365041c000c07802031a0045400300c0c005001c1c48241c134140340d0420341000549a28940e907040017800780040c0101d6901036a03075068901e00070352141c3c045600b15403000000e00d22000d00350342c468807200c002d030090280701d2009010f040c0e0807140c02a0301503c0480600800121a07020000348002d03a851644800140a0240070320203403070030b020500d50451440c44000140c29500e21f0419a1140581200690018464420703541000c1700980b141e41a920340e0303100c0b0742400b06041812110141d00b40240f00340300306100502d03c081c1c01d140d0415a2541e10901021032000c86e139105595040c400340003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 30837901 1250 30836651 30836669
    0x1505040f0b04080f0609060402010c0c03020d0f0c06091a0a210f05010b0903030702010e04110c0309030f0a0818011209060507200c01080c0903031603020d0309020906060c0106030606 80
    0x301000f040c00100040d07494164038902410052070b03c00784164813440000c02c064184205912654208601040d285001d90390080840110740010708081c04203550707040c4100c40d00b1807083c1c40410780c6030040d000541100d05a400410300106210912036054110901c1401400040700d0985455a98100c008851903008100000c5e04010200741e01c0a0781c00603405144003840410510030303291000300488105a0302800c00c603400c040c100000c00c0003400200000344102c2404a088104040701000500648004038200c808041c801100562070703454005c0d006004940c00c0029814941c01e600302c0c4250725005050410000c0c900c40d07082404c0d1800c1c00c104852141d03581e810061b215402100300f94260185c0c092075841e11003d003808541d150354615619040c407221030001090640b44804035100c0220107015681c90380f40e00c10458915628801c1c048002d07000b5040003150782c41c401e1080c040784640040c0000b1698598a091000740e521001741620075540350b05001c00407500b0b42c0036000c001c02c4406 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 30839151 1250 30837901 30837907
    0xf0512040e0906060f01051b1e07061107060903020d05010b0d06020a170420031c050a0f050309060c09030a020904121b0506070e0a030605011805011502071505040f0b 73
    0x8910b5400e144005180b81c0c810780c0704c142c2c100c03000e0b40d020094070711080c0e29090300b1103160080c20855140488880e141d25000460b07150070002444007248500c1240e155855100030320068007911034980b08240616000148149020030152400300d41030401c20b40120000120503400c080031401784a200c070005d440039500054031609080d441000403900144a15401d041400d045c4c0e07031910020300001d541041402c1001c904052503405011416070403101e0003440810f02115000039181e600031010070400f28103c0c20140480a02410449100303020725405016075641d0b032040c0d041d40b50050003500d40c041c03213266280d00060311440112802030303000d4850100c0d102010380009140c407403040d543c1d2603920100022280003c10000d0074940201c010709010701880505004179540032a40d92000d442e81d0704103400050f00d810321a40320348440903051414045680c032023050310000c80c411a5502d0040c0c0c4600c40412000c92031500c011007044840c948189000d584188900c0b80111603008101e4440d000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 30840401 1250 30839151 30839161
    0xc0602041e050102010504050d050c0705060403061d07031101031806150f05010e0a030609030203090904030f030c050910030f0608100609140f040b100b03010e0a0b04020c03070f0512040e 82
    0x1c1c40c0203100400091001384540c1c40c0c5580c0d1261101c44101c800c0050100100e0700c00106c500500c42a0083c21024014680766907503400c100b00a0003603a00b40c81342000c1d08140c0c8904541c000700e108029280c0164409450000541c01140100455035508800288581e540390008d00c41d0300580f800310180c403460007040e03420249449540b0885501a0707043c008000c030ba19040d070300c0c0c11403030800300ea0708284001081002d0341016401d40c8600e41e41d0f10f42c080440d800308000c05401620424003a02a0742d820410004d90071810323210b80c406e08000760b1340b01100090300a4004c0c840d800c1400400e0390a48085880707681c1d1706400d4a001e007064036107000980c0711002071050503094400c01c0443c5254050810303031420182c620344100000640f002d0302c01c80c00a40003903a0301801701005001400d000c01207036503035a547c2e20140341e0b81d5400d03030300200c6250400310f061495107800c1c026070b81454074003c007451401389269a03030502ca90550b60700700c440c1d00810303880480301c0300c80394007174402404004104130080c600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 30841651 1250 30840401 30840449
    0x16090b09060301020a0c0b06030307051608150714090f040609020706050a050609010501080a0207020a030c05011106160e010909050405060f0108070308040b0904020706051501030c021f020a0c060204 87
    0x100500050280c1c2c41444960b03d0f03558004001d0300c005420047c00521030710b0381001b090451041080291903031043c200b0300c100a802600340d07013040f11501010b80c4c45460101d150001c1b81401500c41c0030000e49070380740b001040d80030031000b4204210002c0c680309090903004003040c00d82d00305600895a80f41c2c04504030003840606d0140691004465400f0401498070200154086806004090400ca422400100a00c0195044840e0250010b1109020994038603100d040c80d00c07240541c6001481d400850b44c0340000001e10b0a0284403100601111400c1138441101c0f0050111441e41c108481c1280008607282507204081c0a41c1c0254040d052510700f13040916503e01060740038070040d50000d0802c10214682c80e0a0f43c0c2614a440d00380d030b0b901c0030035a00180c003a00500c0d802410140c41c0105000504070403400c1c8e840d0340c03602078a042c41002d21002c0b0036a1180340708155145d401c40002d00c80320445455034000c20f1a070b800341c00c0c25024000b81e500c41400301d1b00035412003021301d52000c036144a4004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 30842901 1250 30841651 30841669
    0x4030f1202091804020604120b1006050307090306050702030d020403080316050a0e010e0d02060d0b0114070b040f14070e010305071208070204050402120a03080f06010f17040516090b 80
    0x912010740c80c0030090b80c007003440c00c030843c1814a0f101e00110007080c00c41d0b50b1202101c4c000d0642d00503190a42101d802c01c441411405e0b140c100c2c810740c0f410000680c071030080c0f06032031003a21107444080040e851a10303110040d01000380b0325021400f00708400c6980c0b4015102400180d4010180305403246000400307a40382d401d410481200f0702500b444511411035000e003c0d40060319003071902024019410020a020100410340250b00210100312040c111070158000c501c03009003669480085078010350105007038860352901802c00c1c1380d803000040209145400c1a0480e92251138125440d101400b4060308180540d08000f010741e088400401c01c1c0003081081d00040c200c2e211030b21141d408250b07070300c031070501c10000028051522a070008080d581c2d2030f0300c210420801c07001030300c048030198035004001d0350046032060001d410791b5000c10119441000064030840c4030340c482c55060f11034545060b850303c1e0000d1080301c107403081d180d600a61f072880d283c00500030121214003082400d688010020969 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 30844151 1250 30842901 30842927
    0x22330e090411060a0c050708030c1f0f0606080a0c03021c05130506040c14011706010e0103060302040c020102070b010e040305090909010b041409060f09030a0f020c0a06110d0503090318030f0604030f 87
    0x103030090042c900ca52001217010719080500c500784075442d002f006000e002400106100700b0604d4942000003070403680000141c0c2c440c00c00701350300f000700c014000d07020740480c05040084a04814122080044000241e00554000076003000e000c0201200d6540c23185050000c840848201500d40300030040840080300e8028421007d080140030490284a00302108400070a240c0c1000030034410400183d00a50080c0301554001e0020700a9502800019001c1d5000c1502150b907112240000140c499100103c0e034044c5a00d99103141c07412030704000b04003440b50003510030f401c0741d540c030081401d860343c8030f108841c0800c201c0c4207040341510b407159000341412002400a420088810200012448007008441c5251103a062000110302d042a040345415880fa0101e50010341c928804184d80360864030b402d81c4a83c000e800c0340c00d2821f85000131205408151a8056158000d02c4100d41c400c443d0031003088424000740c1104c1c91042c3c501ca07100d2604105807800c2c6e002c1185c400704600b103180c2c0004105c903c9 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 30845401 1250 30844151 30844153
    0x519030e150a1218111f020102031005030c0a03020907050c0703050a0b0f040f081b0613050106150509010e0d05060f06010f02010603030503010b22330e090411060a0c050708 76
    0x1450046a112092444d0003031005036144113804041c2e03141380144483d01d0b504c00560140b0350580c00068001d6200b80c031000d080580c0d4243c000342c28500050302d21000300c03000d4102d06ca042d04e19803d00c0100c04002e003410040c072130140b005074090307001084000011401040201040317666030030140c06114000d0a02c015041c2c0d400200700208400100f801f19050344812280e5682d880301c001340504500b04002801c09026920520500d0300021400340001d50051000304001640c681003e50109050041e107404904240b0190446600409110550701c802600c640800c049a82e500c508186048810126140034542448a40d591100203640116003900007040000c1c00c0d500d016080380014498200120000501b110001e80c52a401215040d8242c68820101d9101c42e805032400ca664180320b044d02d2291864a00d484440030301c083d0500086031101e050080704001070042080d402070050301c000b02e0f8510055400e2b1510310003855807480642d100e09802030180340060a215007544060300d1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 30846651 1250 30845401 30845411
    0x9011407120f05041d070e060a031505040e0d050702010207090903050a0905040209060d05041b0e040b1f05060c0a05030a030b120d0f050c1207120f0206040519030e150a12 75
    0x14141c030510042000070455089105c0d6607a0100119081200078424030b40050b40882d8440010390590489410710448400c69100627803603070184811034041c4600348042d0751001c0312501816002d6001024480d00610540303451a0312840c130202550541c0c07208600003030001030340202d0705270310104480c060300d0100c0c2c06515140307a03880020a10b002e88001031442594600224080018018840d480c1e00f80504c07a50451503512032442509003002c47c0c1c03d071410205100050060700c210f02e00e61480d145070250b1170341850304140c10f0108a0f0400702800281e03110302030030b050200d40104050035410b43c0d9650081a4540400300303200b2403007a206482800c82c0e01821090940783e070040092007041159251007500c4900d80100301c0e2a0a41c40e80d030400600320002400001d201050101041c11686070326008400620440201d035154000c60300900140c2141840d03801c9007084014110410340a0314009000c500d11400080c10203201d4035510758071100010340898229001104190020186401001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 30847901 1250 30846651 30846659
    0x703052805030a0c0e090108010203190204080717010212010f06180305030f0903031605010b0f09130326090f0f1f051b0307030b0312090d0809011407120f0504 70
    0x10280c0005003d09900035190350321040c003c0c0c403503002440f103108003c103401c00559640381e0f224002d41c025103d9800c000c40a9205003180300709030080340c0498030243d000b492000d14180780302c1081e80050841d48a1035408110075054103a4501080780680340c2c0711220a5954038000000c0d00800340c03500c0d10350b5420125241000800c002105036400c40c3c83e818201c41d91040314000080c150f200300d030f80c42405ea0302d020000300280003055101b9001442c09940410380100c80c9400c2218659080784c802d200a00c10410840001e0f01c140141324100150140320038070708800c56046100300c0b00449140c4190f41c880214108000010420003045201140141040e00c010150f1240c04050040503000ca032074a500105845803112a0a511404141d00301d854032400c010a00401038031910021511a208412062400058203401c031149002d004208030300406481e41c0750740e025002001014140040120784100c101603090081c60010b100308600701c00e461103048058800c04010045504104003400140 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 30849151 1250 30847901 30847907
    0x206010807060c03020c040c0e1002010506090c03150d0203071221030209090703020c03040e04060b090105010306051c060e0304030c03120306030f020103020d110f090901080307080301060c051207030528 89
    0x821a06c0b000e0b04c01241076004004d065604801d0054403a40016840b0b540641241e410f41c02207008880c11107003d48152140c82a18005020039501c1d80043d580c00359811aa92a15940411301144043d0070380e48001e40da218010207490445200364be03c1c0701c0c51040708a00c81d0303030100c3c40102101c0b1400c2c1107080c500010007148490308001c0200c2c0c2490f0b4009410003210804009a500030089030482801718901498400f000c1c007880c00c2007034003510300d90002203410341c02400348105960b0054581e8203050720031f030b885500080150000f03588441c2c0c0c2d829201031050060004001a5018190038648645580361030f29480080540c040c0415141207402d000241c454210250115024600541c554510781040c400419a0036140e020315500001c40c016028030100103400014805c031900320701baa82e28a03040d61a0b21034180c005040341c00800040c48454090250440a9406042141c07030110025030091314a40c0702c404168082140800c1c001040c03407017042411201e40c440f112900c44060960009 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 30850401 1250 30849151 30849163
    0x30705010e0304361505010e01032d110301080a050609010902011b060e0d0f02010b09010f0504020318010504081216091a0702060d02040504060e0c07080904020d0c0206010807060c0302 81
    0x900c81100d04119200c1341101c3e9102400f200710345824003088084150540fa01d245c4603944a0306000c1140310006088545c003d202e044001404031015040704018030300e40c0100c10341c5950724490139950702c4000080c2082824060350103007102d58010f120706002c600b13050b450420000c0a105080c1c0c100801d030030060341d0021440147c20f46020507045c841c210780c641130014201d15490651107108486e61800c9055115041840441e00740d0000c02800181406102c104c040900403208600001c8901b044a402c2640c001c41c1e01c900024003810303100008a42040c213485c000c0e02d080d00c08402c080341032114141a45030b42034001c1c101080039030001b00000307009044000640b18050000b28804000380e14400c4950071260300c554010711407a40c0b0201c01d180500250814040d550007285800c0c0081241489900c03424011072507409990b083c207a80e90ba94400e580d01000740cad960025000d0000040e070004e07a01800e03a010146401404496050a081d503241800581c030200411064400500111750040b0742 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 30851651 1250 30850401 30850439
    0x1303020603191407030501060306060206150a0e0103031101060902280e0d0f05010b09010302031c05070804120b0702280507030b010602100c0903020603060409021201050702030705010e0304 83
    0x5041d100c1d40d950603006110140010001442410444001051403510940d58031942c05902c0403c4582d0320b52030110211021409207001503403080d0003280600380210844c041402004250b4041c0944409020b0782048003030b8411008034048135811043e045081c0107500190003c20300440c00d04d121001200d00310340c0611032001c881c0b0328200d5841001032081300c6070031000402500d014981903161500c08200010703000e0907190fa51030000c0041541c0b41000d04d280c1280e40080c0184186003410000345d0b480a19050040300f0b0180c20807003580001c1a841c0030b040202071295152441c6005410507010040004100c0e4045402494100041d840d1369a0300d0302610105040201d15490640b500900d0b255030303500054110844c40c0000035800760f0019100508481c484028065185401000d80315a400c500000358007150500014809081603403000d20400d00080c51500e02d20841c0c60000c1c21218183e81c540c005802c0090207405000d406d0140681d8071103104011880c1a1904002e52810004045 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 30852901 1250 30851651 30851659
    0x30901140705070201080a09020301020c0c01030605101403090c030d0f020d030b1e0307050402120402030f07050a06030e03071205220e04030309031403010603091101030c0210022a03040e0903130302 87
    0xc0411f05545040d4049a0b84541c00ba008542c0c420842841c01d5403501c1c0ca81c0c07032600080c1052300208503410000c41d5500360f4400c5484190b4402c1011031b104913160802001381e444da12885403869880e9804010744002c0c1e80b220b03240e40d102c140f685075009050503c2550a101858104221003040d0344641008041e103a0900b2060428072220310b000a0412403c2d50000768058008900700107001d14098460340038904c02c50440b4003444ac00050035440751024842d079070740640c4880007001554003d40004c4202c407020310503a440d1100560f1840c40ca6601c00080000203100419801c0b10071101200241025070031070744101002e4905141b800d6800301c0200001d08042d01c420107501014014139245d040e18000c411410344035a11900018010100c00a0564039188484800b0700b0950081c403a4400c100300c0f503805402c20340801c000b420042e5125503d0201d96100131401c3c503580b90290b030b403040f0310034030a0302c0130703580c0d0b603141c0340e40c030315440c0c1c0050583c80c92504100910072080d0410f03041d400407a54195 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 30854151 1250 30852901 30852917
    0x308010e0f060f010c05060f060a0501020708030f09010309150c020706020106050a1401020a0b130606090504031710090c09050306010801020f0a0c02060d0c0201020901030e160b030c0c030f030901140705070201 92
    0x6004807074a8500071740003080c074860001440303412146180d07214401e00c0152600360000c0d41c0c510049070f03641c10314460481c3c1908104485012000d60070010316001e181030401080f05113182d6141c0c00e070184050380d00320703401e50b40c0c8000766900c50b818005d881c01003520744000c1c003602d41408005041c12441d481080c00038074400ba03800705d003030b402400101405a00076415020f1854007410303103521315a00940c1240d0386031804002061700c0200344540d40c0641c0d010356851008914456078a1240c04004c3c000020004203d00d00068095081c01349140f0344c415507403255a41894101890310704401070b046100e259005115101440780003500b52900d88400b80b178901c1e000c100c18004504144101c41d480060349003808030340040c0c29015001803d40d43c00c00e0360200310718985c09a030a61514400e2000044403103224904004844e40e40000d142c124982c0100d60b031500405031103291a5900403001e049204c5008070400c00340c03d07400c0c41803011000c1c21100d280d52034030f01044020074a11507410700138180047c0d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 30855401 1250 30854151 30854179
    0x30f0c070e0c0a020105070206070e09090a0618140606010c080f0403050304090506130603050c0103021b1c0f02030c0303060d030e1302040f0f0b03070c02011116030308010e0f06 78
    0x10000303840100120341865680d400c0c405005000341e071000310000f001d582002c2c045528244000f0700b9510405990b41c8600078451554104507042c007000c4c00b038003500e02c00c100014010411920410302c50242d4110044440c44052400c4221105442e000d1003194228000300225640c00c160a1036041d54440c0d800c0369680304040080526020301c0d003000d0558400807501190048007540110300a002c100c41c40e4071200c1c1141000002c0c2c5000740002001764200c240140502d502a0b000303005801e800460001c21660200700d140d160540d0754000e0f00440c681140c102d400b00da0800700700405c1c2c418900c061458801b0781c0c1d00041d5240b02c050f144502481448241c07509052207140c44050601d0005d1801118003802443c01000e90001d0165841000306032000080303c03080492000c1c122104e81c0c1d211030455581c1107060f00e05918006050341482b150140040c000e190901440d41c15005d5155810501401d6040c01001c009058208a402c034903076105000000f2040400541d20040031107424003050a4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 30856651 1250 30855401 30855403
    0x181b190309140604030201020a140702011d010302070609110a0806090a030e06070506100501120606021504210203040e060609010c120212040e01080f1504110a05180405150603030f0c 80
    0x4082012940b40200c0f0103000406038190024004c040c2c09566038400c80608090aa40c288106040240480c03003103402c890111a0040e61140454014140142802c9080d00c0b0403060700c80741c0100715440c0b181800b10020b54545040007101a00010004144610304a02c119507074101041c805002c0c003281d103000c00c1c9941d6a01c000c030b945855100003603031072504103181140350300a071900520f13011441e103440404100555228400031506598010940c608007046e0504002c04050029101015480c1c01e0808031505490a2155001594000c2d50340303924223004118040b81c05400d50b481351034200481e80d026a844143d501c911600300c40c1e0b6095801034490140d14211090203511020382c000304000500341f01b5005007a04950509040c0c030380103c40345044c56120084103d80441c0c5201c08004240451001c442c402c0c0c0b0071001801405565445000040410841d180088481d400050410080110074041c81c0c030794413540000100c940c14030000087d101d0292190040140034003240d0507030300c100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 30857901 1250 30856651 30856673
    0x20702030705040e0f0c10020a11150f0301030309050114030114120706030c0806060a052713050402041803090501030b04060f0f03020a060e0f01050f09181b190309 72
    0x2002041080408809503046455115003001041140581b40c02d4034a1400d0501d00e58500380c0d41e81e806003898112556414504403040d80f602a00302c802880c4120348140080020a800f054520120b500d82d85546001050a04180c00482c10048840e02c0d201a4442c1301c4103490640d40f9002100450751086400701d4044400d07a10320581a108641c2d0018443c3d4166111002c118110340d034261044e03503080c003401143d108003801840051410440752400040304034031341390380e0901030400b4211840320b0800201041c0f80001302614a55441052200f14503081c82404e426250900c58020300c1c04c00c0d52000b40c05034003e40305d254145500c5000165581d904c1da80048046d0950b412000c102580f195010000c82041c1e000c200d014244194010403401c0c05114004003a90000781840c5513000c12000448071078004400c0c12203049000e103d4080d02d40da451102d88010600c0200780001483c101c4041142e9060200304100300240800000c60070030303145421006805030600f00800c3c5040c2c10b02c1c0c00f1041708 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 30859151 1250 30857901 30857909
    0x10c02090f160806060909060d06090501060501111504030806010e060d0e0607050c06010510030f0e0a020307090b130e070305060405060406050f0705030403030908040801020408030d06080a080301090207020307 92
    0x141020040110294180649030b0040040100000c01070503041c1064031040401c0c0c40c1d25a100b5005e001c220000e190070030030958400c4010b841d0b041d480089640b083c0503511516422a096511004244010350703114481c07001380d00e01c0f100203080c000c01f5040314001c81c54003d0405410018114000f448076409600e4000d070a08024040c40d03a54407601680e0b00040903e40c072036445900500001c05d10191140c000c0c4c2e841002c400d406405540d1a201c01c1011142c980d11115041c184c0790103280b0755101c1c0b20b100b41c1c00c107151440e0107010034242c070344105406c084080d0001c00e02c80d860808400d50702e4661030b030180c02e042d0014800103481f003107143c4410302d003040590006206105e10070070803041250115855016510a440900031038444102548810f20200c40d140001042403000170080b034480e40041003894000e228a40c40c298a941006003a81e1090b0007013038465000107401d00d110034161003210002c01c01e900140c4981d50032030b50b41041d00e01c8103100d41148140c01203642401c0d5601485014014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 30860401 1250 30859151 30859159
    0x7030b0a0603020306030c0a050901120501091202010b090105031606030506030f010204080a060b0303070305030708070c051905120909071d04060909020906040c021c03060308072d03020a0f02010c02 87
    0xc01e0380c03a0303002000380d4030459a00e8024041c0010840d843d023460322100d03094540c0200004101d03030820110603450300490806483d659224910440410080741217480502465400071030f01d2650103003070188115040c0d0116019500421407003643c1c007286401c0b00c040e10058900440d40751642c00000c0d151007100c25201c2c01f40c1d4800038000038100d00c00118111318610426013805486080d0040503103c0c095154081d0104008000040030a4071541c00c09038042c2e40d80c00c1c810780700c0030991541450820020b510341d2086210a00000900804101d4140c858802460340c601d000703060004a114807101901c62014801c88840c520b00004100f0001c0545010290080055590740c0341000098082e00310140d000f05150307404600581868040c100c2c1480081d001444000d00b025900d41c840110034055404241c1c0c0c8180100002c1e80c000c00030100540101e5940005007002c43c0740b81038050441c51124020b50440c1c16002c0069000300d41441c0780750300095a1400c140c2280010780380b01d00c00120003544 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 30861651 1250 30860401 30860419
    0x120a0203011406120c010c0303091a0a24050a03110102070b0a02010b1003021801050f0706020c0102070210080f01060302030c0f03130303060b09060405100c020d0308041106040b0a030507030b 84
    0x100b24106640b40b40f10329001c82d0380d40200300012500e03e813288242c4403000d001600e070542d0080441d01940000c621940b144510540900301003c40c54901b01044d50500c0c0ca1a8551050741c02c3c0c00303400407400c076100c03d048010f100000e03c1c02000800004c85031200516408078600d1450311a03000307000c55001460311113040c60f503c00041d03200a00820240c65440d104200280070040428868801d03139511146001040000084500040d80c40f0b410908505031560390030406800029071a00142c007003c00010b0000d41c8407040d0b4810083c282512070340300170400034000200210b034201e01c1005411142d26090040c0c1c3c0b80c4400307031805a02d1141541c044a0761b1800000d1100b8116140520503160380295000c100003500c0700c151308080d101d009107003030780400b080c002404a841d00440c1540320450324207256010841c00c0c1d020800c4918460b10540200d2141d070104820300000c81d100e50f070011800c5917894a09810010310718041d00a00302000105603645000038041030103640300b00d4141c1402815580 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 30862901 1250 30861651 30861671
    0xd0204050702010905100c081b09150906070312060e04020102061308040e01152304030305090307080105130515040201080c030a09080c03040612020f0f130306060e01090b01080411120a020301 84
    0x809001d042c847c2c440020b08010008041c41d0704044402d52503807011203050b20342420310041203401c1201c480d810421900812205a02e03943d000000c14056200340ca070100f10031110a00101107500035442151940c80301001c003c0142e0380810540d500c59000c00c0f41000c0c506a03400e1545480c004ca03004500600c02c900c002260752040c002800000000381ea0358081c440c00c1101e1054550880c00c2003100c2060018481440081e000b01c3c0601610303100501102c80780381c1d90f0441030382990350903a0003185900e42e8070601d4052081c1070006050842007070b940041a41080d9000804070b510041c140002850b0100116420030500e0704901c400360740080da0b003038556400006240c0c4a82c01440f8141c0418049641c1030720a02d400d00030707245940d007036149803420440200b80403142e03640800b001c215003010018011000500c244640800361903030142a801541c1031140c008122808000d510b414007190408220000d0242845d800c442c180603074004020a41c104041780c60104510350095041d424520418 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 30864151 1250 30862901 30862933
    0xa08070506070c020109050d032c0a060f02060703050c070506071d03060103230717030d29040b18040807030e0a0305030403110f0607050105150109050d0204050702010905 75
    0x8450084068640300d488242c0b0940328603d00100080c00300b403030000b082040b4a084520071018034001c4c00c1c900c4000b03640c5c030540180e504031150b030356080e000600100d400906005030564050213240c20060000031103540d029589041c001e19607130800d62205c001070680c0c4407100c00e44003140e510008070390301070a100401500c58020030019001c1c000e602c014115a0307140008075281201d41161f20481c5814ac007000401c1c5984280104200728400d19500085050461110074116500c11025540340d01b5548400019100310020b103030700181254242c810f01d00308180544145110032503000074804a5070001c20368801400b40c119201c0e001c080100024400340c0e100814000f48240d8a16408410080801243d003504d8040503003145d100740030600010740e45c54218802444001c2800000300703641400500a940406030407600e41c0d44035800c1c0304a100f144060704c0701c01542400e02056035401c0c000803500c60f5614460291045481c0c07000320704460300071f510a503206074201050302d41d83c0002200034 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 30865401 1250 30864151 30864157
    0xf03020604060f0c12090503161101080703020c1902040b03100203011814070315030f050f07050102010e1207020414130302060604050c12040c0f060906120e0303010e0c040302030a08 80
    0x151449400d0100c032180c908004d106103868001d8a44842a041c0b85002c2540010000c00c0c108480601c410400389101c2503440c0e45030080706106558204003120400001081c640e006440f20051500511140c0c502c01750116005004d91180c100440440c5402d00004029041440840b501401008070112190b10b4940085040e224603032540b051410300c0c402800300715030780d4054503640d14003180d020403c0c4034880d030088610141c0a18541c0c1d1813544944803402c600d0381e00842203a455020301a0000849810b10030714005080900081040a03103110285844100e000c420201c00f01c8002500740455440d07500c901c80640703100030bc00040b4600766056900c2050444410350240c41500d001611502d864065144501819000b007402c000007003030352151000300944221a2840c0e40440411680309014040c0000c01c902e6480c050400d1400c800a01b141c0c6948425410040c1011580e504140d0004200da044900036000406075031343e08041c80280c0d0181e50402507042c092003900750140282c41010b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 30866651 1250 30865401 30865403
    0x11150a1101150302030304030312090501020a1d01140f0d06090c0302130b0310051c120203030109060f0f0b280e0414091507051606050412050c060f070504030f03020604 74
    0xc01a0780780b892040184000244002035040d401000b051000910a07032000182c00091240821001c0c0c040d51660300f641c01410344180020214901903940e019078044034110501d01382843d04002c0c1ca801020400c503c03035144c503072410101c00244404c1404003548510010880c08800f01302452000c0301c0200071798444801c0d4040c1240c40d003000700c5c003543c141080384d0007550f81d5103041d1802440c040c2401485001d10100700e24107039642ca81300000c0b601420800012031503a0b8055656503052035058422036440740c105070b0950b0006842030241c001e1104100d000e881280c3c1c407050711501038601c613100c0c0001c401e400ba0311005421003d03480c40f5030012880e611600013210300348041480340d80d6405081d20115007806059010450300c0710400c444102503508a189490020300d814841c040c00c07030364008196401c640c200c0e80da404110a101040080070300e020001d181c11841c0410680603103980e494040d1805900000d504c0c0070564041c02030007100d004503400070b034440702d0004a0502a440c2d450840e0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 30867901 1250 30866651 30866653
    0x9030f0d0906050a21020705060711060a0207050c040b210d020106050f1f02030d02070f050c0411041401051608030a0c0207060f0302180a0806010303020d03090308010311150a11 78
    0xb14040b40504151016143d2a54560808040307507000d106078180c03040040103600303608000b001c01051007440024800c500c50344a84814240204078980b4042d0001c011455a40c03042c010440050030104142c1024242217070042407151b0902c0c00503610600d9003428000c11b1038446d01c1800b8100b004213070a030203001c140e0000c10240d80d440d01441913440790440c40d603a0024010705411600003405d0145502605680f0490b414414000c0035441241c0c0301700310a5500105560301d013010414104110503030b07120107990601170407a85a5013024640164010349502c1c010414010f000340e403049040d6000442400c03032000100c4c443c1c0c1004605580165580c5142c07901b003c0d62910081d00000c0e0102c101c4110356510400c46c01d241004034020342101e8122040e00c905a140940d5a596000b050006000c81e00040e00d81940b442c42c01908c3c01234200342040c04d0505020302e00001c039400c1740031641102c2d00303c1081d040c100007480000320841401400c102031400b011070712070411540050b401040d600000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 30869151 1250 30867901 30867917
    0x40617190201140a03060e01080a060f110306090c070501140601110c13020f13090c0f0e1c0503070203011401050a050303040f1e03050601080a02090a0203060d0b06010509030f0d 78
    0x982203203404450424068082482895240800040980101610003030f519000580d035807a03001c100301c000000c0c0c1c442c00c1a903010405130000d100e035910070540680740d1058200103103854502d41003d14000100b41d41c0c0709180c80000211402c00c0c01d000c480b2151350000003042080e060707406074401c800003942c0d03103070024200c01000700064500003030071442248002d05030300060b40c1e014a4030010754080d0382d04210044c010301000d031040104140382e101616160b800441d03101c00009000f005807060448803070411900c0d841c41040f03074480031494560781d0820717030148200c0b20103810001e10307510401c040290503628242c40700d040300700e003aa0154140d4000319100342c0403903602c0040540e030740110301501d944800e100400300842010030000185041050010012281d501d455450a10200343d1242c207207074000d8a444c008500c3d1410049600036001041141181000004110b00303800d200802003e810225000c2103540e030240c010b80e0081c640c01011030759011110501c10340c980c002c002039400454a00 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 30870401 1250 30869151 30869173
    0x306021e03070c0206090a1d07020d091401080618090601080c03010e15060a0803040b040509010506070f0209040204020408070603020d110c1504150509010203071103030c09060f09040617 82
    0x80381140e0050310746a44581c07210100d82c00f045040e40c050041c03664042c0c055000058014904001b851010015003680c01ca14509000d02a08041060340d0000c00c01213110028017254150010840c4421801e02c1d00ea8011b60f1544041083e422141d89101c4d00900360f0360410036a401d00080807410b031000030080e50340c54141001450300f070780d4030140405c54a800c00b8096010107040c0e00e00950748004001c0c05207450564aa0030a8207540c0607400042c0e06d2040050b081c0a00e09080d81418014141a6082c40c80c240b02034503601b1240009090084c8983c0d105800301d002e55880f601994003801c200000e80300320a948001c080d00030351080307414001e0b0034208405010032028100584c1c4641041002030f0040e4030b0035666146548000400449641019070407140d031000d01441002e20501c00c003000103070f03681062400a40302040c403200041c11a401041084406502582610b0882c4400d40700503844000307240c81d040d00ca001e903010300d54019150010004505d110b0b480c01c60500940f00040d54001912 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 30871651 1250 30870401 30870457
    0x1170c0102160b0d110c072408070e010306031b080106050a080a030503070203120a0525090605210702010b1305060603130201030207061b111f02070309030b01030602 73
    0x10032900c00002c0d00920074208a0a0280f0000b06501d1a100c1000105070303106404444542d08600c41004180d03001e1030040c01110f410304c0040070b40c100c40a18005907104d9002005145100c000c200f00e08018140380c0515059009801c240091603000038444070f130407407411031841441c0c054483d049183d0b090820010701c0307003004039a0009a03407041300507111110581d101a6159403010b0421340440c40100704c03140f6101a8900f81700c0c00b80d040030101003010304002503400300c00120340b5400101c40003501c20100003a0303000200b03841151070b2403d040792504200d6101c80410345d0503400304c461050041c0b04001855038198046003844104694801401e142840c8207400c03140112901a0406000c1001c207844140c0342c0c41d4040700c0e80c070501d009032800300c0390358501c0e081d05d11102211024031030034003c904000d0341102c09510a040c0700030040a245040c4031001116907414011030005540c0010b0304001c0c035200700f01c2407000e0340e0050300d090002d5a40380f80540003980039840541035511000411410302c81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 30872901 1250 30871651 30871663
    0x702070902041a030c040b070803070e060a090e10080703050d1e0c02040209040e0118110d0b1902190c05010b0405010b03040605091c0309060608010b060403030c060204050901170c0102 81
    0x69140c20000f0050403c10100d40b640060324140c0e90000030303c0001442580b010040030b079584074041203034880c1030108000e403c2c17411002d0310074840c02041c000310001980c0402048222000c01ca1031000b40d0711424410b1107500c1498104d0302603809034040102c1030040002f1082001000c55503401d4100c490050514540c0d4441c64004001072850b40c0f840f40545425005054074102c000e20000302946086084c1d801c40da034086884805036401c000c020140000b0f085405038858064400701c11240c80d65a0380d103400d8000414000700032071550003030304186010340d05981c550550300758600c40e81d0a40c1ea602502000308400100d6440d824003144041c10304103809840e0403034565895080c2140c95560b500006001c009000018a104110260144c800f050301c48000d00400780c1c40002d0181440d00308001602c4240d0440e0280c0d80c1069904c140c0741c0c403a601181c0071a509803600003103c0803185000360107841540e00107a40031103000004200c0c140c2c0c800780340350215180320460300681350f11001039849034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 30874151 1250 30872901 30872909
    0x919030903080307020726011103100509090c0414090c010302040e0a0506010c1209140909030307080405070302090103082808060607050c04050a050615090f0105071407080105070207090204 83
    0x194188404000042d50b04010310b03042021401580e43c2d141d00d8482281140b02d0742203050703500c1c03800c680b4410100f8000b84103009906201428051552402c800c0c41400602c29209450091451400040340c13103c00b80540c4d800300360001e00c103102c0b2441c428014541c01c1000e9071108414001e01c040b40301030758002e10171607040701ea00200c1c450103070340c0e030a41000091000914103410702c60800c0c0f492000a81c0d03c00b460100030050346980c191039060072600b2012401c6140413500900c00c050600c100c07041c1c000700f5aa401480380c58041003590321480c14604081c8254002900600e00400220402c00d41c00e01030042e040140312150400c000c0403100030412241c0841050120300220049145820700200070f1a40b10302840480f004242c80002090172034000b102c1d1003402c50358510610419162032810b20100f0000705c6100c038202000200010140c0981c0881d007418400b0005040c0c04001081401d40070781c500507019aa102c0b9511071105c2d001e000c00f21000f00050050000c081640d840610a80e003c1c0c0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 30875401 1250 30874151 30874157
    0x60c031b010e0a0201080402130504120207050117010308070c0308070606090b01020105060a031103070308030109050a0e030a02070e04060605040e010c080106020a0b06060c0f07080c0a050906090a0b01140a0503091903 95
    0x400f0380e0019145100c0c064400da07001803103086040c5407100c0302c0c010107008500c5081010003543d48008002d0810910350040c50400c020b2700c540c1207002c201401c05506503600300008960350400340ca07200045c1041580010200380002c180d440c1400215400030741140d91580d4140551841080120300722403040307d1490f40030391104410b00200c3c0c00315012240415024048411203926601c5540c0c450300300f64410011152510100614200c050050700d0308c1c4e002c0c5078021410070110f0540a9200e0b8910300848229000f8a00040c003031148580000d4000d00c1c0c007070800c000080c042c110142c080c16403039031400003054040d400000c00038400542000d07000d412500618540c0c44036020040782c0ea114401c010341c9403007001c0c0e090003000b00c1808842c0050482c54011312081e074482050180b80c004551145114246550400c04951141c0f48a503038000c1ca2110005495140c8400581e00c90000b2a2507810040c1c02003006944e441d00540210b025507600300c02c5990b0b100403411402501501d2820007000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 30876651 1250 30875401 30875413
    0x100306030803160224041101090303050f032703030402120c01020c0409060605030d200102091e0112050a060302040605060a021e0a080d0203160306050a12050705060c031b010e 77
    0x114030364804030409203101030b00c1a00c2d141c180700b40d02403400c0b0f40300c0d818000700317003000e10103002c100b01c03004012403905d000c00c0c00c1a00741d65295890140c003d0141079949041040000001802d8031549240030144206010200032401061000c80e550ba8001f01e408900400526100079801400010450344800d0140d00411050400761f042c08060004844100c0d401912020081039642e028000406507201660b1041c0480401d5103491000030384000400c0d03079991041010b0700544c0c90305c1209009052458202d0304618010000407108000f8010b49084094605410f10161044540050088034000c50703040c4841511071040140500c40c000000c1c6c0503a000350038440b02803408801807085100d0120660310041c0081c1c0300d001840c4e11104c491014a41d00008100f49031003400c040d02c1021409207401c10103141481e0110325440c840c1c2c05010034010075061580304204080144401809000e0502e544440c01750003a03554a81008040225030100c0e9664427050030f40505c19180e06941c410010b00d4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 30877901 1250 30876651 30876661
    0x10515091b0910020102090907030c020d080601120f1e0513140304030606090f061401020a0212010f020c010204050123090402030c0903060411040501120206070b07030b0d060b100306030803 83
    0x1404149000341e0781c0c100020700c100c500c10381e2a18000e143d80c0f030041d0000340c1c0c3c03220800c00308030420740000d1441041c1403420a001c08440e070f000030510054070543c105000b164035840010303202c030210b1840414a46081c920030300795008071500000102082d410700d40b0501800940c43c42e0a84808a40007412608808088004690010440c0c1398500540042e03902c0c1603160307216501540e929400c07076100030352605528443c035903c5210300d20061010016541c11402c0c0240000d4075055641c00180c82510114208241ea01084d03015442d4200e582208650700d000c40c4440714080d400921405021420700e01070503410320940b12002c400002600790881c80d06601600b00320080d0000380503200503510074049407016460801007076000e18011100040d000c2c071000100001d48105800404143e1400f0720043d00684588060741e4071554084919403041e543c40d0340807802003041030f80d84c0fa40043c6e840c2c90f4509001003544103183c1d28109413030341c094aa00300101034007600c1c0384e03110050240383c042000074 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 30879151 1250 30877901 30877921
    0x8010c0e09060a080a08041805090c01030e0c04091112030a05030703020c16030b04050c1c03030902030c0a060c17040b040306050403030b15040e010e0601020a0308041403040303090801051509 84
    0x90b61040d0014007106100c0d0f00c841440307162041241080300c00d0000040c0500801c480d0700190071880410600074080c0d45801082c1945070580f28030b1107418141c032000b420740700c00b0051048512282020704104443e090a0610f840210000b00c05580588124114400b00900100440d200000c140d140d4500d180c40c1d440d4114000e41c412500c90005002c0c0051201e40c0303070340c0e44c4100b0004501030a0a001642014148103003050b00202000d8464403006600440f821164518148102e405080020700c040c4640082400c20130075000040c0c3c003c4403403501158407a007101e0310a0a403805502211011200d01d1000c441502c16409800a1288140070400c00034101d508801da02910030f15000c00c80700c3c20607000c103180d03240d0400380d0320724220003040034000000c0c4a2205401460140044200d070304205001075101c6195400c082d080100000000e030030b100342d029040c0c0700a5132400403a9550360f0340c1e040040124001e0b002d14482e5500740004076001d0708a0780804000300070b00401034080390722254884 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 30880401 1250 30879151 30879169
    0x706061a090411040f05060304060906020a09080d03060311011206050303040312180806010302090a0e0d02030405011d090c03040302070305060906060103050f090d0e01090f0b070c0f12080a0c06050a0608060108010c0e 95
    0x451311580c848044bc80020f1a500240100e04999110648846d041c48000b030f0030481c807030006004161500302c1c10804610840210f020b00c810a08000642c19004080318018003d2a00280d4040c800040c0000c20005507641c3c0c10a03010703895541c0e5406402c14001c0c0b03a052034040c491504281d20403001403025103400d0b040325401030307603406002409018140c01303a424203801c0148440540c101150801c05542c0200b03d004100c0001d80716a01100c4540002034221030020b0b05c824107660001c40040d04140c001c1145002540e0081c044030654500328500319907403241250300a00003400c100114a4446041c21036902400151010301202440580211118006890300504010215000081c07204415140001800b030b2900519500c1204c1c1c01c2400308803c16030300080500b003120a04000d48115400e02e40c0c04954070240e080d40d22000000f040740d51090010b40600600d240805001508004e075000a0803140900c050b10440d030307a80d0300e90b00d00b03c481c503100308000710f0480c2c0a1074403145007104c08 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 30881651 1250 30880401 30880403
    0x50c01090f08101a040c0906121104090b0d0203031201290306042c030d0b06090a140d02060309010207050601150e01030b03030c0a08031503210706061a090411040f05060304 76
    0x40e41910806000005c09441c01c0981a1300402e40c400002e002c0301d68420a03000c02600480c1341404504500d011101061085105840289036590284c41c5035035240d110042c4807980042c122501c62410000d6515004020f10510342c003c102800c100000c054208039900040404034040740c11591001c080c00f010744038070b1002c0c180e00a540c2142c2d240e40d44420a01d080b1f0b60040e0401940c279429508008001c03500744411941c4564000c1c0440710003580c0e1400500103483c0d400104000c032107100008100d6081141c0c400a43c006d03004010800b00e42c60550190552900030300c2154101d980c0c646030350700201c003041446c00c00242d0244045c900c0754002d4011235080000034040700d282030020f0040ca030038085405411540688004140002d841d10b10040d6440b07014101e02400700c003010b6a09242c041200703e61a1070b05180c0100e404801e200881e84150010246010500d090301c400c500d0300d1040e6030244c80301512540c41c1034461164807000a00365003c0d28107401c043c0e0100d41c2000c041042c140c1000308 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 30882901 1250 30881651 30881681
    0x5010e011803081b010f052502030c10020c1506130c0c060c020d140405090f06030a02100201050a0c050309060406050405120a08010e0f0702120c0708010207050c01090f0810 76
    0xa00c014000c003080089841d019502400c540131003030940e42c01035800c0246600341000e110206581a01440c0e54880d0280c041c040b070702544205034114001c095518586008101098980c808250010928207940e401078610f01321515903004007201c400c0d1032150704070748003104a0843c134035594008044200b650030482801c400a903501801c1d10010042200142c000700e00a94a0710340040e407000001c04464449410a4105000701e080080000c10b0300c034014105901066254a051141801d407a03000742506c0803c4031401d4000e40030380800c0c0d820b03c11440c5040545004d0030b20542c241e034000d14610010b0941c0e0b849076203500d00a410040d000341ca95002c1c001010848c1002a8014500c000064403075039495803500170070b00c00481c001401d14007070614031400c0015030b640c081580e01901c150884c1c840d85809048004911304100c5409c045819840007858000b0301c0000101d030108034009903212105240c50340a004010f44441c400c5101d40d9100c6058450000100d8100350000b102101c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 30884151 1250 30882901 30882947
    0x103021804020301230a0b0d05060d0b040303060e0c0708041203090e0f10050411030a0c0908010e0106050a0503010b031002030705090d1101030b030601060c030509060f120a0e01050105010e01 84
    0x600003822603000385e05c03036400004001070104003101e162030a0a8014400c80c0c4c90300c421403800443c0000d620420303917500c01251b910382c0000c440782c0d240144240155009140a465403815281c05401080e203070090b0740301000b522000070040c078100700c11100502e90102c059410b103443c0000c401140c408491048080c44960140441c040070340c800b00510408802a54071650308003400146404001c640110b4002c2d803d0042c4802e0902c0002e0403260084950480002c540b0215042201d03803c9641d0000202035090126021450405400c5281a03c108442a80c001c0d5510802c00d402c988000030855010f4000c016041c0c9856203a90186500150300c1c10600d01c0e00e15072100040d2b2407000010201c82c03902500280c4015945c2c944198403280205400807c0d95506208010b05001c3c4511030060400c40700081e030014071f880f01c1042e520021401c600d43c9032207021010070024542070840e03802225500d02001c0d403454520500940d412a02d040e100d04080c00007002c0111040305ea83c1c3e40f01d0311401205 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 30885401 1250 30884151 30884197
    0xb070308100e0c130b07020d08070303110309010b03010b061e030a0209030a06020a03051b031501170103060501030308090a0809010806180702030d06080102040b030c091305070903020a06021506010302 88
    0x144502da0310030665a20750070303035881d0107201100304040d0607004004450820311034000140c0b1031032aa821b1003600f100c01d458499503145003c4000c0d11900060000503c070100500061480540128a4500045009000010410b03040c816140140c18004121b4101d000105034907082150045401c807600341c9c070152038448540c0200b85401801e01048a0640d400900031901e154140f09803600f018144019400707220b41c0c4140141e1501014044260301702c0007000380311440c0e01039201003655a43c294000307680c035a980d0811030006c1c4001d00c4250301045042c000903642e290003050303440b03215610000c660300344401900111002c1c0b40c0100500d402607001001d24210f00c101c1c42e0310510650559006640d101942200c0f46d0580b02c49600540e82e503801480148000800034055aa10020300d240f07403504d0b941420001200f4400210b9421074141c40d04003480f85181e442500e58003501e009031484180c03036076554000c9948144662400321000c0b403400c0460400d41c80b0b80c00604900c03c0072542c080510443d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 30886651 1250 30885401 30885419
    0x20702010c051903090501020a050a060c0306051801330804020f040e060702010b06070b0105040c0504151d0a121103120a0e0a2711040308031e010503070b07030810 72
    0x1912907043d00b41c0000202080800d0703400781c20380c400340c04284041c219006150f5907075551262a8500101210b0311003040480942c800d5024000414005003902203c00b030082501c00010310a0180503000070a1030100301070845000341d9040c80c11110300c0b400c4e21181810030102d8444c00042c008a9000104501800848c0c1e03a60045150300b40203000a020b090520f050060308640342c804c3c080d4081c004c2882028007080d0401e0b000340c1103034019100420315550301c0c0c100b22824450742d003061051041c101091900950f20140242d0040d240031000003241e2076050070406814081e2140c5803010340c0301d17800f290005170542c1c0b5081142d0f00150440707124440a444c00c1002d900007500f071500052070103d01c00b10510b400241710000701000400e0b1001041085034100001e0440244800710585440c00070000e408074500321801140c02c0301500ea164100404450012031850b01950724030308110f4008160ba00d004109201103540001c00780b46094019642640c40000080900044011a02001a848130 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 30887901 1250 30886651 30886663
    0x60114070501050f07260a0e0304030803010801050609100504020d09080307030e151b070302150103060203071e08130609050601081e010c0e010318020406030308011403030708070204020702010c05 86
    0x1c45040042214644850b003c0300001009050504102c021103d04203518120001c0614075444100c0840d056070359029480081c00903141340510702d100000c1c1c0041403010250245050340c05550003070007203860300d0081040404064400352404030f0021400c00407850715900410b56030300241c1000c03c200d6406d0300c0c2c00005410460780f000100f030720340e04803103c101804d0040306010f41c11000180424105410303004415101e02a80d0905000300040d1b02d001d050081020580001218a008a0703d607140e2030700c1000f94001b942d5602c0030070420014640303203001111011102800950b151050303541c07055004450341c1d40d0300c5c40641d0090303520220038011032030512515005c1c2a1040080c0241c0114040070760520150100401090345042e03c0a6603140c0d00000e485115002441c011540e140d086800030400000520009c0d4803a26004001003055041b140d2203040b940642a02500320b5024000e0607180e21920000401c014802c00c40907005140c550301403c5858018945240d40b60030903900d070fa01d410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 30889151 1250 30887901 30887903
    0x3100501030606090c0c050309240304060204090c0c0506040215090402030901050f0c04061b03200606010e0406030b04080c0f0a0308160906050703081b16140102090109090506011407 80
    0xc0c0c031a03c0c1800303115400c1c0650941414140781c1071450360415141c0a0300e07030065400c0c2d20704c282440130030380109011841141c2d05548141c5141a075900342458120000d6000b4400c41c81e55605000310300007140c0c0114010441203070020082c208a80d16542008401201000d11451341c5a0511003a20148c58501c06144500400c2000007000d050620050741a5007008014038000c0500304030500c20b4941c00043d01c104030452840701048180e0501e41914004854104005503d40d003200344e052900001440b1400b0790b44c282c844060102c804014003060b00c10902000c1d040d910000d0129001234140c000512480c20031400303964540c0b800b0050242805000041980094040030034801c50030015043c1c1c069000390340c10b15404451a1100103056401079034000340a000030040011006100c4201d1500e1440c0d9058400d9615076060400520300c5c4840c6a00359100302c00780c000446520414803c1387e40301501611225080c0e480d00d48040080c103c010900c904100c40071501208030300d44c003c0a400a5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 30890401 1250 30889151 30889163
    0x8061f0b0408030304020a090e03070b22050d080109020301080309010c0510050702031806030609010312030b150c061e010314011806060801050a060e0c0702010e1023070804060c020310050103 84
    0x41c1c1411b00400044902c680c002da003440e4500041158041000002c076100a07500c144840b01c2a80c0310001c200701c0b0b600c1140c080c4d43c250504e19141040000110b12031030b103070b901d54071039034201d980b12250482240400d000d007003d503074020082c50b0030701d42c010390510003000d00c1a001c403032884401000030800d9850584400d000b40e4004501d08600040c1d0076002c149508040e14400c7c25864032600050a0745411321000e00b64507460f2002001062203604148030042c409890100c1d01044c0c20001039440d0b201208100340c1b80204404540c404010029014483c141020209181c3c0d00f1a00e418412603400b4100e800d2a668903801e80c24220040c041c04050315015540025440385000312141c2510030050428405c10b140c00024005801c000c00180d070000d03000148151603408510050351081241200035501c0700341e07643c0700203600c0e9000b28130580f014040900bc42c61880040c40c060064014400e0050441c44240818048284070350410008903000400b21b0300300004668840d401c41e50300382c20036284 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 30891651 1250 30890401 30890407
    0x9061201060f0311030103060203061801080309031005150111030d0c0306050f01050a17060d0503040e0a180f021e040504060e0c0102030406050405132705120408061f0b040803 77
    0x5401c0105030401400a00301031141307506200c2e01c3c032101d1005000c014055940030000c10280c0c1c40e82074000412139440f1340ba00c4029611601c1e40c036502c0c0c03c80d010261091080f085080418441401402e001e52800914686a24035040054901c001c031002d185c0308130301c030038400b40c040c40e482801200785280e0562400101c0c0c0d0700381000d10102c02c1d0b42d404420305000d001c0001021081d402a1050340d108640480b0360b845480d460001010030310900e601a10b11700c00403c001c125040351010140c003d0415040c1041041391948250b1103a203908074002e802d010901c620b51016040007186856100e0f42840b07122621800100068100d41081e11705403121a0788400d11401960108180708641d0303002d0005505061809400a0181c80f03103014240c00342d50b03100c030000d000309001e401103100801198401d0444072071201d03a00303113446107190b0b09580a10401c184559200944c0080301e0549544030064096641d4080880c20801d00c98000401c40b01a100b00004030030f011000074002528101000d155 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 30892901 1250 30891651 30891659
    0x402091e0102120304030203031302040b0303120a05010909051b040b0a08030307020706080613020c100c210203060d06020c0a02030304060903050c040c0e010f05090d12030f0c020316050309061201 86
    0x4a060341c801d03d03001c43e10400b0028040460740020a0700c0c1e020790f5085a000f0f10960380d00c0420080d101140b541c5030503110200384607921003051340660b417180021010402240ea46c0703c9111040d81d01004000d09960403456465083d100b02d19461100511b0240012651021034000304000101c0d41d800344202d0f0b0000301c144020b56506203c03000080c4140d207011465410100002111541c059020820071035000a00c3c00d80c0b01010300021000c515151010000d8000034440548400d0034012155030404510468506070a100d100b5603000d04400b81018810a900e50b81c0c140003544030040c4104c0501c03a00c100040140c2d410030007070002d4140c070380d03544800901d149801441c00d4226250b40384551708140c3d900c008551301807159413102d107091034044a545d600100c10780c1c0b68442c1046080e0008005001401400060060b8000072120369a04015091140400004440781c0600b42c4c03005070800c002c4c80400300000010782c984e042c042c1c02501d14140700000026426404001108500c1c503c00740100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 30894151 1250 30892901 30892903
    0xf170415090305060c0c0721020102070b120f130f050c1905030c190b03160e2d01050408060906040b060306091f060504090620091507020402091e0102 66
    0x5880380403810441c003140d040d5a2415103a00c002800a05a170a01140d8058103000401032440240b40c00c8076500b0307440401c14083d520a48107418143d0142c85007110000ba0202d540c812984c0200405d4010b5000c6e4407407681d0000415000307084203e00304d550444c1000070656910000d00c0052092000b050800301c0e02c02401030020b4000f8001e944100703a108204041e441c00b042000b0010b9049401d0b060701c280301c83e04001c40303040c1900710a40341c1c0030100800180700390305109880144220b80f030391003c00c00d288e01003120019900c580c1e007240301080c280c060460000c40c4c458962407401410054101900c8609952401e0b0f8100c4043c14140d02420a0100f4080c2d031500b480e801c2041500902000d1904840c010340d01c11040c3d0780002024486210707450398002c0f5078040030103084010030a021803c00383c24080c003d49001203d030100740b25044010b00000c440c3d18100c1c2d54804d8054102c41e40040c1d0481c2621960704400b2059030869020800c1c100c0c01c1c0d5560b102c2e810860840306001062110f500002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 30895401 1250 30894151 30894179
    0x50610091a0102060a020309030403140601030501110a0509120102040b070606030c05010305011203111f090b0a0204050a0308030604090804081e0a08180111060114030c040204050a050d0f1704 84
    0x210386032078205941c80d4203599022840c4ca130300481a04c4096900e45039050301500d584195440a0002400007401034400c0e40082a018102e0340558000e0100e2010f03c0009600c602c038203080b280120790200010440d074123142c0071b0f154002c1040e8000608003a59011014101d030f1000c0c00841d21250f460606204002025004001400f030a207403c02443d8106001000c804e0010b0780041c00340014089080c154180400050030920301d224030841e400b4010f1b42c00c40c0082c240c0c803941201d5107508100081c520120f94800c1c2d60845000424400c4c0c85461501c58546582c40540065003094560f610306011800000083c00103050300b50040c410607090403281490a80c4048116000341c02000200c004284040d080d00c01000345085000040b82e0418016201d00000441c0080c5031300480000081d480703500008242404000c0c1d003a9400c3e00001c0c0e080004034451402040c0d40320300310b80d01c244002d00b040c41c0c400c44107605c20810304074481c2807030f102c2d4071074044190041051610300240a020585541d102 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 30896651 1250 30895401 30895421
    0x10b0a0b04060206010605280c02010815010806010c1505010f030308070c0f06020f0d110408010606053405010908041404022115060c060105010e03070810020304020d05061009 77
    0x56905007410080025111301c8188108803c021010806070310103601c01c00e24449020031605c0b00c031304103401008060a002040c0c5011b80c08694510300182660001c0d540441141d14140d5a0040ca43c0e074920040d100080000010f540044d8240c640690154241c410180640001c0c050941c0183c51481c00910454000380403c0400c41c00e071001d07900081e0340c0d9800ca6110390b070200300580c5441070510364100602800c0d81d071105003410a54210540c070b500c10018400d03140c04000a1203490344601040d260340c81034494541031120007813042e5001e0b555000b5003941d0008561044074550030740351902c50a40b0340c1201e0a64007407100280401c00311010a000c60203011058405606244401e590580c004150300701c00c450340281803001511403d15009000c500302e40c01815991503070f03440a580d6079109024028140481c0c2c0c80145161240b40004580044a100900600001c00305402036400ba400150080380c20203d80940d0600044040c0111445119900a200007003450403621106441003048 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 30897901 1250 30896651 30896669
    0x1101090b040f051608030301120807021801050312040509060607050a0206030f19050c0a0c020102030412061a060c030304060e100e0102030709060f020703030e0a03061407020d0e0a120201090b0c010b0a 88
    0x20800540b85c000c0305890444400800c64003100302c090504c01264442c0d00c800079446800031041310f107504071010019060381c0d81070f41203481c41c6619100c000c80600c624021943e2001c8040000340051600100030000703030b0712960070b40305030b009a0750124525410039a9a030500c51020020030103c48910f401282c07500d00717840424442c0307052003000700070584a0581e4030010450120191025a4020070848000340040c0104c12601d4120341421001800c0c031404202c1c029030b82c41000c2100d441c09501703035040000c0a030055880c1d40c5603982e0701401004002d110107028000c441d80c15404814502ca8600c1e00e241d860009666071603c001c004001c10b9683d002030060046154000152079400a0b441c01034940c542005c0103160201e40028050340803075800208078a0405084c1c001c1e250400f90f005021b0070481d001c480e04003e41d02c1080e00d0810307128140942016012908100b1070f6a0382010002150040c14003854051b01c601d01d02900382d014494401d041e030f446003928515824400300c00001401c1d112 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 30899151 1250 30897901 30897943
    0x60f020c101e021606030915050601201207030903060b0a0f0b090109080109050307050d090e07030f09020a0321030509060a020a09080a0303060603050f0906071101090b040f05 77
    0x408042d0148008640b25000a610119902900c40c0208604031108041140000c2e225903180c500a007d046110301c2160846440310703203031a88035558000d4601641d01611924100c0c0e800d60b6540c2c00c001c500072458071840c401c000c91820045115002044818003982d038902c146400e50500d030094400e244800740c0200c1c42c8a4040204440c11281d040a40c0d1072680c10b26901c040040040b07807040d2407034100c0701443d4030304000d60003044000001442c83d18841c034156403000c4040402554065002d02c1a1450070301010000703004103201e0340c441c001002c05440002204035898010a03080e22160704111082060a0340c01c4034a4054009511a0008285018001c0c0c0c581202e440380c456002900c56500690041035001446005401c25000352070880100d81c0410118103009024000d03510401000c0380ca8800031071042c40340702c40c1d00c030b129041d040020002c41d1210841281d001d003001c00320814075582c443d03a82d000616090b40403809240220400301d0306074418100242040b41c2c04d09034a10182000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 30900401 1250 30899151 30899179
    0x40c08040b0403051303170a0e12150c1210080f16050907020a020d0c090b04090f021003110d060503010b010c050a0b0a02130806040303060503010605130513020a060f020c 75
    0x1e04940c0c8698180b411580b100540c9040304101055508001c201031030110707115202c0051030015001c80d005a950b80d0721081c40e10740500007403840700525600c40d500300741c00070008442c0c06254941c100c822002418038114000040c1c88480c1030a95800c20082116502000b54902c1000500303d50001480039204820381d06e2880001e245403445101e0103140c16400092495000340001c071500758020b0030b6069001403034581004a07210324007a280c90b142c50201e004a03e81864810b44452035803050a6200a000c1c07170f02045520f00c9a4603c2c0c3c2c00300b61312107825502900030000509601196220046000e50900c1c041500359802d042d40c1c0d03070412288051174000f041c00020b20740030b29604405007008940341d02d0440b401900c1417550002054410a1000038a0400041c20920a074000e070b40800c102500c410802d4240c81c03c1d8814a540581100100e1443c001030307504c1079030448021711011a2031409035000c980814002e501ca140480c56174a014101990140a03d8075442421031700b04d4020305ca1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 30901651 1250 30900401 30900413
    0x10501060e0904050c060a050304030f02070308040902090f0406060c06200f0a021002040e0103030e04200a03020408010509010212090613080a020a05011b032004050d0206041206050402040c0804 85
    0x74803810700d0301c15641c100204007880010300086440513005029035603108003a590113007071f44c0d2082d07600301c0000d207251081e0a030307032031010401100b070300ea11800c41c914080c5021000806504501049680419011001c0901d40c1d51032040d200249a2501c40741e0f40c0f003480e070900c0002c807400c000901d115811202629452101c10748100d030040c056601d00140ca80130038a400300e180c004000c01c034103c1144001004120700c490880000c2c12a480b80d61290800c01c182000e000031b41b11903141e101c050140b881d0030300c410307441403602910700c00140d8074006041c2652225440d0031340b682900c00c401141d500140b201482d800c40480302da0312400810007041a401c3c0071645928802d034218024105400c040707100ca0000340b080c030440300201d411100910114000468030071a10701d6041181d0042450402c00741c1c1c1300c0710101042000410200841c0741490b01c0c5c82c00340703c00b244c03d07030320120790215081101203994194110307091000c85c00b94100090321f15192041c8000c07110082e00650521101004000016203 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 30902901 1250 30901651 30901667
    0x1f060b0304150c120f06090c020102070302060403140c012c07030503072607051c0306060206041104061a0301050102070501080103020f010c150c0806030c09060303030a020a0905060c030903070801050106 89
    0xb110b0300c0c0014035881c0070403040300c0310110105401100340c1044460400d08001e50411410ba0304024420000d02119007401e0b4200e1040c42c50040c0503030001400540480c1c000c001d440041c0c42100400c0b0319011103c180c2c1c5003150040c030780f80c1034210300160291418820042080c2480c065071001400042e0440d00e80a0343c070b005540c80100380c2103401c50b1242d89c424281d0280c10b03403482041001500c2c0c5000c0c2c0b034050b460740c3c2c82c24103803944070310120548100d40e44280509001c480d0341c5e4020304110b8480da00c81b0455044002c14543d000f986580c030024001c00f6040e00a02d410103d035900c0740d00c0754185000242401d50320b50000341000b500c0f40c018409652003850300350b0400360908083c80d000f4003525154140d03200c980d4440104928044581c0303603540d0080c0c2e0301441420104e05407030801c2c080104210080d2801e030364a5030194418400103282960340e83c0244107112a80c01e100001541e10400243c03254401e00c07108440b80c00c00300e009074050508100b05409004114003c0c40690b06050780106916 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 30904151 1250 30902901 30902933
    0x1b0302060d20071410060f0302010e0f06130314060c03010b0a0212030a0603031116030b0405010b040c050a03050f0601020c1005090a0306050f01120f0210020f1f060b0304 75
    0x950702c1d50280d20401200c2689102541c140c1c0d6602d031651554200540e03107070710905070340d6003502411108954800862141405030b4148046940e000342c00c44d001110110750441d07409400189141e103180c6244d40301c10143c40741d80700d15488580348a0440ca861268640d0100450000b5408003081c021401141c4064074152500343ca4030f2502c40300d00c15012440d180e82946406540c0b000002801902c04080d0800d4003964001e458070403205c0500300300c460703a420529005031003031610100c3c240006245001e08030b401ca0700a00001c58007003800130001e81182e5445c00310074007042000036400d26aa030103000d000e6001c003400740c01d181c1c0d62806d02d0000c0c0d1699014801148620045420043c0c06c038001d405546a50001500f4800b01c942c1740d10f0a4001080d0964103814044584000040e801c10340310030140e003c6a02020401e002025a801c1c4040b6500144c8a61305500486003020314200c01000000d4241400418035080340d00040d4205040340c1c0a5008080103510400800c40441c143d000142401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 30905401 1250 30904151 30904177
    0x30303051302040c0503100b070803060d0309080708030a0e0108060f0f0406030503030f100f060e04050406090203061e0604060608060d0519060903080c0301061e0504050411071b030206 81
    0x15607a90550781c1d1103403480c110020340c4245446130900324640d016010314460340502803070f10621a1030b912040c110307000394440100799035000c10010b005418001442802148641001c070101e58460b4541810f184480d00050003070f07400400d0302040340d64808002040f0b80001e00308584c0604065000c9840c0b00c045400607070085407045001c40980c0c990364008002141c114094a40747e041c407280101003e513060b9050f8282c1800f15502103202420488094100d075502d07201d50f15424020760620010782002481a2130b500d903680b043d6000358401f400036a200b044541c1c070b18401ca40d0a01405088540058075682c01107241600c1400003a41240e00305400c00c1c41121114080700083c9400d078502003c0c030071190040301d940308071102001044d80005022521a8640980a0340c407840c0780b5480b0f000c00d03c42c5500003040c001e00741c2a0740c0492400300c104080c06140030740c5056218000704066415a08606004030800a540e1043c00000c1900780c214085c115003082d000c0d45507400040da40c2c00750412110315 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 30906651 1250 30905401 30905411
    0xb18011805031902030f070611061b0406080c040302061c0609060f0314100903050309010c0503060603010b07050703120504180c0c0b10030f081206010305071e030204030b0a02091c030207030303 85
    0x103656041100290310306c03e94080340c2c02d1396105c910045c0030111040708800c0d544203007000306d07840d40180b6101d0000004001c08050405250200842d001140600304c99000b510030000071000d038840e40000c101d045480700140d5030304001c041c038031400c03035910354003d00266103050000d000b52100c0317030180d40c04c07030341c00c194041003524007402d920341030407001241d030743d40c40745454405410950042c015504ca440658003c10030704d088454140c9039840b0440e01560300010400061185007049005018424010011101d103e83c84c0c0d90340e011f038102c080035080e010910200d010041142c0022000d2051103101d5001d02c80060b0401c4042c007107003a0300c5401021b0100d104c0018800c1c20100b1035000c001d6400455030f245400140c04c000340140e0294a601a0101d100000150381d540039000d01d80c020070f004d07030f07502020301140e000c20078618101403c3c01c4105038003044000045024171070618040c0c1c4e00143d0059540101800708103002040400d109840da0304481d01c58003007a008500351003280d0b050b04010407 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 30907901 1250 30906651 30906653
    0x5010207140f0603091e01020301030f020907020307140106090b06040b03040b04020303070501021c0b030606101103040b040f05010905150f07060908030a05040210050403050a060e070b180118050319 87
    0x2d4548071200145030003140110412550b040002007918210b07210001c03941443e14204a603e082c0e100901003c0c0001e52449900c0c001400c0a40070140e02003402c0c07040c1c03070400403165144c06c54003008141c00501c580d101c020901411246205030100408100e52040c98175241402010132800300600c0900b03000d483d8400602513403400c1c42100d100c150b2105c02156101c00943d002e40341006400c500395101440c14025140c0e42c140000c9090140400801209002c03075942c00847c0c03841038104900320300780002d100000f00075114802500103810b03100302031203445042c00c000601d28a05580114400c5440104030803100c1007030411203110350101d44866035260300038182070003e040d10760002081ca250002c00c115458031554041c0e40650300c2111388148100c80f0280441d06801140000ba1054100c02204030000700183d1001c00150851420f640400365195490841500302880c2900062442050306420b507a000f028a0310383c490070700e0711070303105802c00d00030070f960740c4d007440090a01c00080c1c00311070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 30909151 1250 30907901 30907909
    0x60702030115030c030606050913020d1401090809100201050c041404060302150702040c020102090f130e0d020d11030301180213090608030703020f0105040503270402030a020a11070501020714 84
    0x2a03030b42c2e07001da0005920039624603280c45000d5651005454452510a0114840c5002c802d498040c1080c0c080340c41c505483c50b0200700342c00810712000c46440e103d2002100c0248000e0203810017040c0a400c1c0d1030b0315175200e00709002200d10185080800c5915000401100c800100c05940c242c40071520f10318001d4503885d022500408507600040e520490302e0320300c1070901ca200b10041071382910940c1d0038040140c0f1000d06900b41e0051350f682036030181e0310842c15051800c10780701d4003134031014245011400da0010b0356481c2c1098100c481000050b084101007241c5560400c00708900d0303602c000025841c2d58908512084d00c00b040c948003445c1c0303540005039036060700d58002c4580d014100b0414108004c42d84d5100aaa80e54002d400407400360051400315040c40340184a041c1c865078026003c0c6161101011039450034a0198410320790110b0812103150310303500c50348041d5204500740e881c01a034507103000c2c0016100c00f070420024611070744103500900491340d01213602c50450703442d404a5421005100006 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 30910401 1250 30909151 30909161
    0xc0d12050a050c01020d02090102010b0102061b0702030c060f3601081f2301030513080a021906020d0e03090a03080c03090d0c050406051804030e011103070b040308010503010e0c0607020301 83
    0x7110f50b03903001150f514140b0203039074020601007809030001c01400d620389006980b2039104860040091240030350030182244140020071805100506031a0402c08280000c1c00b80d800240c03403103401d0b910206071120046100302c0d0180c50015502602c0d1040c01c01100c14440034640188110704005018012030045490b5804d075603004003000845807036294407018404039810750a20111003400f03c00045281c3d079402071040764012007610318a08140c1c155a296114140d01000c00e200440c4140030b18114044055420708201511440b40540c0c2c40681c011742000b642c0c900540d442498204100b9091a0780d03403c61090102c0354002c00c0162100354641c030250840c015101c0d220780269500c5240d50800c641c00402c00155641107408015407900d8405102070340d00081d4a540760850417101040101c1d00540c841e40c4a13000515142c1c14250541c1e9107a03003940c1100c1c400b242d04010400c284400c164208125a0141000350001c00030710b00c454016940d1180d148400038015400051410b096403429049 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 30911651 1250 30910401 30910417
    0x307051b0a0f020a1a040311030f12040906050f010e0103091118040b0708091f060308041403100203090d0311040b03040b010810020a0c020f0a030c12050c0d12050a05 73
    0x94070841111414051410024000224401c10a000380030a8440c0581c565451101d40071a10368207007403d5641d00740300064040f001d641e15206240c0400070303c11041211007030750705481d80e109480301e18202400c015100e079904440c1c0700f81d4540c400301c00302c1c1c0d130f004c0d40c11500c60380240f070003254910031400c24540d10351f41e460303407c3e410141c000b00700c0c030b80c00105401d420300440c0304819aa0746580c503000210344202c0180c1c1d0035002030700300c680d078442c1513032010001c01c4c011481c6500000b40e182c0d60f070382c40702c207180c1c00f9500c000b00703c23907540960260514040c030018055050554080d0318500c1c1c0008400c0c1c075010701101a1080c10340e80c00b90303940703602410002c1c0e502034080502c1a640e00c0c100ba041c20300402909100c0c0c10a244210b5517003120103030580c02950305400440d210b4102c845210340c20801c40301c071040b202d16003140c4074000000204580129003c010710b1b482e04032199a040500b026420301000c958124042e60001d8a2400007803601304002c461000c0b94540319440d41c545c0c010440d644d01c03076541 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 30912901 1250 30911651 30911653
    0x9040f020301080a03020601080a0b1f05040203040c0806100501050906070807061103100b04030c380c100b030a08030402150310050112090302100e0109020901030b0f01050d080307051b 81
    0x4038001000041c140115800303602101c440789e030303a1440141d80c4d6101e084020b10200342035010860a170411a507030251419a410b81e00300c0581c0342c2000c10100e820803241500c03140001801040b80c100180305285d000b58008401c100c50fa404d00002038103a104103d54035004100024042080c000781d00280d680c5c0e95401103003484000803941c0d4142d0310790010344400316a403644141c0021a5640c0350215401c0b640e10640a1040510708a80c001206404103c2c5001212080c0c0c1c82c20102074040c4070001441720924089500c0c1d101d04107926107482070310b2483c4030103540b400030700040568001039503001203540000c0040e41c1e540c403440820001c035004d0b0703c80d11180340d02101b800b00f1085080750f0001662801c1e40c481203400002001030055900303084001d0050303081400d0542c0001c4550300b0041c1e516100300b0020800e81120390100304021000da00940f552008081031204105202d02100d0040ca8200c9581942c40c05549800752584000341c0307800241b0100098080044002e04080c5a06401c490 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 30914151 1250 30912901 30912907
    0x30203030d0515060403120c060e030310090506120705061e0c0d020c06030f070309020105041d010503010b030d2a02100809010518121e031303110c01050d0209040f02 73
    0x2621070005000c05031241c0402103840528141ca50420f001500c00b1070750020107580101c0450a410b60341c3c00317103094064a89584401407004090707410801903000fa83c0d40341c01407808500e0a91180100c0e100a0482d41c840d03003c62510051402000418030709882d8101d4515940700f400c07028000c145400e0040030408140c0204007a900440302041108817a440f80d02610030340c2110408000c100d200403070324034581d0380550f00483c000310720030303403100c1e50040c418107043e454981c0340c80c2060710714070240c14401d6058848030010320a03800d0038001c031000d00c0000e4004040c0c04024100c0a0116015024860082142411001d0103003030020000a101da4014120070f0914118280c001c00c9024103c03940380031582000041810002100c0e1441610f0000101510b40880d100c1c2d800c004d1a8094a103840c0b0301c3d07070384d80500f00c4510400802036000e89031507282c0d03902a03400c610f40034080042c401c0310b1502a4104d01003118050741c1040888401030240f080c010380d9140881d0010f4020102030003041803162001c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 30915401 1250 30914151 30914167
    0x4050411070501051021030210020c07031e08041502010b06040b0301031b240c0203160303120203040812090a2406080303010f06050327060601031416051303020303 72
    0x1400007008010b02940c020b10541c5e90310320310103840802d5440f0720444090544411121104402e04102000e4840c0c810303584464254040c0d0001d0303800414002000d034000d4031080003041310562765052000010700000d0001ca94584401829000c3c0d0701c01c465000c4800b00d001403219100791b000e50010320f4001d01542d201e588400568000c0e0300309001c00c0f0703047c01d0000340d0000c1c684074200b0081c04440401e4070902544a440091561309050880c0348018400f080d644000183d5090102c002c0d070000c10440310514915605000701424407500c190b11741c0074810030078400454107076012510780350000904001d26494400c025440c2c291700c000b002c1c1142d054030103406010004e01c4800c0800010155083c0b001c1c50f1038005068980c8003e1003980d4844034484410031505014001a561001c180055080e9000010403020420310b843c1010014541200c010416990b170540300703d040d295120300e401d042900d0602c0c0c503000002800704801003800310101c0c03d5410f007944032014038045d640c0039003901c1e214030035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 30916651 1250 30915401 30915431
    0xc0516080a06060512100e01151d0105090705030f04020105040b0309060105030c040e0303040204050408070203030a021c03020304030e12010e01110702040f05190f060b04170c0a080c010311040504 86
    0x1094045079003e04010700002d162411000250810a40c8409402035041030700c80000241002c46500b0703a65529600c0090106810002c820010101c40240140d0114580100205510141c100d03601c110303c0e0900380711780b90f6400010f690340610341d50000203981d103450006903005c5c010341e481072488035000002c001035402c001c41c03402c1c12184281c2c05c1318090300c01c000070401511500c44030301c4400c1d4405d100050161a1540040d41c01038061034101d49440d2554012a05591050344014050303807203c404140342c0c150942d0400e5242d0b003249001c6080d800c02e560000c0000c0c0b141c0d000c142c460002244004d940d04001c1d8003104424802c07a000300410b450802d500c6401d6040300c03005071721882c586005178240c041c80d4003d152091010764030b21440058040d01e03100081031541c0c812080280d0340c60000c40d00c0720300c8800800180518003401880224101c04203440d000110158902801d1022401c000c01a000140145003240074240400c0001c40d07821600781ca03014075400f0681c00f60400c0340c02c02c54100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 30917901 1250 30916651 30916663
    0x403020c01020d080912130f030b010e060105092110020a0c0308060603011d0c0f0403030302030402120109020901140f04090803010f06050a0806040b011106100510030e03030402010c051608 83
    0x203000c1e001d03107100081c100d07030503551114110f80076041904104240c903010501c0d40c004200d21030120000d8100b041d200c0241c000580d1058200716501e030500c1d4014800c00010100e08da520100c24a842840c040300d010200307081c510342c1400f0407905084c05251991416050159911000314420115100c04100d90018000f04102078142c0200d0741000110b800c40c10520200c078181c48003c4080b0301c940043d00c05040c0088001440014a808280003410184030400c1c01000194002d5502684a0a042c0100901d80d0340c001c00d203400d42c0e80750079040b00041e1950882036045861140e9a00d5120700e100c00071034925100c05000d15403080c40c040c10803040007941409035040e19111044402d03550780310f4005075070034864607030000d021803503001c0043d041b85000c1d0054810b40c0410b241c2540c0000400c60020f150082c140c40230490711201480900450400030310101c200a0903203800d109410418160f1a202e20014101a04210040c0074203014044200100144107889078203010049540d4482940c0b40d80d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 30919151 1250 30917901 30917923
    0x7120e04050c0405120312160210050408130503190201120207020a15030b010203250201050d021b0c01090b0403110a030506040602070201020d17060d031112070501050601080c0f0c0114040302 84
    0x8405d5051040542c000041950301e985046042c03d80f40f0740341c4c620003c2e400342d141c00ea1101188500226060f480d03410f4005d0b14082d501c1401c2054552070324030412100010103400c0980254480c400256544200364928840d00390203090054000a000081030047d1056080103500814040300028800180049040d1200283e580c00c0082c071104d000126100d00c04c3c0803c035007030f4514a143e44074210054070b4001c502c82c0c3c814181140ba0a4980f001401640c1000d030001d1141d400050040c40c0504c414040030022000910f00b2007285818200c4c0309006003d107000103440c8044000c81000c0f2a221000c401000d107400c030b8120342e154a07103440c102010f0f50081c00201c0c018040d41f81d080b0310207030040e100209111080207000300c80b50780d008140100c020076040300f5800c101c02c2c0d1802c40d14019051050082000d80004d0840d91986030341407140c00e568000d00720604200c814010081c01c9803980042d036200c0c022292205a40c4c01404080d1405002c229050802052065040c4001c054000405034105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 30920401 1250 30919151 30919159
    0x210b01020c0406030311060703020f0301060324090902010e04020c03180301061a040f0503070302180a0b09090c0a0f06081b041d180109020306060607020a0b0d05070909050c07120e04050c0405 84
    0x242e2364103e1b04400741d004400c0b810705144c00600040c8034640c0640c00100c4062200c13005410180340e000d0101e40003400070b9100c1801190fa4049140540d6848107580304041c100380e6095107014141c09041d41d407442000030603050394040c4103100c0141ea1b000e40195004000141c8505840c00e403003a1240116441780c4200c0301042d24684000403070741030100d08078040b250000c1841182c401e0015032004499001004401c146596100d441140d0b0348100400340174171105402410020050800d02480a00c6a0041c681c100b103210810420940e0103503404e90301503107010100d00003001c040102981c030f0045030048545030505603103540d1f500e4203224050344141c814419101e8030441d800411422514680000307901504824001006410300c500200043d82c40038002e540c44a45e541d8003154182c002c0c0c82e040e8a800e0f03c9105104616520100d00390151500710000c0141d8102100441e11074400c40500908620021606148003400391481005442c0040c1040c08580303010a1100801da01a02846100b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 30921651 1250 30920401 30920413
    0x1401020c040204080312070e03070612022206020d0512010329010608100e1902130f0b03041101020d02100f020904050a09060e01020f04050f06071509050c01210b01020c0406030311 79
    0x441403103102c20078105280a0082d01c01e4ac2e0928034102d81003500340d4a10a40382d5020003569074501802d2818a985001e03000207405034078140103001b410318114401d483d0402c0703418451b030b00b0308005201d03279541103035800141d464070704040150b600c40c088180c00410700b800c1c501c1000040c0040e002240d00d44250200c941c10703940e007a151101010703461070aa4510222100c075010740c00140e00594010098910798180d0740c002c86035541d0b29424014419005044070201c00301c04c0c0020408007107401d0320f02c00402d0010300710001040d0703c001c0d5103440d007840500e01503460f1102c5400c034070069411542c010101900038003072840c1026001303000c2c12403240115041850511100001c910620965520000322040c041c030b0645401d00b0060041800c01d905a4000805c10410700010506203500891410742e80000c11240958245035042c10400c1a496050003542c0d000303140807068445440190540881002492858200040380b1345900400310941103842c0c004040281600019100b00126010003245c0c2 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 30922901 1250 30921651 30921661
    0x306070e0f04091a0705040906230d12030c03060909050a0311030306030a06090804050301060e15031207030f09030b07110c060403020f1507060923161401020c040204080312 76
    0x403507a21160141818100484200d2502e03000c4d19030541114003890640d0400c0d858110100032500039500144940702e40c03085622955800000c500070b0070404071240e114401103901c40051104108000c1e008065a03614000c12103402a400ba2000d002004010800b10f411417400581c0c9038803811003075000c02c403058100d1084440010489210340340c09400b80200c00c000f130b0303102400342580010403500e050052001240d10746091081a004105203000400f2600345452072038040301e52882414040d8000e000f00316080e6040000f1541080e40c1450f040501d5405440d04480c1c90301d4035000284402601800e10044aa0119403000f1411154003034071759581d403503000c2260510540c480203400805111f1740c00d010346007032680d140b004da00034150a840e10410340c0d5998202d801d0480d045605140d814a0700f20700c103a80b5207034401d02580800050004509288080c8107000d02441000441081ca40100c48543d01c280030500321100080e00540d02d0b66110f0b4141500c6e6041140a10361005010740025 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 30924151 1250 30922901 30922909
    0x41103010c0e01050f04080d0f1701030b010302121903030b13090c05011107151e020115051011120403020405160c030e010e060a02070f09061406090d020306070e0f 72
    0x165000381ca444240415401d000152080c0d0450291a01940800d220005640c0d6042c0498000c40c4141d90b20001d41c04001038000d09400d0a1209820030140050014000036034981c81841c1903d0f0111214078203000f104208a10f0b0850340340c203c15000043c0c0c0c402d4420035401d50021414540119440d0500b1003089580000300e0701480d2000e0301800d00301c07030104625400b07140354490140d0081c0c1900c4410b62102c907103080107001503500800041040b02e1046820b056510742d03156003181440240030443c000b0103038001d00701240c05058800c1128140e20740b110303401503c6e840088805502550310700901615034039081d0f0040c0c4410b901640c2440d000a1030071401142c0301c1000441c50b01d1310440318000391000c5552100203505141849465010030300655580005402003c2c40e960040c1861828980b0341d07100c404065110802490601c001131000156858044001304000c4d03a856840e00c040705c0008d09900c20007800039400d070040300203009001d6030004050400720001d445403510000110180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 30925401 1250 30924151 30924161
    0x1b07021c031b050a0b1f0602030c010f06050907030f0e070905040c080a17030417030a0c090e0105010f05090310050f0f06190510110105090c0114041a0a12060603020304110301 77
    0x200560009882c1381d0000f004481c025800c80015140807104000040a00c520b19a0369000305006da80041180b00d81142c003400380c1c80c11303411100c0b0140800c524103070224901c88005072841040c1a11202c0d1039195658a40c008007070400514100e468295a8044e82c40003040c06541c20b40740c5da411200040340c041000120f454041e03070f1007200700320340c0c0e11078081c00f4000c3c0d000a40110340d10100d031070580c09520880d4000d94018000d51030005030b1207400c107502a100b5504e55010090304d41150004210603a00725a19458090481c2025540c0b1850b202c0000d04180454401201c45842c002c03d0015041d00030088510608948208004549071002001a005149200d10307010481492062109003442481c0d8814030074981801e2900d04080b41445003901c104842814550b80034040c1440c16691140c0481c3c00410b690901c2c6180c40e00700401c0c106040401000744e040c6a100192403110365100303074141c091403140400100030b20342d12100000d000e035005480c00e076041c80d034125101d013142c40c040c420 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 30926651 1250 30925401 30925403
    0x1e0903020303010302010c1109040312050702070302090c0a0e0301090609021201020f0d0905010b030609030d06060806030607200a21051206040c030905070f08070e010303081b07021c031b 82
    0xd50030b6030300c2e5600450fa2996807510482e03011001e03a090100039282e501070a4051446504e070004180b0030000650212a0000c080c0001c5500900080016845001006801840d9800354a07550194900240d48003901c40040c80d4041d03180640b0700c400d2020135405040c40300d108036180d01c00c024030b140400e400d030701440300b0341000c1c240c0800020f828070003241d101c150b04500c81e00002c2044c00b240d0f00040d0030310408540d40c040301d403c0001d03101c010707803a2846094098000d03130500000ca81440d0000ca641c407140184032905100314602d100301c00751452500302c88154442001c8452400407881c0c42d40c515000c1c2000355500ca52207034544100d503401007058800d41021240402c02550310703081000090801d0603a500c0500d507a0b0b41ea45004168240007100282c03484002d2401124603009040c1d141c1022540724034072240204005200203640280e01c1508261075041828007050240485c114622590500940c003002c0394690b00420f4036081c0681c8011406600c6504000303164400200005a1103c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 30927901 1250 30926651 30926653
    0xc0f060c190e03010c0315080304030809190512011b0809150402040b1207080f0d0210050603070f080c0916050901080c070203010509030d0f0b0a0e09100f1e090302 72
    0x2200380010340d00111014001a60703890803480d00c20782d07600401d0841d4404a13220740000e0301c0b40d040c3d001040c00a584403008003000c1d03006518080c91502c1e003480790300500e003200d0f2040e80307002c04d081081040700c0c81c81405044c0060100c2c009590320b07103001e4001d0045e60403003e081070001d060588018042c2c0c00e1540302c0d50036031014103070880c0c0c8860081e58484005004aa02030f035032303428410142d180c07909402c00b1001003200030300c00f080c200a0114030f0700c0110520803103e50300c400811a59181c0c00b107903003491a041c40300d0105007a250500043d003009031035000017004001001c00014941000120ba820320b00040d504203005032118503500d2681860903080b0b20100d181007181c40025480345240f250700c0907116030981d08214050340042d0954005440c81080c6902c0407603050b0503040107100754401d01c000c0743e10401c42c101c41040456540d008a100710400109014001042464140000c4043d03d00b01d400800c4400d0954081000809a204031682a440701415115455885119614035190150 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 30929151 1250 30927901 30927907
    0x708010906150309060f05130302060f150d031b080703030e0609030f0901020f0703060b03070603090210050304020d02030105180705030102040308040e0402060409020301090603140307030c02060313050f030c0f060c 94
    0x4400d40c0640b400032400c445c007607942c44803421400c845214150081045000d002d14281c511300b002480c10743d01402060085030101c090007640b42e2a0381000701c0d080c1d0191940c400b11103141c1410740da0140483e01440a0304100d980f00d00c03c2240d160001c004180c0700703031402c100310f402010300e9a075945d1085800710016402042501c01d98101000688012030051044408000210010b542010100c0d441110420b459210084c407500d400e001c01c0006c2c002c0d41c5401c101d04c0c480f90700040c41d0032002c0940300f03060210000c0070605548032865060213107a00a4002d00107410259070300002030644540d070350801e010300140803542d4901030080394112504901c0070350400d4144004141c5206014004a0388a07804100004d40c03241d03d8005140203004100001810a10390302703211400e000030b90f18100305500700b040001c00094000b541803810075010741c1d036280c507503552004010312041c568030003401f40c0c03080e03841c5040c8403200000103122541340141580e076480031800c40385680360021365244145110078 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 30930401 1250 30929151 30929189
    0x9170306031222080f0f0610031e0602030906040302010501060309021315080d020c04060501030204050319081b03030a140714130b030c0904060b0307020a080708040902040e0708010906 81
    0x30b001400b5a541101c40c010340403001480308505200c403a40c005411074100740c14407054104103000f00710301c442e4500082c0519203001d880d002c2001c01c030750000038140040f85030703900500c2e50511002d4507056401801159a4102440d46994030001114210015800c4c040041002886801552103207640549444007010b668011000684801c9607204480340500c040040ea00d103041080140f0300d0131b95009459404404410301c400c1d20810740016040c54010401001a41c500240b001c5140c2d01100e140d082041c031900d03200c0054400c4c0300d80c1081c034048245070010024004001140107005e940e0040041040728002e50341d1100040742c0d1540811102500c0d0002c3c03801903001000d40b821900c040702016600c0316076800c070b10340047d1f0f0510021100441c4501e80c82c203142c400c4401610280580318110318210740c000356038100c0c0590042c2140704c0440c140d010802c0c004260b8024100c80c0000b0764a683d01c40444100480f001c4404200040d404000060100180d01c5503009954030b40800111865003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 30931651 1250 30930401 30930433
    0xa0308070f080310060912080301091d011505090604060b0f0f07120c0b060409050d0e1804051f020405010c020f060c07060e010f0201060503030405120f0109060917030603 75
    0x4500940d0104401203a0380e00150002000311303c101002078104c40071605064005003814895080341c200000d8482c0b0740e4020412010a60b411162103100220300021041c07800c24403009108100f804560030314007042400d0090780d5083c030039241c00361215000d940e00c0d60108402c1e50414030402e02040c0b01000003401e0310f4101e100400100d070780c07020114a4a95030b550340403210b0f40c28003940800194944580c504020504a50795009041150284094151b64841d6030303c41144080801c1031110449801040c2d454401400750b41c1c0b18000307009501031502d03050030364031010b030000d14080c044d14402c0000c903041c12500c20b40703065401c1a03480d10189103450742407001280c090081140d03c0b900034070188010010400280000c0c01047c0d40d07524075070022500242003068280060010f59042003010f10103510000259022250300b1921762011105c0d9005440c10005981d9069480c0c0d401c0000401c10300c1300c070350003042c1d41503c0384058030014215040080b089000940c7c5a581c5900144940e001d4190 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 30932901 1250 30931651 30931657
    0xc030203160f0c0c080102070c08031306030e070314030901080c1e090402040504050702011d21070201050403150606020c09070818031c090606050307080a0f05011404030c120e0a0308 80
    0x3030703090010280c07039991640684c6442c0f076440841e00f60340018042c802c100340b810003d030003080c21074002c0d81402c44140030f0b441a001c00f070281c8410199a4141d03414181003c0000b0001144c004518140c8441c0034000b907074484c3e01400741540410080c20105d00311034540001c44e188506040e24424001340b00168003009a03200e43c0000358425028000401c0907030395482030078000c1c0f407142c00000b080c4404003060094040b4074240b200f2640c02c02e00c070045903544900120020407a0046a140e41c4040768401640c5501a070b4201529620310204082480c00159000703405660303060f02100c1614046500b0840748042c202c8820000039010310220b040b603030304014090300e00b00341401500d082140b1007440c0200368003201140c9041a03252660310081c40303558494680900307010f0303000c0d02c1203070b060a0b0302d036035210356004008140302804400744040c01020f510840102c8859004c0d48980d0801d410001c1100f628071a0540300d076540d444040460314028260317803a000d02e010f4141046145542c45640b4150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 30934151 1250 30932901 30932927
    0x8010b0c0a061802090a0e0718020c0303090609061014060d06080111120c0901020601050d060b0a0e06031501060207060f050403061d0f070303120207020301140108010f0c03020316 79
    0x2100d03031015040000d48600444148082002103403500c3c40060040106201010b0141d03100a490b00c070760b4043c022400300304401035401503108083c0f0b081040752060f009100b400714803161800f0100c1880a81c2c00c010400302d0041102c502103a050b84c8819090304190b60040c8140c1d14180400d5001460a05042015003200b40581078000350595440200704d003074a8606040c9030040c031001400c94181e409105001c3c0d00306040c0003050f03060504050020f9501d02040c040c1600c6000e044100381c04115003a0000201c5a01c0a00b03e040456699400701c0701c204403d81340184a4050740c1300340c10b180c11080545038101c0703007039900401c111460403e05a80c410b10008a50b41000000c12010021540600412518408404415016910045209007400b40220040311540c0081d841000407039408802e06902078412180181c0e5803c0c82c0c40021b0040c541107000c1c09120400c280001403c900648c0001c60745181c1100c144400518a80704600f01e01c41282c1d403540c5020211204a15140304020014441c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 30935257 1106 30934151 30934153
    0x3020f0628020129060913140a050a0218010e13021308010e0616080c1c0c02010f09021809010209060c010906060f030305030406110f0d020301030516050108010b0c 72
    0x403000040d1315600c5094080b4604059580d172032111071754400104010009418080840106c03034104440742c0c1d9000b81382c60b00241c0048650300880d24035058102280000c42240c40040d87c4d401c000507249500000038003203980000ca640e00c01801e80c05018410303002c0750352a0071030042c00d4500418603102260050801d120200700c60341c101841080385030800614950701e11446614900980c40908155030490000541640c002e9100440007125613000740032260b07140151200b0340c0d2000c2d03c0250480200003141c40302032518a00740da0400001c00015241c00c81c0540050042e8001c09030381400350355600681d008110092141d04003c00051001e200341510316100500680401000039204030f0302c0322081e48818942c60100d0380500110080755440340c846804c913400a410900080740c2c907200c0c0d00405909400401200c02c01c85030140c3d40c9040980c01c000c0d000d003083d00407000d43c00c09 = true := by decide +kernel

theorem cover : BRFrame.Cov 30755401 30935257 := by
  have h0 := BRFrame.cov_init 30755401
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 30755401 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 30755401 ≤ n) (h2 : n < 30935257) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
