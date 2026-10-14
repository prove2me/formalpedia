-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0454
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:53:35.934132+00:00
-- url     : https://prove2.me/submissions/3850a1cd-4604-4b9d-b375-e147a9d285a1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 81474821 ≤ n < 81654677 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 81476071 1250 81474821 81474823
    0x60708030f070815030a0308091501031b0b0702130b01180305010204090b060901080c0c10020c0d090b04080a0219080d08060108070e06040b130b040801020901120c0e120f 75
    0x5029240701e0304045141e00e00600e0040000d0380c001d2080351030180e0740b04004640d4800107444100c3d264141001c0038280d980051240ca0706103c80388285902154800000074007042100d2070308800c8101c04901415900d50403442024800c02000030b401018043c200350ba644d069a011012a00052601580398904003204040c880346a401c2942c180c0d6000030100413101c420b12036030721901400d0ba5914100341c007500c0040d2a44c440107041d00c00c0d2030000100100356440c00c1c4078800424505600464032410350709140c40c3d07a5016031010788046000b000000c40d03541036040a40381125900c80042ca4015681c0e8280008410030200c0c0002021a809003c1072408082c81180c01440381036844608610304000010520300003c2c010009000c2c8004260800c0e86540f41158203607000000119900e5034905007081000d5442c1d449000511404070300401c940a0640041030700580990720082d1500841d90000c04640070f010024000c0740c04042c8250305401e06440c0300703240591100a585142030010140c2d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 81477321 1250 81476071 81476077
    0xa120f06050a06020f0115030210110f0f0105060f030f030406030c0302040506030915060a050a050906030c150408010f1b0e03010b060f1e0a05071509020303040905090c0405060a0501030b060708 85
    0x1c000768110420307000701c91800340706481461f001c101703500e080c6d10f10b5a00440c80064954092808001c0d040b8862031010804214020024924404680036400c0c80c460350390007840140c1d10f2a1182200a40703407500c500c0c000a8845109569502031890700346445025001880c010001e0f07024140c0a2100080310798400000d54485c1c034508026241c0f04880d941c6d400c0002030020203046c8520303901030051040340c540320b4400096503000e0b02d620340e00e03883d05000245409240111143c0c8a1302c0303035107503c084440d00300c050720032108034000a001441500301c10304142e94440041c8000e2203c0c0f60381c0d0b00415807258081144c000000ba00024084024a022424a40c8241c400b0046008002000440d14030b0a41e0802c1c1441c01c986003060820300710240c018050b10540401903d0b1000182040d004d6240c01d50040342240d50003411241d407940d442d0a07010241000302c0741c0e404c0307074081c1007144412803c2c580105407040030018600c0700407d0400e0019002032030440004c0b07170400010700c40c11b00018442c40c01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 81478571 1250 81477321 81477329
    0x1b0602120106030f0e060703150905040c0611010b1c0204150806061504050303030a0b0a080a050c13150b0c070f09090b010803040f0312050c01020a080105010f050a120f06050a 77
    0x40c4103540c10b210002e804d0720300e89040c2000d070fa4a800b0301800c5e802804100c00f40c000215250105102503011146840400ca41e041007000c60310300030601041200f10044402102c00380e464201150b541880d030603007211081c820841d00614608aaa1511084002003030203080c0b00410001b41c04000c905100c04400c415040301c0c006502032400e012451030601c4c200c555000320b05098515103410807002c0380d200e0202812004200d521036420310361176540e241c080700140044808891018030f450030301c99981c51034200d41c00d0003411000751940800406000710851204000e0b4819945842c00880d00944d900100b04a0245c0c091040702148104030001c001d80104048a80826443c1d41420600d141140c10b0380b2094003580308110406c0480f2003000c0c00002c031380d003100801d2440c44940c20241d540d03201c0c450011106510005003908142c3c2c10201940c183ca00c02c0e0790f42c2e0941e491104d800c0e200751003904040c0e00490b14441c1818218a560f1300b1008015989003004070b0403d43d240042400b040590304 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 81479821 1250 81478571 81478597
    0x5030711030a0f0e1002070b0c010902030a030513090e1c03240806150907050901030f020703050c010b0f01120905070b0a020f190309050d050718060801110a050a1b0602 74
    0x1000080e1241c0c0501403600041017103031070010194001d50065991807082c800c4005001e40400e11030942402940f0110019401400b51680d150306c0b4075000340b05502c41d034070605d400d400c003080114a02003640310f0054060000c100400045401c10510703681c0f1460004464201a100c0d000b00455007003406904000e88905031071038102508100417503080200052a190a103000390000c0d41040c0d8884c03483c60b40241c440e0418030b40d62001240103c1c00f500d03500c640314002d2800019401c0130034be8040018910301d88414002c0000103940390801c0000104098a0380c00964503224031a01c464041d8040c60006200f08112404160b0701c3d094100143c01002000016812a03002440c0c0c01d441400340c45d014038a49010070814500e40ea41c058544002d90050354000e0022107403c4003040000c108030800307400c0400d49070050032410804c6801504160050900c43d5003070290b40c0c103110004105544100e965626282c1c01c0c0b25400604580c4034020540348141d44090222090124070369100074240088904 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 81481071 1250 81479821 81479837
    0x7080a021509010f050d020c06130201202805010e0309090a06061e120e070f0b03040b060f0a1802090406080610060302090301060306020c0106030204050619030305030711030a 77
    0x4010001040703448401d070100c0220030002c841c260380c1e11003010701c020296410240c0e121504050100000d01810403c41c0c218071564052004a805410708000351038400d80c3c540180d040076408800c45003544080d9278407541c1c00001489000816049c031540140ca02d40d565000f118280d80f5001d0a54003010008103103508002040c0e000c5042500310503a00510380e500c18450185014401031003400741c0d810410703200c130080200070440780c411460342d401c2004481c428007030b05051105140e1a080c02d031054624003146810005842854603045c1ca1041340c1000c04410035554401c280100c8607003070402c0c69030003107034080003081d0f92174500e02e843c0c006240c659005840300902c0f030a00c41101c0c0310f9040100309900c4807081010402c000508201922800d18004d600c031040c28020902511300c503000109a28000702d000c8503104815070117641200d000b00c600340b14a031526424010071051aa408a4100300607420134004240100e0066400c0320741c5c1c0c6442481c100007280d001c0e04513001a440840010600 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 81482321 1250 81481071 81481073
    0x1230915010e06030403020a02010c060603060e100606090f090b060408070e0430030e0f070902030411060913050403020304090501080607020d02010b0105090108041103030a021e0a020a0504050604090507080a 91
    0x311402d5444008252000d510b9414961000795580c400c410300281002600680c01d8100174290300400000c5038803250501416500e4400c80f610b0341105654940c000349030a5001550902c20300c0c807401180d8401814481c594144105c542c060704480024540003038040100050101080003000c1c0103101e8009040315900b0607107802000340480d2081d440f0152001601c42d00440e80e0a01c000c149001c440c180041c110741403407486400d001d2604070329004ea010301c032030002e01541260001c500c00c5202d2910385290302c133180304004407401000c0f035654021030340010b00b5a0140042c1c0c0442e4106001e40120784c1010703554032401c020380d28240c2107500036810890034885010f804021110361052640001d1100004e500c0c0002c006025040c4020f0400645034041414411103000103a41040c0c0034050707030395038283e40354065616484030fa2600740c105032000c00c620f003e003404101101c001c0d9005181040791468207081101924001e007000ba03001da96080340800180081009900900c0604050005000c4d1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 81483571 1250 81482321 81482327
    0x7080706090509070f03020c0a02030616031413140313031202010f0501061b06020423090112020108040803061201060f1406040302090106050f07060c031e02120123091501 75
    0x80e03a840b0b10f0045200605001141d03800000980e51400f0740d160040c2c4556410122602e460000403019408d40510300900040b4190041c40c00e180c00c00d43e40342803040c001a2440003035100780449026881070520b4030044001209412803907030320101d00d803c50303050140d0281e1554a0140603881110044440301c070742181c0343e07028010f22001500301c22007007140f90706d07090000d020b440740e05081303400601c0619910010400254141e078080c10000900d60641c000607159009108000a00e80e440340d100e0400005408582c0c1e603c2c180c0e900e6044c4c2d100302c03d90300d89568440043d00042e00342c580c051425051f25a544800b4405d43c4c009201100706843c04a18010020864000310800c1c640504000c0009001580381c00021a04495044c0307480fa0361044201211031042c01500c0005058506084c0341014055140c1c10641c0c01d01d1300d403a500900305800108500492048200d05819905d2410041142c05240d0351499900034446480110b00301d01c6400040020b003003182c010002d251841c0d013000b407650b8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 81484821 1250 81483571 81483587
    0x90f120b070503060d080d0908030c0301090b031c0525050d08010906140609030102041d040c1403101505060a12050a02040b0d09020604180e01150f140406030507080706 74
    0x280d6402c01e01c0c510300348800800c00204c40740300c000d0041c00380000d20489584556201c031000c1c1e6040307441292281449038118a85920130300c40c0200d05030429141c4142c916012840001c80f181e510b0142e07100d41801da10a81c0e01c1d81210200ba003000c0c019591039111005e59401ca8028244104082c0100c942c190714003800101068000c4032a4514100d4284a13070030400750103103d0400304a8000c0d4031090040000390181c8100d0300558000f001d1040d2400300703178190080c0301d8051032103040c001c4200e0307403142410318085641070700d2150f1591018005582c080500c0d800f4114001c0c142c1126010241c43e0404652964025048040022910201002c2c2004148903060f04504484010351a2030701d4003440291a010303081d50b11004035a105649021956003c048030000c180400300000d0742044203e0000c0240100343c41d09529500b020600341c0c218080d10400e00a031110070340c075030803020704000c1004200305c0f5102140d80c0155482c000400842d100300080d0000f0721341640101601303800c100009082c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 81486071 1250 81484821 81484831
    0x209060c030c06100b07031d0a0312260c0c0106170d02011a01080118020d0603200d08030a09050312010305210f0406030902010c02040c0e01110303040804060807090f120b 75
    0x144400c0c2c4c050164607808400c95401541500c0c0642c0c01c2d9181c1a107007084141c40050a41d480300c1200000820010160300b411011146511480076900d40002110141c0400c40c201c55070406041001881104994001d4104c00b650032000080e03440e140d040140ca00400520440250b84c001100010b0a6034240103444c6024201100c0c014411a003100280460f40180074004030002d06400e6803c0079604c2d0b0703043d80c00500d521a4144421556400d203421007441c00301c000080500c0b40e20706c9141c0b50404515074a5229032210406145d5951005241c00034035961a085806000400050600d41051840c072400b079401940030380070485a41044050005003070307500400c6044280461031841d0045420349049403020709001c105182c4520040303d0f041c820b040000d41c007034502400c000c011540b102c1080c0c0c1d8504207880c0c2c01045021181d02d1641c034001140c00900c5170101b0002413008070f01c500700c85500400306040c42003116446e6000308501c048180c0141c20f4840c040c00c8000d050000b0f0018030b903001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 81487321 1250 81486071 81486091
    0x40308010f27090f080f04030b180a12090b040806060a120c030221150604150f0b07110310050601081006020604020d030210063b010303080a0209060c030c06 69
    0x441ca4100b80c54003207807000000314070326a14540759090001c84034040a0a582c000f4040d41c4e902a44407400000350081d00050721510103d400042c4050700200c82c074619403503034400400f521440c0390b0725407a24095140f6442c08000f030503c40020302851180245c4040d10340a8013401d040c0c0307066014071820b05015404540c800144403001b10101d0071080084064030b406840c2d50584400d00124030340e81802111a51506108604103107005d40b00e100704050003a03c0c200c07000d1241c102904c2d20000f02e02d02500421002c2101c0c0002000003149920042274407030b1140d6903102c1c1511540700040d0900c00ca402000210917121030800202d5a40705800da0390007503a111030701c900141048030081d40d03040000c000a004540d40075284051500800110305614811882803000f1901c0740035503a10071000500506201542e42030f100011074458681840e102046410300d5641e0703185440480301401e010b42900d028683c20050152540c541c6002486e0314030800c0c0096036103181e000d422618000d001409500700c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 81488571 1250 81487321 81487349
    0x105040803240904030c0c0501020f2802040213080111030115030c030b1c03020c03030a2708060a060e06030601030503030703021305090f09070806070c02100c0b040308010f 76
    0x40300403041c0e070340000d40014203034185800c01d2040e00100021040041e4440d00e450708100c201135000558030701c0c1500c0f9451100340203a54000580c0e603904504006500c9400001851590b03031407800e4010004405808440880303c0103070007007800c03640803500e1078074001040c00050141c013000f40642c1a80d4030340c82c640d241c50341d89081e440c42c40006413850040c0c101500c1e056042e06407440798220070b8010900078006505402d0f50382c80d2006121070807104070098020000d91190030f10380807056400d8808103440301100803c07080d04108241c4146103070030080c607651410103c0d03400d070700708461482005c110400199813420181c5000100600400040c070a0348030000502c0020404030590790090041d05001d0385a2038549100729400c0096000303640c21142e80800c019000b04050720031030182040c5000d440704a030f00c0300362050316080220382403c046a8034115401c010305100c4e2000040203c1440c103441341803100c2d650840b0b05201a50705070300190442c401440620041e180f00801800c50607400c0d82 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 81489821 1250 81488571 81488573
    0x140f030103140a15020a021e0105160203160609080715060e06040e1b060d0213050405070c0335071808010905070b0318100504120c050303060909011506030f0e010504 73
    0x2400130041c10482982c1c54002c43c031000c2007402001140061852100c00713040c000e08003143e00380202011a18040c8600502c2d015942d41400070088428034103ca65403848540920344881c2c014011441d402c9824070b80c04c20200021401700361340d180d0804603011012503224540307a4180c81841300504a648901c0c504215001c0a1800141c0340b240d540b620503001c01d01029240c0001e015000c1c2c510200e05183c000664288042410411134066030f408480400c01c980322190704580d401114400200400d590801c0b2819903500c00c50504241a04110140841d0080941192507018251050300128100300003c6410051040c208400f8184510080101040c1c0e5203805039207281038800c208804a001010403181c01c03400d00441b0480d071650080318900c02c0f002c0360300750050100f00c0d030680c0d011090140d07645145106818054040d5000b03802181076895250402401c050003400701d00c0742d0b66035010241a00f8108665070750040581e91030000e0390402101039441a5031b00c1d0801c0c8004c591400013004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 81491071 1250 81489821 81489833
    0x80108031206010306121b09090f08030c07020406060e10081006030e03040b030906010303030608011b030209030c0a171b0a0303050f0c0601090501150c11010c03140f030103140a 78
    0x30341ca6190042904180d403502d00042c0c00501594010160100f002e0040c84140034000c030b07a00301419981c5c0320040405555440000c115110320320700802801d44804804041440031014640150349a010303d842c00040b9400a021a0388030b5100201041042c0800c810500d002040302d0f8a5002c581008005440c00d100c0d04540202140a12020716540300c4130b8514405042040d64040c0c910304001551302c1c20001c0f83c5070790352002480b04170b001a04214002c079440c901070040f04401c0c08200c4440a400d245070400390701035007180c0303030711501445043d5040c00b096860907803501c01007148184220f8544070b8503100605006110341180c40480040c41c00c184e50740c541c40e40309000c403601480c14649a00b07807440004194030034403240c001188036003400411082c425600560403a10094003104c3c940c1d807200700075684407405007400361494007580710818065004007101c09100d4802e10b495100d04401c0f000004441d000008001c40d9400c3c0480140200001c15080034141040e2400514501460359591 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 81492321 1250 81491071 81491077
    0xf021807081605040b0c010b031009030c020108060d050106090c0e01020601030b040b18100f0608060f0a050a020c030403050c19080a060c11100c0f050a0e040902011119030e0108010803 81
    0x44010a00048071480051141d01a2000b9051761100d4540d15009a44020301900f1250700c058401d0003840c0840544040b540304401600e07505403070fa20f05080441d0015103100710300410954100d510050f11200191080c894000034101501002446414220008041c00d074100c11042c15988210010b10109107100510780d400350388001000782940e2007210354442c440040b01d08041078401e1250801c01c940158000c200350703004d00101000010b0f6075021a542d038800c299900b007045414003000c5100740482c1d030003855000840709005440d2001e001301451640e8400ea1040c0ca6541010f0b0103c0a14502002ca941d25000101e40441d14941003502040d2104050a00104807580e03452441d141603000310b0f003a80400425a060f1410710300404c1d421005420280c1f00070002419240c0100011405041611003041141da6800b403a0150303d4240401401075039000c0e41400481d00d8500d6800d03c040140340c01034560b40000c244407540030314025060180100106052255190061001c1580001030b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 81493571 1250 81492321 81492331
    0xe1c060b010314040606050f0402030c0901031a0d05030909010905093307050a030507090602030a030e01180311010b010302040e06060306041401080d020c09040210120b06070f02180708 81
    0x440320355000c01a00180304404643c020320781d030301c0308000a21500754403070401c880b01610748a00313240f1130310108412440308640e00090460140301a01d03540d4400d42c04029008900c05801e07261601440010300541c180385030880fa15400000c4070031076030921000c44c50042c0300241c414031483c1005030f00b003034440301d200c00102001c141140c100c4000f00ea031402c1502c4190041e027028840f40c1401ccc1c00050250307103c952607001280c01e05001c10704241c0700303075480700c100c0c2d0031a405141064200c01c0218003800300c5c400801115134031254000d02008031075410040c940d100ba02ca107040000003c01141c01d40d0010390006050503c10f00080080e0b02020300083c1d8480001c40f80d10b40c0e42e54420000400502d070203030640c0314110001c0008124041c001400003d500129001c4480500c0d10030b04016134600b044900070741040740d0115160713503d405241c00100034107100001055017102c0f040890120b8210100039103800c82d02c03551080c1541011985420b100c00e00d080201c5132442c1c908805801d0001c00743c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 81494821 1250 81493571 81493583
    0xc010908070503120a0306030c06050a030c08060102190f05010c020c0a081506060702061306020f070504050c040306200706150801090b04140102090414060102060105030f10020d0615020a030e1c 85
    0x6503215405d48241d102030081d41d88049004125030f240d9a00604940045000c1c0c400301c3e24101e000e28004e03026207459840b45030143d00400c040414101600c10b5900503403c101c5106145294600000d40c00307000d5402001015401481c4e0510b202e0100104004030394080201c46d001026030080b00104421101d0f0f1001054611594507103052002c2091031113400d8a500140d1344050020941c0e550108844031042c68920071290201d848100f0402128000d8070a0002d4840404c410800100c843d00030441c403041001c949080c500c0740b006001185e60109400f107919640d94180140103114489144d400360140b04020091303c5400e50b103080c1240405400a028030504041c0500318003025011a117481c40c015105102031103e0710101202d003801501c3c0a409401a10000f040c1820700240741c0c0c521118007002009401c9488c03a003600254084070205015075181e2001058800d505200200c004081358014103020040d4200182411031101c0124443e0101805c00c2c600b10300e80500303041029030421 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 81496071 1250 81494821 81494827
    0x100603020a09050910030b0606251b0608010608070503160e030c0301090f050c0922031e050304030f0f090b0c2b0806040203190e0a080c0c01090807050312 68
    0x5000d990514143c1e0003151311a6401040014141c00c0b107002c1e00840380f14910107119030701d0344000c11100d8018500c0c1c440c042c201010007482844000c0282690007402141600500414140d41c1a0154026085803011139008001000029030000300598000c2d007071301c1d180d400c1d0300341403050070790206e012020341007001050101c20b8a550b80500c139201c1a0a4001d00810412080385031012052010100940f5117009101c280d07401070030020085840349814160040421818000c03100c0384e85a107040c00c0c1c080100b01c180d4029156100742015641c4142919290385a14003842c0082240d58090000340410480001945a294115070030740305683d0484080b645450162103460b140c41c1c41e1301040d4810400d524140f1202010f00c5890034800030099903809159078030746041c0300030303440142caa45442c0c401001000c481d0400c3ca034003030f080a10390711044c3d40c1f1580d816152455560400002c2c0a07041d0068140c1508560700151008001e01d005006424031514000000351110328490302c80407103103800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 81497321 1250 81496071 81496087
    0x30301061d040e010e0109030e0607030c0b19090b06120d0f0c0602190302070201020f030301030b060607030203120c0c0f070b03181e0a1e051c020a1415060910060302 73
    0x580c012500d00100f41008120590582d040d080c041e0031b02000517408140045401c20640c10070108030f0340e525406407914492400140e5810101003402030902038000f48054200c00c02201d24040c90514600030b03542e222460034071a0400642c541600920f9040ea408402a20006600403100394100800b50801904140b19401c0a1020344a448e99030000c50380c4c100042c141680d0036038042c0c0741e80750007a421154800b0344600380c80e59034442800003a140000040025400f80b92400007022030503c41d02c1901c0c10440e400248000c5600259003a00c881c1d82c2c04142d40031220b804016440d450b49410004064561038042036894a220161003280242969101911112401c0045201601c40c103441c06540000d000d0b8040c1d120000100112814005499a036402204200c02d000da86500400680304844c0e40105c84500011340e0740c60002503004103200c0101244031110180000d4032800c003c0d00701c0c4001c04850f00441c81d80100010700c949082c0e0103200c02909640001c2c0142c628038100160b0715458 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 81498571 1250 81497321 81497329
    0x1032f1602030f06010306060e010605030103120302040810050124081611030a050409140402060a080601120603050705120d05040e04110a0602011505040c0c06150b0a170702030301061d 81
    0x10022020b50540f0030401d407042d40e40360016039541240e000382c00402074640c403000c3d64005401c0a11400700020030510041c000b04160001c1060b0758946030a0042c41c06079280600790500c0c40f01100c2100603680c2e840100f140c400d071154001c0c0b0340a01c0c02d0303500c07039001440b182c0940701c0000900351000313002901032180d07a52409074150503440240c510440e520340e6002d06000700264003500609040500b0000c4400040d940c0c0d0000900940c0d00504282c10042c01580441e4400300040000d8100078045601000d014558030842026500510207085124144800c1c080300480266031940c2d035510411440700c00c1c581c0507054a0075501d0717040100010b6161420090322a0000f0100303590b00810f0000005007203034055000641c10340400c5003000300d050b034820800080b2401d2404100100c1c00703a051141c0010415402070000c3c1a03039190700211b103601e0309000b0346680c101188440c045004056946d02990004229603888003c80c4001e6155604011006050034800132107440748403451901c54403541d030303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 81499821 1250 81498571 81498607
    0x5060a08190509030703021b01080103020d05071806050a0f061407030e03030f030603060709231c030c230a0f240506010f0801031703090f0303010f0501032f 69
    0x1803076014409400e21040c1141c4942c40b0700421000761041508141100003211403c01d80d001d016143d4082c268038503002c0c403805654910040350640a42c04001c20001074801000715888281d410014500d03007490240b007101e40c03c0e1b401c02902ca080b0840100001036200701003a0640e103840b0241500c0d20507030703d0290340d0f0b0580036104a50600022403078642c85010100954441d8200300d089a0460b11190f40035158083c550046800d03ca0341420348282001204900c482000d00190018910b0948004048400400f1102c1100002d880104010500c11441043c90b82040400100201d5803288000f041d660b81214400400510540101c2d00c28020314401d1500f01000310103103c0d0031030903801150001004200c4a03d40841d8190a4900d10944291001e038180c96008041104c0503014000d030381c005800040c02c2104c1440350025072a0104c00610245000b00b20340c1840d10440c0f400e1200240907121b03482c20780287e4011380b00c10a103000b41c1480b400c80c4108100107100340d0fa2900009003180040f = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 81501071 1250 81499821 81499861
    0x3060d1e0c030f0b010603020a0e041d06010803030a141005040b04090803090d110114040f111509010906050a02030a271805060307030314280206040201020f010605060a08 75
    0xa26034036000051200f03071020728180303d1280115030324580e22504254100c0c0507000030341c8001442e1640341611800d0aa024030301402d03400400070340103030455210900c1d040f000d8101807001e070004400d1007110115030082038140000e05805e448140b61408803d0700030003852040c1403040b03403540c1103401540c4480c3c0c0103080300c0350080d8a15640b481c02d140c001d550b400210325071000151107000c10340d0103a8018440e0003900710101a038240d06031a644ca03000355042e010340003070311180481c40020985582d980360442e040042c03001026102c81da040005007490386c1c4c0380d11103070502c00b0800c82c034a1415404000c1703810044040c00c088841c00340a0610b0300c00c1c00354005c9200740c031100195000c6800c1482d40ca14260090141605010030b50b140380a1544400241c80000c0c007080101030036034420359801000e040c04d140c605d8104141201440e07600c508142d00c003096840076801000a02040d546e040c003011005800d080000c0c040300780f6001c04030305117200c0da42440042007044008105081c4413501600085 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 81502321 1250 81501071 81501083
    0x2060f0a0302040b07080c0d1d090606041d040309080303040c031b0810330e090c04050a0e0d02070b090f030304030212150a060503030d09050c0909070906090203060d1e 74
    0xa174110705d40444683d004401c8880c9902c168825008140e1180d10758041c82e0b020f00c00c40280007206601405070a04001d481030b030740520103010200302c01c001410100302c24200118005568142800c0141c2040744c03c0d0083c4610380c00410400012400403401305003125482007140c0c40c292201416010034603826040140d4a000e56098141c10100b982c0006a000003c119002110041740030b503c4100c0320403018010580306c2104040200005a4284640c099070f640141e41440e0b007801c0c00030f011030388100d0300509101c1d5110401868154100700d06508208a03000030040030f4140701405c0524007a00c05494490094111058840d841c14019500199070150090108030991210141c8070407640c060403042030049800200034400c1401150304407400a07024510740712404c1c94a201400000606132014810682e0b48078550b10381e40081841920303800054060070341006005c0c4191840c650020303c110f401801484000d0707640481700388603241d11000c500040c440250089180800540001d010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 81503571 1250 81502321 81502327
    0xb0a1401150905060c370606060e1806040b1207033005031605090d0506090d0201020c1f060e070509040b09091b120d0e0a1202060f0a0302040b 63
    0x4600800d920100d000d40580b00c2e030b4609621003041c04000c4c0a00d11101c5420782c4500345444034001c41056204816a14102004d0401c8965400c50705a0030700382000c0300d141c3d0769990200130141d0300c08403061800004503103101c1101000342c1c00c02c0c8411009800d0500c960360380c001d01d50140d5a00c070131000d446011170081d200c805a417810451070780078094a50b04015180b00000101c0300009d0300700f01d00702e00c1c059100c40307080d912440d10000030048013611000030f111301006604030f6582c0c0d15200380b400754421030040c4402d01c0e0107070220781044482c0503143e080d0380c010300c8004950305010604820007400c0307200c200d01c0031a1044210002e02100d50001c3c0301c02e44002c081c0309145500c0001040c64000c00c1e241446085101d0050200d0f400c02105e80c00c2171034219400c2c07078030144500c507048031095034010030b40303c3d5110b4058502414800c0941059003c070701d00e0040c00742107041c40c2ca0900e00a200c107242504200b840342e000f00f4800d102d5035800015030203000401904040c080e034192805070a0344207840351 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 81504821 1250 81503571 81503579
    0x4060e190c050405070c020d06050a020702061b0d0912060e1005090a0c150e010509030a05030d0b0901090c050702060310081f1d030421050a0b0f090604020d0b0a1401 73
    0xc45030301d181c0180c40c01141000001344140d030040258107032055001d40340c00d0801800d51116002000c003d0903541143e0380801003000076075215030103804100200f200f000d5050121207030345c1e1329140741d031a45c01050060b80402004620100e64a0143c1d0507002100880c1140f40055440e00340003507018a061003518150600070070050010b06ca0410501c40d070411842d40c1e8454140801c071007421095400016803141e0701003d6544520054118400c014040f42e600c001c10740d982d1419a0070104509046541d81d840842803440d0064010307004211095040150503031551008045125840f8044e01404001001c606d0700c5980038280c03c020214001a611361000001108035090f115100305070b500b90a06000c606c10740d00e0000140060200c00d0000c5207014600070240000d1a46040301e01303010f0100751090f40c0810070511900c45504d1260200f0011032070701c002c5040c6101c44c003402842c1d259010b40f0410005842d440c51003201e098001c807040540765220042000a0400b08140c00110140600005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 81506071 1250 81504821 81504833
    0x702060f0405031b060d0c12110c01060504020f09011437030513170c0105010b0301060f02030307020303040f06021b0c090108010e070302130b100e18060904060e19 72
    0x2005441c0118181c1d400c00072803807003a040442c8101c00c41c41e0300c03003001c11003496428010780c4210007002c7c040c140080341205203009001280e601b0081c0e4003803c500080c1c1c4c8040702c00c00780724100152104640171030a0001101c00380d030080c060b032200c150621031402c40ea600c1c090100b005445c4083c08121107405000c02d4040b010f0a118448109641003076001c4600c1109107019000d0ac5114091081140b00340804940300e4103600000d546001c8510312040091801c84002805218040d00321a10142c2d582d5243c031134010100c440d07031f040e00d4086401c14018854a182d000c4112a0802c4e00b00c1c40981d0007003032030b0400740000e11510303952000170802c107160198441801328030414142d034201c41489040c1e030f88a00517400c1c0d4480c003000c00d05540000348107000500e4000c4881448a645900000d02140c004008c1000c0b80340d0500070a0129070410b0741d00025140040002d0b000c0754402c1c0403a0718a0404101103000f01001400082c0901e40b40c150810462804102014003942c00c01d000c110741e17545a05000d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 81507321 1250 81506071 81506077
    0xa0f0b13031b05040f0e030307080c1908060a080a08030a020904060f090c080f060121272108010b0703020c041a033007050705030d0807030e0a05031801050702060f 72
    0x9400784d411302960012800c07462113510082941440a50702e166104181180c032150010001c02400c082804440210031589000030f40440e405e4481400c0e9050800030000070080560060203d540480051400501c448055a1300001080405602d600041c0300080180c802a0000b00110405d0400082c002d00d4035089041042d1031511100f5071601c8003c04e4881c01d1a04503003060101e00c40042400c3c081040c100021b480c46805100081c82e01100c11800401c84144401c80e0b10700340c400d411140c280b08071868041b9401e51142220072241340810400303050f03407105110f903041804021032200c4c1070500a108440c000040180704120100343c20400041514840200501900c2480412100c034072402110600100b01e0040070701582c00000c5840e102039100b8541101e503400381140000b50354070300300010403100b20b40b03031104e00340c2e0301e80034100030304486000b09180300c43da00c011018000b04202104560049000c01c81200d040c00b21440182c80e82e200c1c11a0080d00010002020501e5800c440c001d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 81508571 1250 81507321 81507329
    0x60c0a0e030705090c090a0302060301030c0602060c0a0206060d08120a1b030902030a0803060a0f06030506010314060a03080f1b0706030b0a03080412030905030109031206050a0f0b13031b 82
    0x40c515904191014141e07580ca4500070550009001400700c3d14200d4210b01400302180001d2540510310745176804501150001ea20407a52340d80308420500180d501448825806400005041d04000c4660070080d0340315400742020340aa04150201d0040c021074804442c0e2254849800003481e04113655440020410010703100500341c0c20500e0780702011f21a026161b40d5a40050040003d1a01a1903080030b550014203031075800300b121039002580d007944881240042285403800505c5141500014081d144107802ca523001120035820041c03543d0700d5040c071000307880c0c1050a05803103440c010680c0c8454451801500300f201e41d40c84054109100005600064802c15030341400000e103800f00b07000d0b551806020061105009110601c01d41c10701038884100036000385005200d0760781d10400b20b07003100c0018030180c000030950310b00440c0b000403e0154a00411081d42c00d055268540103a200a09606000300d455081d00054040c0ca00b002000801000d0b64100c0072140c19101c0460380b0341c01c6542d842c81 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 81509821 1250 81508571 81508577
    0x150618030c0406030c09020a0c140d1206061704060b03011401080d0f1202070c0f0306140906070219051509060109060501050910032003130314070203070521060c0a 72
    0x141d61255003032601621007141c0c0d1102081501c02d0810003a20040d4000141580411000e140000d02181cad02d101d0025100424001034020540b05140040c5030080c00d000307294805040101c00c010309680030320000303a20300c00c0410407c1640c8031841c180000e003141c562900d0345582040c0800540c0b440d84182681224940c0c0304131810fa01c0e0b800b5003a19580d200c0d0000d4404500d44080f116801c1c2c42c1c0d80c0040c54070360f114455240c201c40d180c401d00a41c82c540b0f90000e0b14072035507c0008081340d20360550201e401c102010010680707413800c070b0310003503a401541e6803510385000194013580c1005010441d040700210301d251010807603d130540c6043c0e40c40000b44a140310b410300740000001e5a5000310203c032500d0001500015a09918540035405070031140303645070b0b0a11178010b4000b40c81960002850149000111031034148400341401000408117110244c9200c404100d01001039a00298a4088402c20b880c580110508180120f002400c40d022101031400b4600800c800c1c240804020500446503803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 81511071 1250 81509821 81509833
    0xd050a030b0a08060f0405070306150602010b0a030c05010302070611030103030e130c080a0c05120a0209030f0c06090f12010207030203070c060c0302070e1009060306050a060b120f15061803 83
    0xd0822800310058400d00c0d00640014002ca4407011000b0905580a0b0007041108d0743d960343d80d078824048a10514180e00c00000074041800b20a50a01800b000100d00b1900b5281c16421034668840d00059842104c1c1070540c00501d07541040303030b660094034900301c0d107540c0aa16507a482c140030704180710f8a5a41031080300c81c4404009450018401c0c0c40a50005aa81c410351355520b0b6004030003800d0440c000f80c1400000d021081090781a18607081c072820b8020000368694449074249803078000306c1d2a906950b074018511490382e0b900c4110645000c0002102c5016039061800017240c0400c04085150f00300703500000f0904203150300000280743d014800c40301241d40355565202210156007450700180103800940007004004802520580c1180520000d110300715954034448003180d038140d0049030b03041e071582d080001d4058148100802040d084d00c8580c82c0076855807100d0076211005222410b400d032020003107100840d0f00600c5105642014014503551404c05614001d420b0901e207045219120312 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 81512321 1250 81511071 81511091
    0x504060b060403050c060d0f090302070f06360803041202101416021f090e010605030402130c120609090203010c1110051801021308060a0b060306010315080d050a03 72
    0x781c000c40b001c4030740040c06442d40341110010003440390703c50601060f030107440c0da14072420811140324001d441c0d0310a07001008581d1405030020300000d19540400c1c2406100c0412030899a100d0b00070343c007140e2a5503030040024030301c15034034100348406800410040c070000c140494081313140103108080500840d903c2d0a154141c140454000c80022454081c0c410280020080100200716440383c0c54402000c1c0c1d054805071480030f9816041506c60f040010708903000030020800d443c40c9032409441d6900d0107914501d0690017003031040008844070454543d4032460241e205d440b8039451081820444818800740343d459002c48060f012004050f807080d440d0a50a84e4654000c20f45925400855805000d00c0a802d1070383d1001460000d102045045c00261130001c0e494cc2880104070500792206920b070064107042c034042c5040b40040050381990302e4291030030226501c0070141ca610640920b808180ea4200080003904da0b00180e02c050711a10601c0703e0b1010b4240c000001d0200106c0380c1d6000c202400c45 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 81513571 1250 81512321 81512329
    0x11010e011b0804060b0603090318030706020c1e09010f060201140105010801170c060a0203040f060c030507061d1c031103060a090c051207020703031e021005070e040f0504060b 77
    0x40079203548031001c0c0c03400007103141d0049030035541c0507001c1c0d00c000a201140c600800d010b0350049501c11515000040c0015541c0501000c0d40c4020b80c0582c0201101414440042e544421b607044007403041c4101070003c901e106a403d1042c5d01c510000e487c1c01d5495030345210070382500c1098000c51000d5400e003a00ca2101105500034a070403100d05039111906a480d00c0c0d25103081c1c1821030000800c5003d5140e43c10600d440b036000070000303041c1a9000315943c07071602c50324110b003000c0c0350098410010082c003e0f00100b98040e0503620b110b50130090008800c60a01040040e17103100814001d44c90082e100b000f0a06014280d12150090300b0352401d104901c013000c0c8507070849c0301c00c4034065440452040144204145070388958500000350902c00d00c1d1643c80c800f8100c102000b114000010381c44a5010310030560b05c034035016001140d6002c0001c180c0042c64010303403076030017500d0a0081c807540c0b1030020342030600c14203003450391007009042000000301030b0940d240078ac5404c49042d550365042007000d0059040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 81514821 1250 81513571 81513581
    0x30503100e190b0105040f0308030a200f1303050a2a050102030412022202040f0b07020d0b07120606090e100501080a0b0609041a0405060406050f06070c031211010e01 73
    0x908402580141080b1030042001045295002410024184000b00c1c1c038030750038001c220156009628658403840c123503441605444201c10010105a12011410300c01000442985c011282c022a484d8444084140401c1040703110f5201408c1882001d46440038009010719031500420044100103428a000c0c0d030341c2c4943c050620030140144e208010801182d0b03400380d41d922045200800205442044144500481030034048200c8015030002d01041510382401c0072400030307c44220b926041070b5140c1c0005404415000010f04584403440000d141d9901c503083c0d005520760088400c100080e107030304008045800b1800307941c0700d200b80c14020800450701c0b00304600403910160340e540c0a0b5616448124090310280c250990484014000c80e0b00c80d581e03d00840c0544003d0003c3d41c40500c04510403c426034001801590089180840501054030381d05c2000c4a40a01507500a66905280c540380000d000a07900151000762007020401106a2082c8c0c000220304400c0000d0000c41c000b181628201c070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 81516071 1250 81514821 81514831
    0xf0105120c01030f060905091e070f030b06030109080a02030c0f0f0d120204320f030726100507020d030e0c0108060102150126061506030408070f030503100e 69
    0x3501079012180c0661003a04140003020500d84042071503542c0301100021781d0030030303218080e0365049103000c20440d403070740100c0040c0b980d9050014000c180c0390514a0040a1080c08090030344040540003840755142500860f42040e032106845560b0018004001c0d103d41041012210600600364440b0303400100103018000005142c0c058142001302c1a02500c04925125015649075001c0c800015007581803080c800c0499142100131034214030f01c1001030403202c064540544584211420f1645c4c035100042c06030305582205001114030018044440084400001094010f00c14010400d04004c034940196004201d40e07021540b99071411780055080d0b5060300440a4a40e210b8064124150311410311180c01050600694051120405486003850300980121000f48034201d038608142c842c40810295401c1044080c003480d0034500429a07452481ea1400e9104203008004241480000702c111040305900111a03159036031a4503028100d50030881c4c20403054800e00344002191103901229910036 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 81517321 1250 81516071 81516073
    0x308180607110d0212030408011407020616230c011401060807020c0405100b031f050604031502070602040b1b010c08010806060907140c0304090b0a0b1c1b03050f010512 74
    0x100e400b10050000b200301c20790060764455081c020000003a1018401440a031a0010010400328201c0855202080000e044807046620000400040c01e09182603a0b481040c580b0706503441291440308240c0962820411903021400001c841c5115a81580400c3c4a07401002d94100c2aa070703100300507114114120b84000141e00140f0180ea0185000c1e031000354881c420080300c450b0780740c403450714420a40048440d1400701c261040d900607440707501081e6000610b02144c4c2d007407400b030956039280725039198003003d100c101da0040b944e0010005190113807409494140000340d102c40150407000e807040c80720741030074509529000d240b505e0503100f841024142c80758103004060503101c090500500100040c040700c10040451189001e01120708010994810071034001c0d5156030803ca0b200c0129540c0d4444117104900e0140204018400d2401343e54002e134411000300b500c1d03031041040c280035211072100240510095000c0311200d40e055030002e80240407100d05000f4a0f07885d40244004808114045441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 81518571 1250 81517321 81517343
    0x5070b04080f0d0c05030717060a17031b0a060501060804110108041406101802042105011e0515100801050f0a120506071205070806010e01020102090a0308180607 71
    0x8660040014440b900c00022558035010180d94200c0403110213004101c0003800c00024040320b01d903c041d410800c40742504000d1000c3c2880350015801c450720b84204900e408401d44580c580709c0c41841079881d4112a14030b1034840109182e11151a40d90f003c1003240d2070703403408001080d000d100c0c4003403510499102c1d040c100f07920003100055512001c0107204035030f0700c0703003019080d10100d005102041c0280e0007203901403d010700745074840c541600f000c2000c01042c0c1c41840b0400c03105021800070440c12001c601070361030100507410710070f0142012030707560542c02d803c9810a01c405074140c0d00a511034003429800d032140249801c00c0100510940303505000054803400184918a00912440d1500500600c1c6050545d40d55001c1c41d800c01104d04107071840e4020768200b107402508040040d900341d20f044010000c91902001c0980030103005050f01d810842c071054401c420b03900035411508400b070002c1c451240e00380ea07494a40c85c00c0c0e124500c0080d030340c260307600d125069007400b10940700324650180040b40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 81519821 1250 81518571 81518573
    0x807140409140303100e0411010c03051207080105010f02030c070302090604140a06090b2d18100501140f030402060706060b0d0c080112050c040e010204090c11060705070b04 76
    0x140004014016a6000341d03140d464034005140700d9000b0507000245400f864a0389002c19440d038558125901140081c0a44800c00c4000340e448541d00d980180242011003203611103007421296800380742d40d1701b40801e00400503c0140c1d41c00c4450303241290802d80e90760440d02c21903201280c40e401400c1202801d80d0180209000501c0d181c090709a000801900000e407028040c204404e0103c001e80b018501e45988840c03c0c0180c2c040d9026219050005a5540c8008544502d60308410111001c00d64100700200c00c8170245d642d145820155140c1d4080468403c50038171460144c14101c407071081070f000c18100d08030300c05c422510300159488192501e00050030759803140c090004036405140101c6e02c442c4c1d2a100881c1143c1d803403024245180c0045400038040030098009064082e068000d01c0503003552000b1000003c60003c1e080111200070303580821003a08507071090b8068003a03500320020741801c0600c80b54079103a211660503011048031088800f29140c10030180c0703c900c2121000ba004410440c0068 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 81521071 1250 81519821 81519839
    0xa140d06110d020708071e05030a08040303110307030c0206010602010e030a0e150301121a01050d020609010c0209010611010609110906070c0e010b090f04060803180312070606031b0807 81
    0x10032031600d1141840c544090701e41100100d070b0240b44125401c41c004640e180900c4000c0a141101c195601c40c1d10034807c2c00c680755a075480c0540030084c4104241e04e8001002c041c441e07000078031407810007024907499050040000e4080d02a03458144010701c624000068031a01c140640030350b1540c450044c502d090039240c42140e441841180c1180c105d1002030040c480388103100c00071402090840308505204d545031409103e402c0101100d1001d4000c890018016a038800801140003581203441c00d517a603034040010b03114040380043c041c0d44002000d0001448039003113810141c0d0004de180003000020f4035000020f089880309100c41a409009000b00748507424000024400107024071071580160f5036440507214400400d803c444001900858112290300b0407a5240c480d4903421a01800180c0c10110700f166640608a508a1400d43c02e184445441c0c806000c140d00058600038695a1440e40c3e0400c500030b00b40a202c12034521490010801c804400210400192038030b150103070074902e00d080c85030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 81522321 1250 81521071 81521081
    0x9020f0d0519050c030f030c06060607060905010e070812041d040c0315021b011b05090d0f050303160903080d05040c050d060c08011202060405092205010207020a140d06 74
    0x1114284601000d145981507001c90541c81c0b40c0c4510b0050102d001c0440c241414440003041c400d070f081d4014450040c42e40c0c40410900e511020540711951100c1e25800c0007405030134000f9000d050b40d46001000c0780d00104c0815003a0a4403004001c45c4c1e560f0382c0800103408ac900c0755100c0c0014888607010a541040d0050001c190094094005030f184580c607920361028001382103040d012503030350020742442c9a16800903800c00140d03005000f00500010055807507804004284010308010f40040d0800556503050044524076400c0951450001c04070f2502c2c550b280d0080d02c014048281000074031039840e2003083d80000790380c4e00c40d000500340342c8803c5421001d4440030340211003e800d02c0d6404150742c0c4074816203000f01c0340664008182c09000c6a4064070302031040c1c0100c04070103c0e411090300583c43c1c0300211011a08180c0300d000340755441039003e8889860000c040001120a8410441030240540250400e00c1c0211200040240e07900304e4114841502005079070092002c0c00e0303401c0458029170103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 81523571 1250 81522321 81522323
    0x1003080910050f121b120a0902240319020a020d0f020114090c010f1404210602070c2c0406020309010b0901090e0105060316170c13060603050a09020f0d 67
    0x403d0410303c000328450850340104451326000b072040c40402c001d0f50281000990311800ba401ea0510785074910055400c0d40034020049111542c0b1402518115280d00481d01c51034002040318440707000110709814401e43c800d440c1010109240d000e60720211085200702da179a280342c2e8004000c645034020080e5000c003000820002555a0390b00100c59045031103a8031803040e410710000c4e242d400d0804001401002049094404100b00c0d0031a45c98580c3c14002214207440c2c40c64405070036a07a00600d8078401c0d1014038002440d0302d00100b16441048404d82e06501621504141200d1148548001400d81d16003c5002191803211802050214401d51f00650700298208000300b004014035000c500c442a0a078031400030986c4c2c618840303441680c02e10030701341c00c040120090607d008010304010751031319060180c0311545460b480c4922804108000d460381c03080020302500e100c00910b4003258028843d91140001080c20103000400e00300c128860003003106c1d802025811b03d50308600034041e0403518070b00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 81524821 1250 81523571 81523577
    0x4060206011e0f03080a2006010b0702060c030d0e0706030504110f060706060e09071a030c0a1205090c0405090a0c0306180f050105060f030a080a050315041b081003080910 75
    0x10225083c20007510000285015024580c0c0d2854224402002012503200ca00b0a6100c01d882e00d9019807404030720141190801c034031580d04d440d401e000003545d80c814403001040c3c1c3c1c400020b60381480d00d11a081512004501c00c1950b007496559030083d000e5070000c0300c00500f48249030441c2d2030945072100740a140c4010142905052003042da0f110403c80d00680c00c8180e41180c1e80c400c1041d00785c0d04000040141280d05269079072028140b004181d140400340c60381900c8800840c09480042c031401c051340400038000420322903401c080102d10744518480040c03078003450800c00003c0807003400080090034164072880b0400224910349500c070040c444801003080c811419070880000c541c44203401b50b0080c1c082c0c400000d003420038000f0069443d000b0402c2c075000741c0114406c8004a003400050740c0b4008014100f05a80380d4440804c00010703140d41c1d0240307502c186421300040d00070761071010986508540352580a0a42c550312100340f04900740c1d00c0014100c0704108401c84043c10110031007050101541 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 81526071 1250 81524821 81524879
    0x1305090a06120c0512010902010903020621040b0402030706210c0e1012150608070503040c050d030503160801080d050708120103080a020105060603102d09021209030406020601 77
    0x51071640b0650740020107031820040000144100d03c0d1100420144000000003044070b0002c0b98000b0300076420307900c40079100b154081116030086405100d92504a842d00188091519091414000042054030300307034020301c110040405c2690142d0504071100d4421a840203100300c103c0600c1000c3c1c1421505c12082110203080220a6102c14045110880090f00c50011030700ad0790030281c08490b400450100c110111410410085403c260740c650070910b40d20700a5907960301c3d42841060404a13a111940214140712510107042c1d0100246001e4904040d104010040e01a0100c600c07003020700401c64a50092034104a115005100810075a4443c00c036031400c107030901013150320000b0240e200b910700f03940c005400b900c0d10b5428440c0c145d000004440e41d40c21418907070450304400c0001d010340420102c2d01c004460405580c01031032030a02c0180640b0146454480014802030b4003d004a424024940c0002c01c0300c0200101c255416516954014101c60b071030311104045900720905800c0b8401205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 81527321 1250 81526071 81526079
    0xc12031d032404032a052b0c05031213060507020a0309091d100c09060f0c0b04050f10060510020601030807060c11030d020703080f0f041403120a0e070b1305090a06 72
    0x86810f0400c180b1403903217040e42e021280d0074880d0800108980c4c54880c01e03020083c100202070303680044101011030749000110288c407803622a00e035126010800d0300b034503281403c0000d90403000c019000b03807a1156034240002c0c0c55481c81070780e56451031200103001c40c1d0405018040c40c0c5041d4810900c200c050b0b0405041a200f000d2014101948040c11044117621090580d18150304880b04030010081443c00b042e030049901c038010b10645042c000140f501d003044c00031030103010017041484492503050045d01c00c5000c0d561135034401040382c3c1c401c49000e0740000080410290012030300034120380d0080714580c6090919078804004003011003044003441108007000e082c2c0760080015044c0e12207503100060307440207142000361101900610380c004200f00c2604000d44c1503d9024101d4005038000c8414160300000070030242580107441d140c9012015803810401c0040268010103210010030042e100d01c00d84910210096100d88070029000b110311000c100020b0070031254141e0f10081d2010000740d11511 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 81528571 1250 81527321 81527357
    0x8031905010b0c01051803030402010f09180b10020a0803060603040c080d020703050105010b070807030806010e2e0206060109030f0507031703090f03090a03060203040c12031d03240403 81
    0x2a008041020b1002c654031085a00911410750040c00d03042c1c07034114141c5100f20781c0c0e0391b03444010300090410142035422203110f401520010b0150420107031070204808030340c1f245c4004082c100282c2e84a400c00e1030800c0b41e42030020540da000c15402000305440c1d9541c02c0203200090748040e00494040c07070b803c03c0004210109002c0b603502403013542c0c0a05900c51640c00d01900b500c0301a004840100002c00148000031401c8044405107035260600440c2c540e22640161341c0c01142e550a260000707030400c4c040101d0700410660081d0074030585415440c003600c400c4102e9503000222001408141d0f2480c051002c16007000760043c4403486001120380550b2695101071709048011030340c0d00203080100a0005405080c88407d4900307494000460400081c28001034408000340b0018251540c000301080602040c40c22540140002400070785004403d46002004020520703030a0410016000040c0d0162034003040c912503500d11400f801c081950301266204a0102c050301c12400d001808070034403103401c1c0c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 81529821 1250 81528571 81528581
    0x40803070f03030c03150501030f0608071805010806060105041a0d0c090806070c051e0c0d0c0e1302130513050a0c050f1f111501091d010b030a080319 66
    0x440748407104030041c031a103009000d95080b00d12000502d81401414507020b02550001c00481703500f40380201312441c0d070142200041080340c020405030302031520041110f0782c0252100c0f454202221040040c0ea0b680d074007180e11140c003541c800307001070400c0004000f00030040a4081c21038071402d082e180707000c2d050903544086610402000001c140d0052080010060501c0707510341c03160040c10400780014080d40c50503186d00f040e43e01040d011094100700110410100161a4921005444513030044460f003440c4d460365019101c0c60041441700320010b008550052500d221085d03019041031006051405071030060400100309140440707120f41a600031601c20444200e00b18040c4521002581c10102400021120400b8003030150794880308414807200c1808004007241d0303040c50120b1450000c0c00202c0d0404007000100e0322114281000030424403002c0e8000307100030030380e41040540c0b005034904081c02d89035800c080c641c0c5904404400d401107030000009540c031040a42e12201011402d042d038a0450b8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 81531071 1250 81529821 81529823
    0x20d15060e1b120604270b010f051c020f040906090c0303090510020304170c060301060201020307021006030f1716050109060b010206091c121d0709050106090e06030304080307 77
    0x1c0c90308001d00c101c000820349000d14400c10400000e20707094440550780c00003103010700a54011036545400381580310b4044500c1a0748464540c0c00c5100341c4207810007000c1d011003030044000c501c410140020f520714203000c01c0f01440014000d070b40c4e6441400d40030006000c91861100b50041d403038030746400c0041c00c40d2040799082071254060752101819400d0040041c00d050f00f00300d0180d07004041c1c000c1e8258002041e40d04503078903110580fa10042c0f13104c80c58284480e825032a6041000480080390880d01900510310030364250f803c5440c485c1400f94500c05490080c4800b800c04001502d46d030b4040340c1000034000c070348541040b42c6441e0100e25040c1e9109401100000e50b42079544040240400007540550310b0b034200c00748002e000d01e04200c080191901c05a180823106c64600c0b10072142003074059060140d00102c3c000040090251a10a00b00f02c200340c0400e884482c0502000030910501034030a081c165106540c0307840c0c085041c82c4112030010b002030503c03513040c4400d1000181b0b40b07908000400110b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 81532321 1250 81531071 81531089
    0xa05040507240e0303040b04030212030d020f07050613030c061d030a0903020f0d23010e070627030b01140303070203030406051b07060206060603041a040503091008090307020d1506 79
    0x11000402c0c000740b403021002001c51098000b04402c005824580c020798081c5c90f01140c0360340404110403852031442c400d0030800ca200c1ca00205071b5144c01111174001c0c0c1440c601803402e07a0206d41e1440aa520004e50f07044004000c076646941100100300740707900ca41e040e048510040d00c1d4618100500f549183c00c0203440b0b00002e00120010700031410403008500f0060003c3c2c0712204480c00300d0766030f107802440401400e00c83d400301c6c2d070a40d0078101c000d400c550f50701c2032007800303032075542e074540d500185581e2090217030780d002d101c64000d40b0194481d8814403900b1603400c21140303103aa900f0700d21220b5660b14084901581440207010b8140980c0d010301c000c2000340303029140c1656516050042c0000310460844001d510303000b42100f040148e03008100380e0351261003110f009035603613100c0c42c040c03508542002605020080d40e504120401070000001c2c25010307803c60f0f42e0140380e034074040100c3d11366070101c64404040d00f0910031580141004080041403a104840400c429600c0c1d105407000c550543d4405541 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 81533571 1250 81532321 81532379
    0x31e03090f060405010f0b010305061e060f04080109030f020a02090103020103110f220515120402060f0703020a030e0f0114030c190503010501170105180c19051308150a05040507 78
    0x805c03106d074820b440d9800320a007010b110a242120000f22072101c03526a0f00d000305248641c040c61031741c8940031500080d200405c0151035549444000d0b008150320281100810040420408110700000b6001c03500c03940202018810380c21640114050541000c0010f81103030b06100711a48402c01401070540000034003804e4911000882141959001c1580f2a0b40140103031034004180d00c1420f0121600302d60350721029030158441d44049000c074443c603da1160300c0d920104140c410507a012500b041c409010b607681200400d00c410400020200344a0451b002c00d109400440700211510060341d481503001d0620b0b03060191540750040580d0710001204000394000006000035a00075298416841980081840c9581004c3c0482e00d80325040c08801c1420001100042d9013010200855140e500c001075190580c840c600c002038041d801c5600c8240c13003501041408150040009010703c560300142007c14895110a144540185000f50084d1134030b004d012070100c1c50440101d10200690200420188 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 81534821 1250 81533571 81533591
    0x11100510050105031918060c032c210705010606090812030408090402180301060f0614030f04080a1205071e0305010b031602070503010f02031602031e03090f06040501 73
    0xd94040035810031030600c0380c1403092007010304c00030f68010980c0f8603e140020780b00401b02c402e4110038403221002440141411540c0d000c05a0540102407121105003207a58170100340f410864034441c0701e17062262554020000b803185640d21000701080b0749003a08080d46041c803641c40b0b0724250350395600030380045180c200301080385500420031091040079242500b41075081c9507450744a03511a91102601c5950041400010710200000c040c0d60304500030020010965540308251700e540c2c4920480c4080707540240340d40c048a049030b04a07403003800c0640006000e965a40d0700e4642701d400910030001002242e480040071101d003845614000c0100d5140c240203520500d1020844144103410b100400d41000010019000c07100301752500200d17410b45034101040c0c0c8880807481c0036403035400b007a8558280b035003000d44076500394010f5005c0d512481420101043c085000e07a0780e84601c0507861108070741070b01507481000030032024542242c0c020064500c0e00b200c600d402d500e4018195420340e1680d41d5404009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 81536071 1250 81534821 81534841
    0xb2b03120e0c0a0603020a1205070509041a010f0908030f0304230105180c01080736080d020f0c010804020d0b070806030705010f080103020405070201020c0706020309030d0c0b04020f01111005 84
    0xc00504c1249425494003400c0140103104001a004c501e460a4440d0301155026010f1800d41e007030740001401c00c1107010b007800000c1180d81070000320240418502414440003030b200300e07400003e40f0b501c18015840e0500a1142505940c4020415038911282d40306028040725103d20301c5c0454032101c2c00105403402d0849060718150b0320b4124541807648801c0424081d642c12015007588100740e814010154803900c3d94505c1190610741040b040406213440c500d000904400c00c210039540d00000316050b8090801c0b0507030383c0d070714005040c110640c04444807803079540c0b00d13488840d030207880034040e020703e51140d503940311307400b4820703680345000c81c1281c420068141005c100c031b20b004240c02d00c1c01d05000c2192100c017600e400d90600010b40903c1d00e4030005242e550003501200c0d5100c0d01c2d00d04031f402e07050369a44002d44035001010380901c40c1c000c4512620b01d280c420399400160540280090190b6150f5600700505125507024483c10b008010389141882070f001d1100721083c1c10030b0000460075150102e021 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 81537321 1250 81536071 81536089
    0x3020306030c0d0b04030e060c0a050a0c0506040609090504030c0818091b040603110c0703030f0201150f05040b2b0605100e04140109020604060c03030b2b03120e0c 72
    0x14900401d0b0004880004c9000e80000350b80041d05410100301418600300032405070312030307150701070441e1103500240c1040082c00900c1c804054012030090446d86d40300c0d01000624807581c4a1400020340000c4240241e15007a40000c2e0050710904000801c5005640c80c2d40a039080034146c281c0d2a40340490b5000030b030030014180c0341e1061001c000b202410303818030203650035401140204410107030384540c400e0041e0140c00440701d1400c5900111840d460b07403440e004024801d100030381c4006500b0848100c1d0490100c14811059401e95003000d01c0706824141404002d152507080d4640c05901200000c14110701691051710340f003102d0044156406032030601d1010f86402030128443c503200328004100014511001c41d421039030180c1100c550390030800303040d0701500364014042e5010800103000a00c043d007125060303404610a48040c020001d05e07800b0002042c500780030311990488160311110503100029001c0b54101e22078148900c20140d0301c8001001c0b90901c000a440c0380c1d0040f442c000c0315140000d01c1c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 81538571 1250 81537321 81537343
    0x3090d030e100e0a1203090e130213020a0801050d081c0e01140912070c030803090a0308070806030a0305030702011e0603031e0905040f0204092f091807110d0302030603 74
    0x4104100f1410110760a0503051140305107550404514508051091403400c005040300d040380009410802c0071f9000151008100f2846045021644521008280251103007040345480c0c00f00d19a282100303010714046603030400c440c180002c102c40c80c0305040311041409000350072807000401444083d811801c44204906001d042d6129604016070030780c0000310015080c0c84000402d4480340e02c0d140c501d604d441d00381c100500341c90340801008800240002c05810140c06076441c55165214141c09403042c9500303440803501500207482c2e280200e0701170401103812400d076100000341c01045410328582d1420210f043e0640c50303101c0c1d000704180340e400000c0da5030714081401507204a0f407400310003409070f0b1041d01c01c140c01940c4403204945040b0156040d030b4001c01c0c102c00306000b69134030a100d0480d250031212041d850300031980494020300400405559003d24080e10300c1c118004406102d0a4031640240200c0421082c2c005065030442d09126001480007036072005a01e0b414070004150504a040c55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 81539821 1250 81538571 81538577
    0x50403020c030a2a0b0c0a03031112060d0c1509090f06050a091a04090b1f05030d03151208071202010b010909020309071a09090604020903071703090d030e10 69
    0x1c03040e80411400c5107924104111140e09613100ca50982180c2e4403148254406060401c02103212604500003281c00c0780d80f580b1907502001540c0024031144100e000c0d2412541a1078035400004840b030400404411000340243e641a2010741c3e00d0300041520b058141c038000014006040820000740c1030300400004950034042403000f2401e0038003040b20403143d445003203241078445a03d0300e1060380b040423083c88401e010344180240b090300c0c10324240b0180296100c10382c041c03004002c0392048a4000041c0d080c0c4034001d01070a1080c81880d02100a441c0d60301e02c103e8248003611000401d04101a444080ba41c40f8080f00e984400035814203140c0350022100b18405c0d6410300d900d542c03450380d0040307140c0700ba641c042d40010303117a403500d005c0c03a490b0612540017130880003d07203810220342e50070060242001c51002c0300c10707948554030042408143c3c0a0f07010201c2c4c1650000000788140d00c1d6090070311007800d40d180212070421111b240001c03001c5c00c08480030350115108200c089140d040411241c010b15189003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 81541071 1250 81539821 81539833
    0x1c0f09060537090506070504140d051905010b1f08011d0403080405010209120c03071d060402030606070b0a020909010b03040f080a03060812040518130305160f06050403020c03 77
    0x20007210b000c40c980c0070b40c0100da07108504506200c101a501105119801c40125a0b00b0715000002130015401070180703004080ca022080740c92480c042c152000040ea0000180250008a140c0ea6011891000e4102d80b19500d40b00c02840e241c850946918800c82c110340080c07460b12900b0303c00b80007041c06030006002096402d40b038025110403003c5042e001076041c03600360b42d9541c2d00e040242c0240120560680d20850b8038645d4a001c00c00015075082140c1c00f10280c1e091030395510180c0010506100300075219540440008441d0301c1c0070340c051540400040c0402d4507249165844c2c84c8050001c030b0350315540d16400b088000307281c200020454003400329891039034518205074444004044240000404141e00060b414120b64402d40055004000403811242c8282201c1540501a002801003c2c05a224400c4400b0508a0181094003a500009540550484503101160185d120244030543c00f42c6020182000a441402c001ea50300c1c003602c40090300b4181351400030b00f08249070b60101d200350b0001e = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 81542321 1250 81541071 81541111
    0x60b060307020d0c0602120403020f06012108070f0b0a0504061109060706050406060b0408030304050c010309020a1e050a080a0201030e0d0516020a0801020f0a090b07030509061c0f090605 82
    0x1031200354443e0b98200300504030020715140019100c0c1172201080846c0b15024002095000560045030410000607920681e0303d5500310312051000c120622011410303041c440c000b142e0304c1401414968060901c10301e4030403542e1114402a07009503101e44180d640c0d94200300030b00000b48100d4482d40c850060391480e010300840002c0107030040a8020781909e984002080800415500880007030540141c403d80b1290344400d5903071240c104440c1905c0e00e000d4000c41d508698424440c561104e1b0b402440841d103581424143c400001e00d900010502a40d010b034041400c0d07031100c81c04002849450007d019411982c8001016101c034105207031456840100142181900b1400380c407002d01400c0c400705142c044600000b20440c10303580c03010b403845d4070004000c40c028103050024000c00704941c41d010f5149a803040c0d41d88281c800c0380400340004000388040c0c1458a06000200240200f4901e19002c281c810091081214848902d01c0340d2140e0320000f90080000700e01405130b0040e8080c040b8501d09000e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 81543571 1250 81542321 81542323
    0x120304020a050405060d050d0c0c09050c19030f0218030c0117010506160f0309030512040e010e090a1410060b071502090612010e060925050901020304081207060b06030702 75
    0x15401030503c00d40e216000254203440f000007101d40320350000304a8100d080d6000014100401121003911015140781c00814079410070f00642e8001c0038002d41480c600744a00982d508007003070340d480c6141096101c0c2c0e92480c551041340040c0910008880c88070801704031170001c1501e0640250075003418800711010582c0c00068040089045036404d80b4250760ba1500140c0e0101a0300c08280b00070110040c0d20108024075074028008010360f40329808071000000c0128494034103000f60310a0200b20340c040703801807101c80c0709850040c1c3c10043c0841100c07080811540c03806501d280495014145a000c001444424491801040c006110344403a003450942c8640301c04a42c030061116070080150001403c1c40c0c1a15210100c41c001a0b10442c0c1c4c9501d941c40308a030401e19042a0303a614400c0a00d8000302d0340540e81e10446000d0150001e000c1c5232451702c0d94030140c44c40d4118072011419800f080c080041d02404c1484184040e00c03040c4035641e9a1225131a00c88111101180410302851060040041c0d050b0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 81544821 1250 81543571 81543589
    0x20a03030e0c060d05010801060e0c090d0227150406121407030803010f0e07110a0f050f07030b0109240303030b041b08041101020309010e0d0206040803040807060212030402 76
    0x28040c90041011850720054900d0301140401c240e801110002c0c820744050a540d01003416215144002d0041c1e50b6101400c081070304007940d4016005008002d00302c40c3e45440308602d64468030203410807810388407018075014501510980b580009104004100c2d2010b0328180b0307800c80304001c03102005200d0904110030000d41c200100100310100b0080059511082080340000459020f85065030301c1d0384403c0303541204485441110300e07404441010804c4240500e081c120010035800c001e14449031075441e035510070300300381006503054028004002d05660050003410702035806100011700c254544100c201c1112400f1401034a0000c41c1d02d403081c00041c5050b0821b0443c1d03090714000c11005480c5002800030418501078015080341b11030101191900111003602c00c0380109400403480400100590f01c070b01c982840e45001400381c10103103007545461401600c02e0307800a40800d0900d80c03141d4440d403841c0e110ba040440300d54440c0c03004100c202e0341085200c442a03070342d0040c1825070a0903400324240c0a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 81546071 1250 81544821 81544823
    0x90708010c0e01051308060408040305010c03020301050603040204050a0906052e03030f12061809030f090e0a1d0304080703150c081902090d030513170606010e1309050601050a0602010c020a 83
    0x1210000b14000250b05c40004200608080020350340c9030300f068a440ca0f2250301910007140c06500706040200024000c3c400e503070480b04060422440c540d995405c12000f000000d03c0c445100e80c1c0d0306c042101003442449924401c2c80c1801071000c9103804500807501006140002c4040280c20345d40510000e80d221940306d61140080c28510361002e000a10070015084d140c10a04404102c40c1000107504269000a500f0038020340760b4410001c585001164101c9490260041205c0d046010131061a11a4800c805a1018810b80c40f64111807e44160855100ea4014400d69100d4841802842141140c0154880704070f0010000903030315441c00303004844000c020491026600314500c4001c8840e804072403541c00014000d039001a1580340c064060342211084c1d03810040b140c070700800c02000d801200a002d0b00740708020714030340e65464011904440f44405241d00420005a00d200c00c00707030360144107c0b5900c80e80140c4819030401c002d10403000c415901403011681800e18071103205402207402d0b0401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 81547321 1250 81546071 81546077
    0x706020310080f15070503130b0910180302070b1c050402010e060d0e0c03010603170901050712030207110a050d110a17011a040c020607181706090708010c0e01 70
    0x30340d035032403004001c401c0c0641c041c840a0054540c1082c80c5540491203940d540100880000c45841d0650120f801e8002201d0782c0840c0c012420586000c2821801c00550240fa4002126a0300081d816813800741c40b00c4c44807641c03410200e011004109078041c0300610203030148490b011f042c1000e0700810045d070400140014101c035550404a000e591140e0300c55103480b030024040d41c0c0e640c0a0324055000800f00716004680714050a08054558501802284100ca4004804007c0c005400c00c0d900c40756481682001e0601404000c0000003c0c08068512481850b5460058880c003e030304011980411000030184180295032050000f5514034144540880e0000740050362070b0080b0010412101090300203040c034000340c540186001070150091900d01d482d40c03200b0426550114184001e8546103041100980c010400059400788034881c25a00f20001144210f1026070310b0305d100601c0c1c082996501100e410030410010210b10070409a801840114000c00050494013002803403580d03c00540e07410 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 81548571 1250 81547321 81547327
    0xf0602070f021503060118050d110f1504060206060a12032016050a09150605030a110310060e030706080106050c03041e0815091009061b030609060b0c03070602 70
    0x10300a40c5002041e505a001d403591514a000c041d03040310035001107942c0d50000780551300c0070034818507101c403840c00c5480207446040417061035503900441c014100303000c0e0380150742c1d8103101e4a6661a184071078400b00006c2101507550b42000c0d07000f8103040c0004d190074003c0c0e0380b01e80104031319450748000141d0b0607010b19140404000c406201070114000d502c5060039485078014043c10540345040034000c48104441091565580d0b11010094407541128103821668120040003c02c2c01800219403118810f40300080c8034413018203558a5402c03c2d0350320402800d03049028065a900700f2100d180a0030100c00a01c2002d180060041c01c1e0007050180d00700304000814000c0000b81c2c10819100a0729880550280c083c20a440101c201c030741502c942e41041c0300f80150003505008540403c0d0060b010100034200f5230381c0c0d0140704005005040310458680c0d0f0350f10252002008138a00703201d030b900520340d00480c40c141303031a0b410300644007aa0400c0d04100b0b0100145051020004105c3e106243e03c04130240c0c0f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 81549821 1250 81548571 81548573
    0x90209060706090b0106020f010902030304060f1e051c090c05060d02070203060405030a1b0308070516080c0d14040602030301050d02120a050109030f0c08091306050d110405010603090f060207 84
    0x250041490091942e0f0500030440e08001604070041e05958055007145c8030045803410361803c2e920001000394141d08100020f01c02c05100703250b005c01e2089141001405101d0040b0028410707820036480a00082c80456018a1860700080c0408210b0490100348031301d82040c0c541d4100740c0c8840c81070500c81c15001440c0d0b19414800d405544040b90014156829071400303041454030780d8840e1000d5000540c1580d0784000310700c103011105240541654030030070a03650341d400a0300c49a11249103802c646d408081001c0001d001030000304605400b900c0035200880400b00041c2080703000300807036505000705210070700c40154001305903411034001f100e2541c02e00780c09002280f101c0f81900c00b404000d0140080301740901505400120b80b03180301e0384c1c0c0e418100340301c1354080314906400000200381c03584c20441c16035280780c030400e502500c0b4101c2c3d41c00640305035100000790003031090760340840754480f0351b40c1d2140d11494107200c0d090040019040c1030021a056588207036540e11040c2c0000c142c99400300c0c00038 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 81551071 1250 81549821 81549829
    0x11706070f1209030503040614090a060b03120714060603300c060106170912070807021908070305011b090303050f090409080403051b0609040906090b0406020a080106020115090209 79
    0x1e88081c54030003c0050b070500e420b005051b684110340940c1c0d00390825600303184222520007503612540348400504a0f84c001956244041c1030000405c940c10f208201c0388015850b0f00300000d00010340700c0c520384010140401e601030304281c0c0c000e100b03c1c40b90300311a191500354484007500741891180304519145100801c6032040c034034092031441607002c4c880c050000ca001608003d1404000c1281c0d0301040d0542e850b0520103640d10981403081418070000d0203503c0004207250f024000c018401482850301c2409408070010410081c2d000001c0de034400d01c020410300c1404e2254014244910783d054220541d1000c003d00400c0c918403000b002c0010004100101c54007110a603100c0250081050010f0383c150b080c0107045806c130b40016503e50090400d1102040c40074000880d07030b640007410715420601c45ca0104001441c0e40a4151078840d00c0b852001c0010300c0d1001c0070307031107144103040040e101c01c0103803001824041c05030011025a85072001070740400b80c40c0d0248100b1140c0e148005a42d9a41c004040307 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 81552321 1250 81551071 81551087
    0x4170105160c1502040b0405010809030f070b0a09021206060f010207050a1512020a120f0e0a110f060d02071a040503030a0903200706020c010f05070602030a0902060705060a05011706070f 82
    0xc3ca004620110780828161800001802154000d1340c550707a0740d448941c20300f62a403045107a003240800c4200b1070b907000203a080c03079000d60005030340500264003105900850340d5205200c3c00c000e04c540059080140c07514207001c01e006021028402801760a0900300419000b00c40da010b46404040346600714800a4420600a0082102c4401c05d5468444980c2c0280011281d1010010b0b00760901c1c101d100c036048540714403280d0500c11401882c03421740316291103401c0c204e20012142c201c1e1a4140c40407264489200410481240c41300050351421181042c0c5000100b0071907090f002e880b142c00303110100d080001a2a00318102520001d1440f1107071506903000d0350b04c85015121401c07081801c102004010071000d0440349144c0035a4101d0403800011a5003588036460000403417010702c4014041403096002d1680500c1410740040c0007002e0340c00089450300055000c40f200c4e404401081051082ca01485005100f021911102c0300c54040d4100c3e1908401030042d01041100341108485078822079007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 81553571 1250 81552321 81552353
    0x180819030311120f041110020615060a1e030e030c061e0108060109020903010605040606020c04051f0303272601060303050703080a06051002030c010e0a17030709050a090204170105160c 81
    0x1140c01f07071030301c21000c0e40b80c3c0011682e4015041400240c8452418698100c480c00240c9a0300c1c40800c049004051170803150740e40c1036008043e580c00d41c0b641030a400300000c051010001c0000c0400303261036102906010b031003500c00c520340031480004122885001803803906441d0407420160301ca10080001c00c2c0100400d0340500d43c030604028002441c0ea40214200601d0309060341c00340300690f60005040700d0b0011010a19a807048104820000b1034803840c048105d200400c040d03074481d4070303030703801d0440c40c3c4210303071308114044011105002140e10400c503070010442c0c0c0d044005e1040c54950f40f8094028000c088020701400812400a40380740a40d41c03004000e40b40041c040018030440e44802503694025102d503100b03030740c44c040c10015440000180c1d00c0707000c1d52004c0356207a0310305c0240b00d200c01c580000d030020080c410b400c0d80102e200d959082a000c043c0c900e4903c0103841c3c2d840e0440d506140c040000d40d503401c0364507050030f00c0000444858029414030a030b0810408104035450b12140c0d014015070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 81554821 1250 81553571 81553579
    0x20721050d080610110c06070c0320011b020102072303010c02161409180f03071203060909020a0506030601050f07150c0f0203030106180819030311120f0411 69
    0x1051210a42c00c902010300491042d64a41c3c82a05030040a03980102c00800f04251a4020040d01d0746d20b25000b4010070031030303120b03d0780b040c40310355a50746000340000412514040c07203088480074829540d110348004035410a29180c07861044840d00080d450b10514010611404c01664103141d50900501d8102500c0070013400803c40085d0307403403000b915904980c500d148102002c0d000028001d4036000d030360140b094000e09050b40c60b00ca201002c0440090021480703040c2c0a449903500c8040d50900143c80070f0360040407250501e0040c2c5030010116101038200209441c6094112405622070300c1e040c0007503034016503460742e89850303440043c5d58074000c0080d106448807000070020100300418091207010b204111041c0034010070600c0a9512107510641800140d10600c01001880d109034460050103001100c86140c040c0c5518500782418004044400040e202e89a080704143d8075100c5c060710203900c002c0c07440c2023450703500080c22400b6001c1c0c81030b11106a144041824408a0003c0c2114108028 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 81556071 1250 81554821 81554833
    0xd08100b030705120f04060e01020c0705040213030c0f1503140601030e010b06160606050609010507080a0e060408030a02100b01020706030e07050d1209060509090109090309080303010b180303090102072105 90
    0x401c405c1040c4100700c4046404604110602c941c3e14014001d403141482d85c20301070140c039418141072000a4014000307a0168608401c400004501311040b2800a40080da952040d084d0608034a541e032514001d80d0305081601d41000c0c0304d00200e00d013514940110742441c4c041501200f40c84118003502c8440141544072000160748a0907881a9600a00301c030300c10001800015616003c0100c94018a00c410380460020410400050050350041c001800a401d201c01ca05041034040703000e940240d0000b0389281d00c0010b01060300b64040003c0c810032140c5040c01d01c41d482818000035202c00300d82c815501030607140c51440340264002c2c051040500b80141c2103075030301e04d4203042001003904a46034034004207072080e0000c2044d41c460320894001d0301c03000d4010401e5900c0c0c14070000040019010640c104480500c0110b104003092008600804040000f01d4803070164608440702001c60000d094400d80c800c000690070341e43c02180c2c2e0740450700105102001c0c10008400c0751a50000b406c5c0003072030f6019071 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 81557321 1250 81556071 81556081
    0xa0608040209040f0c090b0114070201050307270303050c010516091502030c0102160c061404180e0d020304090b0a18110c070801140f131509020d050604050d08100b03070512 76
    0x790344003190887c400d81e07070002c030580c25240000c0d0070711425a0281c0018010030001d03549038001c410f104521024100c401281c190b4a804851040906400c1180003400c00102e00d40b6003c001d000d003d400a4400c2c2141c4820b1200c0c079006045e14031305225208012001b41c0f1607a902600910581c1d1141109200a558515251510010000741d050703040b01c0c20749500030040b4201d803061401084c0c6448640300075190500340803120004040410342e050301d150721207410300807010081c0008090ba071a02e800542e01d540c285070320042550f04800085024182c10201048442d4280c40c002508882d070180000300d00c0160341405400b442860300b03208139481000000610500d055100c080300c2c01c11320143da02503403141c19943e00103a01c1510110311111102a000003c00c42c2c03401011080309510500180c01031a076404103e00340f620040643d540e801020420040c007405000442401381c05240c02c100320b1502e220000e0b8102543d00607031030510404400225038034050030846586480e0580c02401034580 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 81558571 1250 81557321 81557339
    0x604060f1202121f0b0d150b09010503010903050d0c02010605030d050307030b090402030309010f0306120606030501110a08040b0402060906030103110411130b07150c1d0a0608040209040f0c 83
    0x146012030080f920111014050031003c03440401d04000f122008001301204000c01c00605401740642e9808080010f4200c0060b11010701250840c409240202d128021042004417940050744924042c0e4107004003500001c2d4001c0494403c1d900c060800285291704e90070890062559800003030305071080d1114001440d80000107188101d80582d0184074408458040c400c0c00d080580c1c1c001d425a00034002e11400c0e600a10400652b03007910b00d0700040c800e648180400350319034410707026200c07a9078642081c01804400c1c0188148001440701c00e40c5464400b0a0080c011003004102030403010901c00802c0441d40c41604403066400020300a0780c03256120b003040303d103e1415130711151040b4a0680001116018681640d00031503a6401c020003062400c092121150b0120030100c800d01402d13050030420290358851004030014070740d281c503000401030a1070710340c1424071a400c0344100342d10341c020405039074800d0080c3c0e4480d0341560b03c02c07100c0e150743c50103100300142030340c000305404041003001c280689 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 81559821 1250 81558571 81558599
    0x70e210d020f010b10052b02031306060e06010912030c05010c080105041b050f0a0c050f06010510030603050303130f230c0a081b030307050d02160815010e0604060f 72
    0x7088004c100b1003074404204600c881000c4601408074400780021510030302000e81020712403d000c1c907042038035410040d209041b40d108445880c2d040c000b1100003028050035111f01c0010b400d0b011190354007805c1c80c9001034450300a0340304550514600395419020144a004107000c080d60200080c02030507480d12000d00502004d01806025904e4512250b9803a0389107a41c2d80c0d10704a4640344c0030320342006144d404005620010105051050b40050f000001d03404000f61500011180040c10265040c28200550f01c04651030740c004041c1040410700101b000801141d801410310420150307445201e01e082981031501c8840900031000500e154410b4420052418420a03c0e04041d1403588142d0410400e0829240c01210110b81c0007941617481c15403c029081c1040e88018212414202d00740d45480c5480b03404c1d0a03180041c1c01c001a0802000c00b5421580c000d4400007014040d50201c1101c0c442c1403d40511030a0b111040340c0001c0b4134141c445a0048000d0701d20442d000526640b50004100c20345 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 81561071 1250 81559821 81559843
    0x14210304030804060914010f170612060c0307030c08011401080a060506030f010609081b0f0d0c090608190b0a0510050a0306020418290102031309050907060503070e210d02 75
    0x6a40520102007c1d0303c2542c02c030080590649071204014070b004141d82010000904203504100e00304a451420001001f100b4411a158440503582c0c1c90f044800800703540284650340705204000f001480b00c0c2d0b13181b11140350340050030b10b0050100d5503203490300005400c281e441b80d60860000000d10a144d20b00f140cad07082c141e54030b6460751007007251380741c00f01c030b503140d8401d06a4010301223495100880c0d4a010329030512641c0005000c002a00450f444503402000e099115026013644c1d00b008200a5a0902c081107421101c3d6103907400c190003580f544071200c0740c0188250030f401c0e600c0e00054a5442c0744200741001d0007029080502b099100e240c404001c1d41f007030140c0441c8407040b50f03240369044140c1c014102a103031200604608045032655110070044103030681815070000b808111103e000280540004050b041804642f83c01c09400c6d281c03c11420707411000800004100300f0003466000504044e400c0c4081d241160800c1000f200e1040040851103034030180c2c0144d00000818603030018a0110003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 81562321 1250 81561071 81561089
    0x50a0f05070905090d18050a090b0325030c0b03130b100807060c020103181106070501020c010f050f060415270e01051b1201030206030919030513142103040308040609 73
    0x4406c2c0e90310900f41002640300e501d5100b5904103003071004003d660041000000b003e03003292184136140c8120455101040110540c1401901c0100103000768115010024450881030914608054204410b00702d90b010303010382000845030100301c085001c0041d44008100c00d50a0380c0c00182c0b100b200521080040b28281e0010341000c4d0001d10680808644103505a030007501000104103940900003580c01c0044281e80703a55090210100302c180c2801b6203102c20440c0d90780003407540f038484103201c0c3c06a405041c03280640d24200c508600c0e841c01d100c5542c192140c0d20f0302c0c0040b401d0072451b051080150004071502b4242040c0c1c04078080e003c1500000e0140141a07082006401c078161001b981d8090410414000400e2900400250a1810003984c1100069080c1d07081c6035014010340c0040031234002d04600295001480c892070118121030180500440051011000d10020003e140111101c80300c41032007040c0300c070620b1301f4001001114000c40d13014014079240d95603150007030881d40312440b5003000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 81563571 1250 81562321 81562337
    0x16140a03090f1418040201301a0f1e0301090b091c082703031005030d020f12030a150b03060103060501050301150e0402040b0f03041e050a0f05070905090d 68
    0xf09030504124080c18480a40040003592070700070082403030f880140c0242d040c003280c000040c0c0d038a4003801c5803402800b01c41c0220f818140f103140c4504202e40112041d141d085500a0880e20300380d4462a90f0185188201e8a90119012101001c00750200c60002a940f640c608484101044450341d4030a1161881030195a500f8840c40d407001c409800d0710180400203036403880000c42c0c1590b9800b0300c150002d409003102d141280c80180461942c3d00c01d0308c510f4054004884100042d2401700032032698440390703202600711081d603a51101d07a00d6400441300a0240004400140100560762004140d0b11107a00e800b03005c2c5079035090400441e407040d10b2060000381840e00100f095401402181d040b01d0307820041802280b0341100840d0840041c01c54503501c590200000168480c814000d05160f40510381c0031a600e04040c030f04200c151480b03160039070318480c440000c10080359012034001600ca81002c038401c1507190074680b0714107251103900201012450700b0709000781104006200240000c440d21200d00c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 81564821 1250 81563571 81563579
    0xc0c08030702090c0a14070305070b01090e0709020f19081603060303050d020c0705060c0c0a0510080c030a0212130b0702010510050f0a050d030c02180c16140a03090f 73
    0xc0c5a200d400760203900884464045180c400e92000101150103840c541b0b008104400d0700300d140d16901100d000c0d03001820214407401803100354540c1c1801098000310800c0b40202c19a90b042d01e8095070712031105480da01180180da5800d03801d0440c1d00188103001518200501070f030780170700740c1e20058070502040c000c110303048001c840c024420324041d031b901a102c103424240c074074100d00c002e5031100a07400040d0086030300c00600751300d41c007003d88800b0300040301416030346002d10203200060020b64031051041c0805010b010205401030b02c030380d0f00400070340141c0b582ea555080d10000030f4030690101551400b0a2020085c0000344d04065110b5240300350000c00041d12816003c07030986105559400f642ca64a00781040589001c05010500c0c80700076111400f0700e0755501c0020701c051525030040d004a4110712002003149001c04500b6050142000c03158a103050139840e0800c0b41c000c2491100e640c5480b80d400c10b0a0222000c02c118140080d4000c4580505292800800720f40c1c0c0c80c031070905010b841d010003103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 81566071 1250 81564821 81564823
    0xc0415020604081207050d1d011a090609070c150207060b0315071101060806130606051c0201080a0e0d0c0507050a031502030c09060705070303090e010620010b040c0c0c08 75
    0x750089800c40241030800c0008011313244480d00c054003100900a0402010b0340001041c041c0403141034142d00a2240c40100007103075800d40c2c14007002c0d00c0c2c104000400460a41d1740e51030000b9007104081d1405403171662601800d981c0044892009018035110786076007030a40c9000d03001021031300e1281e00c0c1405035010040c04d0540d2503e1038480c08003544115800a200030784038007900e03042c1c0e4000320004100c0c590703111402800e0510a454100703100c035600040000b84003007801500000c000645c0c490020025103580c101c103441c0b0180000b070402c40485c001c07039455080c6070000307a80310300128242c5682102009001e0628030303456a04071005c0c040c541e0002828130380010504100ca030050400090140d80c0040230000f50b0004000b629172074003d001104040c0ca604001e03200f010b201d0001003040e6811420702400d0603410354007019141d0307100c00051054a600c8029118441d041d0f41c090150071540d045003a001d0481c4003099a001843c0800d00d4600503401001890494090300c40c00c64401e89424803d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 81567321 1250 81566071 81566083
    0xd050703050c01090b03061210020c012304080301060e0d1a04030305101202060706020403050f030a121a0d110405070e0a050306160503040512040b0a1e120e010f050c041502 76
    0x1a40d800c5c041c0001000344c01d1401150a0300c01c00390054030165a820b080542c103d03040000d12242da0ba645400c2070131401c4000003a02a020350401c1025141e1030b1903566084584414000c1c081004510702040000e9101c6030b11406050380d0248005c0b13090b1810900b101e020304001c88023a4002414080801e080500210200c1d080c1e90042240c42c542007101d40a102c92540700c1103007118140d03030801000010400500c02c1d90f40804455000d035564095180000302640300064010000301c0c5440c40708a41d0707680131a04040210001c1c0e401e800c0e01d200904001104120319410b854005017840100141e26030f1107510781703a1803601240c0e81e0200548500c00c2c581e48180895980c1c07148120721680818540c0920040d541c0144500111801c0300c0c080103002080350417030360000e9044030f008940c500c0c03138a030814134034010100c1c05084c210032150407000040c6651304040c1000e80c040ea9650328000906002e40000e1510103100f10103121604240f82103450b04d90080c42152143c10301d041210488600c0440c40c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 81568571 1250 81567321 81567329
    0xc0c0203100902010c02060406030207021305010e040212011b080709060201020c0c0d0f0c0e06090f060a17010b0a030c030b070513050609060d05070201050f1005010915050403020d050703050c0109 86
    0x40a80e01c119280707070300061404900981c1401840701180c4016681c030f20041000d0419546c000d615a001da205116000000d4007480c11a41e040c0401441a10301c2d191080d5440b540403070701e40b0307204c500940b01503006107464a1105040000d40b884a190140c2140e06203000d400e15075280c11240c0e0f0346850403400c03800765108410040d007120302082d4041c079200101209d05c50003020b07070380000317105550b44001305400c59200115094195040104602d040b445030396014041c0d01c03031301c031040c03800320001051081c15005010030b650860880c0c0c0c17990002580540e03e10314014140150140d01c3c3e041c0b08400b102c0354071040712464018400648032501c03482c2a110200500452240c003581014204102a045641702e20f07000b01c4180401c0741124403601a039402034510f5000080e450500168105d69070500034040c4402c0c08184030304102590340402c1d4941117820340307282d41caa001401c80003194030344a15400170b980028603c0b11075040c0324003c94000c00700e83c4500304032440d0b0348801e00156400100ca00c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 81569821 1250 81568571 81568573
    0xf03050715030608060f040b0604110306040905070503190605090102040f15020a06050403050c0708060c27060a09060801080604021e04110d0204050f091312020f1f0c0c0203 76
    0x20304100d2084041400004400d1509000c035509803135203451490320700120b48280b12158080c0c03c0c0824007410300e0f511340d081710041e101440844210b480600c59488041c120300d01882d56583d41c80240101440500b001d40801000e81e540519031050b841048550100e0036222103241c4404142090380c1482220100e4410f00350040c1540d00c0d1400240b81e9000c20406003003075006451305100090803501c601849540f1078bc48294030380502d25240c1789407443d150032000c848c2d0300410501000c1d42c0003005070303000141540315500014040f03501041c1003207d0001d0340b94002c0f8010070450089500801c50000f640d01c10768807001c2c941e80e155041d0383e5a0703006850107034100d031420440d00034003048051349000311503001d040441d04086860858003258020350ba100e00703c9901080500c10341c0340040c6034840c003080c21030f0303655035a02300060074912000b42190018200c0314131078071030707040b05000b401400f0442915401344c40c40410f6200c3c0c8882034007a9602d03c020701a15040d8020501d41c09810311612451300a0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 81571071 1250 81569821 81569833
    0x60a06030c05151e03190504050c190503010204030303050f1614030411030604230a0206031f0801150501110a0b07030e0c04021305040b090420060f07060501030209010f0305 76
    0x20f0181e44542e000481c690800708000000c1d0403c10000603076080061031070712568030b19290a4003007401002c01c0300860900e082a0522000c21400600d41c03000f003804032008865038616070558040480d860348800d03010b50020030000b0070300d609984100d200d10070301c00720130b82e03140e48942081c492004100811004501d108100348116550075028590251041d03108184443c001000a85000411103040352412844111180c1040d03200034520b040c1c0d56100e00812203010254002030b980d010041100309904409002030b60704035481c3c03540720028a60003001700400c66919040514544003405150301040e031918681d5100c20001030840c65443e00b003003240241c1c0e224868120094050200c0c0e000481c4190031244200d659107100030130240d00c06004000c1c0d5545000140025940b4010805108079144000c00001c03e40c1561420b00110010034241c130240b0028000801602030310790b50b601d41440102e0703c2410445903503c030728144d0703000300d9001301585c0e03860a000709806034a010060040e0020 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 81572321 1250 81571071 81571079
    0x90f010f0f0612090305160c09110a02061902070206040306060905010b0301060c02040e0f1509010b0303160b0712060305030705060f07050904090f33020412122007030302060a06030c 80
    0x25610180e041846490060328011f0481c1d010f01800c84040c1007900d803840c0e45c41007007103450401d00c00d4840c0050f07d070100c2810041c4610b00a51a420014000d4101e05400355541c2040109507049482d00355006244179140c40e00d0341083e01c0100030300d018043c46d05180100119182e05c0741030641c1e040700d049984040410505034248409000c501180313000510801550500889060000035110540d0322400c10107490043c4000c0c0c03e544152031458020b07002000a440700c42241c800500416800c03408688517900d03030440c1126070340a00c0180800c124034001e03002c01045004802456054016001c5600f103031117550110000f400142d0b96000425010007108038241003039001000424000c81050f42c0140d01600c2d1446904c406060302199a80c04001c401c244100321001034000c0b040c030781c5013141498201100f681c02d001085c0c00152068280540515075944a0300e0103044645034070340b11400d42c411424655030f649800340000c60240c0909000103041d4200c034416141200e801101501c441850 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 81573571 1250 81572321 81572357
    0x5011707030e01060905011203091505090105071b0909051b130b060d0507020a0c060503090303040b0c0c01060b0901030b0603090601060f02160f0509070804170f09090f010f0f06 78
    0x7035102c401e8840d548407100021140340610602d4001e2221690b01002c0c61058903008152100e0340c0c0007002c011801007200d03444641d00c0010703a0841c031002c2c00e0a95031400c5500f08180c24014110400c0603800c070b801d4002c2a440c07019006050a284260200c6a443d0008840040085a48103649400c00c03100b000c905210b007081e401c41100c001000d080c2526000e114080c20064070001c403085d4000d42d0100260400700f0142a080300000c100724901075066050002c030b041e48038800a400a4401440480450003a600013401c44942100b0b10008102040e950460300c00e903500011411070200346042e10409082c1003510481b803082c8104009410b0980c01c080c0700b56400d41e2941000710452098050a0800100000c0d200015040b058580d070b003114a040700300411028018070740010044450107000008050b03c0840c0c030382038850b100382034484000c001820128080d0a25199012039100c05200d04420400b0346c150581d9945030610054540711003040c48088d500c0e100307120000d903488490100b0aa8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 81574821 1250 81573571 81573581
    0x43612020d08040204180501021b0c01020d020a060504030306270c0e0a090e1908041802120621030a03020d060602010c140306040902121c0807090614070803010806100501170703 78
    0xc1b08510503205041942c4072182240c1200d80840c502c21034031400408001801c00c0f030b0205650091008010b0b88115007030017034941c400d201c8018440717030312003004c00d003018000c1d001480035150f54604105034000310180c0001401d2160403120416281103030750a01c0034401d48804002040180c003003a01d291400c1c20060040190032000e201034014891284080403604002c0c8264a00030348c0310a4070356082821145c0c0b0011549495254248104400c04002d004184026480401102c40500041c2080c5a528688031290146041d40c0000900700307009076010b0b409803a81c1805500d04116081d04c5010603422140050780180114440084400c28200032000560317000a02038808528003043d0307404140c001994170000b040c103810039151160907007010f5802c802d061509141c10030090038a00c80241c1060b540f0b004000800c45803409008078401480c1c112051260b101152594a6a4400c10503441d100140d44200460320a1007001860b0742c4112401001420140c4200c1c3d999103500b82e068000745 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 81576071 1250 81574821 81574841
    0x80607090509190c050d0f050118050711030a0906030509030301030c0b0307030f020d020703031503020618010203070c03030801050a060503010602030d0905100c0f140301080a02043612020d08040204 87
    0x1110042003400c07061014010400b510740c0796101c1c0d41e00c6906e085506001e4a1614500411302841e08004109080300008400c002c8181000d001800751a41c060444907444100b001420910001031000019540306041e04c00301d52040c2c0d41040161100100c40da142d00c801e10010742018080031041c00305144c1c04000355040791540c10000b40795800c200d034060a982004050300f21203a800315442c1c1c203140c3c06010f500236400703468030802c03440d90035540000c20600440303400103000031202074035a100b40d00800848400c00d0b0040c205003400395880c81c00401105003402030501400340d0020010f9008d00840071749050701c510350041d600300020315803c50300a000041080e07070f8074890180c29108000b06031045500801441c0d990102c00c04100d180030f445a404401c031007001c0340d410401040001000b0840d0a21541c2c1200d010864281c3d00c1d104414160115411448400d0600c510705080001e00c40810b6105109600c41881107076064070030307603c1d108070104003004142c00a00040c01440c0030781c807900d201d03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 81577321 1250 81576071 81576091
    0x30303040b0a27031d0906010f08060d0605100614030c0403020f0f0909101a1f0917030c1504020904110102011b0c050114090a030c1a071206080607090509 68
    0xf41c900b05801100301600c1105401041c800c16840b410703c5603841c1c1c2d4071038028050b42d1144007400c1c01030000b401903800d03003c2e940410a014011270700035903440c0662410650004000e00050178000903403070001499201c5c00e404207040400b03010303524030440c055174851400c500c40b0034105842d40d02030200c0c2d9003007200c56640c000100c40c040e0300035a65680c9800c1c051010803000380340c00c1041d45c603071008460792040054402108010f040390240e49001000ca500003080511402f000c503804010b41d810003107900880100c6055107440c0780c04a4000002d48480d0a290044540130110780d14455100d0406a40282d0022014400103001c940d082811141913641880001001c844000c628821800305031701c1c03880020000d6050606000090003a0380c000c000d2400d00d02c4560900403521662000520390050900090a28090902c4801d1070b42601d0f00d07141c0300d5007071114502a800100408a001034001e44207291140c04241010b001800234468a501e40302d45072000c0c186810800b1000c0020b20007050303 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 81578571 1250 81577321 81577361
    0x40f050a0b0a050601090602031611031c08100e0408030403050c100f090b0a020a0e0d0c0e01060e011701080304061b050f030304021f050f07140105070e040605030303040b0a 76
    0x14491050581c85907210482c00192410301e03400044c040f81c1a5403180c01150300900c91003000d24420300c0124030041d03005040d030080f4000c1601003810300e01c44440502d60001c6002c141c071080c80d040b00140e07100d5804c4810940e500394a4021002090b01c05a802404000090001900090081008019140d6004101c4407508880354400e010f603880e400c41115031b940c9801e410810400440c0d171940e00085890030275402c0408800c0700400056481841910a020860080080c80a1400d22201a00444020036640d607103580d4041d000c100d004100701d000412902c10701c05011207001065050301c0c4400040d614203803070001c048407160311000170103000c8040d8001503000510108200c000880c03181c0040c40c0c69240a00401c82182521924403142013110362002400f40d03482802c0b10282c84414007800d0b10b5014500740303120359002c0707503003050425880c240a108200380c000e228110900012171b81032240a072210181500ca0200743c030300500300554400851a21070704e0303402640c91040078481401c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 81579821 1250 81578571 81578573
    0xf050f09030a0212100c030513020108040c0305070e10050d050d050d060b0301230102030a02120a03230a0609060b03130816080304050601060306060203090d0c050301060b1809040b040f050a 83
    0x45504d40a0400d64400e41c8120450b607245140c50207074600c800b08909082140b4a86071407030842101407503600904020f0144001010421a05214400b5503000411290015168003036103400800954210004071440f040001b518a44441980e1103164408060007000480c440255030355008200720f221115111000030a403980780c0340155000f8a00c240c51440f10080c1c810038000c040e2024210303a030464000300200524240c0028403180714044101146940316840e40d0114001c01440300100191076030308196040d40e440380310301c8034040e0f2000442000304503640c6c0001c000300e900324450680320b000203000088030b1a000c0e40010030118000c01c841c610341200480c0054845400c0302d000c80e100c1c400071042c401444002c2003694050301250908008107801c007000a584c134058a840030740301c0c40b580740d151410004086511b00007041d01800030300925440718504003c0384c1040e29020240445080400c5192806c441c07618007944e0015030484c05a00d60352145440c884d03008900740e07148c0c440c2d090b00074 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 81581071 1250 81579821 81579829
    0xc150a020c010e010b130501050603070c110607050a0b070504060212070c08060112060e01090809040b01090807080a03121a121c03060e1317130506040f03050d0f050f09030a02 77
    0x401d40c440403000002d0700170b18a0108044548001c2c0d841c01c030140780100502564490404a0303802c6100c5041804414030280303403d0420300e61074500741d9005080428004204040080c04070119803042407608203507030762440221141d01aa100301801a400588645944d00e00c040050414902407110214829114500d06103041c200f03901144120b040640303500c007440203070710816140c94035050091100d1742440d143d802490007040c003d24800c540d030703c03d070750031582c00380b00d002d002009184c080c0e41c1c4c00340e5a07150315070300c1d1140800285d020416141c4040180e410501c50314104c90f60050040003000012000e01c50080c00512a8040901c0b5050240100b140c8440192030051a50303900894041d0804040001141000c2c0811403030b842d668980d400000e0410300b030700b50403049010029031241c06811003041c0c4c91030280d0015400c540009001300f04940002091401d4038010342c02c50b0400e03814a0011940f04146a5020000401c1845003e6900b04044018160040000c04403200241550005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 81582321 1250 81581071 81581081
    0x70909030507060911120d050a120b0d03020105061005073504140a140307090209060d09050c0f0a030308010603111b011b020703021507021c060e120c150a020c01 71
    0x39260131240c1200d405031751408009030b910700e04806015105070116008050818010302c03d0440511000809042207261158801600200e009060006100d440e00300a40205400c0d02d510b03000b09007407011182c080c0e006a0803103001c1c603130045185094503424502c1d101e00350440c0c6c5401046440810400f2155900440030340080c099001043d80401440820043c1e0310710707a9441642e1411299860135000c2d500454140119510107801603030362800d000c0010220311a5840722203400f0702d40640c441c140b100c005050380b014001502e050b108803c90004100f01a209440f004002036090f600500149100c2d81040400500c03154095050074190556081c03000340708071031641e15a40d61145100702054007035031031503540c00300d001030000503085401240c2040b42150580086110003d150811911108001d4030344528102a03228200c203103140c601c020308101d42411030580b080517001043d519180003100c59402c4500028140a861604801550071004040e403210507802e10108200d442c081c054 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 81583571 1250 81582321 81582323
    0x412020904170a030c02070e0c0d0b060f070c0314030915090109090507080402030d030b01050706021c05070507051209010c0b0601031104060f0206010b040f05090405030d1a03010b03010e0709090305070609 90
    0x4003161030440501d0091800d0041e0303100231040d1042c0001c2c4059400c03640704030361100c5940800424007440c600007003042c5120350120880440000187c480c14012080c0c50441568800c0103403602401c0301c001296924040c02840035405042d10030030710100b80c2c00000810158074107042409809903540700c00000c4400499001e00400d9856040200314034061140180406160804200112400000a03c0d9010b4904003d2003190300041620b042202e11781c200310303081c9040c0001d100d40c2c60200c1005019800c64042140d10b41700b02001d9451030000142a20a5510180e440c0301c28601c542d11404c243c0030000e0701050506035181e101c8d420100c00700d07006001400403610307614032503a050718000385040701c141d0014442034004d00c070501284581e8003501040712411218030b201520381d410308506500c60800001000c40c6840942c228100c040380941208800881c0200400700580041c54261a503d1890464940141c40140300e01d804ca9400802050300034a0000c1c00c143c0d842c0c0d5084c003101c8041da4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 81584821 1250 81583571 81583577
    0x30604030f080604090c120614090307021e0f0103050a0b030d02030a09060201050408070215160c060306060305040b0103080c01060b0d0213080a05101a030109060e0606060412020904170a 82
    0x80101c20960308a40c0c01a00200d0940c0c003002928001d860700070880d60613021b90300d944108814003400380031303e039001a420001c0350360341c000590400454aa6030f90340142001ca01801c544c102d2200c0350110b8480080f11110050720051030050000011401803100800c0800c05580c0c030b0400210701d0300c0400c640303500801540c00030750350788916580c00f0b04003540c964001411a0704080c101700004403103109650300150f050350440c00d05100c2d506c0841243c0a00c020b07141c6400c4a40b800c19007402401c1c2e81890896585803020800661501e0048007525002c9401a1003103402400402c0040c03641d00040088600c01800040da081e01c40d80842101d501030a0008134854020498a200741c00f030038a01e400501004008000e840340f281c0d540c94a603041003010001550b0f4880300003a14a40c5030b01c8138076103840b0041c02042020042e02c0e18100600480e5502103251043c04005921420030804840a50340002021f1002c14069403c04c5000000103008955400302e1050307042e182c92400c4080c00c0134002d5a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 81586071 1250 81584821 81584837
    0xd0902041e05270304050d1103160303170609070c0c0902070807050606060715020310030c03050a0c08011802120c0603010e01150c11010c02030c0604090c0210020f09130b03060403 79
    0x385814440e42c0418402083c101c94048400507030001c12202120b0090760f103020405650705000d0464215181c8640c1c06001c2c92280001d00101d07046144c0a4071300c41d484807000c003074510040c540c00c2c000888030190084005000300700f14501400744010b60700c3c403c1d103500c1c0c07056448060351420707a00604812100d0395400700d40f000c2000b1050011a0340b0105c02daa0a038206103050303c0e0b0a80c1c6003441600300803180d5002000c1105004014981c05c040c40c0c1040c0620390066072032801c0da5460388800e0381910719480450010a0440301801600c01c3c45c0c51101615240001540030040105802c4107240400c0c450080c1003007080c1c8030380c000b95000740308003407401000758034140d880042c101c003808502c3d081080303030070740f400000b03060310f95401e50030300286440d4040354010b00c00300349046010b0002581c040d41c00300d00060021407d4211811041490f800c0e210b182812401c80b80a901500c100d00d00d100c801404080c001b410a480b40387c3c2d0040c9400c001117080110040030030309050b0161401e400142d400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 81587321 1250 81586071 81586081
    0x111f030608010608010506090105090a1118040f0c02060711071203020a0302100b01050d05060d15020301080d09050d110102070f1404050106080609180a0c0f0311150d0902041e05 78
    0x3c0c0300c0d000052001c003000b44000c0c505580090741d9a0414040d6a115120700c6002c00e0139000340d640154201000d46503485c0d950b01104441c4500d516148013154402c90402d1a03182c013220017801280c1d2020302030b40003001c00c0e40f9407201c00e46594807a225591882d2040c40d80002e01320700e5103800003000030f000b034000d00106201350900909140c481d402c1c9481950910075a002181d80c050110340001c101d000740020203841c0c900000b808070b4007800c0041c081c04046402d131480f000282d4010f5040f1020042202d55044100005850100c00c0340f10b0781e46d2040c4030008403c041400c1e240316060351300c4c051060f54510794895074151612010703074000e88144d608592104c81a414130b845041d01403c11424a8006480c05100240d050341005002d40c12452004445c0844600100030701d0384401d0f40a0b841da28419180c10107011004660b101c1030740c100a007038116031224181081c1010100c058081c4c601c1c90301c40d51100841c060507101e00120703042a6034031003000480464400b14828817600002c003151500385 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 81588571 1250 81587321 81587323
    0xf09050a0b09010c0921020a08010507080a050912090d02041107030906020c0402030c1603020705060c0a0203010b0d030203070b060102070b030405010b0909030a050a03090c0302060f03010e0f010e0103111f030608 93
    0x110b10950018040701714010300030051008000e4041701c01448046d0803400076403010410030b5160740e1120320b880d8201428014107540010101b441400701d008100107036582c181307000e6910400c204902d10380780c008202d06079150804a480c0b02c1c1c1540041c001103212181c9424440e50f6900580c8150f0005414540c01d0040300c1c3c1c140015041d80c01c1c1100c0a50039401d002110005034407501500500212a1404030001c2500030302103c2c008140c0203000740e40f21040d200c401910349180300000c034880c1d440c22554240a01c0c100407806040754055008505054442d44da092101d40e020f0174007410b520860f5400294220440000c1d44a18807410012817a04908424413a24660162040e42182c2043c40250030007907104085c2c0f00540c000c2e1501141c00841d504001c054512541c00c003940107d00066894090540d100080d41200c1d0200701c40d081c00d40da0401000d003460340a00456181850560040000c03e802c1080215840300007049082d00400024200e2031540d005884400800d403607400c200a4000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 81589821 1250 81588571 81588581
    0x3010315061509050d0c08120403020102060a060608010b07140105130204051303050a03020d02130e010303080106050909070818010903111e1c05120103051006050d05060403030f09050a0b0901 84
    0x15480b0310b1082e40e0400040640b00c4091409014000c03441c0214000074085c12120b014001d101300c4040d81c5091216a6001810b03a001d404180d0261040c44040303104210301b032013400c044805135501c0c42d035280d08003170381600c1503800003100748e8140c284a00c150948140a104880c010f002d043c250a80c3d800c43d520520090f640009c00c48080140a4103100c008603801204032082100c0c2c0342b03001640d0307207154408640240540d80158906a52180001c2440c0b4108210581a01e009480d05d03403450381c0e500012501803013002e058540150001007c2600036004204c503580041d418940481014144000301e421126419401d40c001068843d28194501050194035240e11562a4111608080c03060882d590725954041c44911500c81803d219800d1185082ea0140d000f55900102203507580e092003a681c0706aa003a0201132443e040001429140c1800e50101e120360003000340446030307030b50b441c240d0041071411110041d0585554a01d0001103040c0b00c541c1e6010303c42c004020250425900c10360860b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 81591071 1250 81589821 81589829
    0x2150d09150504020f0f12120a110703081921060905090c18100e0a0e010609020a02060a0504210801030b10061b1b1502010b060315010c06020f0301031506 68
    0x1d440c00080c880580c0740c142280c400c010060380e0036048045084003040d440e003900c128610460281000b1203001d694940028407400c107036070356604152040c0d07915841d2540007502c07004000d2081089903020310070075000d40c1040a6800d0038400c0c0c81005024005000c02c400346000c00c000d0f552100188502002841000d4004440c00000c0c1140c0080c1c3d030100d0450148000b1400d80380c07a81c0c1c400540e41c0840c0f04070440151054400d024410b041c40c00b018405000d81c400200510b50074042c1c041188403c42c4203507224520b00303500401954840f24403040c002c0c4070142c030a640c00c04000508808608840c0070195000e842d55440484561650400e41e0030240301400440112285900400004e80e02c060354210503038030784038662010b0000d86868200c0890740f4045c41607000350134000141d910151a0700c4409541250002d02c40398641c00c04000e49803000700c610b072020015a2101c031607294071a415030080107109540040c03810a00010701005a00241e00444074051000300c02c2240e5103081c01800018 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 81592321 1250 81591071 81591113
    0x30d0e0111160b0f1b0717070c06030c050f07080a0207090c02030c0610050a150309020901171c140a03020706090b0403090e010501050d180606140a0f1203050702150d09 74
    0x42c02c080300d00891096074035903000385c1d900b00491000f05100b105900c411518014031403940d50b501c09031503d4560310701140701d0135020a2800140c2e01a160256040351071072802c9680d07842c03600040e40c2d210301141e0071410340c070f000710303c954131000c2200c01c01846000010f41b0b0507002541c41c6d440d0540c00701d01d000310007404007441c446620420011500d810007170900765070f408414003084420410048000b4550a44c010354404007000000400c83c0c000001000c1c2049a642030b280407038291031241c0c1c0c1003410000740d0300c005007424154110051800e0090484040603140151510a050711001c2c1660070440c8213a030101941c0d010b06c0205604503000c0c80050989041e80c8000b50b2401001800e00d0040d4440304c0340d0701d5214138051903001d9076500c030541110f900410070449161900a020580141000744500440c026280821034000e03070071869007140d8014400b1000000030307035802c46464001400403a0040800e40151480b9455400581191035003604000b41c0c0c14441c0c1411226503243c0b44030303810340b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 81593571 1250 81592321 81592351
    0x70302100503040317010311040b040b010e1203040306091a010f08030703030902060c1006050f03070302030712020402190c060b040e060f09030f070503210603030d0e0111160b 77
    0x50311840c6a5060812040c103006440703075140c2c2401d556040120000b04405440e1070000300402c00a41ea000322a048140c404101030409075090004841c80503200e603010541004280b9000d240ca0f40c24000c00b42805020f817400e083d0303a9601d030016950010000c8840e040303a0001d41000c0000022a940140406400c803010140381402da5038032803081003400f13010507440d14500019915540200e80d0040c032a002100c00c10300c44014410000e00880c001d80e48100d0a540a082c4540350010782c0700c0607250010050316a507442c2103042e910350f039040401240c02680911480c00d040a02c11401845100c0c030f5100d003601c0044514004084407040d0b99036611a0340b03001e55034000c4800008a0075440141300d100b141c95520380300b8440340b541c0514500854040e1002481c00200308020000e40b0307000032220780c0007040b80302c0081c00c0c1088040c101c42458169109015510b405089600f1181c40f1a03c03100000411002c1512030044030751022111011a1644482840801014105036030b032100403000d00c056 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 81594821 1250 81593571 81593573
    0x8031206151e0c03042714011401080402030a05030a080f0f010e01120c0504020c0705180609040f0303060f12030f020c010906121e050f0a0c140a1803050303010f06020703 75
    0x80030541e420304a8000105241c283c03107a08104440c09401c101e10380300101c49078448101e8030920f860711219a068280740d034029000000502c05070589400c6038040c0c901284100045810601c0104149d0340342c8a56590307100400d60070700040103400c00c16a03512815180140b5091401c9102400280d14290194010840892400c03a900d065500400713030101e1040c1b0344d0508529000c0150407103580a84006900d202d10003001807110304484080d80e28003050070395241c2e00c803400725084a2140d04628508002000604089480200c543c0711b4203000440988a00c0307603061140079608128000b0081c2c042034030500d608151803907070742d0160744010020f1680c154002090500c80d8032400051051112403401e84c0348241c0c100d064100c01140b4641ca025480c040500081c000c10f85040500d88907075000b107420480c2d680520300e0429195280d0030360030350326401042865480610701b80c0810051031400200b00030440410300041d40a81e0041d612541002c49451092209a002400755800380034100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 81596071 1250 81594821 81594847
    0x507110d0203030609060d050f0606030d1103040605130305030406021f02090102070e060102010e25050d1a1e0f06031023150607030c15020405130506010203040803120615 75
    0x298406011740c4d40000c19250000410b950341d14092006020b80903035440c1c03080010740041d04510a11040f0125940c58034050401c0e68000004103107410715410400084c040d450040004000c001020102e110125940381c0b00d003400c54000d074100000582001d00140f014000e08140001400301d110b80c110328240340c4000203540ca040728854140d43c43d85100000d00d25038000e500c0b11002181403070684031041a0042c00d458648901e110710020b890305444007117881d080a4802800655018001100c5400021542901c00b000100003030f003a802803540c60f6102004454505000c3e0390074840380c0810303013440c0c0f04060400e400f000014400519200d01101a45000313800c141003580c6404003040c96845408000540d50b0000d04460380144001502d41c08040d800030b0070b108854041c8035903246207480001000280e205510030301d40d00c42003c9003016504415548480d41003901401120f141581d640d512900355040111a508551103403020030106041210a40c0f40200072012000c2c6000d81c1d0840c61 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 81597321 1250 81596071 81596077
    0x60402090d0f110301090605010f060822080d0c0c020a051c02010c020316120312020a0c0813150c0203010509011b082a0c1c0203090f01090f090507110d0203 69
    0x140040200c1c150b2181401615030310701d5512800640240814045401c0190140000707100c0c0480000380e0401c00100280b00c0c943d00750261000640d5641c1072581c492501140f00d244210039207444001300300f040b101154a100b080c882601c19220021200d03014010840702082c02e601c00d9005196880700c8901c41c540c0c1d80c64154140c0c1d42400c1c1580d02d90410700100e0314040440c1288012400c100f41d01160f04007000c0f10301c0003e14070a684240400101e135050348280d0140d900d180d004100e1506520000540e68406000c02150902004040d0f6607500c00c54040700340e030942c988020031503e500410540c2070178021141c0c00079a440003072150009400c2041c1c40506004103040030483c0380c50216003a503d1a54901c91840d40e00004003c4201d089031110550350700454502d5058807031921181506e50a2583d02210242550003850030401c2401c140f10218500c0c0400a04000050310081080c81e103511030386c03024001d0702070000354500d04880003500c100c001410786201c6034490034250014a50000071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 81598571 1250 81597321 81597323
    0x905100311040302030102030a1d07081b01020a06050f010f0b03040b180715080a0b010e030d120b030601150206220f06061715060f010203120711070b09030105060402090d 75
    0x3002458001c5001110501e0145400083d80b5500000078043d0300301c1c0079080704103003e040b1114a0b8020341840c000540e00c3c0c0f40c034816225a500007800988078840d401ea40d0311504141070040c0c41510501c2e07528107044400440d000700349440c0d101c0041c0300101d081580710000d01401c4604514508103034403816411500145012100c20b4040384035412142c050005500805c180103c1ea0090021880040d0205004940000b4060300e0b01e8000201c0790b00c42c440c00b0001c400080c002d40071074101c1f080704642441095107030b894400e440303900d00600e88e2020046a8003c2200c502c0381201c4400e440d100904104000c1e01c00e00e0101c400090b1400b460b04020244c0d01d01c16840402045040014900f550150030303079900200c1c070f16440381a005412440880c800c2010007660312282c885590704000c0000c2c0b44604034a070f81c010390007400b41896200e07a08108070303007051150030700103030000c4c01d850850b02d402925080300f05412404a9080528103090141a4101c501110f066052804100218000442e1048 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 81599821 1250 81598571 81598577
    0x11d070602030f091c050105011d01031a04020109081203040515010b0316090906091e020406052205060304080d05060105070809040c03090804080c0307090b03150702190b01090c090510 81
    0x9004c08280c0d07a4042d4890081910003040c2141513810300302030703008050901c01e03003014040000b00209502c4070012201d050700d80c041e841c1e000c03001c1c00314100c40413110001c2c0b04a0501c82c401c8004500d411042198000c1103041100090ba80e1a0524041d4201910038169a401e142c0050040c000d240a60b01a07035400310000c00c011502c40f80310002128a417040380e119604092510b140403d03c5445e80e005446084003014201039001122100f02040340b0071442924002101408811103803281185800c84040418140e641d41640f507600180e1a030b80240c40031192044001800c6007901005c0c09100d07070044090074024201212502e4005842c4640300880d84035503501c480d6160014000d41c854074819401444050f00d8a0300d44512030f41d81c007404824030744280314040002400345183d018250503520b0183c00780680310410a8441c80e04400600a042540122480303149074085101c80c841156026090426455250514040c100d510309041101045020707202400940c60320f02103160700000030700d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 81601071 1250 81599821 81599827
    0x702030d050d150609170615150d0f051f0f03080a02030c100605030c0402030606040302191d040c06021504320105040201200a0f0f06050702011d070602030f 69
    0x141d041c80202600c1c414012482c0200d01d000c034005a100c1d81700f0081ea5914106016055200d41c801aa51202120807207503035018003030310303441a0410307001ca00e01c40c01c40b600c4d604e41020003184080003602c4800b8140740307e40e40d0703880401408100f00c100c03507108007d40e00365a0509034180f18074540c40d030000d4000504110400100c040005d0f10070011681c122407048265610b40f500001032070040c000310b201d514440d1286404850407451b05108480c010300c0d006041514042c070f15401d0008000c4030354810b1340c10031141d420000710800f500040e0a540507114007480e402c0e145c103107080c5c00045800d420a008561140c00541c29140b00281d800750080e410103030f1142000b00e6041c200004480121210b0701103c84524070941030f00c01500402d0099100b40c852040944c10030811541c0030b82c0004098425910070864000800c0c0d106800010b0140100341e0302c940544e064542d40151801562103c0040c0e5642400c00280480001c0395441619a1800742029603e401d900958a000703418039040804400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 81602321 1250 81601071 81601087
    0x5060301210f0609140f07080604121404030c0513020703020a0201120b03030a020102040801050a09122a05030d0609150e18010e15090d0801030609030c020603090718020702030d05 79
    0x260000c1c5203a10503424000320015103081c10200f03c4401c24541240b184c40420303003010b1008200d0f102554808001400c1c15070300e2f6110713188820746008494041c06041506040d100000340d000304041c41c050080c10340301c1450724052061000401030421141841440040002640441ca2540c0103030246850201a41d800009030020b01100414650504c00050600e91030b0350103401410480d84100e00030401c1d5940c41d01c070380080d01c4601c64018188070580c824040d00c24060130300900c0c013154207080415034100921400d00c40c1c0c00b2101c400d03142c542c00803501d030301019403600a58008c0c1c4100030050000702c0c0116032080c0490708501446003000d0060000608144514843e81400c042c4a0028448012440c040c84d40364194101c0c51600b0841000024900d244001610f1106803031642d5032100581c0395480b00c2004100e0a80c04030304010740780d1549409a640c0c030010314060400107010b000b21901d00a00c0c03618911b081e0401c950309078014020b802c0076a40124a0482c2000c41d401d01c01da41d0010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 81603571 1250 81602321 81602333
    0x1a09030c091602070f080309060309030c010203071e0306060504170a050d050c060c04030305191101090c0617060d0f0510090b100605070506220c030803100506030121 73
    0x11400960484601030400003290101c2c400d8014015040e025102415252144800301611070300400302c00d98820131940300c0d181400001554041504002c1c2c03410905280c2c04035003668011796085000072842d580e040c00d9000c101402188640b598142040a10301e000406010350041e072090b29015541241810b09503030050143c0c8283c40e50103010340c0c0d0405070f00500500030760040d200c0c1d241a4400c0000144d503a102c86000c41d802d030303a003540f00e15007040721548070080201c0c420341c42101004290528600c0042003400741d90100d610400760315405600345200149148281c26a40f0340c89958002070003015214100c4c145940c540224102030b1a01480c2003043c900020b400181e4100c3d0b140064038024004298036440c061020004100566503440304100c2c3c86002d00000a05070341c2100300401c1c05029504000c640f00241000c1101284195481d80c1c00310310f01e964001c0c0c1300d4440000c100002400034144200140c10210b4100d41154146904030001030701803035010241c410b07c485403c0c28061 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 81604821 1250 81603571 81603583
    0x901140d02030304033c1e02061902300a022104050405150906220f020c0f0102070b04080901030b040903021c1d010e1206070903110103061a0903 64
    0x2402038101e0303a0b56a035034500310b510080c1a0400700c0322248102e06d0095030100c2d10302c80419007a0102039060f0038881c40d444d440c5400d289120f2042404a0f451002c3d4016101e0801038504001201d00100d09032641180290620080741141c144940140b4685030b50025486072040980c99246140b5413603050340c24060f031520300c0020f5580e078004070741007422000740e85420040059a10a940500c255161841004a6801100a2070360702c070403040005012420b2018480003c02c0b2202a081e01c121034114071030040301c0080050003030054000501c081c46907020031400135460010f0000f1890014036841d205404e180240008140500020f00c2d0b001a80c4240c03c000ba007040018010451090700707190280d614031020000902e1001d05002d1b0150040c060404c407a07452401101f0342003200c5086004581410b503100c11964020200d140d48c0004040800400380702e1051600c41c08607007410b50904c840094450002e441c109030a1482c103000009060585080991018030b4060310f840c1d280000a003494 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 81606071 1250 81604821 81604823
    0x111c0b03011107050c100905130b10050714060601050307051803031602040b010c08030c160b01080a1b15030c0309060e030405130203041101181505040303030608010b0901140d 77
    0x1d03080242080b00d03450a58020141076114104450381e0280e020305221824a22140810210b101c92a04101a051420292403a00b401c020300162505038a030004034920840b00c0000002003010800708100403d194030018142030b13180050845103003c0340028851302c001803d500c104117000c1208084034801040310750f001e19000342980c3c2ca540107801918141207c7c1f6034260f220702d041184918181d4000e80c00d0f8121240c202003203c0c55581c82803490881680000c001d00301c42c80c0c103128a4004103816041031400f80c04501d000d00040070941c00c00c01215030304100100c4018800c02c1e0200401e00d40c403106049020b41d070b81400321b019011140d0a8004028820010341503d01b007103501d10564001000801c01d441003200e11540c140c090003a044100d000450b0020700040000031400c2c0b481d800307803101d10890700030380021003811502c44250100241c1d8221844000c80d170041400d20406030540a604040c0807010002c01210f003012001411000b07061140703a07001d211001e84a2032a4550b0b11103a1426 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 81607321 1250 81606071 81606073
    0x60103150e090133030b091203090d1e0903020108060622060f0201060e15040902030f010b0301050a020c0d120f060b0d0c0201020c060c03130c080f010609111c0b03 72
    0x7524000c1c034824007800c100c1900c0c250001c450303084200c840c41d03210010308005280051260000781980c2d5061420b02e40039000c51807603c1416002e20511041b03c00840c4a00c40c1107000e4800d0400410380075094420b01c5c400350444410320f8a902c071041d94880300000807a030b02480e1410f019203a03d008103a003481180150743c0f400c840c0d401392404410344a2110300c1100c0165a45c03882610353311408900702d94860180c8044031210b080417070408003c018418000d000f0007400090382101039400685404015170351054165150981d00312645800c0c4100c0750310404090f410b500e440f205420030364907440842151414131480c140c1c8882c203415154411418449982c2c000c101c4d01d62915030341c42042d0000440b9000440c200100600c00a106000350342080210100804c00c40c3c03640c00e06002c0d10b41000b401190040903105410300420350120815006155240c0034041fa4900c076000d0500b51002c81d0401c0284909010307c041c00500380c601198141c001e41642c1c81c01c000303051180392001e451511509541 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 81608571 1250 81607321 81607349
    0x300804030210031401080f070608060f060a0c0605061f030c020109080412050f0f1905010e06010f0302041803020d030b060702041d1b0a050402090f100306080f0f0606010315 76
    0x20254044d0b0196603480070b008032020300703682c0e284405503580c4845500301c02c1540002c401001000d00031060950441e00041280662001c0355000c0b4519400c5220141c0024040c0342c85942480824412590000b0007034803013404490320002800040708001446104140d9240c0c08007107446e200b94480350001e42e00c030011968560399040807400040b0001d13026611401012003d0000b02c2e40080c51464000744035020740007000c03a94002e405955807619041c0c0d8603549501d514244001c0c140f100701c1c040c0500510420b50a811401804100c80c8003852125402c480340074804082900080e52100c500c0481c0340c042020400d41c004201e45000703000c2e0094000e403e10f494514107d03200c02803410340c0000c45040b900c04421200400d07010203460440300c3c0e000040d80f002401035040c9900200703450031014065800c00b812280206251400a8080d10002a5542d030203001c1960240100034a00b10280003c20188884252543e202c21024103031f43c0c140341d039620740ca06203a40b202000e0401490020785500f0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 81609821 1250 81608571 81608599
    0xe03040621110a020706030203060f19030605010305070f080d02060a020a0e030604080901031116020918030c010c1211030105062101090e0d0f05090103050c1909030b013008040302 79
    0x35004074503c01c02602401c03a0200b505403191096a01c24030004000c550041440020b2244808810841403640d00f69818080082201d9004441c02944140d000b80340329880d1001890300300d41d0503000f803402a0001102c1080c1c80c3c0c1e0000d40f107034000d0204d80d001a80e5051012050b0303010620868299014041d80c401c1109000081d00a040542c40a0702c040c4180e410f2a03600780c03079a2103111160304011010407913460240c1000403505034461070036160003d075080d10700021031540e001100100c8281e0b441d04081987e855010b40a040c1001d11068284860f443c4284200c109008c1405880d0052401041c521410442c1000200c001e041200c08105556198403002010b4044075000013401e105901e2005501c0d84601103840c0c07512200da481c6403c080003080114003415019084101c803210134003140100c6e032601c26401d0002055601c6086256281d40780001608030b0591040101d0510142200c00c40c000c101c0c0c403140051010149485800000e10b4a03410034056a0006504100e100d09504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 81611071 1250 81609821 81609851
    0xf1806050109050106090f12020d0c031113050c041205010204030804230f090c03060a0801062c09030403030c03050c030307050702040f05060f0d06061203021606030e03040621 77
    0xe4140c0380e0000c0700b481203a88594054850840c1486180d0710705040000c00c00c0360344200e03102040e8262008043d04601d5505031542540301407541c1094030360000e81d1230700408a150010803031402c8031035400c06210300c2c5000d41c1c9101c2180035910408002408141d07154042000a50403100030310b03070007180241c540c0e032a90400d603158070b00341101d491544a080d11800d00c5150130012000d42c40d200400c0c03003100307584040d50700e03610740c20142ca519040100020049081d1400780141005803c40c101c2e11020a00e4010000d480000c601c0300803003480c1840320034081c208001008a50940b0f801d4101400300304034a180c122260701c5405140c10f1f180c0804003d2040c2c540d07020005020840c0204c90038011304410440358011200d01b80e95041e4000ca0f038008800740781c101403601301e020714040e050020f00e40f5903604128162030b0f1018800c40043e0445030254007000c07044090280a0720581c6800c00c01091070f940550f5991080b401442c0030302401e2902001c4402c20f040c1e5002551041520a200c0d5600130700d06a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 81612321 1250 81611071 81611081
    0x30d030203090d020c09070c080d0903030b01030b04061d0403090e0f0118020a020a0b0903070203070314010507020736020a0309030306050f0d020d05190f050c06031303030f1806 78
    0x400b9050042c1c20108540f1880064010103100000700f28170f0582d01c0da0082a10b0043c500031003200c0100050200f144102090720415034428041c1d1004a43d042081000408817215003101c10f1040e407608100b400703258240c0c0d050701001c4183c488154116269410f00396050b8a0300c2d0b00186009803244100501003450040d554100c407142400c0c0b4403815103000c0090141d00500441d000180c2c016003106020070745030082242c20030710400c00c0d246441d4958012909140d520742090300c0c5040d90f42000e500c2c40f0800d21510340c0c8007030244041c0800b44e0a00100040c0d00000c0d024060080c1000c410310b070300f0503d940e050320140991001e4211354807000000040c000c2c051400058012a146c0706001449003001403a06503465001013a0206404160b803c00440144031034003650103200e030444254a001c3c03010411a20940907009180382381d58246881850842800e0640e40560002d10900040a46003800340d5101603040c20003150109030580380c0c000800c0c0200f0700d801544c0401303032160f044c0119070b405 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 81613571 1250 81612321 81612331
    0x90108070e011203020d080a0b1008040209060303030415051504060e061002031305040e0703080304150c050403020112050402030a1b0e09030403020f01050a35070c02060901110309030d030203 84
    0x801c144603030f80c641200403600400500a005604150f0714480c22034405c0d504194040200b800004980c0000d1020494400322400508040303040e090a0000758506520555031040b0100c2c011031031440d05580e0100c1000503c0d654040841d00c0346d004c6086240c4907101c1c4015600041c10800044c0d175505a4490b100c001610058043e115202105155920200407503020200f100c15500f000e41c81c041c1071000034a1001c00034886802490000300006008400450003513014440d1643d18041181c0240111035008a1000901c6420001040180d802400c0e003150030000030000a0180d8607400840c0c1000498280100034000d00300f00006200c54071512002501c80510324500d00d039850000c000e90364455408040d6010702d0700a0340c0600303580304a0040c00328050a180c500c080e40d403070703a14080c0b06115101854440302c40652101d42e0200d0109101d0740d00001900d066800d202150300807904622a4541413130401410301301802c030490302042228981e1601504889a401c0070500c010000d42040e94 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 81614821 1250 81613571 81613589
    0xe0d08010303120902280305030d0b01020706020d0801030818040504030f0e030708120309120301081005090a03120e01110d020414031606030c0e030f0f07120507030f1109010807 78
    0x2542030a102c03568481da41c0d940ea4090890586511b44180000001180c200c9542c801c00c0324600200002e40144084d00340e50709082070100b0703100503c000190504031241c20643c219444a2881d4a0a0380d008180a045a401201282d903401c180301d00d92080c5109090f4041d0014108005d12042590185c2560250420365481003e850401c00c20103840340c0e8140b054036415440001d100c62132711400710085811260160031074821050203607090304d00340c009900a2443d60080c0380d494401258600403107a020390000f01910490130507a5003c0d046030546140d0655075995070880301e036094400d510070589048846c1380e80d5128070414043c40041e40c82402403000c07001540b2a038083d2405d0000e020b0b0742d9100c41410200003941414012801401034150500030016042403080b02034409001c2061441c00b014040d010080c0d800d540a407a140095004880c1e62406008041c045680420341d00f06403a4400401401c1c050306040096684554800d0694004992000001c500000040500407074090301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 81616071 1250 81614821 81614837
    0xf140702060a020d12060b091203040503120d060611032208010207290105010c0b0405011e1a15120a020708040b040314061e040c080303090304050306160c0305030a0e0d08010303 78
    0x1c0400d046d0f0b43c0342d00c290f000c80e20b0140b00c4002c2d903242c502c5c8a01c0d444030748801102e003807541e01c3c5e0000f40341c2650102080d074a8080080c00c01c485040382d00030100034018030700300003c521001034602d640d00e101c4c032518008d403040800768024560300c40e00134a000409145009644564075420080314809040c0303007220325510820801100b02d000b1a80c0c0314100c0e00e050f12031a4005141e07440b000c0309017000800c2103aa556039541c000c1901100181603860340341ca60540014810441e408443c040015203030500d10540c0c005140c1d400300c650403000c603240030211002c0f0010a48905000c600a4000c0ca0801482084042008981d0b041400050000c40b800f603101e400c03c141d4498080d07905c42e0030944880c1d403030491900c120342448402d80707451504544a61307402d0703d048c4c0d5610b03420b900710f070426604450a83c000003807c001d00d2608200d01500a8800100e8040c84000302c0d8000d89440508100281070040c04000101c07847c90350707480040140700c0c000644541405202008028410034001207010603010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 81617321 1250 81616071 81616097
    0xd02011e1503030804062901020609120301061107050904061b05040501081b0702040e0304060f08010b0307030510120302150c0c0604150207060e150112030f140702060a020d 76
    0x90240d00080101070910003100c80c19900d088134507000040041c0ca06a49428184000c801813a6004407030060741010302007000c81c801c000a007401805042407981d58052011488604003110459044030003070700b040040409142051410700c51181d100d50760282886081000744070240e0000c011400f0b24174134002141140c900140c829009034094940010a0480090395504c0d0f01b1f6505023103040001c900754140403040e0b0000f8181c07100c14242407250780011404229582d000361128030032002034184483c8660408207031011a000050641d002c00d511000800e12070030901d80084042c04007681403810000303081c10f02a503500792690501c01c1408048c0002040c004c10078081d1440c8030b80b0038020f40302c1c5486944913500b17040026641210140e43c00c1005400040c1c1034442c0750140c17502034010b01400341d8281d0401d800d4500c164042d11042407010000700000368400090200300da110b003003004421440f560481901d000c0c100000750098000a408902c1540000343d28410001c40d03514030500c0000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 81618571 1250 81617321 81617381
    0xe09010b12240f0403030908270a12030c0b041103070303030522030f0c02210c03060604050f01030611070b19060b0c030904020f07060203011d0a060e0601050703020109050d0201 78
    0xb0803180080c030b00c01c03110702080000b0310039040101003d0144210504003060401540c054002c5d42c2e040110050904c03081140a081c01c4d40218001c1554503007203403011100b51405412208668801003841441c00001001c000030040500a8100e002c0e0803161044e03107a1902030010300084da03e02a036074000310484003020302c0c041c4004608a43c145e503200c0b90110303072113412b40d102d00580e0000c13607015480d00700d000f00c940b151070761286034440e0701d41c001c0111200a03410f040c01c25101030036082c00781d4104030400000c80250141241160b80c800c0c000a10794024040c0d40c080383c052008020b003140035041c207000bd41200d041600007030820120b0200060707a03540724503803402d2084005040c030a40003440081024a05030380034201401c24201d01910f464101c0d900c0400320381c0260400c18030403c40c80b244220800043c40c00c030340e21200702d500400c507e80c200b42c0310562010004041074100000003908804040c401e42003000304503070210440b184d041062030040d02031701c14030941d04404030a01540c070603a214 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 81619821 1250 81618571 81618643
    0x90415230a05130e0c0337030e0d080c060a02070501050603060108120a0309050a030221090a030f0f0b0a0b151206060702010504030c030b01090506040b01090e09010b12 74
    0x480100308100c1100750728010030244c4201c2400704018022034844d400551020b05c00714000d800d0b48490080c0c0362841c51062554801c030045031a4810350120720903400650040e0301700c00b103800211a5011602d072140340150240c890214402c686015000500c22009150380103041020701c5a07000703022560b24175080c10740c1e4520074031030f040180e448000c070714540c50b44403001013a04444030304e80072403045c8280c1c84803844c0c241410011070050303102c4003588440740300c0d0314406030041c6100000240344c000490002140441e06000140035101030a8502082201c03942d1a480700fa03030300815980c5a0300d01039140c00c00500d1010402e9000d100055460140704001e07400322604105401c5011039103807110814480d80750020101281403080802000c8040388082104500442c850036441e6030641c1040840b90554034041d01460107541448000842613130082600d04c00d035000084c00e039005688035103e25015001600c1c40d10780000c440c651030456101c2c04110003c0000b8140000052440c9217913100b48289 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 81621071 1250 81619821 81619829
    0x21605012a08150906150403050312011a0405040b061611040501090e060103120e18070e12100527030301080c010c030f080703020d110304030f080714090415230a 71
    0x100841000b120380303207401c02c1c01356000702000d80121140c101d240c81d81a92584146c0050fa01c0381c2c40401c82d00400010742c0c0e10140580025207011407110080e45e400c9030140120300074a44216180c6103403240ea511740d44156480318030f2100140300c3d60441130030507808490182035043c1c02281880008601440c85002d0305101110600040c42c45070300c5e40d01c50016060080000c041040001e004101895865007105040c01040a880400c1d42c00d1441000d00a142028100c0380030340c0c0030a010803100480414000b100c0111000042050b59485036102c080e4544251080c014250040503044d580500201441c1641d2a8000f01e0390440081401918000c980100007000070b0b116030143e030001481052207a401109500b005400d0032004007082d41074483da6203d00c0314040020040009040e4096032030854a0002e007860041c50405d00c07002414100e0610003c050000001050312046d11290300a40e00014152400180191501a03004154100d061840b503039038804645442c0300d00e01191100211 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 81622321 1250 81621071 81621091
    0x60506090a0b0318060f01060207050904020a171204090905100908040303050d0908040e07121a0d020105070b0a0b090a02040602070603050408070209040b060127050103021605012a08 80
    0x3514010b5803085541c40140750300400c02c620802400e201004028144c060030061105d40d205604090000307180050941c0104e2003003610400740030160300c80f140c3c0d0a0684104ca07815101c0c8444c840c1362146840d03450f18a400b10940f0010340000c0c00187d5030b001c80300c0d00e0300c64401c0e201c15410320580300d0300703480c1c0320a809840f00c0c400b00410000280584010b082d0205101c0c4041503c3c1e2554803403448982250b444483e10307500701c404100d00306a120041c4004040440c1c0708222100310203d4903400c081014260900520480300c0385015680a20296600254884030665140c50300ca02003c02808508045c0c0d40500d040c84042400754030240280c0702500c00690040414503d85001103019050140c8151046d001c02c10200d0050385480301002d110754001c004403800350514100040501810502d05080c4000314522100d200110090b00c1c000c070341c001d103000f680382c05408a4920a42c403d4210040c6158070b01001c8418000485903a0100341c0b018a614075442491300703c00780d0319801c00312800065 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 81623571 1250 81622321 81622339
    0xc03090402070213060801050708060603090a02040b0a08030f04170708030706090201030e0f0a150e1506120601180606090e18070503030408010b040f09050607050a020309040207030309050106050609 87
    0x6800c0a90107003005500080ca40780d18801c04a154408541c2550030201c110b075110701c01c000c50250041009a017105040d203180d40b03545400101e09407110030740e40b0000c1c451601d60a492500350303205040c10002d007605400303480d0394070880d180014181e03105209030b00c0c02a01c61040c020500d2030124440301215040c81c042d43ca81750041d5104c400501c074101049060554581002400e100100100c10100c580c0f00001c000c22506400c0c1030043c45862880d4408490410f030b00b40398495000300380100a80d078004595603540e02c9010000310f042101c030159102d540b00300c2d000000c00d00c1c010658000041c41e070700c0301003040d0350b01c5140c00c0f107003c1c0b60f50240403480304100004c240030706e518107003e44241c1c5c141c0054540c0d117a200c00002c0d046074001e5120740010ba4507200c00a0161400740314070400c0d51403088080000d01016a61161690401420380c4203101000c501d0312620350083c01280c9200e140240110b5884003030345030240007860864029183c542c645040030456040820846154400041038110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 81624821 1250 81623571 81623587
    0x6030c0117070521040b061507020904170c0718090c14010201060305030d0f0f0e06040308040510090b0708070f090b130e01030b090f010b0609060a03090b01060206090d050c03 77
    0x80c0310340c0141082041010820042060b031301042200c4131010022090a202c604107804d1007044a00c001c0c0485218030081055030703000c4860b40d4101c038890355044d1810070f960f0390b41c0d080000c50540400008001110005510300ca121008590542600c000c1d080e40c1c0c903030180818022044a0301c080c0000c000f9401c2a070184045151000410001c0f081403001280e03103910785c0da9407410350300480800700e5650b80f00e0302d0a80101116024500c41600c42e001c1c208010005080c006a884002810250900100304041000d00c001400441012120130006009011071481e1031070460703c003107505000040d0400e0216001c544100c19261104020384d44040002d400c00040344290792000f1068265060a4040020b9aa1512211500841c00b40716140400c0ca4048101d074148101240d41c1481a40b4008401c0f080d136480c3c1c001d075104441c00342d689548801040070141c00070010701ea0003030301102840d0000100c0541c0007481900c101c1c0010150340c100715618500341d65900800059000c5a0421b016041c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 81626071 1250 81624821 81624857
    0x70803180f06090406031203060602030c0c0d03090806010608270c0108070c061e0b0607030f0c0c080114060a06020703210509090901020a140a1d03010b06180906030c01 74
    0x203281c024020b000b03500c0c00d92401c00281c105c0c1c1d1164400c80d9103044144aa220b4540c1600c0350000a1900707001440c1303810743c00754405d611041e004c5480c0b0720500c20040c001e410700d8441c41d20714002d00b10040407035040b544c40300005000c80204840740f4292301c45400f40100300c0e0310b0300d0307440703190380306230b043c01010402d03510401542c7d40b2000070406010040f51414036004035080d40100041a0308844d159266000c0031140e04040e00c000c0784071540100b00400101c0c001aa00c02c43c94142c881007441c206100070114a4002c0a0f0b051681c0011610341c01d0021841003007885130314007800380d2811140c8450310fa80c0c40030181e0700c80c4a40c2c4000381210305008001104102002d0f642c918080403843c1c103e00e4001c06e100014206601910183c800303a5000c540d075400d00e6044480088c0100e4200c514901f04618500018680030132504000c603c2c1e1030401801d040c2e03880035044a0b00320903008200b51b03210400c80014142003000403403842d1050284401003031460402050301e0759411410394030001c00c050061655 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 81627321 1250 81626071 81626089
    0xa050702010209181e0106120504060b0409060f05180a030c02030106030606150315050a05040903020703051f06170c0108090a0506040804030506091c030b06090616030207080318 78
    0x620555408100d240140ea880d581054118074120702c51140c142451010304220480c19400d071604e02c5001001800025080303c422605112007400105040e0783c0c43c6004406000303042e48039030300581400d664004100494020503405800c117102005281d03182c846009480c0083d4041200035004071141c280846e121b02c80310b42005001030700100b800c940d40c0c2e031440111130040c2d10205040391040302540c040c55150140c070305081000d003403840c240c80c01c0c20009141445d69200340c902c00c0303a0fa81d464504050086c09404020b64114054444d001f4000c03e0300d10340ca40003040c0d4070b25003914011000c11001030b5650b081c040300356450010819015580019240036601804607607940c1b041c5400040000d008000551046204985061f1224034603e040c07840c2002c040e00e00150307501f0006841061602012000702c2c2c81c11103103004203070600d03440b010a10600c50144455000b40f0001a1000c240b0a51480da1000074480d6080f01c10b03d030b9545110a40328000c50038141005c020083c591400362402c2d00d02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 81628571 1250 81627321 81627331
    0x105131803021c0e0306060f1f02030306030c0d0506060d05070306091a06010813080d020c060103062f2205040504030e01020d05161b05060a020303010f0609030b0a05 73
    0x1440880244800d451400030601140141e008032940f070003003041c0110042042c405414100f9000d20f0030000240c460600504240c060644031110300200d03034039186c43c52045203001e5100140301804c900000d441ba4002ca4041e8000e104960210000c0c2c1044202500000d8000015090f2505c4840802005003018202580c0c1c07031090500110205203a80700308104188103614004011040148641481000803c0a4180410f420401141900307500c82040c0c0164081c618598840014101c90001c0c01840c0b84e2129a00c1000004000c11015502440341c100000401c44029254003480341900c06045656003410710342401034102224070340c494240301c001002e1001c3d03001d0b07454602040842e04200c3d0194001134500d0310091a03940c0501109450203d03070300e0700f245802c86003c0c43c032440850070341004145500205003e01420101c0e90440301408000304543d0740c0755001c010007941c0c1d41081c0030b940d44034210240c0c0090200e0142401904480e07100c0c0000880350798a14010b401050001c4c2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 81629821 1250 81628571 81628609
    0x909020105190e1509010219020415170f031c0902030141061804020d0c0605040e0a0204050f01030203040c09061d010504050c041203020c0a030b01140103140105 71
    0x10120b01122905600101a525a94083c0300c0071801d041003400b0662100703000a81034200089001d90340c0c0868603005050000903610342035141880860024000e40c1c07a2000314444440c808600347c0d04100300c03d646000039408449008019403456600ca20070042d00c0c500381b5a038400c01c10a0a141c1d6080186114001000001c2780d000408a9200c11000034240403400303403882c02c02c81800407001460618003c1500e0802c4120301e004d101240c005400303034840c0f00d03a0030725040000d411940e031f90b41c00c2d000c41c40c1e000340d403c10030036600c15010304036801a0055035540ca94900010b2004405842600c04039040100b0307441c1030a6010780190001e5101070000d82d21480d8022001c900025203008400040c03525020b4070303000d1404c04441c69244e240c1070704854401c0f410b1100f84501c0d140c0ca00305860654001c40e21324040948185001d0f482c11416044950704402510b4002041c40b10400b10503048600ea00046540c04003040d004400b00c41c031208109007c020450300500146c20540c1000b9000340c1070036 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 81631071 1250 81629821 81629827
    0x3140f160c050d03050103060c08040c05131506020a050d020c150304080c0f0304090b030105010509012601050a0f060803070201020a030f05210601090b030f010302061804090f0209070f05040909020105 88
    0x2450307543c1840c2d101d004640100f500c0d14010410801c545c410410320f00d225181406030f90074207a880714481381091150b1031141e28121810100042aa4018040080f100442050307555680102179140d819119050f50079000f00e0040500f158008100c030781103d00c00070110102e02d080507842c207400d5040a081a203240100380a14940e0100410034a00c1c140810300c0155100c038034002d007040680d8076050385a0b000781d040500400a039207034008494191a0780f8210540075205200d107207103421000400710050340d03003400c040c0400342c8141d500c200b400c02c505000a001f0180c54100c0360b940e81c861076000030b0059100490341c0c2d01103071140005042c0c1d01807070b01d025071902c100c50084541550a55030031904586822040c8001580c0000e0301a0080180f024600d0851508d21020b00c01000b0511010740500d0300011000440b20003640010306580c1c0060003048440000d003480803082c604600120b00a0400c400407903221402441c041d000310100303944007881d040c00d1402e684090080104106d05100d014 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 81632321 1250 81631071 81631073
    0xa0308040e04031e020604050609071a070203011503150510030b04031818150603050103020607080306040209061206040b060c030403110303040305150a15030803010e06120102180103140f160c 84
    0x10784d07113001d054050f600a01c4d260409060080c1080400b07043c068981d440800200042c501080300240d450000303454281d00c0350070b1800440c1c05000544c58603005101c0603040402000605810581480f640040421996403282d9141d41d0110a90001600c00d503400c20000380060300c40c1c2d08810170401c0c0110445c8000c0d0381d90110075012030110410039140c903200c1c41910b0703811030a41441802020300786421720255140d5004075106d40700303101015050100000004445d500d69404440c0300f46400f900450751005400e182c50b8138014103540880c4035500701081116070340b0301501a2280c9101c144080c618144c91659101448800c50070743c181c05000074400080828800c2c0054004030b41c0c01901e000c10b51400c160010212184103505041c071414540c4240007042050050320305645900034081c156442d080009110122160b214203030360340c00095002054266070700741d00c81c0c0c110281c03401c0c400c0d04003c90081d0321040080318510f004640b2000065140396003c407030304040f034000e401c100300c1c070880d5 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 81633571 1250 81632321 81632357
    0x60409020a0b07020f030d0f05030406020c1b090901090201201504060204290f0f1b010b010e06040e0601030c1103040807050108090a03081605040b0c15060a0308040e0403 75
    0x100c0d40c001c0e00e141c880443e20f003041d03040485015049801c22805000d11040c03810000e8070b8810700040d01d000b0040048001410007815504460a069890041720b1a00c4101000041220300c5282ca003401410b158010078056841401580034859058550104400070001400b050f241810907038400c910800b04524034800d001c0c801c5d58001d0f030107114096962420620f10990201a004e500482100d030f541140540a0b03001003900c014084561030a5901c1800c0d0050f103202d03000d240d03807540c2c0003107101c0c5502984c6241540030510011007038030386644841d100c10402559005600c6580c904214106c0050f0301503100303a000c1c0903401c19509003041800c40818070146190415000b6608649c4902c0060059603001121903034804103c8000380281529584c0051007501c0c0900104a140c80b220b03040c840c594040c4c81541e0282036414580c684900724480c00e0b65451034a040b05100030320314000420914188a44182c5c01e59420000b4030740b415103040d90844801c040240141c0400c4840c141007030211403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 81634821 1250 81633571 81633589
    0x212070e04060e010b07050c06030705090d03030b190f050a0303090e090a1709130903050a0e030c031002040f092009040605090708041a06010c0312020c030a0c060608010b0609040506040902 83
    0xc194505d03544031203d514140d45405001c01080b031180c1c106100304626642c0c88012a2002d03031096036081074018040c541a400342c0300c80c10361158006034801c82e144210941c08480802c5924415462803403607620024880d000c2400c0c000034001803c00181444045d00d1b04d0781c09904001d961701100c0d010303115230310355000c1b192a640c0010903481d0005090b07009458007081d2950b1f0500525000c1115031030f1039801801c140b00d02190001800380b030702d070844440d41d4140400700c28460082c00791050030b0b014441000013540b01d4020f01848003400703000802c00030003610a421410000b0100702ca46502c80c10342c00100e83d00f001c5071299001d038031103201150b5a00d070fa078550381c01280681c0f260703051030800d464410340140009031070014101c00c0b1000c0008a0380d200882c0281107406040120401e0311710f1f45000080d118000c8880e2061100050701c01c6083c2e80b2050490f03080f40a804104442e079154010103007030320258180301d0303030140c002d0014540d289480c0e0300003034205400038800560382407294085038100c6 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 81636071 1250 81634821 81634829
    0x10e0607110a060c03030b011d09040f050f030409051b07150213170c220b031002040f0611120307030e1e061b040e010e040203070306050405031c0212070e04060e01 72
    0x4d50303000100040507010f003d41e400c0701c6800d00b40409240141c143c1004026151403c140c8982080400325090042c20b820840c00f4641001c1520750002500c030701d0740c0c2e8a900c12b20886921500d0b0200141100d0019503e038070a0380304404505140c8081a04e80240742004004003c80740d40c0d0800c484205400b54801400080130100130040001d0420180321f410f0851407202c080c0182a101101003c0340c031940c46203682207030340010006c0e0450043d000b1074542400d010b00421954070004021580446d191703062011a102c1d642d5100c0f044000780c0c0c8041d1101520210b1400b80e090510110792954002d420400702c40d0903c0049071280005d004211004070500410700401d50800410701450250604c0d44c611703100d1721111058070301440c01300404032090701449007400080b02e820114046503803d0210000444e04000b0900c5039080c00d050050316984400f0745142c182458071000c40d95003001d4000d03212084a040030f61441c980d20400c0c03d41e9505882602030354065941c9101143c10101c01030868064 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 81637321 1250 81636071 81636077
    0x70815041101050711090907050604080a0b0610090e130b04030e040501090b0d020d03031404060b0f040612030c170a0806030d09030b04171b01020702041406010e0607110a06 76
    0x24202418000790800e441122a81044000c004400c04140401d803100940441030310541240d41e10303642410304044075900041e501240000b00010840c0b03000030341100460180510785050740f00d4404000c0f58410503010100130400c84035040190581340d0150303540c048507022361801030f22030640d0b81411030351007280c003103012500c0360b0425241410315104c2d4502404504404122140b0140300080c0481d1000800078403071281009880101071081d040743c081020f84020b41d80035800c00b80b40010240c220007604600807050101420110700e01800b80100300e42221402503828009521704417184891300e9401e46000c015004032000c101054401030218a920303a4403071070681055802c15007800381740f1104004110390701d10288041003c0c4844550000d41c000d5420080100a4207015014069260040b5100035010200c6c2c1c0c2c041419001000300510846003080149400d066a00c0c10312000d85801e400a541802e0120079401c0031001070810794000c0d078607a500803110170b0000c0d08030b20300e6801032800 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 81638571 1250 81637321 81637363
    0x60c0305090708070f14030c04060b030906060103050408030a0506010c05030406020d09050306010b3010030204050604091707030509040e070501090b0306060d0b13060b031611030a030c020708 84
    0x1e461000e12801019010034005001d42510745100204104800c2c01014071000302e01c400070703034582d80400491460034030103003080c07107515525928040e841d00101d4207000e076070066400007603d075031180c49050300c00da51100106041d5295022001c00a1000034074041c14072400f0310000012038800c0000d080100322540c010800c640f03900400070614035181d8012030083d80110014400c5106a00950340c40d14000f00c065a041c0201c2e690192031181015028101d881151090003811091401d00c102070324000e840a011645524082c0811500c00c80009088002c81c2d050b00c145041c4001c00814406020f85041e50a090315078002408a4140d600402404e40c0500010841c40d40c200d0200707001000c078640c659041d49007410100d8024801e00c183e54a015640314030030101a40d410040000100361080104642e41c0c40d0f15040d040c0e6401507441c0075480c184141d2801150340b16002042840800601031428503005072800c1d806803103603e00e00803d6014031071004c141d415040001c9a980c1c101c074210111 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 81639821 1250 81638571 81638581
    0x18010504061e03030807090b04090b09071e08280c140408150a0f0c030f0608031812010615020a02091605030f0702011805160b0702090103060b03010207060c0305 71
    0x440300e481c0d002ca00c030300100951107110040c00c10680d400b02e0750581046401a982c551048070303d03414039001005042804a0085801e2800e64025171801e4010b407003400a6864042c07069400c45001004c030211001200b66507080035110390156500708400c8818070304030b5a44400111550054041c4c0910490358440443c40003680c0500024a00d02000c400245861b04204c0071a4980589444101c401007150020661111699020034042503241108200c45054010700502078100f60700302541050802c4004194040d0100032282c3c450500c4620030015000301007401094003100408524079503851000180a10148408154180c2568058042c0c591544100124040080c101c42c5648400b5200310f154140c01c50122034002c1100b911980c00b59658003c05c0707000d1310808072030855180c6841d0740350701040400110381061490248d010540c55842e00700070702c0c0302e029a10001c0e601007418401040480d0b5070303501a0281e00300190015180001c686c64102c00d0300c021500c0c44000a03a0ac0040203 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 81641071 1250 81639821 81639829
    0x10f0e0a0b070e060d1802040f0902010801060206092e1b03060b040e0103061a280e090a14070305060f090f06090309041a0a030503030115020a050d050a0509180105 72
    0x6034001400c1c100b00c10b825843c4408101c81e0300403040c3d0070f00165507130300c1e540c910610303480741004070183d00070801d00c2070f03c1c20340094001420000d08101c0c045194000041004c50000c241075101d04103a03c01000c40c0101122030310361142078182410314002c1f00081e50307418043d55010f101c0c00b9070340c4041424542e20034000b0040c04c44040341d008408074201440280484101d06050a0469410034008500c003841c03d04a0f580065102c1849030340212451685c44043c401e0003d03940b0030461801021000c1980d90a08520041c4101c811594a0700403008550000b10b00824500d0407907144402c8a00c400d4480d601c042c81d201c401d54807500f00c0e003040d03c10024075140030080c08000a117504003070b001d60305040707804542d60302401c2c020034030464031151070714a21a801084072840e60801000001c10703580d6420240d0700c0c1e500c03e008403100110321124000c51107000080d00c03665944d003d00141091203040700202d406401a0245c4000c000042103290140e0342c0d0760742111031020b070b441c0b440d04035545804100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 81642321 1250 81641071 81641093
    0x90b01050a06030903020d08041e140115030b04021216080a020a0603021303060b040f0612051501060e01030207080d021c06231003061205150f04150e010f0e0a 70
    0x10b202014102003070341d00002c1e804240c0c0f104d044100d003004000c5448619001c0300c202642e003010b40140081c0801c1c08140301602030411403046121008024080d2161110060303c3c075140005010110010301060040c1060382580014640403c159440c2c043c06d04c07101d45040342071303a004050315400701554205610b0075070040303401008181000c5244c003000c0744440003c5821844050b01d029030714414a100c540703941d0460703580d40c00125000c00505031180f011242203290008103032031601c0b44070320309552124206403e80c1a1040340d1074440c490392103500110042e40c015802101c0e001d10501004614410300e0010742040383c514540400c40b401030300c24034404c5030702c1c6a001102d1803001205556103482c0c0000526041c0109940d00e0b8006184010b0540c0604503581c080b540030126822418207004e00850181000006208011340719220403048520080080c2d80c041c10035115410441101c032140c0d17221040c42030340c0078000f244010701d040b460750440740001d00302206504006594070070041c0828407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 81643571 1250 81642321 81642329
    0x1501080c0a021f0b10181505180d060606021c05040f0501180510050309120403150216120c0c0503030406052b0609020c0607020d021908070204090b01050a 68
    0x4503904000281400039960282c900300105070310707012004018680c0d5650484010b4982c0a0050052080701031707402000d81c944a601002e01c621004e001003040c1c0d00300180481d80c8442507442900308450b4040d1102c126611401140c2d200543c01c12280c00203005000d0311000386029000f918119071819403000106448450400800c481003101380700090000b00a203041d18001e2904032031b510720ba008880928110341d0007a540c8026001c20013448070b039001e0000c40c801c071203030002e9407003400004003840d4440c003079030000900b000b119504000c40844240e0240440c4c00b040d030100d01c029101e5840d4101c811118030130380c02c00603000401800070701005600180003014150011803900345880401401da014802d04148442029044c0584041650044400703d080c0002d00304401c41c1d0325189480258414014804140141c00014200c01d00100b010013000100e0303006400540100301c50521000107a00c02200d40070428410709000d030719036108903181c8a11401c1541d1055060000704040c2462541c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 81644821 1250 81643571 81643591
    0x204060b0d0b191202010c081218010912031a0909010c0e0f090a09051c02011508010c0c080901090e090a0b06030a170901030216030801180e210c0303150108 69
    0x804015081030129090b004c9842941e00144104070b1480120f50a032544640503121b00d00114007602000e00128805000700c40c550070540a514910b6030150a0b13602c182c0000d04610b00b400b4200102c1c60090704584401056007800d504810400000141e070070006607601040c03a03546500074180c03207030040d0740d0200001044031000d102042038000035281010080c000915203403036080d030004126003040504600b01100d00034240400200701d0017802440048a26050b050860300d0004440d101881440741d001c0c080d0361603c20048054988100c268003000905041000c00c040008204241c0f0030000c0c01019184013a0203420180d0402c00c11401c00036207880e1080d000101c604001901d00340d1400000d0000c02076207a2507996840042c1c0081c01038180300500c3d02c18680460081540c8510320f81d058956107080d403801c44080c042013500711448100e018801e44c1c801340b05603011f80fa2852100e40b1210114810301e25008a0200a0707045030002e495200040b05103840f00340140d82c00200c40c03540442e00306 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 81646071 1250 81644821 81644839
    0x81c0806040614040b06040503250e06030a12050405042a030209011d01020109080313060606030c140d02090d0f20090106180503070b090102070506090d0308130204060b0d0b 76
    0x1005210303c201407080241c45180c0e502091070711900c42000340d0f8010640101070342d010000503803550a008031410b000c4d028092070081c01041c840a041d0700d80380601805070042c0345800c00d80ea02c01c008000390a04500610009100c00206c9555074040d100d1401060300c61940c09181d07100c504000c0c41400c0703101710241070040c0250011640e2041c11000c010b40c07400d220009010314800103030f00412a0b44006006280c00000300903030310200282d03100b5400c0c40f8050030452a907a03007100f10100d0b4480c1910400041400042c6500800403d0260203400c20750341d0300500e080b403103600040d040410600200c502e1032804160800f4001c00c0401440b5040c58103d441401c0c5034028005060000140120800d008504165813241c010507071019014120103402c0b00e20560f103c4118204940180305030ba401031164240104140c01c1020550340082c0001e0410305c001c0340c82d990b042c2c0301b46200420301041c4ea0001c1c40e80c01c015a8440c002c1100516130284030a55403020028003c042c0c0b000103081c140280380e05 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 81647321 1250 81646071 81646079
    0x240f07031b020d17120720071a07061806060515030c0403150e0f070f051c0b06060c0a0b0712090203060105120a0206030a05090f0703030801060810081c08060406 71
    0x40c0085403d41c2e540015186081a2141c2400f0042c0c040d0b800c03040100c2008008100c5060b4101840c0401511258906d00594044c0c525240d60346241740150741c07142d0708244800135400442e2000d03003003a9106000101e0900302e040000c1d12213500e02d52003a1669a100d034420802402c003913030400072030405580a540b41d46040360440490b48550303c4000c0400e0a10680b034000076100c3e0b400806806494020303221000110521140d40f05214040c4050043c0d811800203068505028029070364038400070b4200c4a5017264545132440b140080c011a0810020084140656400e03c0806040fa1060704620098100510003c0989445081c40070442d49844600c0c2c002d6580010540d04480040740d10748041c1c04513150843c207110b01c180000f5000000401032142001d40c5800240c8a200140111181030160503035150351202517103c0a00428500e00040c0019441071019650200f85120548022665044254a020300140c03140004044042c803100b01194000300c200e4105904480910205041c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 81648571 1250 81647321 81647329
    0x130314040803070f030507022205010801020c10020c1c030e010b01110309040504020a0b0705061e0c040e040807080406051902010204150324030b010e060904030c02240f07031b02 78
    0x30900c0c00381c2130000300700c8440c00701846071044601d4590f000d807a05440308a1000305440c03070301303020b8441c2c0e410500303040010401203014402e44003690b0070500144a08040315440308002d60200607120524000c00031000307280c0b0740c40e041d4200d50102c50b80d400245440d02020260845001c240c2c601d0403c108114a80078000780002607410a060840c1d00003102d8450b440014465074065012605040000c11740e01b040c420080303000d0b0b00c200da0201a0100002d801c0200714031022040303e003820455418841440400186445168064480c0080c00d2811500d0303100c0480d00d400a5228500003880014020340c81443c00c0c1040980103007a000950429060001c804a00d141d00300c00c075010160340d46601c01080255900407601e001c01e200e61310644580b28209210402d009014100140300c200c80443d8490412000e1244595050364498510261070b501f08078020080d9a4405a91880307803003810403c0810720000c08000c100b824102c1d90b62074161070702802c2c40f21580a4045a5003a04642c0340140e1a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 81649821 1250 81648571 81648577
    0x15040b09040b100e0705040f0801050106081906231e0915030316030807080f0c030c09031614180118090804080105040c05010e0d11100203070209130314040803 70
    0x98400c031542c030942d0300c40034219515245980507415a900020138001c01c00e4100c0010f00640702040c1541480548402c00c00c2d090350b5080c0300d40400505d01c88000b0300d05000b4615401248401c84001044107955000b000340c05031141d03000800000990039100010740703021020520340805001c1d45054001c0c3c0c2c0300c00103001b50401010100a90f440072506507580c4e50600860364021840c2a05500e00e2001d4200200307480001c0720010040b030000800300300c00595003c009072050100d060424a1a41e51003841c0c0740c2500030864254251050f08251400c406920a07018090216a00400301c4c41d900c410421400d401c10030618108105540010b0103201d001005000c040080d103032000c1001c900c10301d00719280c2d10555205040c0c1d540703403100f07000c208110300944c04101c40d000d80e40c0c0031603122118104010079410303090080039494420105034039414040400700f8a0a01401034a00346141034000c079005d0b1404440c01d0000e058807808110406030004400b4043c5194190a54240f40c10074503410f5480c8 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 81651071 1250 81649821 81649823
    0x1219030302030702120d0608060c0304080f0703030212040b091216060b01050f0c0106090b0406060807080a0b100309050115061403060a1d240a030215090a060815040b0904 75
    0x160300040050a11030007000003505c1d4410ba102810b6581c0c1a036119903000b07103640e020318a064081d81d404100b030b88604000b52800b540d0002d081603d001d580e01c9a100099003d410124280b54091006422070031401c06010700c01c42c0200c150751520302d06010381038280a104e0000c3e01090000b4400c2d9840151000750840615078080c10000d02c5102200068a8502800e01d1075000c0c8003000660041880b410340210048852884040c0310548644082100341c903c0750203004001820840003d003014801d61109400801c0c0d1f400004a10a00d00049050340b0004540c00c404a529a1103242c1040000d100e1650780300240400960784a0900301c2c014003030f002100422903aa04084003165041c2d890040040082c4540764181640ca81c401a09203141d001c2220140c820412402c959903842092218802d64240300a00303881c40c1500b07550812020100c242c000c2e0030f85070070a0000301034948072014000098201c0362903030091468412048154503401180c4ca82c003a0781850741c52a110f89941d070010380c001e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 81652321 1250 81651071 81651077
    0x60305100e18010507020d0e01020c01170703152304090533010f150206042126010e0c1303030804020111060403091a0c1207050a050a03030b121903 65
    0x991242c158212940d60054941c005035407a0200344000c56400080002d0840c01c01d4840c1504041c8070001aa00c4840403070615010a036482a070441803410917907401d5120485040000b07258422151502142e00150400c0703020440034440c0150708002280c10b005800c2c000c0b1000d01042c81555122504c034102e460b0280384244542216400340d1082c1000308880404c0c0c084843c803550394865030b03882c1030f5801d03109e584454518081003100075440452641d104980012034000b00410b401c0010000306c041e5400700d000c1081115048540d66681c09104100004003c030220f02541001c1d24008003050160000c4407865080156042c41200d0f032031f03510f00300c80d014107200c00903580c1c80c00180d0301000341c61948c3d0400e0140004110400d40c0140748402130f500c42d150039240003580090050014070074280c9140d902d512640100c850059004001c0c1070030380c454825103020018a0362020310b4860301000480c00300e034490104610a0074a41030b000f07948000d02c0c0083c804c0f100f003000440c2c04142c000c2005820 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 81653571 1250 81652321 81652349
    0xf0b0307050d0206120406090309050d020a05010e1201060e070806010c150b0a030206070606030b070f081302040e0601090608010c0305010302010e0d17040e040b0115080c03040314070311010606030510 88
    0x155662402075854589048281701e80c58a050b00c1d0650007000b0042c0700724041614010003003014141440000030044c0d0140c6501301d0941440300540750b40d091700c5100d9034020403561450281d44828000ca50080c01031660030429800c00e080094007250000f001641000b60020790700b07003c00d142207820180b11090250025103002800080b81c005401504041d41040000401e9000c001450348950100c038090400700e081a10f4511084908c841c81c40744000c002100500858000e00e480e107035540705540f0040c0001503140c00c240003d400c1074400d900ca91813250b80d99001b0045c03c2c00a0280c45409540da10f4100415030440c0c0c000f8010400c110b0b00903009007030b92070310b0700100410368a401c2c0340140c0d000e0030f054407903948404004040100b11000c850001c00103000003848841c0c140402500322454445050310b80c0d901c01d0090258000070000e40c1000315080d0031000702c5503100d0013418054080e950b50f072040241d0200341c0c0d00350340c690b42c052420146404200840e400c4006000800d84041b0301c0002c030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 81654677 1106 81653571 81653573
    0x160302010609110909060301020706060e0f01060305070f031505041802011704020a031721040311060613020d0b03011103010e090f030706020901170106080a0f0b0307050d 75
    0xf1140000e022039035103490140032913079100c40058001030620010340c66940507902c0c00d5015269001c00d140074400a101c08410a50250200341011f00c0130703042811004241c942c0074100300d401c15079030f660000c00407500c0758200001844002d0081c81102c0c0000303440041421400c50890200300820309204080c0c2141a200e44120340003001c01b01c10500d980c454064804c80c005240044a1040084031007044050101a03c000711400b010f00080c60302c4d250140418488181d031081903440700d41080700942d12410600c490009440700984c88100000e900300180c10100d9041d58103500b4021400580680440a54100c0344001d02c21a410386400180d20340328154080950959041041032a0104031150010240c804c01803615000b0030b001440d19001a034800e03000b1400003140308060240e014843c0c0100d4007890040d141c02c0200c15048000260303210307030f5407107820b005032003d21300300d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 81474821 81654677 := by
  have h0 := BRFrame.cov_init 81474821
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 81474821 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 81474821 ≤ n) (h2 : n < 81654677) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
