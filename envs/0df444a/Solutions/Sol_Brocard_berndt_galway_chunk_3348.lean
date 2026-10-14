-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3348
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:24:06.839874+00:00
-- url     : https://prove2.me/submissions/85eb8e13-b711-4b95-896e-b59b203a2bf3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 601978417 ≤ n < 602158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 601979667 1250 601978417 601978511
    0x140313061407150e011e0b030303100b0a0207092c1204090c0c050a03050a020d0323090a14010c12110a0806010c0c0305061801150522 59
    0x21040601c8429141954a480e011140d100d501298502075490384121190382d1130038054034070085282c04008103d151449480301c1500d104501d000d00940c070904c10040d508203012802c1c0111781d03150481966602500008a00704249500b0035481700742008608040196030100481004a00403103003050355a01c0704d2002c0d1540380103040d1010b8164144400d0001141c02d60008019640500b407903c43e1044d140d03607a03401c00f03040e0790058002c1000801d2040501c1d4050251240c0e0b021107103070401c01400c01c0b02c3e060081050300400700e580540d5100006600d02d604014120380980c1010fa0030720600210742c0924040d0200358101c1c00015900710481000c200c05024a049001c4004211420a03998010031030303620000901803810001c24070380c030380013180c0c1c10300c0900050350044000c0c08842c503201c03155240c3c110021400418582c0f410b0313010074890951260500503108100c0c1d00b1486003075100c45c041c58640d903c281c001462841c0081014081d139602c1861951120041b0b020101901650b201047d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 601980917 1250 601979667 601979687
    0x310062907020117100f08011d060c071101031e050103060c0f0e09040512040303050409051320040b0a090504060b010c1703040602190302090a08030309071e0314031306 74
    0x1010440c200c807844c41000344048443c1e4488031415581c0e206036960300e00e030003012002e07a2081d1200e07556066203100124413030f0429290311160f00010107442c18104400045481154005401000f800c1c05850180c3e02c680c02c054248113290031f49010f030b03121051441c4000c10302840222000f81c40d166a000c200e501485036020b4403100ea0700c0d64400680700da42400701903000104112103501600609458150000d00907202031b5009661b880d84441c285107041c0108c80c4003402481c100301224142c00000b840d505a00419000340c002d80f000a10034180105011b002d880c48150340c060740703074000401c00e804650300191003203000701c2041c00710740c02050054410321883c000280c804280c101300c0007070b83c46600c801160410f12407200149084120581101c219428500c0000000e4000454084074505041900c000d4007407000590326505280c803d0f10b941c0d42c403d20581c1b0f020320b400b080540c42c4042c40481d400040d500140780c030340c55603507200c2a682caa5100151950042607244070114201d48240300c442 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 601982167 1250 601980917 601980919
    0xe060706021606020307050c060919030f11030406030213050f0f09070c0f24050c030601110307060609021c0614090402060702150309011a0904060b031006290702 71
    0xa242608544035000a58494642810300007020211200020f910b88015403041c100b507501d19490750340c0b0440c000d08040c1301078036050190703000d403161003001d65680e50403a030041d0f850b04026079100100001600c844402e030380750007003a000110340000c5254240d001007001451030f070800d58181c2c1d2584100652043c284078069008060052100c590303007000002a508010340d4240151a4002951001c00e82c103103010080361411782c448840d01d4010408054030140107000501030003146800a19000f65000080c01d4504100f9410240031001d10140103e41d00306420103003d00c4065142c10500010354084407a28580449841200c280140c6070312a4400707a81c500c94240c205032190400f004481e010180c01a607009408019140c0181d4540110624890389006000e8880c50040c81c690b0071503016840f032801d030812100d0440c401c0e5442c00100d5a000750700034000101c00f0b686101091030441d01403400e90510b0316080d0040f0340c2c24868020407801401c80c1c8420340b0b1074008805000b034a800354010003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 601983417 1250 601982167 601982179
    0x91008010f060f2904030c03060b01080411090c090307030b1816030828080a1503051e1c0903050c06090913020f04020a1d090f0703020c0c0901150306060e 68
    0x144800e0611014030100080341040e03804ca0b243c0a0300341648280e00646c01183d01003c403078010000c0098602514038003c00034205500b061600703464006040c2d000500461180b02124001600d900070901a6a40b0817000780468030301903142d1401041d1108103561466000c0159517040010780703000a2904d8460185001d2080c200389195102d10f6181c0200c0d2240c0b0191041281e8011502c070130140c0d24880b0381056407441c1d1581080f4800a007181c45807403c00018095061041c40821000103020141e6001c145581a1605040110710f040180c11820035844400410145500740c1c0d000c011070703040c0c90080c001c0e10050910380d000c0205a2040e1614a070708080103400043c2005210080b086c006070016000c80810020075000608981c0300007900070101d0b918000c03890803505003030490000305d48259130381d1f02c65060513915040e0b02c2d40001d01443c101600001c120312030540034003503900390b02d9000e45541c4141d40c4a450060304901582580c1000030318180300054a01e108100001d501c12010300a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 601984667 1250 601983417 601983419
    0x4030b0903070c0e1312031401090b0f060d0e0307230718020706060302030d03021c05060114070821070206070f0504170a05060103080306130606021b010e091008010f060f 75
    0x7190b8480ca001070030f070b1203003003000c0b1506170210700c610802d41c585001690b0006615040364050b20305230001030700080801847c00d450440152118444003050010490305907498003d80b405c00f1001c0c16080505c41f201c1e0101043d270100300030000700d4a0390101160114121044d82068016039100058030442d00001400451080d03800d6280d8001c04072035010701400700d100794994021a2820080101070000a03030300140e18031901b2801001c2103d806e50782d1138180154100000000c01d0114803020b80481d4040004d420030802c809242166a40d902c1d80401407441c0b68080312000b00058125602c0f800b50040c2c000188926214a854034400001c94982a09003400c0058903c5441c0f008403188819106498000012990820089000f076103d000c00568078070344402441040c00e500c44e03010700c21a06180040c070a540e004541c604001d0b02c041350102d4101c107030800481d500d40011505a030012800c0b070900c0302c20701c1d090141e603082d540c40400074401342c5152984002100c125104011054040da90 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 601985917 1250 601984667 601984679
    0x601080f0a060c0516031223040303021b0703030507200a030b0c130b0c160311040b1c050c0102190b1603020c070611062d040203070909060204030b0903070c 69
    0xc0f0581e078021180c03501c03034180001d45807244c40c003194a240a03404183e0403020842d6000b018007501400d28100006109016281c0c8410b9005003000342008081c142c004c503054051a11400c03052800801e210211400581d40341000351455215503001d9540c26900281e580700c10000200c40003440c070002d4100c050441c030b50746070f03ca0000d00161480141c1c6c84104146901a0003814115010303004030f814103640d035408902018078210726040c0c00c4803441c500c02c90800201e4000303a040d860040c002d40740401c00c9084480055110140120400300300d40c021065503052200002d0301c80c03a0b601007038085078020002d403190075501501d002030041c00405200c0000704001a03880d10290b43c02003034100135090400b4000c403030741801160740000000444100c1e9a04040c5020842c81d5084241c40300301003400404000c22108810351414410341300e035606000316013192020050381e001003e200b88101314091040c90014040d52141c4400e46041d080340020545c1039502200302c907503641c0e100c0c0059100e80d207016 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 601987167 1250 601985917 601985921
    0x80f0411060c03070302070f06020d0906081b0c0309040b0a1406070c08010905061f0b0412051f0f14070f0815060a0906080a11180616080406020601080f0a06 69
    0xe403600c1c0e0804814841e800341210208068400da45c440c0e0007405c1380314100500e401214025500010840d8816007003c00015080080c1d0410b4501c00d29042d203a6503201c0b00d01640c030324444911744581450011f200b0080301d5010015000040c01110140000e0b1410303403c200700000203016100c2e110010940252042c50202d004045e51842503502c4e00219949051160844107941010350341c94111004001c00c10314545100e00042c8005909040c60303030709010020101e8012405030365020402082070a00b884401c004ca01d042c990700500d220380031852202031038040d01600d2f003884881418411081a02c054005149110341a00e80d1105000c030101e81c42240c5e1410040e109030641484034000c0005522602e004011008035511200c0c85c0c03500d00100104111002004c5e841d00c2441c0400b981c3c84800c0b4481120390646110081404004002000a515125080c4104a603001d049803070380400600e600600101e03000b0f5001d80c0d1035030780c2c7c400030030361210400102d01440d03420510311100052401e03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 601988417 1250 601987167 601987193
    0x6040c171609030b011403100e06010e0405011b030615140a032703081819080d0b03060a0b0916210b0409060509190b041112100c0f080f04 61
    0x140781040741c05550752121041c00800386c101000d01080c0003800e0b615400d0420032000c1c02c4510030700c10400003540c00109a241c24041c001c0c410303c000000e01003003e100d800d420210103076400398800c0005031303243c2c40c000d40100028410401000d02a20759080c0e401c2c0221608240c25440108440c5041d01c072035000c80c001c1120b02010390648040350007840c4641030000305400f25501c66241c2c05428200342043c164284106040c00d1102d50040000c50844038200d0340005110750300c03240207610350119440c6503018005000d210b54241c89500f00300844001c543d00803002c8204107541220480e107420001d50050030b400c6034000c01085046500c0100c040003899980058481d1510004105a014000500761842b010041d105035032201c0520445a005000002040d220305602040e81d180c00e46da4000001c0700240054140400c0a45000301030315800c54400b064115101950b8080c0e6106403040001c10340e0301c1045001960460800c003001c0e014148050080c2c222401e40300a907550b9a903240b8a14483c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 601989667 1250 601988417 601988461
    0x6091f020318060109020a0818100c110a0c0e18120901020c0a0308030a0b100e0603090106211a01050112090f060f06050f1504120807020d0b06040c17 66
    0x401030300d0380b000307007051000c00c0c080c01d5103220150b0307108a80c1c40000c1c004007014201a079030040c2031040b800c140b040040c03d500801401680410080c0000c0d1050300c040354250403168150140c51004401c000c0d110030f035403059454154a0040a4546404c5c0742021441c201510185a2051109403542c40424001d05a40c020501c101c400d403001b141c002c90b4510880364021140807801105004005140d4000e081c10854141c40403540a000c0043c028030034458a803c00c0c1c0207000000c04140d800c0820b40007140a003110010401500342c003001402908908240242d82d80b01c807003036001443ca030030b0210103412100c0c16551248101140c1403440010544020b0403210140c1043c0c1100005600d03000340d11003020300a800282e014502820b00241c43c0c1c0a039520742c403c030f64090001403a0700882c800e403410755103985e80f6151031001c90700d48030f40b2912500a02940c0710307804003115000c00c000181914415102a1028005140c4552056450f0080d01020070108204080080d02c600e1658507102c600d001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 601990917 1250 601989667 601989691
    0x2010810091107112b15050c03190e030405060322120e010504030209040b040503120f01150c0b07030b15040b03010306051b0403060906020d1a0306091f0203 69
    0x581c4100080403541d4101c902901e400e404601c510610003e168102590001a1240924030745020510942c034100c450104100c156002c0f1040d0070300100c030741c100f070100d4078102040145007000c01070000745070401c42d100c0714920b4803205031420010031401100380b4003282c04021405d107810f220811945410050908183e06011a080ba0805440c2c011000c1c0a078000d00705441b001040c2907008006401100c40a13040c0030017048100700503220700303858960080c4c205003e851242c4561405500b58440ca07031644e40c2c02910241441103141c20b030f54142c0d0484e020580348051465a1286c15104d0b1303a644000501040c50380743c00111940e01a401c01100420700900c4442c26120400041045030059004042c00c108084018070401c449845000d03080039000d0352540c4000002401c0e400c1030b103d039020042c1059142d06c494410000180c041c6d5a070901d00318401e0000d200c400740050182d000c400e10300c503c00e1240401281c241c2c4000f0903141c010503510f507450a440c01c09441420080e5101510301e2001003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 601992167 1250 601990917 601990919
    0x9040c030f1b030c090605180102031201090f050711031611130906054b010806070210112703060910110f07030305040f050f0c0312030106090302010810 67
    0x2411849240c1c0d070307168440b40a0b942c00e001014020f040b640c80b28040e00034410080c0c401d000355034001c000d80c3e00c02030581070090118450200101e080d4043d01d545000189000c20010030520b82e15007000c4002802c0c80d40c100708a5490010480d132007050b015100303c0d142c004005804030182c00c401e2400895000d552503061180020010a82d41c00c1c4501e00c01d100d065846806a04002e0305e40107190300103140504d2001c18000100035103007080007090000c5031400200e50300c80380c04000041480984556811031000540e541c940c005d4565504445800043c040c031110001041c000d0312502000b42d105481a0b03040c80f40300038060f0009154454004044190f211100206540421400b8410300c1c1c200003401d40989000d00280545a103525800040308044c02511410b000e0582583c6103d82c046c5004100b03903c1f10306149010714003804000d441e0780210ba40948d1a03110000300440c0301481a0103e8020095070b0511150501081c0a1400002c4250400300050340c070642803190482520020281b4907 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 601993417 1250 601992167 601992191
    0x2060708122202101d031b1c050613051c030b030d03050c16060605030a0507030203120304032c3604050a060c0212030a14060603040b061003020c060901020403110d0809040c03 77
    0x2030940c000800102217000100c0c2c0b0900b0158066000700f88c1900301051440401c4c1d40d644d03202c95000f03120b0b44e11a4102c223601303018000104008003412001c00c0200e10751068011004000d003e80d00362041c024450220303258401c52180c4503441c4150005107025041a644404404000c00d00450a40c0c0f01d5807910000b003500e64045c0f069414a5101c0d10050000c9881d51050504103410508105182c400502c01c01004ca50014803080080c54505030207084445501e0a5002000100c682c0d103400a094075000a100c2e4807590345c1d15108000486c22801c200380d1014000c4403140116002499a000300c00b403940007a803150042c0c1c003240360600513a80b14070480c003208140380e00220ba00c00c2c043c603119107880c02492000d00300e440e086002a0751042c80d61600d0b8660000d03091018000e10b016400200111480034440e82c1074032078201591050355842d003011047c50307010b900240801d581520040038507556a103070403030b07460701030340d0f440783c03030707907043ca0071107000c01009100405200c4181a1502d41e48640 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 601994667 1250 601993417 601993423
    0x16050c100501140a0e0108121303051e1006060c0b0a090f0c0603181211030405060f030105150412110a0e16030c050c1902060708122202101d03 63
    0x81d12070014000903c91610081001d6902d03554003101c000c02c00741c0014050b0000216030410b0389505525125940c8604121001d08038100e980050044d018a180344907644400f00f0402001401c1c200440c3d84a050b240c2400d0200c403241d06c24440400d030381c100b00000298440d4900c6511009003000005d1140c20341e20341c0d07031070039001a03011a155200f1400a110058240c480da8021500d801c1c812500350900b545c400104000000c1300409119402d0841c1c4c0b48107004208a0300038103030150000c0d803a01400024026aa0001e0098502c00c82505074080414040c040644007101d510040264174901151115584034070b00150142d0130426216003c01c00c0404005841d0017000e8460300319403c14580100241100d00b52f034584010000300700100340140030f00048886080c0010034414050003110301c0000c4403031045a030000d00380f42010440020100d1000703890307031041500c00441400c8045070200b8030f00b110616040254401c4110140050862041080c45000c00d800d0381441c011031000c1c400a0310b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 601995917 1250 601994667 601994669
    0x20d080d0203070c2618040b100e040e030304082502030106030b1f0f180902090703410a020c0a05070f0f05060d0b28050a060816050c100501 62
    0x7058619510380104481c10072010b0b5420f05003901410017040020222400344200c0200046500b00c03007030301e1400c3e6521507010091003a8014410000b0424442d0050700c1c20300321040c000e00ca14680034240100319000300880380f10316449034081e0b15210000e50f6440326010440241c980d071030901e42151005031024403441000c0c50051480e80242d1401c2c480c024815203100a50304004030803080c01f08001c4101642300300c16500c002c60a402080307400425a4001c051004011303510498010074000700d03a4043d4056032801c048104225111030b001070581003680c1e10610a88803100300d20390181d032011f20b134003545c03138104540080c00b624180300c4260381d9107401004542920b07160018042048003600100019000344a45c0303c900f0005840c1600207605401800003010b1541d80b100400f1304a5540c07a40c000180440104108812010002120000701d00307500665004a100c5403001c160700e801000c07098440e0b110042404c0d10543c007510300300ca044e044410988003030b01c070b00409141e0114403409801c1c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 601997167 1250 601995917 601995931
    0x305061305340603022802030708030c031812070209040c08031b07050a21020d020607110906010c02091801020c030406030e0c040b060409050402060f160302011512020d080d0203 78
    0x901c20510b88201c203481d060350104061500c104143c080789070a660a580294612446069480b04072140036421803180c82d030010321503800017007000584086840910b005400741c203410307124400714024140e9116429910050600801c0c00303048018901030b05881e40c000d2207034541f04440c0781d03591203541ca5034001e000350300c920781a0000c07030f040701c880e082068030010b0004842d0a400903280c505030b00040e01d4200d0b0081c05020824030154290f4450900340c4002c0b41e0b010300700c59603031142c90070b02400c54902e20311018401c0c1001c0d00451402d40c0304410031207000b60003c203108495280c541640c0b12003020200145040d54007030090710b00888080c0098801003529460220302640301c0700440d03003040c001c0380990303200317030b250040c10512a110007081e80d082e01d1405800190b00e44942c000203d0b0b0b03000d004601450f415001880003030002030014450035241c0b2940091001c0f0300e0038079000c043ca41150050160000550034032030007515040c0f04010701ca47c000c100c05850040c003403c3c10000da0340200d03216 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 601998417 1250 601997167 601997233
    0x1030f0f1a0f1e0402090a0609060306120c060e0d020405150108010e010e010b0a03020c0a0606030201030b030a03050f0706090501090309060206070e06031504180606050f0102070305061305 83
    0x3512001e8002103903509841280c1002da142d8140d4006844001c2c1d842c04000403902d01d440b14081c035200c40d41100e40e2a400142007801c000d6480800500404060240300c00081c2465000545900b00c00d61911503140e10400450000d81001c004441c0743c8822070704a94400f60105145002d80c50314481d242c01401c007203110000c041031510000d0104841a44030034040314400004004c0d0013a5070300414159114411900e540349002c031001ca002e8010700215001c5400303001d610104104041d8040c40449100b0389091003c20b607503504042c1c85d0402c5040c049c003c140204907107001010402d00400c801c0e4812240014032203403640b6258210365880508602162aa40091102540411032a03902c07101500c1d18107030710380441e80880c9031800042c10b820304941808211000782c1d52241c104031440b11400e241000380040390304298000d000e941c420680612000455104154408248041500c0d0000010200c0c1d40394040c0c9541c09003180802695280140041c0d1000c0199141d6900203190319075100c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 601999667 1250 601998417 601998431
    0x9030b0603163c060e1305010f051e09010501050f0f070f1106031e040c18050106030e0c010e09060301060b07060e060115020c01030525020703110306190b01030f0f 72
    0xc000c0343c9200d11031002000300c2c07550b807149108080c0076a040d001d41c3c020b4a04145082c60342d0001c19107601203c418219030b02e04010022035808503020740c070012a04100c0c2d80d03506641544001c1172107290007000c0301c0e8000e041000144400d5020f04000c050f0729940865580c903000c03800411071400d0300013400803119203c0c8000c000d0f090105860745440c84110480b404c1d403450a00d41803070704800b084100012142ca001c5400a0180054803201c00e00504107001a91205000ea501010040409000e404e011070315160300b18001303100014000c4000101038540029042c1d1080800848000082182d039040d900c40e0b0b401b040c50005000074000d0a489039001048918250320f54500301356050300305c2c0000c14540801c0060450740041c50f980a01002c2c2000101c039124001f1902805210030520003449803150f03c44440c0e154005031050480c0d00400c040404008024100341e113038002a210342d804012085d10103400e107030040c2c1c44000030600504000a85151400d6001d0986680c0045c40000360383c1c2c0c040c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 602000917 1250 601999667 601999709
    0x506061b0a11011407060902030102070606060c14070f0501080402030a0821060d0c0519030203070b040e09061006110a050d1d030105061003090314030c070c0b070309030b060316 78
    0x88000b0320850242448890809001c00501440c007030f001c0054403058aa07880c1c0d6056403400e42c1200c003840d41003a42031016903207031038000c0c00c00648103004031201d0b0164494a4810315010490500380c900d041c0c44801c00d10b240a00440b8001400781017a68940101001000001c001000a03c5070206140342e0318491034417025000749000005100d58000d40c2d5407000d82c0d00040c1a04000740689500702c4014280c01d400d0f812048514540d80c03c000d400d4481c015000c00e030a43c1d40406041200c2d40c554459007542c0c1c40440450300c0d4041070700c6201c01426115024440d0900680e140401c024050b01122043d0401e600c41c140f6040c1a42c156401007240c081411406004c400b018041c10700341580280103d05007903004c1514900c03280c80f80010035641d01c403580101031040d11403c521140e030071043c5450b41888401424180d0100800316091070b00c00d500040c1402c100340c15a010960149c540508051071038440da00c1d01523008001329414040d200c15074000c20b01c0643c480c0c010f82114109580c007000401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 602002167 1250 602000917 602000933
    0xf020609010e060a02070312110c1006080d0f11010f0b1f17060a030b040809012601030209043306060c0804050d1a040305032410030506061b0a 63
    0x902026240d0b41811040c0d061030400088650b013040c446000103a1360426814122100c0241a246200850070000303086048078181c0050b203a0074090702e05032000e000c401000401100c0b241c3c070500041e03801c0100c2c000741890148102d40c43c60b0b9440e0400c8040d141031086010b00315a010001c140380c466545c0e0103546942030200000c20300e080b45d10090710080e100c6000241c51035440342118a40035500000244881d100c00c9480070040d03601041078081c904051401003c13030b810520b00d01d0700080c09641488032007a40c240700d10060900802c00152541d003107070248030418034001c005440341854040003055007000410396500f43e80b00500c0d0810402224002417041d11601d41c4000e08001920350305c2c5004c500520100e40032264100e451194000031403910f900c803c07082c900001016440c810800042c15001001148a46580328503103080011600194030500821130840e03801079080c031641100c5500039404250499402015a41081d6001050200d0400066000070050b0030040034034040083e41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 602003417 1250 602002167 602002171
    0x303020d03020c100f1508012403030819180312061a0a051b0115080c1807030902032107030e0307031a041b0b09030c1f0315090c0f0206 60
    0x141c50154549003001d80d2080d598141500340c16142070b03645001d540b81c000c00b540854040100900ca205803142d480721524001e00f6400190f020f180136925441c0b001c03266503c09403080d00d6041d11031804079203030f0b003a020790346d501c0c6d18240080040e640d06894840443c400c250007401e41c841d0f86c030039080f0224042100d00f910415400000f001c1030040b0202c12400449058a16800c0c881c0340c02ca46803025504041000d0005041500c0503503e0a201c100b004202c00014400740c1d80014221015000701d00300380001c48140c001c0d07103041d60310b8960110301920300c26085516502d0005080b07900f40c0c40c081e4003000040f40c002406c0012000000340640405401c403250b1407402200b03c02502c80d19107552103042c00e40324205c0801025400010010702080349041c140225000c0300e00d01301180f0343e1610b0009400d54840d0783c11354400d225101d2a14004d19000e04031285554064031001c07040e42c00707403105902808080404c2000d4034000c01d8042040c1c040741c80b4010001100703a840b02d00e0400500000380c1400700c0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 602004667 1250 602003417 602003443
    0x102220609061d0405101502070e181e0a020a080a030503180c0a18140c0d0e0f1603140615100302160c0e092b050910030609050c161205070516030302 66
    0x4204c0e8200032b03145102c0c404aa000001c405041a580070070211141411001001001c5c403401e10070381c00c0c500c1400090306149191003903801d00011502c0d8040ba17641c503003005034000c00080f0100700084840740910b041d2440d542c8041d003207408170ba4215001504101c5160070512032560030741000082122107000344000300a681121100b1800d026484e040300d8032400001c40b08403621080c0d502801c001c20070010126412000c20381e100030a00e10a850f031045054481a07072400b03041c982c03075100d844020540f280500510343e10001206d844606004c11000310845100034036900780000300c4c00180b248000565540f1540000788680d052805030081e48101030331058044c1e002103517004556600c03141c01d501d0451078400c884130218100b88121800c1c4603960607540c000c0c24400510701d83c00d030150410300a4950401c2d040c09240d580034410012801542c8900c940215034074070900100d01c10001c00a03102c13086242c42841c041840d12014074140e1906101c417aa008164420010f166042c400d550180384 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 602005917 1250 602004667 602004673
    0x60c3417070221030c0f030a120b01081605041a030901051b030415060b0c01050a0501060201020a0912060f060314070501051224090106020102220609061d0405101502 73
    0x140c1c012408030005004002580030f011680b1103040c01003001541c40541001d000c562126440c083c0310368a07500716001c0280440c080002c0268160168000c41e240000c1c180e40d41d4800e43e6031880c1300021304008030404800e03c00104004160070090008808516900c9190a543c90034030000c0c460845000902c0d0049404103009040080d03009101269002070f0006202030000c0b076a15682e130000d010b107600c018184d0100260550646c101074000e01d00c20355500340c04106036030761903c00342d09074403035028a1800600300c04020310811385036003200c0500c140208000500074000d01c054070111905c0d90400e82e000d0a41c8904d05c0920341c0204505c4010f82004e103001c500781507804080000000c4003030410041d010f100c07001c40c48442d070243c0c2c00c00103c41000307180b000c495075a600d01038000d50002034406101101c0300c40703103014400810400012074029954540d0410310380f45085500d000c800b00d42d001103030b80c0750103c00d58503604c0c0d019407409130b440c400c507840e0703018541b01071075168241c04480581590 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 602007167 1250 602005917 602005927
    0xe070f140f03030a0c050114161706130218090c04050312090d06090f060c0509181009050c04120b0f01060305040b06281205060705030405060c3417 65
    0x20302c0100c1640c80841d05424085400c03529882c1c030034054803031044010f20041034802000402040c4680080c0d54130b03d20f44503080c90100604048640040480d01550002c0300b01900800d90000c2d41d00903d1162139070746001c4849090307100051941c1009440e01d0300207620202c2c051005150510517440300700303180301c1154944500407004c101d500700100d40140140b5624400c400a01034000b8044141a512100c2000118811000581950003074079841d80200d07807901c8840360700d80761149010300402aa001c5181e07010324042041015100040078525020000e000010700740a20106020065205640554061504100070044140164020b01c20581031034144070228503174a0324240c21610a444052a02460b2440e00600d5107101c42201074080d00d60b180001d006000b8144500d501d0310440c01d480c40742c0c03503811045480e40002e840281503a00f220000c43c1051100e0300040c400c111b400003950000f1000480054102c11f0700d410500c00c44070b05020703950204241046d140050b1111415258241 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 602008417 1250 602007167 602007169
    0x61f020c10050405100c060c0207030b0a05090703050619050a0b0607020409030207051c050f0a1a2203050c010b1f081816170304051804060e070f140f 66
    0x10300c51a040c4a00032416010075403074440c842c000f290083c0c400503102e06013924603208000e005012000c0203494092501c90351840162020606a080301e8022458000c42d444880c4600b00415001e001d06c0c10764840c8110000002c0d4040c420745108030104088020b00115404203801030b1000244010445460203404900564600c1c080d42c4202c0d40540b07000414500c1854180e20341000b9800c095401810490000c050b246040a4040a42d10034015590080040906c0f20b40c1d80b0019140108204094080300001503500495250300030100c00d180703140c0700c039100c40d0911240d819041c10340004400080780e42c2140c40c2402446104582646d840761007541c2000312602000002c941d41d4100403801d004201c0301e280b203403031040240a501e0140d50060200e03c0070080b444001d0b101d080284440140743c004203c03004010307941200da02401100200c000b00000014000000700111552030ba544102c2500b0742041140d100a010000345128040c1e00703000c0740b2050b8502e0034174140c2c410070b2081808002 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 602009667 1250 602008417 602008423
    0x180e07050a0e0108221115250308041410140711070807060f0509040e010905061b040b0d0f09030806031e1b0a080a0609030e040216120c06090506061f02 67
    0x88480c0f61a2245c0f0759004610301191a890350000703040c2d204206902589001401e44000d04010030701c2000309241303203004030800310503c80d65040903020589400015010400a00303c0f080400c822400707441e500d041d4122000b0880d950700b00c0e000708c07903c43c0008000545400a65804504581400500030f0750319003980e13a41d8820503030040c882040103039001030050703074055410b54103c101700900600c402400305c0c82042c008e094030f0700181e6862103102e002c241c528034000301030315514036a410f446240c9410942e0700d0341190b00c240103929007141e03500e4024080f02410310070840000e1180e507540c1060304000e0201880c24281040110f07400885404140789e910b0000341c03c0400070110044080018443c00014400101a900c0110280aa031644400304080d40c1e2010705c44520944850b50800d00c410244412800f40d4254107030400c0520000c84040b034031401443d09140c00394500041035100325603641d81a14045081200c01c0e03840301042c441c851030072604a5207440034103440381c0005c03241c0600082d030f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 602010917 1250 602009667 602009701
    0x20f09121906020c0c03030d1b08070507020613031e030e060c21160c0e1303080402090c0904090b1509040c060813080c0c010315060906180e07050a0e0108 68
    0x5041c0d400610421341160901010104031001425291580d403030340481c3c4090300440103088070b00e045030030040d003075a8018138141c1c0c080c1040d80e42d850300b00812a03082c03180c1a4002d00701c03070141d0a21800c000000420850b02d160411101c40e2000b140d8610500c0c01501c20401c480340640b240c1000d001c44d40b10004005505010301d12214802400780300b8209414541e48541c040c10a043c0380c1d50201841845208000e4600f1034101c4110304000f40ea070401c00c030420615200000700000c410340041809031034100100d0380c1112000a00a00e49502e800004089031000c5400f1100c40712508200000705030f0340c1c00d9003803c040050f5564141440e10760b13944803451071a402620140a07a034008516603031b0420001c4600c143d4000d500c3d50743c4640180070305954070310841409000a0514001011184d04400b00c4012100300e03481c0c941009081040a688040740c2590013166110b840c640081c540da803004846010303000a490306d0341e4601d408030004000c00310064007207050125003002d1014500303ca0350002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 602012167 1250 602010917 602010923
    0x201090b1606050a241707050907031e06080c0f06040e0606030a0e190b0a0618200a030501030b0903070809040905010906090305130f1a0c070306020f091219 69
    0x1503207a5400049600600c0065420301d6091078902d0340e410320a855189003003d480252420050505a0f1b1611640d14003071409100d4000c0030800100705824080d411070f040e07100031540d00351031001c55000314004550060784119290760141c40c5003061410300104510761901c094400900d0503013000d0b5586007000d03014104500030180000000c1c0000c0007075200c08a401440000c0e1500d261104881e65200c2808400c25120b8000c00c07000721b100c1c10042d114200848842d00c201c0801c080d00caa98a000501905220100d80342090109400700d41060000f054001a80d480024043d4110308055075070300c0e4010810302d1190302c104a851f01281e5583c00362240d80710f0403200405e01c986546080380c003409000100800160400c1d03070043c109a0040040c1c01d18040c2c0d01049640659503911641041d6007030700c9240c2c20290001c9414801d000440000c0507544420070848200c9992a56900c040303920100c4255020003002c45c0721141444c101c0400c803503220726100105011203000c240c4a290b440e08550007 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 602013417 1250 602012167 602012171
    0xb0322020a090504050c090a020a0e151c05100501020a11040c03110304060615020d090506030c040b0c0a0c06050906120402031f1e06030803042d030201090201090b1606 74
    0x16011550396541250150009200610481c145490020f07502c240940c0194880c0726050002040c0e0b20192080d640c1c402445e580f031304580c0e12154240304e00004907440c041c0c2c200a003008249400c0481c014100c0c4200c0c3c6c040000121884c01404990034080c0540010341190040140074001c16211803021141980071540014a18020082540104440722000881e500040100001d10080b58000012280c1c410510190143d0704081261542260700061001c505000b900b40951705001001d594040d10003141d40d0300c4c03d51915403100c216044041480c2550303002c2c01000c810080001642c0004103038074100241808070040024280c0d001d1414503585180e4520001019980c082118120100d0500c0c9281c04000050082d000030300300c0003213040070000e115a0300b404503450601c2410111380c6c00442250450f01c8580d90403144e014400741e50221006402410384640c0d09850f15881018881e8000040b241e0f0140b0000d00005002d500c0449814800c0c024682094011a91007440a512001c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 602014667 1250 602013417 602013481
    0x7030c0302072a0519210c0f1404050f06040b0102011407090f140102120c0c030706050403052a0621040b040b130f080a03090f0602130b03 61
    0x2086000340544203015080c1000c1030b00381455840b01c0964002c01c0c165803911020181d4582c014440a410340d44002c2100306036025040044c03180300b00d00301c130500c110400001603c0f24551540d414010443d0000005400d0425003003242804051180c11500019107060040d450070603a080c2d030906004021502503034481030503110680c401c0d801800440440c0c040d4000a08010740d0050200d541401141e80c4811404000304002d0001100480c81d104140d00900f0401194000f1038055004034001110501c00c03600308034030341d94042c4202c0d0040c0449645494541e850340c01e1003031800e9484c2c03000c41c1e50245d070308894486090151a481c60080000c1e1141a607525156030400c8074040740600b281d110302c100c201400204540055014003d13170045c402001c407500e421620706041254141c3c0284000301c08100100040c0c038140180c0800b594a00b400a03081c4200d8a03204840c0c5580324040315819400200031b407000c0b1940400c0c034042d01c0242c4580342185007040ad5250462103c2d030070f41d89014440132b5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 602015917 1250 602014667 602014691
    0xd05061e01050a0f180306020310060314010b0a05070f20190e070908030415021204080c0915091609140303030117010e0f0a05010c0e0619091d060420030703 69
    0x5c200140a4020020750300040d55900308030000b0341041e00c0c1084100381c0c40c00300246940c440d006d40a04520340c0c03c16100281d180c040c02c98060762040005406101c802c0c06188041402080c0c286030381805140f0020b0400e014102083d212000d2156032440303900c1c0c101d01ca82c1c51124040488003a0340344d445404800d44c03a0003400340c03051492984004058480050082580042c0305030840ca60030f0103408541242500d8005034205010b940260f1310f9aa000e9225650140341c8602071a40081d80c0301030980341106400042171908101b280d00e43c0b039032503020384e140281c164001c819200a013501303041460f8039070700da0000a440b40f0040c4680038030030004400ca455100000c4d0701020f0780022040450354210070403601c00743c13500c2c1c0d42e800541da41d501e0484802d401c5070140c2110030346510010300321071034042821030403900e00786150803000402020540c0800d9010645c1d810502c00d008402002e146403a0500030030003a2451007800d00c540e901044e242c44095141107007a2600246181000b0450b603844103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 602017167 1250 602015917 602015927
    0x3180d210e120c1906050307050901053006030316020409050102370f0504150201090501020d060e0603120306011b0f03080411010921020a03080d05061e01050a0f 71
    0x220010341e00c80b1603040c044912490010704440000810390b580040d1803400d910122a00130036101d1840031440400c0010451032154001b0509c10300141000c0c1d0400c0c90400d6664000c100f50341480324092500e00900341903907800351031550322000c228021480c188a80ac101200307100d070140001e000b0382d1160032040c20840d081d010780f5041034a0406000400c605000c1c4c00010003014104850b03503807c1c40000701c0d180c0d03101d0f030586082d5501a4440d213140c189080e180029002030500d0760001c5550711001003001800c02e000501926005400c040b584030b040c00c4c000380303d015000c0c0040d44030790302294018401501240507261b000500742801c181503c1840303640844501c0d80c41d0700a14210848545504240d0059040790040340168504e6402081e000c0065030044030038010003024070205520000e11b00b5007030300701ca051184050102c12020380e40b0307a12104c807030300285451002641c644c010001c0074141182c0c40c860081c44c480c200360401030b0303000010b0700300d101d4942c481041000e084590074100f8056 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 602018417 1250 602017167 602017187
    0x90e162304080a1a0906150616050105250201140103140a2a0801051b0c0c090c04090c050a050403111f020105012102030601140f1203180d21 62
    0x100f40c840f003810500d003003029804045640345410305010046035551200003035180c45828203202d000d15441501c030401c00c00c0e42040b07a1020b42c1c0d4959000312000207900780251401040741520b0000e22281414030410b0101420542800f10b84c034007076026165250b14014030f8112030300003035006d640c030f40c01001003030500e4510700d4090556107a0000c000ca120b003140c000c04240d952000050100c180d00e600c030b02801d890040d034090124400c101082e001c00b50281c3e0092405180d08011034148102c024081001c04000b207484a124a201080c100f1100c3c0b814000c2030070440c5c0c1031404c0b501d000c0c1c1c0fa00f4003500501481c0000340032400c000d44c0f13110881d12215903170301c14034211031070741031100340603c10003400784c4401d00403003c9202c42a8802070b4184649981030714441c3c0e0045c00342420368208601c07414800384c0028460350229a5100303020791526a0440c0d20402d074004c2d00a59565840c900340320b8003550301c2c8170300f450240030600c140a0110b440d00ca80600c01c01030802c2541e22401202c0d00440302c0768a8 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 602019667 1250 602018417 602018429
    0x121707020612190f05131112010e1e01020f040909020a270606050c030a05070507150503070315060c02131d0309010306090c1e0203120106090e162304 66
    0x90780600c65800c0c00000d40280c1542c0d610740c24003900465001c140d00303540003541e06c0d0460841c4420440c001686041c4c00c1645610007401701c0220b005d45400d500e007517450b41d4100100d2500000010300726440e4490011206201c1b001c0250b00c0c1001000c080f4820f44101d10444016569480c143c1003199101d10252000700000303080b8a02410075410001c503078a4018400b821001e04d0002d002410034000c0003a2000c0041e085c0c0138600341004181c003034031140c3c0a00000c032254019000d001c5018810105203255645050751403030b072246040030740501259150040803cac2c000006100700f248039032015024005a90543d07000c03040b03450922148002c1c004000e24030f0500c19001c0100303041c1000000c054801c0d484260790501c0301d40c3d911109982124644c000d80f034009400c01d034440b00055599400c1c2001100356204403854013400b800480042c2c1820780104001552680d0300b040f841005007500d9420070f00213040d1031a520f50b13980b40507003420802e040603081845464020308000309568141e80085c82 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 602020917 1250 602019667 602019697
    0x3011a0319020a0806031903081909021302090a1d0601113904060b0301030b130b0403020c040518100c1202040906081e0a020d150e070f1217070206 65
    0x3c0c5031005841048100c0c0c103c0c0c0a4402c111800c4020060401e500c2c0c122609a1541007207901c4008006a00c110000300300d03d40d5684410b030010068031003519000030300044020042e1609510020840c1030300300c99000c240c40200d80e0040c600b80a4925001c00d2f000082424200520320900d469141410500901401000d00c6885000d0315041c5800451984049000304110302039482d030200022a40140200104440144010300001d4040c4c1040d81d086801185a01e002584503600c120120f10115411170041e0050703000804142414091240c00003164052a0850f0131003002d01e5030365040d0b070000092800e4407031000d00aa580501c0e5090109100b1100c15540d1703e442d0b854070409800f1074441d20f07042d1301c5401809090100540038911441c18110084c040c10390703c1d5020000341068161b03043da80075282900c030010410b568410011040c00c0c0c9006082c0c01d03480c204c41c401c0300e004160710900103210841007c1c4001400108580c0c0b4500024200b2911403161b1300100c1c25078003400159400c006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 602022167 1250 602020917 602020927
    0xa15180302031c08090f032205100909150302030a02010c241b02030a12020a0302040b040e0412050c0a0b040807020603180d0203040b0418140c0a08060603011a031902 73
    0x10100914a240c140716681300c0b05220b80700d0034443d568801030401c901c2655007051001c554041109071050840340303882141a0500ca858034009503040038401590780c0860880942000400390360f00411130200010418494541e1540e00403130384403e1010030003410041030170200130410403c4405900d012081e44101f14804c030100b00c0640041400385803030711400e03130b0101002c030b1814070010450b00300c2c004e90ba842c01a20501d0800107c0607400c91000c000c2419000c2c000820041d0400024000400c0c8409031034180b400e080c00c1c03140040b20707008505420040c08212501c042c000003c1c14000203548401e01c0c3e0015a1941440701150091130b10007907100e400003040c1b02a00420620f20307591064108255001e82640307100c10b0340c0d03a10a030301c50789600d401c05100800900c14540d0200880c01e81100b00403800b0391409080000d1601c3c100c03818100e144000c07070102c248c81c1d4000400c44e4000300507942c0914650402c000c1307040c02001094900301d10b00b8004000f909400c02c444041040c0000104255254 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 602023417 1250 602022167 602022193
    0xc0809131a0405150f060705150a0606030c0c0c05060c150c19170a0507030e0d08100b0405090105060a1107030c05092818020d0b060a050a1518030203 66
    0x904480302400b4896401c200100c2e0141a110107400400c480081245114035500d605105154000d100180c45078003c4019030100741418501181c420303140c00344000381d0b0301e0810700c0240480d03075480c04110800c06283c84410014043e0b20a0070300781c80d0220360b80c2c0e84500c18928454179100200406151803410081840344040e03c2e070000d000e110042c11b07030304d400000540d44220340000d1001d052038640c07a2400c001c10002000e96202a0300100a46004603008010b03044041c605007071a4000c0300090041b90420040380569203030a40940714100708946401d2500b00001d11880060041502c1403000159000352203000b40030903808150050700344d8807001e40d0382c1002e55000009100d0a80508580800240720b01c10300090000c40b80c0620180705003240106003080014443e01d600201c010b2042e02006015075180042c090090380701b2454440b0518208040c48130100441c6d002d9401907014100c24020301994a1400c90540f0082c60202402c00b645130030880c1030b008a610180d09402412006100c0c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 602024667 1250 602023417 602023451
    0x4050307120b060102030c100c1b0506010306050a0911062a01050105030607031b080601091a0316030b13020f04090204030605061f09260304170706020d0c080913 71
    0x9a0307014204102c101d41d5203000682e22803103101c0002800b50407030840345c81c0c6500c039903000b0f19a07413820b4a131401a1040c08080c9203210715204070190348a5004d1001001000658082c19a104152110134002242c659542c81c15008205441c64464100811843c007031a00018880d403140c00860400d12001621554440c000c1100b801118001e00035140092801c5000340179006100341029407914000201c0d9404440301c802c0949070504015040b030f030009444003e01d010742c00c0103012240043d624109500000341940d000c190b003a0901d400e150b10741320250745d00d8441009401681401684d00c100030202d000d0720744640e41000c1c2c0300c0d51020501005000b1107620481c415841a50480d46c1c070000c00940d184a12602d12400c00001c2803910140a03800d601100e14804024030313120078038600c070030415282c11a0015000003860405080189400c20820000b642c0100030300c0c0094681c80001e101d00402c4000141406050f154000603408403503128a5a040e1401e20411420014050302c0c091000f0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 602025917 1250 602024667 602024699
    0x40b0a0806030601140d02041b0201020a080f0709030b0a020904020d051e04120c0314030915010b0a08071b05070e0601090e0f040f08040e040f201e0604050307 70
    0x41100c40010100d0800003443c1d416200c1003030f016802c480b9400100901c0c0c1c072610000f2600300c1d44540180b02c00100310845903140154540015803103407010709000700314801c01028268110a00d0040c403070519001203211090b01d41140ca8203c840c0c0d11031074444064411554080d420a10000706005050130035446540500103280381e0a50084a00310300c03519040b01600c02400ba090304400003e0594082e0f1a4100401c1c400e0800030300c40b01d02c07211040781c65001102d07540155040b21110002c00b103144500701d4058101c044000b420820049001482a140100b0060500038140800000e01404001d12340350a039002040f120415140c0c0194802b800080e90b00601040c1c0302c034400300d0300304003851801e4440c01c540590400d4546e0b6030340b113000545402d20341c1910340c1d007010000454804a402c401511860141000341603a2a161911101c22110011120140480e507541c4001c10350714500345404825a241500040006500009003c0d110716480795130725104089001501d45003029840d2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 602027167 1250 602025917 602025937
    0xc0a2001050115020f10051005040501030501020310061403070c0c0503060405010b01021006060e0d1a010b09031605010e2404180e06101703070602160203011a030a060911030102040b 80
    0x84a05003140300c182da0702e601762071140b01c0c1038000c808640100307802035203d9648540340d5648104283c0c0d560300031030100c0d0400c0c1c1054506940004c01c222520b031149070180002c2062307152505440504000410090001600680c104040a0300401c10b004100401001804004042c1e60b082d05040c40e182e4000c21500380764501500541c0700c07500580200d407160104991040d141ca580c1181248204030750039400840072103141220a907038006403400a0034081c0a01148410540c0d00d0902004040c58124030a260b00700122520340c00b8061030340d0001480d400440165804d80f400000d044120100c418030a01c200d18051002c02e00040042486800d01c00d0415440400c000c0d140464a03460345440044600220000300640e00704a0201810898074500402c0c1c001c0c1c1341440025542d100c240d9110300c03048502450442c071810b095140a101b0300b00304001c1c2e51000b40030040c2400c042500c0320320726100904001e654013450000d1009581320280e040c90010300031507407070b07441d400c2162068118405207 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 602028417 1250 602027167 602027189
    0x2190605040f170331350703092103030507020a060f0c2607081302060a030207020f0a08070b070f060c080f07090b040302150904050109051603060506030c0a20010501 73
    0x404001c05d80e0050921801c17440d83c52003114400f661a6001c4550500070b80d2442030038801d603100310704a241c3c4204d400c280030b41e2a50541d5083c540c200149801665003100100c0c40604600070100c1d24140c034001130317140d403500300401d035540e0780403081c0e0500d007207000003514013810000d002807500d13040d5001510000007600c0d80701c4012042031095503591004e100314900808a0030128140710b008042d42940042d040c24201018501a804681235800061842c1c01103500441e2440440c50329880d68000b05905490180404d03103402100c0340c0e07420704c901c51000408400070b455414440d142e0101d01031550082c006000c41b003240705000304152011111900040f90502c0440e00d49441600018111481c001d60306003010304640070445401101440a000704c02c2c200152506078903107000e1103008001204c0c00061610b01901100709000540b000c0701c1c201407030701c64203100b03680e540300980f90085441d298180d1030f030070214030507103094074904009090311480d042e1400054905421040c10b82d0503150078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 602029667 1250 602028417 602028451
    0x15010807051c050d1808070b040e0916090c18081b01020f060609190f090c05040212150303130929130509120a0201091202190605040f1703 61
    0x1a52400400c5140003c10580003c140e0b00101c2d440fa00540000c144205481c01941c0d5451201a246c555254000302c19284042801c001c007051400075554442a00c0c1c01500450340c50000c3d52201800300d001c0c1480459460801c0000c0034400e1814036074101d41c0301e20312160b158075103501540e10500c40440540d0011010948400d80d44041180e0880c010208000c00c4240c41e00342c02c0040c00d41c0020414030084d2001d0000e843e08603014001c02c00c0740d180e035010008014003107040c0109100729541149008600410001180d140d5025045a00440078060042807000d01ea0003e400c0d0b1180035000c019084070f80c0404582000203901566401081540d0940d40c25081d041d007078170007620504450744c03201418080200e1032403540c01450348124408140c5030044580c16001e0100c0d00611001d1005030341d02c0003000304200404c0c05031005066540001c180d104a03401c014800e0b05a00480200450f40f2030780400c08000c055458032007516402004442461203074aa1419a40c10440d484000c508004034 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 602030917 1250 602029667 602029699
    0xe0403080a18030815120a0b090a0f0b040b01050a08070e19020309100609090209041e05010606020c1908060103021207080604060b1905060f160503040b0403150c050901111501080705 80
    0x50b0b1408040c511b00090300304070718946c03036188042d00014030004840c040c4040140c0000c00088106804038402c030240283c034102810040c41007075058101c2401800456403c5c03084800004640c4200e4101c802060250395074082500031341d100c81d290765116140040144110800c010941a0740b403900c010017081031503501e1100100b500d05580000c0c1d007104072000482d010402000001007102605154000e40848690b200c90071070740361b94010720040c0c0140045221510384150007602e01c4030890000349020381002540340d11b45206210007842a103078105c0703010290000303002903001002c01c00c082e43d10703e04d410b081910140152480c140d20030844141c60480c50541404148151040075050500b442449801250264403205a68864090250000c1c000450400040020340f00c0341c0d42d180c3d1240d1171450004040c450350b0011146c00c0782031101c1325002c0c0b54030505940d0410700c2440c017a58410480c2007003a05000314149a1811004400000b2400d041e000035000100c1e50151880384050b080d61b8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 602032167 1250 602030917 602030929
    0x1608180309030303042f06040302100302071203020a0e031b090402011809020a0e0102061003080c0f01020c0a0203011b0509060d0f0f09111905101b0311010507090e0403080a18030815 80
    0x6c0e40c0c50340e01135800d01043c409420030790440789008d02d183c10010300e0242103455000600d070b01614010001303500011190085a4020b644100e240020740c000c0503060760003120702d00041d40200c68140203a100f82c0024040da0312030301c50300168500c40e00340c200985841e000e8a030065030004030008042039032807a110740c00d5440050702c0c521541703400b10382e400341c68203507680c80c085a44995510317807a030306c1485207102c0400303800e200614180591000600d00030304103105240c01d44500c044640c5d103060114a203e070300309410504540c2d0f0716008444482d070b1001e031445442e008004802c036451256241c030a5a03228542541e01089005004040710080d100081040000e00c1011080e01020031b1500c03c0f0401c080c0c2415054040401a035003064000c4403131400d5000740946d039019065000030003447c08c01e01914800e2040c690800c40b980b405d07445a81c10034403c5040103401400c001c0c108451a00020900543e81e4482c58100000c40c2d2041d03240401c5040081c5449026120456070b2a085001c03074280f85812 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 602033417 1250 602032167 602032253
    0x19080f16020d06380904030e06040b030a0e0106050303030a0506010201020d0608030a1413090905010905030324090103020d02190308030c04080c0301150510050d020301030f0605160818030903030304 87
    0x441c040c600d414013010a00c0041d16025004a0500542e07442d0b442c400d65901000d84060842403149a03100d14003201510290f03030f03106a039160541d01d0214103200d80d8401004803940504054004100c50f155040100d00a200d00c0c800a0b079518a0040003250400d00031006003845541ca546881c000700c030000144400d40702d00700b080241c1c0800550100103a041039080010114002c000014083c031054030343c1c078110b03882140c0c58a0b0740012014013030755042d100401a01130040580d000c40e0190f0540e4040f6a0364880401d000c0d110340f921400d64841c100e55040c02c800590741c01646640c9270706224080702c24940090160106501501e00d5807079141c02d05201d460694100c10200560740380c0341c0b206011001d06e6003c44c04040041c100814801e00e0400d0000714029481424040b03402501d50400d04201d5501400040c410112901d82d24079607503100303031599040502c02c200203420007000c0100c0f40c03862113031124141d0103000200c00c000c00d212500c00039000700182e4101c0f8004480b00108642d001000b4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 602034667 1250 602033417 602033501
    0x70905010f0c0507031a090d0212090f040e100203060102191511190519170f060f03060f0703180b04082a010b0319080f16020d06 57
    0xd210251228a10807041c0b000000d0180e802c3d60381c81d0303480b81c0b25152109480b00c1c45c840c60380b000c2018002c0d180070030440d10f401d6005a00c054041d455038103000481e10b00c030b281c54080c4151480d10185020b03643d150b010801104403802240e0127051240f1544001c0d4204036030060150007103150039009221600d1102e80c806902c00c01c0c07102e06801f9003401100506850000c01c0301840280140c0380032080c41100700181a140d41c4410342c48070b01aa0004c2440d854101941e020840c402c04000280f080c9261501e070002c0c002e0f00c240405036104004240d43c036041100c0540d06120b414140180c855031069628000c80b40d943e01440329240f0011703807450802c01e039200101030144180004010034403070301c050f01441a500c03101d80482c6840c000c0076142c4201414a50307240d130f5500c00c00c941092500300111060158040302018112100d926100c50902031400903040e5070783c0001e0b61018820040b0a84160580d0003880748480c2c05503070401c80010400100d010160246035901e50a01a05000080401e061 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 602035917 1250 602034667 602034677
    0x122703200604080703020106050a0617070f0804020d061806050103051c050706020a0e0a06030c0f021b1c0204090b04141207020f030c0a060509030c100507021e09070e0907090501 78
    0x40b59601c0e51070300c3e84890700613421550b8503c40400c0507529031054200600707055491310280e00680d261400c0a21019044806002ca01000e01c03903201d41002e00c05a00c030b5011961400c4043e540c0c14200d0103003104201e1114450030075001d083c10851540e01c03441c1602e000b00c003110720803056405c0d000715002401000c6004101d0520442b8001480c6800030480c1c003816141c405d82154807400490f0304584213402000c0800e4a4007000701e1980d40c8140c504501c1d05c40c6100400e0300304469500302c4036103000c010145d030040807100404450141c0c081601e001450f400380c030820000005042030235512000751812105051360700c0061403540d40000d040000c02000407520740c0781078081d90070001f480303100e00407142d01070040c402c1c0826143d90301e48446000300302c1920b640743d03101100c038101400c055070304001510800c14500c0071003134a640a010746e100980c1c182d5121003120140c00b01c040e4a1040010200e50108085042001442d84445010545007080d50803928985600b4010765041550307005040c0060 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 602037167 1250 602035917 602035921
    0x5150118181115211911190504080a08070c060507020114160605040507060f050c0d210e070905070e09160c0f05010501050a0b13061227032006 63
    0x40741003032101961103910f604143c980714441c1e408034920442c41144048140c055002c00031100c016110030344d44050900420042d2815000300005103000f0705080340c0d02007042901802449000d00112030103800d110003203030050107241c0303031400c002d17400424220355002a195000a0050040c000d480320b00c0c0e81616540003402c0800c0701441560003861240000350140c500320008245507201d000e01880c02807014180c1c050500b88042c05c4002c02c0195402041400c121f21050317054041441d070304802651400b0325581c908185408101120030310804040391824040300ea0201d0001035400494500d003e0600450307803401f00079240c8a102c07100464000c2100030009040c00e00c0000c0400d81005a0b0074000000c41d290b844003990560751036012101695a035005002c1c615049101c070008068032a0309603c0d098603a280c0606140e0b062046d42c003403210659a0b8844403060b500b040d40e08040a141c02184400b80600d0b51080721401202500850000a95000080440441c00c0c8828000500400c215 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 602038417 1250 602037167 602037169
    0x13030c090c092904090f1406030a0302250510050301030c060311070303050c0f04090506130903050d0b0f10021c050f1804150f08010507030203040309050d051501181811 74
    0x2205002c1c6a440c2e0f10410000c9185d01091103a4910794002d5000091902c0d0714192003241c00380040c1c4610320942c050010500001c3e400034070303064001e0390700c00881150841504802c1d2640b005402c5150310032002c8915040241c1e21801850403240202092201e0b166105025030840b4400340c3d0400c20301808102800101e4043e40000c0c4e0428450b0354400c0c9032100c0c140501c04141c00507046038042a813250103214461818485020040c01c40314010040002c0701e0340c0c060301c6480751541c142c02454450158488513903039142060b0354010058841010400350b954000d40707174070b05650340c1b07a07010080729040e00c1178511071015248455800d00030b081c5000d05010062411302d00382118aa07100351920b221001402180c1e403204000c01c090b04040c0c4210303040c08030072070944500600700c0d400c1500c14010800403941c80250760703044800c169200c644090f05420094145054492408460741d07900000003070485082031221000040e0b52010010790760b460140051742d200301903001e002801c0d10042ca100c6 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 602039667 1250 602038417 602038469
    0x1104140408030910050106020a020f1c2306070f020615010f03020d060b0f030f0c070807020108090c09010f0f05010203040e0f1e0f010306060b070314030a0213030c090c09 75
    0x7000c1c3e801152850381080300d9403429070384240c01c01c50040c1c01207260801181401180c592811a0450f104054400250f05100e0509007808015008003c0c080d10144805e02c0b07521100c020003071813800d03111646011301005e441400c0c45d40f50f1000520440c400110203a2590002e01c500600c16903c0e1211284200011030194102801840075a80c1c0c0e181c00240380c1c00c1020041c041291241102622850940c0030034503110b00003804210480410001c2400060340b070801c8230007250b82401c03c40b5094613440c1969103072105d40c0c00b20a800800e00b01c000f041c00d1002d9116030089540075145221b00540310b4004a172240101d10400c852035142c04007140000d020781c400b155100440300200e21152001d11015001080165003101e45031030110014404c1c0030f0240110405810011002403402d01984d400500c005003011055550000120200311540e42540407100110440c2000c0d4144a481c0e06109102e0002480340e850b20519150350825010301440046088543c0c1e02c4c03a10001480c1c036901e00388 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 602040917 1250 602039667 602039671
    0x1205030901110c0d0207050105071509080403060e01060305011a010912170f030106120902010c20060408010209100305010302030a0305070804090507080405010b15090111071d04110414040803 84
    0x141554907003412486400d10480549030441c0d841c002000389201c0c0307804c0a4100600c1d03030009810407400f04100000f19100b40510b641282e290100002c4114090800d500c1600075500010b2241d0704001c1c07030620240e01500008180c034000d01c000c1080032880180945000011240180450114a0f04204001828030b00364034850082e41102d0145886c80000e00c0954000c016040701800c000c001801142e6100c5600007400c00d100c4410400d039060342d00060030f81d040240004080854008071564600b00c09503800c4410400a0941c54541c2c0d15405018083d4006084041c01150346000b4042510320034080c0c10304894014000e0300c4609401d840032159580009015120301d1410040050240b0091142910036071050740c2d2034440d41441c2c1351440c00e4800120025200d17120b42c150303a00200c00c20030211041020700b402d1150941c68490445424280e0319884541c107101b01c1c1214010000f0002c00c60762003184a81380d1000814031070002c02040700d03c5000024104000000050006811880116 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 602042167 1250 602040917 602040931
    0x1218060b040603020616060c090f170c04111210050f370e09010e030a1b06052d070c08090102010902031b03010c05043624080604120503 60
    0x882c034140c403034000c03030f00759445134034401144e4190340c10801c1813004500c0340d06100b06440c5401e140c103604c0c003040d500303071747d021401105101c001905400c0c04a0000300014903202c140940300f0b20001d844044003c88580180030310b0030b100206c2900080400c03200f01d40820641d1030040940c1c50302000c10782444001c5030420285410841c100d032a07003d101640120f030300004480c244040341003e0501035128504c1c180a084d0070b540b03a042190ba89100f0401005940740300402d40341a50001d00844d51006030f02e10007010280030030b4030700001e10001500700c0c44490b010350603404951050354a008040407481c0b05c1100c0d0500042c00c014031110005071808020b02c20a01c05100220315000c581d0006410500707200c02d00e050300c0d54903480d10304240c1400e018401c0d2409003804c1c0641014034204908c8190031810901c0b030340c25000c0c0400c070008017407800c41c1011a890354810030407558000c0740720344060030305448150240840c0b0480006108100180340e900c1160f010707014249240d8101c1041c4c61642000d8009 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 602043417 1250 602042167 602042171
    0x708011a130e0a1a0411031914030405060310090b0109060f05090604081912030e0a0b1003050607050319020702130f0f09050c0405070c23120406020d1218060b04 71
    0x500440c000f6200c002c8440220901030441c0c5c100791500b210204030071103407240a07030020100307440e804030f070481c240f030540381c00c25804c2050040194110742180b1994201a89c480d00200a103c0c1c08a98214854155281d00c1004c03c01a140f1b2001510034010a00c50580011054622454501d2281c03010301f0361079102400c441d05003505d410441d420a0b848010115a044081c0030403401d0041e544440d0000700b005080c01c000760711520804603224805404041d02459035031010664288842c45204000e5400000755040750900a5009120340d005503084c0642c3c1d0502003510b1800309842c400c44103e00e84c0108407803001052410680c024001d01c0144600c21640d986405403402d42900a07020018807031809468030304d00304c6007000308a45000d0140da0800803136043c010002000501d07483d045072004550241032402030310316a49402c40c41c2085e00001c00010030001006500000e040119000c1625049079940e080d5898178211200e1000300340d185040c80004c5000315501d50302a0701e1004d800342c00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 602044667 1250 602043417 602043433
    0x8060c120a151503020d0606090f03030c0f05191209060e0d06060803030709030317060a050904060902151b010c0219051501030b0126030a05180a080708011a130e 71
    0x1d85603060030100f5141d400710344c000504074440340c2c040c820540540001e050200203030303040c0542d51703078815441d01008040c00b90444007007040c440d81c01810910140d00004803205011a0b90b001040044040000c4500713050815800e0061401911206c05071750340c56440c040c80340c009000b0840c001c20441019515280c7c1ca25021500203018801113106035000d8603a0080540f8500c0d00800004040d500480d50341991418001541d407050541e0003161004c8945035483d49030b50414400515040400950084800000e9002142580302a02e020300700c040f2100c100d07030002400c06007a1003019440300700580040c41f140c1201b1000b500c804c2059401102169040e100301985200c079081c080e0010b440038000e8400400030003e40c085d003090600340c2036001c886101c000c0c01046036240030b07038111031090103c01301d0031640b0541d80c1d1003038803402c4a004100140791580c4102694641c404c500070ba03120343d4208404140c0684920944080e0000f0181c4100c904411074440ca000601541548210602034840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 602045917 1250 602044667 602044679
    0x71d1807020c01021002120601051c090f030806011e20010e0303010306110a0914040b04090b040209010501030c0806190807060216050a05060306040c0905060f0408060c120a15 77
    0x26a8a1203040c0d541c0040000c03601000c00a450700e440e0b01261448940100810450141000d4065401500a09041c3e49400e0302c030b610103000070340c40980c1030340c500c1c50728403040c00340022482424005030290f128032441780c03994001140d243c0c81805020907103119500352050a28401c1803022400b030380600d9005122400019841d0a49000b08060821079102000500602500d4414001541c0d03910140925299403500f000c0d00c40d05440c82443c4002089000060171502c0d035410034046c1f030100610412182140e40307449450780c00c06580c20307400b800ea001d00200e1154002d1240701c514941c1500d69882030b543c0c0c5810071443c107110072080b131400c3d00913010000b01c0e02010420f0202418158000c3d040440ca0913585045000c1c0980c015441804401d0f8104640c0e1180400c4a401038000c0e600880c1c9060141d0003550050768951000f44c0001c3d0020300700d030040c941c4030040c206644084043e074a07152034215000e0960301415070f10440344034028002c100a01c1180d40b02a0030325460303000c220441d940c0d6207 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 602047167 1250 602045917 602045959
    0x3012304111209160303121a04020d0c090806060607060b0a0801051015030204050d03050a110601180f020a1b03020115060f110f0c1221090315071d 65
    0x1c00400e020b20406101034510148070203040c0b0098407207107001c0f02e851070702c00901005c4500c0500c00d04d00c1c6d40f402c2c881c500322514030917940e600303d000c0c0c000e42d070b503e0000328007400034540404180b0000d46082e1000c6212000810344500901000f040e071400c0807031503180d041c01072165189a0354010b20300384002401e440b082c090b040c800d5100396141e10700503107040200e900000680a400c001c1510400090045685d014400c0c00d1807030301803a001e516100d47c0f0f0000d40e05600b420452001c2803003841c00004071190140400c008400079041c00f1f03c01d072007550a0410903401940d41c50004266411100b03491f440e40d060348001414041d100110f444d894203204003036000665000800000c0800011000c000d40010300e01555990040051540000912505440302c1c400719940d44140414005980c00410400021118031004004523811101c450b401240075402042c88a000c0d0142c084050300300c06800048620030081919a50700441644819101d20036100780c0c6568802c0c4102241c0d01c103c4246 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 602048417 1250 602047167 602047177
    0x30f0e01060b0918010609060c0323030a11040b0f031023010905030a0b06041a1c02030d17010e071103070308060f03030403020612070302041707050f0103020301230411 74
    0x21000150740c56a0030014855250380503019405401320310302c0100030580e4850440d01c1180c00c40d180600032008503190444440f000c1c2d4803001d015960990303d100184e4591001103000344c4505c0ca04201e0300c900c030f2440e642c1c14052842007190713101d0b040c0500e4060880c0c40b401143d01c02690300c0401e9116840e02c031022990007600d03500c000900844600f5061a58200c80e4420182c60228010407074031909036100c04030200b00902241c05107444281e26501d01c040b25031011983c110040c01103400b2a10620041000710741d120f0164480d10811000d20321850046040340c05400054082040070381c203095640c2d1345600090155004c0001041070368000c1c410900103000b59078803c0d602d245582c03c01d80e040042c0322900c200700034401e4204010800040e0366510860ba1400315614080c1815a69031005031700074015588907442c03607042d20810345c0ea28a4085081307000c0d01d43c201c0d20040c590140d20011030480c0824003507040c103800d003144d441c1d89840c1014100080441c0092002c07802c0030110301404c8840d044 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 602049667 1250 602048417 602048429
    0x2508030310060318050c01030c0e0a08060a11030f01090b0604030602070803090616120513050a080a02011a0a0e1f0b1309020c0a1e080310060e0307030210030f0e0106 73
    0x254402400829490f0240e150324044c80c0041070000c9555031a400d45800700079101e0340c10304d540c924071180d0300d50060300e0520310b4030b0300140704020700c0b541c40c0314481c1c50310411611100700070302e404803010300c20030040d042d02d01a01e0300419040240c2e082840000061901010082c0d1140040c04000000f55540c001000741601c02d0000700e03101d0500319922841d00c007010b440320005005140049404907800018041aa50a400c0100d80707034442900424018600b414040d1480c0140c85901040c040b034080242a59100d0394020001085401c1460039a10540f001d0b44d640036005d440104003190340d00b81700c00c0d000340e45004443d1120441a0070800c44540d030fa0301810240c440442c403542c071200c2d8030048030014030015000394513182c503010500b61150002c00b40100a0604030740040c1d0000030843c80807a0045d031011003e6982e040146000740307014118030503a0002088a030b28041103060120300c0008a0307601170000603207580315070010b40141140542d588241a81d07450f680d0300b110030074011403005101c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 602050917 1250 602049667 602049691
    0x311030d0614010206062b1208040c0611060402010f031803090503010c0309080d020a0c0f0501060e2505030a020702031c03060e09070909080903061f080f25080303 72
    0x200d0010741c1100b92608005482c15504a20b01304075881c2c40b080c800ca0082c10171042c7c2d071006448a0200400f802c0200c0401505412003841c0d4030400c030780c00c0100720703001310302585107007080d95070318001144d088401c036040710009c0d081400801d00550041e100a00e10154504000c511821000c4090900280d0240298002001076408018030304080c86050b005418614092200501a45854000344100d54402c29055400200e040c4142d11641d00480c0d00c59114180744098102420440d02800c003034051000c0001c115000b0030259000900b1101c0034113000040412400c04250042e1090307000200044182c680030000800183c0d4103104a5004a00d064a005904048044014202ea2241e080700804408001c01d000350381400041d29411500080c9010405411620f02030041d0300600c014070740c05204040c2070202c0c0602c44c1c80c048030b4000340140d10310403023aa18002950f070340c20f450044150a82001442d1020009080c40400e2035180106180c00080c7daa44202440c65000321000c0350500c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 602052167 1250 602050917 602050919
    0xe0a062312090d1107050a030210033309050f060909070b0a03020d050c0301030f0b0703090804090912050a1218141c051305060d09050d020307050c03030304050a0f0311030d06 77
    0x6900a006130b44505070020080c10703060b041c000814a0104180070181c07041b421051008500c511075001070070040d100c08003418450a42c0d0320714071400c004034058042004261600450a034640388034403407041a80d8a40c2403115140c000600915100150072030b8007900a0130400300b00e102c0004028210300525680041e0b840400b00d50910861b4000b4116480c4114208010030104d581c0c00c0540301180e400064004042c0c58084040d001441903160050446c207001c03c00260815441d03210f1a12580544411000a0098101103506115211110000c00c650702c00010002815500030f01407511ba04402d503a0420844d112101240340030b600c034007100e601559070600b0300400c00d01da5141058680c10541e06107044d0b003500005a550a000341400703290301007200d501c6000c060700002800d58100c425207600103144c0c4002500c130b40c45008161500d10401c0324401c1c4504002003140d07c04c4c4c2d0070034094595610565104610915090800c1e0204540606080048082440182100030304503000207884c1e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 602053417 1250 602052167 602052193
    0x170109150305030a270311060c01021215011b0b0a0b010203070f06020901090b1c050910060312020c0a030c1a1c0917130621050a0b010e0a06231209 65
    0x1021400340035107074130100d20170b04000141902e0314104011500310f6049449031404103805009000d00304080c59268011001c4c42480508070b0b0750416a000280d031901c01c0407150400e007400781805184001c0070b0070214000035010081c0c0741d0003040d00000c1407040d00d141903101d0303c0300b8011034030150341900d0850f40018144240d60700b103480900180308640a0340c0c10202c0c4248428201450910006021a1207000040c1030707070803d01c181c2c3c025070100c0000b007040a4580c01d218856001c40030220026208000b40c2c030030704e45020103d2a00301e81c3d01c0034440c4102d5041020401003800c1886205446c0b210611558040d80c0b01e905022034216126800010b0a40c1d003820280d582e1405261003400f00f000411004030f8080f8010f1444081d500242020124130101c0c1c00c115500c061481c1d00c01c0c14240ca40400d0001401c81d6820082212078241da401c01e11a1803041000410106c6100c1c40003c2185e8134910f150307401419030b00307c81c81d020100284d4103002c0400140c405444003200c800aa0b504190503220034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 602054667 1250 602053417 602053457
    0x20703020d0804080d081e04020d0506041a070c0206040302040903020109142d0d1d10180b0903060f070c060e0d02060901020c070b0717040e1501170109150305030a 72
    0xc1703a40d20b2402d9401800c20380e00c04c4103640c020741c0001c48525605400034040d501c560725072144003540007045500600d824103249a01101d11010702007952500c0c0701052100e44100314001d00303d40c0041855180500e164200801030550060031402e6540314413120000c40c044c0846101d1701c58030395000e00a1416801045909401024540c2000074890000e80d50a00342c0010442000d62581c1131200b203d440c00003052100f03054036001503034400141e04880718203541c82040c420314010038001001070213884550070301c100c1c05084002c9415502600000d2078001c001a1003d40240c21801c1100d4a03c20b29150740c07040d00c08034810442c941d8810340154a10550420449510030f4060b4021030030003900360b4820751106030903c228100281e01107980030074002c441100d45d900049115003030f0741d260340e81d86580c01d12250031134101d40c1c08080c410350264a54000c0b41501f1103041d0342d862401450782410046001041200c2001a2190048401100041040009017004401034850a201074148960300310 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 602055917 1250 602054667 602054683
    0x70506040f151706040203070c060e150f07210b0303130e0a0605030d030b010201140103030e010210060305070501211422050a02040506010c0b070c03110d020d0f020703020d080408 79
    0x1c00003c80703e1524600483c4180701e403c0a402c03140035a8a0716038074412295004000401391000c0d1400407641c0c1807100c001105d111440f03454400348811703500d032180f80000070300464001c00440c040d1340740c001c0044d003102c0d508001c102282d000000c00610040109196070080b482e2140312103400c407400e00c03000b2400e40d01d00d584030a9501c414002d80d802e00e00482d031140c550058800901da11812080c1260b03000707402c450307d41e01c4400901101c569503414002c0c40c00e45044100c1e80907010344e0a4025004100e0b02901060b00d0308040107040003442c0c0b000443e141c03082d4410052002141c0740d0005c07140c1c4041d00500c0c00111031411003100c00c2c05c0212148030031071031a0802035091016030001500040000c21f001c0d41654045500003100d5507400f0068800903501c010080458038244100a455a042031089403118041d960b844500da910640c10740e80c801d1001401c002583c02414012000c40c814071000c00c0004051042d80d11807a942da0100f2010550003000303c480b000c0104080c0900c00d42004440 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 602057167 1250 602055917 602055959
    0x1303060b0303280e09040b150d03050403020f12030a03060e090d020a06021b07060f031401061707050d060b0405040b030d09090e0a2906030705060417070506040f 71
    0x1482d0540201900800c910100c0300320850030202c520b00d03070390b03e809400350040280c0090a007460a20f85482c103121341d0441184d034a030081d040d60b24040b441c0e040c9502e840b148030b44d040d21800e19082c11a001c010307550820711081c640c00440210204083c240c1032024200110154401003082ca00340500b01c070f0b40c2c00c0000d0168a02d644080031703280c1219800102c10340241c1d000040180c0e20100d24502301c1e00a074800900c2000c0e40710f100000214181d0081c2c50001c185080c1d502003044e8110b640000e2043c0c0c1c0203100d0180064000c001c031601400001f41c1050b08440039050561421000700c85800541d4229440407940c9200030400f08814141703800b80484442085000e081d0b640301105014001200c00e000700381c20383e5601d019400c0010302c02c20502036090b800c170000420200d00c2c0c02d507108020040c980d44c40e144040c1032004c201507040004ea020103583d07005082c5230401d414040800000c030942625210320b80f041060000703aa843d00340040c40a409100000500d40d0700b0000400c10441d045a492 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 602058417 1250 602057167 602057173
    0x110f0303030712020c03040503030703050310140d020603060d05070f05090105090c19170c0403140a050303130804051509010206010b120109021c1a0406060e061213081303060b03 78
    0x3114591280fa4600c0004015a00586601c00d0064081c45c0d4040c03070708030325010b11001400505041d080005140b095004641080350720342c6441e002104450007401e50f5400a402e40050801803a10388003450f03020318050003043c542a495101c0d00d00d4074039103501031502ca0580c000300340b0242c2003403030005001d0801130745e0201040c1000d01c002c2c44584107030410046c4c1c11205040311070b142c030301c56200f403070314500c400c0034580d0036007046009400341303034040d00c41150b900c00d080c100b00300c1c1345e14081340d00b1a03880d812074065425907840141041c400065100103c6030440104401714051340e440b14004911000c9200a6480c0e213444800a440c00724185c10514264805109102001456009075415201036840250b143d0b00c1c81c4c030701d01910040c2203486c20800d138200044117401c032030311411004030000100ea0034040b241d91100281e40021101d401a508103500b0032044048a0880040740d4001c05040c20700015103407251910b1202d80c016201006d95a4100c4800f0004e0041e80d00031580081000c8001e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 602059667 1250 602058417 602058421
    0x60605040b1c021207030803010b12090f0703060209190e010618080601050d020d1e260f0702030c0a06030b1806032a040f09020a0e06010930110f030303 67
    0x4601e20080004100034400c1280c04006084e211003800750708000d42c5d00085054132541c540c0e080a401d43c0005230000844d520035400149840307400140410740c0508500074100f09803d58550b20060b500800f1115004800c0306211202110049c0c500380080510003c506825414094005c0c2007126041071914205010b01d0280000e0001203070f0715044030b60172504c00c6c8285000d4400b182941c414144060521100308044101c1103086401407001d162003070281c4d440c034980308079040c032120494000740c0aa0040c24403080c082a42903800520304a40001c003111700040301c030000200d1920050300500c0000b43c231100240518104095504050038400d00d500200345403d50100b0303650700c2045241181d8024811000c1443c20360304502c0310780c0c108090320078080a20180c0703007800600b9500780200d004001480380040c441d164104110b0103204140d451800441c5001e44945544c40c1100c5248601c0306590b6071145040103080811820702e00c01c102031a0726043c030b401007000808001c04c40318003a800c1081 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 602060917 1250 602059667 602059699
    0xa080a021c0902090f1605091c0501050402010f0f0e090405010b03010c0f0e03010504031704021207120c080606102a0b0415050402130213050319140118060203130c03060605040b 78
    0x8070454600706c4a2505940714081200010701c0c0540103048400f0515070341003114140801034020f24412170007038803903034011400c0040c121000b00c000d8012a0000341741d418190600c4c80c0518009800ca80540008142d4085160000e400c4176801d10381c2e41d010034900741c1c1c07507102c503034000f0040b52000304101c00801c01860283c8010b032170307003210007803d1444007110300c009411962000c8038401030551100403070311460b858000041d050f56030a03500f03403031845c03000c4000901e07202c0028029115890203403548810056564058031031444025100000c0c0c0501804445620000c2103401d03000ea02465a00c07030907080034203180c200b40e161000b80c6070358281064104005a25900151468807084210041c0d6070800b0441c003000c0034a16822503a03140c0240d9038100f9402281d900d42c0b210342d03400360181e6500380040320407042c2220702e90754110380c00d0740d001500200440c6007940607507030264441002034000c20f01c5a40d901480700c2940c00031070748142e40e0641030016042074420100040010f4640c5400310354104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 602062167 1250 602060917 602060941
    0x901080c040819080d0f0f151a0f0403171e0304110105130503070306090b01150905130f02030709030c090204050603010512120f040311150a080a021c0902090f 70
    0x40090680f0810b0b000400100820308044901c00f880800081004800750010700014060b1102000c200c5410408060340c0e000c260f80b0315030304550101c1c52440540309042000202504a121681071407007080c0400004660840b091550841c0d0302c1c0f000c3d9540e0b150903503c51056525885e1000c3d80564207104000008013100780e941000301d024207100c0c0c3c4502c409039044403101d03001c2c0c00054050244850010400c02141c1002064910a440caa5100da03268086007503e035078000d45840001c1c0d410201001141004400040c0d500581360340416100c00c00400c41040c0d90003998400c00151595408005100300002d4420103017480035029403403d440c4c4400103a01d800180aa280300e0500a18102d03030040c000c2001c0403040c0035041030552500ea080051130480c0c0c00500c002e0b2001400e4403c01046894880d1270b1601c01c1d41d44403c0ca90508100b140121801600140700d51210355003000b441c1645d0385201d0807152031400025010503c1c9142e031041c881048005415000d0784441c0c1024000203e00c51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 602063417 1250 602062167 602062183
    0x30d18090903050a2a060902040f0b0312280f020706020d02101104032a0602010c1403041109091b1903020112020720090f04211e02030901080c0408 65
    0x192038035401101c0001054007000d41c118001d840141d03c510405000c11405402003c1c40764000c8030100010140b2b46c1c070307000540c4c020042c0b00e40d16401c81c500b00c00d00d0310b0b4058040e040065104900d04080503403650394030901070241000c0404181e080b0b4031400c1e12a13040000310041c24191010b880440d14aa0005c1c1d55010b042201e070013042d4407024000e10130003107403007640c0c0155088074142c80040b401442c003020b20803411480310300810522401007000c500500403100c2c601516950b08007035070f8450450340c1c05a08054011107015910181d11901daa407260030142c051009240580000c510084c00c519080c1082228a4001c2c001081c0d03081071f940820341200c0850f0b4080c200f0325000c40145000030024415141c0003003900105070340c4000800c40060118804883c00da81505841c3c0b00c06103400e00e59001180c004115181c0b100480c0200407800007040d84d24501e60510760603445a00400e1070801c0400040c140050740086208240b56901107403050f000707050b000003a840c0c40c1c1441c80150f180c0c801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 602064667 1250 602063417 602063437
    0x308160c09090b191b050f0d02040f060906030501050d030e03010216110109050f13050702030c0724082502010627180510050705070206070308061302040b07020904060209030d1809090305 82
    0x41100044058021f0840b4540488800c00f10f50b65610b507a01040b84500e02c0c01454001034203030b42c006c991035000b4415281640d0005000f45209143c070381e42210409000200c0603090b5409022540c070b07840c800c1203410341003403040582c440300c416110001886a14960302c0940314580031550309846031290031441e18070400000380031445643e40c01d0140d1542c4520f07600c845031441001c000090180b55840000ea00001c84802035003a014125002c4543c100c041d64608104810300d5030f503007880d40c0d031428020451a07517400041104c65450800d604034015511100d14003101c00070184074200420721800300362001041009100305050303292030769500f00c00711076039083c5950350300072407992805042070741c20059008091999404407454000c10821040d1442da0060484010a20238100c00340241e07016918141561802c0414540030803000401c040c006941a0f42d0820401d8026201404031070749a04298841001500f5800007418050f0744662044c2c1c40c82d460311160000003030b403040868501041c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 602065917 1250 602064667 602064677
    0x50103050901020f2709010803030f010f05010206130606180911010c1e0609120f0206070207050102100f0b1513120b15010905040507020d08010f0308160c09090b191b 73
    0x61794035000c0126016242400341c0c042c00e514000556407000000a40c0f00e400d441e1068034050b41e0300e04c0c544403801c0302400340c1c50140e04100001a091055140c0310650b43d4020345010480568990400c00040c0344131040300007240c2c4507403080b41440307007181a038654450300f841d100082241d83d80728118101000700c84180c0281084c0c0c402020b0081540100201c1030304940c071048218105000a0021921491180301501880000803400d03030000c280e0904959040c1c018000c8984428404030040c001c8014981c0c200d40c0e1800c40440503200c109a00074500c2c203e10f02141d0340ca2000b42c440030801c00c20740c0b03e81c0c03401c401d1528000014020040650704100c000302422107140c01c52005036080780440d04560f400a2401c010411040c2d40010003002d003003003a80f1030584030b1f6200d4003412003e103114000030702420003c00c00a010100e01e43c190308205d501442034074400c03d0b1a0316160041c0c2d0000101550300c8142d8030305100c0c4100e174603039804000312401c050030000030340032003444003203803060120243c2441 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 602067167 1250 602065917 602065957
    0x70f1b0f0311120d020316020a12031e1b12060501090e151e010e0a1a0a05040317070c090b030a02150d240b0c2107050a03030501050103050901020f 65
    0x41c03401c103c080e000f100e00d04000340c0c841030f25480c0d582c025001207440b000c0c0c0c003c0c2203007100c852a0010941c0e07c2141d800c41484054201445001d80103402d026010100018440c1a0000348400c3d912822500d12040c1c5940b10324000302c00001055400b9081c1816505454500c041116a8106000e80b007100d6260010410a03900c1c4030060f910600030150480e0055030702000b0300040302d032000c09100b4001d000d07260b82c40c29000351000d010300700b000b07405428503247e820420041c80d940b48101070150360185143c060300d8540c070f03660343c034408260b001d8114103030002c04124041003182501047c0003414003020200000500000025034070700d40d5100182c0500001c02c000140e00b01c8a4048a68810042100b4040032501c000c2ea03141d4481010003170090044021004280c040082d000c035226407014500074940c406407140b00c1081031000040c0a00a80420846140090340900c10341c1c0c001402501c0001d42985004005420f41d200100b8042981c2d10401808540b14140c0b001e8a00307a1510142ca0856a = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 602068417 1250 602067167 602067197
    0x206090a0201031a09151306121509050703060c022e0905030f130305060f0f22061e0501050103020408070e0a060504140a18030903030806031005070f1b0f03 69
    0x1c04c20300c00741160400000420411740030403095501d10080300503207078001c414012005030307422140c07680640300b1030080ba5003807000451840d19000c6030031a20600000703186400e580d5554a0000c15030b2007101e015807a0003400c1c00e0a038040c072022aa0703c64100e0080a0092401a52a061420458083c1740144da8808010074400b081040d01d048000100e00d10f607599002030780d20000e0000a00c001c0741c15204007000a01850744c0200024011001c62081c40c0240c4c6829400001491340d14010b141e501e0000c0d4180c1e004182075000c0c5011802c114104078040d0320401488405845050700282d0501d801040108811b0780002000004c5806c01000d5101035103440817040068088c40d441203074010304100c11100040845c0d20b04c0c0b80500402d4804021103d00ca204000b44104602e1010700032825507042000401e00846007a6400b400c01019141000c13902120f410454400365100fa0000b0912468400d03116005140c481d10780000d040d03000c0141c2400e41d12420000c071250002010020442100814 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 602069667 1250 602068417 602068451
    0x501110709050a0b03070b0f04050603220308180d0914010504030606170d030b0f0405090f2d0318040209120105040506190e07050402180901150801060206090a020103 73
    0x103041110341c01c0c07015041100100e409041c060300c12038440d001e6032000003001402d40d03045519000010540e00d040514101c200030300c94200801c0207104048aa16000c0613890032a000e0580d94400d841c1c140342800c1803500d8070410000009a015594040d5011851154004500004558000805408424410004855a004688c001001d46041c0080400d081e90b141001c045244c0000003141c94803040070200f242980e80065020740c00c02c007100c0054961341496000940d200a003102203403040103030040060300d01030001c54041d045d205203a022825405490310315820800d000c40c0110300700500e10300c040b414800c04407545407103030303600081800d016202d81304590041c030104002004a440e080c2081c07603e4240494034620040e50052800c400c1d051144110113103400c510008003e01820f00f010300000b0b612911401c4640c140b80368001035503558981c0c1d09406050107824460301d8480301c03440580030031410780000c4295080602005809400020754151305034091902040d141510007110034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 602070917 1250 602069667 602069669
    0x1d0a03021f090c080f0c1f0c1118010e0c13140d0b0705040503160e040224040314010c02240c0d020d0b031501352a0901030c05011107 59
    0x8120f03103a003000051030080225191916841c54000d0f5a030b1055802e0410031001d00351b0402c0c080040001d02e0b0441c00303620841500c015a4803c0641000385171014001806e81109003031040c8094082500500800351030030412a002002280b8850801c040501e2542030300e946c2d4028402c0315000900391007030980c1d51699140629421050400389070502c1d12004100794003601540e4040e220300580a03031100c180380485c0e000c5803043c11112410751199070821580c60492041084015070305070307668100024640080c00258843c0b5480d00110142290f40750954000f1050a030954000c1004250015840c00a10b030407400d018000400c3c5581d9441e0010365070043d80141c1421900c00700314601d103100d4940c0404140d0070210101da50817000e0141c442c42212090007035061f5107040008540403000244840303110680c070b1160402c0c1818031000d0303540c030f0488040b141113441402c0070441c112061130174000c0d0080c2d0301e007901c0345441d81d81140c454010021103481824108000c2e0190240c0e5030030113201ba24 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 602072167 1250 602070917 602070923
    0x70c021207150224010308030f1003051b0307050a0b07030c0503070803070306140312043302060103020901080d14031905181002030603070b0a0915031d0a03021f09 72
    0x20b42580364000303640b150810510395111503040414003250062032512030490381d002d2059031459a0b00c49181c1e40c0140041c2126040c1c1109500200c000f58003800320101503100000c3c9615058800d0003098901102c9600c081d010b000c064406000102403941100c221540604040d041c1801602d400b61a501c00c581000c1c3c800c12012061089042d45034020303d0883d2003c0f0610301c910700812042540b21051010403581c6031404010800041d10460f042000e2821915518140713814000582090103d0f01d402d000d0068000000500840c40e22400d014003400030000240084201c0480150200d00010803000100c40c011000450350001c0e41d0045217803641c03650041c000d50410703e052080d035025007000c0492901440720b200080c034000384262449510020010004c151070540110208e038410000b02e400c00c0483c0d90f01207500c4041d4007600d801c411040d58000354242080040c1d0001000000381100703603402103000703480460740c00030318000340024407031215200550444c0000000d12000c4401 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 602073417 1250 602072167 602072189
    0xb1c180201231c0615120c02030c06010801050105122406131a0f030a020901030b0c0408060c030103020a1208030703051801060b0702031605060d050403140304050307060e0303070c021207 82
    0x281d0900e034a903011044400e10303e07640034081d4544603083d40103002034101590001440740002120401000d4001d1340340c0141a0066a00d0305401d60f04090800800342c0044416a44403401000386003020b203100803d4150480146c0034004480c0440000340449904042c40451050041800e594404034442e0442552500030840d181001076200c10240848001620405241c1c003120401e08022a202c0140b0340c1c001c003d141640e0070f640e241021144050010b080c141801e01001c0348808003001454010700070003848503201e41c5580304105000e40641c11001140440000400000c0c001005072900300301141004100c0d640d44085010030b80001a117005201c0d800c00e03100040c0210044000c0040c10700a80549000b020b24a0001504a00c40d00ca299000001003003140803000c41136101a4001e4441d03d4a00b20441c0d4501a500c0c10341c01c02d40f0142e503150000505041004110b01c6400905114000075504504d8070000c05490704030b8694005c0d000710301c0000d525042c40014010080944160050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 602074667 1250 602073417 602073427
    0x61507060b01080601110d05030421090e0603030a05040e09100221010b04030b01050d0507030605040b01050108092113031506030c09021812160b1c18020123 69
    0x12002030003400755071a0110702071201207001540b045408145a002000042c03003441600c810468590f0301c000c10640310205843d035000800641d800300804040784680e540ca0105040c84581820340f81e006d0a0365100b40d200b08007044001d500081a201124070f10300c0c0100c0150b4540a207a424007515020280314148001880e8450201103141805541d09030b1a0368491a0380784c0e449803890748518000544009401d400420684c03070684441e12103584508144c99015a80381d0b207510640340305a80c212002d5103060014081541d001d020540c0c898201c0c3c0082c6041000740700740f101c24143c10410b0b0a003c1c040020602a54001540d042c0015039002c02c5201c1403040c004042c4000f04240e01044900c0049928002180300709170090b194081c1c8954441d46181024404014040b0240000c40406001d0014050800681101d00400030140710180d1540d80011202c111109800c100c020110306240c5110341c1510000c42954181241e420300349021000a01c0f00c08000302c8000421102610034000b80c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 602075917 1250 602074667 602074673
    0xa17071a07090603060e13081b060f09010207030f1b14030301140603040c0e190c030e010b03150406050403090f03060c020d050a051812030f07051204080d0305061507 73
    0x32210700c60041542e07040840b0781c0f10780049041d5402c80c4507440c21401d400d00403852500320a0f1000c0d90251040384110b02e060100c100c44107010608407590105908031004112104201c08101e9910440d5140214600300c00b542d4060306c0c2c41500001c0d0300801045150607040b071285070700146950354100f0355005010140d0104543c0d03a80c800d0080c980f1040800e16a00554100301c429079018540c0055600b0b01c180c2040001062450010314460104030113030403400c607500591003028225072080d40c011403400500241c0900303482d00684624000d40c09495070184e1a074424548981160744018081825161800d0849040185070088012488104400004c011b00c1e41d0182007805002e4003a591500c610031800c1c0d4840c0a00071030358000c40e9017004032404a58021260b00441c00c0014540c8007124030f083e1042e860745d048140465080c030800200801031207810424250200310804400745428103001c100d82c0c542001200240a142d2640c022500a5a420107400302c0488d0700080d13252a002d01c0d003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 602077167 1250 602075917 602075963
    0x20f010608010510050a0806070c03051201060503060f060405060d02090a030b01080303010602100b0d110d17090f030102160b0a1b03050a0c09030210050d150b040312020f0a1707 78
    0x341350000364440d400e40000b03050415000c08001c1320600c1019082c00d0f03403164020394800341d10720000c6040080800402c00d8001c0442c034524043e242135030b5a50307203070314086040c8600991100c2001e803144005020812003070361448110794180e201d045e00540ca07850913601103607101409400040c600510080089684080040a54100d441a508550081e03d9107460301d000ca402d40840340f50828507403031b40140401c289909103d07401da40945800d11900c02501c07800c1002001c3c0c4280796002e100014a0801c51a01c59404841403404030001c610f0a004408401842c55800000405661a01c00000d88a40103944070f01c070552003400440d0032204502400400130708084950212542c034040038480442d1050240400390b9501400740300352406200030644c1c06421001c524130040351a003030300e01904040d039410200146000c200c400d44590851a0108903003100003103000c11503110031415840c00d0b00004000d4491a0402e4a1503645001d04d5034140d894441c0c0d02010b00b0080c1d020050022849180e = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 602078417 1250 602077167 602077171
    0x323010b12071107150203281116050108040212010203040303050f163609022d03010b0a0e030d02060a0b032413021203090103060b0c1c020f0106080105 67
    0xc07800303140c20740c0d6038502c055548150342541c00304613501c544401d000031207141174a03407400c12030b03401140d0404042505001c010001503200c008282011031070005100e811001c40d841c5000c1d0fa0024015102a00c540c0000301d06061040604110984011405548901c418400c840101e00021340d503900c0c007400c0140150005503441c00d11184600001340c05069040390074041c0044654031020f007948003107102004501c0903c00446441c054440c3c1000ba0004000d002d0004c0898150168030703541101c001c0c3d0030b0805403052901555450291705400781c1030200489041d00d009003140780d00d8942103003080340d00d5401c00d40d04580511442c0780017106907400248044c42100280307014070590003050145610744c0724000d008424110f004200300018460303c02d6059203e19400c01d0554a4002e903000035520340e0103c1c41c108181d0700000382e4001c4070750b454040d030000703000c00304071052801a5506405075950301588192801c10401c49804c2c1e0304900c01d000b082c4c01c0414040c001d1002c40d4803162040e0007032400b = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 602079667 1250 602078417 602078437
    0x6020702151809041e03021006260708100c02010204050604180b0105090d290c030703270b09070e0109060503100b06030f070c1a060102060a090b070323010b 69
    0x80c2203421420b030301d040c100080c825a40020742e0101145042c00540c2c0030002e00d0700072001d5004000d150303002d80c44a481184001d092000c409001c0c0c0c0d040e001503480540c520b540350f01c01c0c0e42000d04180451400002d03640380121041c1c10026110700840000c03402130045800443d4032420018000411035401e1200800b001d41c03150040003451940e0005460620412a000b0b4001a10005550200e070210b040640080c61955502040d100549601d41c00300c9411908500040b0703020090202030b036414454140003001e0b08940d40e40c0034a002c1c68550a030303250040000d03c0514443c000070a10981444520300401412114258a5841c4e0381d04402a1000e400f5070741c040d201da0fa403050030544890007210701d00324000e88003500e5503e13034003000c0010402c000c01040500c00041c4a41d00013492440112100740c0021031403645504202c1c00083c1040005040c1e141d0803400c000c81d00300070a06812203d0b07000052802c00143c00010050402c0f1010305102c3c8a4000582c403100010311035910000030102654 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 602080917 1250 602079667 602079697
    0x50a02010c090501120e1c03091203140c0f092d09010e010e18100f0606020312010e0901110f07030e0603090304030215120a0603050705010207030317040602070215 72
    0x181d502140d0040e079510810303000800d00728581094407165030000c003071445030100341c9402d100b9203440501d80304c2484000d02d00182e5242c8402c02844900e1084d42d10044131440c0034440c0124421030b044c910a00901609054100090488a440503980445003207480180110313803c031110b10081068881490882861403c070540030794482d20300342642d6410784420b025011082e03403c2050802240710010900c03881800d410484800d03100081042042003011108080340c9031070300b204040300742c2d132444d17002105651091181e562400d004d480c000f8151100d03607646281d01c1c2d448400190150503d600700c08681c403070014907140c0c214408401081603d0190303d50800c502401c00034040b1910088910800641090200f8401803801c51020b901c02c904510000e410510388102d2104042d000b03840d00390485a49a0040003001000e00101c07000303180c24006490039138038588000d42100e011012080d0031740c150308006800c102103903050340d481383d030040c105020710502e01c0046410f692000084c41030800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 602082167 1250 602080917 602080931
    0x5040509010e070b0a110a290103350406020124050319150f0b0405161211221a071a061201051620120d09060c050a0201 53
    0xc105002e00141c950200300184106443c140c807141468000010000c100409510386410342c1780c3c1000480310380c60049030100d2107041e07400c1604100102c1000d809035420300641c01000860341c206d821484200d500010321584e22910004851200c4d00603403d0390124602040108946034154880080b04507801003200781d003100d450442c281c0c400d0510503a41d16a102803225103000301001c1009150340c2c0b058101d1041c0c0d1071b0300503104060b2548110015280c0d9920165040c051400d0b0041b682c000103003602556811300381c0755000701221000381c090701c105a00e4a20b00f2074010b00f6481280d0ba005106050b1414005207071500841030046445480d6000c0c3d42e40000a0b03800081c901200c2680342d00c8070024100c1507001841440e10341c4000c0c225944035400c41c21181160703000f8010036220341c0340d181c0310512040c1d0000780070f07000d0901d110000c0c10700d2246e905410314241c000580080203520301a1100d44030780d1221103003406041c1c1c81d034004243c03600302400590200d400c132001d40200c3c66180c00030b015039 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 602083417 1250 602082167 602082181
    0x50c0c0705040902034902010b04090305090411090301050a0507180f230310050a0c080f0f18030d0504020a06170105040c0207090219230711010c120801050405 70
    0x10303c140d0100a513042d00020b0360840c103034032002401842001c2c462041540c1c03000350681c070854041156081d00c00c0c041c09110240c40183c0c2031040004c01d00c0200e5040080200b039850060080c011080c20600440d650400c1c0946040301c6419034600d6203005000b0b0156182c00303542a80541004c1d2104030100c2c2034185600e1440714042c107079074141d03004a929403444501c7e200b050900740701078040b21200c40c50154008041c0ba10248003e0b07404045100010405050062542003260f8800c0220030422805c8000d00c00178500c00044590000c44020381030035035444e40707040e103202c41c071701e01c00c1b506418440011108104441500050b118900071a080c0318030a64504054581d0318545904600e01110030005001514041d4480c40207007441d032040321b4100d521401404c00f2a80f0480301020002400040c05100760342c0314091412056070000428911078a50100c520680900381009010041048055085034895440034074100c0d001101000c40380e80000340038180250a000344c9000b2400c1ca4006816 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 602084667 1250 602083417 602083421
    0x51c030804020409061e060303020715021b0316230d050c01080907170105091b0a0303050f09150918090d18030b09030a02010b0a060813060f050c0c070504 68
    0x4980640351500e0540d07640c0d0030800100390304075048401c1565003a106c807a80145803241c1d286d82030b050500142c102e0450801030725280b030661201040e8405a00031880d101e5020410031904401e458010388070081c0003002030300304027051a220304100c81c80000000e101011035003034856650b0321200d05100c0503000c000c0c030898021120b40a0415400040d0100342540b1400700b00b540074520100766411941c464810100030544c09250b80a03507034584090156601042c840501e00880c210309520f20000d446001c11000581407001805015011590240507900c803c100c0742d0840c0c0c01090004903099100d048080e5410480d80c2e03a020300c0350344040d400d9414000d4000d40c0907201e100000c0240d51681c6408a680ea148520b4600001450010020005569000e44c4c2d018080003030103151500152070000f82120b00711007120348900c000c07400c2004070a07000003009400010710044c444020140341890800780011700c010b41c8810b07140c1000c20007180309141c05420b41459400544e074550359282c04002c1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 602085917 1250 602084667 602084719
    0x80a0807060605091b09032a0103061403061f090c050c010506090c0d0c030b040204080609061003120804020613031b090b090f091603051608061303110304030203060a0605 75
    0xf940d280d060004a04000e000006003400300b000500700c1e817909400310803d1201d023010030744030341000c00c2d06030034a8081e60309401082c025141c1748090050302108103000aa0b11180034002403c4448000009900d842e0009520000b5211100040c45000c214040050043d4054811440554a4200801d400f858202030041c0500b0103409180d08007240e42c5410402130100e0a00b4009140d41c03030140000760749071800500010f040e1180508503500e02011400d08107440103044a081400405007030002a01e0454140d189007a01e151200311a6214408215240300e000e2080800014600c1c00004010751004401000a42c401140101c80d60b035005440a136070a104481c0c1d40b200707410380011540038280b40318941c0080ca010403640008034000340136503407840681003901c0356000403007680000405504840010300c940b0f0010803080c40c004202481c9030f005100010100960503942403c08041001900d001d141c0013000d070742c100e00702802500010000c5114003402818100e100344103506103c02c40b20 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 602087167 1250 602085917 602085931
    0x120412030311031e06010306030605010e0403301a09190b01090e130f0f0501091a0601021b03010f1103180309011b020303040312030f060e10050d0507080a080706060509 74
    0x4402843d00e004130300800c0b0310007010700b4101580d0303180000c0403a2803801094000d080304100c40360941401d040042034112484481380907200910f410090f000c12200c4c00b4080b4852060001130190348411500d40c4804121582c40c1d4800c0c02034042c010488000403500b009040c1490f410080f6444500056034128401c2c820031042100d40350028190101075109071030840d00c1036500b4000e20700141d0361004000824401600c1980d9a21110340810024414040c2050354001d0444110320b081b000003950f8003000200241c0b54020055040c141c2c0e20300b500325800c011108203041c0304d01c241719031051070750760821240c602029102c1d140400001c03901008560707000744180c0d40c007903031035146200ca0300c02910100d000f01d804d0b01c810480040030a89002080740a2030751a0340115066549105400546030150084d8031074540b001c0c14080710108261000084a00c00c2d40c400c4070206250819909100281d4401c1025014001c1e4040c01c00c0483d8005144007845114108011500c40041c80350071242110780c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 602088417 1250 602087167 602087191
    0xd0e030f0a030e03030904090510050c090a0308070f0804080c030c0a141002030f0d140a0605011b020a09050907030507170d0509030a02031204150201020f18010212041203031103 78
    0x40380c070404111800000c0a42103900c0e04c01e0b080f01187c1160241e1005440e0354115100c0c084090b002d50041030340280e60240c40c80c2c20050b8000c0022107001040c80010100784000070444200304960902c1d0b8892500081d48039180c9544e64100c5442d41c0c8503101071880f0780560300c4801141e15200c86c0710410343d8480e490f115082c009003001d002100f01409040d20030341c8800c1c0110a4ac1141c040014a000102d044010030100c00300c10141e01010700103844a9000c5040100511259074450080f40c0d220304a40001d000c007186500114581c40c002da0420301d51030382031034104031070b209001030348504a9100310200c070800ca58800c00140301c10000e5594808a8000c21011030909110350068140914000c0c103641c0403050ba0790001c0d180c51490591502c4049001c142000070058000d0a00070851050000f94908502c0c41c1d2040351074800d060000e0711140502d207540215034030801400f0003c0f00c6002c1c02d2580c40e500c0b2400050000b02c40c207003c40000342060464003e0040c9801628010301280202d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 602089667 1250 602088417 602088433
    0x40501030b060c1b04111c020f090d050c180f040210051216030f021c0905030405100206061f17042109030507080604080d050c0d020c0d0e030f 63
    0x11000390028801c500c0e8400401d20064040e40c0d014844c1090015101c0c20441103070882105010075510080c0380c0855004080c006d008221030b007c3c0014450f05003180c00142d0b1000c030b50145120a003e5003085541080c5007031103500400000082c00004624100c820710b01410304100340c450a000100d0b240100302c102d50003c00c0050521412001071a12a402d1081c18182d0126000e920010111280301403514100d074000c1c49160144a48403408590400652800585a00d603091a4075000a00316505548500c00002e101081c41070301c019140003884440d44400c2140700a41d034170001c2e143c003445007010154188002102c8441100f804209840d500196510034801d1802d00b00000c1c02681e00480050a0207030300075114124405030f61071070700c075040650f0035402c0291903c00c0e02c0e00880200c0d0310030740500010600410031350341d011000380c4000c1510390311040a00418041c2000a0410500220303928581101c01302c0c03404070010881d40c590003444441c2d4100350340d410280c8440440b582020b82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 602090917 1250 602089667 602089669
    0x20c060c0f0f0c100e0115090231090227040c0f0c0c1716080f0c060a090504090819020c0108070c05071d04140102040b2b051006020c150405 62
    0x40600f0030301d5142029212000380211410042d59041c1141e02c4540c0d65501c2002ca0303210303105984002500d40310f40f0442c18004503444a075000803001201c20380c043d0f5442c450b41944c42c88100c058020700002c407000d40d115122440391070440120300182c2c1c0030141c1c58480c55455800c241c41070905a9002d40e5810310750000242040d242816108402e84520301000c4010420390810140420b108184400a0600d056203280c4015004840c1c3c21949480c1c0000c1c80c07070151600300042030301d101942200c001c0d80e900d003036506c19101030b41298043c07604282040c0440050103d1440a03105d0304020100c021502840c0c54800c0340c8403000f411075503000c22410008200c80512410b032141405116508590425440d003402c4841c12005208000e00c1c00702841c00c04c000c1154108050582d0000b4000035420981410b00743c1c01940240840040389240f040110304041021101d11802d0a00f040c7d420030460030000e18003203812202e4021040584a912824801414010030002c4032402c2c02d81d565051501b004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 602092167 1250 602090917 602090947
    0xa03290607020402161a060f03030c1203270703020f0d050604200a150f090602030304030f090b0c07030c060f0507140a14060105090c030103080d0c030f0609020c060c0f 74
    0x144007803440c174044004110000c1d034280d41c3d605441081d16444002843c1041c10854810592066980250800d20140c40400d0000401c0d6a104d09010011a2607981d0301203a1601c0c000c0e00c480721110200c800c1d445880e042004282c000a880c003d86002d5481c0c1040340500039116101800141254414400140410704411910324441c404108425044140c440040d501507096041758002d00d101c0b41044085a40001e0925a40745040c1082e103140d40c81c140b8043d441740802040507040c0701d0b1407480c80032750034490071640c000740002c411001d032541551140280d50711480d02049501540503500418503900817040701c04585129500c00d444e04c4800daa640041054202c2003000b04d11491060600182c140a507622410782ca02c0c00800840d0b15000c02c0100e00c0c1d07000381c00700c1c544010030401803010590380400c036044040e0002e07010500140a0401b18002d03c040e041e1100010315000c404945030580b50020401e001d103800448403241c5544004068030310035454442e04c0d010301005005961600c039 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 602093417 1250 602092167 602092177
    0x190b0105060a08161e030f0609060b0301060c0221030a18050616080702101e0e0117040c0e0a02132c0907050a0b09040c080402030c1c05030a03290607020402 69
    0xe152100342030f03034030003003179400c6400071415030303020a80754190004803110070720403070004011825062104c0c03460901c51000c00d10040c000c030810040807810907000d6490b030000c0c2c1038480441c050550500a802c1d85156102d410207196400015621a035a10520396145003040c195400104618980f002c80303444400040c403011422103601c4030601403007015a8507282d01070541400c0b0b8031001d8a0000d03420b5850401c220043c0c6140130302200560f0000941d9124424010030021001c00c03004c0b070b03201e0303040180340350259503c0005400c001c4001c0011442c03268000c0d241d445102e03041030050742d8540c0c00015519101044920150407901d08000007106c2c458401034102460000380c800d143e4480c004110500b003070307400c00c40c0c031302000062040c02810306100d4051001d9807407514900605140c0d0000e17488107440c3c00700d64800c1c5000c030b00701550b0071003242060b03001c107620004481d27a4144260000d009032408035400310100081c0d400c1c8007444200c0350300a002c01d03003000b0003041c0f614051f0340c00c10000b5048 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 602094667 1250 602093417 602093461
    0x609060f090e09011e1404030c05161403010605010305060d0204020f04090f0618090c09020a02030d090f0b0c0c120a0509061c051803091011190b0105060a08 69
    0x6911000802d1a032001826010b44062000401c001d16691244100c0311286440144140c0c980340d00451942903040819070400c0d4140b400d01d611400500b40545080c44104544d1540880084001251002cac589192180d81c0140e0003032144c140ea90005408403981150050f8002515078654401450154002d15062681d40d5a06060586450b121707000c0b9914140580c00301942d481c0c01340304944d4014150445c0c0780c00940107229090603951021031101c600d200d0761881075008180c80008034001d01c2030b14400011504200102d80103410101001d8440b200e0545406842e400441e421a204030121001c40e1000b90050400d03046000e080c04ca00d030310001c5c86504020042c46181e1b8155906002040c02d00d2481c240c44245200c40700c025412154041e0035251450030804810f01601c102005a44811008454104902d52000d4080e0703645005054a07a42900a158408a86041c0840c04150b07181c010038100351560380350700c2402014801c5d6140c0c0c00c082a50a4001003502c2c010401ca1909441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 602095917 1250 602094667 602094677
    0x1606090201050c06010b120a06050609130209060d1b03090f0f0309051002010f0c030510060e060d0204080d08091501090c0207091b0806150910051e0c160609060f 71
    0x500d0000c2c0d4148a030030f0f003011105039400507c0030101000c8a81140d00b194a008c801c1103054034020001e2002d10035401454010080c4051519400c00140d05071107020340041c0c4503540d03801c4145032450051003103501d0b040240d511400042ca41c18800d10407916969070000044840309000e03107a40c00c2c0c0b0754046034200c1c00c12460880104154031454034004040520b9000032580e180d500600344c043c0e40100110004140c5030030100900c84041c00703400000c0364194240400c104e42035002084003403165244804116000090002e00d01e180019141488861179035605069102c025030640c46800b030744c10140500d024803006010011540e8040c95030f0702218011641c500796035092010070303640600c038080c40000b030491103855000d03048030003564407010032100000201d80080401130540074480605004440b110b00d419592401403080b91915001c40c041c81c3c180c25000c000320549540a0000f911450140707402d182d013500c40c1d9090640c155a12929240ca2407070901404a80c18000c441034001009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 602097167 1250 602095917 602095927
    0x140403020301140403020c01020c090a09060b091509091b090a14101d06060f0309070b04090b100302071518020613050108100308120a0e15011a160609020105 69
    0x2039070911a110741c0007802400011545442d08002c0c0c2400c5458031040d0554015136a555031542c0e6010080380d2120040000240c2140a41440c400400202c48542c1e040100e036000c5c040e140f45852a040b41c0342c10101c07801046a55403a42031911181c66000b50408800e2481c03080d8402e00e45120000d0748483e1207d00040d43c0e843c510001e0075151001d0310030a0081c000c03620140320190700603e4201d0295444c40d03004c55607090900210b20507110b90755075001054030200104000c1c1cad60602c0b5400080a00d00551034a868480c60303624001e140c00f944151107400081c0b4150700310750090096038000d80d0001e1182c801e684032021294083d00d44081c5211030300518443c01401642d036030740907142d5021405181c0300c8060070103001604401e0f000d003c41c0741b40140801c080000907903090880e00c009116209205868450030581c41c050031f10103284541c0340c0104d03038001c50400c5429a419040300e03402e45005c0d421555603d414801413040384c03151038182508109110111b01c0d10f40140d03804610600d0f09602e0700c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 602098417 1250 602097167 602097169
    0x11a03131a0411040f0216020f04060506040312080f07021507121404051209031b0120010e250603020f0c010c08041502120f0615040f030204060b0f03040314040302 72
    0x41d1104640440c0c65446201a00c02c107404c01d8070685250003090310b0214508000365807083c49004003008003d1003890340004400164440350070840c001c09015105a88450320317440c040c3c10340017103a0215000201600c0000e0316591207160680e0055109070040d00c50350440b080d1074032082c00300400480c203201c05440940288442e034880c0d0392000540c292101c1c01c42c01c103450110700302510148086000c1805200c4040c8560b008510240b002907002c042c442d000ca070301c0b401079640030200c1404028000c60301c1c4211800b040103401401c0203061120a1b24840c0c2200146400e0070048489802c038445905041030000e64040d60040042d00d151141c1c0c941000e40e0102d460f42903c00c07a418043c001480c0500340401c21000300392120700c00e8400300d02075003401d03c1b050702c40c00c0000c0c00a064600c8198144045912034039007110328200d0f000081c00c4030351381c0c5444000303a0785143c10510040b03006520f00b41c40080c0140003002510f0600c0c00c4410442e01d1900c65840498491645072843c41004100308000001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 602099667 1250 602098417 602098463
    0x71b0f030507170d0c0306051e09091c03020301092d0c02010b030703030309020114040b07032a050d0e01090b040501030b1c05060402041b080f2d01030506011a0313 72
    0xc41c4c1040012418171460305e4020261201d5600450150b104d0651040728040c003032101041d1560152030001c482d81d44c00700c0040c50400c01100142039600c0009180f1003169041d0000c6050b10400c0409000d5a0465900c1508030900c4e0002c5044c08c0f101d284c0c1134a0800d003c1e410800326403a5520010450f0894180002e060154551040b03010a5881e0262421075800545268103a9640088d0508281c5040d4030308006120b251002010845402c10058101080c11150703072030341d581c000301c071400c1c2022458295030341d019a0014001081e020030f1294400d42c4100024000d41744000c048500b4149800d0064026203c88070396580e00032603100120700c482c1e40f81030824103468010742c0140210700301801848100c5121150800d10303000000c003501c48164008820507007103642c4804c1d4a21035512006a03078101c12054007880f8111082d501c0b00300e241070044403202e046c0d034060301c25150542d0381c0311040d40822028080074100c4a038180001006141038401c400b2015015002525a41180e41030b4210 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 602100917 1250 602099667 602099677
    0x1b081f02090103270606060f0f050a12020d2c07050d02032b031104082d10090b06012303040c0e0a090c0b0c07050d0602040302030105010e071b0f03050717 68
    0x384e003031642800602405514003c00c002411903040241c054068070300004c00514604082c8400d200f000548140102d00c1605402e00894041e182151640100c0c00040c0144c800d0a1003102d03488075a800c5000f40c900301c08520010002490300820b64241f410085c81400c0d0b0f544d42041e68503001c0c3e00300f00c0721030402e01e4013440360095403c91401c8600110300c5015003260304e0321f0b40b14a0700ca5000c1c4014008110b00080100404641245805e4400c55400401e514903503501e0003c02c45004a0202105954031504005c6034a0310560f0425520f42c0c3e204011500080307407824201035000812200c200340036100000b1600306002d20701c0343e02840d80381c103140e0994030416181e40401582c1c0308810010700c0070481c0c800000d0550105a1440d002404030354560b900d40e68010f9500c100f5000b821242040400d81c115002598054000e1013550b81d14040c00c18813180450340304010500090301d401000c1e40310744080100710b511480f02c0b070040c0e00c540c03000c89090b00300320f80407102d0062943c0b00c400c5500e400c2010b40 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 602102167 1250 602100917 602100971
    0x711061b0312090706080a0518070f09140f01030f030215270106080606120f072c102601090b090f0c060a03090317041b081f02090103 59
    0x2540d580303040492080460401009183c45801003201403103102c0d440522160010b001c07900100740d0703440b40d651000c007906034111010300c28032a600c000615000c0795099041110311219040004160300c4074249110700741220002807a4099000510009104020840f5801d000b1710484a40094681f207000d482c0700182e40d80281c02d0507244121511241c1c006c545051501000700a200c19890000380706e5480c02d0150030144607003a004d046068108080140210140324202285e01d000d83d00c954202501d44101100325405030896007118011031074801f001d01442001500c80c60013850094182c99841500d421034182c054803400e0f0845500c02401441212402401c18003224100b0710580da01d803204219402c01140c11900081720195520015074490840d075050101d07148029107070455020000c0084042c025144d8000d000034807003c0c071040c503c005000681081c40076125004555900c0303101d0754525000c811440203a01b0410f480c1c0242031100010b04000c01c080f0215050803044000c0740000c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 602103417 1250 602102167 602102173
    0xc0d0f2a12060c0c02130c0210150e060a0f0303050318030705010e0115060801030f020105041a040503010b04050c16020a080d050705010b15040306051f031104060602120711061b 78
    0x40180400d41c032400f12000c5160030028060603142e030110390003103216026054507981d10340503503800f5802800f081c218028080b07000c0060422184605030032101c180154151400c0c3c85000600d9410418001d009944011404805040ca141d404440c03d0340002c0c44441a0020708104410152080010708949071103080003195400300881603508407910b2140302560070f02c118004014031038101d26990306498100740c1d14000c580c5035000503120351140e50321800182200118000395443e400c0302038825a10110001e00c0b2459030f1004000c290740068032982d0340142c04014a510a00240744450810b92014004000c40395841a0342c0c1d0402c1202c15081c00842d2000680c4001c102e028440c2c070102a90032120342c40320110800c414400740c042c84c0001402a0358074400f08151403031a45844446801042694a5080d00c030b1400c10598240b0701881800359040c03580110b00c02c1d001042005031100a0f0203850700740900743e1209025084140646034002034200605403c600b000d502c1019504846001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 602104667 1250 602103417 602103449
    0x708030a02130b120403121109040e010905190c050607111e060d0c0305090601030308040b25091d09030a180b0f04030506011502030f0c0c18090c0d0f2a 67
    0x203414451f90b070341c1d0417000d5031404203e0a20001c922042c0c0340103a0003a540016080100c407241742c01408480006001442950585000314001000c5121800d2050401003006940e0314203101c00b600030200b00401c05940d12074088558203241c00007100000317200703406440b0f8585aa0118040d503000320341e44e42116488a81c403040715a014026180c108040100a10340d646c50754070000c02558000d8402018038402101050301d0408000030080315190700801c005e6078149068000c0d02a030340e075216070880b042c0d042030309030f0030084404030300b078454190f0070003a51401c180060215001140c00d90301d510903104610000c48e1350180c0c0000b52203508515807080707035618150f027852031621005a00120714100041e0a0071009a40802550042c50780c01c03940765150801500d56a0402c2458410903800001c090300c10f00c002c01c0030b1021540605807900543d05100001014001c8446042c4e901074089403184040d840081d02070390403814205500500a440320a09940c0f0340031039032084d80404154084241 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 602105917 1250 602104667 602104673
    0xf06180c0605031b070b011e031e031b03091502120412061b09090203060d05060a0522031704030207181e0b0108190b030a03051305060708030a02130b1204 68
    0x3640d50a01c04910b840b07030070100c8aa0b21b240c51000c050141285002c400b80c96074008041c9000c290019642c4200e282500d5100200141080d115280c03043e800205080030401d00511184a0000016016694010558244958418121184981b486c1144185100c004550951002800281440d119000318917585414240143c5c1d50307015691407184046003805000e0b41d000f00e52001100c07a911405a10b954600000803070140c900c1c20041c240d401000f041052000d02c03540064810001c41020b02642c10ba6050030340301511402c100140804e0385004103c0340030fa404450140c0c054443c1c81203a0103103450b501c00c2007165051142100e1801c0d290b40c010507030706030f00710070b40321002c00c02d06000c01c1403014120000709800c0001e050105e240361fa62a1034401d850098100415004018040b2801a0390314a0003d100340e02c4048904140041d1100120385494800c04485100e508141514123540ba4100504001c4d8402c0100e0b2066940c98503002442d0384e400c41c0507007981140702c0c0d0803500c1840c1c141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 602107167 1250 602105917 602105941
    0x7050f121b130e060f090f100806060604050103020715090f05010608150c07020420090f180402060c01090507030c0612090816020310060b09030f0a0f06180c060503 72
    0x85000340300390381c0c1481000c418900724000c1c9012104a10070f062500d48801000c07982600300400905d0b0820084810000c482c041c0400d024022030030b84207400d070100d03600c00b00782d40ca480341565080d502910402c02005258400d4010b4104140100008004024410071404c1160120142100d1100c1000e1b900741c00c3c40001c4c450000207200c01409004280700580306120b180340010041c0c3e041030700219000080d03485030741c051140000c07400341201c0200d510301c8030113080c1c0d04070140c2c05200e65406043c0986d9424080006120107070a4140da0003103858642c200031b10394000d0240c040041d03581b10081000700c0c008001c954021401040031851032070074036400902140061809000f06403d00c0b0f107110015901d0030440350000346040300500c40303990610000342010141c000100c83c1c10705205020802003040e000a1401c0381040f81218200c4680114154440f01c02c1390000d403600c440b4001d448013044064000c1d944110340ea0390900c5c80144c90343d07104e400c0ca0ba0b590704080d0000d0f00210401c80904008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 602108417 1250 602107167 602107201
    0x618060c0705100e0102060f040f06060816080106080c01050c0a170304060b09061521091606090b120415050a0f0605150712090b0403050c0a0506030112030807050f12 73
    0x1034134040324a4012100040e54880024280c505c1c2c2a14010005013403140c81040640d8181c0d01c4042070000030b65448e000c981d10015440d914281280010300000c0b0700c1414410001103030205000303010100d40010040d207454010408001071801403030034000010b075040415990382410714002e16141c1c2850b040510448010000d070f0390281400f1002d00c00c280c1c2e50700240010607014103e10135038400401002c100380c0096440e040c80c03c0c84a00c401d01c40c0440740414604843c40c04d03005a4409079585640c01c46d001c0300c03179104100402d0300820008080810304070790749920501908044e0400d103411b284000c11128111611a1099651140d2402100c41800b40c20003e140855807020034040c0241380301e42920460000800c44140844171b200002c2c00342c01218018a003907842c00b41c540d40e490800d251240404005d03d0301c82c08181201040c14507015096074140c074000b100c6001c01d10103a40e4151440c01d0b000e8036030014000d05100c000c0f22001c221004005d5080010031011160620805044104080c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 602109667 1250 602108417 602108449
    0x120a120e100e150d11030603010f0b0604060f0c12080f100b0a0c0501180c38090102100e0d02100216030815040207032d0e0618060c0705 60
    0x1d04007582411a03004070a030a403080103ca00b41c0c00088589420a4184240c02400203940e04000c0680c50808106005e07604c100c1055000384000041c0001c014210350402100b183c0c007040900050000c00d22403c10510307126058105130304010084d8480381760100e185040400042c21910402c0442e240e01d000064008020404ca40f49a9040005410346401811071402c00c00211030880300610509421565414505c3e80054000007100d0522455050650190364040c2c00b00112500c0407000b003036003441c09802c40603101507034400c9103040c580d07003035101050f0700d411481424035903c1c40b84081d00c00c8100005246000341000315040c2c3c03019062503142484075206900c1031024601d041180e01c421811958986455003443da505841c00d401e01c040940324580052002c1410820103403c54a158a041149541c0301d003a500b12070031640c41c81001284003400584585041b290383d04103180589600c400608458404c85046408030300107400c41c00310a501a03000005c2042281041070880c038151030 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 602110917 1250 602109667 602109679
    0x804091a03300f0a0c021806090a0c022b4d010c0203070c0e04030c0809060d020f0306181e07110d0c0b010803120c09120a120e 56
    0x800300500b840003204403400d00d841041101070110072004088122a4160059000c264603a54408001006580080c000300c1c010981c520050003401e40722042c180c40303420010101303c015541c6080910191403248940e009520400c20020049480d0b041d001c0c8034072803046040c0c031f0003551040004102c40e00300d01c1c0c0440210900851201c285800599840c442d11030b040102c65003070300c104001000c0301c034080c0c41d50350b155280650703641c1c40311760110003402254003e0700c6030320402c0d0301d42c181140c0303886c1c050341c0050125641268803030000318010050003100f04020100350420010200000aa2344070035140300301031000004200d202d161482e509280c0103100400350f52140b4002026891089101041550190301c4200280000f80b00701c81c240c0007450070030165840c9101c43d00c4084d0150410081c100c8045100c180042101c08000094820340b06090340c0111064a800c0016580340c1e00c003450540d04203501d0148240d0065040010f00305061061840b01380b04041c1440c018030710456581258841c030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 602112167 1250 602110917 602110933
    0x40606091109040c050403050601030605040501150b19260a0f0603050a0803091f0902090a05270304090c120b030109020618041e06051801050d0f06090804091a03 71
    0x1a414600703070b07100608181e80000c1c241d80140c00c252a42d0085a000410a00c10302002204228081d0130050007244140c0090154044200302202c03800d40d0f501a07402401c000f4491030201c00d1141480305010f030711509104840200340c0003450b40d00700540451850500316079042c4095804140b1500100e2a4180800c024141c10f580c1c0303443d220f060607070002d0101800403021491800c0140b2590008900307200b0094038682941010750082c12500c00b040e407088440c0000a001e500d01401407038401d43c0400342048a0b03440ca1105a0480008049000d030b19120a20020a584038244103051003040385444820034200304004c020240c4101d8820b0340d00036410315585000684409041e1803031000800d03504110031032090082001071007456507884000c88095480ca40124482c0d00800694000783c03a2280d0410900c418000d001d0001e00c50545c1290341c400b00c4002041c4954504000a4481d0901246071038090301ea170311340c0d90400d03044281c447c1e0740c502100c1e40044468000300ca039410140c0c0a803482c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 602113417 1250 602112167 602112191
    0x2180d05060106050703180303030c1107141203040b0706150602030901050319090c03030305160311090d0201051201080c2701090f0f15050103061d150d0f030804060609 74
    0x314418481c0303c062040c045200d400f018000c0241617aa482202813681d091a40c0c0c0c28014058103103a180c02d4080b80e600c84221115200100e101c030103032100c0d11031301c200e45038000080c40490b0140c0745a144060200b8000419084180c07c000e044441c050ba20102d2113140c2c25500b40381103c7d07203910540955004004a450690700b01081c0c0fa40b05030300c2c40c0046080300000106a01a11401c0d000070280c10402d0400b008064060740101d025442d01120002001e40b40c00040e0119945a071441c8a882418030202e0450703e084060407118520600d0040d0400e4602c6801d042c03040002c1e0025100d58210988003945410078100d0704c01c041096007110b06a26404009110352018103000303142402d9241c4880074810740e07241d040580c3c1103114140c20040030400b031480038801e007114051103001904000000640380c4401e900c2c2e070321039100c41252150b84c0d1541020441480c81e83c0c1000c580003400108200301103102d51000da4a0540651200c03542440c26107009401c03203a443c2c1100c401e41d0b03c0c1009034410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 602114667 1250 602113417 602113423
    0xa0b0105030139111f0c0504060233040b06310e0c060f0408070801021c0902150304030e03010c0809070b0304080c1c02070909080711040f02040902180d05 68
    0x10002c59107600d40001e40740d030411500208982c040c0301c010300c03501c1e034600074213410810181805011090100704042d61b00f801250740f48030b07501ca15401603200ca4901c0c048002d0305440c5a804d640700c682c1c2006402030959050344040030454041e5000413100c010031142d803e22400d20f000184500c040700e150440340420005000d840c80d1181660240c1d68038079040070b08410048440d500a0007031141e40c031a000105940c140358014062507030300b4042c3c80c40008040805000781d480e540c5040d505490106410040f440c0240f20901080c0d9000355290414030003128910001d6004900a56500307c3c111001d1060500303643d131417a080c0d001c22030042c041040d241c03030205100741a10010006540d81392214108102580180041811603005400013896800174105005032481807940075620300b980c0c0d80300100b013111180d8401504070340007001108002803015041000603030f402840080d403c940074116804a8026410407103459600203200462150040c0c440c1902d920102d4107224803001d10743c3c1d4251 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 602115917 1250 602114667 602114741
    0xc030606030103110112110c1902030331140316080d39020307061d040507030e0a15110c07090c020f0f0304170c0915040605030a0b01050301 62
    0x7202d481c20702c1d025482c1c6c0c03144032180211040803c0c144103034401d42d201040300394001801c404991060003651404000514950350030640c0040c003540c02c0c0540c81e00200142010120880c1c40311480420b101042190148004082e0207005162611100414207251400350100e1941990080280041291420009180084880514041902042c0900c001d03010040c40c250b0054840103224461465080c40e18031f80c1d843c1402101282c0f5802e95881058980c21003041c06801403500c46004014503040c540c0025030081d030185000515041c09080d06414030b03810f81c00848440c80b055080d03000c001e819004124915003580c00785ca161420403200c06503103004910901a015031180c0f408850f41d4028000d1501180000e019101840103d1a0341303a01ca0303000b4068000302172a2002301c540f81400c005050044038a01900c1075600d5207420022549860720800c0a0b075020361280c10207d12034a060001c4421035101ba2808182541054209030070740346242301c0382d07192906400303031421000c10b0310400c0d038 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 602117167 1250 602115917 602115923
    0x105060f0105090f06040305010203040309050613062a03111b0a051309020904060c0f03090b0411040f0633090306050402210a060c0806060d051f0b040e0c030606030103 74
    0x40e6142e0f03000010135807112411240561200c03010400200707010040d00113500c128401d9844500082e1100200290750107142c6000c20312040705c02062103980d0040600c0001a001400203e01c9440f08100e10848180d509904400141c402e000003c40c021040029100000350301080c4151000c0040c04500150a188145440342c540000f51021313200603030740034650f0b454019018074101e2802d410110b01070701c402600c1d04009429940000c01c2d5510038403a1520b8980d0100c01c083c010303111525205d40054070604016402a07498207418904030700307842414010100c0c03c020900c61520403500341280c1001040026811508005124004d5400358414054951202000a5076100c7c0d00200f403034590b042801c05850b03240c400d021102d1200c001200d00306544110410302c078407041ea00d01140c6040041c1c42c2c844e0440c0d000d120340350042100d80c0103a607120841c0f0881c00006420155401102c031015800b1815125000a040c4600171402e800c7c00e0f80051603181003851400d106000c26140d200c144005 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 602118417 1250 602117167 602117177
    0x260703174b1b03031b07080304141204080f1204080d0c08040302031005040605060f0a090b0612010f030b01080309010909090326090d020f0c0d2415080105060f01 71
    0x50341e442540c4030540e062095120354003444210b40c0c00d5040d64a50080e5400880001c090400b034101c1c408003400c07079442c95800003405044d9119980c079134100c2001c2c1e00406405015075800001031101050180c4002e1500750010a150f0b00c02c510703020305040c401e152100d1044800c100501502c00b001030381c80d5205c0103515103002c402255007844003090156400095044c01442101400030440c0d802141c02280911000c21a40e10340504204081501040040e040003060208100d04126980031040d40301001d00440d14141c641d054801d42090300340c00c680e07110b8032549400e005000350351001c00d014000441c000c40c5131441d03010018125952521801e003403036841e084100101480383c00094800c0c00f09803640c0119556401002840306001c8074000c80074030988081104081c070014060f04502c012101401c402808281444005200840c05644004030703a0360312411001c040741000514040030f500043c0e110380480c0c801480352020390240c10340b40c0c108401d01c402d5980e600319031002c9080034240 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 602119667 1250 602118417 602118547
    0x1103031618031208132001030b040e03031501020a0309030b0c0d1406010e01050703080606031509130605060901050120010b0604091a060426070317 65
    0x108450301e926041c001e8555404401e000000c00451140c9100c0c41c408a8880d80300e255112000c40c10040090240603080c07414420060ba81714004541e07250b41a007040c91301007869100302d07020070290f40c991a100d000c20351001007040401044006000b600100c01d02c040e0003918450344006240f298a4040a8084880500890640c2c2d400303108440840c103554205101c4c05070140c921141d043c408039906804544003e008044a602c90011a00904d80c103486e00501a101d000900c0015000141202d1141c60300d00307620b1072240c2d00c0c644000d10440855500c010019014601032007030341e00181880d800b6070107c000610540ea0050401c401e03401240d403040c0a03da010903002800360840c00403054111000040c0482c41517804d401c40b091107005041c0a2140c032030600140042c500c118843c0041034440c899003d00da0740310400700c8404608200c0700303c4d51a41d46986074003101c20480303020303200e50b450700241d20007582007200b0150f024a81c0b8090312601d00c5100c001d0741c40c0905208001601c0206070408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 602120917 1250 602119667 602119711
    0xc150c060c0306220c0207050301020a050d05190603050a03090509100905060d020a0b0c0114010e130f02100c1401060e0a020a0c050303010f26070b0c011d0616110303 73
    0x258500c140070b00405540c4c22400c003800c1c07000510880c01804014000e4400c0802c003403c05008580d1a1580313555405d1030401485202c00041c040502941300c0f14a507811141010b00190080a0180d40150058100354419107000741c1000125804180107009910030007500100c215603001c211a040500400d190b61038000081c541c40300b02c04000d5005048240200d490070941c03025000e4024128000c002c1a110664800c052810901c41c03c898040301d00001007122a5002844030142d205d405d0422010186a000806801c114a007000024180c0042c0000380b080c10912400150003420003080600c2c1000d559501c5400c2c006c081e5241c1030b40000e08814602e01c501a40c801998001040ea52256161410b0381d10803282e0f482049021040101440d0003102450406108481c680c0002c1121915222020005820002c0b40038040c0d503030307069000d90703641c54000c400351040e01000c050000e40c94280e2141807142c0d042254081000b003041d6080002000020890b034001480d22805171050000036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 602122167 1250 602120917 602120929
    0x61c080403060b131506031103060a170f030a0c0201030606030e0a031107091e050916090c0306080a050d0f02010908070b040804050d06060620030a11030c0a050c150c060c0306 77
    0x180c00716084520304507040030901707840352590b010341e800c0340d8051001c5110592008804d00007507072110340c015902d18042252110001402d880c501c543c2c0e05540503046034480d000d0841c0c002d22a00404181046034510071982e15202d544040c204070300b41008404104d107001551180840c1004050110040480c04140d4040001a006114074581070203800200000d6807000012030030704041050500c40840c1800e030000c501070f155501c1500700039080a00d4101150040d14280d00b20b6001d0607a50300c40458800405d02ca12881b150080005041b02e0700011002040c00000b07045803011a4905041d0b1000987c5110450f0a8260420300c0b0014648590170001203901c541d034841a80008114449410416280c000350121059902d840342da0000042270141c1e06450488140c513250400c2005801c1a40203d14101c80c4175600303030440e030810219001484c03174040f952a084c3c50710781c0b02586c2d002443c45c205506c101c2156034480c1940c2842c0c04400c42035035941e4083e0011214600100c001402030301c81e6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 602123417 1250 602122167 602122189
    0x1107050106081e1b030c040c0504030606140102030703120605090106020c10020d0e061803060403120b0904020f06070c0b1314040e030a050c0109170c10090b06011b140303061c080403060b 82
    0x41023080240a200301c0540681d0207840211001801c0c0301000485c5900950f0710050007030181c014500d4006603650840e040000d0340020805176655200226036078451920107406440d168000380500d40d00346040100700f040d814480005c545c80813014a071925030002c10940101e0b01500d10340e4071260300d40702044000e007051040c69054840d590410003410303032210050600c0451840100710032411002480154501190003035000b07442040b40ca0303645c1c02e24500900c01140038030032510a0646803542c0700416400854011103180308001d0030303c0040e00f40307201c00f07641050171a0100640c44070201215180d0140281400c24010040f400c8a00048290000152650b001003003008110f039220030307545560818044c2c00050f204110449030003950034131030108481d803c10806d0701d2560305c407401169100c08032803000e820b1740d8644c0074100004049a482d90100807103613016503141d1800106001122a441e2101c581d09080400700788003283c92801100c0680340c0040740441d503100c051002c5038540590b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 602124667 1250 602123417 602123419
    0x7020c09040221032502010906050a0f0c020609040c02010b0102370302160f060807051204350304030201050f010b0f090a031505060405010f271107050106081e1b030c 73
    0x40076a17032100307099a0b43c0841384041c03007600c038054815212802115180074000340e0348040f0307100180c03401c0c00c2d900039040040c01c5031000b4042440c200d900c4000c10103072440780c10150050b039146c640c00e4a41c0e68043c4503000b1040f400801240d1001c0700403042400900340034000e9405a1090302d06d00d01854800d10541c51111500043c0317a004641e100c10040e200c80c0d80b0721502d400a01c00801203103801e4030400c210340b01c8401d8900e00421a03160f170703150594040304280c0754043c2421503260040180c0e001380c0074604014604c2ca6525160b00c0c16060190a4820060080c9000310007540144070041411007902e5405075106007403601c80300d2440210b00c080407981c01c05400b828080140102c1281c00782c01461040b10700752401d00c80ea90fa40e04071580740c000e0a0043c1e03192421109441e8031003101d424403104003000c6450010580341500c040c2031529a000c8001951540d4541d0005c0c041e200f410041c900c420780c000641184440054000980c0303500c5194868410581c21980b581802d035010410001c00c444 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 602125917 1250 602124667 602124697
    0xa020c04022d03010504060f060203070321110d0b0a0509130501061a030a0b060310030b1b0313030f081009050709080f011a12073b07020c0904022103 66
    0xa540b030501242c10034490b161003603080150108486035141d51030b0003200e096800940c1006540c0d40c0507940c803083c80d64003004c5920444032134031449409015020202846042c0c45640300402c00c070070070954104182c1140502c02200d01001542c803410f40c0158450340442004008140c01d107003150140000303900160700010306250010030708007148015409900420b8040046000368402d12410f400103d40c803407040d50340c4030001c1010901c482c800c0342d444840541200880794501e1501c805940065840514400e105d4100c0010580c201003119080000c40c01c00c1d859a107014442051004a0344c02042c2c1070703a4032080440c040c0b0380540c052a0103040341c001518040c071601540c0030300900303140031140e081d101c0c1914174140d14106101c4034122410700c1c0d0301030100c2e02d0402d8900c6444024036000340318010100c2e08000c001c44000030000003585461151208a810f021900078070301701140700060710400e103400c203000040e91411002c1c0c3d0080c900c1ca10700b8806855a102580c00e501900080c200c40342c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 602127167 1250 602125917 602125987
    0xd02150f09040f0e0c0933010e03010902010503011208090604030602070b100311060918070e01090b090a0311032107020906011107182307090611072105010c090501140a020c0402 78
    0x1450903d014100f081f401e0ba101c0341c00500010405090725800240a4045401040144600c10040000307001160180c80b10601d03140301400420b455034015401661199404551941003040d0011510380052041003091441421360700c9140c00c200c0101a140e1042c100042e00c008552628a04aa030040c5080f040710558507189070003410304400701030000c0c001040c0100204030007a00c0340540d1428403001c5c1c00d03c40c140341544d80b10212866400d01996041c442c2e5411103100218504e005100b0380700c0030385210f49071169441480705404000e40309505005079490103c0b01b20400080a40448000680b5201e14040310110383c0010421003154803400d42e035000710480d22204540c412030041c1d04956490903526034400c0b003103c09280c1d00480c280310b41c2060008111840b086590022520000c080070303032951015940c2d075130071501010100404a0442c4800b080380f5a0400c40b00386410001c94002071600e4032001000392035520ba5440340307100325408505101c0050300500e01b003410103011400081c1e48 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 602128417 1250 602127167 602127241
    0x603021c020a120b2d0102011104090204030b071b200d060204030c1a0a11030d0c021b010f0203070b040c21151503020d02150f09040f0e0c09 62
    0x10100001c114507046040419444c00303810408040710741500b0840380381500c02c0f25141003941e098082c03e0a0f504564884846002d0300410030010402801d0400d070042c4e4407861454002150000100150180150320900c6291160300c8001150302541c01541400318080716901c00e500c03484080c0e65150800c021722010420014142d004000307990084c45030b0340d90f440d640d41012580382e01e41c11280c01e0a0900703002020b40036004d502c100d00200188000e41e81805c0391b40d90b204c003c450000160070300680c4038000324012080710800842c5900e000b2b00e020000c0c01c2160402075981e10072050010140c032201d400103018004251300100213400c405040510380c10110000c03c2205085450560b0031444103100b81045864034856032a520b0600d03c44142000d1458003086448a00920143c1e0454500e4103010070028405004001c10903000501649486201081c801240c801e1b102c0800303080d18000001c1072600e0300164082e510070080355088250342d00d50b940501c200007490802d440e1074400c10421412 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 602129667 1250 602128417 602128427
    0x280b030c070b0a0612020d0512030c041401081b1308030c03032e03140a1a09250504090309080703030c02041a0904060e0f060103050d0206011e0603021c020a 69
    0x1c81030095090407120f44030030606a04031340284c0714016070440e070f40b903200c8014105207082c408864090003d4a078200b10001c803510380f0354400c4482d8007860030001000c1c440c118488510b0b089103942803034405e0b29883c005440314052040c07101c066640180100c2c2820403c121070303940102030101042603e8954210250417603807500b043d5421520707546811101d6607248510040d030b2241824200980c0314140c034645484485d00e140b00e9001d0003074010f07450300350702254141424011689000c1c40c05400c9241c0207803441c1c10041001507540f0141600c0d17086514007070400c10001c050303840488000800828500d01582d0b0b0a040c0e07840800745008440c400424903402c80f0345681b001d8002d0302c080c043d4030031404a100c51142280f85507a0b0080900303002c280404e180d41d1140b000300100d0011500031345100d040d40c03854003400760b0040302e10360b100c0d04a40b201140e05002e024010079100c825032550034800c94001c00c8024190181d1000c041d0301051010000d10018580b0041500c6610119501e180c1d850380102 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 602130917 1250 602129667 602129677
    0xf250315060e090318150f07051e010b03070905070e030a0305030a0c03060303020a150204080a0c05030f010b011b02150a030203070f020f0703110a0b030c0a0905010e280b030c 77
    0x780b5405404009125101c000c0112251080c64441d2002d611085404000070309240035240482482c0034031030300b41c0c1d8181d0702005010b8036001f04000c10000d40e5030807145526a1402c400b50945904096150b1400e8500150348815581c8000002c40c060fa03c01c18111410402804220b91500c601e054450034513030071a00840c010f070400c400904c1409a1030a0907000d4580c83e100050040e40034016100125080105540c0b603408910000752070300356260152403404070100c20a452018034032404100328542001000ba016107200300901c8964104400a051032241e0510b030740c1100c00e08010b002c115581c81e54460300c400d409001603521a00c808800500a400c115509008105a4190f2203040c0340005000c1c2000306000703000700350302e0342144d8900802080200c2055003118111f507000c502034034424044c42c4507200c01d007441a2922810000103080154560200b4140180c1840e0b03111643c8a00c5500030440d20143311901751400f621001002888007580100300e00200441400700c0d40c0200c00040c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 602132167 1250 602130917 602130929
    0x20c0a090e03300708060603040b150a091401090506060f030a0b0a060903110d1707031404080105100e040b0c0309030c0a03020610090e0c10090f0e04060c020f25031506 74
    0xf62a0381c1d0b80c004c2030f01e10104c1515090351000b81070001500150800d04841e2780203150301000080c14200a010030146a410307006201195158404503001403080e103c000d0051000d81014006400d281d0040387c41403188400110741d40301c0000000302602c1c5550040b018018004d01195081c50342c50350000c001c0500c42c0403c0b660782903400c0a26541f0b14000517401541d0f9040104031242c800390a60050707050f4043e2404a00740804003852800c81c10450010b000240000d13000882c50785496501c000c034080d0940c01001c9000a02010300c4045984280010391102038100304503569150148102d146004e00b00c01c2d40810300c1103103104000c140d40803900501803644103181d00205034803106010280d503c40000900c1c0d541c4100c000410601d042c1e004848191060306080001c9500d54480340f0302054541c106080000031b4000340300800c401840b61442091280c4054942135030700c0009a0748a0006108416100ca00c02c43c000004000a41240b802980d00150003050307620a0112500600381c544a01c0d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 602133417 1250 602132167 602132257
    0x1208130b1c152702030f16020d0c030f0309060f0b010810051509210f0d080c03070c0c08100905060106110a0303020c01140a1a01020c0a090e03 63
    0x2001c554403140c010781180304040c12202071014100b001c0c0c3c00c070400c03114044154104086001d08038403181880214000d0000001e40704440c5040c034038503039440961030012000c41d44400c3c0c0c2c090000e54020307030340c5105039494078209440704071140c01100a85560700015112528104e44103070510000e51084410381c0b001e032036035900b554420f00184403000030391090a411141913601d0ba540d050888000b4940348030b0003800101c519040b4101c200051080480410141d0300131080c04480a030104451112501513142ca044d941c50203041c0c03a400303800090300311000d001c541c402035010020b10740c2001c005400c01c00101c41a0382c220300301c020042c0a20031000d481ca4080d580000c1901072080d10320a407102c0c0b80200504a11805680072002540210800301c1255a200c0f10740c0c00e50b81003054564003035020007802180c03011800740283c0002c1c08100341541036510000402a49494083c6103104130380b81d50380002203c00c3c11080c0c05003107224848801c03013080d604528042d1110b544110080000c0550300503 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 602134667 1250 602133417 602133457
    0x60b0d0c122f0607020d0614040c0b04030c09050702010608030a020a03090f030b0c030a020408070303080115080f150301020403080f03010e0906010b1204030c0b0f0711070b041208130b 81
    0x610342c600003a080750b200006001000181c2941414030050922a1018118942122150300e400d012101001300035018810140700344402d00c415a44c1101c0603001400441d8905465550358080d55031461050032065038841000850060003035002c0720040c24042c3c15655a29000303c8000e4031810480e42c11401714840786000318000300180c2c6140142da0380561521282c1c0c66040c600901e540000340f002c5111902000049004003080c00a0401180305c2c0e282c900e510350414040d1682e4404035251141088001e4042205803500348120300c2c2c00c031400680b403220b0250810080b0740a445145c20140c02410005510b840400600d0700460489150150a0301103440f00344496898900a00c1000c010300024000401c040d0040103030680c00c00c0c80f0b41030001c440e20190703684c0d0f00c107450110380540810210200304a4407603000011140f0031581000a0100e003410101d801da4103000d40e003d090b001c180d44194000c1001052030444407184110f40b00380d1036103a40c0d1365440001d0b520000c0895041d200c00a8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 602135917 1250 602134667 602134703
    0x7080d02010c03020c1207080f18130b030d050c030d020f0706060501022a040e0f0a1e030c1514040606031a01050609040c02010219180b0304030507060b0d0c12 70
    0x1081c2c9440309040c0002d4260501b51590403007054100301029280e41108000341c00720304002100500c0210502200d00010240040c01c00103095081071400c04928240810b410326540c020604100c0c203001d500341a61104822480545103024501d00d045d00240700058070040b02c2200c1c006049040d204004c2403201c0368a6500490302c1c1c58061044103200c8103a160751500c1d03000d4108402450000c05000040c0700442107010340e14020010780200301d660081304030b030b0060040781207884600001441180100d403101ba54001c10201a4604c040e0401c44e00221034090018240c003c4403040c0d20000c9202d00070f0525040c884005c2045100481e89220307942c41d0901c417820303501c0791113049400c0100440d040c208801d06000140c4480103020046540c02c000c5964007000811201c003401850740d594141074607400d5018259104a0f400142e0301e28400c0c01000006640481201c0145510010102d1804020000304881e030702401c17070041003600144808103003000c40440320414980034101c10360034401c0c204 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 602137167 1250 602135917 602135921
    0x4060f14060a0f0f0b210a0519020f0d11120721050f130201030f29060c030708070c030b012d0302030c0d020612040c030b010e0903030109180507080d02010c03 70
    0x84181c3c5050301c00403108115800c1204060141c00004078807601c5051298041c40b0301d001c1e01207c5001c07501d13a40320113201d1180440b04414850340a8003408610b070610300c0034010540d00030f11103918140c1e6100d080320b000d10030240041e10030400064000709244d043c11000540f080840a0701403d0650f4900d49400260207903020b4940201400394610003903482d840510400200501c0060341410345501444100682c24490011000d84d03c1003854074100c01048405415004007160900c1000148004035042001000b00c42689a0180c1401e603030398420320705502c1560180e40007034a118110300000440c03601c10844400c2c07180111110b6803500d907000082000c00c800c2c501020350154001c0030140740303a00780303210028007041c0010611400d15801600100d1000d504640c22247c1c0074048000b08108024024484d004d4800c0c0389800035203141c09030040b0307603034001489003850103501c81041400e518825404a40400c0c0c20009441c4025150401191740707507400041000150b182210f800b520611034 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 602138417 1250 602137167 602137169
    0xf010905040f05093721020c03010f050417220603020d0b041802041512060e071514130e041a0117030d0c03110c0105070210051e04060f14060a0f 64
    0x3070b48014603175042c0f0000c40c590501d07024004551006074100c100340340c0c42241c1d43d01040031600340e0017892490b01210605007034a00c82098091038500700382c14440080e01099000700501c0c052141b89843d210180c01d807480c01d5581e03c01d107506a009420740400c0590303064009261400c0d0400040c411541c40e0000d0100320380d02d044039003d02024441c198801803609800103170030b0004510000340d0b0f650304c1d0494250814019071040b521203030f550103481c00302401800001d00030022020700b00e00c00800707020061b042044d02c500e101c1e5041e600140b45590340325504008000361244c04c0c0d8042c0507140504d04601014030701c1090f40c0d048160b0800000e036410004120141a08100c4090742c00d000d4101a80ad01500901c40403000381601e49608015084202000c1e0804586c0c00001040c14200f0f074102904100043c0011266a4100340800a4002121807140d0519915403c407841390f5485040010003851001c07812401242412032020095000a030814003540c022a0180b03034031a078580703440e4610045 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 602139667 1250 602138417 602138473
    0x403030912120e010e04111209010203070f1101060b120f0906090a1b08160603050705030402010f051809010b0d050903090a030314070b012607060504050f010905040f0509 75
    0x3070718158502c1032295241a11518060404180707072000c9500042c180c4600d01580d950403503010444100002c0018510b0360400182402180745083c813032001084929404420800c0c0085840705803034035036096000d0001081c0000c070301a2100030782c10103410319110070303100004400d200001041c405035000c103400b0300488060300100a00e803010360350340c0c14800602060003214159070400046080091240329100d5400044125100742400320240c00c40b0070140c11f00c810030400b481003000503608a90042182a00e90810300e49a880100034080d202445c00c414680080c5040d0000800c444080080c05070004008014045607688800321603590003402e00da01da1040101000300301007070083c284010203000310100b03d4604181d039240d1a03404c1c0d5082e8800c11b00408040c01d1030280040303413400c4881210810000d803211502c0c1840040c658041c5000c2e0512605c40c03400da580c101e038000c12000001700009401403001503040c0341c162006110032111075181e4040c0364050301c180c0d010816000c0c9a111 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 602140917 1250 602139667 602139683
    0x51005040e0c030706110a0b070201090308070201090c2312071d04320303040503040905060619032403080414060708030c0a050c250b13050906010917030403030912 72
    0x86001801c07551000240c41b161a64000d180740d41d4082001202003510032503091f0008244281c5600d401030801100810399021649000241c0000803001c0312610101da0080364511780c0c60315002400f517407003080c1d0400c04c1c2e4011141c0348802c40144000c17600f03604035201c02c103080c8910f5a00d4160a001e0741822180246070518a00d038420308a81000a810300c441c01c4c40c20b080341c0c1c030074902000c0d501e141c3c0240c03400e541690010070100414551030140d181c3c012005d8590600b84203000140d20051000700f8031600916448142e681c903107000c1440710106005166001208143d964145011070f0341c0a0300072554ac00c1c4002400c0c9c28141800021141d119602690b80ea28660320310f0f190000640000030810200f00c0100300f401ea145000b0001c0d19403040108207050546e050070700c400001c0d00c045521444a00700d00f440522504102000d50f0011a0300c15112070344a6a114030040300d185c84660886580080b240001900000c4000094016a8800d4441200c843c0d110070f00e0f0520004c1001d00103006417 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 602142167 1250 602140917 602140919
    0x4020304020126090610120609061b050c0c1008040605070e0a03150c0804120e21060709080129030f070308180102010902060406121103010801020903060a0506180712051005040e0c0307 81
    0x140c280c9e44002105c81c010321000401c024800c08141003e0a9000d1400005402190914055030180043d804440c8212007140c1418a920800340c842000207201400113981c5030300040401340220351281e14408000c01021003562a4500080e801d911001c1c4010140c3c905035048038050f0060079031601907500092002d1180103840021036509040130b002a40040545041d103001c598030b04501c03a40003916601410075441c00e008001c1c0002d05c2580046c12030f0781807441642540d465007224002140307075400fa13400c0c0c075001c50f4003082c58a107840805031100d1041d4040001481140f01c041c22004c00204843e03100ca4400e640121b00b030f83d40c1040060741c400c104010400c503107800b441004650418038100815100b4290724081c589030400d900038541039400050050803031a0502c605640140940d1b8100205c3c00c208010525503249a26110700000d400008210018020300000300c15088a000c240141d01c2d22101d0b10700914014420640943e0400c2c1c500d14070342502040700c403481c0602070010000d00e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 602143417 1250 602142167 602142173
    0x61d100f05011413020d0f091b1412010204050d030908060705030f010b1803070e010602012f0a1107031209081c030c17150a0509040b060402030402012609061012 71
    0x100d1400b80c4c00360000c6908114882c007140780c6002c1e08041000343c000008041c00d0a0803e8014800e0003d0784174036411100d0740c01c2c4940c00d1040060801501c040e9448240d426007111503d00910031078026070350158503112010105640301040400b03071810306040e103a20b52141b400030f0b16103010584d80c3c0c0c55609015030041c0101554107016010701841c00d03007030514182900b070200c1c0c10903d0350b401c00f400b90000e5034014080b0720707024028104403249085000384d041408031107203081030001d180041410381c000100040e42c00e00c00c40d00f80403544045000e94118554901d4020540c100b03c84000000c00d024020000c2d8496020a030742c013100e030405803e1415940d185804800400340b40e440301c0e00303000441e4609102ca851102540e449112800c1045030b41f8001401001626403083d44903d03c40c41d00c0030b040100040c0d003465416084042a17802503200e0b00c85100603181c040c581403280f000761440301c1144c590901c0e1149007500400d451425103029880c0d0207506d9803d6400c0340600383d01004416910000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 602144667 1250 602143417 602143429
    0x20609150d06060206070e0f0607062a0909020306010507060b060c070f0f1e06050304030c1e031202041203120f0203010b3a09061d100f050114 63
    0x50440103005905644401000464603040144100c440c140d03078200c1801401c1c0c040140c1ca40041c850704009241140136000249030707040a042643c0160000301b84070041004580007145808d071250509010782820039540042c40440414540000c1d42074070001442404074822a40545810303910b2500d031079204e890740380240c05007016a035008681002604e507024030606c6410090140b0002500e411898080b00c1c4200b402c03660400d040e054000d6a0b04c561f00f8006082100440e41c403402d2407074030307541c45003025210420740342d4000e0a040000000030044c506103241d081c0956103e500e800602995000d150006c9006901455a40f10036403c030304000300e07004030044407000c61041c0001c00c0301d540711170444041e60800e03070000420b20408109403a0300f00220484c16070100d40d00b0340c038120300c0304c075a0120b1015224440c0e540804660361442d0809018694116041012140c03542210103401140342ea030341c40c0c080144101507140750140004862002d0b004050483e008620340d003030301c40ea4800030084 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 602145917 1250 602144667 602144677
    0x5070f15080705181c0203030a03022101050a031704050301150521030307030e030d150302030d030509030f221404150b0304060b0118470904020403051005060a0e130206 74
    0x104000324100c5d6100183d400700000c00001c9001c4c1c0e009a1101c2a0a903d0752258203481c00312201d040f00d0000500050f103444825100700c80e040900000341c8410400c41100d248242d4000e44d405508041240c940000d0302c2c22480121039064541409500109443e480c0c8031142d584c0700789094000b000800c0c00984650820a556001a0243c07450f05006906807400c0390070b0010031940c00700c080c6000b0029490207001040f0516030340c0c1414032681c50324403500c907128421240480303400c0034045800030b5100d09041003400d00321017811400c240c9a072516625502c4005551041d07118900b00300b0410403880c008040e450841d00700c034070003d08645035583c41d08050702194103e24100700c0c0c1d24803c41540310352650580014000d40480c40a905032841c0113001e0140c401e55080b8500e0810104508080c006442520380d403101015038a85850900300011301a20490344003400ca8032503914142039405465000a000d50011905441c44030b94400b1480c11015088454003405070424002401504056000741 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 602147167 1250 602145917 602145949
    0x112141c120f06080a29040f080403050d02010510050618040504030e09010312030b06042d18150510020607050d0906090f020108010609080a0f05070f1508070518 71
    0x4180c4040b66800001102c000780d20095280c0c0c462005035042c06010005603442c45800c01d0304041c544502e0032002050400136000506600340e0403282020f10036020150b8000c0c42c0c0c0700d01550b07410300300410000c0c06042d05480c0410380b50041c0b000000c1c2c40c039001048410075500c101c18909001905c00401c0300824000780103a09001d40880114840d9480c02880350195115000400b60b03ea40c0210040440702c9107040c01c1e009000804c01441206030b82e404150020600174115044900071035001482c6044a901c55010a00c2d4001c14081740c60304c0d0b070440340c1d4171000181c01c8494107540c2c00801042c90786004800300940c224602103007581d0702c00c1005000c900801c80700403510700145d41e200c1049510900055480d00074088a0600b1503074000380d0381c0c7c0100714034580b81e41c0013402c000c442c60301c880081c07a00500000f89000b1359000c2060901c500030003080d6280341c8580095882d5883d0501c0040549204001100c45001038841c5004409039540007840b82c03046100d90260800313010307180c01c80880309 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 602148417 1250 602147167 602147171
    0x504050601240822030c060513152a0f11061e090c06030109050601030f050c04090b04060e070908070f0b090d050a0b010605040f06020105130206071a0112141c12 71
    0x141d010348a101c2c0031400e8034481c1d610f402e8068078034148007040f00e0014002c50070341d1b09d06103105408921841061004000741c4030f00040d540c15600780403d0b090621000034a04410b448038414501900407034100280851078a8451401c030707000c8941034654504a881d001600e07801d1440c5291800321081700c40d400380740c44045412030110000003401a030026030200e501c081c2c80e241040032a5905d400340040f80e00d906103060089040c40c05804006001d00d01514081a0741e0340ca80401c2d13552a1b41241004200d0008a0b05280c01d18600c01000290741e4002c040c001e20803c54001420042070103188101ca40100c40d0750704000300c04003000b030f0b90030031800d082d01e15100718010b06011a480c103110a00a1400c1d8964580d514070b020ba10141c456080c0c0d00410569141004101c190940d101c200d43e0100c0e8102c40d40340e640e41a9150040302d40490022102100002c20700124058440c00d40c0312031003500800c5043c03031044103d020380d90b640b04042c8042648904c8803c44033800350250301d01e017000500704800 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 602149667 1250 602148417 602148451
    0x106140f0706110c0a0c061b240b130603020301050c030f01050f28052d0d0f170702011b0312270320070b03041e0605090105040506012408 61
    0x140c916100d5079440c00c6c0c0b0700851005c1c040050035003244a24460900304294807200c842c00340ca0303d00c032611044075020485029040200b0100f40c1ca036104060000000f0500640e00700b040303008400810b0b02e400200d00961a00002c1410728032203c041d24410003102850745410383c2060b041c043c07802d51804000d908158400c28038000800c220210b11040c680a810400d41a0318240800c1842c40ca2400807031210700940000c4295440401c1c00d9003500042074a2155040085207003600d072135800f503200a021499404006c00111282400500f01e03c1d000b66a80409194406940d50304030003c03210050209401911141c0c1c000d455070071464490000b6034070180002504400384141c015a07400440026a10703080440444407180003d15030b02902c20000c0595a00b810280141440050f00140514601d4500c60a45100d42c101403d402640800140101d0030f00200c014042e000c00d480417030700d0380118400459041101513010198441b90340300110788840d5207000351200440a001c2041405442007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 602150917 1250 602149667 602149687
    0x1b03050325080d05100608090309010c0c090c1808070f050111150c0c1002090303040515070c0f0e070e0145080709020702010210020f09180106140f070611 68
    0x10140500d81c3c1c080c44085168a840070201028128a40040090250180c140440e032140007058820060b02802c01e904044010b040c2504c0d00c0760203a2117800040d04048401510a9010140da0400c2d01d9640c1185a52903c07090201d4460303119020b00c3c00c40d204401801c0141d98440c9007030034442004407040e18407001d110108030091300703000c4880d901d0020000840308000e080c108100442080d98140840c142024139002070303128030552040511500c01c251008100c40b02c51021100d2046c2c0c0310021200e42c80d61402c1951a10160340b00304d03002400ba1100043c0290300400407828100c505a644401506040d00340714410b000f001c04002e4080140c0c103c40c03110441c030070000d42d070600b0072103001398140b8074007428030b460301e1015040003501c00c1c014001980144d03000502c08020151f001405600c03100010206d0f00c09005a0544580c022810a0124007e2020202490580b040c6588030807140c0190080b030141403180c5584404e8522342040b940340424003940c440c050800c40316031241d2030408401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 602152167 1250 602150917 602150933
    0x50106030305091e03060601080903221401031e0509011401090509061e040f170307030b0f0114030103150204031a01091802061b10060f031b03050325 66
    0x90801c0380855000542c442c000c1c84c12200713030094041001c0d440b010071584180444e807506400b4201a051004010100307154800510030341c1d00500c82c5040c03032108442c10040c031102c03404c981d12880704a918103102c207007101c2d4801e01408144049202c452101020002103490040a0080050b001035507a040080300f00c1d160400824000c05e22620041200d06112241d10300304034000d0301c4c007405c581c0401203142c4450400000382c0d600c40e4100300000100b04187c18101a040c0c061044441c00300da0000400100681681c41a90010400d81c3c4c500c4e100001c0300019200d50f80c0088805d8401f0000380010400a240d401c00184400780e2020054102940c0f980e607c1001468148805000503030f240040c411007001e8410184403210781192040400d250b82c01040540c0703d81c1900b40000c4494045445040c01c08102283e540542c4801c1000300590390300000c0004200c601045500410311095a00700500d155036081c1520f41000240d4a000388503041c01e4403800503460718184410919010801244001e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 602153417 1250 602152167 602152169
    0x131e14030d0b0a050d020109090908090405010b0316051c020f0903070f0305011a090c070c03050f0f0712030519120501090203012108041e030803180d020a020306071b050106 76
    0x6407001c80c98404500c1049694041904524021010501000b0150307900c03c0041c0101daa03084e80000d141c60960818002d54410400a03039040360400000249100c503080080d07110b4244000211403545031039404849612407003007501034200b0341302044074208030307203500422a440c00c0741c3d201880d002150700400e042520300e0f40817070780101c00001700b0810703c14207000f000400c1c0d00e807401036183d42600c0c5e00002c1c80014040c142d035035800004503229082003503020b8407201468100044801d503054200c240e03a40c6194402980015025601000070700c01c01004120030080d40c140c4031582803849071340000301068803500401040080c1141c0c10b03489892940700e218080c0c0b03462400941e0f25810a00c0c11502c0d103c000001c1442c5c0641e0440c04000b0072031100c1958150340650324196003420b40000061410140c41c2c0000d0440000041840340d030395440366403031030020712104c1610184000e184042c1e031a400f060001941607000100041d000311303c100038001454000d20340856410041c1d13141c0e14211034203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 602154667 1250 602153417 602153437
    0x1c050408120705330603190b190b03032b0204060c030305010806280e030c0705040c110a08090402160f03092c0601050702030a0501090308131e1403 65
    0x140300050010078030000d84680360038009802d41090394541010321005020203c82d1544c00d1001007026039400b0303c20020b040c080b1380a0f2160b400114280400291025a1414100f0a500f00301c00d481c0c43e141c1c0036420500d040100030b181005001410100400d0b40d0030120b0000c0004260031200e842c005102802c00740c841507543d11642e240318900601100c106802442071780d4003505c1044107000014000012060000340f4903c1100c151011880c082c090700840ca5002d40404070703140400700c00000710081214000c85003440490a10f80c0e007511554040300001d203030b40e000b80096102061481e801015a140c000d040113191069100b01c1c0311540015001c1200c20a90f094004402e166000c0003e0014020712500b0500f101d882c2c0400800c040401d41107000f0303290034400040e41580c004d10540d034038170350042c0940340c89649034508075001348054101240821002800701d440301240c1018403054a034030240d88203188004500c0c1c00000d120480b01200c40324503604000c0411402440a4009598 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 602155917 1250 602154667 602154703
    0x50a0212040309090c090e190609020d0b1e1809070f03143309010917031012020a030b1017011a030c010801050d030311030106050309190201021c050408 67
    0x410104c44100361003051522500700807442805005182c841d41ba4641c02482c6d91120a0440d0040003000000e021958000d2036650301c00715048022150541100183c802c0480355030820301001c01d500141401c440945903040f0800c018500c00c0107520901e450380041c030920803109a40ea4401d11100c00034135036002103d5001c1c840c0b2480084030020001046200324800880703501001c108003460041c0a040e520b00303580c00c054408100f42820a500103140c694001003100e9464051a80c2d824503944180c4081c0d9000c140b0070800180f8099107505008041d5009100343c0d0f07180c2c5552910102210060100000900d8001000401c0565501d040b96512300c1c0c08000704420301710007182800401c01d246501c0c000c3c0c03c030000320350551780e00c005103d05403601182c00c085414118102200141014440002d801d0000000864810b420a0155100707800e881e003140c00e00d202c447e10340082140c040a000740568441c602410348460302440d0201440d02c20700c0e01500705a91501c1a07480d285000c1c4001d18181 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 602157167 1250 602155917 602155919
    0x1103071502010c020c01050f0d0f020f040302090a02040b04050d02130c0e10020304050d0b1305010c0504050901050402070b0601110f1c020613110f1309051f06030f06050a0212040309 80
    0xe40a0107081102c3d01140040e1442c1c0c0c41d041c1c00070300507101d003068042c4660780004428040c6042c941c85a90500c512181c01c54940c00342654140305a4468001a44100c1351a07000078070020a500880381034a4001002904041c0b0781014408d102c0c2134903004076070058041c12007501000003441403072000c28103a905e114100d02072605210100c82d40b88020ba0031900300304001d205a80312800c40f201020361001b4841040da447d40c2c1c00c000c0401c03000000804a500b01140e4464256010000e4008c0c0d800442d00290710380d0b622001c100881c800c1000091180040744005092980074003619600310000b041604d2410035512030190600c0301005480300100e44d40c82d003000c0c03910ba0400c001b0754400c9000d803500100003800d888589400070510f40c02482054a511030f00c0017601d8803440d050103140a42814412560f140c0b0b0880d84a60303540414110f46502124610460307001f9028510459030080441c050f076404980301c000c0600002440d00407200c0d001c001511040f8a40d00c4103600ca14043d0751401c0e101 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 602158273 1106 602157167 602157209
    0x15090303080f1e0c0304030305010b04030302100b15040803130506090d06180b0a020a02010e010c090e041e0311060901052403100e01060f050306160c110307 69
    0x104400000d02c8214442880617500480c46a20240440d82e01c905002082d0b01980c4400b134010303400580b001380c541c80654040c80b003050016104002e04440700f4021006a03001e94044500d540c0000340603481005a250b81e04094117040314181e1030f044d5a40005140084038100240032503a4400840c41600324006100d0982640518668200e190030085180290080074500d00503508007002011b0030f50701880781c0460f540030703621130300c82090804081c0744a0180040040760042c0c032071a94002c0c1d0381950400b4003002c1e403103a43c072000340200c40c60003103003440009041e49000360b04250a100b000d6100590010540c00640a00031054840800191400c1d00448080c2d15451611140e403002c8601074120b5410b40314910f001700c41c055541d6050554624048440b8500d660503030b010f119040e44180c0041c000316010384203c00b00001d200001034200b004940c4412640b08885030b4034002 = true := by decide +kernel

theorem cover : BRFrame.Cov 601978417 602158273 := by
  have h0 := BRFrame.cov_init 601978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 601978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 601978417 ≤ n) (h2 : n < 602158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
