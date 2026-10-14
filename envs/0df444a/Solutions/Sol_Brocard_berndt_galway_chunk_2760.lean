-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2760
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:39:20.794985+00:00
-- url     : https://prove2.me/submissions/4681baf8-e084-4165-91fb-5f951096fc8a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 496223021 ≤ n < 496402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 496224271 1250 496223021 496223023
    0x60f180f06020915071b051035040b0403080f0c090f06190206010504051602072106060b2109120d0908070c03060501090216080a211505040c02 63
    0x4140e0aa001200607a2003083c203001c40c4080c2c0c1c4191900c200b80070003103a5030040c42065502c0780418408599100f004a03100c0b070801c800c00d0041441200040c2660088a200303008c016869040610215100010f1002040c604401551b04603011684020180e052004064100d84000c0d00a4190308180015190980c0c0d5081e40d0b010740c1d400b89110b0a84244800c44a48400b01200d1001070000c428070380103400351030013a5880724288241b9000b5443d10f80014243c00044a842c640da000d80ea001d4803a640c40c00400315801d20180391514044048040c040c4006113051142000910b03c03420034503100e158030f007102e500c10302d10b00214070350f08040307541045401c13040407500100e1944940314440d212492401c103c80207000c02c1400501e410030001c3d42030107015200200500b02c0744a0802880300740c1c0c0703a0081c072090380109400720540c8200059040c00280040f8041d00c46c0040514040551240c482444d00d8840541c00c00a800c140d5640301c1041c2d0050049940d8015001c244c7e0180002a907000d002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 496225521 1250 496224271 496224293
    0x503030405090415140a02071403040e1b28020d0c050606190b030c09030601080f06060d150f230615030702070305030a020d030b0d0203070b0a030f0603060f18 70
    0x20059203882404100103030459100495044180744031521781e15082e500b410096011040940d488c0c900ca481301944003600100300c030182e07850104010119150001d589558003038852203410365440903c42a03d0100301b5600340071420590041010076400007920185c1000e5418030b4910030003100d0351504010450002e01290402d1040c0c40d088000300d10240202c0c6a1416504941e4182078000148003402e40c03088050000707031030110b040d241c0507681c0c4c0c0c100c5d030759031480146145095004040051501d140004001c807100740185058100c0e40354803940c03d4110750030500350071311465643e4200344181092010382c2d035100c2d03800c2000c04a113003803c030b0008208800a041c8941a6180000010006442409848021644801169110101070202940319242c6006040000340360910740200c610388458081942500a4040e141180c103080c090b00d020341c4034041000906440d0203090060b4a158032454000b140034507400190b8a032030980d9039051b90580e10558802e09003503800b03440454424115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 496226771 1250 496225521 496225523
    0xe040c0f0f050c01050406090201181a1305030105040c0905070e0603161e050c1b010c12021f0e0601090204081203040c12120f1107061103161b05030304050904 70
    0x41040ca803802007000b00c0b907600c25841e0a01c1207509040a0208200c0140c105205180c402d1f20307120318007203090281e01011031403841a50ba5480090000090741c082c110000c0c414178402c451700319600c03521b0320003103801e45a098804a4110780c690b04100043e54403803040070340168251601035454001c60b40060790760f0002600c4045139440840201c1003c40c02117681d401c111943c00240001d554000304040c00c03a4000441c3c1c541580545011602402100c03540929450030584a1708030741111b40e2541c00c00c04038040c0041d815807042c603045c808181c0001000420740c100c00707100803503d00060301c1030303504240c0c042c1d1026001500501061240840104981e0700800740c0740c010980742d0356141420b04100c0801ea1000454078050f2010400344004401c4510b4102204c3c0c464032441084180100e51a60340c50b884a0600d411500301881b043c1c1c410840885079a5070b844c203c90400d95002c2094000103070001048034009243c0083c200c45c0303101c3c0c0310180d009080480c065810580fa00c00420441200100 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 496228021 1250 496226771 496226777
    0xa24031a01050c010e0d0809010b061c24120302241b1303060e151b0a050d021605061308031512070306020405180c0d090816030903030e040c0f 63
    0x14880000f10002d40c0100c0320180c04004035034a00c3e80c0c05401501c6c42c501505c50311021350038185801214106502103940300c2300364811010390400000d481c1c4009003190641d40d0420038891038600d003c1540b0b00d030903034041c00e8080d070b1610f40e0406038940a46801c01c02410300c031202404100d50717a2070b04000c401e04c80d401108c0c03001004940440310f805142512a59810814083d84007a0101c140840360740b003c042003c480e0102c40c030001c400e0540140300c5004949000341a5003104a12009880380c03409001100f40504081d8101130030342c1c05243c20382c0c000010903560403800d450f2003410701104014042d00621510888011030034242c490910b103200080210940d8510200350401540b220365402c2030090166003076624154a91034030750081d40c41841401c1c4540c61030b503442482c0202d800160380c0600103810071315181c4a01e40c03070840050450701205490240040c040c03001100c616102401c9100d1007a03035001429811441e026042d0701c0030000a60099251421542c0031030b401016503030f10900141 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 496229271 1250 496228021 496228027
    0x60503070917030d14060d0303181a04020f06040608060d11280f08100f02121302010f03090809010804080f0408012c0303070c030e0a24031a0105 64
    0x4040d10591010b40c0142001004401c0c14101d810303010014050300340522030280315500601c6800001c40c001a1030341980028900c00242c00640685d015149070061007040075110b40041d2500903c0343c1c460380e9030802c800380c14000c0208502d85880300600c0070320110307941400c01c1e0500000401e855001000c142c000c0440281e000c044c0f0050841d0118940002803201003481d040d811401d051007490020810b910382c081c10041661132562101005540e00d8100410044003241080c0c4081e21104211f00c21842c0c4c01c004d00440e00b0503030900a442550010071481ca4904688001400c00d0b11880300482050b160030407500000f007940c4111604a082441c01030040d0315070307040508007841102c0320307281611000280042d2540301900019240020f0126100c410343c030312030b55030546c046a150750b204640c1081000800e10f41c0604410040740707000340342c001004040d0388089054005a5080111564040240320115000c42030100180900c41d01d001d0000342d845840c0c0d141e040d100401401d06004000c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 496230521 1250 496229271 496229281
    0x61602030715150f0816050102010b010212030c0c12070b01080a03121e0f090c0e010305120d06050604031a0a15060e0f130902011206180c0c140d030f050103050304060503 75
    0x3d1940340c06051940c4181c08150368940c220b65641030b2100485024244d8000006401d600610a101c0640e8040c0c0280813440b8407660441c1150348000c3c18400c0b60a402d10680c907928104102814010580a0225941d143c0f01c0c100080e20703140507800901e8507401880c007000002d6000c880420401c48030400421600920f414403009111000c500050081ca41003200b11655990740020310401d00543c0e480d0603464a54444406255003400040d045910030000003000b0806000203000c40610400c0010704191210700244040d842580150784003000188804171402c40500f140c2d40080c2c0c02d4404201c0600541003a82c40f03007009100e047c0600030f80002031469074403403030b0000d080f0403001021501c001c1a0f010500004245410050780029264050101803200510030401942c12452403901340e88640d041c014090324890070700070f017081061822140003400c0c030314040b42c2d12841c0742c000d04403004108800800b06e4184000b00e100c0c0078140801080407074400700032038082e200f46140003030350b907954 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 496231771 1250 496230521 496230551
    0x206100f030303090515190f0b0906061b15180c0d03050309070f17010c020f06010e04080706020a0e030c0f090a020901090b0c010515010503240a17061602030715 71
    0xe6000610b1546e01d50504001ca00d442d000f15802c0001000c3e1400c010048041c03801c3c404039050905c02c55004880180810349a20b851030250408030301c981c03100c0310017295200e81c0760b0622030284580c0c04001c4104041c00001c401020f164540d440c081001030911414201c0050400d003074109000e0180032000000c11040755090050401800f20351101d1181d16556910118000b540520311602c02d5180c2181204c5040c808031719520103020250080c90300364240140300030b440c02e01402c200c038084400c024040001d040c034000b8000c10b03400f9848030030010b8080d000385400c000e00c0e105543d1280603118190303403103503980600d1030790850800d503070061325400081c0050750004200d1708802140c1c0302c042200400d10a054018501c6001803061b21084001844011360741c40c0001d0342d60481368440101251400c844004400e01d03802c40040008080c20340e280d8803000f120340484002d44254018500300b0504000020442ca01c1c01b1252004501e027604588842a41840f207a01400c0403d8075000c0c01018051 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 496233021 1250 496231771 496231783
    0x30903170406150f090f0203100e0a02091e040506090106140f04030c03050601060f0804020603040303020c01090b0907140d08041502070506030f1e01140f130e0a02010206100f0303030905 82
    0x11082d07405620f0680c4800103904895400d04c030740c4c1300a504010700e2001c0301c11300b4001d603402000d00c0030510360810f062400079143c9000050600c51b00076801d010616541ea2000940003560311012100c585205040041c0410b84200400303850041c00715100400c1220b500c00798070321503034481101c501d48032080ca0f243c150840c441c50b071015240c5160120084140500892018100c600d940c90788016230355402c00c02d81d00000b00311006903000344203000040c04a40640c00500c11102020000102c1c1c007800d549900d101c12050355900c602c0d40c0720b03d4051110011003070410301c20b180304035608400e6200a41d5400d00d01d20503801040e4841c1c11519180c03403094002c008050103820000c0610b41c0301e1501d0159082141404c880702c1151840002d1700306100040c0e490784505036102110000c0c0585240e0007840441d0030a10484c0f6004074942c40c1030010b090103445400045545d25001d00840d10360750000900d8010003034104c01c500036010b1010003002101c0c4031824101c07503242c01d01042844113403c0ca181006 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 496234271 1250 496233021 496233041
    0x60f11070806090114070305060f010e3706030902060405042a02010b1c0209152107030b0c21070908030a020d09080f120c0c15090102010b01030903170406 68
    0x120035101400a10007040d081050200d40300d003212006a61190821000e4481c2560301c103401070306104002482d07520500e0f403c2c2e04cc020150504000c030410700099110901d84888984a1030420b80c103048200c1203030706841e002800e941c50240300d11012900042c2440c440d5110303541c8555900d40380750b50801208943c2c8007180080030720300510901101d4029003e00182d4503120300c40c11504145242004044035003000498010f44031951aa41f642c00d4006044440303c48641d104200703088410403901080200e4011611000141189518515020901030300c0a01100a20380c0c09010580d4244541c082c00c0710450101e074018030345522416030550f8140c2d00b5401c410540e0000043d201d001d541c00180c103990001c090781e28101e46030b0350b80014944a43d80c008482d4002d80010103034007514242a0040d06a8988003401da640182c503100014203060110546102040b4010070300007820343c0c0a2041c61a010800c0c00c3c10b0014038030341c0e6401001441202c403800441e08001001c039082c00310a50000d1031403 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 496235521 1250 496234271 496234273
    0x1090b0609150d11010207240e1c030908120702090f0c250201020c030d0f140c010608100b0612010e040303150b12010b040510050706110f0d15060f110708 68
    0x7000241440b846080d40d15400170701610644500240a0119480c219010308507c580310300ca003111058200d540900202d4182d84c000504c1480000e404440449426a0b5100f0b488113003c4e1807614081500300381c1c0c2c44444841c00d60781032100ea0017584ad400f02d1903500c00e00108821500b5900d803810340c50f0a008a45001e0034054486002c0a03003204180314081c07090b4000d030200ca2803000340004250381c0381240c010b1440000c45000e00b006419000e0042c2c1d044a24094082506111001d0000b0b400c66000780c1c0140d40940c094907906450010b10b01c602811210251501440d1440f411017091101406101d40344902041400203802d00d8800c0e880302108542c098601402d459980000c460345030041040c07a280c40e4004000001c00e1400c1c00200c0b803c89070b001c0c215140c0c00300440e20550306a000890b050b20200d03102e010312042c105103540200290004202da1589801c81003540400711200082078001d01061100184142034001c02e0b81040b01000b0716080e0394504020035600c0c01c081e000d600841079 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 496236771 1250 496235521 496235539
    0xa06050a050411090c1e190806100201060305060606030a02160c061404030209040807080403050f010c030c02030a020615030a14060f0f0709150908060403021b0301090b060915 77
    0x84045250030541c080c80c010f15400201c25142e40800482c188181c88810b10035500700640320442c908000d2407030450a920111500384040c00c0741d00d4200c44000700c43c00000603000000c0010a07d0401342122412603184001c01105017175940b0170742d0320280940301600c07a0102000203034902c026501141d21440c0f610b9150348903910300d45420113000b8500d000d92000f140f850a1a000c0d029142d20a48045940041144000f030b10745803680b100b1a40051415581c1c22000c210100208900f0441174428015010001a8502c10030600400301c403052448501150010407030601500d42c0000c1c5a50002d00d000414000590520002841c104080c08010005481208849010038021580b144660f5132540446000d41d0390206600c61900e00701c070942c000c101d903008184400460105140c02c01c02745410700c41c21030f5403210081454440c0846089006030312002180c030502da00719003c2c502c2d01d0f00540c000d20803001e403947d070000702c80802812030f805200d00714002041280c003050813884200002c0c201100d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 496238021 1250 496236771 496236781
    0x200d030207030201081b03010302060c1509070602100c020309041113080313050a03050304030b0c040e01140a0602061b0924030a0b09040f0b2509092f0c0a0605 70
    0x921104640b10581c0826200303000184090b048005201c0c0032009840760030719580c203690030407046400041c1840140e2085c0c68014441c0f07401050245c4c0900c182c0720003400414640368009280c05809200509140d003040c0300302c050356400000b518440e003000c942c0401e601941c1000000c0074080e84816038011086900005041d401c040020200f51b4001005401015120003e003e802c01c3c0520005165030b00400c404c0012403421303400c2d180c0080300c64003003034a0190707654014603041c6400e03005400c9101e90b56000e82c01c68034101321004000c14040c00509081d15000c5513040c010304031004820801030001400403159034400c0300b995a4181158031b0000c0c0708808071100342580d00103c84426155181c03040c1f0300010319002c04510320480c0c0c0001d040c104000e4540e1456500e08010b0800d0b112090f41091780e100104462600c500e80ca40a9a20780d4041c40c41c000d03000d0306542150030010355048030481c1e003c00b4421070300410032115414042c110f50f1582e020829031301c0d19a40a002070f0a0a25007001c1c05 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 496239271 1250 496238021 496238023
    0xe0d021f0e04051308040e071b080a120e1c031103161d03061b07061d0709051605070503040902030a0b100f2a02040504062a0c200d0302 60
    0x290000c501600c0822069039640c0c41c1c68039080ca082c0005d040650107202c2040700c0070b00042e459078000440e180c80034016072440ea40b040f1346501e20000300c0e403656000c505510220742c0242e09600702e1568042c14041901c61405080d11441e48203402d1090300b0030b0300101c0c03200c98042c0c0c004019144444802c16542c0c98000c3c00c50b1300d00440642580b00241c000c200d002d2124800482d58164650010007806243e1517440c035000076101e070049906220131080c80403d01144c01841210a503400300060044070341d644480d09801c011035600300103c040e18260901081100000e000c0b40445c080741040c5584480c0350404505c0d5000340c1c1e10020300d550000040181921042d0006018401c05490315078140e030055009940c1201001a00c3c40012088449219014a0261004082500e00c403011603c416240c01013003d91340c00329820b540450300c0381e143d03030b554200c011440501e001d5a24002480c00406000040040c00c1c1c000d0081c0070611038802e04403522140014001d00710030000c4ca06040410503190107 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 496240521 1250 496239271 496239287
    0xc0607060516080103200f090a1d0d021005040819050c0706030c050313140a14060609040201050f030a060f24020106060c02040e0106260d020309010e0d021f 69
    0x20580840034071804420b41800b41d400349058079031211100c0012034928207800c1540e64400800c0381d0208101d08209003580702c2c10306441c0a82054440402c40100d000d51900c4032046603008603107160701c94000042210f0b80440e80d8070010001c00c1c00801c15450302d003000000fa020720403400300c582ca501d1140030215a0010700801c5d41401c03040c29280e80503603a00054048402c05070360000800c50800000300026a00309a10403120700c12201c01400c030310106162071400911100031241e000c0039144d04030b200b040800050b40d01410468541c0749914041c0e000825030700418041000440c004404a4034050301600400c02170018070b2100380030700d90b03500c95401c1107a808201e44810410400c245c9821345106000b540300b0b41e95552a04c0003484140d0f800c3c4402044e10162140b0f895680d200c022a816510848060095030502c125070070b42e0490640341410030007010480e40540d4010400145266001408000888411100c0e88030300d416500225660604a4100d070840b002070000f00d01781036400c807003c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 496241771 1250 496240521 496240531
    0x7050705060a0606080106080601021204182f0304050304150c0b0f090c010518090705040e010f0302090a050c0d0903050a0e0901080303010311011b080423130b01020c06070605 77
    0x1101c00d191200d0b0505402c86405004181c0021020b00060140c0b40c0103410b8250854410320440d032510440038020a80c80d00150407003a8940314005003100c00c5151401910b10301c0184081010494462001d1404c60828200307401d2005100480000e0a118040c400e44e0000c0000607803282036844601c40060010400c114101c81006008001c103080300140d102d17a51044800c03a0003085041504030040d186508480f46601d2407104100e123480113500c0e2500c50034016a0b0030b8541030b0b20b960a00da1001498801600242c1c0d04501d054010000340e500d1071030f000d8220943d00310024a5854081100f4845c1c86540c900041480c00c0c41da480e03081603400300080c032003020b2039a54501120810380c10015030441c20b215401c9558002d100600124103000320350091342c40141008a401102c0c1c5498140c50554498155400840800c08000f00b00b90907454859050806e40b050341003a9641000840220728546042d00c4075540c3c40900c02940d00803c000320021000610700c50315600b552038102d000e010100c030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 496243021 1250 496241771 496241773
    0x911070c150936060909080a030e030f0904020901050405100c02030d0e030307060213030f0609110f031504020301060906180f1b0807021005010806180c0307031e050607050705 77
    0x80000c80e640c1e110603041008071995289115401140c03203c615404002009070f960583d40c000c00501040107101e40c04206100e056a951140903144002e421607490032014041608100306069502c0190000c4890b80182102c00584643d00200126400d00440e0012034100d00c0e80310100001136084910170f54000c1c82101100d54460400504480945801e408960154000d028100c0090354070f80161020010402c001550143c2e01d40300d56800d60015041039988581d03d40021050007107180d0000c500c0001a103a0401c0c9940030004250384086076050036400000040100d400c640d002c0d0001001000c030201d0511941d5204c110004a0040740460302c0318140c5810390b246502c02c030a000744940004908400d43c41031030724503010b450302c51008010300c045005071002c1410170304803885802d01a21008005001a14240041650f088840c45201201d64440480d4035425034000074407100303584d4441d5000c0d502160200356030740714803001d1000410b60700492042040c1580d001d005440b141e40520 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 496244271 1250 496243021 496243037
    0x1c020109110613180b0a0b0a0201060614030720100b0405060411030f0403030603061e0b221806020417070603020c100e0c0a1526010911070c15 63
    0x14042182d28071983c0d2000c0008030710f0140402c5403c18100900620110b0344002090b9241e41000150b41504113400000820340d000c42c42819056091081002402c228200b5031191000306109a8a030300000700003008015103465102c0003145503c1d8410241001c00b41180c1c1c40748140400380d8041d21840954900503071401d00011a1840c00d0b010300040c10450420240c0b86846850380c0c120070f41c10080080d820325843d01c4000002801a20503e60321055000d02110324451000d68141581c3c0413202d6180704180c03050308100d41c100c3e031010b4120100140c07040003480e04c2d000d8010030301c03502d188040030300002d1000c20300061480765110440a902c41c0501540c0140d0749541042d8102e0182032554040341e800000808403070212503000b10030000440080741c2070701c1c10a0001071103c0c4100d42222000405000c038805071503070400e0000c41c1c42003481c00800100c103015400040d0140c814421440c40a4940c06100000f10b445000c5503a566000071031603100648900003941c450100d1103850001803284 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 496245521 1250 496244271 496244303
    0x2090a140720160303051b03040605040e0105180705090111190b060d0305090f13050a06030510020a0518190605030603060a0207050312060103020c150103050d080709030b0403021c020109 82
    0x12400c5035001c46a00c807840c0c3da490650300c2c200d413075420000c139244058030480e01150004174100083c10080c00560b94482ea92420442c03600c0341450180e0040380200708482a00c00f480710040388003a4490203500d400c6880c0e205e0080101c8400803402944c08150080c18a05011400c20044420303016004601c61a0103446c0c8c2818003039020061000540019410701180c042468120091541544020040b520610385004000204c0300191030013402656121401c0080041c140420200006900e8003113041c07a0302d01b04043c00c6d80c1320341c1c2d14202c4035009540290700b06686801654005150031490111042d468140141c8541c0c070594605200c0c0c8184000500044003900817144e0b081e5205000d107007080381c4525400060840a0b0425060680071f001d1f00704013400400107044c01c20307441c0324205015459810414103045c0d802c40e01204000b9544d0401c4415a0000b8003401220760080201070b940c0d4660030b08038101819615040400390030000804986541508613512160044100c10002440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 496246771 1250 496245521 496245523
    0x609140f090606060d0f1509090302060702030301050d020906030f0f0304030b01051914210102130b0f07030503090f0a03090302030c0907020714040906061e0e040f02090a140720 78
    0x700d5610f44d020600304a002d1031040d9030342000010f03000140003c04d000c6100360310a05096965080301102c5540c400d804000c0c107a04002c8650080d8640c00a54699410140415900d030980c16029001e149580045031050b03c00300f200b91100c5072940d0584107854070f01c000386031322a4003500c420354008071040300200b203520300300113481e1502905500c0319040030310308000b01000c000000344460b4446411001071086e40c071446941c12401036400d00050351039404071200b0244001070f8000400300c0f9010b101d420510041c98048994154060405545076a240c2c107043c3c0c0b4041c4d120004d00707064043c00c0c54040405800c18403450690380708900390b800e52a011414030043c49421141340300140c3c8036032802c0020f6158078011403000e01000d400460703405800d442d128240c0318140d214442d101d000c0481d000d80702c0b540b500c5810240c036940e02c85545070b09054451400840341301c400039208411600c0450142c48055000030781c4901d80b003210721a10702d003d21000d42405925060800090f04034050485007406c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 496248021 1250 496246771 496246783
    0xc010302160813081c0509300f0d03090c0b1c020c030a1704050c0f010c0f14060601020a0b01031b0509070f0e010f080f07050c03040e070e0a0509070e040609140f09 72
    0x182a59000d0a0440341710401410090070011a60504150304851a44000002c3c031600200000402800c3c0c5900818942e441c145920030a4800c241c5421001e0cc0000e00c0e242501003215030541140d601c030604c0f0000454030715141c9078503128445c0700140d40020343d10b021018046452143c0c5500d0104081d055404080301402c079001801900700c1405154503250280600d24038071418500031819070800d69448500b25241c09040d00d1085c200300c100b006601c1d0401629510190a1000e04035490003903803180e0700c0c9103040c08000c20301240f11000c1c190f080c401d03080301002020014034000d01c074101408081c000401420340758000509a0000025550050180111700c036a141d0302d0343c4c255a10b28841c4403071b911018055204002c010091980786000400c040c0c005004402203591383c5040007040038210a400100a5005110036482084507a880d5510f41d40e00c0480d40c145005d0340010000020010138403a086111041d107080c0c6016802c1171800c0665118007500ca1020085407610005030380d840c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 496249271 1250 496248021 496248073
    0x230a0c180b0f04050c19120c0f1409060d18020310060f060804080d021215152208071202011103040302030a080c011b050a08070f020c01030216081308 66
    0x1025600c2d6040c01414164040c0e40e00080c0001d0315130800b10589004000c80381c07000f8805000941101412000c04443e01ca59801c03c1d4050034211070100300c1900182c8180510043c4014285000c41d44065079150350f030482e0f45805107a01d041101103201c400e0015600004d0500703a0281c403840150600d215458410142500c00040401000300e2811008507002c20006000320380c2450144081c04d040e50150016040ba81c64000703880c07000c1e143c00c000201100c07003294001031080c9201d44004500c00300f4581141d24140c08001e4000d001e4034000c0100d5840d4009921400c000d129000d40001d11440f03c804050109201b6660076010315414055903950303000c7d601000c0d50682101c0e480d80009603002c002440e41c8010100041035100d072407099094406004d460b030001107130001402a00f61540042d00c00d03071000c06400c124002c40c8040d14005d582d040900c00300c0c1d0506600043d005000d07403141d603640c002d241e80841e40a54407004003903c05800031451007903c00764400d0007401809203074460100c007405 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 496250521 1250 496249271 496249279
    0x60e0a0201140c070e090c091f1208130612060b072d140304031106070c0b030c0d180c05010f0c0b22030804020a0603140103230a0c180b 60
    0xd8040e491100a10f51004090721900d1151283c005400d00141c200c10303100744900303409010381d0142035041c0107890400420008401c840300500665450026440900f552404415403d4140251a005a40b03200342242c52084d0a040f02d00000c0301a032111120a070700244100078000c45a45003961012030040c680d0080c08540000000c540e0031104070121460706080704440100030101d600c42c1c640781d4039450300c1d0320820780001400f4414441c10045a0821788020340380541341c07114913207c1c0902c2c0c03c481c0c0a2006620307400004070f84410480c1d03041e2016200c1c0ba2000b00941842ca0703811500220308014204d41c511205080010650f0180c56140c01d201c030346489485030f42c9070a5840d404403030402401349000c210302a02e60b00b01380c412601109525442500c0301c8400307060500400c64605940d44c000c0c401c040c200591600040740c5100001e0440e0392001e885506116090b044048406800c541e1410b68807403105440248400548154102c80501f00c2c20201d1040d240e4560303068032001d404041d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 496251771 1250 496250521 496250537
    0x402070c050a0f0803040b09152808010806060909030904020a03230108070b0d1509050604050f010f45060f051e041b051b03030411010c0606080303070507060e0a0201 73
    0x105d1081005201c2880c004089811400d0b024184603d103400261094981512b003001e40380840500401c48414100c036800c0c00096036140070b0795181c1e00c40d00144443c1c0540b94140200d15003160400a43c0e0a880005000795128104020001d00800900e4559003040c007038044200d074481c0d000750080341a6081800030b440003d0400d8820390095000500c2d1014081d41c0c0e02410740341c01c09041005001d00368180002c5541d085c21410407003614800380c4015941c1c00ca80f401080701c00319180b07c800440c0c5041108100b105560307142050b1138100c0c0722059820401c4801c082c419144d04280f0f21244900f035141c1000250f441716107440140da1240601c58010042480524200084083c0c092075544024000700303000103ea00c544070761520140f41000031900200e103854452a07083d0705508105c0c0c1010041d0305602d00703512224015658001c1003030500818141c0341090040a4016502601800080f01c0c1c1d241006840240148e00124060310514a41542c3d44d01e00c00b004180242110b070146d4030924 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 496253021 1250 496251771 496251779
    0x8010f27021c06050708060102060601031b0f050c03070c0302120f1b060c070603050612030f0f130902040612140f0f09161203022e020304060b0402070c050a0f080304 73
    0x60855007403101010b0340c02c08200c405002071000c0c01038174413550460340d420307a0701d080000002e407074401d01810031030505090406080b40240100d070f100c5400e00c3c1610f0460030103100b520050315103109000e10301300c1500000074140d0902c118510340d007084070f10079505d030401d5030895400607840354101e1408404c207030407144105e000a5183c1003011003d00e8020906071810380c00b420884d203400400e61026000c01d4490040002510304121036044400c05040510b1404061100c2d0401900c910808845035500101d1000c00310058080410060003401d00300319522911040d0103070201c3c5110303203000a01c606010f442c14a83c022001d07040e000700c032200101f65440d2901d00b03070800641001480351701d0070322030f41036200c1405100f10140d9008003410600d0800c00740d29401c0c02400e00d01e80071040d040307200c6080015090141451640311014140540041e20381c1c48914000d000383c4640c0314010f80c40342c00030801c80107000d0608200005c6520889041001d1540c520340c00c403894409100e10b0a5607001413000b08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 496254271 1250 496253021 496253029
    0x403020c0a14060a1b030c1106070b06191a091c0209060f060c19050709020301050105030a0b0303070204050f0f010602190201110f0d090602070608160f0309080408010f2702 76
    0x404c09011a081410800d20a911505907030503150000342c0c00100a20209800e002c2c0780004a6500c00f01a1101c5142183d5529042e20382d0701c0142c500c60050104c0c0c00b00150074038507800c500d00900000c49280100424240d541d034001d402003410a84905e154400200810341300750b0b40e00d5a100c0d070180c41c0721a40d82d43d4004002407900242d1100f90069800c10080d90360901c14440307450743c0308124854800f110307490b0820516042c610341040782e80ca8410001800b0796030b004020f407035001540d08c20228101c1903d0303000c64214090314000a40040c01c0c034061085c4081004212403103800e0202c1614100d0b83d03a214101d07580c03400c01100304807480c005900c0c00c0c00355100e0f0008821300d50724041101c403200001c003d828075000083d00d00ba000600c2500040c4211036041c8107540041682c7d141080160a20b484107502c2422038403411800c2c0400d891040303203028043d81188180940100e8110b44855882c54402d02130f211040c10140e07a00c2c40c0034070098203e03170000701200702080c6000c8092810b4203907600780 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 496255521 1250 496254271 496254277
    0x1803060504050706030c020109020a090915020d0c1b0b0f071e0908100c05031b12010b0c060a0e0c060703020c0a06030605031510050d0f05030309030901090602030a020a060b060903070e0403020c0a1406 88
    0xee440183e402401401d414040303000521100d856400009004400701600070708200011131440c2c00b10801c0d0710340030302050f0004000354025001007090304080c0c544403c02c0d10900e03450150b02200130381200458465607040380000c5e00301ca003044e0542c1c3c111400b40d0170706c0089902039074110000c070f0802e00110700783c40d500a210485c001c0780f0a8404c0c0c074260100d94071440b102c1090780a42800a400101d03031f00315200c00d03c1207540100118000f80401001101c100e40c8801d45020214014180400d0442c1814404c103c2e5401400c00981010003040c0c8588008015246502499000303200320912030407010074956129105040307410b65044154104010014181249142610207802c03002c041c1001ca04284002c50003401880015961911343c1d400240080c00d0300c3d03104005642040c4008070703070a500403580d40e80c600e40c000c42c00990b61200000081850142155203605407051386d801103481c1100400c001d002d00d02075001c407004090b11608100300d0014078080c0203c001e0500d960404941481006 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 496256771 1250 496255521 496255523
    0x3062612090604210c05060a020c09070314040c0302030d141602010212040b0315061218010e0f01230712090303061802070b01061e1803060504050706030c020109020a0909 75
    0x21629141d40c0341e035044102c040f007a26161350b200200c20403100704078034000840c1c010001038030b0f6117080070300410001c1d440e0700411855500a00c102000540b006120354880c86000d51100c65002443c100b50a010040031800d000480c024464200d502c860280614410f03d510344010300c1180c946802d1030305002d0070101c5130608038107521404128100401301c00e00a04003803c00d46d04403035102c0c60320308840d007000302d0704400c11070180000f045a04904a80710039525408001501034a6031401a0700304a401050580a4a90280109581041c4441c01908801c20545102d00712086040301a042d800c0e4100307050702e000c030100364141c0e903070841800d85402c42402c040c024280003402540d1903801100118500c2c00680640741d00055110401c0441e111072409002580340c50341b200c8041d940030800654a0341d000d2014850321000c0ca402424080c90b02c10f010319403141c030074065821326181039a92200140511000319040c0003444041500c1446103085103500180300302400b03032406c00d582d0010600c07100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 496258021 1250 496256771 496256779
    0x1b050c010e0109050d3c0c090204180203090c06040b0d050f0606090d030302120a090308130206030615040513060f0b07050d12021b0d09050a08060a050915070306261209 74
    0x190942c2d040401b0b00203142c12103441c1c25111003050b0703180000508525400078590740d44140f00034044055800180440350240c803800603075036210b0000e01c615000d580c0d071585920040024010800e0074501c000f41400000c03214007030007152528552203020000448145030800c005020f00c000751710f017100c82d512805000b4100146000c0c0d1120600440080407500031050f242c48003a40070401d0750040305560300410091841900d0b410340d50004c0c0c180e20000d002c40388907040c042d20208024110004840041800501c8003036003120000e4814040c0455118245001c0d185a0001480a440208a803112540701010b001042000c0f001034500e0000040342c1e150440c0e00f400071842e0010034a02c03160500352080b00410492070840c0000b0100d5900f9042180103207003954003040712006c00035160303410140c0458080b070266030300003c2a20708140c43c04041000c886d440c0c14020200d030150300c0901500c4d0704401c0c091080810f00c072406014115442c07003045540c07200400b92440414207014004121b4010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 496259271 1250 496258021 496258073
    0xc12060d150f230408031f06050403120807020d030e030418060f0807060c06020d06080f010e1903090b0306010311040906030c0b030705090f01120626120a0c02011b050c010e0109050d 80
    0x92001035606285810401c0449c5c0001428414885590b0400345d085055140c80c00e418030700070300e000b5154035002100f00245905d495228110a1040c0f0603203000c0d100000e030725241040000f155002400d0f031803040075841030701c1100c0440d00080200c3c1c00c80c00e6443d6600c45200701005a61044001d60000c404910982ea5954020489440034804074200e00020000030611501161f02c90b810200c1d46140d50704c41001502c0c040c000a034221140000b100c0344155096160741d514401038000d23002c100c2c003404c1645000100458018a1036006038240c07402842c515905c1a282c100040f014442942c001e404118280601079070707854041c100d09940d40040c03410040300a201c03484a03043c0c480b641c10500494181d802c04241051040300c2e441c0c4030507031000041c000300014426400312807003120703070303940070008904010410b41e4001d0360074240507050310035000300000c0c2e41d0500c80c1d211481c54034514005442c0a041d020309600c9814010243c41c80180040049119a9220007040c480041045880d40c001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 496260521 1250 496259271 496259311
    0x402040f0611031213031707140706020c060103201012020d0e19110609010f0f02010b0315010603150e070509030109060c260c12060d150f23040803 65
    0x11211460040b151559040917039006490b0140c040680e104101079440c102d8020806995808840d00d01402c0e40100d50555804542c00e141e0b0284c864105004000c0c400c50300000200b0506c104040045064600300e060b449040300c040201d10250b89541000280041c04401946100c2e03034002c004064043d40e001981903104588141010500644104030391280100301003400600c0b50100001c1408170742d401c0c0b40c180148000380c2105c110041e40c104000f00a1900f090a078001d500411401070003d0440d40c8005044180191501e4240100800070381081800c606040d4078041d01c800741c40200c8020790f22913030707181021501500172800d140c0c0c0c19901c1d1601030f80440c14902c00c041c004070150761590400b05c6000546060703e850000d19444039640a01044440e102040c01e442e01c2c00c0c04603419511640b10000003424a1450744c0c1d001d80341ca5100410011f00c070400b0341c0500980c501d40178060229040c2900000c2183d0982c0213000512180b801c0000c2c00118440003c542c8241150206c49110002c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 496261771 1250 496260521 496260547
    0x8072a0816020a03200901120b1315020304060e01050603070e071704050d02121602010804020d0b0f06131e150f06030e0613110907210501030606050402040f061103 72
    0x16032055440f11815115070a80385042c8100f102145d0041d07541003210b516121917540f03440c500b4000a4040d44030440441d20f1604a4100c1a01e0942c0000005000c40d0010100702d0003540161021190949000c0c003800c0600f90601a0b0361050710014042e042862a00703803e60a0224014007e108201d08405082010180564440e008900a4004140740e00c80c6031806860070b0791021080d81100414030800030382c0300010601c031003800d90a00c0c04903590740b558400b0035107800d401c010040240942c2001c10520008404855104250440d900011a1b071901c48200c206c609d00340c1c480c4002601803080d0070b520525900020403104140398801c007030355540c400b00c51001040c1c2c0c000b00b0000351110030015004108005054000b109840100d145c140990f071042c280c400300c1600c0901400c0728000042d2064007416440e0b0130100d42100c0c920340c41d0390764910880100424042290f806280010201e218280ba10a46094649190103500c1d00d82c24420700b900c001481d034107424564482000703044443e02c6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 496263021 1250 496261771 496261789
    0x303050712051e131a180f04050411181326070515150a3f02010809010e03031b09031f1a09070c0309080a0308072a081602 54
    0x9182c00b803c60301c46030360402c20031160681c0c1d4400d41005280c81c14121200c2e0742e00080326586500819540361104410000c07600740c024a04219600610300010081031152700000c0c250013010844207100c011404a556540c11041594000d104440030035240c00096982000041030004021040700c5190030559800d06507800080125850f0b0880b08a600300030403004a004c2e0401001d0512024607030002c808612044083d00c0b840c610b0459031032640303040107940c6503070345107900401d0349200044558425410b106085104100d0009075013400041c33401c58184201c0303a8064041d006545542c841e60301d148008003204003004405182082003c0d295030b0700f00101003100c20354ad081040540c401c091113208680440d80c003241e40103020100c1c0b0206da0340301e2003410342c0164541045a40b071402402c00321025240e5411803055849460040c905250300104040c1c41030040d540ea003200c851824080300c1c0c44491500030361050750754a44521000544520140113000198500803510341c0560b0005078030b6003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 496264271 1250 496263021 496263067
    0x3060a06030b0114030309010e04180c17190303090302070e2401030c0c1e050307080d0c02031810120f05010812120103080d09020303030c0c011401030305071205 71
    0x65403000d0410070807864a1400e40140480e81104c040c441c80500465140e100303102e03509042108080a5407442d5545030b0000141c13003605882c00c903101c031a0380f505252b204007030b028441c03182c440c80b2840c1012038000628040101c80c000b2181005180580c0c095025110346a8200c00398094958085040c030b140790703d40e40c410700040110302d10718040038001c0030034001e401200314101801d1800590340c554101034095444e82c0d1160217041c24040a00115621040c2c0c880010030a000015010050050100c060500360080c020100a11110b5141c2a40c0d2440345445070751024154607240103552a180c188840160314500b05003099068030b062400446004801b00c1d2280ca603600c0041c428428100716442c0c0350500d801d101860103003101044041210148401007140d8000649150740c2c41d072a0b0040504140c1c0502213945034105181180110b8000d81c0b81024150700c2d2810038015030b041e40100354120313901038a60b03601c3c00c00c540d11182c206000901501040c42010002160221a00b611401c1c0350 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 496265521 1250 496264271 496264291
    0x9090307050a151d0303070807141209010b12070e0604090605090a050c090106140d06050402030c1c020a0e010509040e0610051305070906180b040603060e070f021b0f0306 75
    0x351142603065000c40f5036075104c0d0512454030007882020554000116601710486042900295880007011a40f00412900c0050f164102040790704c00c101c1002c52842c01020340d03000901c0081504428042a401049a058499400b82c5810020740c41c107458030039044a405030000c15114100d4a900e0181c42c015100403410340d20021710901032002c00e10881e912608101c3e11410360b945040c1008003100a01910004015400243c0c1c24118440da8000c1d030042ca8050415034032843e104189207100c0c1c0150410310b40ba16040d50f405035030f905184c400c85400c6606a101c1d00543d0546400444054000a0381a0740150391130b10010064002009168821102d0000b44c0c0d080500385800c0c45a050381c022408056507041c0014403d01ca9000b029000a03075401e85824020034400e04900d0a046910354055004220700040c00306009606030045c4040e15241c0c0c040c1070b880d41300c0e65030454071011441d2852005810410341c68940e905503003503100c0c8518004004404411030840060306201040c1c0c0c0c5c550348 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 496266771 1250 496265521 496265543
    0xc03320406170402010503011a0904060b0903060705040308040b09190f1401020f061b0715020304060e03090108010b0309070f0803090a121203020304150c0306080712030c0209090307050a 82
    0x1c41d5840340c181010103400c0c0030010340d20304003580081c02d1400706002c0d50203080000340400e826100c0d814195500701c9001081030200e6547c07020165100c0d404050010301a010303507000a102c44e40540201c0cac0845c5ea10421080c9402c0c580f505511468018034101d6500000b1080c0d000d1b9003003c00714042c00a070040020b0000118502104e400d07501c1c55104801c2c0c155002140c881220301c0300460881d6004404002e1003003c03500d10b24020155100c0c8090050110f07600d040b0007010421160301541c415480b55404010300c8042c40490b41c0c2d42d0051510345030004075544014080c1a0045003d103402983c0c950498001c9501e450b45a80079543e95000154a9440840c503d44946840b141c880020300020303544485001030fa842e030340a00c0e400a816107003895000004901049010903c0d00340d0103008100c2041441124080203000d4845c0748150740c0c2501c070b0801b0201d49240d86440d1a08041c0c4d054541d03020764009a82481034000c402410504940000e20055000c07442c244100340b15148281c503401c1c4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 496268021 1250 496266771 496266779
    0x8070602120c040b0f1303080c254208070807030e060610090b22090b0102030708091c1406010602010b0a1202120109080318010506130b0a051003020705010e0d0c033204 74
    0x100072b006204c152141c0018203442000070344508484114205085044219100c0802c440200d2407500041a10594110004c201046e65400240980104010317503800030700d51110b0034210f0a64119031202c41658120034086145890007a04202c0707a1411410805070b1181d40c0ca174006403a4003c800c42e244a0b20120712841317603007010510410064403158100304016401580002d41c0c070f010321b903801404094001491070050350f49006809a071414022011406249032a06900518920517106114030a00d80041507285c010700608443d800d01616550701070745090b40d18152800000c900b682c00c181600300d40403000380700303015443c102400b46060769680d04208480c150700c2c10070401007241c564540000d0080725524004403611082c0340e0030011402901250004200c0303441035002c6580311780003c0180807050380540240c94013501500082200304104101c2a03126405488880700040444480b400002c0c0a101c20140403084004040d0220200e14244402c4140c00c0c1100201e0304000303d8100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 496269271 1250 496268021 496268053
    0x1f0e09180c190b03131b05011803021e041d061602150114130c02011d010912051315090e0c16020909010908070602120c040b0f1303080c 60
    0x281c40110152000000008144610811111140918001648008081450700c09020b000f031000d903070803540c0b2144501420798204850200c0740300301804a250004c1002400c0b040b5100c01e01140e8024220740c05140064103030601c461100405284c1c0a42e407014030940964103628140e03000106400141a40d0400450b03c403820511380c8140000c6501038520307030b066071300304c00d035590f0441c0c000c101c299240010b0310000801103261403c496481501d0440c0f41c0400300c1c0c2c15007184c600020801c050400c5d0750031070034085082e03400c00800130702803a00106140d007a60340304600800c0301c54000c0140d801d460780c48000c1105509411210000083d00d03e5100303020390303010905084d400c4100f0f185054a4070315000130b180301100300c01601078807901e4404c1c0000c0c02c0303070f40a4009c0007400358002d624a50340e00052403c0030080d080b18070965051102040001e451440c140110b800759252981c01e030f810518402a154420340c0806903402e14000b00800010014020202070f1485400d04000b414240010440740 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 496270521 1250 496269271 496269283
    0xf18011e020c010f0c02041802040e0a0b1503010902031209041b0c0311031c050f0702010c0c1e021f0f02071427010b04061205061f0e0918 61
    0x80d40008035205803092a10340004203000700e21000e0030640420f0607814000d5071600001140030750014100b00807041c815501c521088081ca00c2110108401d000d1001911386d074405101e0001c0250702c0c40c0b0b001c81c14950981400e1130160030f0050001c03500008a0740401d0910020800b81440c1c035a000c611460b262805004245111060444000c00088209002052860705400140922210307000d0041703001c50078011209030600740c40340c0203031044600080c08020301017298006086801500890301a0b403041c00717400f414900d140d030b403a107002c0d4103529038003200340049980401440c1a5410540142c58554484860501003103c04450f000341c0c00000d084020b081e882c0308215042490309204048024014005580c0d080e109100244981c1e54111103205a6030150403035007043c0c000004030212803400070002c1d5401641d48107a8203005102100a9420659080340d01880190f42d1303844404081c1891101d000303c6184c0000c2000c2a4000710b105040291410540f040c141202071a04c82000c07c24 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 496271771 1250 496270521 496270547
    0x250c08240a0513110a03080307091e0803070219032009070810090e0705030102030c090109060503060616020126070306080a0b04080903070f150e0f03070b030a020f1801 74
    0x401d02c034900d00301c0b5200c540e40d182d890004110380380d40001010952030f4003001d40050340d4041451942c0341424040030f000000c43c2e10844000c00b80c070a1008600300c00d12249041100d07003c0000707600b00b04d29503003045540d0105210f2000b50042c6c4240c00000f080c84205440c000308180c580f00b4198505202c20300c210b00ac0010001c3e018880d5500a01082c040d8081045d41183c4031300134006482003990800034102102c940c02580d0660010090110b50101c903c01481c03000c03c240c03104440c0c1c60f500c040941e10b50004403111580000c0a00107034050498801c51000c0c01841450103034062000802e180460030207400d90f42c1030700e0b45800300300520380b600b41c482d1501415a4900030020010182e80b42c40248500820046c010080800c018070f00303860410140d00a0039859180800c11030320f50016080c552981149071000821000c200d80c140d0501c2602409500302c09009402200d080c40c2d03d6002c90ba0000d4000c0b0310a603401c201c0c1c0c11445c4d03068000741010f40d10140741070b000d00808800050400081e914 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 496273021 1250 496271771 496271791
    0x6090b09060306060d031101020405090903220e010b090a03020301022803020403203010290a050406030501150501020c030d08090304171f02250c0824 66
    0x424044117a503104510140386915141c40340d0390f4000c1d40c4800e40680125031207150032110f4401400f10088000c4090310503024400800d000c908070600308199800360390701c561b0110036407202c014400c0798420f0000300700074200a0602110241d89601082c22640008200a00b4143c3d000d61124150420198820b520016107401e500780790850701e4030f1001d051500d4603440113400403070142007180c5441e0b20000c3c40d4a500c0900f0611032400244062203000d00c003e89141d140a001070000c001e020318070414040c0c5941c800d0240d2990080f5040300c2401110424584e44034190000015441d66140a203a0145115400214204030700e01c1c1305c0c4011000707981002d4103540004503808420b480000360074070548500c1c0380a0144d0348402c81c40c2802c6204c0e42c0c0100352040840c48030003040c2600011045441d6a05000000c02084900711120880c00b44e181c2481d03d80b0303030351100050403500010769000e600703010304a1545925920070b001d52418402440b0b40c202e125100031350410010884605c0d07503000030382003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 496274271 1250 496273021 496273033
    0xf010906020d03020c1903110f070e0105010309050c0a090b12010c140f0904020a0f02060603070f1512181a0c04093b212b06090b090603 60
    0x380302940b501040c2411104041c0d011811851a00d02009660b50950651b06048101c0e500da060007007244070700014118130740c4103048408903000000561071086840001d04075a02e80d0030840110041c01071580103892901c200c0440b08403a9681f0241c40d0000c21440f82c1c0052040581e0052108404590a0318505a494504000101908000031740381e00100407540a94400c003c40d68079002e4007500c0c1546400a101041145040350864580401d01340c10b81c0803101d141d5924010103030350303400a000b0384003d02502c10040000030340115a5518a80c03a03400c03c08001400c29000c0000c440300002c2400031909502c5041090001c56448102c00400d60740b28200c1c50b207001c41e11548180b24500c601d4028642d81e000700307080c030b8011118044006400341e6034040e0118910420513080701e046001006280101c1524002603180400c1031010800d50310201360400c2d0b070b07030704491865013118400d44001d0090b0b0001c4004c0b500503407154a014000203007002480c060389506000311803200618140c083e81c402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 496275521 1250 496274271 496274279
    0x90b0403150507020f070b220509040f0201050c0106140f06031b0c12190818070e1b0d05090f011503110109050303030106020106090605060901021504030302130f030204051302090118090c140f0109 86
    0xae0120286d02c25004036a6482c46412440103c50510680c0c00c8107001d546040d1001c00e000165044410700071034121050003042d9a0384080210510044d621100940ca01a0311400b003000781e11701074403500c40002c0966401c0c0d2240001103040780e00010100d403211442075114581d4907008061540c0080c84030200c2c00b00760841640c0309580d0031b914000c60b102c0c403044400090700c40c41400e108204c0300c40700d1031600f600c807100c410f03515024060507101c4090364003c681c0e0161081905102d03031412001c1200d04000c9032855600c035a406d10003850801030400510b1000030035140c8080006500802e400e500009119180000c40c00417076180760482c1d440f40e8810451101c5a0ba400a2042c0000090201103034241e125464250002d1083c0300c02c04a06101200002a40003400304203403080760f0003540c0600c030340d5840480300b0222441440000b58040c0000c801072080d10310041588103041004036001038000140d884a840c141803e80c030100020384440c00700001400c1c50406014080b00c01e0908200c22414 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 496276771 1250 496275521 496275529
    0x131203021f06150c02091506120604112d0a0507120905192c040b04110612162109030e04020c030703090b0403150507020f070b2205 58
    0x705070345122240541c8114000e071a00359002000034101620564080c245222026100d4400325806030b02c0b549420300003c0494084280d00301d50618020030b140c0c0f41183d0a001951404c002500c0c4075040b668440204040d0f110040c000d18103d500343c0d007001c03110003450041c60a2415898004030b500641441400d1301e8039000415690300341d0740414840b01011102d031044601000c503600c05c42d44001c5070398911100341d110403071901c10782e0010005100007000340301030030030400c50b040019102007103020b0014001c82c1ca40416150805d2150030b103102101c200a00080064200c07171035200040d0300c007034284104129122030355241400b050a0110029440294480b0401e00078038007118050344421280d01058480c1c140c00d01c1151001b0411521410392150b038a903660000c2c00c049010400d14a000b2508445040c1a074046071361014810301e1968101c01b2a001502e8090220f00540c8a00e1060320b450140510a0360064441140ba0603221101215500d11684c1c46503004440741051a17818000c0b03440f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 496278021 1250 496276771 496276783
    0xf0909110a060e131a040c020a0f140d0309080403080f12040501060509010e060306060103111204050c1228080412030f08060a140636190503060f1510030213120302 72
    0x1c0106e5000905a0700d42500707074200341c10020020084010140c0403800c0100c0c2e056140050880c0c03070308440403403181ca80700b17030200d88917480c018258050902c005c1001803010310003050780840c65040a802d02c810102c0d0301e8a00034090b41c013150141d4544d24188180d00340020918010203450428803460301301800401d496401c00741907a070405444264204501c49c04200700c42094001041100c034911700b50a1031a2160005034203e4807485000060904080b4001a036540000c12222494001c0c41038100503541d1108038802103070041c00601000420008034a241e03c60603000751200141c020394210010450b0000400b03c2d44645619034050000103000c4404005c0f8036000c0c0d815903a00c84c00350024808a5000104007181c0c5100d03019a040e10544d4205500b180038000da8050b41c0084240600021004180c02807a4040c2d0105000850b107880700401283c1284801c00c0504c01b0042d80408107900a103250300f840086500090a80c10008030340d84070f000284a800c600c00303580d006555009440302c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 496279271 1250 496278021 496278071
    0x10e011b0501061a0301080706090501141e210a1b0507110301020406091401020604080306010305060a0b0a0309020a1406071202072c09070f0909110a060e13 69
    0x4a44004880400034254061009012851301038100d5000703000b40300825030300c01d000b4000710b405884800225103010705014826a20140c5810300d010b41c1210301104143c100b642d18240380420440d20390504207800004000c004400500c410b48482090303414109108060103110302c03580ba06418002c260b4540c54400389405107450300300d60303d40080c10040d070302c24a41c20340705915510001d40091065046440c140032102808400000300405400582c1c942c1c4049034080d005007001c000161071980304e83c1c003596101d0710007041160000c4d02e40c9031040310b90700035000d0382c408280d44814070780641c070b88020528000d120307062105003401c90400100b0614000c5440080007290300d84050b86d200c2c1d0090290340060401e807202c1d408410600c0064072030400d25101040e0701c01c0c2030b080100720082c1e008a00d0b40c00703448070012003100061920b00b40c80002c203d070321402c0c0d031035444004c00090301e944e90210060051810f40d0300ea034401d100d000100030b1459010650095540d2502c02d40d03480c030030382c103442c46403c0ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 496280521 1250 496279271 496279307
    0xc031f0f0501050c0a081206010807030207080d0b13050106110f0703050705010e0105070b0709051f020d0807090e0a0608250b070618050a030f02010c0210050c09030f030a02010b010e01 81
    0x281d030b07807004d81c9858012103920040c00e04001160f1700070742d68914441c83d44204d90903600c0d48141c0e02c07419820380807885000006080e01504020030802010315801c94045c20001030f240d981d807074403c504840c080f50002e07042400060145002041100703404c0000301c0303203000c5103000b03040c03031030315590b6042d035102c0e46071041c18140210402c0002c5e40d40c0c040c000340d0788155040040109685080300000b40400598080d192043c110f407084c02c050511011200c00007030300b144d0001c2029020411007070324030b03500086c00101082003580001c02e07034034404100715005030030400012840fa410706448604100f204009070981c5580710509012800143d0341d000102d641d40301c022682e4100d1400c020000d8800c40b140103140c80205074400040040c0014507510050190380c3d0003a110148090407402c0c3e4081f4035100b40180d021104040720392409034010b03a00041c07114511464003204002207810064450b80c100d031039400215401a80301c1d02070090442c40142460052001c18407100041c1a00010180700c400c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 496281771 1250 496280521 496280527
    0x30f020f06150301090c1706130807030c170d090b0604020c07120602160803071409030a0201030515041404061a060a050904060b0d0906110c1507020a0b0c031f0f050105 74
    0xb140c4080d400500415000f0200c0205d05850f50100c1e280d00748005004540c61244e24002482c90320840c103003050140e4403041452400c52075807411509010140802c0d60004096460000002009802821903004480f404581000182002441103000526140c0101c0c010408080308503404a094401e8500001c0d45006d81002418043c0c02406088640f1551485548043c402d110320700018510841d9103a403403100d0a00c08501230031140c0541d0491641640c440c041090066002c2c0d04800c0d806a082c00c1e03960610000d0000003404c0e00ca8a4030241e410543c0340341408140500b600490a45200d00506209000301d80408039100344a40312080301001b00106202da810369881d040310000340804a0110f4542d41481a1103004008415044414514001140810611700400c1c1d4128401309409012071500c0190200c46808000b4851003c42c01015500e40c0022503510070940601c0114240315160320b005010021000d104001d01c0c491200d0542e1f041005601a205030f1041d1842880e00b291 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 496283021 1250 496281771 496281811
    0xf0b010206010e0c04152a020102030301060f0e0a0b070311190b1324060807030c06030b2b0b0105191a040e0a020a0212160204180204090609030f020f06 67
    0x20042c001c41e008114002c0d26940103243e810ba0000b111407c440401c58841c200c50a41420500c03210452040203025800c1400104881401080c003030100b00010b0805c3d140c0c0c000b0100005491080d241c110800748400452400145070380b0420003c00080d0980050203040e07480400d00301488030300e1000522490000c40050f441c0141841d08102c260790200030907212503981596406800751440c400c01031503250200c0050700d10780000c5c500c1c04403904840320808480c141241140985900641c854001d405ea41c814144280d01401705010191020a001d9000c0c105141030b540c600c406074410343c8076009134000d9101907204e0048041c11180807034000da07072801080c480c140643c01542d0007100210703164804c100307109800d40c009000e000d201c0d509840c2800c100c40541d05082c019003c1d0b100004800001d14030040c103180d0b108012614903010f11812107805039001a043c0c0e42c200c00c084540c1a100c81445003011b0700103c0410b0620001e0003d00051601c40c0300c666a1640e0060100000c03003000d240100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 496284271 1250 496283021 496283041
    0x1c05160e01031e0218160507030806090c0f040603200a200f01090803010305153705041a010e010803070b10030c0f0e0901020910180906090905010f0b010206010e 71
    0x5800e03680609480380c811040ca40445d88001300702d03628901315103601c0e0f00c03049151150b4100d410460345510303003002c0fa48401062000c41000100081c00501d4100840d20b405a194800b40005103015a030104a822941e5948840e0f011081692000789030b00f407100840301900302c0c0581411400c0f0f0201070110010003032150f882c00302420109006546403014180030b100d33940c0000c40c1628043c03000c9589007030f0110491108040f08440728440824007070300c0c0d600702c22840500d61a00540c001001c100100c2c1107260242120004e44007254240c940c0704488400c481950103a60042c103502421007030942c0341114854582c032521200404c100c5254002030801c2224040c03060103581c110100341007441d00c6515034982420350703020784a103248a8200140da0220b05008503070a0f41c0700500220480307510800305880c0c2d0301580b070311322840340006540884c92000a1040f18002c101101e0040768203209424101c0c00c650b900c0d00a064441c0c14008188020790f00018110704441c0d450b15803030155a5030510764 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 496285521 1250 496284271 496284323
    0x1101110306011b020604061716090b07080f040e180a1101030b030102040b0a03150e06060a050d0f0e030a0306120b0f040f080307020c120a170d0b1c05160e0103 70
    0xa500240c0428042191640584ca035844c0c85103540c9600d123183c607000000d0b805140e0401312400058120b0405008460350075001d004540c2c030440c009824a1b2030003e121105030020b0b000300c4010100307602004029614000007040491088010b0004545c003929000f0000c0c003400b021906154450000390340c2610b0942c11100140311318131801ea144c80c010303400280a0580c14074040d540c50124800410003500791442d6070300034000107042c9442d24000590544242d08200c01c540c0ca810703692500f41d0340d030b07010728001c801c00e07248604013559039108050f001070120380d5180c00041d12038030100070703500004140050341504a001a84481400ea07900d07d07240070100c509000003810300801000340500250001210095808115800a02d8403199961556541b0b0700c070402038980b041c903064041c58190200300a00c901450510003182c0104418041200c000c26036000a401103425411070b014000240705015200441c00b55000d00c10b890125601003005041c003015100d083e12000d00e00d0580b500c1d60301c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 496286771 1250 496285521 496285523
    0x61e1029030901021809131b120c080111090901050427080c0712050606040e0106050d0b041103010b0d080f0d1d07050418060902031504080a1101110306011b 69
    0xc2503a01d2400c04030441c00b039045000e10b0f41e492070320342405000311324101e0040d82c031410010f181003030941c0041d00e4000030385401401e05041c000d081764001c540c1803403050000111900986110404518200949003128400c8020048072007007403007517181d240c0d940802c603411550219804101200079044907914841d0f03178180d0044d01e1100d242c104082122240141204000420aa030651503031941010450045940000c20b01c2e008100024514a0b141d1302007036800c400c080c000101d0f0340e00c4001064407915065815221800801c00300010030003d151039801e075900a43c0244185082200401c40140108500510741400400c58199a103010429100c031042640d10138031000402000c0300e008007990003080e440c0d900525a0118960038580031f200c15200101089144803010340d1900c00040000e0317401241d0500039400100d51411169030540e0141d4000c0600c00e03510340c0202e0000d00b612002000ca0010f59040807240308410f01c214059030350021080c00c0c1b800b51032a0031a00d050919001c000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 496288021 1250 496286771 496286849
    0x2b0c0209041b081b1e09040c08121c140118020d23060d1713180c17070f0f03020c100509010c03020f0307030e030c0f061e10 55
    0x8400a0b0341c800009200d041500302c50913402080c2d480d0b00601240c01c50002901c400b1034084c3c026202103083c0400c020b0f0380f040c0910280011203454900c85410403030200070b6100340304004201040d40380c0f0404010740603000414010410520180e541c001103842c14440c0300828490012000d05001d260740455440209848003006010113481074503190001e40003c1c801c906140b86c000400c00c1c04c0541061000a40000074400a23071080f03040614140c2c004c180000c0741c50040d441c0044c8803003160f1091300c460203d000011510704c004580050660401c038010b104046000c205100c490340c1c21158011014a0600c0d0010406000c4101900a44140101c1d40610701c070f00866080c02c4201070b8007545c02151200000d001506000c8030407000d0303000d400b5841020050070004520f07202c0c000e900c15003c071400e000c250303410100f6600c285d0b400c080280400b040300d0341164040110181a10051448101880199021078140740006942403421402240744400c0c2c004141c4001d2083e101e800140b98101c88 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 496289271 1250 496288021 496288073
    0x901030b07110609030d2316030e0105010f08062503020306010e06070303060603050108160b0a09120f0620070b09070801061421100906021b2b0c020904 67
    0x4013541e0b940c0d406203c8008603140b804800a0011120010501040848040e200c4c00e40c1c80e0300c509010140350007861002455500c1c03451400400080c0580e9008240310b0700c09841d40c910b010a11420440020300e064660b8001100741c4504900030405505624954900182c49640d4000141c560900d032425081d8041d102141c81700070140e161b003041c0203030380c595942400182d82c2d5081003982c03182e203441c0004040c01c2e20b490034041c620f1000090610a211440c0c40d0036104d0341c4007541c518003840b031320080e80d40c1d6410484d9002845403901614028044461a84160004442440f100360007001c6000b86041485004a100c0b101c0c00c0010201800000008100071642da1142c000c0610001c4042c6005180301c0c1c001d1160901418003407880703486050007806a042d58454180003e28036000f048030120750a005ea030f2520411001a45080f90b0080020100b80070100701d642c5400303440c0501200b800011008c4c0030303a1366074041d1003420130b254103032110802030700d49240446501c0426100c03005541010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 496290521 1250 496289271 496289281
    0x40b0402040803030910051302060d0b0a030503130501050a1b020406090e010e0c0a06090b3910050603030a1b02030a0501090b0f040305032e0b130806060901030b071106 74
    0x480114003d05c844801c440c014100d82c603100098450480c0c0c0318001885114000026042003c0181000d0951010000d0081d8420300010604845600166565440070822003c6410f940d165203000c0c10090800e14104450003100826040381d90745528103821040000360119120380d003160014249014040c4003201225911500038200071100c0016441a0740d00282c41e4201035440c0070a6401c0c5560780910305040040c1c40040e40e00070720340510403035161f280485002701056901080394004400960041e081e80c06a6840c0ca103206d00d403040124070b008140002641e00000703d800150a030b080080c003800280800240082114001135054080c8180300410024103601c41c1400f10310882205220307460b046000300310480121001000b081c001c00104188640703050000c195000c1031100340d2060101c0e404021030000756580440000d4001061464041211a04c8c40d0090034481c0c00400c041d29012000620005042c84041d03d078681b20b0022030100380c46090003941c03400c0d440c0c0440d120790030300e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 496291771 1250 496290521 496290523
    0x30f0114100504110d0c0c08040f031101180e070c0606030602090301140f040b22110907140301090b0a030b090d0e0a08061801020c011a1302190c02040b04020408 71
    0x111101d10700344107210008079503031609100700e402c800d560302416800d12074001c11400081c020101c1e03031070501c42c00c0c034085800170b0300d84401400681050000d28941507d5850711011a01c00c07018228140b01502144041c3c0d82e075140721200071541d401e404000d240d29404c0003510b90180c1468040c10f11410990003000b030180e150000c00301c642d03050300208030721502d0341c0c40d40340c07100001d4400c400b800b5204004200420035050400d070b040034211020603114154000c020620f09400c8000703c580d00780402e00e034407980c909010350315030200c903c0c1032540d461828010807222520050180d42c007004ea4074081c00103191076908052003d503512401042182c10007110003507441d180100c03440c00040c40c51300600c0d614203001d200081159014402001a0307141c10801aa801038100684a020342d42400104034882007401914404020402240002c800c41c4051180e495000f580e0f5480ba41d004001541e20f56850124000d411141031400341c0c1170203550b05c00a0084c0c00d01c2400b81e175009001182c04102680 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 496293021 1250 496291771 496291811
    0x61406091509060a1d03070320010203040e041104050f09032203050307050a15020f070b092b12140708040302030c060106082a040504020f0409110a020714031b030f01 73
    0x80d91700c801d40a07030a5120800d13544104a001c004c00d90041240c200071205840e450b015501c48050040d81c1c1415100c00200f82d001d9000c4500b40d940050301c000402080c1414441c2d1070f0800000016a080d03454250318550b907900c10742c41e498420b12180881b00704544420800c01c00030310381c0f01054a80e0703403140d42001c542c2c50710907100030364420b07440800310010010180700b1103d4a5000c00107040c10306956803920141c4540060400d081401180c080340c0d559034011140014040e20f0016100311142c419000502d142845c0d0504001e040c5003003104090140d29194180d403244803031420345030b00d6a80d840c0880c01c60054250030075035403050000100b1200e8101540b00c2c8510901500301040200c1241c191451340d00090748800030542c100300034040341c24960014000354540c11191440c2c41d66603003c1d003080310700c0d601c064003900c000480c3c176180301c580c1441141c005202c402d940e54004080c2d01c001a88075003140742821556208642e60010702c1d02c05000980394984141e000301321b0036450072000320000c9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 496294271 1250 496293021 496293047
    0x3090804080102190509130207030c02042c06040807020f0102071a1b0d090b0d060506040801020904110a09060c53120c0702060c010c03061406091509060a 68
    0x100842ca0131200c0341c4507009941e6640300c002c05032025480200400c40c000c0d402130b00290100400d05001c0000361300e0318001c45d00c610707411544001d00d458546540c1c4108501c00f80f08080385821002c10320010805080c141c46055030102c500c02c4112100000603413805107182c2c0030100f0741d01048528140106c0130806801800c2020701507e00051030500c8542c1c80304a5082e400000c1125120180040c2800c10301030000e05400c0800081d90316210000550b60382c12580c09490240e400040000711030819000e40340700b101c0708801d8581000703e500c070082d00910907400307020f0400c84400c040c0e00600c9094002d03109034030502e84c0b00e54001d42d00c00b448142c460444158680c0c050030825085000c1c006c0360548521800d42203505542000d100020055900c031002e0f0000207480c1d02403016402680d01d0340000c214051203540001050150024083c0039103036640d1251b11044213089a0520b04c1d141c2c641100c20024003281c4810a02c101e030031202589010300341c0d0380794000c880454035400050300000312085103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 496295521 1250 496294271 496294297
    0x30e060705040e0c040501210209040e0105190504020d20060d0c0f05040602070b0c0309120304060e0a0302060304030e0a171e1618020409090f121706060a03090804080102 75
    0x90340c0c40d400d41a51300d120303902c00c040c00076441741c00c0581050682d40e116000c000380c040c030240c9480140c1c00020191810a031440f044c2d0b940d0f8105110880281c1042071a04100c149003d110902d40394001a41100400030080c29120210240610b4503e2803421114440c0d0018034442d00c1c7e100b0203001038000c0004403844000704850300c0f406149140124240c6040700c034140e004040c00c0e42080c2d550081c0d03030056000c3c640284000d00001c82c070340e60b4000041c3d401c070511340f0046403900e2910300000e001c1c500d2a01a03c1c002d0880f40c00620158442400f100da00541605040448840340004908008400c2d4004040265180e0110394624030100b80340d41c00d50246200514036103280c08002c0c0d21003040c0c041c1f0f2244040001020041d960302600c2e0a0040352522600504069a070b0180205480c081141114002070300c500e04000c202c0841d015800308040c515003240c4801c2da5200c81d11002e04040d0140748911800310b809a1198401c0d00405801940b10013601d07181c42c1c1da1035840e4041d4100025410720 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 496296771 1250 496295521 496295549
    0x9050114010c0b0114060c060717070c110411070548010c0302030c0304180c0e130b0a21290a0f061e0906090204140f01030e06070504 59
    0x2158032035908000031a403c48245007440e4a022a040d84000d840303800160442d90074042c1443d00b21081c400e152244c590740e203170803281001c00d00f0725507044903004008001b401032004140300414907007100e00614042c19a00002c0381103e41c8020400d60064900042ca140300d5220004465109070030000c400d01400300c3c000744102054180790408050000d00500880e9054903880c500758401c1c101ca000d42d6020340103403841d0801c05072060f825a4416000301c0b054050514030035a5440b42441000f201003d41e01c2d00307000c0313482500c2c00240030b4124450f40c203016680b65070711640140d950000f403200410100107811407543d039080460680f9488030805503503800b00300b070b206002d83d460380358a200711250746100074645a64485424008128108840c0003803556200041401004a80d552121040c1107440b65a624a000500015284190848404d50340140020889480580b0a00a0308001240d0598142040c3c50049000b007261010b040c00d44d2082c042070141042c0c2080050003900c81c0340c190030030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 496298021 1250 496296771 496296809
    0x1180219210201030207051506090a050f0a05040507090c092d12030e09041b0f06090b0d020702061216020102180d0501140108030a02010605040603050c1c0c090501 72
    0x308040240300d05084070100607000212111440c448090080c81414010704201b81070315030900d400e06240e05401c1d024107240500500b403800e440880c1c1c0c8004c1c043d40c01d2003540b4140c004031287e40b9003d02920b0340d02d80c541d40401c080003c1849064040d00c2c0100e000c011a80c09400000d2011009204444005032292080c0c1440601a06100d003002c200c103100010080c0340c58006040c40070703201406d9013002011003150341590340e40105140268010501d82400411000c80041400d21650040c0d10355042c1c548100306030f581054003201216040e005190711018a0340d9040082c0c80345004c001e5001700002002d41d202040f2906e0303103015010811040071901111501a401c078407502c0d410001d00ea121030783c40fa006141c550303401100184a00700205600c0424180e4410351082a00454080d80001c541601066424807844009000403201404064a540c40707003915540b400d030486020304c0181108141c4c074010250400e401d03680c4460035002c01a41c03101c0480040c0320a0240c05102e60740c1941201d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 496299271 1250 496298021 496298059
    0x306080703210e06040e07020c0d030207121703010b1b0a0206032e080309031504120c031b050c01030c0e090f0a0b040e06090f0a051002031305011802 66
    0x40540380d100c4507094620b5100c00328080901200d0b4860010081c800b034802055840d140040c00003444502041201802d00902c042e050a40c2607103828040c00c10f40410308042540000c10400301c0e5016070030300c0508009418400784004a0b001c3c0c0e02c10240000000080c0c80c918180180f113180310117001800c0c1350010145650301c40a07110300181d4054004d0001c909100c40f0444114105000d40380f00800d1005010711464001200b030307100049681000c01c1d80e04c1c00742414441d60300a040c2104e01048a4a0f19954402440c54091104030812013410020702c10180038013448840c03070f52b54603a150095059403400b183c1d81e41800e41c903070b4000b03400c0007403480b9803a004001d081e401450003820020281d840c88040000c500005103500340d01504c2e241d40450b16122485038039100e03191503007c6c08041c541800311030300d49401010718107101d502c40e55001c03010500100320b0015140c0c40e214003507030726210b4043d074261b512291301000c2d04035460a0744d101c0c01107808100e0314540d14400c2d10048000d8103010419 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 496300521 1250 496299271 496299283
    0x501120c0b07030e01050306180f0a0e070302030a0807021809030a090605090102100f0f0c03091412180a1710060b130e040503120f09010b150d0e0c040c030606030608 73
    0x40201c4d980800109480d03008001544c0e2010002d00300d01c22040e00d02410200140c800da6003a04554660310910034540600d004031040d6541610040844900c0d40d80400da0720009900c024103040d00214080045503a90350003500a502013503051070040c02c0110070503071030b03a0002d80c00c4400f282076858002027150250041c1d51000105030003400d0b40520145c055406801e00301040001990b40d6810b000410203d8460882010343d9a603000552100e50718104061082c208280315050707219144000d05c99400780111001e041328400120981001d407004510000600d40240e01000601c0b242c00345180d41c0042c80460801290a041c0000c580d2800d15500904c2080c0c6480c0b116421141d05000e10381a400d011504a885542207901d0000b001340ca0a4100000741e82040200d04200b0611a240500340142c0500c0b080072a51408180e400d90581c3c0b003d482200d11034199107449a454007032141003400300c0c038070702c1502510a0081400e002c400600500fa030b070190b140847d103003c2000c03608550020381 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 496301771 1250 496300521 496300523
    0x3031d030a230a060f0606120614150c01090812150604120516030c061205010b03010e0711011d010e120706021e070302010203010911210a0207060501120c0b07 70
    0x1820000906403500040314282042c4844010322600d6000000541c1034859500b080d003030500c00042003418680c0042c001440c0000307100304141413034028010001038a0003030703401400840c0c0305c80410a09021180702d40c000c4034101d0396070394a018440c5082c030200744000c085030b100d00d605000c1c2e1540e03075880b0702401503411540c003900040c0c14442403106820b005200f2500b980a070301118400324000340c0400e481501900100c3e04803070864030400c06c66030407221314099611103c1d42032009604200032083c86003c14400d00100c5c60340500840c0100d4022641e8500108145c0003d1000e0740c0c01880a801090542201d45100d600e0301401030140030000c59002d1600b03111801c0310b807910710a030301c902c03000e900040110200c1203102c0751b01c030b00d5220b0107030000c2820314860380001d83c40b0b6150002e0b0318211003900035040c547c4181001080ca94242060b034403010750400581d03002542c4c80342c04001c0002c0c01030f040028030b120f00d000c2c00403d0301084a29001c803403d101c0e10b441c01ba41a21141507403400d00401c44 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 496303021 1250 496301771 496301783
    0x30b0a0f14150a08070b0c01060b03090309010c030302190e030601080c09041211070807030506010b0702130c030204050d0b010f091b08071e030c0e03010c0f030203190603031d030a 79
    0x408104480070102c400203051600501034009592686001410100c0a50000420a20000380c044072041c0a014260003840410305440c1940707400c0450360340701e20500b00660f040200380300700d08040502a906440010082401805081903600030150090301584042803181c811000002981c180006602100c1c44003d02641c00d5500c5507920391002c007480070340f00c1d018480d403000c4121051008001c000000c0a07180d0040480900d182082414290181c0001803500400c100c0c0b5009a111802e00026280003418006420b140b0080700714002d00480d00000e51103001c0d04032510900080307c190a050354884d100c00f44200f039030b0303110140c11038900311320102080c1d00c5148128070460065407159442291414002a00308912108165560035120410301003951454840a903aa1006000740c903080154000c00c159148050b016000400003480d05042640000005041903a84404c403024076a164609000b15622481d000d4003450b0413442d407034205400d08241028a15001480400007600b01d4 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 496304271 1250 496303021 496303061
    0xa0f110409150909030c0308060a030803060d03031d0d090e1b071104020a0801060e01090302010504090e071e030510060b07020d060e0714010e12071e0b0301030b0a0f 73
    0x1544210280034141e180552070700c02e4400000d8442ea03140103807440d240c0700fa66254007440300da180c080c10841000d01520b005060301001480090f41400c22240c03c070130200c407808441003ca28048000c1e00540c854140c1a01e081646801c1c01c000c0010a00ca40d01800e0711840c04060f2500c202d217a543c00222a8800903440701c000c4030314118030041c01807103034501922094403400308510201c0c042e0303030000603a603001403180c81c01040007581c00610040c11002c24644003a080303141d60002441400703030f4002c0f20300c407650342c451b6080c2d400000c1005d14010101c1c410044600d00981480001a41c0640301c155460301440380c01d0944100f1511840e820386c1d0362405c031030b4242071307941d001d1120300b24407100e0131140d01e607903080c980030500c004000000c020100005850644425107000400400150840c0741c004e08102c00c50a1045c900410b0500a4030108031516180c6000e00d000c14440100940c000f0061402c008004002d0243c8058142d01c40e2050041c1884070341c0c404184001214040c0001c80c51840401e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 496305521 1250 496304271 496304279
    0x10170109090203031909090e010c170901090f0c08060105010206010f14060918040210110c100215040302010213060516030e040b060c01140603030c1c050409060e0a0f1104 75
    0x10751095403035078009000c5034105942d803c258005141e449000c400400e15110081044240394011200c010300b684000780188580030310f0250040303105280b070480075210040050107082c130035813184040507000504098400a2400c10700040882c03800354034802e000d0800080791650000407184c0c101d0b0004562084500e1400d0503c80c00c0c1e036080e4411692084003001400059030307410182110b0007095202c6020b0b107081601c10400c6481c00c0144d004107000d40b020340807041140104d14401c521005450391449241c2c940d000303c0c1850003003414118000140d80501051590560107400025900194942060785030300050b9400c1c0901520444403625041140001910400151403000005000800d60010361000a101c50b0030409040c20180e41d1004826002d1000345035071504080140e011b1403920550070782c0c140d15003100740c00c107503903070940d40c44a920300e50302c0340c42150b00404289804014a0b80c6071030040f09540400c0d00e01070041814041c0e00506180c182c45401007107400380e603140d1310302460 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 496306771 1250 496305521 496305539
    0x30f050603210c01140405010f0c320c06130b100515390105131707030e09071d03070f09090f020d0809090c030708151f0e101701 57
    0x403d440946654807081c10060315070f01011180d000e1440341001107010204c898008003107031640d16600007002000c40d07541c0e403403605d01da00c05102e9030b4503d0450300080800c0c4982c00042c0c4109850200144206010460010741842141003890300c121441c0349261204800c0c10b500c50b45c035000e45503000030000d0240030542100c00c0100324101e21450901e640140c0c1c00d51288c0000140100c0e402200c4a9a08448a00d1070a211b480e510603110000c6184000d01c81d100c4007000c04a4109245415000003005000d050007024042c0b40170f94020562550303890410303401450b1084041e0240c407800d40c202a1513499260214414068540f103940c641c620300c4c0380031401d0001c0c0c8003505042d101d0444220099015841d10450014100d0284100325581d400070421702c01900c10081846401c48814000c0c0041d0f40c0d40000055000204500025010b01030400020b05030b0725040140202501c2d5464010b80107900182d40c140000310483d19134040d00c084a1083d1103002c41010350b00c1030f0a43c0030f40140300f1805 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 496308021 1250 496306771 496306777
    0xf090f0a0305270907030615051c0e070902030405070312080f070e0d080408300301140a05030f01050906070c1a04080f0f030108010b040204052d030a03030f05060321 73
    0x551480d01d60b424103001400b0610913041a0341043c00241c4610b0140040b5042e1009841000d14625020b480d2075000c01c102c4071003080b401140f403c840e072951041c0303c014004206001c060b2101250442d1b82c1c1c107080c50840d9541000340710848888071100b60007010a405454204c1c0301d1a0724850304080d640d1600d00031180e0000b0f802c10680c1c8030981c0420b80001c10841e101500191810400a001415208504002115422101c3c500c2d2231b6031140c803d0090000003055034111101001082c514041070b00004404603400e811083c1c2600c0784072813800100005421190080780742c00b0590f1015120b074281164010f18840001c0c040802e810500c8010340041c081d8140d005014500950411281170341000541c1d11110207800920004001404507100030711a41c0641d2100303e41c214505841c1c100410fa04500315454007280c044052300c42c070380d0014100b07002d4000074001010344842c2a041c1c075000c0c0c0208100765005041c1898070000403074078180020310411078000f510681100404081400d85168 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 496309271 1250 496308021 496308067
    0xd051e04141e0615150a080910020f0304060b1f1407080307020601030b0603060f060904050c03030c0a0b0105060301080a120e04140a05090c010e10090e0f090f0a0305 73
    0x2116400700000071141c101c40d481e24004407a0043c060350f041551803020f820103288402449602443c3c2114090340348541103c4082d1040d00f0418901e0307949042c0141002c2041c035862211a00000d1010303400205000258400c510890081040030400024005607400e12402c0d400e1450b41c140100c10890b01070f030201c40242c505441071900c0c6c4251951810400e80003a00c440c0c024ae44400014403c1010f41c0c04080e0380300400b034000b08203e241c22840100c58640190089018003040d4011405004090200c00d49200024080f01da42e6465002182e1343c80f07084c10700545100440800100e1a0724080341141e0495603500300401c0c1a6800e901c4203000d01350600c400c04180300386201035240c03d80311070103001240c58024100054501d0600c0c07001c0c040c0caa0040c41e09840740c0089120000a81c3c1000c0060b4440c041a40c0e0941f15042541080d1454140c80d0400c290f46c080c46400c0080c00f04071303018802e00c0b0b04069070079510200204036140c1d85d5940010002003315906001d415080501e94240a00d26 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 496310521 1250 496309271 496309273
    0x1003090f020d08090108070201020c190809090f27070504050c1c09060e030310171e06070e09090a03050706021903240b030a1a0a0602030d051e0414 65
    0x4101550002e035822101c41c03400c844034280403840d04150b40c0c1048200d41e0003445800254a4140ea00e21041c1d161441042102c4048441c4400c40d420f024581094a401c0c50000e8000080341c200620744840d00b031402c17580b001c03001089441d0109940340d0030355030f503401003c0c1200908000d403c1208000162030000c017888aa1281031104418141d0402445040e642e15440c00080c0041281003180944080040030211070b402007040c06103039000044080121041141d40600300b94042801600b8075102a55010640b6580c40420b0300420300810400d004007610b0b1550000080d20340d040c0072003a0812607040e060703500150f203000d021074000e400030101c440c45001c00620300354444020744041100c420100001030794861406c2c404100c003101200004d04203601032843c141c50301004a06030310006004400d03454803601c041d0401050403e00c00241480200100b1189442d810001d55130b030489a8040401d42c180004204178862441841512604810010101e951107440380a040c8200150038402 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 496311771 1250 496310521 496310543
    0x31c0608032113080a0302033102041e15050a0617280204080d39151407121404061515170105040b0603061009210302100b100309 57
    0x100b010f40100b18001840d06d005849042c8060b16101c014a03520b60007075400000c40d150001c0410880203842e045a04540119040710983d02c10141d407241e61804003007031804c1c550b40d61003c06030303000c82506640b000d0781c04040702c0b6a03a1008a5480d880d460705802c00c810f008010409450000c95011aa190f95a13010300e140f86c40e90950100302c5c0e1141e07102c14540e400c074044021000da4402d890702403241c620039100503200740b03805100f049590200c000105141c4910012010480350384079001401380540e50401c40201524400100c100044a0050026688840c038403007110481c411100152064003500844d0381da1503483c50010002808071a01c9219100000101c00c40c0010800a2892166032244540041c0c845881e0700c2200c186c100340d101e18240b0000c0111915101c00341c0740d00c40c60442c1c03555416441c889044e03c4e03005041d0410b26a001e9400140409001c0c000400e51140d407103a421214010b0000013190704941e4110311b00b41c2d00c40d000c0e0300146005840380e004102c90a00660724502 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 496313021 1250 496311771 496311773
    0x603060918030f030105030610150c02011803030908060708130803090102071209050a0f1401030b130e2407020a03030c02010e06090a050105070c0308130311031c0608032113 76
    0x461500003443e0090142c600000521141c14240005508401c000200075405401c0c0b000050300c503480f0300460703010030110943c07550940e8818a03425010702c0700401c4020049403a800c0080c28518a8011000a03214031000720b0042442107900a20800b41302d40c9822502c40c06030348844040d0b00142c5610103540d028486200455000480c460540405807903001c41280f4240c18004540b2680c2c1c07005001c04ca007000c04208030940c21904001140e02441c00094110f4440000b40c0c02e640384202d001800e520342a1607102c030b079800113070700d90705040121204519002d61140740440c020044032a0340c01a00140c2400d800240aa0001c95200040d40004a603080c150442a49410021540542907610031407085003031007420700c1a6600000913282041c1da02003181c40c098040d04000e00f1181c6000040d40b03040041c58401d00c803049005032041e0540b07680360305a446d22401215120380d01a007140c42e118001504150000842e2001d405c90704520307141d015070b0815810400c5000309400440542c00150300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 496314271 1250 496313021 496313023
    0x18040b0402030f0603160e060409020a0f030809090a0204180f23061002030a050f0c07050a03080714030a0c02120f0706090603050f071b0f021302070302060c090603060918 75
    0x14403c21030980000128a81300040601e07241050120090318400268140501c541030500d1035480801070310302241c180c0301880400c041d6880d9500442d24034010940c00320802014100400002008541d440340a0b101c0b04030380c1c0b08070320691051940351104030380d03444405007403504a038624441240740003828450006030100040a581d400d041c440b0b408004004552074030028480d1040308500c011030a0000141d400360283c03050184612000c003010814201c020001c100c1d5001503c07018000301c400c103549141100c1075800015085590341c5c241d141c0851558400000c2c0c03000c0301d007035071744880084c10107400307101040c62024460750740d501881c0319003850079004101030070080190381d6415194900d4618000c003201c2018006010b1070a01c5402d20080aa0010340f18101c0040340121803403444040c601074255580b17410009400016158004001c87c0300c580c0944284d038000d40035101e4913175600c2c0c0c842400d0301c100010f65500040130700100e05d2900342124142e92041a841c02c0c44000355080c8407071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 496315521 1250 496314271 496314277
    0x211706090402010c14030d050a0b0306010506030a0e1b030c0405070801051e030106030b060109060e011e0519021b06031b09030f010510050a1205060103121202040b042918040b0402 79
    0x441725940300240390608400e031032140540c0b2901c095001c20a000350840040e4031040103104203441107d005c80411500e003441d50003910380100d000100ca015000c01d640c607040e180a01d2413010b100f07002c1c2101c0030341e040c00d02d805200e21030001c56481591f03d80c24202042a60781c81641e82d004001c0c560b45d42400141c0342403207484003071401010b000c00103180c0344000406101003600110100202c3c0b04081c4181d0740c00010303038061000303500c107214103840d503a0404a8980c0a0600b2403581c80b80c080e560b00c3d0031176401040084170542d01415401a48084800784281440b090b52495190800d26103d005404a10006040d440380003c05560000060002d01820344070143d496808402424004108a10740310f84814000d100c2e041c058030f030303400d0030361115505c502051101503e1041e0f84a03014031014481c1440750101c00f81c0280031522944c48a03143c0c3c00c40d40207130142014a801c0340d00c1c40030307180c11240300d80b501411200403103524003000302c41450b155484e030340703255a0070607140d003140c0c1002c0d41e4034000303 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 496316771 1250 496315521 496315553
    0x8070f0302160f0b01080a0b010b030c0c0a0b040507060336051f0c1106181e01020414060c030703030c03020d020301030809010f08061e0f060304211706090402010c 72
    0x40c410070720f909003003440c03404a045e40201e881c0d5021208000c0095000b501c0d4074111600f0300c1d5055240c0c0d9400703c405030940314a00e0f04003e2030087c400201d00301300e00c035005c45025a00803800c84070219101c180540403030700da650034200ca00f080d6240010042c280000d100452143c0d040d024001002c8540c0c500e071502c801c0c11012910f0b9100d090030b1103480040e030b2084a00460b0146031150488503907810064860401070549400c4042c6194a1014098100180503c010410009591070b00d4039244240c000e402c140180001000c001e10780052519225086d10300148903200a545400b116541c15002080c010304900306058081c044000428000e101440c0217501503c0d1081e590400040010310354500300c00d40c2c40500141c0d00501c40545c0318101d502c0c0e203246400208001002c1c0c0c010010b060391035030407070aa500010001c00c22007007002c25000589c03141000d444500002c0c01c421800d4402d01141403001000328000c900060729440c06e0306040f40c0003401070411803158201c6455920b0022a00e0076 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 496318021 1250 496316771 496316783
    0x14032d0c01110a11060103020a030b0a060b030c1827150402031504152601020705030a020d090b030601080f22062003090304030303020715020a181508070f030216 71
    0xb4104071403d404c0982c2540004d0800090021903046a000440c00da1141c000074005810310000140303244103a92100700a88000f0301856240d180c00303030065540360b000c139104440044912407000030600f402055258000d504030149207800e030000c0500540054010300b82030701c410200800300d146d61a503100440c0501800100810031904230b07428442610440b192459551400803010806a0500b85c20000c0441c031420040092860754141203000e8042d004000d0035500000444a8409800141c04400c3c102d9035120754000991380c100c5a082404121051070204890382c0000b0080d00241d035601741d00c01180010030015108148070a2180c1418080031201c2d541d40d4014100301d20032025082c2c2c0c00c80c104210491840c54456841500e90080344002028150081000f00801016804000034080e40310307070440d11541800402030940341c0130b14400540c2d050f002d1001c01c9503450007150850190450701e1701e00e100c1d214802c0c21540c0340b810346c05103410144e0038010303000713202e42100d544004030b40200 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 496319271 1250 496318021 496318027
    0x90507091203024c060810021b030301120803071b0b0f01050613050d080405060c21030402031c051308070503060112051002030a02040306090602030414032d0c0111 72
    0x1c80f103210282d0300843c07078100403409501c0c0400c00c008044a000220914240c0e6070460744c840d2036803103019050680104510b400303504500821a0003a5020304107030300812034110040303407040000c242c4910003030140307030500660701b10020b0102d2044c0d002150008150710700041840702c142c26401c165001c5c00ca08030341c041c50003800c2c8802000b0a070f01700b07030141404440b811b00d00040541c01d40a211807a1140b039000740c62442003030040c45062020f54008000c0500143d5940e0104102a51210450a0001080e600050b415000d0740b0b03c0409491003a43d000d8010002c1925850220034038800c00d5405100700041000800070300380f03050707001000522407080100744403405c0004040c200401600708040c0500f035004a1030201c0d0340000c010070078180040c00166240c4848082e00702920841e04040c02c41402c00c0242d100304103456005521450144400b51200c45075210150745a114204041d04200e006074030214480c081401e5034207821800740400ca02e4420b24a401c98250b428000391244008408 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 496320521 1250 496319271 496319293
    0x603020711010e0f04110f03010611010e03030606030a09051e01020403050606030a0c06080916060801050f011806050921010501030201120204150503090f0a05070501120b03030409050709120302 85
    0x400a01c203001c20007401c1a600f0540c0307031000301d01e20700d01038401c081c8201c1c1c54919081c500c084100c00c580703614580d04146c075a2980c4410340500200301c58007176418a1341c80c1886220030480d010041c0d1b4000c042c010641031441e242c07189040d001d8140c500042e00c0340e000b20342040c0e0250b68a108254044240203001580315855814410305064000340014080d4000d202c8000004000c01003100540d900340c2031108458484504003440d140002803441c200341300480001c54103d4004c40194100c440c100d0b00042c8504808004440403140c21040d07803054505c411050207454052000b5000700c00000c1d1141c3c100d00017071240041c0200c45141000300c903954810042c800c1d541d00000c480105030380b401c02549800d150a58040d58118a1601074042103004000705203040428460b844a02400d039045841e07140d0755081c5140c40d00002d110342c0d404101d8038802e607000c58402d13000711049514000d0265082915203151007000d01002070a1070100030350705030701203030b00c0c1300e1544035009050180e0f00403c0100c900c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 496321771 1250 496320521 496320533
    0x30d230d0b182d040303090c0f06120e030901020703060b040b04020324090408030609131202100c0e0a0b070f15050f060108060f12121b0d0c0c0303050f040f06030207 73
    0xd92280302000b9403401d00d43c804071031229400c00d40180d45450001455039503400d140e000050950401c000d500d01c0c3c14000500c20343c2c002c440c2c0c46440415001000400a1030f4111341e17403407007403075a52400340e041890100041815075000c40410b24003d40081100c9801c0c0c0001012a030044422812840c5071100d013403080b41c1c450404c0c1c1c40c3d150701510001c000307003050f4032a0140340c000104002d02c40c44500000810140140c041d030b1250a07030002d1041841c40800b82d000e034403101e20481e409242881c144007112218401c030034a04200102401003103029040405d802115400303113205842c0d00b08055004000540420254400c24480002c006032500746440302c40c00b60180641902c1c1005a01030901c8469503400002c0d40340554111a030a074500032054820b405c0c25001c0020000307140307021410005550916640ca03e698540100360740356201000300607500c0b03801200c4c029220751040311040c400030f4006c100a060302c5110394071460806076105080380038101c0c10b0b0041b100007074001c2556003c0000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 496323021 1250 496321771 496321801
    0xc03120201090803040803060d0b09030c21180402090604030804060201050c0915030402130501090c1e05040b031308030103080a030f0605011e09080f0606030d230d0b18 74
    0x11600c024002801a921042c0caa400301400c060407841000021a00f01e43d42c04d003c24481c19400403115a040c40c010030040d032a50404419aa041e00070a8101844228103001518604c9000170449003030000d0098030344441d2903a041031035041a1f0030003413040301c0d50701e05015200852140300032507502d506051000382034038401b030140c4041c0141031126150b142d40d800588850742003141a559143d50303035400002c543d80f0054400c0e4054912300400402c0460344c9408c800a00075058403104020364290000781d4041c05511041e100080c400e100c04e0107510310200c0107540281d4140306d8012140a00c0e114214a580300780e1048455203c0044d10200c51074043c09104006155140c00b040000c2c6010006850441c85140941381c4451009144903001d0041541502401e03000c4100d0b20004180140c3d60f558074011b8503c05d100384601c0b406801803501c40c84500d4058914241d0243c08092108000b0b00d841d0804012044966103500a10b80142c80302c2d00100544074801d004940a07050560909020381 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 496324271 1250 496323021 496323053
    0x180f060601050a14090a0e070e030f070e07020a061109151206040506010903080d02031b03070903020d020d12080a0e0d083121090503060412050c07030c03 68
    0x28219104010440c0c0e0090243e030301070520741c00d08006004600484200a104039015150700c01130300304010640001401c0d185100d06004d4441e503584a03541c104156580048541201403070740581014070055140c560f0240c0c0000303007801150340000c016954642030310139485a41c050313080d004c070342d0a1030b07450a4483c685006848000803450903d4031802c0034800000180b003607001310344500c08115680d210b058114019038110180355101c0844070714410203588103890131880c8000c45241106180c20345d0b0101e1380500d400d500c4804032980303140d09028600502c520705a0380003004904104c00302d000d81a0100882c8000d6441c02403030b1820032158801c90300d0105500d0f00e03540c0101d0051100c01c1d0800350722600810071001001d450240602001250b205400703c1404040b101d20100c001c2000402401800d903030f800c51420090840c4450403030b0b16002e50303c14941e06510100c041004034180c1c1c2d0840074840c0040ca030161800c030002045034a41051507004507256000341c42c0410501c000e000c030280001d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 496325521 1250 496324271 496324273
    0x201030c050405010c030e0f04060e061005250512040608040c0806010b1b101e2018030c100903030909060605190203070f060902120a032114180f 64
    0x1c1030503c40001d1254800300d800405009540500c600c450f0798a00007000c40c00f600600034422284c441c0c1414030010000d8a007107008003171506001c1d43d550300070b00944a20f814150030810310600303045a010460151404280c6890084a1003080c076507c140c030040001c2e02a6440f1858141071600c1d28030180090b9a11141aa0f0403660040c000c261495003101d660010385410304926407085890103041c1040e8580804001d460114114595487ca084c00300100c059103034100700d4151742c0174540e050250355600344000038408200d03140c1c0700303e4507020341c2540c440040e00311f85441440f400410b502c1c0d001d80701e030740d8046545000c003082055840b8036844041c1c031500d00207205c40d519141015246026440c4410020340c1400d4442c03840c10303c00c000f5900e0b4150031200710114071451341411801400400390a0b0300582440c1116001c1c0350000603e000761a90603618070b08004602d452006c1d041c403100481098094544074501c1208a142c8029070281048a58501c1300880d81070300c9900c2c088011404081d5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 496326771 1250 496325521 496325527
    0x6030606041a01210204030605090613030f03020d020903060106030f1514060c0a1704210528050109050309030d0906120207060b041506020d090f050d0503090d0305070201030c05 78
    0x689034030000c03100500300303080c0101410721306003104150030010f440c00d001d021720100d400002e00507240c2086016403c02d40039641142c9411115645c104d880130005130203d544140c180100b98403a50042903032802c901801410000c2c83d00000c1e08244081e44038100094071081180b54200040c4180520100001d0034802d015292410304021106840b00c640e11a24000c11242e0004509116401d8121342c00410241080840c00c2da02150b60000e00451a00331b250710040441c3c10107201a400040c1e0f080340003048a41c050070402968015408203494a12814812040002c1c01c01d0044200062160003c1e50321000d1483c103152524150801c6a020060341c0002040721542104852654000e06503000d43d0781d0b265400d144000d00010b11445400ca882e101c0e40e0181039000340c0060301601d0803a03080c0e80c425803000304221032240f00d45c003070160000c1e481031082003186072240100e20000c0c41103003900d061207000000900d080244417070542c0450030009081d800c5680c54072890803003d00d141400d83c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 496328021 1250 496326771 496326791
    0x1107050a020906040209030307060c021c210b030a0c1e030309090f1d03030a3b0106030f0b0108012a0302090a03210806040603050a0305130b030f0603060604 69
    0x5540c8200960190268150b1404600641c40c0d60301214005c0202030f085039541c005e17501d020002003051030302481c014003c452000c0c600c81650a04c1c86c92607901680e4680e5040c2c01441c3d404d4801040c1040e000c02c1c580c0e100b405000760307101845071030140d40c080d8441c0303c1c0306c0e1b10f040b150040d9440e082c800301c0000e901d1480b0500010350040c50740000e82d401110002034400390311000c80024215240190715068096040150000c800001188140c3c2840c10a01c001203004c0d04941c150b010001d034009003040b04000000003c100b1110b07000d050580354001141c059a240c0318000203065020042d600840b03010014000e1590074007400240c4141071b00d10003400400c80d060f49641d0441e4004020401d0340025208840742c0d15501103802468000c10032404002080440303441b0390144500501c0070410384000152640f40c640706100c00c0300e0700103020f014610002c0e58122250742c02600c140700c8140000a020603610303105d9020750b100311042d080440382401d103041018600600108151f200d1070030601000c07 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 496329271 1250 496328021 496328023
    0x1828110a050a03090804120510200901020304091802012606130b040e010203090d0201091a07120f1a2710030605100504050f0f0f06040b06070302010f110705 69
    0x2406980c20361808035200c54500c00124090503010402074088603010030040b4a0305000404050000d201e00100c0d40103e007107030f803101b003964100c0240c00004c914401c91940b446d60800d00808407840c0510603285082d403540c10000c00c660002118004000c4048804070031941c110301c10800840c01e0303821021801004286170500340300000c0c403150081c0ba10010484108240b60840040c2e104001c0060082e0945e01c03a245000b508102c80c04903451055845500100d4018032030841c010380c01c14903142d00f1800d48030380e0110500e00174150504001c242048040750514500c205004101030020114460301c07000003103202071852030300c424401c244200060018140091000c2400d40e03410380859460303514540a4001030019038406400340c0c1c00d11007041101181c0c2c0c0e008bc01560380458007004551150400050004070855007401c83c0440080480e1140b00540342c29075000200600114504074038901084094001001c11000f503074669000d410b00100502172024507054501d20b8504001954070b0309 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 496330521 1250 496329271 496329277
    0x108010603024b040c020a20010215101d0405101e09020112110909010b0301031509170c06071e020c01050309070f080f010e030f0304020f182811 64
    0xc1e009440e00c18518500031105005004083c50340144100254501c8403c007030340b2400e1007007003144d490071200700031180300c500c5034140d030384802041e4000c1c0030204403490441d44030380001d0404510000d206000040f009000440f08600d441505402e42d201e062510f8080c0ca03240400710810b8019003000400350b0b8550150306000061407941c0340214114265000517111aa0741140030485241030040540c40a81000010041040300707660405a82e030380c8202941680c00280401001102c519a02454003141d0b07405c4034407070b2801910290032212036502641080d9001441400e001c0c1c0000c010403d245410109080b411100e10742c00180e04506044020344071598807010b00d050180202c00714401d80e104111000c00b07440321781e2800c0145074941814a5603601034440e00c040b15820002a4844013001000351045a07960000c03c03402d546541d403c201d20684048101900020380300031001080042442a90040d0404810721381070018158102c51441150240c00d014582000d08000c1c2c21440c207402c03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 496331771 1250 496330521 496330609
    0x20f04030b1312170f0604271a04050c010c0501060b0a08071701050102190606080304060e0a120201140f0d0906020408160b0d0209030a05160501092301050a17010801060302 76
    0x29110a40d0784000040090044071105540004510074820050a1404144048a0103118000c1c2c00604000c5000f80f85080ac640051241c0c1041c2c201c03000c1940150291400706110307030300115180d0b842c0c2101050580000303032201c000491510a1108103500020701d545100e2091782d02d5012907040100103590782c600c401850a0500490113982c0078089141d00c0040607250810030317280e0b51546c407000100f113036060151321403003072400d5100001c10300c40010030030f101e0f00d6060311510071800c2124403500ca1900f0003a02e0004c2e8860401c03003074402ca080ca00c584800c0320b10070040180c469081c801514540700d15800e640603125007060040c4210700c481700585210b11401d840240e514420b40002c00c2c10002c1c01d0500902c10f00c00d02e00c2c5490701d00360501103141aa8400c0ea1079490443c1e96140026030000035185d480c8000d45031208440381544204004d1941861034141410140860368441030500381c26400520030740d640f10001d00840c600103e052420540d083c400446080c40d240d4181c40207845e440c2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 496333021 1250 496331771 496331791
    0x140604060b011106040b150a17071e080d05070807020d0c030b07050403030804120c050a050714060307320d0501031203020c030406030c020a0206120907051e04020f04030b131217 78
    0x40c7c80040d40d00d80c0e2081001c0c1084030f82c26131100701000c020903600d8440e4040d0503401c1c482985001020303840010340d60100c82550001b491800c464074000d886650145138203460048080060b00007603100c426038a2840c078070a00c03c0c000300038a10700341160081000f400b0a403c0050410080010aa00080403508990801840580c400c07000c4020356444c121032100601074000c04100780140030010400700211349890001303600081d00344c41080030364442110240b0128220701c081d2070500d08800c80c41c20401b0281da10036010307200d200d44084410340109412920b0b854407000180100001c0054540034055141030035410080c25404440c0c99000d180101c0080503600c038074820a682c4200441c0c1d14464029000c07039a80c030341c46940d400700003a046078140e1440c03260740c000150030b0410905411381c4540c40f0f815000201c40f81d80400010b03501090b4124124803003400b011020440510b0705030301031180e0764041810390156242c000c02c00c464002508081c13001720b0401c068000c20784200e80e58043d610b51 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 496334271 1250 496333021 496333051
    0x14040615080703020424080a061503021810212904080307031b0306031101020a0506010b1605030f0903060a0e0c640b07140604060b011106040b 63
    0x81d01715a0300c1c6c8019014a01045000700f000200b001d80030070412150350055a0901140f1030035980030317012003828840290400ea0410071110032101d1802c3c5c41d81c00c0042c010030714030103699501d0020301c003230130680300d030640500c81030404030030004107100642d00215002c2c030109405016444c50030351800001d0010380400c200000188007240300368803141e003040490b040300240201c0100020010001030108456038048043c29074547d41c000107107124401d600100030800340e820000740302402e400820200f804030400d20744800c002541030001d844003410201c49284c880c0240010140313454005821306070304a01c0e02c14501c44886010601c00e80850341a6045684c44035424607203180d041020302c510240c1850000c0310462022003003c051340ea0441c162046450a01c00184250482c1101c0c52540300c80c4145942080f0a440c944003a001c0d4038040c83c0f01824000e041c0c08083c0c1400c1c81120201d030402d0f5110030020540d030b0003c01051140042c01e004000900d4540d4038030381c0302d02c4003602c1d031584a1084 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 496335521 1250 496334271 496334291
    0x10120e070807170304050f01090308040b091305061318080d0f060b070f080319020d05041203020f16110a030503091c02030604020f130204090b1c030c0f15140406150807030204 77
    0x2400d203034270045500100142d07459989221030040750300f280c102c1030b20840c09400001c82110071805100e0180c54000c180c11030003a501700001c0000e228016481a074600749004480c00300e607100016203158040c5c614003150444841c4800d03412070394140c211558281081c4100e102090302101d541d080d01d90700c251520755903240d0f0422804440c08907120003000600001d80d0351541c85294003c83d0146208012005800c121100300350180c1c0640c903081c08419609006508049544000403400d1134000c440402c512499400403408a075500d8205948542c1f001031101c5032401c2c40b01c41c501c20740064004400802103150300003915a000030f0000792040d81c03180c0051509035696071030f0521000b0325442c1155160b5884540c2c0c0090710001c2d400e03d12442e0040c4500d46c0000306200d19a811503410b41e114600c18605a40381011112141404da03042d10b00142020b1000ea02440782030f83c103080011220b042442c0074500300703058500140e13003c02031040508003040142c038001054000c0c2c0c0e0741150046203422513 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 496336771 1250 496335521 496335527
    0x1c1b020a080d0f060b090f01050f090f0a05030111030117060601090b18030f0c030c060f0f0d0209180f060d0305030112020f030d030204031a130210120e070807170304050f01 76
    0x1e011076581e42c81d1300d4141d0015082da00300340101943c96090300c011890105110056455010341d12080c10b1880f02000840d02d28030b40498140b0907104024401c140711a1140c0201c2e0850340c005160100703c1c9800001800100301c008600f0f009042c0010050403e4544100000c110074241d11074003104110204042c04810408a900b100030035024003118468610305100725038404000f020b183c042d0003000c08205803410030300c04965046800d01c1e21645420b82c081e5480d60240c2c0000401d02c141030b82400740107040d40d07480d028000a5642c0400805e0b080c248a69208907110003c1d00c014410804082d044001a41140030342c0c4c1110407080296980d1141400455041d898907410300e545802030220300d411094160f8041c20541e4010310440350000b01d4007617580302c50001a2410001000340c0c07180c02005160211121681c115580303071556100284071100e86c107803419410388803041c1d04810014419518204043c0e001040070746800010080310340c2009440707124070301400d03000380c81c0011a44401d0740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 496338021 1250 496336771 496336781
    0x30e09060433090203130803060105040905010b030601170f18030f04090c0e03160513090501020c060138030403030914010f060902030c1c060801021c1b020a080d 71
    0x38070100b1042502d800a0025598402440300310311281800440810001114401d43e485000b003d400964000c1c0c26481e4054590001408241000303c00c01012980007054001c0303500074516540d0007902c070b04010001500d04a80000e100095020503810022010000103840343c22032040803032000d0303c4158550070350851098811505134203200050000b08220581d001d440800300365501c1c442010089030400d86c40f041098503503201d01e56800b400740302925020090040340c0c1ca85031720002d1170851643c1c0707490136a08000040c00740c41e00124010024072000d94086104840c22000d80603805520000d820542944600071641003000800000c003014003a6000951003134000c0030000680c111654000d018014010000d0101801d00c50000b4010b01c090080e01d0082040c03602d200e00b4011031042004203070504d10001c00c0c0302030702c500700041c1d5014284002c2406c1c03d080740d049040d805c40315034440d05a89244030800540a04900c4c030854465010400c00c628503440a40c4030f584aa1409100010345 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 496339271 1250 496338021 496338041
    0xf020409110414030c0d060f0603020a03030c060507030203060303040905041a01151116060f02150a0f050c03070e10050d0501060c050607090501080105150f07230a030e090604 77
    0x103854604104007140a44001d4002c03540c40c0616070940c0d405030802c0c992507010041e0040d030014035414803e400202550045020f0f40c00c1e5080004c0c44958a40001d81ca4000366070040d40032981181d2441e00b4812540100c642c07095003400e0a601d541064004213649100314401c60300d100d5a40c0b0013190411048007a209240d0103815040000c0b5615244000c800760881c10303400000c2011043c0380440481c000c618010980c0b001d6083c80e031898944041903071079460041d41001140101000850420070b40360b01540100183c107800506245151600002c440b03000d082d1207040c0e00184100700c0710a03440513403150041d005440c01030082038001429116400303050f07000b124072401e050001c2140c0d90b202d02060305031070080d42100e02548400c1d03019118031030f03940501da0025400308018421414428003a0088001c04031082d850300c00880f100c03060035002003004070740c130807d43e07240d20080b6004030742e802d143c124100c4050040e102041d03078050940c0c0041d00e403e5005500503000201295610b51100c401a = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 496340521 1250 496339271 496339289
    0x20d0b04050102030609071b031b06060303020609101a0f010912062306010e0108091614010f0518130914010b01090f06091701062103031a010c02040f0204 68
    0x203090600c0c10501075041114628041c101e4800014000b62103410207003009040038007801510700301524200c03810f1183d81240c6207001c001d9022007000031250701c40c0c0350046000b0344c054a01800c25848075409c0c08a84401000b51504000802801180c006581510101c1c119040491200300c0c10058918044641c403262403580d119500700b09004554109042511060b140c442918020918508090b403082d10454000782d582480c6040d01d500854003190003c0c41c01c2c04680900c41d460003200d83c0c001c2940c008002c2400d1800444013075581017001e080d00034115050007170400003000201c11615484444c0103114100c202c50078440342ca0998403540e80d460300201c0c858420140151014084e0084020040c00030b2504100080c0c02c48420a440043d105150345071540d803454101001c80f000c2e2403c240403c01d540c4c4040001e02c0803041c814407400030600c10010f0700c03034051a080107000c640e030750f1041c03480c0c5c2002a1148441c50b0b80c4195641382c02c40d412200064607100480c035550090240343c0004800c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 496341771 1250 496340521 496340543
    0xa020c0a0c08060106092c04061b0309020307060302070503161a1e060306070203040314151306050901061203030c1112180a05010203091c080307110607090b090607020d 74
    0x65000c0f80c00f42c10380320f85842d41a2516541c9481111504218180d00e00d602c600d401031043d003003c80c0b0301240d0014081c00300420350845913070703920848421031241c29010175a034a84420450030103204840003011181411820103082d40c65003501e07031107004d440e156044560345810041000d683c1c80d14404072901104101c0354a410b690b00210851510b1840d140b2180c2d041c001502842d0010b0395510034000e41d40074605182c65980c408513040c40b80703201c201160242c0d0380d81080c00d1880c1c0803000e22074480300b04140210601e03818000202d9030054003d4100340d06060043c04004413480a1400103945481c1c0055554181c0c0022214007180000c0400c15010746085500101083c002804004000720603400f501d8654104106528603548511405a0070500c40400e242c5400240c0d61400c04461780b194404100350b64440071294130485500000c1030700030007654914407040100c5a81720744603080500903103040c59440d408034040c0b114030612400001511038119150820740c080b185a0109070400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 496343021 1250 496341771 496341779
    0x5010c0c080303070f08060a0b0a0c0809090406020702090c1617120a0b01090603180b060604080619180f080310050306010906050f0303040317030601031d010c09080a03080a020c0a0c 80
    0x5001c0c0c142c400c0000510400080b0701c01d4684034500400311509d0541c00d51421107107100c1030b1240c0c500c14405a80e4618148452005a111003d250344604d120b1580180d44406a00c100600b1500250410b514600c1c140040000c07a18010000d2044540204002881c0e08102c56100f0310f520401c001800320300818803c5c4806c11540e42c100b1a080c41c2c00341c03900e4410130b840d064101d084880403081d83c403400c20070b0511107000c01c08c2c000d80d60350011406002d0742d1609403070701c5025107403000a032007512602940101c22f1508012600c0340324903420340191820401c03842a16000440d80c03054002030003054002000c0384584040c010648000c0074044d080d5040d0b5031352040c0703100080210780b1400d40900468000710481c2d140220880e001d0b00c0c0d1044191603d16000f00030b0034a6504014030140c140741d039511112000b0203142c0c00401300101200c001052201039a1001000c85010f58480c2100d948a2507200d000240c000c00c240d076100c5030381c100050b1118075802c01d961501c010344502030041058410041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 496344271 1250 496343021 496343027
    0xe012306160c1415040506030402030a050610330806040f14180c010203030a090c0504180510061a030405011b020714060721030b040e07260705010c0c08030307 70
    0x103080b1083c00380d01190f4404400b0900c0802c81c101c0703400100765841048140411701d0540061a0440d00180841d030701c0e07a201c0e5a69034a4a002511303004003510800703178200174918092103203c401182444100e120508086a00e021400c0791691203001d203c007000005409448a81c08284d00490858040c000d040c4d01030240b007480801035a8001501c00140ca07501d0806100284d80c07846201c0c117900440c03031076403001c440500406940c0340440d210010040c0c0010b503941c2d18098100003c03444c043c1c00b141d03c8801d10f0300c030b8900b5400720041011207050400400c4000c0307001d252203256200e104034071542c03640c2c0c07450312500403c040303e4480c010481e401b620350b01040c1d00080031303015039000c0c2d00281e6070000d090301003100d24040d10f040206860401e8500b41c0b9a413811a13019018a609030a021401400c410001025031301c858107903a1250380568004c009070103807a030110348240129100b82420103820901c1c952034142c140120703070511000050130002c00034a15041402032454000350f0307840c1d0410440c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 496345521 1250 496344271 496344293
    0x6090603050c0d02090105121516030e0c0f120a0807030c0302160f1a0d1e0c0309170309120703050306041d06150102010207080d090c0e01230616 64
    0x203071080d104954122140b4200f0541480c0c07800c2d001841401141e1030401000006100310700c3c08611401220003080c0d10007e00546d241c056070481a40c0d201008041d007004048a40766044c1c241c940e8014152505162180100c69100304016034602601e0400c2d10103040c82d000501350028044640024410141031b0711503070007101144264290b031803201c030101040288001d140110307031880520140070003103455482d4202403403c1d6082102401c0c807940d0309010040350035207411440c10180c510b4031801198828401c0140c282510f060030060f0214075280e164000120180030004407100001041c00c41c1c5c1e04003c0300c12400401c0d2a0380f9540d41c510300d0b0040168100b80c1d402406507040180138102d007880a8a07103540049a1030003481c8030b54481c241049071000902026041d55070030066400865412001030410340d01203400071641e40d0192070700c40240ca0f00c2d540403400901c00c1d4070040c01440101190494401000c4081c1802a81c024000445510600c0e80b9070b040415114194801c001c900c03480 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 496346771 1250 496345521 496345523
    0x1e0a050403020613090501290732010f111c060308361309170708131401050f0903150906100e10031e02030303070917070302300106090603 61
    0x814070842e41c1e100f2303912003205139241d41d80301e03030b01c050b14503280041c1c840e240500702e400d0143c04100340544483c41641c0900b03541240f200d00c108003007590b41241c80b009010301a5400000e0318208481703c40518144424091158020744614008098064076052504402c01071a0002840360343c07840f805840c2d880145043c1030a0740003100181040c0042e410b0800e032104031810281c03d207005080103502c92002001c00d61004c641020b5442d108004c0402050040e000280c4a00e81c42d85e03840034034605c02c04000100303030302008101d1070030603255016982c06026281d00002c81c0003666210026000000d0038200c0b04415070104807100f5081150503100000c2c20390184142c0072107036980b941c4504110088050403241c03230303580c0061003408000013180400018507840111000710f907408425030010b41158000d556400020710b18040a10141d140312207202e601d01c035020300800b071032403071035002c01c440170b4400f0f0312121720301048a8580c0c41d6941c02d5404c0303030610312203000800c5220b40360f150300c0c4014401c0b07000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 496348021 1250 496346771 496346789
    0x6030c07080c0a0c1202010503040201030513050d020f1506102105100e1014100c0501090302150f010501091a13240c020906040207140703030e010e0102031e0a050403020613 76
    0x4000070317403c07200c0c207500309959010f039a01480e42c0e440c0e40054024040103824024242440d07007203039000c0b80041c402c5020411055001d010300c2510b040b4820f10305900e00781c260780c40501d41d00038007803160394000c90500742503103070b00344210511050360b5004030010944084150003402c040410400221024a26058441e204400d4455480e45141c1089003001801000b4a04442d0300e00c09101d450301c01041011041d81d45000b0240e02666600c2d10300755203000340704801580c000c3c080c60400e10b030b81040f884da001034109103401841d894540020802005445014024030250042800c3c00350f1000440f6044000e0034542c0c000135554007010300c0410034100300a0320354440c1000124840c1d20401008400c15001000030710b554807074808200095002c010221072400f00104d50604820f000c1c0103100c0114043d80365a20085501c90014201805140c6030a045402c20062510040d800b010001c00907031040d08280c1d00d07080c0c1d0705001c1e101c2d07201e47e810103540280c1c00b084413a1047c000e0390b0420142c990f194 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 496349271 1250 496348021 496348043
    0x1f09030212010218013b030d0206040b0a050a0923060a09020618030c0d050304150305070203161b090218040905070902030a09141e0304050f06030c07080c0a 69
    0x540300a00301d00444d84c000c012660b2101c3d0503045988a0544a810382c61031079070039800d4041d00d01c1941902d19801070b0a1001d00704080c0d40c0c59840ca01480305a450000900243c0795a150640c2c070440c207041e0007440311000d00d80d01c901140000481d94481d601c00c2d50b002e02211b02030700000b032030300b02108035003050350742580f180d500001e04541a42c0200200076501070a4242004103c10300a036000164020041d09403003411070240441c0ea942c260104820300410141d40c0d00d40c01d06840140141c00110f44509050400050061480d4000126007040c08640400c0c0010107007403a03c48007860150111035041c1c000c0990119400801e070b40100369940400c0b01e0300d102494207170140001d5640d50039014010b50441007040001c4502600190f5000c05002c200103603040c881e40d1500303c0b01e11481c0407401254441c84460701c80c5840c0c1c4104c207181001a20007141068500400079200300342c1140d90340c1c080c51010000c00e245180000a0300da25640c09101c0c4d0ba1540070700307600d0380c1c0c0c0d82840d0784d0150344141c0c0d01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 496350521 1250 496349271 496349299
    0x9050c0f01113022060306032d081b01061502060f28020711240903031921021201091812090518090601141f090302 51
    0xc030600c80940c210340c0040d1925212418500b003404a80c80722100141082c85003403210780390301038020300d803801260001381806028615160882e90084e04484145854402c0c1480829003c59119001e8400c4100c0c0c04010254140f1421120310311250007000f2100c041421030441410407004021440301100800c1000c0d9a0800c06112000da42907441c0560005c5001c030341301403101440140c1c0601d84100038850100049803464102c0c060100c600e000c6640842d1000030044c804c2d40311080c11800700c0300e450082d04443c90b441d124004d140300030b071f030b60703440010f1242d905032401d006446816078504c3e1100941a00300070301500704d46000c1c00c3d4004000c81d0400b5241c445e040b41c0700b501c1c40b00990072501d0407540c0c20701151800030207541c04110b840c1e100003041e81001541464a0000c031601a9503001c3c4440e191009014400d1518804400710403001c0d410040c0a0700c3c0080c10a04580f5580858414030b4002d81c089101d694015260109082c004070b80d0701c5005401041e51401c0b20710a9509036408402 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 496351771 1250 496350521 496350527
    0xd090308011e0e070503070908030304030503040309050111070605130f0816050118030b04030e03010e0d030c05041406070606080304060503070e0a08061611150103020a05032d1009050c0f01 83
    0x10364050803c0d10b071545400f050f100c6200390091342e0305c2030b428206a60b00c1906d070308500e0300d150800c560403800a080001040101903000e040a002803500f800d19012251104100c1600e822580c0510020040003240400b8136140740b134bc0031002032403484036041c003c54580d00165195406008040183d4600c100c000886520a50754504142402001e00391400e00b150f417a80300122000c1c0c4207a04000081180010303a550a20030009591101c000820145842c0b80e8040c080d10301544005062100500040082140040b44050341040c11110706550b200e82d403030075000625254020080c2c1d840003140c003180c055000340007540140a161108003259844104100c0720408034080d034007064000c40041f0b05007046a204001104100341440b1440e80d110551880c0b800103862a5003031910b2041c401002035040190704440600000d50241003c601a28424814030010b04400241100940e4800c4010b010074002c40c0322404104e54180074800c018100665036001d50111540706000d8400c2c98125580 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 496353021 1250 496351771 496351829
    0x40150b130912210902030703060212090d020d050d1e140a05010e13030e0d05060a330b0307030e01022106101e0203090307030f12080114040b04020d09030801 69
    0xc402c150143c1010003007100d560140c030120004981610600c00301100003000c0f400a13100c98114000d544215180c2007040340e1901c40c070801c4032000d6411900d030290059511108540c0c4184101c0300204200007101e06a9404002100900703101c64036142501649d8203030544a00d000e405461020b0200c0d0343c8402c02c031740c1c51100655102030489000900c240000780100311144100e00700408010140d41e2075100c10341490001c40c0c000940f903584100c000000c41c446001600c4424441010700191000344a000c034050079640181600e0f1040400020041d5210740c10044038040450000c0d9101c840e09090740d1102074181201313040b0b0030001c00010b8054240f041c1ca03203101e040d8555505040401d418110790750039500504000c110300080001840b00d440810081000310b00c00d90119540921505052244400c03001c8403d00700001000104050b0740d081c14020440305085a0020300240c1d103000180082c496446a44415414609114203254100750b055040b902c25503141f090841e06815006003401c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 496354271 1250 496353021 496353047
    0x4030308090708010e0304060f020102090904110406080a11011103160b180d0f3507020d110c150408060a060f0501030204031a06150340150b130912 65
    0x6403047c40708021541c443c81c01242280b100303000040c500034207900807452490085a007a60045003401000e4000e04061050390007c100742c0700544801c0742195180940300b14010040d504005040040385048402402120302940451b401034060340308a20346031264500459400c0c94200c04100031420ba071501003500d90710926032741d450f4181c41c6901001514900d0040b07040c4012448210307014502210301141040ca203443e0aa41c00a052811000c001c0c90f00e01c194031002d081010340b114071892204001085c080c0c20004507600300f0713107034a00010300700f0500441d40311420f54421001400300c91406944260181c480041592701c2c0242c4800064080c0d03c15132100401842c5841c0070301080007490305003940c1003640148400c0380140951409005600280c4001440d0007801d000d10760040b5020381c40801c407095144544260203030815071040c40140b80c02c1c0150408803c0f02a52008000c1c56000c00311078070008140141c0000800d940710000c01c1020b004a03041c030110882080c0c000d0150342900840 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 496355521 1250 496354271 496354273
    0x11010504060c0303150b0703090f0501050c03030c090102030f04150801061d0402030a1401030317011517040201090f0b0a020106091104031b0b030703020c060a091709010c0804030308090708010e 85
    0x10710b14a07502100100080d091000c10000e03214000700724504c03900014501c80703010b503503642d4029051140c3d88508812a502a44c1480000c00c4100280d502c080b040e6603116104440142e180c4414400607425842031510081c100b107000980421182d086140c176901d24440b50740d466a15a80f42d40e01628504100e110140304100704829104691410350021644099481c03000314824072820a000311000084e042140464480c41c5d1660781c2d60202c2039901c1c01400840d204201c10560500051310100d0b10b050701c0c040c040034000c0043d081da4001c001e18001020465100701d52956100e807088a00e07004040d1440042d424603600081200742c5010f4000703504a990442e82c941403556940e0252150941c4e43d04668203002200061005445406184580d01684002d6507540220b4007480c18014020b100000485c41d00c4034141c0440c11104202120420500615a880b890480160344005800301c3c01030181e58000b03070100c10564080b403c140240072070411180001c0d12403414900782e915a00d554004c0d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 496356771 1250 496355521 496355537
    0x11404180920060d0c020c0a0807081c080402090402120a0c1d010f0b0a021501080109030f02030705070e060f0603010801020a021606050304020d110d05070311190b1810020105041101050406 83
    0x494145075202c03092402d1715004458010311400082845100e880d07210070003035005140d04021700071081c8504a411041c511400c0307440c2c0c1040701c1c090035281003e00042d000e80f03007610000d011900c1d1002940d826100380c0b0100c1e0000318942c030344030082038070301d00501c18004043c0307a50444600e0001c01c0d0506030369810003805d61250401c030320031300c0e203410406002086104000001201d0402032010034040c1000b0400862640c0090502404410700d88107060304660007080300c81c01142020442005880e80d41c4500010b03611940005581a00b2407a0b4982e80400f0010001641060541c0240b41013100c0d9000d03901c40000054181400000a10814010940420005005141c4030054609042c0701d00c141620409007507005c240c005c01c214104507280d6128400500501060a05e4182000812180c0600c0e0a501c1c0c0014001600a031084440c400e40c0406c600c40c91007220520040032600103004554490b243c175000030b02800040d2401c0d00c0d0b080c080d4420007106d504c01c02c100c50a0b5401d98070740e10b81e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 496358021 1250 496356771 496356787
    0x206161b0b030c0d0b090103260a050901080c1b0a0b061c03030207020328030306091503060b030a0812010f140913050c030d03091b1401140418092006 66
    0x9002d60104d404602d9044d42d4041c1c0400d00c2c0e40d9108294080c0d40107030325030300081070a41e95a0f030740364200c0840461004800d200c50005640e0010403205940801c0c80c25180f16190000c41403024003e0440e140f452076240844110350040008400245901502d250b44250b101d9000344a2488208070800c40090300b049004800309000b0780003010b0181c8043c00f260400b84e451982d00d2216840c215800280306c00c0718600c031040c176030b150160901806000904204006041c0c1c509140c0480c10710008080c240c560340c8101150743c00340305403490035030070031100b65031010740c02c07080c01808109020b0301c000d0895804000c01c1d030481080c1c402d104154040e1040402d038440d0b8060440f4010900c0003182d45114912203240b00751420b1110101041c0c1035100407175001e81e50b16140d140c900c0c181e4404034100b02c402c2c40070480004034905440d500da00a0812480402c51851080018400d40d0440640303001d002e000b000783c40e440740c0d0051141d03500517150789424180761110320301c00405081d43c9560140741804680 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 496359271 1250 496358021 496358041
    0x4111c17091c050a0606270e25050307030c050f090609011703040e01060522060903110613060f09090b06031315090c150e0a05060306040b090c2d12070c0206161b0b03 73
    0x1914241100000f10009e603901c00010340b0700b0a468104854040c04502c1c100000c1c2060008900040700807556000f4618101d00419502c00051186014400d54a10186882c2c841801201d001d08460406925590384440024145d41c1c05005c0000c401c0c1c0c0326131141081c158070f0005460542d243c41c3d694000341d074134603140c5840c104000403082341c1c04031080214207018061810b4000081c240764880400b603002c1218042c08a598540c000b2030b100f800e08070485040d40d80c0b82d044030f900c08031850b0180003c0c44941084001c01807103017201c0011a00e41114401801448900e8000b116590f10b0300c0340480080c61000caa01a562100311508200348040500c6070303182030f8024651040f000b810014001500360000b41c4e000700155103031100450b000070030710550500e119030302c28521b803222a440d043c038111041a1005100d56070703600c4803c91417040071841c058401c407040401d030381d00200750949503040350295400c80d00300d00004440380071019240003418a6001c60007400c40e004c0700819811aa1800141 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 496360521 1250 496359271 496359313
    0x70c060807030b0306150405090712060c0201090b042609061b030d0c0804060e070b1b010605100f17090703080304111c17091c050a0606270e 62
    0x25070103050b241d1082c000c054904001c0b0311301c10404100c440c4034903080724084c4011a0406898000c1c59000301d401400603014031035400001a0b07000070005a08410040b0803401003030039283c000c0000c80c4850501c01481000c0e6030700001502c0210100380000302c0c1646481c03541c45000c20203500103505000e0031200310462941040307154000b0342034074601481103c00c00101c6007152065808542a442800140112482018860481c0341c00402440381030502100840c0110004100500301c2030b1021a0031220a4002d50010140a04004440054004050704082d401d039101c4001600201420780540500c5c440075002d0450079014010322411070b2940645c0398070043c03081d107581c42c001201d10344603252801d10030040413003900100c40705150752400901c0480310072900104883c0920502d12541d07a009590180041610316440b00d003580d41c58142d042040114024291a240c403200103415030141c0000e1482024500d804245d42d4000c250800450707455902000080d440b0300e00d0080fa10540003d0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 496361771 1250 496360521 496360531
    0x30c03050a0c0506010602011505060a0503010308280e120d09090903030b06130501080115082706191d0a031b0c06020304150c0b1521060417070c0608 66
    0x301c01d02c9582907031201841e0681c03c0c1d0045006039510f1040600c041690850036000d0001100c080f441c10f0034082d8000d01c10700040c0405032480d100000d1480d801082c0e8503081185c6030310380c03007030030341200c0700303101c0a80a110302d11442c070b00800c10310f400d80c00703034035004a2840b07402c43c0c3c03d840b00d00c15241090441002807400c24000c6051558602040d502c5d5610103000d800302840072a541d061060416000600021040c1d009507408904440b031502c0103900141403d0340012800343c941310380c114403040950000000040543c4131700520050251180c401c0749441c00400503000c003408451140200c60f502090b400b00c01b0381c4143c001c1c04400000900c41c0e0914845a51110051000d0368121b41ba54010081d5030781c00b250141e84001820030100d11140c02c21207106030a4200060004240d4407132030740e090382c0240b200d901040100600c0d4883c1d0781d10444440f0400b484080500156521003005a641c00c2c02e540c15100f042c046203601040b0300d406021500d4441c1c1c0000e00c011520b1a01d901911800c6002c2c0c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 496363021 1250 496361771 496361777
    0x1401150207080a0c0302030f030a0f0f1b0b0103140a0b0411031509060411010e0f240c0a0209010e0403050403030e0609060f030f06040e030a1b0507031203051003030c03050a 76
    0x2000031000410440303a080f4a0082d080045814510b10406d450245030241305e0019420a01003040842c0c3c1141d9039100d940e0341d60400402a402e016000c0f02c04140c5042c2c502c0d00c0721000c15480043c440302c00303810703030503248502200c0d003d243c620090720381d55242d1980003c00100401000600180350403002d038043c00340c0502201da0600112025102940c0100c0e052a0503034880c9003000240301e501c4d000072001440a007080801ca44090b004071f880d005465901e18001c4a510b00d2060350390011500c590200d13501c84010603120a1141d00c03030743d100c03003910b0000d038071889450b000031458589440940e805503900d9290a0300e094a55501580d80701c0050300b2080d40807100740081c170703090f4407000000c06608008114540c0e4030303d0009514914244d0141400b8041c038a41545000c2412000080b138804010134208142c5483c1441e03042d0012210284c0003c060b405080e00000400080031001710000e800e9482c00d01456840704001c41402a40c3d10018000407003901c54072020074002c1c0300400c400e2800345 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 496364271 1250 496363021 496363033
    0x1523030c030609100515090106210e070303180605040e0c041211041a09071b0f030302120a091203050601030e0d0e0a050603040506160c05010e01060e010914011502 72
    0x40300003030400200321403802d00c981010103028884a141e208180e80494005042d2507240701d15001704940a105000352010b00003407084590051244800c8210002c950030f1043c00203005104550b03403601c0040c802180031032a0611505031501d060402d190588003950303242800e25280002218806102030030061424204100104800700d140c3c1911849c0381c0a034002080c040303012000d000c2120808211801c840250040364a002da440f513011581002c228a04800c480c03090032080307900c008010710020304288219051008041c0c041d00540800b001900c150052569442070040698003028002400191520130040c40d040c000d500544d0404c406260009503461040c005500c0c2100a08200000c10000c0c200c6415501d440c58158002d4082503842c0c1c0c1c1142090b0391120342c0c80030003410350400c8440071122500013034829620b0105040e0804001d20446054400b902d000b80443e000c0c250192170688004a40703001c0318001c040801b0340148000c2c0c426031034450706001c0341e4840c00807501140110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 496365521 1250 496364271 496364293
    0x204180804090212071d0f1c06050f01060504030f0b1018060510210e0a0b0c04090b041107020f060f040b040e070f0c15060e010801050a152303 63
    0x2040190014107002d080060340e030b0074038640d0201c810703400400d00800c00204007521410400c410a0307400c0120b02c00c1e98400c04220004001400015024481000c41d00d81d01200d1418000c65804c914024843c0340440c1d0441d03600d07054212400d01c550300014200094240b41c1000180b0100d01603a8004844c100f4440d184e500d41e2072904008001900c103501282e1a020244135074908021510320b07502040c101513128101c802a01d4030030f0074030204145810742e40c5d20503035507000209100129815500c2110340c000e91804c1d5010302075a030040d0190184aa03c3c0a4465005003440d1041004280200442a00385480740d420000800b100852840e044803052042d041100e0100c40900050550b802c4400e45031030404040c942c41810046c0b680d400c2000d8192103404154001d202140e2058002c51145110b00510304202d0203011300340d001405041c000800000d11a1b81035100c54002c0c51000750a0101d46001800d180312800b26010710302203500c2c08640e03032804e903030140045044c1d48405400d4640001c80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 496366771 1250 496365521 496365533
    0x2a1d010206060928051e01080601050a09110412050706030c2303070905100309030311090904020d060207150b0102100903050a120f06030503031812040506070f020a0305030c15090a020418 82
    0x100795000c888051b4281c080c414001e9035940203601600703400000b000c1640c54540018440340d11449001e503c0c984e56225036518400700411100070703180c1404040441800740c98403580e242d85502c6070400207031821051049a62050307150620040211030111000c02001c1c20241d1581d001030080c0e018000c2c1c01034002841d8546180900c8003914a44000031040402d0a02074103851340c0b000ca4000010003004281443e64402c003445403c690180e96031580f01072149410b4000303118080c0041c03c0f000f0031810345401114103400405002c502039007a910911441403510b0181c07825903030010007183c01440035803501c43c414004803101d82c01c4408082181a04000c5003000c641c0325400070ba6941c3c000204001d0300d0031004810002c0040f117003005004011801c2402070082c003450049501c16800010000c042c40364811250383c1054009100300c0c146603907407412039601e50107030b6418240350003007540800c48045c1f5550502c0c4a4141c2c04058480001c01e0740c2000004d14041c40b090824400103031504d07002c10f103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 496368021 1250 496366771 496366781
    0x30f03030b03011d07150c02062b0207050703020a06020f070905063106050a080a03050706110a020606030d020d02060411030109210e0619032a1d010206060928 70
    0x50041d1010340d00b4031006c04068500c60b103074041400f0107644003c00503200d9000f202c0d5041c0c108440d0805400148907015016440b0300c1c41004260300104400303040c018089011401c0b248200c84124085a650f44280d84410f510501c100e02034000f51030410407246c11750403182d4030a000400200205c0030710307540d51105c0c80751070021440021807607105640e500d6140c42002c015040480301c0c054800c0c601015281c0d00c04001c0e100070b08001c00490b001d001c10896400c21080801900c040319142e00030408025541c05046580510911582d82103404103800880c014948520960142826a86035200c6c4060003511644080d050366803884540e0202d000e85103080440070010b08150035100c05820300500800c0c0400034540301e403d0400140c040e40803c030724512010925030070080340030318983c1e00c0d80c00c3e400001205241c001c0c0e4501601140c0690004c09030541d1201c6802101c1142042c8004a0b07882008450307050700070541401080c0514901e4000030b103103407031740c18400c01403510a00502c002d40d2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 496369271 1250 496368021 496368071
    0x180c06070c14010504050604060525050c010215010503121602060c1509070b2209020c03090a0e010605030705070501020d090b04021f051c0209060313021009030f03030b0301 76
    0x904100c1041c0705200c402001e0080111013441c0031800d150501000a100344564419402409000103154000d0f00304401d000d00083d00a91420032809414148540c450011240990040c0074100e120312107a4080481a8140c3d000513000b1b14000d44500003610725075202401e44c1410f030188528650041c1d95a200070040c070401c0001404094400b051120042200071742013062a4014001c140f00681c106000c0e910380e8102d406148801d5040f00c152800302090940042044500020740c144070110000b00a00341400c058a4040d22580d5501011500304404c0c0a2500080c90400105d040c1c0e900c900d025003c800d000e00001490b18003201e241200f21000700f002100c401c0800340811066241c00902c60142c40f00410a105031903402000003400c51080c800000d0010b041d0b03110305040c03d03100380e0580701401e00c05030207143da0f418060084456040050b00492083c00100c0c1c0b0b800e4998030445202d000c0380d90004656103003541542c6c1c10740107009001d28040e050f6680e0700080b15420382c0c1c03040031070300d1b0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 496370521 1250 496369271 496369283
    0x405010f0e01080a0f0609140607090501090f0509010302060915190809010e060c0313050118140a03051e0f12040c05030c0a031b0f0803091e0603180c0607 68
    0x441c80c00350560092541680300006a4001c9401407010511040c60f1407003441d480a13001846401e41c0c40d151800d021200300300c0c3c0c1a8800c41d0204900c840e04003403000242c3c1d400340c940c040900d645070112003500f81a80205a04810300c00010401814250041e08000310010505c1c0c0c0640d200d1041000705402800c81c080c445007011001c841c1940c1c0001ea09030300242070070028826040702c3c602c5207035504030281507540280e00010000e6900070520105808450780301009005815070299040d0701c041003010141e40703003000c000c5481e48801c00000c0c1c1441c4164103807501d500348401c50352072803491803c81048040701e50040000c40c0114110340020b00c80340400e820000028180b5003494940e90030a80c1100e0b000b640003001020540d69a180400c0440c1c0d4892100c2054418010b408030312340d06203500500403010564801310707244402101403d0010b401355544040303d100301d40745030510784401034060b4220504101140310005d01c05a0346620591440448c2d424140d000c000c2101070b40251000d55070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 496371771 1250 496370521 496370549
    0x307170c0102041d1906140f01020c100206040b0a02040e0708060301060909030804030e030c0d14030c01090305041a0a0c0813030b0a1d120f13030b07080f0f010303022109040501 78
    0x117140a415804c0203020f10300c0780b04004560030005550a45140540203500c81d244d0307030140c0f821070fa06c204008e907004071002c0c080e002e103000340d031b4406942e440d01a601290855007000004038640309074401d40b0300b00d070102100040b50b80c903500000e0314040c0c0080c09940d059522058041442d0001e401101d081500c256a44400c0d40b41c1400d000b42075802501c00140700e0741102e40d180b102c1d5034403031410810142c0c0103108284442c41505100e4079501c516100342401d5424000700d1814560004050411164206540400648081903d032402d00c00e0074102008103003e480000081182607014011181c5e8a00403ca0182d88949405969980c115840c00805403181e1603180e19040403003a40c071010b0741c0304005000d11404003e82440602800103846045400071a01c00044c0d400070038080011038003c12080d140e410140002041c0010482740c10100d24400400700711108240d0040c82e040340d4050b4050034250700c074070384005d4152400400c5911481e80030302c45204a95140d200c1d4030700030100301c1c0c06410 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 496373021 1250 496371771 496371781
    0x71a1207020a05031e0c1b0324040b072001051b03010b0403110a03060f0203061008040c0504021b0304091a03150c0d110c0615030307170c0102041d 65
    0x44201801041401150000c8060000141000003510800c1c01e080c804002081c4481d44021400d003c1c0c46980d070b08621030244c100d042d40fa50b108401e406a5002d070113403859400501d01e0450a0144080304200000100700000c010660018416403c00c0303a602d4104030603030705072032034a2804400d00618000c503507440007842141d44100b9881103a40301650101411580340040254040c040e038070018262100310307840c030003035656205d41e540091a0300c400100030230682c44070800c0094108907039403806103815a0000300f03d180a110300d20b104d6075210f01200750365402d103018000a9005034001c0620360007291040c081110302800038101802e0711f14400512120328035540000c052891210600039006002c0d81140340d0305030301899510610a009099846c400703005c0f0300b03004100c01003d00c80c40c0800807071401c0200c04041000ca002e5201000100c5080305508201a00e034032410304002c0844445180402502114201500c031400c1203000050425680d101c400e0020013400c883c0341d01210b90312003080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 496374271 1250 496373021 496373047
    0x216060b120109051203040602041d01140a0305061524031e01060804060c0207050604120209060406061d0d1202071a03040309051e040e0a020a090c020c12071a 70
    0x80380000e1540c003e01403801e01e501c40c6515405000803110884900000003420701016404680080028400c1020368081c072100c5409140e000b070154136010b405d00604518103142004000e07050780d070854060605529918296080d1529041c2c82e2a045412200d046201031640c0181e50305990ba500c4065980e0b280c420b004801c2c924500591004020401005110569110005c0d640c081c1c0e0040d000121048100c5083e450501c803503012503402100014040703540c41b804a0b071081c489200740d91200e49921030500700000e03100b00c0d01070f0780c00040580f41c86000b06a031900c19003080c0100a4007000710281c15841d01805c64503044000c0d409684019000c00107a04140084400740d4100c400035401e600701581d008007904007900c1081d114401c2c401103140e11011541d0042a143c00003002004140c000b01d44203501c48013507120a9114450102c000141084c450080754144025603010748803000c0c010080080191759070560000078400d00d1404181072000f003000c0703e4208003498815071103001c20007200e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 496375521 1250 496374271 496374289
    0x170403020118060e0607060906110714010902130b0f06040b0c06070f0e130e0a03030e1005040b1b041505090a0b1204080c0f160905010608041707060216060b 69
    0xd800b0440b4003604210301a801941e003e2082c03070403121a0354174281401c050f0090404510080c25a030700e00244031898451200c000e110036445441c0380c3c120381d000b07400c01c40c0c00c8130110744000c0d4108904258800c400500c503401060042d90040441c000fa0054501040d0a42c0207900f20340341c21480050345080b180f00c10070460764480303107a02d8034008401c08200c5c01081a45040e1000380100301a03680940c02040d00d400070350341c2101250840c0c51507011803c004001e0120f500c24101390f070003040c44489060007180030b203a10594022000c45116243c95100d201607501c007629801403c4014400801c4882030051700404402c21a62036546408800041100e0b503417030f50740000440c250401c4030b0101d070950f4807410b076030040e082500c15031a80a4960303402e082250b402e60700c90150203000c220100003001150641b054800c0c0c0303e000c005517078070b0f0720701601c2e09a41a00c01400c003400d1084c1005034441e01d02d0080c0b5440344103000c054100070040501050b00c0c0740203982107499039103520039600d25045c901a0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 496376771 1250 496375521 496375547
    0x102190e190b04090b0a1203030203191506200c0f030c100e0f01030203040228080d08090d03360c120b09030a0e0418021002031e090f040f06031704030201 68
    0xb1900140380905d80c60381c287d44150010180750b00800010909400c0418545170800211070038440f021204480d2407034a5201d00518001c02c0000e902e880140c0f000000404a15116400a1514291040c100120340070b00e080c1065251080d420452610344400201c658110b100e501d40c0f00009001c02c0c200020b04607590b6070b1504242c818070400c00980d880030304d440302c0903600d180502540702400144264040c42500001400e10600c55441c10a507840720360f0074403030001d42060780e10f0341846030002c9050364100c000318007042803a05410400340c0c50440c4d002d80354116400c0c00300e80d040810350f1039103e20360150b8003514150113040c40d6881030210b0441c07580c0d0700420450145181000c110001361028030303044c034000d000d15030318912504200c5043d465020400d400500000900c20b840701c00035a070340c6c0b1000030250013941a036604421030b00f4100c02d850f0030318401420a0300c0d50b1402c000303010080c030000003202602da0301c6200020108910000d241c4c1c074440304c08240ca035540e013140005442800003201e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 496378021 1250 496376771 496376779
    0x30c021237091a0906131505071406060d1209050a0603020c0607020d140f07020301111308030307170c16031e051c051f060801170102190e190b04090b 66
    0x11441c0f036164600c000c443d0300312411078966403034000a040030014881d6035080104000703620b40b0313101580c41e0000060b0500600c1804030f884003200a680a80e115802074070340c2074000030424484000104010b244150414861500942d020b03903940018084068550110300402d034001280a54034400b407010355405101c40c0000c11000b010960f008280000714030841d070101d000800d581c0d01d03804a00f42212980d40d00100240b10f00e45840100301a6a4060f00c0b260b0024094503500261103079020082d00d00c282160f807a20400312101610f00066184018040c3c11003140402c000f1440c1000c1c040c0300b5074024041d0b079034215900480d803408012510141880001c0c004140090440590b44200342001030081032000300f0703252500c15002c9503d1307040701040c0b0415110980d000c10055440f4450904135004100350070f02d000200041c40c0d00f00e210701c0507442c000c0303051044003550b00742c010080c50341d41d4003011700401403a40c801524402050003941050141c028005810000b40d41c2034042d145201c4d800711 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 496379271 1250 496378021 496378049
    0xb15040c020c03070b0f1e0309012a0f0311030a050106110120070c03080c060a050c0c1009210503090708240a0f1a10030c02123709 58
    0x100043d503200013611502c004c020001400c0c1100100c00410380c1ca4010307400200030361146a11590007226081101c0f5100c16600e40070003900c0d4901c0c402d071032071041140002902c0880501d103000711354044c0d003200c0b600705042e19403144010362929900194421820100001160750401c40014030b521101040480c1d80d030b05001c2c01c018584002404030031150f081c00c01d085e43e6031100d80b0b414070074600e4a0f4005404101c02264010b400da4010440d00e01c40c440030139040015585001c1703100c15601887c2d070042641c0d48032140c00e030341180441c1c3c011b410302402110444904980c095540160354602e10300e0400190004c800d01001010802c94032021300808805130104210b08010034220000c000028011f480c412000f007954520366038460030000b10700510501540d080089142200c210100d2068040c46903d6107800c2c0480c460300c9009400081d507400f4041100d100c164000040d04a82029041241d020b129441146800e0704800e4920040740c1d0b0703012264010b810050500c03145984401c2e8180c07046 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 496380521 1250 496379271 496379293
    0x5071a0f040b161413050607051b03070b040530070303020f0c0d0b0a090c0308071112070501050c0c1206011505030708012102031005240616020105070b15040c02 71
    0x101441c80e052001c0130b0405611130074400304110740c14072039900c07482c1c11860000d0307030038280f05001c0ba9100e070003071101030000c013000c5400040c5a41c401880c0f0a0660301c90003808140704910b407400e83e00e0952940d0107c8461200000d9461008e0002d004280d02040d500c104020010190140284120b41e18601d0140c00ba402508001c90140d00ea901e00007008419504002071445840303500c40400f032500008451810b940b00d140c640701c0d65120000c143c0e41c210441d02002c8444c904110011007010b90003001d800f01c546840c0066886400600102140b401070f8400d06442d51103240240c2d0800388880020104c03545440310007540760003805151720800c03104004004401d0303041401c1070f04446000b101103640122440d148c0005621451000790b15015444800c10b4201c401d0b0012400790010905180110040032040b201200a008200b40c0045d01403010711300d0440c50500403180140181880e03440d20020350790b05c944103501200c0c1c0d00f02ca00e81e4402da00c810390405101d00d8000840743c1c00203103009904 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 496381771 1250 496380521 496380527
    0xc0a1401020f0d030f0c08131b08060f040b0115090314010f020d020403030e0d05071a0904050708010e2d1e01060201020406030f02120f0601020f0706051902060708040305071a0f040b16 81
    0x41d0318000c0c1c2709528400d0505820703035881c00400024400403080d291b460a05201c501817405c2c0c2500c069413800f03510300001c603801007000c05043ca034500544481607100d01c0c6a4603a00340380a506040411956211090003080b0500d00040c40c02c100b12510040e6a1030079840c000c0c0c40911103080030750007441d4135080f00000500001c2d41405032181e068000717000c01d0700c1e6a264040d51003640701080c0c020b4104401c1c0844550011038079030582d000c0d4050301c00503603140750000391406038109042c00d455114410014121400c0d0743c1e500e80084500009041321400303804c55440d18070303082e1700190040c0c1d07000504000c51a41807044090f494942c04055240400e00304e13072040d0303d02000e01212031054025001c2035040e8000c0100f00300d10b405e000c040d9107070703643c0d03800000d09a50014250f0040014800d0948691103201060341c078841d0508c0d0b1600c0501e03403500d49046601c0d41044000b280c204064031402888004541503480c443c0780070340310014251615140617810340e10080c048010724004d44c0302c114821a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 496383021 1250 496381771 496381801
    0xa0801141f03021c02040e030a050a030e0c1005030403170f070e030f0f0d1115130c030204111b010b06092205090d08090c0a1401020f0d030f0c08 64
    0x307a009090701c85032000750040c0c100020036a100951101802d2040541c85070b01d41c24400b1a240219810000703d034555000940b80c0c4920403241c40000d20410600f0041402648038072001c00d908011511150031002c0450140318001030f031480401d0001c03042004040d4400f03500610f0712000b43c50410781c0d040c512450b08031141d01074004024002442c060350382e25101040107640902c0124102ca01c1d0321010320103141c0f950f503103400c00340021301180e1042180c0034000400480b101030090b803c00c80e940c1c0b42c1c1200b1800501d6080129119040910008003603603a5009020403001d2207003403d0358505410b240c5242254002c84120426414a90441ea8951783d42c8145c401b0003031300f9150030411803500b581c0207405403904041040c510b40b5000500203642d800080c406d4243c029500c1c0d002d416107410381403030303540c625000c000343d80003841d0b036014800380b0314660224114420600403140d4818514046034181413028840400182c0d030f40ca03110114480034082d0303c0c03000440e41008241401c1016031045141 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 496384271 1250 496383021 496383031
    0xa0c050a0515071d09090c09250206040b01050111071203021b0f010801030201121805030c0c01300f02031305010b040204030308010b28080a051b07020d05101a0a080114 74
    0xd203034000041b06560207004014510700c00800380c1f1603a1820b4000d1450003c1201e00c00c420041e182d55401000c180002212406141c01440360143c070b80c6090011a440800e12071045102d015182c4c000981020b03805180203414403d4019215401355102442840049071211902c541d4580c04040242c1e600981001d05480d020300c0c280440c9072800f0203810281880744200200f00f00c0742459407052107008801760048090314401c1d54100d0000070011143d210401c00c4141d050003401c0b0301500242c0c0c3d5083d040303080c0082204041031080c1ca40000c00d04a81007221340000d4110a61905020444203100791403520320704460460401d404c60710010503940c01401a04900500018001030329911403411200d00c0c00504514a5220302c8514004c00d00c05050302c003140020304060216043c4008000d0600d0fa0013a10504a42818515020440e0000305600c082c0e07503501540d014404011440e0080440c2002150180720501807903800703000329400d50307a00ca5600c40e403610103000074003102d19907000c0e044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 496385521 1250 496384271 496384279
    0x100503010b18030102091207050a050906060318010b09160806010f050a08040f0c060f0801050f130207060b0a0f06020616020a0213021909080c03120f0a0c050a0515071d 74
    0x102d5060300c0802e0085c070840007a04d6200e0803649440d41a5880000e000013a610203032031001605a54609114141c4000d80d034155114005000082051646036980702074105000f00204180f01c8110200721001802e0381c5880d80004410212081c4a42080b82e05801c031000303103803100080401d04001842ca0244481c548100700d040004501400400e0600c091496044540b9104a55590f900501500a4a101c1102041d034050000034946415844260035590142450080c0d1800781c1882d8002c0d44902e40840d007069958061940340e86950542002030003038055810182e605080c406468440c004006030308a03001c0b84c15030300e02d81e9804900c032004190705a5080c0c0be050103802c0b011001e07000d00e41c9440150302d103036400075005a0748180c05a00315600c0b030b404c0e20300708112070042c5911361031007030080c1d040d180080050803d5620640024000200034ac60482418000d0f96519401e1000c00075040ea06540140d04881642f1204401550007110034280f01850301000134600000410303450280340301d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 496386771 1250 496385521 496385557
    0x1b1d040309140a0b030a020c07080d0c080d020c0109060b040e06060a1e08030f040501090608090c19080703060c0306060908190819030f0b011805040f021b070302100503010b 76
    0x1a5260800c102004c1e140c0d405a098070b9203441040326000703410100c0800c2007031080400000e40004040340e0307280e024482d940c541c11052015160300113564003600c02c03082c4240d420840d001207058280304076910700d40700750b602158000708003041005403641e807a201c0b07007260030040c140b003400d6868203419001c580c607003008410150726512400700400e40036400500d05000016808d50620300d0030000300b044e107100340c940314011900d9460849614030100d032a81040e41c4060a00030942c41c02044419400c010740d4070040d94103483d00348070343c1864a5603004864240e1a900c0c5628540c2c1c06000e03810192046182850045240469055850941e001c09011090f00400c8041c11302c44858102c030ba150f0219040c4401c14100d604000b0f00900020740c0d0212510b103029a24107007503200f00141a403000901004494050400041000520203803c103140d0709a402c0001c02140c049004072000e64582910240c081140f65005100000c6030340b0040508101e0200300510500640740d041c4c0b0135600605841e01c1d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 496388021 1250 496386771 496386809
    0x10b15180303161406011223030c010c050d0b04020306010807030b210f011b0c021507170414092503150b210106170c071b1d040309 58
    0x1c250302c40e503d200540101e501002000744416180311600c1e0340707220400c45c1c1d01c507030769000814a400b050b10300080101c085103948803d070b0720119528540e45254041a00e240c412446040390031107401e45031081c013244008c118450b0700d80291180c8051840d0954080d0314510381140000c1032100010121004d041d6521110401500c2e00322802014015206842e940082280440c41c0d80d601c0c0c54482003075941c200030f83d1800b890158454501c0382c07201c03500c800c00c0002c0c403a1308014403808040d6010101d14070500801d40400c404540004810031b58801c41c541c1c0c2c60811240041c074281d4039521030300134003411003800440c458900160780304022150384048101d00c40d400403030150403440501104070b4818500410f20a013000002c103012800c0b940d0441c2880340c1c9103000180880300744030b200b001c19000d02c00804402e0001e9201035115500260140c50500c0a9a0700310b11808007011801ca00f40d1a860140030b05070941d402e40880c010400540308162134031b560020f00d0320701c41b03000355600b07010706140c585 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 496389271 1250 496388021 496388023
    0xc021e0a02130f0507080402040b030c030c010507080f0d0902012304140d020a141309020306040323030106090f08160314011d03120609010f14060d0c090503010b151803 74
    0x183c610046003006000700e00b06500c0042110005603010f0344114075201ca400020f280004d0305030740720711000d006403042c07054840043d1350507004605e050351582000c00074980303125000d0b4020400c404141800040c00c05a9000042c0031151260380e0f131500c9004010070484103d091019101116041000c42c0d40075200c441c041052150070303a0000390020420040401c51207200c045c2d603201c9000079240501d21404071402c1c801607622103000030750580c00c000013150110b0b11842015840540e024188081241402205c40307065000740c0c003000019401041c28042c1d082142c4e031110007400c501008101402e4190700e1a0303060641e5110080101c00d40c0707005102d510800390000390410141407440f02c0080c00100000b61650300640d00401140d07415400101d0f00c1c5040300d02c207416900358109401c415070400c0d021445005d10845242d034841818080f00761003540d1030062140340e8032a03540300c54442e0714101c01c0c1405c0d00da202d00102c0c42a070b540c4620b04864070800301a2148203a500d074403a145540300070042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 496390521 1250 496389271 496389281
    0x1513031718150c0a030e041a010507021315120501060609083012150111030313051516020706030b100c08040317040e16050301171c030c021e0a0213 65
    0x181098001e00000b070017030517000180c0d4960500c00351014442a000103244260b00310400b44d021b40496418400f043c05805c3c2413101d14060f601c0400001403407071500311011010006903008074101080c00c041c0004001c001e00560000300700c5420040746140c107028030f4075115450104450401501c4511042501c0c5031040c00082440b0791444c801e54514508a4000340c130385c812283d00104551100c01c0f05419441607a02281d52405003010354110340b40e042c2c0d082c419180c5500300380c0d481c0c82014082c0c41c14401810b5aa40100f000e4130112620302904800039003080d6041d880039040c94500b10a084e0191507004c40d110b144000c0d46441d070f810704000d190401441c001c81e0006000e2500310014059660340100061041c1c8221401c041d05030f60711098001c3c9080c51002003440000e0060004000c01c4c03007204110f001c8050010162104200b294050386801403e81c091080001c1e141e00105104540501146140c0800c54441c030840350954030180344d0b1101c030604003c2c064007051806021402c0340b41e00c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 496391771 1250 496390521 496390537
    0xc03110114011401020f0c0a050913081801020607231b0109030903050609031c05061f020c0a0f0503070b090303070c0306020a09060e0a090506151303171815 69
    0x7054610b507100c00003810010307000b860980c05440340c59880b0307169000010365405200d100501c030006160031b04080c030203461009080341920a00030010032000402902c00341004c41c90a0903014803104a03900020301c0d040001c4c11940034003040d440b044540922400440c20b502000b6041c00b83e0700c0c80c443c1e16030311054440d07a410441551800110701e04155004944c8001c036400703881250718648540006d69205c0c07003160b15044505100408000d0480340a4102907800700d001007180c80308443c00600c612685501e54036140040c0c11500c000d054074030f0428002c1c0050090189840c410a003410042035641025004503041800045200d01866408004442c0712550040080150701d030b42e40307401c00180d0800680c100c0850b54560300440c420344078540440360030328010702d03c4403454034220103030008003000340034260807444500b0501d0005240070024500380311980800c005003440d6003016034148081030400301c20700408200c0821100302c01500c40c2910f42d001c480300c41c814103010104451511030300311 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 496393021 1250 496391771 496391801
    0x112111b030705280201180302090a0608191a0901110705030a030b01050f12040302071d0f071103070605060d0f0605060103110a0f080c0906120919030c031101 70
    0x1100e102100030001d400014403400449603900540d18198104140300070b14540c6410f4a1070224002d503101d50458071404164001090541c1d0301e03600070a1103820112146403441e80c44400812140304100301d9001d99040314655012866640e43d9154007410851207a40701c101ca4400208030300d4102075100d0a02d102c8580745e42c59035013a141c5002d58994000c10703201004645401c2900e81554024001c640c0d2041d0000046850288a29451444804058004c0e0118801c00c42c0102e200006080400c441100d45100415945080c4000b8a2040001071420041240040d0f902400800020a03901025880980070889a8880c000300b500c1c40340c03085000d050414118442c400380032195000364007580007a07805010f0489140741c001c3c80361091381e0448001442c8451b011850038820007505400100ea440800e10700300300980020f40035042140385480203d00c5030203100c0e040030304202c5038910385140c0e00003810b04500f0791005028001d041c4005024000700e000807009010080d44139240a800e005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 496394271 1250 496393021 496393057
    0x406061508040b0a1e020a11030408030c0f0114010e070210090f0b100e0a0b120d020303011d010b031b090a0602070501180b03071b06020309031314011211 68
    0x10350020014501540c068652041000210707400709190b025407428078094448000701c0c0302452810070000d600c04080503040141c4c1451060034103505200410003030254a00441d02e401801c1c0607181400401d1ba4660b030a1381c903003071074010910b6100e070450381125421030060b20b1580c0c0b00e1310300707900f481303140c0b2246001c452400c2400001c01808408946105008400781d10b400d6507811916002028a401181c0c828030f250b90020390400466082018001000742203204010107009015151994a601d1080941c1010005000002218a6500c40041003c5004045514100807070f803140c03101400c070300c039219541c0d40c88070b500d0240349044030082e550260840700001c3c1d0b40c3c00700940303a85541c01000d000070b11801c0c0d0010540280100c05080d0740000302c8513461500c0c0c80c4416900040c600c07001c004e450300740c0c0c2d15110105500b4809503204461031005191b5030155a051038102d02d180f500200480c80405038445440d03680300d502c1c0350b84000e0010001407032240c2050003448034001c14010207000c036903032 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 496395521 1250 496394271 496394309
    0x415030915050408070b010506031e07020a0803090f21040308090114130e0603010911041a09041104051608040b15060d0915090b0403180f0e04050c1215040606 70
    0x204d00100f10780c3d03024680e6610703540d889904121343e5100a4a02e50544545c0008014000e1905c01606400c5003136801180c00351026641e4051543d0002c90b041c0c1c0e1250400b41110508060900025802e900200940007082c1c1540200c691070340a17a00018080314004201e43c009030340540b40300815160480042e946a030306070415100f0203d01070081030b9103028444041070b2642414003603452070b240d0150008c41108c40000901009240c0b455145001c00d4085951701340503100c0f04900c0d8000d85c01811107402c0c8001e4401071200b581c00142c01d02c0c0b25280d07545580c4142c145e10064035900b00d5449a10340d021a26071003000f9420b040540f2040b548201c00203883c00300303e015948501499441400008002c403400e00341030b011250022006020302c0340403000034001a01c55910010a402003070310802c0000d4442071001070800241e040038035900c1c0c05200f800103000040103c00907001045894101e0311400c10805515015081242000c00010b0b0b40446c00308900e039005200a02880740304560540c00e4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 496396771 1250 496395521 496395533
    0x1b0609060b120d0f02191103150f09010501050628090513061406040308040303050c031c0605090a060803040b090105040b0304051612080304020d11040516020d030204150309150504 79
    0x8811103543c0440d0300b1542e134140c95070000c98002111389420041070b014801c031b80c50704d00c22000811501645400360108076008494189800b41c007846001e01030541c2840c24810746400c607801030704081e22808040c0030740e0744058907009166100040d00c005640c00180196000e854030b800d40d4000075481407481480d0015055140d00107411690030320f80b204e8140d2580b20500c030b000c1c82940009800c1d90002c210601c04240244000c01441c10700740300710f0345880b0903500720006188840c000328103096210101004245803c400381d40e0040d01c003050800005150110302070340e03403141d40708140c5a00e0300412109803076030041e41030b14024029030031815031300c0c503081c5465900d404100064a80c5da1400d0140840d51800c1142c1050041e07a10848503488c6071215001c00100030740d210411a20200c0026104c0781c161074900405014410500360f141d03c8180340703c0b02905280d1408822420144184010000720b4a440b11442c800f0313070390f81000250703244541043c4047c003140e11410204a810482032000b0080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 496398021 1250 496396771 496396783
    0x210708030c0c0109080d05030603030d0f0f1b120b210309190e0705070f02041811010507020a03110d0c060504050a0e09060f0c04120b060a061b0609060b12 68
    0x4480381600ca40c0000c18006440703c02d143d000724441541306d00c000c25a600d0040008640000300181104c0c10118a00444016601850b5024080f01c0e186d00c3c07403805a140900034014060355039921070b01003030b102c00c2e0000d081020741c1c0ba0050000340c0300d2100404039220260030004542100060400c00b26050945a80e01e44c41183c5640c090080203d5090107000011443c406036002c090084246459001040718a500702d22030035200b1140b02040d542c0107a4a074440c0b6442416003040d10407102e4100d007017446120203101d48640c1842010051400140e543d40242000c0da648924040c6069403000c000c10300900c50303030000600b0601d6588020500642040260040b00e0084039802d0103941c5400e003001c4000303400c7e10001e4076a4000408280e00041610500da845101c103041607040c544d82e038102c0d41d221000960300340d402054420a20540342081c407000c001420241c20207c000182013240502c0504107074402500c1d47ea0750302140002c01c4480c3c0c0020210b110700500b0b6000311071000e40520f44800c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 496399271 1250 496398021 496398037
    0x3040209090307050304030b0601020309040c0201150509011401211419020403170a0e03160311040507050307050a020309190611280c0b030c04050a0b07050a0221070803 74
    0x119140d00010070781c6000008951941e0b92010145040c903155940701488140050f10700f0b415030100340401c8030543c0361485040b156050507400840c1d0a140003854100a5040390089402061284010300800d10341c40c0340c0707600301002032911018200780c40c50340100090f4043c95011540d800c08010281d10300c00d10100b90301980b1101d9000e8180350030001e0078030492096120043c120b05a0b840d2000e43c044840000c0d040900303450411158102101c00041d040c455400c1001005a9031141c0604c03d00040c02103000d0320f840d0540b01089076003003090000d020703404010144800c2020006404004138424010b0f036104d100d02411244001c0104001c244464003035001c1c17080002c052400f1940101c81c00600040440d89502580004c600e2410314040b131a1070041060303031a886080c5c0c0028110000300001d62140048810050700c441c01c1c00c040006443c3e090b8445110b400c01448a040411400300b150b00050b58120b408c101c142003070121001e0345040003a10a01d207030040a500249015011000b040b0a03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 496400521 1250 496399271 496399279
    0xe0322030803130c24080402030c120709060603021c020f0d020a0c0b090a030c0308062107090b01081501032c0a060f060602100507020c09041202010501060c080717041a030402 77
    0x3140c3c68103040c00304110a000031740c012000000c10348003103034011707500c843c0c1280c00074096502305d036000c40104189417100c0031000740e00d42c04079070300300304084481c800c840c090146407070250b1800549800e07000031003400c0d03120b104407141e00042c407003c407038a01000c070381085943c100190744840484501504518a01c20245d800d8041d41000074036840011900e50b03c2d056040e210b8882c41c0e44680c50840d441c400051800342c00142e8010f1000b0b401c4a03500c519030000b41044020b241c01410803600350103982c4800440f605000d0800c0500c248014440310380c1142c20428600000c0c4e0b00c2480190825400845004001c210040c409144a00d540450b200010a00944090001c9510940f10030300303c81440c8200720044e080020340d40760700c008580145030449114030440745503600321400284298000c0d9001c4176021416454540308980a0180c46c7c01003016062035130746861075803580c12086c416040300401050704240c84071002101c0e60300fa0b901501034480e031460824504601450541e009840980c81 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 496401771 1250 496400521 496400543
    0x702090709030218070216091a1203031909060203040609061b0507060f0f06080616020607050f070f051b0301050609041109250309060b040e032203080313 68
    0x5000741d04810403607502a0a04406240001d42c00d5440c00c0003030400400c501442c101041452090207a03c00a400d62080c0002e10a88c4a00b500b0061110046001e0040201c211510071000c00802541e52000c1d01803400c000050710031501030010000500001e00c290301c003100344018071000354417031401584280010400c04110003c2007050718100c96140000030010401c443c001031441c1c01000e01c42d2103017400420030788484041642555000c0e080b00300d042e48800c080103020459105c80c2d21142c001b41c0082d0003e4100140c0040c00d030712444000e401c0c0c0303200c0014a201001503409100d803500c0c1d003100641d01c6801c040300d2241d82d64440b0b0b40c01301c1d21135824200440c0d0780c0e1602500c06801a0741c460110320b00051984280400c07590010244089228000c3c400c03041d085035072846032320408155500040c150303510314003101100d10b151005ca000314a400e810519114000045404080094091001261803c8482d02240b1420340008100340004824800d08a10410303000d28000d00c103801c0018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 496402877 1106 496401771 496401781
    0x50d020a030b152503120c030c2a0f0203030d020705060a141303050d0b0301060f051212070609030e0409050a05160506031b070c0b070209 61
    0xc04261070b001240715615107034000d589a61951100c1c9400d15480510514101c0328541a0391441060f685100c0700b818000c0d446a0030501210109008003892504020040e10070790b103030800428981140d00f440840c01c242d44800c20041c24043d1000700413903896507a0b99103406001aa01030104021301e0030302d4039490006081f0640940b00a000c075080920b1040129035904422a04140d40e10090228092200c03155400b4240c0525203030ba20794082100701c0008000103048213501d50300e814400035402c40120701c080116181214031184102d000d80805880702d450303c1103550040403c00042d400076103194000346880e8064502154003007166004a800c60300203c1d400e84203a0312031004c03201041000c0118507a0701c4c4040700f5001b50146000e0224010740400b9100c02d4a0307040c01c001e00b05190340020142e54038541c01c015469940745c0c2c0d40c40703c2c1c00b0641c00b250099004940000020b0 = true := by decide +kernel

theorem cover : BRFrame.Cov 496223021 496402877 := by
  have h0 := BRFrame.cov_init 496223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 496223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 496223021 ≤ n) (h2 : n < 496402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
