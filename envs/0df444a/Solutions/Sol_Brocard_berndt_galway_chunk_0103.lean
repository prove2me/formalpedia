-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0103
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:51:44.371981+00:00
-- url     : https://prove2.me/submissions/57733fee-e33d-4529-ac3f-a560156214a5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 18345330 ≤ n < 18525186 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 18346580 1250 18345330 18345343
    0x9030703090801060b071b09230f060109030209090106030501020307030e0c010e090114010e0303070c0608100b0702090a18110a0803031902090d06020724020c0c010513091d07080d02 80
    0x4001c004108907040810441b0683c007c160822031030142000444196001450030b00715551400c40e420001c0340e1303642c0a541c0101d0708103d60703403400904040c1c010009130400c2c03510b45404c840054001b2458940b00d40f20b40c0e003640d00980d05d400009030740d400e0745a4142010b005c03c40c0d41800900c0e00500c038811240014048003010700510421111007140317000581c0c0111800c0d03180d00b01c00760559460301464240451488030a01c03601c4003142c841000104115400c01c0050151018445494102400d540070b101c90300e08000c11a00300319aa401030003582e0104000c00041061181c2910901c04500382c0600190303403025400b000c090342c401d0003842001c3ca540d41c40941203170784100380181c0b00c4030700100080051035080d0010f00b031588000f0342d880c2803000200c541001003a0214403507a08102c80b4000340102c0c0701c2c0c1e109098168111103100c060a41c86600100812030640d0000200d41d91a4807c0340101c4803156040041e130605042441015003062000d03000501001019040f4400d2009002c0e45690 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 18347830 1250 18346580 18346583
    0x120402010302030603010e0730030210090c050405090d0207051c02040b01022b0813030806090c09150304110103090f0305031e01060c0311010605030c060f090909030703090801060b07 80
    0x58003c00080c2e066142580405440141001200c814035911582103420926815010300a6a4803012051800780d422000454155046e13000f094450200d1900301d0081140d4407088503580000100015543d80303600032035019000030006001c0021104802038035000159005a004491703031214010b00c509046410403181d034054501103420b0400a0040f81004010b180c00d08030310719290300c2d40021540700300442400100e11b0326258099180d0f9000141100c6007400002e00046960001032510b060400300b191700072000314052818684100001803540031000d0b20f060b40c0540c04801c10040c060000341441c0800001e08081200102d15211010f440004001c00b03824044000042561002d9040d00217160303010803c40c010203035849040041500300c0c00c01c8242d0000d00414041186100d040c89001c048401c010010140044606c0600019402803032100c04000400e2060f42039913190142424407404010001c4e41c0d441000b4035000d007017034445d50001859680741580501c920f850110450b05850b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 18349080 1250 18347830 18347837
    0xf0f1709070306050f070e1503070302090109050616030305010f030b0c0c0f010609140a050906011401050705100c170103020f09090c030f030c0d0215071b12080a06050612040201 78
    0x19038a0444091512a142c0d20007441e191428080201d01d41e405145c59004060651f82d41c14211440c00c00c01000240f08544401070750300400c08920040d0103903005010414040c10180c00ba1651a07001914a8120806000020403591030704000c15074144030b840c1c058611344034a543d40b5030464039080d020110091048140d058000b070303803036041c0d0b100b04181c00d0036003100750003405807949909a0b04050300c030400111000519680204101150754041e00d481244001d004000c542e02e490300211f410b5600e9041d603810f12a0030003180707020030710920201501042070500810f8a0780c0c1e00000074642424102d07500969042c103c010f00c0103a81d105200c00c903080003101da050582e154980d00f2400c0c0003c202c4d10a81c0f500c2001040b003115080407000c3e10a0448801c20350b60703c914030f0602a602c40d03151201c45600c002e042400201d40c4c82c09481408514044c0640740c0c1024401595490100741340b4985010109000c030b030401c080030901c0d000300743c0a004103407051401c0403214249090607030070141c4003c0c1407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 18350330 1250 18349080 18349127
    0xf0708070e190501080706030f0c0c0308060109030f1407060906020c060d020c03070c240801030206130b030c0405040c030b22150b1207030b0102030301150e0a06030c0f0f 75
    0x120070305007003407240c481d100b100420555968448180e5034101621400f4046800d103c0e03804c2c10009588181e660712122a00c49003ca12401e60302180c412100600f11414000442004000b00d440b404d0440f41441c443c8540401440080c0d40e07251800b01258095010803600381420f108483c1c0c08510041d46420a54601e500c51a650b1100340c06030003200c4078032445100200700780040c4500d80c003518084468084203041480c201580b00600803644828410128401000400041c28414020003905c080303c020038521076122802034840d94004d80362050380d028007240900192078039108c5c01145e4016030400308801e680c4c1d080810800d00392000ca030b0140d2595889540d8400205401928003c4000d81d81e5039210b903290705040c00541c100804410740412400000781c0c40740d00901c941c01d41801d058000314256883e00c501e1f18020f124401c241010040b8000a000041d211231003040d0107080b960f01e003c180d255600000400b50304141c88844200030004c0b00d00450640c0007901c1d14407608051581148 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 18351580 1250 18350330 18350341
    0x3030403060213180b04050c03090a0b060d0807030c0b0106180504020a030e0607050a090503062502010f06060e01111c03022203060203010305100204060503071b0506010801020c0f0708070e 83
    0x1144030030340c003002c1003201d9030240715560484c0754441410490b0032501002036072620868024030740006ca44081450b0312a00618011078100c3c0c1042d640003200510326402c0b005144c2e50b00c1c810b600101011000300704059000010001206071140c0503020b2403a109028081c0200303000ca02684901c1800d0040b580060f0440e61a84643c00c00c014040c000d0088401c14240304c4401400c5078040080300c00020622174000c507440c40d000c504a03015240050b00c00c0a1540740e10441c1034050b02192104081d90741e200905212864540280c600411040d10f41c80042d41c0381c580054142c003078a013030503491500280402420070074a0800f240030340d40d45250050f21554a041c290030460035020f1b00703170094068104d0010030011203800640c10381e0710039000c1d6410100554800000e0f40600c3c001c1704007080081c0005a800f41c460501002d022a4802024106070350382e8440c0c0c2d00f415000e0b000300a46035000629642c410608120f40c411003404040244801860030504070f80343c0050340240c004c0815070001082 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 18352830 1250 18351580 18351607
    0x5030601020a121106090606030106050a05060a030c110a0b01050103050705090d030e060c03030a05011508040b0601030207020a0537030203030405090a060e070201090b0f01050616080c03070302010b030615030304030602 96
    0x1850713004103104444190912092459880c28200c8846c0e119600780b040c04503e6040600010040b81c2001d00181e0820000041c254080c1c120095180200494a00540b5141404103c10780560303014005842c00c1d54100000141a11001000f0105001003040744241d40c0e1901e02d2000b00554045c5807039030320802c8040c00902c192240c200e1403902c5100200c180701d014805544498103c40c10126003290344140701c3c00076141c000013101c02030400c040c5040001d0300c80d4040e4004000ca08d2006101500c06901c0ba00040c400c8019080e0200b01d5164880a5a0700b00c03048405004501c0032145c022150b03603146038002680c900c0755002d540d0042410f10301060098050b500b204024010000b011b804500c4c0402c4001e009045103001a40c00150900102e0740800e0851403a6041c0d0700080c00e12440d1561801c2d83c0b0101c14002603007218610700408c004856840e0a10140580e544240d0011926025110825160000107130090159520801e252802c50341c00004407003c6a07485240036071289064000c03038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 18354080 1250 18352830 18352847
    0x80703030e0309030a0507140907050a1d0402030109150f0522180503130e0609040303090302070b03131a0601020c120c0312030f1005100e030a02060f030403020d05030601020a12 78
    0x1390140b084107201c1c0c0c00c0100125030403050b071340804070f1500e4007090f040c10000c91010588400d0007181040103000d80c2c45103d0b100040800306d003100c002000c0360984001c03a089a10981c05881651f07078030214107450b50b0781e03101164001c00340d94400c0c50180d8100030000d25000c041c00c403198103a580d8203c0380c60b209809034000d412a61214030340306011030142e0604903104d6114440071409800c41c6e21000c0744502c48840507030b02681001c0e00300d25490340c8940e82034000b08103000b010390a510440800145400c0728070001c5126581702c2c2150030099140b40380c03070106480d49805081209a40204204082e60300051640b4130301c5088400341d4010951840755810001c20b45001da405009504a2080a080c03047c0110301526140040c0c0e8416650107800d00c5440510303000360b5500c40c00d80d0410507882c51043e020140c10302c0c4028152011080319500240706c581c8000902401040d002c4204824190148950341c001c09080c00e0243c0380d032400030700003905d584075000c004116030708140c2c54014151260302e11 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 18355330 1250 18354080 18354097
    0x20306060d1b060e120102040f0e090114100602010b0405060d0303020912010f0b010e01020c01120f02130f0501030e070e04151b080402031603020a090e1615030b01030603080703030e03 81
    0x4003020b64507440d0084c01044101003941c0542c0040c05410b610400c14401c440845800c42c0398600b4060822214107043c420242c40505c0035034035246000d520500e039900e4980074081003101c0440b0580380050103030948647c200c00900c6907191804200e465107071200300049099142c940140d4070040e420016042030002c00581e81d5035840c0828651291800e40d04c06070104030241c03145070400705100c004a0340d411560f044030707001483d442c0c2e000304469a141c000800801c0300d03010160400c3c004a0104445140f40c0d400b0004207980d88501300060350300751162912000c4218040c1800904000c170f4a19090400b81c4020700c200c45d041000d800d40c41c59a030025204503c072481a4850001e2010000d1035a042581c059109009140000c000111070420300c0c42101d070702500d003d0685c1d00d4a10004014007401ca070140c114020100182404e443ea8a00c1d00003820030581c0400c07100309082c0000b011203d52018103418035191400500c04103242c5001d81302c41960601c1c011400041c030040311404c50146401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 18356580 1250 18355330 18355373
    0x303110406020a02010338010e15030a0c0822032303060a240507050f070305060f010501030207020a1205070b0c0d141204020904050307081306030c0309020306060d 72
    0x1404a2001d030b003c01c4021016000b41c1e82400000d040180064140200c0010815941d0303561000200d6000c5e8201420900c4005040c030041410302100402d29003c13100004500310180041000940092442640d8910f09a803400d20000c0c80d08849030b49410b0501d0f8001420027444c000c0110070940301d816100004800d00c206298800b6410703042803030b9074106841c4944100c000480109400c2090946034030703c3c1103801e0031450005d55060302039529034050310040e034081c000d05003456910342d0708000581c011031140e00140500e00c1c00c1c1c0304044a512040e0081410140100000c0c1e016a036109008010b440300820081c0420010b80780c0300340ba0401781c4c0d01c4401e002902080c501c18034007000ca49074040d9611501e40c118040b030712141210882c841c2d0020240e034152804046009800c00e54141540903207d101120f1a282840d01c0d007000755000100990144034403440c0c2070007080e40c14041e480c0c01d00e015050500071026542c1c0041c3d01c0c0c07a4020031050007421480000014070005030010300f00c0b8401d00a = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 18357830 1250 18356580 18356587
    0x14010e0402150f0a2607020303010b18030d020325030903060f15080f0c06160605072102030105010912020102070e0903070c09020c01050106050403050613080c010f060509180c0d030311 81
    0x108050120f0b040003c030201e0240c41380300507170381c55801160050702c100c140d40d010f14916820030181000c25000018004030821041d040045603840400c40d182155903171f5002144c490002d00000d04114075005000a41d0700048211140000d80042040d0181da50010300030514035018055140244401050b22680c444c04003000105824007090070303da40700b01641603411710306020040c40700ca841042c085020070107450300e0007804120b071980001d401850600d050325032107241c0d03107041400903841c1100c0440c440d80000100202e40e08a05848010300d081d0103402c40070109500007035100c0851303100c6c00446512450000b0310039807003801124015640f00d910f001001e501c0b94800d1000303401c41041b0060a6207000c0010035028010300035217049070390082c0100600d40e101c0800031001d641082003152903c1c0140003401c8240c03800e01030134084a0b540d40b00060072602c0d02040011503e40070742002c482440605a081c003e4130080b5050b10140300990b0488151500c61504030010a000021000300b0107011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 18359080 1250 18357830 18357847
    0x80705061003030207081902060f09030303070e040b011b03082706040c0509040804030f0203031c0e1209130515030102031006140a09050405150a170114010e0402150f 73
    0x1c060700c1c02524040d41c01c8402d1583c4807409240e0b03c45000a2520601d034414995000500d0020700130311000041c103152a050036891400b00307203540c109440d4000800c4900d052a0064207080c42108119a001d18210741a503010518550103120b1034600501041100c00018222071848000c811540c00c1e141e080420300030f45220880d84490003542c089610308001c8400040504e0300b03640d0b290055400100680c80c00d0b14640d261800084940001ca8160205105902c01d85a010200c0032404071021008182100c201c1c1c8110300342002003104141c41e203018400f4041544800002202c2c928214400050584480d408850340c1c2040040f40d80d410340c00003040045070300300419900f04641194031344054400c48030b201441540541c02c480000038400c250704000500e0282c01c81a04024050035544244020764049901e03408990424008c0310804a43c10030b1900e824420052010400b403140ca1055040018403e41c1c0d40010740081e100300882040f01071500c801c0c02c21605958402d1a000f40c2d5268071 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 18360330 1250 18359080 18359101
    0x30301090b09181c021603060c0e030109030509060d0209040513050706170a0507030b0a0602070f090b0306040809060d02160c060f0801060f140c2805071208070506 72
    0x701d40010301800901e00410001ea2004000304050b03031a4501401c5009600b9006a600d030003400600c07800c40c490b00d00340117482001c505004019500800c0c0c0403545070340700140a000c9440e000ca805010b6890020004003181c2d01c10240c81d130103001110703002c0e034612084c52404003034012507d607158040e01d4402070004c141280c154001c42c0338411425500c00a03a211015200c1412116031228100c86010001d551690550300807540002c060800144121407980483c50001290300b049015900002d41480340038152180d400c001c1c031035500c0511a40320210042034031018041d00041022001003000c110b41d50320720080e81c50416480c101151550403288580450741c0b070100060310840f06660012070440e1144a54920301c0307035070341c071748002c02c0c1d2030140102d485028001540040002210780440a440140000e019502c5101c000f130000913070003980a540480640a1600d05018500340319001580110301c80301241c40780c190b500a40c25280c207041d0034034400d401c1d00506074016842084900d510 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 18361580 1250 18360330 18360341
    0x3030d06080127030513030524060307030c09090201020703020d0b0f0705031e1b0d140105030115030803070c080307020f061f0311060408030406020f100c050a03021303020303030109 80
    0x5410300203028425030103c0c00050f50380000b06540b80060807018a01c0400e010705d004180c0d40b88407184041440e981ca4035140c0c144540b99000c241c40b200e150903130312030501180300b01d01d0b000780044016004c0107103181e441c0e003081940d138842c1d0441c0507224110320f41568000c8c40308000a42d0003800c42c8823611080e00d0250201d08046540020742c0382c40002040c1100e200d0403d8a00c142c0f41c0c0c080098100d450012141c00c80d40d801458aa2440030580003e0254800d080180200d1420004041a49081003401502a6005030043e0b4020f078541005403818074144080501200c0d00090065603d8035090070407555152034103c0608481c1002080c030400301c0d400550920203280d514141d48294860401c5501c0301441e401c07022031040d01510082c07000c46d00b42c56010001000050406141943d035180d0359013182c2143d440440503801401c04a030f04510203000390300c0183c00d4090100407448034888064400e020701a0f41d5410568081505100c50601d201c025025540040c00c898030b0f90303035640c8030704003504 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 18362830 1250 18361580 18361589
    0x6020f0105070c0308060409020a172107080715090203070b0408010f050105130b0102010207050607110d0c0512070807020d1203060503031e070c0e01030b0604060602030c0d050a03090203030d06 85
    0x40ca0503002031082c0e841074030310000d240d5150f074440c0419101c0e801003001034817800c1070136a8440c001d81400a282130360755005420429104028000510005071500700a0140482d21a51640100065800103207060101c03403805034030042a0400a8081d20340c003008007005400250948244403000c10b00d140b149003e4800c03140c13400b00078030158510030200c0064072003c0c4500e80d08840e07400d01c04490700c216900318400030039040c80018203241d40717909c0b0035291007007c0d52810082000e107180c80c030859909000b141400a00e074113040030078010070b540f291341e07600b2500c0002c180f242c0003040010401c0354030380840d02520f8009155140c600d016003000700400c1b42007ca5000402c1c6020400501400d020058505028481045100c1c8a030a10784504407603019510440e044d9088450109140e1800e00c000e81c069806018141000d2400c03c0030300c01241e099400c8101903600501200100728000505118018606d260090300c4102d9190190090320b0a42402945030102050400d20032199511400468 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 18364080 1250 18362830 18362833
    0x4090c0302090102070905071803060b0307060212090108061302030405160501170408090402040519052106130303150602060406060b09010c0f0503090a031101080109050c1608090a06020f 82
    0x548004105400301d1003024080760150700600707400c00003009564012907008400d81802c18021501e100b050a202043d0780044511982d141d110342d2031400c01300415400740c5818001030414400d1481c0302c0d8140d0141d0b045080c100f007603240000c4c02588030304200306d40003600b13054150b48905017442c160703440c2e00b0741d40301c648441401030900140a600c150805442c2c00da501c000704165840f26115070b442c0e0f600039056a600300c2d40030000004c00e6214201301035224100d000c0000300482c2400104040050011040c0c01d43300d10748082035100c8100400c585030801015200c60140d0009440c055001d0701600001407540c0e8500b00e03000568940200b00140703d244590000c11895854101c0c000d014002e0017203150026024002590001d504414042409402502200c4c24482036800080300d07140c080d0812211040311421503540c55170811903460140c10074a0040c4407038a04040f89040c14055540020000f150308a191018000804120f412540016081020180d112000a961240d060459000c3d5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 18365330 1250 18364080 18364091
    0x20d0f020a0206060f09010f0e0a11070302030a0206010509040c060806030f1009020109050303031e07090801061d090607080a09020a0906060e030d030c0f050f16210306031101082a0409 81
    0x44d00c1d040809034141c8100180341c02d041401c1000507216504001d0032604041c1e981d031006500004d103a03000d020338510a038010750b40c03103c040b20000d040400603402240500703290300603c0300181d46c680c0035030162611482e04400c51b0784e4800011745071506010052615004070b490b4100c41c9940d94101c40b140d90b00070b8a4080c403255903a01456624071086a04042285103110460503550a0100c660742018007480d00035004c80d1a03420060868149900a10800b0103103042c14242a00c030f003413a16401031501c4054411441e00c002c0180001c280106048596551280400115550000944054405444200206600c0382c202400c104007800c40c0c4c80c0f00744610072000c04900e2090054800c4208150f54002c0380d480c440300c0555483d048403258001128040c05400141d4001c01981e41d40e25001e0340480760b40e6501c021803860700d010b0042e401d8040600b401e0050010501035100c0300700c84042841d105031b65903501c07070410495504014905d03d4042d11707002c01c00c2c00c0b81900c60284c400e43c2c800c480c2c00c001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 18366580 1250 18365330 18365359
    0x30b010503040f020f01090b0406030203011401030c12050c07050a320c090a0618090c08030903030313020a080a20100804060c09050d0f05070509040213020d0f020a020606 75
    0x40900088078014520702c0c2242c0f02000500305030750104100391040c105030707003a80e03210800b08c64183c0060700800f0011ba4040010000b807100a40146e0b01110f003030030108000040c1100c0184180c10124044140544480c00704045283c408100d0311030b260003000b83c40e010034540c40e012a080904200109240b02d10003224110480f0301814480c0e9a10090020300d011a615424002c500b80001c0c4814a0750380d640340f00003000c005002c41e080d82c1c04040d4034000f0340c200d501d207088600d804840d00043c0c60b0341c0c030a000000d4991400030407240c2100e144070a00072048500e100140c00000b99802c044140d004201400b010854001c0d29005e250b005d8040c031036a41e0f0365030000d100320f050600890b00c00003134071b40d000f00b00071400d1980141d484915500d014610b064031800030401c0d0040d00c6e0811a000300c4514421003c3c08418003400e000780101b110384000c00d0500780c000601180e80341041617080d550000d0101503582003a4448001c815540c9025034403180d9191001e5107403842102c80ca805501d82011221 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 18367830 1250 18366580 18366587
    0x41508060a06080c03070c03020c04050702240c1209030403020604081006080309010503070c150606051c05010503060412110a030908010b040b1c05070f0b04030c080d050702010305060609150406030b01 88
    0x62040340020402405c6039601c03001104c00f448450001d505501034001030320121b0300c0e076015003032050205400030f096840d503001c60b82c01c43d4582051040310081c080390034003441590803805c41e69003140c21720a50085403225582c450441c4a01d45c0029130081c0b00240010750041c1c003003200350003408603000801520355038180700e40d02c07441130414181c00554200000b80066003d03031021090180941034003c1c0760510b4440002c02c07140c1e19040000400c4001c54014404140c44a00c06111030b9151010b01c031551500c40444d94503040a030004101e4808400c074000c0b000e20441d0700b03070f456001c0c0c001150200782c2e290902070000c4e4018000c1c40c9195003440c0001c0c0702c0b401c050007101c481c1400601001444010001c105a526501c81d004880c0f9004840c00081c5180108484030060300404000c1e03561a855850000110714291b031010b034403508440b00d01d041454204059a00c0c860702801c3c04903240e5a003100203003041c4101d104159010b90760240a007007410750030000c1c0042d00d4542d20208440440a801913 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 18369080 1250 18367830 18367847
    0xd171318060302030703080703121104050312040305060705031b0409021308030304020108010b180303070605060405090a03050405010804030e040509010f0f0605091801140a14010f03021f0203041508060a06 90
    0xc4d41550140f00708100141c0f80000030100d050007440c204441c21010700c440f2090724005ca141c6805460082001d00807031805102c03c00f00400309200141c50503217166186032b114903004043c10148500400014101c850f00418400d085c802c0d04151a80c842d240c003103000c020f4000c50724942542c100b80310082103200001048a000715016110810941e20f4078001a8050f4046080008600d1440300c610b0210748081000d810685d118101c00303c0e02e8034006c020b00c41107800040c252202d550094600d038000c240c020040b1010340b4020f10700300429a41e031b820144c400d000d54a40d4590824904020401720040662051100c2c0c00740100921800100e16600016100ca0340607240d48107607014042250644911150030100308884008a0400003074402d42c4003c4000701d4036402407a0b03e5903803001c0000017510005024005181e41c0c00489821034001c0384920160100080c3c000a03150181034405000b0400d940003440c1c0740d2100c44111030390110062814000b91415402225128404075045014103401c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 18370330 1250 18369080 18369083
    0x1503020711040e030c03040e1b0708040b0a05040510020609010e070605042702070f0c05030303130201051605030c010e010506101e03060b040f05010206060d02010207050d1713180603 80
    0x1c01411504400b040010a1a10481e080364881000714110030001440900018401701002030440d14044074107055010243d8602e2068100801c1807a001814041c20f0b642940ca944100035120319080c1016916481640c011030f0b4403413048011545e00a6000809a10480c8840000d005400c4d070104119a1102d0b00d009240200301c007400180040643c803480c9004c8a2100c643d5a10601a203140c40012130b481498181d80c620000310000d418000401d1035240241342c141c0085185240040e6880d0141d040407000034104031000440c04503408011000e40c042c60380200560341c0d00e00e0b00444941c000c050a00c0b0160b10b55083c4400500c0c280741c1300043c0c61085100362500d0341a5141c0c02c04810841c245440c00c0001d2581e540000b2484009d51070162003e4880911210340240c144000640b074040c0c000d103031501c0350081c4024640140da01007295001c543c825078240c80c0455280c640440320f14106512021280d00210366231400040c0021424101c0d0440c1c0f240c2550949406002015140c56000 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 18371580 1250 18370330 18370343
    0x7030f0903020312090604030804080a030906110c01080603030c060108010218011419090b0304060605010311180909010e0102030c070c060c1a0a0603120206010614071e05030c0a0c15030207 83
    0x780d000b6641c0c0d1382e000a009204004040d030385056101c1d941c600c0103401c039400c0200c1c1584100701c81c00800d030b001000c0d07030050312050818042c480715141c08250707629100ca0070310b810803d40c071000c15107649040082e184802d80c2078058a42640e16125854001d401c4142285441007028829000550042c3e0303a82c102403508811141c0307049644800850720340c60302455a02080040c840001e4900c0c160f802450103648500702c08525645802d00060646828000d008901d21040101d801540c2d04110660726800c1c0c25150200b0700d41d10340c101e0034014089190000925400001044881244600181081c61103a20300c801240d4903484112000c10021a00400300114040c0c50321000810450040e4080761042001c00c02c1303600c0e9680c40c569183c0e070b0b4103070a02503401303032005000c0c03180c000c031019040c0004c0c041c80c1818416540c4805420402003400c0d400c8505126901c641880b8040c004c0b2225801e04c3c00440750302d810700c3e2410305015040c5201d06040d8003258a584142c680c1f0074001c5419294025a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 18372830 1250 18371580 18371593
    0x30720060a0503150f150301060201050c032703041203030203180604030210090611040306020d060e100603111b030705010b1905010e01020f12120a020a0f0c0602070c0b07030f09030203 81
    0x40c5800d081d10403a90132180c2c010081c0120400302d50ba80d00e62042850094000562039514103000070707080d120f010b026188518810700c200b000707140e00c0310410b0300b200b13460030507030711401c2003c0901c01d04602c070303d421a1882c01000300014091507015001507020311118100342d41f0420300071010544442d4242c1d8000c0c0160801c03140c00d10744a005400100c1d480340145000070701600f10784003054084c0e01c01c0d4800c658494010840340b90a128501c1010010650040c10360030901d041d01140e01e810000340a541e0030306a51b1142d4103020700700b44003941e003500003000d084105105259216552070300a064200e4107582046004081410000c01e482c100c84002c10340c454105007048015100038010444c841c0c1184140240215250300410111030341c450302a41c42c0740c1e11840c06001d9030b14840000d005c00b40190040250802041d8003542c5100300321076a1500040c03050300c3c0c0c6400c0020748584032019103131042d0090003180e8240e03101e005043c280c0c0309031243c65010401440689407401d003440040e6140e0841e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 18374080 1250 18372830 18372841
    0x70201020613050102120f04050c0901050303031f0b0310030c060207060c06020d090605160f09120b0c0d020c10050106030b03070b03060f0607140f070e0a020a030608030720060a0503 80
    0x315a82c0702203d200c0c00c00541031840740c000032071826604480b4100007100700c41c180804d1100500c80c620f00140292101100c0d5814540480c4d070368840a0011900c140c1c1e070590704400000400202d03005044d00090141c2d581c104000840788108043c0800d50709480407190004085000149003000c40701035441d00c241c603000b10345400c0c0094010410b0000704d0342d1106001c03400560688102c5101d1414019240307503003410003100070200070b59030340c801d018003506c1a41480528a181c1c2e4000c0e082e03512014402196807081c01d01c0b10030740143c0742c0b070700841390001c81e80843c24040855983c540901c840410000d5070b981d04001c5094801c444015a01900010703000d00500342407000441d408140030340820050b9411001050140d072004809441080c080224a00140c00c00e0240000480c8131000400d1150308203c0c03075101c4d41c14040c12018055500141c1c0a203001d01030740000b8002d040d1b4030103032516140d01d828442d180d079500c0c08900c100d4610a0030030442038038090f420b07200315500301d585183c15648e030f9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 18375330 1250 18374080 18374101
    0x203030721020906070614011202090a0c020106030c03210309020607030305100b0c0105190c120507090504060b0a0206010603020f1204060e0105070c051b011d0d0c06020714060702010206 82
    0x2084548907840b502081140956199100103054041c4648000541c01301030480080386404180c000e02004d0540c40380355400b6a64203180d07903801c50f8030f041c0b00040b00390321514140e00400066100804c0c07103860840000a000c001ca41000420307031180d490118002c003950084007180d0007507000940c000c1c0c06112200c0400e00c69404950302500030a0144005519810b8440180e001403541600c5691134008008a00300f215941d108002640d0000f0b0102044085020303022803020400d0741d0a1580e100d000941451165003501300a041c054000c11001c4c0e2a4028040e141e40325070a240302601c1088000581688a4822281c04001c050328050030b00d521442d4040c2080c6000c0c0c015181141c5400e461000e8940a1043c45d018510365119401c450503d0710708036050108000328030348414940c1c5000820b86c0d80005400104070324032200e00c120380c280c40001a91814101c2c8014111018084010034010380004010065855040f85032019011400800c44c5600c9002002070050f0886000b28004008 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 18376580 1250 18375330 18375377
    0x10b090703022b06050411030c030f0403030b06030403090501080f0c0a03020d0605031b09010b1201060509030109060603050105071814040902030f0d17010b03040b060114090306090a1202030307 85
    0x50f161089031105010500806220b00c54808502ea49a504111514040c40307041c07a04e040b0003410030b00390311305146119614040100a04c0f503203010301000804140c4207901840404800400c0369859017010b080044c40060345001d2103000c00c002c0c0340803078115521920304502c28040342d0700d06483d202030010200c0107500b26006c07614195444000101d80da81d07040c0710401125201c40b06034003281030428104402408103038810042d2030420045c0026003200340f07a0003030650b905818016070713401101d03000c01d00411105001410301480c100020041080c10b4020314050205641c582120301d003035428074040e000082c403440340000c2035140b6600c01c0b420690020140d090000701610380d0b5020304d41d80d0604040703402050780005182c00e00e0a40c40000030041060140a5548100c3c0c19464141d82e1210f1480002d450707681030040300100c00403000c010804595182d400074081c3c403d60300700540c103079684004601d004c8600c0040e0340c0034030514900c000241c0307104017049da0700c0103000740420030259070681 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 18377830 1250 18376580 18376597
    0xb1005011b060f11030a0e010b1002070506070c120506010303091508061203040b03010803040f1703030a0f06080d050301150309030c0f0303110a050705070504050c07200a1203080603010b09070302 86
    0x60703c6801c040350007001301000d94804c1140140120b094000e22140500311101e100a00344968500701c03c100e0040c1e4001a414103a41b0103940c04c0386d6500b0b060070b041003181203079400090b0030703140728030103404000e000b10300241203e01c03a480c2c801b1440d866007503100607041d41600d07420001d20f011001030b281c0d181103003660b44a586100142e9181c03d456142c201c0e12548242c101101c5035000040c01c000b0280148905401044000412403400c0341010f010358484c0700103401c2c441c0701606c52032600b00611a0380d1009008100001c11292421070700c0c20050724075002449120600d5500882e1030010b075000e800b40c2d0f00140d038155911b680c64419542c601da02104902801e170205661418003210601c0394070010100401d1584415840d0306035031503c01c4c40c203030258018902450605041c0126a0711170403d1b50107550780481c864502d044200703041e00500c00180038003a4420240080090b03d120080d0582c2e2006019558214441c1d13107500506082e1044100700d150040e4a1800040c003462203540a400480c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 18379080 1250 18377830 18377861
    0xb030c2215050703020c0105040b0403141606020109020301050604061203051e030403030e060709030506070507061e0605150a0210020c010b03010905060627060105090109080a0b1005011b06 83
    0x110384881080341c4080001c40c448002c1100007450b5400d260f01000280e0384a4001d18025140504107251a012030045200040160800c0203c0c102c600d002404640701440003401d00600c0384d07603202c100038080c18907240160f010f54606800701d20103081038018030003580c4503a03e9407044142c040d9000c56159002d69103003103400d00103031128840080303a140258080e60095501081c1c00d20401c05a0b81481c03000790a070740603c8200f681c00c00000b440070480307640c030806508ac80b0342c6035403071424032a02415064017504c1d0404443c0c440d40d0041c41590b480b42065a600b601c6001c1c0440001b88000e0ba1881031124000260380807244800c495041900100105403500001244522403a004242035640d00602100c082d044082080400d0600071001c0301081012008a840f00701d40200640c002a4050441410080c00151740703002c6034001e010000060130b16008880014180d07007400a04890243c4441064515100e0000f409600c05c00c81a02c82c800100c002e000032901c151b946400420a18503c0c0215 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 18380330 1250 18379080 18379147
    0x9030c190f080106050901080f0717030405061201080d0c0803010b070807060516020c0406030f0b04170309010e1608060708041b080a06050609010e010e0705091005090405010b030c 79
    0x41c601c9100c2801c0040c80207000124000e41001e04110314103005804c24103541d80314441d21083e4130000907404c42142d011507000c5240b4501001d6417811849a6003010350840c10020b5550f42074924a11054100c58507101514503a6080010417141c0e9032850300c025010110034001400303e40d981b5030080040d580b00300c4400340750149568420781560000c64004661082011800c0091703901070010720001c4a0807941000540e007155500d072020258000040d00d0810240001010454a9800c84007640d0400b11415180c1c60403051123400307071501003000b84071401030640d19116081c2d900f904000f0b41781c084002c0d101e0381c3d442e240221801d840003003060711104110800c036260301d404504214058141200602601009800d007281540c030003800303060051000d03000402c41120f11072012070544001e450f0340b501c651035480d001c0b181400b6481105612521100540300e003590408002d00c4416810b039010712035a81d8501c901c8600303001c00c407804d0078820b07020005150083e01e4a071640c1503404054525010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 18381580 1250 18380330 18380339
    0xf110a02040e030d0f0b03031e0c030301030507060f08010609050607030c0c1518050904030503040c0504050c030609100b040b0f04030c0b03011a03060607060902030c150d0b0609030c19 81
    0x50320303080503032210b1581001601c81d8011301140200101200c80d84428010003a810b40880d80e280304144221410f0885000240c110380c0140c012101890300f020110703501c035612401c1041e181c212074030a11001c0340c22800c8020320035004d103a101d8100c840a032604096603140106005466225810840401003401141d100262a4025820290240e030400b403030001001b60000c0c000400012140d028003504034400c00481d83c0f524a240c0c2c2c050740c5841c0154580c1c44500d40464441e00a8100603402820a0708000160b10905c0c05180319160840d0034038103070384400040c13505c030048a015500025604110501c51101e0318070080070002035002c2140c0c0380582d29140d0011514071034010720040180080100003007805c0700807200e1100300781e1100c94078500303101c1c0014a0390302ca5030030b00030312090301c0300c07001010740d601809284c09400001d4214007040d42404818400b95000707012121800b4585030b582066414414142c600d1680050011300f80d001c100030400c14120844400f0345080c100036500840c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 18382830 1250 18381580 18381589
    0xa090b030c030106060201060f0503010920010504090603061b05210c1308070510090b070b13050109060506010807030c0903060e070807080307051203040201081303031107050309030114070f110a02 86
    0x10005d042d40ea00000c1c00c181050745220310b001c0190701c150712aa04001143c0007041e90100030b18140c0034907115a01d1410807410050700d550195500402803980762100010600c955038009a01100403405042c03801403511400b504c8074001c0441d07000f1100311402c13138081c0540e5200900c0b43c0000080b0541410943c50b2044110080714507013021515800c2080c042007a41445440c0d42148401030030300c044924203100b102c030064024494007815074034108010078075042034245600140341c0c0081c02404294400d091120103404281c450500040d04c050001c0c039500c0c8288568040304040781c0d035040f410352454a52001170319403e003800013540034000b170004600c401040326000500c00756001d07607166407250a01c103007407482004814520040400c201310042c0c0e44280c810307511034180c003040100280203050490082c004141c1851041c0000181d907024031200001820500e03030f048009016602185102c82d200c1002942d292021515009000b022280991f05c80342044003010122104455a0740014 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 18384080 1250 18382830 18382841
    0xf0c09120708120f0316030920120115090b0f0907170106030506010503011205010912030906050105040903020a0308180a08070303291302160c08070e04020a090b030c0301 75
    0x56589a0108508100d082c4007448074141d03400481c0985804c2240d0b03502410383c90b10005041201c0c01019082c1e41c480140030358407840803990055a11071036070304041c105004a183d0300d801184122146846007513218014001c5201c110003291040c112030307103010284005000d082030341c075900c55000c079031102441c2c88500345a1320503012079a40317143c10342c03092207990030400060b00b001081506050030841c090344c12808a1b81120b01c01a204c402d01030b29400c00318010240c40500500e8090501030502e41d16605800c8602103034041c520412159a8850402040380c4101d680200036802c480c0c001804603000b103040c1948031100c035048100c0e81d5005901d4606140405808032401c200118211003819810b10540c600010b4126010102c1c0241400303561544404941941c0b01d071602c41d03d51202d100e101c0c2c0595250610f401c550440c5a5402c0c0f80260074058135020f26480391092034400603c4501c0b580c0080e014070340252030243c0c01410f02c0c01c005e02400f1300412854041c401c0818070f0340c0780d0301c091190 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 18385330 1250 18384080 18384109
    0x20912010525030b03120a020a060f0b03010b0f03060f040213110a11060403021002030c090405010b04050118060e0d080f030a0605040506010203070503030a15050604150909050903030f0c09 83
    0x20b8103141000410700c603064200c00e0980000301490010801543e440014022400001380b4000701d459041d1000708918000701ea1a00074941801c00f40c1283e154a05900420301c1400103d0007402182040d905006400c10741c81062941940084040b605100100c0c00140d08540040c15500913a002c00b0032080c242e5403105421400058002400604941e0000303040880b81c0f1400080d2a150400d0b0b10025524000014500082903001010403080c00650041b01d8001c0c4001d442408a90780da142040751031b0b00a0302c50706020483c1e03c1c00d14003840c42c075040361000f50340382c50f1104415141680140281c000b0794481c00c5032510b4007000050002d5034017102452042480080219065091000f4041075590242c8142d040d58402d021200000314007000f640da000081c0f0000080d03034a501584000310b00d2256020030340090001a0200d500c0074504400c404481e0b460b25074420030f668910100c2c00311101200c9547c0f20341c20038000301e2030202c1d011100680152030004410b040c91402d5000401f1190300c0c035003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 18386580 1250 18385330 18385351
    0xf070b0109060b07030c0b06190e01030606080106080304031b0905010311150c10020717040305060a06050a05010e01030209180109020702010e030d050304121e09051309020f040209120105 82
    0x100034071a414081c0c1c0003e4003880d0741d19400c3c00907079034000e00b40d1240f0003401000e421100000500303685407080e0740c4036003290b10529044c81c550342d01090900240d0078001512440d00b004404030344907005000728411100003070b004500d09440c1d40c03102c510306885900c1c501354502c01d61000285824050184601a44c080c03800c90703d4100c1284200b0990842040e060400c0d07603401c1c80b4040d035080c030206603025040d020400141c0e0303800c510701d000c802c0301f4101da00502c0c0c0200701090101c140300700010740c2c82c850041c0400c20091113803148104480e1004501c00c90b03001130f800303c241c1d06031940b29802030041c0e0320028081c0c1901d50a00d030b00c01e035440c0200740c020001c0f103580402d04806660303000c400c90000030001e0300070705650404080003e006100043c009001f590002100301c80007480b03044844c9020b052491510001c444c509401003010215104513807191115407a021150600361180150b41980185422580e02c5880c05000194010070407556111011035440503041c8000c1c00707594414a01700c00b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 18387830 1250 18386580 18386603
    0xc031112030a180c05130b1c05070801090f060e010b0301050403030c020d080609040b060303070f0605010611030901080f07030b0d0b040605010b0c070605030406020c010c0305010509130314070204020f07 89
    0x42d9070488820060034031101c199840354a0210703021604103800c0d16000d541007503d11803130b00c400b50003820b001c91300c0c10742101e0007405200480107002044ca441c90720072000c2d6403000c0e66070300c08103003a2004013401038000869100c02100041a40c1d01074514181c9000010034002030b5100060f007101e05c00c44094010030380310142038a80b240d042c07044c040c0004071402c282d5100c0c20320402140c000540180010b14202e185004201305990410644001d0b0340e000d01c941c51f40c0909031510402500c401c0c451007020549401840000d030300c0100640d041010181c6d2601902c5d030316a801c1104021001d010312060650b190310b040c04030b40390301c0440c240b01401390840c01c82c9410726103015030484005070b00001d02050b007400840e0715840c000c10250121001880d0150b03c0351542d0410302c0003480f0b222602c41c143e41c41e081d9800460368058018904942d030482d03003100242d450945107071150b800032074001c3c00906415542203c28104c54094620903001400060078a002006000071641c4180070907210380d405074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 18389080 1250 18387830 18387841
    0x8060406090213090c0302270315040206070f02010908030d0203091005130f03090e04050f0c0105031519080a05060108070b04060e09060d020619081003030f0c03111203 74
    0x3401050010001104110329080f011400040340c4032240c0200e220781502c80e881e906440f4401c0c1c0550b00c15241000c0d40062551034030404d1266004d0602031140207005880c0d070b1401c00205540414402e60b00136040e20f1900402d41ea40c0c602d12030b20034500700c0c14003a400b08007103045071003007005c0d100c02025000c0041c0c1c2ca0906d075002524010b9800c07007407480a420001040800940050480c038034540c08007051400d0b200900d001c1e681c13607a00b604000a019211000c020500c90000340c44402c84204900707450321102654011541884200e9000c1c0c15048190001527290811480224142c0140f0b1207154106071100b021070300304240c4160a5480303500940040c4800d00080c00310702e00030440d81c0ca00038503042c80d0140c058000c4c032000680030b20902210001070761544400d1000340400d58024242c60780c550701c280710a26080710304d410000008000318006500034000e80302c030b42c080da50075894140207845810700407a81b00081150031820080400e20003001090104602c9028603030803003040f80c4031b1511 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 18390330 1250 18389080 18389089
    0x1020f07051605010f1d030d120e0105040206090d050c10020a03181d06010c020a06020f0d050c0a0602090d120305010315091a060d17040302120d05030f040f02030109030806 76
    0x2c20804120280014a0400c0355a8010b200340f039074909181071a120780314982c0030b200704200440c42c000303030107010f429100c0003401d40c00b442449401013005030403c2400c000c0061035088800850300250002000c0007400440d1070300e5007800c85414403413012161080c000d98085008040303003241c11400340e0b0000d241541015080b04c1b00751070181035034031b4181685240201090030110f24900a00103880103802080c0d4603441150440455a005030080340f40395030341c04009645000440c12418103020b13004003080c00e54468801c6654066100000b404020100e41b101c81c001d500015190f68029080030381a4001745034080001c8402003142c85c0003806600d1418441040502c1150b41038000d494400c02e440014541d40a48207d600e22070282082a981d240100d2051542190007800c0750031128007c2c42080708001c0103000f52842500c1c0510b0880c0c59140c01c90b618000c84004401060701803000900d10b0300300701c1c10340d681705001d081c80e401d084000d60086800c49070301d02001c1d00060300c80401c200325810b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 18391580 1250 18390330 18390343
    0xd0203010f05010302240919050603100603060503010204060207181d030a030507030b03340311030f03040f09020a030914010903110f1203090114010b03010303030605010c080a11010e01020f0705 85
    0x6e840d00040c1813007003003540ca03820314400c05020034840c8401c00c9821088134611140350340544230150500c3d0fa2030520181c800c16101380c5115250009080010206140c1018000c0c0c90442d0130b0340d0010140c00382007020101111130740b02210300341e42d40e0340d02d20700006140d42284d017510451060f002e19551440d040000781078a900134912418582484024401510f0016080010045140c0560f0101c2c5150b40c0f5440d1041c4107000d010b0040ca2401c0340030040c41581441c0440205044080b20f0340b0f03040405096445e4042c03481195055041007004010020035a0020000f00003607141c0003030016070540d58000d00041c90705420340e40381c1d51441020101504810081d40d01d488800080149030f8040610a030b6685488132542d8440a0200100304944801d402c1450000140c1c0c40d1910704e90b031582640240c5800c244025800682406d00000b03195010302d080c0581240c100038024a0300005e1101a035452010310942001e9642c1d942901020a03420b00c050311031030034000034541c4e5a4400342000ea02e803d1 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 18392830 1250 18391580 18391609
    0x110c0727050c0301090203040309090c02011a0906060304140c03031306021b030d1d040203040b06031203010b03011a0d0f0209011202040f060f0903060e03070611120705090d0203010f05010302 84
    0x2403a110500a040b0200c070203481c1103461605000d42c2e0ba540b00d1400329072900c80d0741d0080c40c155013400c06103011a0f4041d0058080b800e890f406041c412031500e02044010101941d14075040030003080898003194403049420081c407410001c6400707032440380300031078030319407101c0100e01c5a040140d400313100541c0d0501403030202102a8002d030182000b55400241c0b234200b641c2883c0103201003284039403055252000900c8442400420441d100d00e803e0400d01e410b5031086034003601c60701401c1e203902e403c40700354402d0324107036401c5501450a503801c0c4420746415103411840c411402d0000e100e02c800031090350181c24a41d43c040c640158940241e0b40c0003522044404680c43c0c0014010710040c042982e030b40c0041d10842c0c105141c032401c5103140d5242912102e5440d0030142410f401e0280c08501032000000901e4198450300c1e0821400040482050740f0b4003604e169545412004004200b115200710050a581000280404040c104984c00282154a6190402c8000c2c0d15800104254a0055200d0a114 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 18394080 1250 18392830 18392909
    0x30605090a2a0e0a020403050d050a090302040b13051906091a040902120f010b090705030106081303020304080f0606040b01030506030a15020d09050102030a061e09110c07 75
    0x107651656581c1e5180d80e15034203000d00038640c0d01030041005020a6041c001e10090803009071500300520501c1c0650302c2400241c3c0d45100300d5071104e000030720030320071078181d41c121340e66408505056900f008040d110520f42c10fa1f200c05520381030122001c0a209150003855001c02e00314003000503044e43e03010380e0543d90061141d540b6210701d105101d064100c4190300c0c40b104540018445a062000039414003406602280c14860b582144400450540c402e03626288116018005551507510031541c0384800d00500300050b01c0c03100418000d8041c440210001031003801620304064881d0080f034582746039035a0b0b001c0580d100c5418820503040030f1040c404900020318082c05145080d0011950b0381108600c002d20b02c002c000c0c1003546c80c0c10540d05485441c002d0007014010312005042143c00b079082503904207171040c0f40141c00200b07514030b6640c096100d09035103544c02003140b4100d10f03c0000c0c40c0404040c0d00d02e4a003040b4110281506001c0b0a020301540c60328181d6103400c0c49101095120640c03051100d4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 18395330 1250 18394080 18394093
    0xf0f071103120703031805030c150105060711010f020a0803090d080906010b03070807051c0507080901050402031b03070f0816060302040f030809010302070c030b01090b0102031c05090a0b010e0103060509 89
    0x180000b90304035119503806080214280c038030035005811005030000040c05501000c901c00034640004102c1506043c280800c1000d26601c8038108901481059001407051503d50b4202015502503512588580a00c0c01030750300003a0180c4849075941e00858683c46607030440e039580100150040400e54105000b030000308a075605103020b40403503100241c00c282c00d02411000041e1500c0c801d4081360555060110604600c600304003924001c0d0400b99400760104404130001000b41030140f013000c4c46039400800919541c0044001d040070101c1130112503400d8051020089640f14600190400900c000001402c208115813004030b403032005c580080701054010027041050107440800182a00c3c0c0040c1310990750004040180d000303105a200c014903442502200109010542c10003a040f02c010020503c142c1d40d000004a0716441802c40c07082401d56602d00f01108441d4992103a64043c03141022124014401e40715010078400c268003c0712044616401402000181c1c01030940150140c80103260 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 18396580 1250 18395330 18395353
    0x100b130501030e03040b04060207050f010c0c06051e0301030c05041107050703080f07061d0106090603031403060406170a0201030c0e091303031503031806020d051b030f0f071103 78
    0x46049040c03040034105034032a0716403002c40f881881201e0003032003400e6019a03295612403000e5200d14682c420680b00300e0382c4100504295004101038010702c0d510100a86045040100503505600242015042e810341490a19403502e03000e002103000c0c502030b600d0a40b5442c40c00040000740c445002d11000c08010900401e00015400501c5106403a401032404d41c945103845400703440c6004410000e8141428003503007a0b85040480c0c1b109000c2034440000707104182e2110010b0095444c1444000c0c0040d001d0040303030310500035440c082c507001000240040798050b581e95101c84400c0b04c9000085698122800300021036070540315406015416041030100070070f00c440000e4509000402d00c031800c0354045100d134101480ba83c013076030503190281c1000c8007243c1c4a040040c00c1c2c00113201c4081407a403001e880459818000128882c1ca0b6011340d648900e8040d0003501c812100f20b00228002040c1700500240440c409210050070394000c907900c6c00b0f51101d129081c860855072070504124041c1e0001e0001c8003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 18397830 1250 18396580 18396607
    0x10c0c090f020d020d050412080106050405010c020a050409030801060305060f090406090302010e1e01050c030c07120c0501060e090d090303020c101b0c03150510030308130209040803100b 82
    0x104480c00440300007040d10715444000d020f8402c659120612510000307800008184662000d809039020706e290f419a50303901902901c0d054000e001c3c080110b08240401c0200d0b6120b601d42c1a5a2072000c2c0410a070300c5c1d07841c1c011800f941c2c003a034411004101054010b110072030345031103401c1e80400100c8105098000703210205901d0f10003d44051700b15038482d4000c3c81414000d400a58080042c90112800e0510580c40c208031001c0900c0508550350a2101244030b0200c15002c0d42c1c0600346034140070b840c1000d680d451045140c455400b480c1804010f10419000c12020b2040c00c00900e40d20b68001c1035403500007030150501d240b024030b900c2403064600040c00440d900017038292901d031090380c1e103810782e203821401684c445280a84c44d58480899480d040e0070450001e1201003107034442c1d42c9400e941454048800180c800490f003402e084100c1c80c50410200c0d11038403019801c10800740030032b81181480c2c1c0100d48945401c5030f0a03110703828004203004640c08a42c01c03000090941103215805d008503110040c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 18399080 1250 18397830 18397853
    0x703050a050a0c0b09030a0f02030306150703020a17070606051002060606130504020c0114010602070303050a0c03200106030c0f03080f0a0311030405070e0f01180509070b0c06090c010c 81
    0x20040060101d40410b0340c6004000a0207016000703d111403040c601500025030301c2d400303654503070300103040300054041c014000420b0341d000340c00061810401e10504510040d40350040d000680443c460321a028012801c98148203141c1158124003070b9464025092550a0707800307da0007280907009190640080c81c1c1c1c003181c810f0700414202c49007a542c8211040705103c0140581240d5030252001900803542d0700c056100e614520b154002c40065aaa00c1c01c0c1a030726503c1d148009000f10341c0070000c584c5485c4c490a4002d42c8184a400c1c40030f55020100903080221598030b1038400319030355450090040c05100c81080d8000c1554841c6016040c0c04c66494010902804540004c034550120315904628060b030040d100150030310b007005440b880d0a0a0003a5128101e01c181103a0030400c030003050900f003603490580c7c103881c0e126155046c000f04a441c14402848024071100e000d02903c5008035441010000030040745a500000740f45505014a240d4105210042581c2c1400310006801c000201b40500c0c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 18400330 1250 18399080 18399097
    0x1080d05070b13061b03021e070c0902030702010906050112050f0f030904020c0c031f050f01060507080309121912051005010503130b04120305060f010e041802030a03050306011103070305 82
    0x41141519440c500300000d0702170031404130500b481e0400d202140e164180d0161120780f01034040026081e440f8040748195108101d0b006d80441070a01040c00035603000d80055400240d40d1000050401c01c80e00c912044600c00e03040503100c09803030500c02d4203002003085002802a50103010340822001c20764070300d07540e208031807010f40a07540110b0f100803002010b1140201e980c00142c141c031250250080c21b5940000c9010311501d01d945020003081902200954080c16110b0070340340c0c6480d02d0340d1a15820115040104407900030f110f80b081c004021094840038000b943e5004881c1840c0d80c4a20034003905107210325811b0600945483c08103d891b90f948403014088442c28240a42c2e03940325031000e24801b51000704040c15540c0c80c0010311040000018404840c800c1540e001c10461b1130f81c0080058541c03842c0e041d980024140c1e07119917000d10b0258010040027610450580c40824070350b002c01e0910784440801d030040b0398040300700205540c214280711061200340c1e000d18600780c03581c1d03005040c0d800350f140c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 18401580 1250 18400330 18400351
    0x110d030615230c010b03070b0304020102030904050612070303050d140405071707080a05070501080601021506040b04020904090f0515070801060302030c0d090b0702011107080d0911130501080d05070b 87
    0x2145880070090701660401d403410402031030fa030360101c41c9001c0c040c00c1040b400c14000d111b820000610960380e0820340f0b00484d0705074041d62074503035001f04000152030040c10f910361048481180400c100020401c1c035000314425203440f911007040340d0168085881444815199003031110401c0002000403031448203980d0441c0305140d04c00328a0340342510b083c61681200145100f07900c2c003082032000014420713003102c1007645e6038440b60b43c602004a0f00e03035550b10f045182150284e004039000340350940000b00100000fa00050610948000140036135030540c905841c0a441042c603803041c410203100e19861070f901300c403118547d400c0109008000c500140325050400d54040049100d409039101159409800440c0601c042c840320b00301154100015112000550704e081201c21031803030030b141614141a0011545410454500c1e0800050081c0c0039007120082c0c20540c54000c0d03a580d44860f4040b120300303168001100c2d030500c070509103001e0381d12000c401805020b002087c00140141c8940341e011580302d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 18402830 1250 18401580 18401597
    0x4050d06021308030310060e030c0111011b09030507090603050316050c0a03080d0609050603030901050904020906130305010b03150a0e07080d230403050303010b071a07110d030615 79
    0x80000c028025241d21492000480d4000a04400000055130103422092a695000c0d9620303501501c5500800001c2600358000c0c202d224030b158058500382e44d45a40b45400800c07d02000a0640013403c1d80421190216500b6032080c018040b0803c41040a080e0016003006a58156103070240d50303018003003e10080b81d040c0840c21701080b41c00d200040500e600900212401c984034039003410389070885082e002c0c4142c504a0000340301012406450f0007214050b010318a007601d410011100b030751000305826009a000c01444244d502c3d0400180414854402d1500c100d40c150701d0454256114810041c4c46a03120382380c4d0468450007606080d0b000100108006100004503080c10b00704956503005c408207000f901841c0003155007090380360b078480c401c48503000e11310102c0038481c0b002c5000b58003014045510600040c0200401e00703009055a40c094011031100c00d2800000c80a00081101c00710b00003003042d0151405403008018042e105081e078102884168286100059449044c1039184100729691 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 18404080 1250 18402830 18402833
    0x60e07051b150a0b040b030a02060f180904050c0901060203070309170a120302030601090f0e0a020306030703060609020405090705090906010e0103020d0614010809120412140a0b0703050105040902030304050d 91
    0x40000001c041c58412100e0b8081c68421a4100200481c244040c00760f401d00314400010300c1c010440c200c245a00400040c14030854803400100c3e50003100048078100c03400c070346010341d0750f036091255480340c3d204000402d8541560000d002c1280c0c81a880001594400d00000703000070b4202150400340c0d01c40b480c88035503111407403480c18902001b070036010304440c40010703500c005581c2c0340d002540320310340070b80364030402d165245402c80f15010340f803183c2e040c00e02174003011038903000d00364000b1074000300000e0807118426107d45034501200c030503501c14080d003540000c04110342d08050703840b01d50000c1d00c3c1c18a2414601d200000c07070311414004010034100440f400c800c0016078000e0381501d121102e020400c015190701c0d400100e082c0c80e00891800d012a003264009003051000007182c80c4411200b0b8226410585080c03c40c6040d162800c1d411118400c010491400e0482c080007901d0f44a4022103c80d2080d0910070405021241e06810040c080e030b051102070b10140e1800402c4034100d070025144c0e610303111000e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 18405330 1250 18404080 18404083
    0xc16020a0e04030c0b06030309150901030908040e0708010603020a021e010f02160215070503070609020609060304050d090f060c020d02060d02072315060105030a0905030a0201020409060e07051b 85
    0x195048401c1054106040c80203041e0b100d43c4000e00c45100b1000d0070520b0301d54000f015640c0c099610309991080c43c1091a04162000030003804c1c0072001030401090400705c95440b85000c1d002500107180c1012828100058180d000b000b10340100014141140b030319003450310081d01d419511420f0140c81c8402d4000c8a101c030b0095100c1094409000401c5403142d02000c80a207014030201402d03072090341c0c4800441202000c00c02100ca0190784203005501d02242584c0d150003514070f103035091380e104800f4406100540c4031500110b1049203d00301078200c00e41e4044001d441805c0d540c2101403041504c0c002030204942041d1440f0341190103c812002e501c805100041c0c451107092841100d10780040388103420010f040417485c0c41030098041440b2110315106a441e035802c120244a040e0003028000314044e075000c0c030002c42d003003c0025004103460445480305071940c1e0101e036030880182e600041c10031440c170781ca20809000e0100303552a041c0724142000000c00c01c2c006c0d100c1410090481a1070409124070 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 18406580 1250 18405330 18405349
    0x80a0902010e060307120c0f030b0303032e050907030203012d1701060816030218040809090712050f010f05030703110f0d050105010603020403060b0f0904030f03140c0301090606080c1602 82
    0x5000507c02170f20200701c02448000522032150109042000092040c500032041c2c0c3d2207100c003000f16a01c001a20801200d502d151810b44030040281c400011a154858045e040d05c6010a07807405684e035490321846603045040e00101c10701c0344a00310720b2407d00e056034114040882d14001404840742508801d51401400180d100103018810400305110961416000c441264004c480c2d9034a00d5813030458088440380308480043c40a0001c0102d6483c030300d0003a103850340184a03481c00b030340d545105044030000c41e9070545900d01e0b4110740c500100301c0c1c800f20301160805040140d01a041180ca0756980c80d9810350b1034141c407441030088000040c403c0d2113010700744440e141c2200c000d00641d43e41e234801500a500034041036865134240001d86240742044c1451440c2c992019150745001d40d11070710201c3d240c15080b0502800c1640f030b4a202840c98484500b000d000b03092120b46a9941d5140425003401c075041e690081741445400c07000c004220b10a036054401d031481c1d03540b0411195031b441c40010401d08 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 18407830 1250 18406580 18406607
    0x170702100f031508060405010b030307030c020103020315040f0e06061e0d0503090d030306060806040c02060a050a0213091407170f10030803010e0406060b130302040908090301050106050a080a0902010e060307 91
    0xb0000000c204c00c0005016004a002c1d10080001290f071070245030300e034801c0380805030219a41108510040d44258011030340b0042a400300d9521a00c000300007030549960b007030084091a00c039060038210010601c42c1680202040320001c04441c02c681502c034403520b5030b110103031041c1702e080c200d002405014800c0383c0004000410380d14450110b4038018000702080d0180301c0001d2251000504c003401c0c02c1c825410018200c0d00202115543d001c3e44c0c1d0040c050040c0702d038402540a01c8100c94400b4441c24440150800f2200811702090b075006020401c40b00070010703400c00c1481c02e204140359040c5801c40c0d400c820348494006140c1e4901c09440345480c503951000709001c000100020f40c00443c580c48074040d92150130203000f26a27076100c0b0700010f40a07400d04c3d1805108011800c10051425900c013951301032003038814038104256540041d084807401d138010070103e02c00003203600303407594090324465001c248a08200310359142a00001c0a100e4190181400340000101040d003681c0202e058800d20f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 18409080 1250 18407830 18407861
    0x110301121b1d09150103020d06020a111204030204050c1201061d0916020f01050c030a021c020d05010e09010c0903020f010318030e0a060503090606010309030c08070b04170702100f03 80
    0x151142c0d0900c41408204a031080c000380500d1903240b6a50389440e0490b0f0481c0d4000b001c020b050905a2074500c020340c03041c013804050110b6051100d03941c0e0010712182c0c0500c0c1100340410b441d40d266006000940b10001c1c810350210100b004004082282c0c2079025046d5641c501e040d80d40b10280540780401e68912a4115030301040050412a00c482408000e01d00d1442a43c02d803100c03941302050760381c00c3e0f0301c00b80c44003400c0c00c1041c0002000c80380d0b150301505201c291005d1070a02150000b444a04036482242c2100c01c081e00d60b00103001002140ba081904404608000c10280b40301c01d0700109176810b54040248100c0c891600700c401c91307200390072001540c0002c6c20030104c02a4903160240c800204140080d0090fa440c00002a20038018401da038803070000040504210780d64800110010305022008500b440f00010110021440b00c1c000380c00000d125000f010404d0a050030207249030742c084d1004040181c8200140001038035081c16801c1005032138100364014a05121007607011b00307800188003100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 18410330 1250 18409080 18409109
    0x30909091b09090302070303081003080c06090d09080303040809010504080d0c05010b060a020601050607080c19020f0402040b0711030106080307060b0a0906080d11031b0a0303110301121b 82
    0x203000da10740c66060314154030580d1030034050b6030380c0114040d01d40da00400750150b0414002000440c5c02071080130350103c0244120792049803640da0302c200582040b11010084e074006010004202010044000c0d05540d504040781598540441c4965900c1700810092480700b000c01c17903862036402402514007600c07200381a03500c90326030300c0d90042c0741c10420350003a01e0a6090824401c0303c3d0034150b0031129405220f9000e408560b09000030b000883d405a4400c403068401000000c121302c3d020b1003040072081ca4042035980c00d440d00e00400400011782515903106500c1040308008940d21003044034001540240300301520342100740045d0040900d588400340b14080001e5840030000c03160b0000c040e0b07660444008822a840740c5d00441154000d00076100981e000c010300b85440c60207103018120513018041143e02c0c104221481c02c0c0503000d01440841390b540f00d209500f04041d014000c002414080044141c255850807801d1094189117001c0a080b400003402e003461408092868407018110307484055a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 18411580 1250 18410330 18410333
    0x22107050705040b0604061b02060406020d020601050303030c0301090b0f040f0204061b020105040501050304060b1c060c0212030a020d0908040608040b0f010503060408030a090f060f060b0705071203090909 90
    0x406a000a804640500440d1408600780c90300b03109016111402a1405090500b80300c025180714030b4120805182420110592006a032040018000ba140d580c1c0581140354414002a14000301a00007900c02c2d0801c4c010030a1544031081a641180c45200011071070390f0744040072402c2c13648032009245d081414038111411800c0740b600108101e030995654000d54015001d0120b103011800c03140240000c10400041040750f120720051600140644400911205581d00003040c1a0341001100622100014250103101e12841030180e142c0e400c0c005880e1460704069040c0c424480100f101c0310680d400301c0c1c0c0c5100004158811814a94000301c000d0361072340c85400281a540c4100c2d4210385009283c8001003481c0203001801741201c10140080c900303600d8030359070071405070001031508071280c0e0b0718000000030540318080c0c4081240900c400107a002c5a505c800015035a5980080f0001d80c0200301b104000764001401d682103a007002d00c00c548600c41c0c4d260441e800017295210030071036400d02e60640d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 18412830 1250 18411580 18411643
    0xf0a1a0a060f14070506040605040305040b0c0105041a060a0302011112040b1b1204030b1b1209070801140406050a0605060d0605090703060b18011b03020a020306010b031003060c02 79
    0x100010282c0340d05520078407000f103080d068411540010183d03040000414001905600096046882402d00506007510f800150344240c00c01450001140c0d10341040c001801140d21070204100800407c1c001d0b5403809002241d01c1c01c145d032100034104916100c8800c2c5000081c4251501441148100350395641e94100b403e400b90404c02440c107210f000c0400281402c0d200288008641840c05e50960a080c61601e9000f100c0f0002440c1c0044035800b082e040c68010800c80041c03024060070815040c4909000304a00e280ca0001e4000d41c58680c50300144490740030711103c45a80c0a40e002c400440c1c0c81d1399003c034070000f40a05500443c0c1014010680050341308003900200103440054900700f0169441c01c1d011410780f0000d00c035102a03076000b00400c0c00f00c6442440c1c802d038441c0c01030600406641d0340310f646001c0301e1650481680141c01144d0030904601d8140803a80c01088640a10b41c00e5081c079849800c103400c82031100070712041d035034003a524005000384407880f00300c0f49000d4600c407045078120307044 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 18414080 1250 18412830 18412847
    0x6120108060c04030b07030207110904030215010e01050102070b0903010b03070602060702010c0203040e0a0c0c080d06030203120306090609090f0607090e0a0603030e060c01020405040f0b0111060f0a1a0a06 90
    0x211807800740000003003203148040c0603201202e030400301c0c07a005629410b8060b030080d4802402980d80b00c0b01d00f041d04190f6183e0b81e68090085100754000d0607000d96130051510f00ca0010f070441c2c141d900480c00104110307a400100d41e81a20403a0940c01d0b41d134051400004e0052901c0702850303803d0f0160100c00074001c0e030046043c07441180c06400901045c1000c0c0c40813a103d00c150700403540305408400100f01d450a082d0301881007403d5074100103c150030742c3e445050076a007002d4801c2079a503440b06801d00440c21b090004003015204000890304504040002444602004004600917504800000c0200c0c000704407500b69030410006450312810245001000300445001c0c03010340011510124412011038400e01003200e801d50b41d10a40401c002d001c0200c05d91281441401e159000d2001203481e6846c0c0c03149419054050000007003907109200054010030400307032090a61b401550030001000800c80d11594060303141c00000980588810f420300000e1250038400d50005004071002c075059801a501 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 18415330 1250 18414080 18414089
    0x60f03061d0307021f02030705010501081f050402130e19060c030c11070302010818060a06090b0102060103151e05040605010302041d0a120c050d0810050406050d020f030309061201 79
    0x24000c825050a55540340f2640e90001d411900a5420312940c54005603040c261381900e00c192403418074907441d0b690070740307401f82c008508130740000511440c90460f00c024842c2c0280d041009005504d00798000480c1403482c0c507189141c00d0b4441d481c0814128040c01200824030752989040d4000180d42440402001121418030100c0d203449800712000f406072040000c5401203400510002c2d00750750045400e0745002d4003006440301e4600c10319400400910085114010703066000a001d40b60000420554200380702241c1590022801400445c841c1e00309201503101c00d81d40420f82454400691001c00071289016000b41d107040188401c004464001c0744c100d9000707d4041c080309010340c108407400c402c00d2050200e0b80c1d01410341c0c1d8000980b0b0b0b1020701030b565910f09102036121080d0b15800c3c20003c4101c07507640011291010015070f6103131150260050032f016501040f550303092001041d42845500b00c003178828420141030b80035a9400b04204c03103000002419803501c03101035031506d42d00044c083c060f = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 18416580 1250 18415330 18415361
    0x708010902030402030d03090501150b0c060a0b1c0312020708030402040501090209060d0504050a080705030a110106061209050c0a0909021804030c0b0c0f070c05090702010c051804060f0306 83
    0x11040014020b0b20301554005010740032403000c100c410b800508004400703c90035500c81c24185c98044424090200400d2085e00e215038600c0304c800014100180100501c0c0254178246c2403107601c1e1113203143c0c402d409419400360400c2c0700742c600f000d54111100e0494002038600000e80360b810481d4200103180107500c29201889641d8803041044141d0040000702a0090000d100403000c0e6801078202603001030041d010740d20816102d455142540d0b00070306c400d55640d48000b0b840107850368040032441100e80342d44000c20516044c40c00045c40c000349041810803450f01c820701c6c142449414271542c1c1c24200c0c01020600700a91310220007002d0102400c05078815141c1001f40404080100c13299445aa455a40c8410000060342d400c01902c03400340c078002a11406000740303416a0400001880401d010f0910682428a00010441d00c042d00a00c840116414603020b221041d0300181a60700005d80e48414420340e45a450100c0d0042800fa40500e030003201801d40001271184991210403205142c99 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 18417830 1250 18416580 18416597
    0xd09030e090609130f020301050a05091006060509040f0f05150112150b031009050702032502010903081e1209010b0603010e06090a02070b040309080d111506010504030b0c0307 77
    0x1080050300002103440c56082800040091311100c0e00042801d013030362103410315071412829600802d0840300112207949220781c0e02d409005030743c041000992031032004d07410240f100a05010004001e8020000407900654455400b0600352046420643d01074001c000304108515040c0604403004001600490209102d88030014103085140619549650f64404100d411841c01d1074681155100900c0c4158080e0b0800e070100d0080700718080c09024801650065480d1010325000c0d081c0c0140c00004501c131620311814901c0180d0b00410000d003100d400012154490344c01c00e0f0031600780c03840b0481e80500018001890303002c071755185110318010210701e8001c03c0800102010b0041612080c0140300e440d0808000040d11490030148180c1c0c0f214100d800507041080039a5aa080400c082d981180858400c040910107602d0800504103420340314502190f40744049150203072944010410070b002e0010382000100c49034020f4003218020f40d80807401c10381602c1e101d10315001640058550100180380c55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 18419080 1250 18417830 18417857
    0x100501081005060f130506030408210f060d030e0a080106080c0a03081204020301060506190e0306070903020d02030a0212060f0603030406090605090d0b0112050609030408070b0a03110d0903 83
    0x300380c07480a88201a20103407070080c419100140e1a04803a40e000221000b0703040c00700e00390303c0711009180038511424849840710074140304007d9a9016001c1c01c9100070100040001d88044040c8098000d907094401ca00032580c58103003102c80150312480190402d080d07500004244a0544c03141c0111240c22041e2080c0030a040c0401130403402c540310150a02c0c0040c0700d402c0b01007011942c5150072910040001401907a03590204030325400202d483c01d4911501c0c042da121203a0440c44005812800310050003003860403c038060600200341c0006800f071407004444c0e07001c41d28100003461850f41c00400000f40302ca05440d585603249012a1002640b200c3c1401040305420001305803001c0e036850ba00c0e80c182039410084201c1e1113401004080d80d100c80c503500d04401240302c01c119640030301071800a4001c42c11190400c989004000740611405e903200700070400ca171440c003080a1042d250102800c030f03583d00020208070094004500300d406000c03000984206a00f0a552222460700d1194490b00d1802d01c00 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 18420330 1250 18419080 18419101
    0x30606040b0906090a02040504061805101802070312020d0912020304030206040e06030a140303061e060703030504080d05130c06020d1709010204030506011409010503060408070b07031410050108 85
    0x1100c2207907402c8152000482c0b09072801c800d0907503005180410040c281a6510006010364441d40d00c13120140c0d82e00d103480c03200703920075003d40e640c051100a81020214600385d8881e540e90851200c0906141c0c2c040303014402c162051307030283d010845c0d0100a6403144410344c2100d000b0039103094201c40141889084041080c00482960708a9800a040e41e0406d898040903000d0420b000b0b2003281e25000750300307040c4005241c1202400b401d100c0d00c802540c8038070300742041c04a180d008040d4074500f40c0040040c031420365242c2049501c401c1d03140c500411a5103c1e4684540706020329810620424101002c0008010203211600141d600496241001c96a241c105980314840c0d070007120001000440440302d803102004e80034bc1c2203d80d90380018030345540d90700e0316820003c0c01c0c1c1000e04210f00d503980c8241d0500c4c12081250260600320045e0205080940d00d021051086c900024000303000b0b140001c10380b500941c80b0208034940201e01c04181d280048101406d0885406450b011860000104482c06207 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 18421580 1250 18420330 18420341
    0x3010605010f05070206090d0516030b060a0b04030212031e1224040507021207050c090702070f03030806040917030a0e0105010518060a08030f0a030b0d080d1d0303070e03060604 78
    0x280c40e100c07949000015001d00c200c0f0341c03001f00d5554020030300820b5800040d204019000886441c80c2901d80748a013545054020040040c016034451100400288824056001100c040b00e904950359180d00c654244550304500560143c021100c15000500526582800041006d40d252284008060f031711440402c141e041c540c031030711400b0700020384506a40d00f0254060390300100300d40100d9a001c540e21107817070b48030b5000e50780807601500048240c408074206200e1081d0001401d0000e480d0a82c1070101100411142d488081c0030040a6400b10704e01d9200d0f6400090701d140c100b0072210f90718804945402c1260300907240c03000c14910380780100038148810702c50b0740d060710402001030314286a0224803440c140c4001d0002ea50200e402c42d000556800d00300020081c8020118183da02d074010104064100d910418800b0300030384600c10304000040e00e800c21581220481600003420b40c00451010710303007c94107203400600d0710001041c8182c2c9500006036610180080f8101c510503613440c0b00b484260741 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 18422830 1250 18421580 18421607
    0x180f01110f0a090308160c050f030319051306050304022d130209040504050109020a0909080d0c0c050a06051f03050307020405041a010b07060e06072001060e150301060501 75
    0x81c8441920014024000c1c40700000e2440c0c1040c031180c4030740b03c07000307913610010510444070f44241c100f40800ca10f801812000f800f084a0010b003d907054404a84ca82c8610311009107c4221a00ca80b040316000740252072006030815102102641c5411b00a40143d00948042e40f04010030a8680b01204507903142c1e0143c0c0026610a80d004c0c079509040c081c044070a420b06428060b000e01481c000740d1660311400384202d005100100d0940c01a0050040100040c0c00c0b49840c1c0f81000001800300d21018201c3c4d183388074203040010140004c01c2c04a40204c1002401402400b800a418091003d190001d901646401c035107100d20300310f00c0e1010300d03541246200051043c1c10610054016141990055030f000340a5100503138441e14419180700920f10903085600500d2001c15014203001d05031003100461241c1c10000d10032402d0904004c1c0c412004100e244440c01c82901400140030710a422120050095250002060604c00d4070a609010035030f1016000790b03e070910000b91903125648421094 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 18424080 1250 18422830 18422861
    0x13090506030c01141e0909010b071a04020d0209040b240a030213060e0702010603150507080f28020903011a090f0c0702060a02011d0607090b0c070806180f01 69
    0xc2c411680190380000710348102080c42c19090125503090000c0c20942000b40601c8664650b42d0303140d5100b00311554a046c0c04c114540071083c0442d034006500e0940350380e02400e2080c0c401c0d40a60b52880028400c0c0510700d03000707411801020601c0100102c40140c503000c0c40d5401c9065201490608444841c90b0500b141554403c0c250b5108001604000d1000d140d82d848580001c50820b8840741010b0041c00c3c281c42105c0141e6503000100f050091400141019032003006080c001070410010041405401422640780c83e100100461500c0601c85402c4c403011207280e606403070442e0148034840094004650702070095081203010000e41000700c0000c91b2030500103003400c4044d107d02001051045008000326603440c8100b1411025070743d1079025144940580c0e00100c1c120550605052140b0504441500540e10540c2442291038000c640320080c8c405032505261034901d41491245001c020707500c4030780e80c2c0c0120428810400c0b8400109a00011305004442d00b1480c15403041d400c0b1394085030000d120 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 18425330 1250 18424080 18424093
    0x114040303030203191407020706090b07020f0316080106050f0405070f0503040302010f060306021c05010605030115020c0d030215010f0506040302010c06140f090f060411060a0908060a021309050603 87
    0xc0c0c025030196030080e4418070043c0d150001e920451040350300c6d0030040f21800190800f000951b5504001c0c0394003810031842c210142920704010080c2901458800a10842c404107091076152020480b0ba441d1340361201c0560045035444580340c3c000d107518041c090054050480c181c2e042e08090103403e00460265448070481248208211001c0d00042e004400719521041c10120b114424000c5002030341c05401d0069940302c4602e1501c00c011624020085040d00740001008a55008801d5904581c0b91002c4030b110302c0e032069012400e080c5280e02d5541d01c0892035003044203140d80025078030701900072515440c410b07907282c0740d140307012400c2841042d81c004001c0000b4001544036007595a07001d481042c02103059080b160b0040e09840003100c00b0078500e141b00c0c0800c00c00700e10401004000f60070b14400384c003450400351a000b032486c00344822540aa0400102c1c004a50702c1074288c0c20060009509960301400c10b81d0005010f940003143c02886004002c1c4040350f041d9941c1310319401804010002c001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 18426580 1250 18425330 18425333
    0x2012c071a22030f150606021606050307050c01050c0403050105070804050a15020d050a0504060b01090806060402030603160602010c090f1d070e0a0b0705100221040221030309060601140403 83
    0x120107032100888000304211000000010003044e10502d04901c12100c040d90008820202002c0744c0342075006078115400b140140c0340e00d082d161103190560300305284c0709aa907940d140d0107440c030348550030b07003401c0c258600410845038648160281052f244a180207100e41e071541c20007210324040954010340a90410341c00e04000905114a03e9003100d1052805070820315810850b40c1140d504070b882030310441e01e800c1040100234051042c0b40b0303080070909140608900305038105a440200908180c013503503000011444680d42001000010590f0030f020b030503034a4989034001e029082001c04800421185000424a0301182100b007007a100d03000407804941c0c99060008140c1e00c0050122028890100c9020106844a0761114042c2049004040d911400380c50b1942c98114071042048286205001c1210740c4180031481e186400c00d011105551030301d907800050000596001c7c61000701c89034450040d100701002c0051446202c0c10350540d0f604c7e586000c019907488000c80d0540440d040308100500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 18427830 1250 18426580 18426607
    0x5091804060f05070305160801180f020906040803070b0a0219050702040603050f0c0910120f1a131b05060318010605090c0301080d14120702012c071a 66
    0x16800390040e03401040d0040e00400d980e088030002d8034400b00090700c800410205140c2c5400030760781c00800385403034001c035850914583e180002004400c921582c95105143c1d60080c0f075016640301ca040149010758596980703402d02da8a44c4086c0007200c1c0482c1c940d001444400c41e81c800c1d220342c1c0100c00082003404140b601c048070140d010f11b04c12680956110004008188104042c400b0350070702c103000b4188180300104101016400410301c03400c2d0208030100f4006107403a0048030385000e81c0403c0c403c41c0300351680740c02003000301841a070301d4405c0c0e012400c00c0380042000300e203100d0550090304030b8217103c00f1710540d410b26008540640768010700d0800214580400300805041c003250071100000d0003a84800008181510980d460a201b41011005000c20802480380c50003103110745c20000d80000c030044400c0380d90302820000e0038800c0e00400010f04c141c0d00039000702c40c0b4000403031300000d01c58104000806140341400681700c601d100d58600440c0c040310368203095140400c408030190034041c8110300c80 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 18429080 1250 18427830 18427879
    0x9050402061b0106140603060a0b070206190302030411040209032805010504050609070f03030c150209032407030c0c020f040207080a02070801050f0c0703180803070807050105070509 80
    0x4036001030041280441d100b40c105107144204002000101c1c00902e05500c00e0340c03000030554601d1083da401c006100032650b45405410807100011010398440f0007500014080e03000308101d101c0140c184103007441006601d94001c40c4a24412845140d0040008080c4412070007500e00705a01903001109800c3d280744041c90486900031800c0e03401400040c559502403e41d03006507801c13030303441c3d2050040c09080481800303128041c201101c810520185151001004181903150180551085090003e98240950100e88020350b0140c00c481080803070300c40400342103103101108200c014818020841181c42070280c548400c0561303640d011000c18540800046400020116505c250700300301c9200010031a0b000340400180c0c0c0e401810710340d45011041ca0945000900304004d03c50441d0801145085217019155600c0e0546001000d105a8a10040070480d464100c000c1c02e2102007081010051408014044584100002e100644882d40203840f14000c4080c0154801c916034200d006504007280c1c80c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 18430330 1250 18429080 18429083
    0x30b0312041d0603030d0606030b09010b130e0901140112031d01022104080d09150e01120504030905190f08160314010f020706020301140f01050a14070501020a020d0210090507090504 80
    0x40c0c85c688003001c2c0306d00c81240c446900c04004280c40314139416007031604d07000c03142c0100759032080c9034503181c1b1006403130000c3c46140c040c681013000c2400202d038244109500640e5600e80070040300c3c03082c0d40c41d040210070200c02c0c110300b10006501c2040031688c030442c1d1020820701a0341a00100350203c0303076400b510b8810141003940380c012072041c48001030082c0200051004505282c60349203102d810300d91826010550072404030107000040c985c154181c2da008110b628482074010000507a0303221440c088070900600e1b840300e68448203011112100c412400f180340211115254880d9025a07182130182e02c0d91500921603015061408041001c12080301e80b414000c3d0078113000080810380840480100d030004201950842d9003c001032064501c80c241403021810210f031500030146070800020070f14402c1c1c138003e0041188038030000015010160a8035803150b03012000795183c04080c007000755200c168208403070043c4140560b08052062911440c05140d400ca4040c01d8124203004150300a0710001d0720 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 18431580 1250 18430330 18430333
    0x30e010c17040605030912040b0319020c010501080c0102070e010302030d0309030512240301050f220f05060403080606030405030406030b01090315050a0501060905030a060e010b0d03030b0312041d0603 88
    0xd00481105007000240050070094a80540768103020720300c9032410124040740560b0150800080c003007148a1415a9401440d4076440c0404003640741d81c201c060300468ac2800c06035824440046440c0c174003c2540b410200080e42111f10443c0d8450a032800740b00284406034141c0c04c40a4154201403194005035403c5000341041490b02040301c01000400d18115059240304440a00610419000000341441d5040c114000c0c130250500c8084110210030103801e403041301d480c03130407560855400711052c0c0d01040d401030703940e480342601410f2041d2124001c403002c40c00204c40c40300144d03091600382c00f80e9026a070894000c50402d420507405070000c007050702005041c01080200003002624031020a00702101d8540049040c3c10302e844118151841a04840144050395100b440281c038001901080c440c1c010401003003010f501004d4900424030180929005400c000f4810181a003681017078411804c10340071103440380c07403540044540c1d001714000d081104a200c0d0f008201091046086038000d2001070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 18432830 1250 18431580 18431603
    0x80f0705090a0e090d050a021b01090801090609060f090b04060207050c0a15030c03020f120c04091107050d021b01030c0908060a0e160e06060a05040504060306050a0f09030e010c 78
    0x40001c030510300b01d070b108840c805a9241000000c0c1c4060141440f10010360401347d090890384200651125100c0f40ca40b1940358071004c404a09038480c03059000100182c5e00200701150301403c00a024114800090342e4a42c01e103001c42000345924421400010b03000b412212040e201d40e42c4a01c0694414007003601d442c030495001060643e980c0d092a001495084440403106143c0c01c4040d003070328010f400c1002803620501241e114100304804548181e04010b01e0198140d81c0d141ca044114000c94012010b41807501c4003c041100d00761000f0549180507904590120b00c003c00200d0f038031910f03000d0401007038030301100b0000d055020b500454481621401c10741c400540b10941700d807505100b101c1c03000f4002c2d15001443d0b04820705003c076290b0741c0261440040c0c0942400c1540301314001c0641240c0c002d4100042c070154091140381510702030f11000708207002450341c0c1c1c24598050082a29112811490b201c4000c0c01c415180c451028583c1e0301d9141c201049500b20010343e500d5030ba201b403d8581c1e03000c0c0b1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 18434080 1250 18432830 18432847
    0x3040305011b02010b030601080601090c0908060106020304061e140307022401060e0631030609080307030609090213020a0513030c060e03030408071202040b04090c05040e030a080f0705 81
    0x1c0c010b4007038842c442d0000c0284985080c000a003500d1103a90824001e8102c8401800b241101103181410b41c0c410b280007060100b41100d049902c0d503925440007045004050010407100d80c00301c0203004540c4582c3c1e54001d06205151440c07440d40c0c2030200c070804200c00c81064042c089422005d564020014015030b2805445aa01d030f800400c804010001c0040e0b0390f50040c800560402d030400f440c2d2009482203420104044003080590401c004260b26030312500500c504200408050680515408407041c00908064035140040307801c15070340000881d0601c1000b00d40b001241c0700382e0700c0042e00100801d120054040344a0020740c0071050034010003000b008a59013040800c6000c4005510230305007894482d20701100100305400302079115209400801c010401000005980c001f03491040300e410010344c0d01440020001d182c07110405800600702031a07401801b03001401d0504486040d641807080c2c0e4040780080e922407055000480204521001140c64400c0c201440d030740c0440755041081c134080c0179 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 18435330 1250 18434080 18434083
    0x7090504090809040213050307080304050306270304030501051009020702010509102703060e03030603062206050106080f012403050a0209060403210c0f0201050903120a02071403191403040305 84
    0x24114001d8003030306e0058104000d0404000e018010030044010f10b06207814103000a40350b8001900015105140114030100d15850710140c0403c11207440890340d585a0f24604203000c0c00d81210490301c105064280016001d050b4021280702941c140d481620385200c181c01c210603088442c1000e130030840d603d58480b0b104c00400402184072294281d400b4240e5103581340810950b0300011041344a6001401070008603200051401d4005003040c010304400490654050f4807451390034030141a480c200400050b2868001400070b019001040c9800301036a26260350207618078000a29075958498001d41c1c00b415480713030b403000d03801c000b01c10005480c000d21000025202e4010b5081a565a03c920b19901c012010188400064042c0e600f0300d008240699190f8143c01031000b0806414444005080c4445075000e000c0c100c42c29a0500d0040d45906130140025681e90384d40c000c1cae207002e5005200c003c00c1480c0000d4070440107894004194111082c555428041800c484034800c0c5502c010b01003c00003460 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 18436580 1250 18435330 18435337
    0x1503030c150108030a05040b0703020309030d09030308070f0f0318140f0d080606030a05060301090b01080106150201060f050103020918010806040c140d0308060a0306060305160e070905040908090402 87
    0x31200911075480e004005807072500341030b40f10810990080044130041c41d0000141d90071500e500b43d06644035002030405a04501c94040b00036810b00500c058034803450303080702c807280540340a9541c08030540d4800030140e035a840800301030b00c0480c0b56400000259882070b00f1031441382211452a02a82507207560b0103111044c0020018419002000580f0318020208900c1d40040e01c03520388681c107410004081803040c48080d043d511741c82c0d00d039000220141c41c01d4100040440e480018841150f0f51a442d4a00038a9a4017800c582555000c5100c181c0c0ca205020343d10907114031503014201c15182c0340054000750720031b00100e9046020b80084c80c20f406520020b5500801c903100c0500820729261a200c0e400c0c100a420003605640342d2540c00b401074a41c046406420b030b0341800c05000946038a00010300c90b038429400146070340e040030000300070018081b03406001d0f208a491001c0c10030f0313150540c110b0503407000c5a10384001820f400040180e480d190300b0110b00603008410840c40c180c4181c0201e000c0c0c2e030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 18437830 1250 18436580 18436597
    0x307030b0a020a0e0603010308070201030b1503040f02030c0102030f0405040e0a0b0408040504060609060f030c1103160b07030506091504020d11190306080703020405100504050103030c1209060801030b150303 91
    0x294042888400381c1e0b04010386040b4010125401741c0780d503041d9a0f400e80306004221002e0304040c5e0b078858a0300562642c02070b0700d160890492483d5100d00c0c0c189030410203000c003032108034064042c040320001194000002e807000c0c80048841c280c1440d050030284401003c503554005080c0c42096405070200d010402c503140a40d000703c400e280d40d2824030040c801968802c2d48101d0800407080340400c480f503440500f520043c8440e00d40882c491004683c211181c0e00b0f03440d042e000a010001350142c4002c00144c299128611600309442e5507605d006080d0304950040781c9142d0058480700000302c00c2c6007040b030085030702e00c0000c03c014202505418010300300c440c02e0b40300c1182075000241444a01010b1007141d00406100c1c5000d00070b80f403c1502194590003140700090007541c4a401190b00101080e901c17030003821000d0700c20401581e41c0c0c1001840c0078050754050300c080e09030350807030343d01c181c82174036024166021515850070f182d2841e61a012000c500170b10060403201401d401045a0b50244010304440 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 18439080 1250 18437830 18437851
    0x609060703080f060f010f1101060302060c0102120a020702030703080a03090804140f030a03141804050c0a17040506010510030e0a150e010605030a080901090305070f030b0a020a0e06090307030b 85
    0x2440e014140103100390f0090040c0d4450810050f00f8440d0360f91007802d109500c0c0152170061003160303010f04800d01600071504004c0d4802c80108617000070000c158003030200624111444e040584071061540c08920400402039051f81101909002040a550040030680c1091a00190501040c0c0f51125107800c50b8200181110000c2038000052900604100b403202d4210060101c882c0c9a0394080c1503065880303013500c03d030000801c181342e0700101c2102010620b100988103000c54030300304600c0c18860348001d105001050019610808900e00c26500a22607540400149200d03401c001c02c01240640d0b0050f00380c1010303103405005100d00400c0c0000030802c0e102e1f510584401c089040c960041d964007011a595503032404400304144e50b000244607144a820000b0281d540116100403100c0400c81d800180032031090b190000341c2d1000144250301100c1c001e042000f150b444a070010303016031181124490004080040a00341c81c9003110007090400f20007411208025500d0343d0b40719800d0300440d00310380728 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 18440330 1250 18439080 18439097
    0x306020405010e010e03060a1a090109060920040302040203100801140402030d03020a0801150203130b0307020c06041401120609090311060709060c15060e010308090109050306010506180609060703 86
    0x90358003c0c0582c82c12030001d0030894103c610520109503600302c020a000c003080d40b602003104a04440800c00000d40c1380289c010070240da110008400901030301c1c4100d4607860700e0103e800c501e000e255508140c0500c10040d0b0b00e07140c10300e143c003080069000075103c05013104444d03000240e1040c00340b041d94442a441c1e42c81c0600d0f45401d00426003002c0d8070458520506004014403003404d40d100e0116410f44082c0b2200c82c019a00341d1004034039601907543e040d02403a44203a004607003411400040c6102d1100c0350b080b0340301c008914085c07141c0b40c01184030790000300031072400325886580100b80700301401c2d505080c000341c800c0d6078254507400e40b402c000096021502c0600c24280b4100c06214040d44000075003046060079141c03000040c02800b03141c1d8003900742104c202002030916610340108000704408141c0315125610390818041941c4070003e11408155020400201420085281030480b40000c041d282070084210850944902079900305511a8042103001701c44e550714005011458043d0359030196 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 18441580 1250 18440330 18440339
    0xf09030106090204081f050c090409050a0206030708190c05030f060d20010801050a0e01030f0c050a0303090503010c02010605030d030e01090b18060c0f030406020705150c030703060906080a0602070203120403060204 94
    0x14500c2d042c42508025400d1108010823001200111590b41340d06403000030340203600d400c0440c1007013801000294490130000c180528158000c00c806d01078502c4802c2c80c00110044c0600e80b003114031289404020032010300000e14040600c0380d03102e501c8000685142c0108865039212600300c5290045066144124480c2d8000780d41c1c00344c1494007411007a15036402290501c40070440c1f0000500c401003802858103010300070401c40c010000d000b403002410862180c1d07200d180190004500e401020301030741c81c00d1103003200144140682421150302901802c02e4180c0841c04070094090301da24040e1543d02c0e00140c00c00280c5840403d40324011420403002c503500051542030800c503025080344409042445684a604242001c40703800c140d002200695414241c0382c418100100c91401c03501c0840148100018406001c000f140315161660341000000d0b07ca0924408071040c902400c5440d0707001c121403a000910350350082180500080441e2076007030074203100755259403107600200c035941d401050810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 18442830 1250 18441580 18441613
    0x1c110126040804150e030303130804080d020c040f180305030a0207080c060a06080703030e012d0c0506070309050304050405072a150203010302060d0c030f0212090c0303030405030f0903010609020408 87
    0x1884c04420380341c11122120140e00013035603800082e000e400740c601700e40004010840200f044400410b05e00d02900c0e0318040090010791202c0e044498a4000c6040061010203211b9134400da1030030044103442c0790503180c46a2012281c03a000100702c3d044c4203a003000210086804038020b402210741540c02080315142c00e44890043d14596440070244da2310444080c00040d40003180c10b4a160000e191100300c28006103107002500f4808219503101035101058103c400e43c0c041408d0880c01d001c0e01c110784031500c0341c0700201c040301c40480000c2c01c0c9800a010034401854075400c281e800038032038949010110791000c076040700c911504814110601443d001042004861070f40000b4a00703c106003182591315603004105e6a110302c1180715165a41c4882c0d030300103280030342d02c602c0c41614100c40c21034903120f095140700700711141518000614401c641d420300d55460000202c0b07108907440409541451032203882e40c00c2a0f0031030641560305540324400030038080100e00c040c20082848500514180255207002e9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 18444080 1250 18442830 18442859
    0xa081504021216080108030f030403090909051608030405010207090e0309030d020d080912030106050901030609230901090503090910050d030f0806010c020105040513020d02070609021c110126040804 87
    0x4074280410130740100b12801010083d02c441c0105170303414950301e907118581200d5855060304003000840c60200110140940080c8624400d400d103230341d00c4200c0e038450f80d400e5540d01440c4551030050340200c00c1804030381c0b1a0381045903480d034003904590414000d200000d040600040740040140e01c0111249a0164030080042d0401c40f264080c1c072105e0910814100c25100501810051280c0065015090392195008100074410120104441014815102c05440100c800892840945404601050f03011b00c40c45400a41c0722000b9071030301d1814010b2006002008000b003076000c5008500040c1e5494850070400071501c0390755050080c2d0300503080600f0410002e0203040c100250506603600503600075040f2010369808544400a01003d0b030170f01000380c443d84482e4180a4000300b1410300300400e07074100400091085403a009024074840d2083d40d0283c1d180e50190103050b2410300b01c01e1070f501824481c03c02c0c8804610310070224504e041c8400d100c007000d403000c0b10071400011b0101b002c1010920325 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 18445330 1250 18444080 18444121
    0x604120306031e1a090303060a0605040e011a0c01060b030a061401120e07090213030302010c02151302010e0603040f03081501050f0904020c07030606031104110a0815040212 76
    0x1000040d007151119082443d211030840c80e542036202c0c071401070100725030810004025100f40400ca628265511507140d420548440313004804854000c80d0b054050000c2c1ca003a103422100c10061a841d12580c0e055403241e0000040c50840d0401c5400000103003802440042d0801e0141303c2c0d44c03424071201d244200c0d0110361188908101111480314503030703800010b804070740b07182000125001060950103402c040555110065491001480340d65929019201c40220380c065002008040068441030f83c030390014240c40010508200e000504106d1040c0b0a20100d5006143c01e412140b041400b0682550007034a003580e14003203040c441c0701010b03840581554040008010042c400302c1030380001e000f030302030390144282010020440c070b0840d80311541a1000252803400f12031041d917076401c00a00401250100baa002c00e00c10343c1e448002e05150081e021250841c8800b1450030781d2405044030002e1010307003140f10045900900e0b500342e80e180e002500b1595080010f41c40359003840031100c50001e04131102c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 18446580 1250 18445330 18445337
    0x7030b09060f010f03270b09070e0702030f070503120103030507050105070e0f040b04090803071707020303060604050607030c0204060803250302070509040c0f0902030a0c030b090601050d0b0909060412 88
    0x1280001c0380d80c8882034282e51413103400c02040c1d2841c20100c284d80980100060062585e16440850500c9184050f00b0b00450041040d00c40c01030302c400b0b038252860011500500540c0c410048024403042707180040120b10300a0381500d0400d14a0042c46403100420303070060340080c6010a842c01072200a11455412400a080525480d09a90041075401150481c03c520a940d220f450a41c2ca03140d1380c0040000a40c4030040780c0d924035165201402003041c80002610800001d400a075400340004200c90003680c0c01803400e401c00d4540000c000b499441998120100403010f03c900303005844900404003e01003c4014545888420781d800c0e8203401d644019448010074440d00720b0100b038020407040240c031000d44505179566070300d003000e07420002140c2c0902060b10000e2000504090594040d601400f44020207100c0003000b4001182580c652142c3e244e401040c0d180801c09641c054001444111a0100081809517030000051064032040f261856950080b500308410080c040204000d00c09a40c03c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 18447830 1250 18446580 18446599
    0x708130f061b0507060507020a05090f0702060f01050109030807110d05070501020c090103020a0504021e07030f03060839181e1005040903050903100c080a020c1f020f0307030b0906 79
    0xc881c40c1c4d440d01c0502c1494244200000e200040d511100d14000c0586406031107520141454031941d00544000c551050050051002041011401650306412205d05035241d6070a5800c40d1102c00710b99101c0001150fa44c012244214200e07200d502a69904030f02800261003020f141400180c20f000c0707c118400d108070b06100c01400140c0d54030720480b003660b04c2542c00688a9200c40c654071603164500002400b2414045100313401c01d903010031014140040d6036424000c090307541c00f00c40c1d80c808010340010401d805004c0f41c000183d00c68428400d10b04c5805468002e200520800304119000e11045080f03040c071180104400100c04c0c0e9800b120125040c480c4014a02c3c0100001c0d41680690107590710890319140500103140c803075800c2d140070304001030a039083c0e4088000c421008100078494600482c1500300011841c110520135a075003100a103002c0d181c10440090b2103004030100300d811a000c00d45c280242488025400b000c1c520034111a1400a41e02c11080200006418003c1840d8403a40604 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 18449080 1250 18447830 18447833
    0x207060207050a150c0f0b0603010c0804020310150506130f050a0303020a03030b0a0504110706050a050903090d080d1b02010b030118060b040e16091406030703080708130f061b 77
    0x103c0400480d0101102816a4a0a030004030b40c8565100d1010780214640128034052100101203640111400c070000c12442ca004442901e4101080324040e6054018082d031500e010a1604402074001d114442c1603500790b01c070b01c0001c901c3c2e00010100381c1c640c4c1d4956018042c0c00c808200110282604a0b11015050f28555000f0f564224a64005040540714a50300f15592949a03074400500310082c418400512014500c04d1590040350060310b5850915020076503802c851311842e8060392116010710700c0c0030092801c1c0640c242c60b0800480b041c48040000000362607682c0b1402240030b4001d50500180318062000909454120141510a0f4900440301c0b0505803048519107965a03c90380c04030380c507180798001034010401c030708841e4194003034031101540d00c0d0314418086059460a038020040c00203024141000c1807130484078142c26600565051010460380f0001d072005501c90200f403441c050680c01c003c095407003158450102818004030030711423290070111101c5c02c043d03070906450b40700308507 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 18450330 1250 18449080 18449089
    0x1803070f1e0e040f050607090303050904150803030a05090f0f060a0f0b030a08130e0606030408071e06060611010c0206180708010203090d090e090c09070c050a12020706020705 77
    0x107200d058105189201c01403205110125084001d26082010a03403d10b05818078040343e481407141102c460013100b0004503400d000d0b00b00002540d4040d0754245c2424540300500000b0720528072950800000500006600b0300200025881262a02c00110f0141403001700c8920744245840b548401c0d07002282010340010000802c5075100a482002060501e500701401005013039a65240b40c250040b00f120005002d00d01000708040310742c200b03e051000303541d000d0024001d10191100e0f680301c40200b01013008640b0100c09001070300c1c01859240c001c80c011481403000c1142804003250029143d0b00d040117041e820240100504040720f00030311908022032002074461000070321001c1c0c00f8200d190030390118541080002d010301500c0c0d0003150741c0d050040c04155a840450003002c0007a40092001c241ca101c2c12150303900070381074030000f00080d51941c0c0401c0340c880030060015003000144009003000c04c0c0104014080103002c1c1c1c031403004180404800078100b51040c0c00804c1954410041007046488 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 18451580 1250 18450330 18450359
    0x20901050312190908030307080106080106020109020112050603190c030213020f090103091103010603030503101d0403140906030a0207020906031b0607060609020a0503010f060311031f051005180307 87
    0x4100c00f1590381c041500e581a120b202c41d5400002c010300c000720401526640040788c483c107a03407107515050b0490780d031924202d09946210704001d0010b000c9046851400c0d1382c54001a40000008090362012041441c40c104145e82010090b034090350703200010015801c042207801903c0360340b020150b10b08a0350441503142845900f9240b410581c3d076290010031b001c3d0040d800041800d0040081c040a5913900b4002c0144d04140d8079035082510400001a80f405040c060301f90700c0c0f40356140099180e0355600d041e00c03ca0320340f0718403d00580d006c1150302030340d0f035035607000f1445008c0f03501d0300585030700050060210030103000b41414002d40c8032503100800a4940700410701103010844120703641d5185480c040c3d02400c030036405011200c0c000304020b00d030315802101860598030f07070007000d20b5159554001101900c41c07c0d60001682081040401d0054412002c5200000c002d07134401c01d84d0a543d180480d410041a51100001800203c1c5017450b0200222014619120840081c44000d08100b088080d800c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 18452830 1250 18451580 18451597
    0x80d0c09031e0f050118050c0a0e070f0504050a030804030308130503030a0c020c0a12021c0b0604020a050c0708030d1104050f091008010509060105090a151502010f060909020901050312 81
    0x240b400c08030b82005084500c040c600c03a4854021b200e10040300701101d001a1003080211001e002e01e007294500c2d07003819103e85003140c403001c003909030316141c8a07002d40c0d440400c1c00105007000810040802c0300d031128101c80b4001c44c800e404030b5075641d185090040c24410050071244807103a1f140c1d40280406e0001040e29004a1440d074005900281518142d02d400008a00f440e000701180c00300080b400d200901c210300d410300035547c448401034441c0440c03420303403182e401c01818403c410000c208503041c1079002d081460054201603140042c4130306d0580c0382148030340c4802c61a500005024800714902d01a25a48195101189052509000c0091451400701c0e4005000300142c00c00160f03400c01c1e80342c0582c000e20150000b00070038140001c4480c0c9880f000d003d1940150b880401040c01441c09100c0d182c40900070b101c2d108049401d04054030040b152a0800c1002c56403114000c2002040912600c1c0040c0020780340050b450340240305002c42d041050f4002382c0710b40c200c281e00b040131003030080481e054007 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 18454080 1250 18452830 18452873
    0x105042009010903060e06060f030610030303050423100b030309010203120c04241805010f0c020103061d040c05010305070206040803040204020409090308180106050a12060e0a080d0c0903 82
    0x9416401c0100c40d601001c0c0d20141c106400c00c5001d100c54180407078064000c940540b508641041104207065480c2819600070301285a89442000428802d9112941151103a881c03160345c0c1d107000f41c001d40002d1014910099070b400c417110b80500004184203c0c118a08150003650a1040b0400040d40300c0c01446a01040d0109100020303003c107051a0441d8003030a00c0a03801d908103074500c00400c4030f986044050744041219030350486040c9010008201c01c0f80e10507501e2000071112444200c0d041d2160035001c9040c15111074012600d480384800745c0ca0384a01c01c542201440c5440e0904280b407100740e07401107043c18075007010312107071303603030100e0426449508a041c4e640e1b65101c502c08103000740b245a204607144d9281010b0b1000309079201800302d0046070300c0740c8110700718509890128202e46043c45500e80c8606000410007011110070151000c0900804c03001980c404011242402c0c1203140b041190178580000e101d038045442031007540a00e42c42d40c5050b50801e0b0a56807420984010b100508040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 18455330 1250 18454080 18454087
    0x207050a03080d060b0c070e01050402040506042102091302010905060c0309061608030c1c110414060409050c09031e0c04020c01020d0c2102160206161407030b01050420 74
    0x1460100c0d00b128008042e0b038a020781da00c24100000355100d07c0c0e5400ba8240000c13105000081d2072415000751010784400a01d45890146000361111400b8000807018070310741082d1081d0f1004d40d40710b80d100c51003191991000c06208245200042c030102e59500810700c610014080244141d20010580348400c034207803000b907543c540c1b001943d0030305800440002d091220010420440d0350403800981074040051608020b215602e500020543c1c030151600c1103454030910040041208040101e0303107489000d09014505919181d801d402d0703d900b202c80d20020742c00098804800d060410280d00001d4007000024104c040b117200fa2a02c8000e1410075905c56034002c0740780c21002e1420350468100710b0550900300f2600940050240c0000040760801446d4441345a0948080103c0d00032940e60f001c2c003d04008642c2d00b03540c20840c2d282c000440e0070000220940c45880080c0d0340720b943c1030030104410700911200d0300c2c2d860005c2c12254160800ca005509000c00d82c00c1010210903c03111a81d1005480390302c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 18456580 1250 18455330 18455347
    0x6030c080f040f170c0d0e0303120624040f080c01050c060c030a02120702061602010207030210050c0c0601030f021f0816051e0c01060807030b0109090501060b0a0206060901060207050a0308 83
    0x8030a01d501890700c1c541c000207604c0201d0303100245046c1406890303202d00b0f400b6442c03401011303240d000d9210160541088280010707801c0c50040306915207801103202c1ca41000c900544400400d40043e00410a040c1603502d00b400040f50801510b43c280c0800d1a00625001d07000c4229504c03800007400c1084403c0020008c02d04044094055a003203a03040c994210b0f072440c007144001e54849040d01c81136000c105101c4c1c003810443c07041c000c4903402c0b50590003c040c910b110644540007080700514280311003105010b03000301c0c80010b1051500070360003203104030301c2c001841c01042810320b400c5403446c01d4440c51403023050503076820440040d0b00094034201361400b0f803034901099031607204d403410f41c090012062003008401070f9032708040c0c4060301d8410003c00c041510b90714215644c0c800d5000c054004204c4100410503040c058000e250542d2080d0004070396141c0e10b00c0000c250360031000c0f042c40544c0001e800c02c4003604003040d507030307006048610042220924040105503000b2007400081c140f1440001c0340c48 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 18457830 1250 18456580 18456593
    0x2b0303050a0902040f0c0e090705120405030702090106020d030b0a050a1202030c1005070605100509011802040b07030903050606010c02010e040207020a08030d020c070e071d1c080406030c080f040f 86
    0x4844640240050185c03070100300ca0180103110010011022030029583c6c12080c5c01d142283c18840c0040e900c881d4601030140f44842c0e040720006108880a210801032400103890300482a402407945400800303a038095445d001d41134481e0542c0290040e4040882000700b44e40e8503241c0d0741243d40c120346a207210100303170010034200b07010042c160303801c60384080f032000301c182c0e210008000076406204104803548032500c144540700c0c1c0303600c10181d0101c50600103001d001c0203040701c00321001400300c00501d095544c00050701315400445003540400d6034500b041050250502903d64810030900e000b066440b41c030340c000781540200c1810a4010396000c03c0302402c54680030103540292040c4002c498440d005001d103440a036105a5001121f80110000002c840400b01182e074040c0740b80d515085000c41c044d081010440e100f401596500c0441c0742000944078140d4440201040d0140034600d0362035042080280c203072001500740900300030040c41085a00c4009107141c0da0040e070302603041c4e52044118144403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 18459080 1250 18457830 18457841
    0x207080a030903030e01090308061005070b041b030506010602010f0c02010209030709150e0a05040218090d050703090915050301060503070b070b07110f01020301140f010c0b060111100b2b0303050a 86
    0x400f261b61a0241000505070811034084c41603404a540d8607418015040481d051f0040c240b00030212030522000c40d0002e214140282d042c2d00d00d86035403d40c103595039160b10345000d10a81c40040982d6603400c0030417040e0414050b54506991078002503103040f085a000c6503031511b07588501150302c0d98440d50003004411110006005100c040402c1da040e081c10012400103080580b170403031240075401740a001d03081d5003031043d91103000440060306840007240c00962760760380f00e0a011410050803c4003c944e88806202d500040075070403441c002254107000c141030840b40c1c00c0d0090740c0b0a501804041000310316400c121803000d5031001052413680c95805050314083c86031a400aa98000e05100c66816401580a14102e6101e6103524545805810a21a4002032880810700054246003214049401c03000140d030090010b1609400c10140c03c1c1807142048601481380003100d0b140c10302ca145916182c0714050030b01c11016a480c90260046001c00c00c1242c02d032000030705054403070001134024812031b40301 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 18460330 1250 18459080 18459101
    0x80309010f0216060201060e010801050402100f0e0a0803030603010509011104030602090402072a0504020406121505090c070606080102160b0703060506040321020f0c12120f040f08010207080a03090303 88
    0x2c400c0000d40b98807019007e01118018064512a12000001c10703d00500911f8000d0390090000ca104604004085451824505418040c0b0110346089005511442d210788005c102900196842e410040300301401e50b40701910550b026810300071640a1004088200c408495101000603540c06800000c50b000c3d00a10001a00001c0f0b00b04000c8100110ac10380904190340178030040c0e0b9041e8a5804003c102d0085003d0710000880092050004400d503500c030740030340c09000941d42c503209d0b0340310700281c01c2203002c6075008900240450003500308040e034041d2502801c41c9c14025400c4c2501c2e0004080060042c01c005448000c0d41f00c00b06010501a502c9070010303000203412180e0340d07500c80c00c00c4031440501400034503480400c2c0b85410051440815540216154134014100c8400140c08010024030310f41c00c42050b40c043e50900c10f1040d8445002090441050180c1540392490300500340c0e001c000c243e002a52a034010881e01001908510445891480d6030400007140d0205080407002404103104 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 18461580 1250 18460330 18460363
    0x105130e010501060306050a0f060c1e020d050309010905010306080a0204021c09050a0317060112020309010209040e0705040b010203040f150c051b030d0311030c0304050a0c0f0519080309010f02 85
    0x402c0482c5c0c1038204001707443c4140e425852642d946d002410001102d0310803000000d01030110507002803000f80b5107000d13659618040c80004480c41c1c000820b083c0d80d80350300321240d50000405180550b00700e8100401003600b4201042450710340034106485032a80078000f4130840d8000740c01550f14040518442c88104201c20402c412255450b241d9a21130440106401180030002000402070449a09510400c41a502c00e4002c0420441c0356010390400f4003254510354080c0f02d9001140c442c1c2c81500c00404070301d401401c89502d401d080c00110750350518000d0441d001000148255010808200200e030600031122031100e03000d20b4122541c0000c120000c044d401840d48000400f4411039118194280031001c0da684192201400d03001c035507040004259203c01440041c3c1c41c00d1200d070295910600410944006006655a44d13242d2505034010401100501c0d00c24050390404003a2040308404101c12104030906140c0a9660b901410804504002d504080329407624030900144112511031003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 18462830 1250 18461580 18461591
    0xa0206210705070302010609020f0711040f0c030203010e0105010206010b12090c0901030609050606092208090d050f06060405100509060112060609050306100302010903080a030b0a0e01080607080f0105130e01 91
    0x220000c0940e8440d0f00150300560810303001240c200094400c42d1000f401183c10589820520b030380e690740180f0501c100a901c543d8680c42c2036100d122600400c1c00c28140b5071380041c2e80c1d60414614880c0c85030103070030143c1150312100042c4000301080c4101c50458094855000b9983c0d15100d40911341254012610307000f802c030100020400030b40750020100548a401074401c966101c40511007408421a082e0401312954000d500e084004041c41b241d4482c003601105190030b0240b0042001c04074441c90031281c69100307202c900906001807009a400c0842107034144110304109980c1c02125600e0b010303603446040d00c10040f8580c0d038000c0000c417112100402043c0005552520043d141c94054841c03a8004d007e01000114056288401401030701c0d4140c50b0801aa07046460b140615044628500141560341090306034940e1540d5180000f44250200600d01d581400b102504004015004106005500c03003400301c40c00500c0081e0341561000d40c1c958201c400710810080140c084940160760a5103000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 18464080 1250 18462830 18462841
    0x204020706020903012405060a090506040b0a0207290d0b090a021b06010b040e18030c030306010e09040203060a0e01180c06020c0105070b06040b01030e1903030b040e0a020621 77
    0x7500075080c83c003c128000c114800042603042c0201904d040760076005d5507940014009803078820050000f480c0b4a1074895000707a11784001ca011940640c00602a56401203540030020343c1c1007100703801400c0b0418400744220200c00ca10307610407400140307070080d8000100c0c20080e00e04003948110400280204112020300340458060000d62000b40d00003c50b5005442c59103581000050403070484142c0c6106600e4103150959120180c1b00c06030100b4103000602191000010341000035000000704400a1980c900b8000005030092284004450155580724100310140e54049180390f8048040c600204150306038a01e103c0c018a00c60b140030203041140101c040074044039003050070580d0110b4084844405005005403024040c0e400014102c0d800701c00004d42e035040940141352001410306010800c030164000c55410304240003981150355031203007007540905615008142030a0300540d41000608a5004d11035141c100a071000782c0281300008146011111101001030400c110306840c1e20300e0b040a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 18465330 1250 18464080 18464093
    0x61e12210306050910030f0609031103030403080f0f1e0601020102040b04170f03131203020319081506160f0206040906030309030b160c020f0109090507050a09090e030f07060902040207 81
    0x40c01010b0155030079100103402170840340608030aa0b40c200c6184940c5011590390310700a051048011010015455000c40c0800c8013000514000e0340b290700c0325000d5203806a00140d040e5002013050010b09038071028880366070001540b646a01c034040c00600216039480d40180e0191007281c2c040700c0740610000b400111032071015050315243c95410195444030303140303005c066541d0107494a01103148481b080100000080d0310410004188a80150780c1400e092240030305012400c4a11080401d101c0030030171000c13120640c0600c015000803240d5078241160f90040c21011110f109008040c0c0c500c4400d00015552203000b41c4004080400061080545a10340181981028401128424004408a240880c1c0190380041c80d144c15540c8201d088215000c0040900000d50100d06000c1c407144003280740241405241e2003001390f40c40316075550380d05480041168146a0100da8168034184001c0801d11001c4101c4018082219400d51144072505040c0c00800e00101c0080d440b074400584c50042025 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 18466580 1250 18465330 18465341
    0x40311061501090503010b060316090509070302040305010c020f0615060408160e010f051008060f03010501080d0e01090e0a050403021207032c150a05090d1401061e122103 75
    0x203a8410820940e00d130103250994596601850f0310000600005804040d03588101d105202685428400a551200815014002901c69400081e000030302401401000d0041d41c400112900c0100804030b07202c1d10f060f4a441e0040c0130001c6940d014002c054040e42c506058030041c016140c01e64078101c20320007810030030f40084d02c1600c0e40401920000281c0d000b107104c041e002c54101600c50404000040d01c03c40f00f021005040300e030300420200f2a421507031801d1103114041e000b10b070000d040381d42400b00040c0010789039010030b40c10411007400502081009240058200c1d04240021855440300e25090342482e02269614900c1d280208405040c140d0085106a1800d019a00c0c8060014540b0b00b043c210302c14415115000603078400c0e6410300c8048240100302c00121480c141c0d0500c110400010801c2410b100c007a00e0740c000f1000011004a401e100d41002403046811b01c00d0b19001d002143c00c03103041144924646107141072000b00a00c048410008104a05210040741d80388141001600a25 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 18467830 1250 18466580 18466621
    0xe0d231002040305061003120f03022703120708040e04140a05010219050403021008040c120f0506100303090e0403050706020d0504110907120203090304050603010e090607030902060d0504031106 85
    0x102d41740100b0740c180d0749100c0070740641c2d13005071140541c040e038190251341c59807061300d0765010986c0c20442c00340303080050b024071024090f21840040d40441d030078080516200301990600f4841c0400c21011000074484d00448003101c5c0391502a04146d592405d0007000c1500ca400f4480d440c3c0034161003001088010750040c4000e16500f4000c10b1480c5082000312585d004902000303401c0b100c0c0b010207140e2140034100301e40c0c2c0640328500b41d21829450300600108400c0c1d505c1c0032034201011800000c1081024021541d00c806136011015880c1d245803070042c0070304014841c80101100420200d010b251007a0b08880c10a0380110b000e660b104140c2c483e007402450101c0c0d09481c130400e030f140c40454900e0049440350040341140d58400300f500904a0f224000e5102902005191104000c002240c0e00c4890240d8000c0040c0021202c0340d2130300c0c072403490030a44024490381c10946480181e60040c1c0e60790060300c01d0b902c440c1d800041d0f15a55490150f50740c1440c9840c1ca00d00d0b2145004000d108007001c401c00c5500e5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 18469080 1250 18467830 18467833
    0x51006020607050306012106090c090e0606030906160216030c0602150f010b0f16030503040213020406050a0507030509030109050c0102011409060406110d0203100509070e0d231002040305 82
    0x681e0340b40022100c034001a21a9800100c2c0807964421440114058864813090142e000514a54400c080d60031201605510300110b40a090208038034180c0404440c4d004000f030300e130649545003e0001f1600c41c0f10040a0303c090940c1d00341c030745108920804c406490420030248009400d9145d040c030004018040c459007005200d09600342d18140c403522503950007000c0c800c4050620fa42404841d5130240c024284901190304140a0f000030680c1002e00c00e52014000d44540b070350ba003002d005012120391309980e903540e89401000f08000c100c2d809011144580d58900e031858407a070311468115007a00c10000595032641c00d1554240078003401241001017844240c0003040740c2100c0018901003d0301c200c401e880702e42c01480019002c034215070422803d19080100b482d00c3c244400710141d08a81050b1135404004965803005d10190400000407500300b4200e0501040504c0c410b40000e108194540d002031000042111800021282040540e001003c0c501a00e82c85004809800001d411600c800d8a45 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 18470330 1250 18469080 18469093
    0xc06160b01030b1005041b1d061218070605040501030f0923010510030203070314070b0d202502060405030a060905070e070206010e100e070e030c0130020d05100602 72
    0x171481c140c030404800760003240c0c09040c40301241105403001c4c142504016180c50f41e18400400f13503601d10b00101401c8503a240b00c05030b00c1c14404980d0b222420003001c00d2176203138003105c1e050025903040416103003158070034a804142642406490805050b001e480144810401c00000320f18064084c402886816080d00801069a03042c0c1400000400c03444044c0d050342005600740041810b0061000001160500b01c0d9841e075680e985100041c0d00006800c0c12840e0342e0000748240191b01111310815100214007903052803552440c1e69901d0b8050030b10384503041840803a43d41191201c3c0141d0340100801070640b90101079900700310010b4020042e0449150003841f00c04203560346880b1132f071070041c406540105141d07820a108100c00e042d0160130094140504080090308031140b040c80e6228020a81d03d409204142d041414070b803c442d0394a050500010142001580304082c002c0f02c254802a03080c01080d409002100f070007481034101404002d418541000791843c02c01100d5003c50341994200c602 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 18471580 1250 18470330 18470339
    0x60309020906040b0a0303080604020f04060206070207080703121211031509010504090309030201080c0702030109030f0f090602190f050303010902070c0608090c100e100f020c010905030c06160b01030b10 89
    0x2104c4281e070240b648400b03d5501403000c603105612696001c000500018507008102c00310944941242d488540182c0c00041041040b66040c03001d240103103403210041201c14110f40c0c13129840e8103001200420400c0c0d443c160034107007550750081145c000031282d0300c80d641d003003e1a07446c0d401500c0c00c4409000d484c20310000602400c0c680b0880300500c0c0c06540380400c00d811035004484c00369024080c1d0f02512820700c030b1207000d69020704c80d0101c00c0c1d100303498405082e0100a80a03060024805400b82401f200140070040710b074020401100080c000008590400954905003040e034802c1035026015100c08000401c11080c6ca40c0204956406251801c004c19a50342c401c8070366003400c6a030a05640c1100142888505002d80c1c19120010310303050815154514801050815100004800c0018011401141c0d144d4050028038030f048020b10340b6040d4141001e000c07a80da452446040340c00fa441c0014500803540d05420f041c2c004039440882e811203075a4070700300120486410340d0707200380c42e4a07004e02c00075 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 18472830 1250 18471580 18471589
    0x280207050d110103090f0b07050a030b031615050409050903030109060806090d260f04031d0901031b0b0d06080127020d02030c0409150e03070305040b22060309020906 73
    0x3640d03a4040b52403507a011082004401801541400321a60203a0500820004001481035442001d543d038a0f103884041c1600000c0a43e0b1100d080e141c000e800c0f0016540c10040c828400f031b001c2d2a480c56869082e0481d200040f2810b10596214510315454441448100040400114100e070303002c3c0018040c1a448110303180c1c84110940d891100b0b41d22051160000d64000c40d40341c841149195040340301c111922a14004000040b94104603241d180400c2204140d040342124209a0405548000c8021350380c01140058906000190809121056032000701c419048403d001c0d120030488a034440c1c4107204284041c0c20140101c2415500b032810070020700449101080c0e0000100c40c3d82d264810241d0240300700d0074406003050740c06000b400d9a9000c0f0391078a015410046108002c000c920850703c031174a0040f19601e010882460f00300300040c1c40443d60100942d8103480c0d0304001c10340c0d40c890645a0b050141048034041c0c2c0c8447d07100340001290341d0140e110030020703030013030343d401055035604010003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 18474080 1250 18472830 18472849
    0x605030106091505120103260405030316050c0d050d08010e130609060b060a0c05010e0606010512071707050a20070b070c09180c0801020c030301030b06030328020705 73
    0x4001030415000b0803840c0220303407100303040f00d8040c10100e2520411a04072141c211098105035100f0350b070004102101180400400f000e00801c0f50400e0038642800d0009490b4400c4503040d0341111a0410248280003090001040b521b2004018000784046450400c0d00c41081184203404140d03041e00000f181c1c0c80619006101e084da02107c91695030755a904c403c01400001c1055801f1079880d0a4180700c3e4a50000400c3c5444107500c90b06513804d5035103030007429643d41262040080c1c0180042c041640d0b041825035401051321411800b0943d21500200d41039000c40300c00003121021617041c032500f550440010103080025030744040300d104806400d600b42008480d0f15005503400f4041c20880c8850610280c00080d00c1255540c0c400d5642e21803003810b413101a4105c2000c10080460841040392036040b480042c98000d000f9804d20159441c1141c482c04140310281c660505100098050b41d011b01c21651030303641c414080d030054000c1c048620903206400e09207002600c108100070800e4138169106 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 18475330 1250 18474080 18474089
    0x1203020d0e030a0f150609060f050102010b0a0303030519141e06010e211204080105010f0e060411070503031602061003080f091f0201020c060a0207050c10050d0207030c0c06050301 79
    0x1070620f152250340d41007003c41c0031481940c030072000300d680580c941014000e5200420341400042261824031b50b484031408402d62003a03055a140c02c0700340e1000d489156070481101e8050400141c541d4a1b880c048859406000c80041d0311484c080c4007000d000701c42d007502806102501201130000f43c25000e2007a110f5001e84200e03011802c0700f00580c0303080c5024580c030b085001c001617908a00005002d0b44919208103403070020315010020605002002e070900c17400d0700403d0800c1000f14100c0c90551002e41e0403002074445405035448100d00c2a0111110003102c920701c1e03200003200c1d524a0a0f10070700100c4031017070b102c450060054002140b00348410a0301c8005494211030540e29081201681d0a030a51110041c1d42c0c0082185080d40c0400e03500700700e9000f030102da0790000740c0d4603a20b40c0c1c0c010b81041c40c02854003c800e413041c4620400b00d070340000d6050f15032500352202503c40c0034a071000c0d038140c0603030300c03000c15942c0c0001012020103a00c45800440d0360b10412424000030b858100954590009014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 18476580 1250 18475330 18475333
    0x204030b16051b0f0d0c050f010c050f0901030216030305061e03030d02031e01060c0507060206010315020c120f0703080a0932010606030c11010c0e0103020f090306011203020d0e03 79
    0x75041c0e070f040a502c88010320308180b5040700c1018883c10b80f810306143c4c0c119000800f0583e90714001c402d00000f4400e511560781c0742c8008220710f1400c0507000c0e10368002c81409803000d001c0802c00c0d224607402981121100420740e1554207008000c1c1c50028044c0c40112640d5000306895640030b514034201018502c030f01080100514285014802820000d410062042d21540c1d20310032135949070500307862007a02030540c0d69102510209541004c034505400b0741d20100455100200400100b060481e4181681001840c0540d8903200c000d2a28904801c50958100d80e200024003454807407100402040518030a8562107000d81c1d98191075030403242d00c8a0080d15032030072400600d240d42144503002207540110600340541c0c441040c1c0c82400c4488641101c004a680ea070483d0300c8013504030403126100000c42c1c00074002c140e1010001005154004031050605401140d43d0100e5200e01040e902d03590009012141c103581d480340b0741c600c1c2d08a00b54040d005800f500f110381000c00c4c071400d284140c1610140 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 18477830 1250 18476580 18476587
    0x306020325020d0203180402070b010305010c020d0c02060901050a050d0608100b03120f070c080f01020702040b060a020d050901020111120708100b070f0206090d03030b1315120206070807060204030b1605 89
    0xc0d000e40c141b0f41b41155100b642044424001802140240e002e540030300000101810003c201a00d45001c125004003030101c8040c070b800050351184222606d801c03003032030055140c0040080958040c080c05441180150500d03001180b400d1000a120200c070b41f0502040c40881c1500003410f4884030741d000890510241003103042c180800038001054554840c9540d4140382c0da55a1040e428404586080806a500010000c056180c5801034120740c40003201c1c0c144c6052035111019585d9019070082c00148580071607084c81c1a030007035003c2c00581d4030300e002c03107540c0300c4090485c0001c00200300c0d001e00101c0c0b1003201054100c0d4421295600395070111111915015807910383c0c2903900e10f0246c089070304c20010014186152200d0f12070041081c42601c010809000d124108525041c20b1030407889060302d8003007201204001c0c250104111380e1012140b800740400c90001c10034602c44c050015002c210f000603840c0401c00d5590062003146c1c050381c0d0040c100e8542d42d035070500c540d203880d2900c4001101032 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 18479080 1250 18477830 18477847
    0x6091805120a02191a0112060506040605060313051e010608010c0c0203071e0f0909020a060206060102030703030510090c0203030f060a0303090b03070e03060702030c010e0604020102250306020325020d0203 90
    0x1c240403032090044890068404104d0b1602c0170803002600000e0782000c81580c43c03c100241d074001c1c6c1c1d8001341c0480d0140a0030b4103200114549002c01411000102e4051100006100040c0300203212640140f1900c0c40700c22511900702e0107898a03208a0b03043d03618140104480d54840c4043c0d5100d180c2c0240545811480c0640302e89110180c1000890b00c480a1800045c80549071500c40c401412400000700d40b00c1203a0041100d054459030058065421444c20003416a82c0441102d840503072600b800280c1d62121600407607282441c1d0000e00404e86001c0300014002d80001c080c0d4451521524103480681e511028801c02c2c000f103103c001c0c0403c03003078041070054031054406540c3c007180e540380c1150410050340000313180038810388032000540c03c00600c0b145416020f01481e0700c83c4050b0001040705007440d0780000c0d943c9400004c0141ca0701084060002c0c12030750242e41c00011500464155100d0401c10701c0440b0b210001c0e001c0b80006001200012001c1d800441c0c00d4041e040d07070790065403c20206 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 18480330 1250 18479080 18479113
    0xa09080306010c030e0604090b0909010507140706060302030f01060e1506030103031101020d06090203012105070b0c030c01140f06100806100c0b010909030e03150403030b0406091805120a02 83
    0x140e0b402103017807140a21170040f5944510001c0d10052110410101d02c104030201440a81c86000c0c04141140e4108800c108240744c0200305000b40b08101200203075500f401d030803c03800900396070304001d503d070182182d45485910150046010345501d84c107009281e440d48003030380c02c0c1c514901503007035003110080c401040800d01403d01501c2d030810090016151020b02100e0380202c03204e942041c2c200c03633808001030107403885002161540341040034032403810b01c4154442e00d6640c01c2034030a409030f4050000310904421010700c00e5440281d10000240f0821203125260000390008844615000c9000d600160349031400a0700480f222aa0340c8403400c69880342e405200304002110019818409822700761030004801d080701038020268441300041140745481c00412283d018042144640e000e02c2c0340341c400803801c6880d590030a07414280090030600540201e009401141c1c0407103001454a42d100021940207000e10788200e20800940d41429825509002c15000f007034042001640700045c01c2c3d089054 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 18481580 1250 18480330 18480347
    0x150207030308130f050a06051510120b180f150d030e101e0e03010501050f01050d1e020705010f0b010302040f0302060f070b161206030206032205010203130b0a0908030601 75
    0x500d0b0180c03090902e5103ca03444d0081b0308404482c82940c1d00104000500919803205600108840c04004109800001014031101400c1e0710303d5107a0f42d40d1004180c2c0e88180480c003090109240c49505485c1c88041074072589000c543d00d041004c0d64221028842c82c000c5d101364a0664141c607040700900c512020301c0500008981c800040c00344500c01c00080c18555020024002c0407543ca100c0b0601c130070307010b040c255403043e031010307000d034450716401203da0ba0003800f81c500e41504d00400080c010000d03a43c03410740c0d00c084101648514400580001449410b4000107043e01003610248102c0d0100740046080b0720031441501030441e440c1e40c2c1440103290500041090150305802e03903043c00b5581d110360030015420748000c05500310483c000f880c0703035030012107050a01110410812113640396802003a91440000e0003e04424408141041206001100495004d80041c001c41d10780c03510030781181c0600003040d02a10f6403044000003c24840b600e00a030b41016a002070040c0c11a120320005640f51207 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 18482830 1250 18481580 18481583
    0xc07050a0215090103060b03091507052205011808030904230108060405060a0603050309010509040e010905010b0a0e010305070311010504030f03090306050a020309060c0c01060902030a0615020703030813 89
    0x140844503000741e50b03500142c45107149003240300c80d070303e402c11030000d0200c40d1158050782925500384200b00e4030030310100f40300d5454011460440903640d90074070105e46500c180c01513200380040d5460b23581602842017600c00d05840080e211100403c5000042c500c6040f950303c14541258000c0000029905060308030040300c2030709100b0101103084402c1c424600203c00d030003512995120004000a101003044a20b400060858003088a00c0c03c43d1100394480c400c40a04606101c8005504280780d105e59020008402030302c4020885540a407510502801103072164910034000da00c0085003440c12001c0f140e040313035481310092810520319503a2a0316031030240b5580307051040034040000401c500c1c07101d484c03102d846982c8604403907003149044421540098500b0480c80d2050041100000b0300050a64200f00c4035280b41d0b441c0c0e600303042d115016110f00e8002c040c0241c000b00a120300c0c00340c581c001d42c0546400785075a1300d06c0e0070f06190480e611030f03440c40b02400060b200700101300038013903400c4071010760b9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 18484080 1250 18482830 18482833
    0x813020f0d080d0903021e0d030b01050405120106090605040b03060f0c070b040308070201050708060d02090405070f0608091005040c0905041109011d07020c0d140c0405040302030d1103040b0c0705 86
    0x35094031907a0b003075004815920125030315070003803500305035041c00861a4403810450103e0b0030b060301041103540d625503008580515075102180700f4560702500a6800814004120300c40040340741207064007070b000d61310906040340d00b80b500100d8030349001c0c0610440780201400070542a510501c45410103c1c02a0041c2c03100b40d41003018501090020040f18812406619042c03041e040900c4024219031005080c0c104001001052000699504040551003501200c034401651543c0c20041d040c18410780c45170401a1807448005016504480010b105194a07070a03203402c404201400820b6540440d4000c00c00c109028040c00340450030750007a83c106004200d0075441c0450b0f040400d41281082c0c0009107401a150b45680e032454060b03011540c8444148040d040c2d200e032110104031282c00d0140001c141401e00319083c00011410003070345104d0240104103000c54100b6080203900c0f540100c0c00f1895940c14184001c402070494400c69024551080341010103644141c001207190300003540840f4036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 18485330 1250 18484080 18484099
    0x50a06030206070302060906011d0f04020310020a0f090e010602060f04030c020307090614040e1009061503030c0b0108010e0303152403100905010302091501110708010204150813020f 80
    0x150b1965000303000315074420380007002c2c01c1c1008901e42c1d10b00702c016400f00000390140910340704208a5070203820b4016004103a0003015440d9480061300b03005201e01d40b001014404503100d008075038001108070700c559480d01d50101554a80301c10114000090040c00f015030300100116000e4103140c0269070307000c1e000f031404521070f141e6603000a041150310307481600f0107902c030a001e11400f481460a00324240048400f00007002c2081c003c651035003681c0d03c20440d12665940d2400500405400440603410360f68109000e045e22071501070005118a40240c420b503000d00004220031b14144505141c80030134000450541c1d480d0b07912171300c541c201c0b541d520340c110100c074200c078a40c010303495072940e464040c44d00195200c0c41e01c00d481c41c5240c07032140c1c0a00704144c01c04004201589a00755810382081040074094007404409006881e0004800d84003011486010030010f000b040641c05003003075805400f20544010085201160420016600708000300c800d0f00403540146090110740d40d030901d0141c8001003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 18486580 1250 18485330 18485333
    0x609071211030a0b0409020108041704050a030b0114010503010321120e0a02100c150f0b22050610020c01080a06090e15090a03080406020c0c040e0c030c090702030d050a0603 76
    0x2503400c4101040100c0c0c5000c818400c8040f054080d042060030142c4003080384da002d40c0c0008280103001b800141c14190880c1000c14190780007011540680000fa01090207030380e4a00e0468055a000d112307100a00312040010750f02903202c3da040383e040303941110032419181843c000f100f01e0040c041c0310715402e20400c104000054441802046404499a800740000341024014080010782c940607800400440c0c009860002c1c031051003401d807640039240c0006900c0348000c0640300500380360f008079504c0140c42c521113500c0d80081d10081c615042007001809076407651010320405ca5544504500980c0082e1144039141d440b0340045a44152040c50109040b6603078200007003220a5284552500d07003101500c0c0c074010100021194005c4844001001540740c00d4900902e15600138000a100c40d0b0002500d4036030040801824031400f030010810494114901742c16643d038501c9071411402801241420b01035450709100c42807254110750080c40c0303007800501c641d80040c00c000b0841011343d540c5100110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 18487830 1250 18486580 18486617
    0x203071406070c170705040c02100510050405090a0c080c0604060e0f090106020f150709031e02030303011701140405100b0111030a05030f010906060c03050a0201021b240609060907 79
    0x42c40800b122880146a1320380480c2014801d03042a40128100044c50381d40c0303540020710b29140780800d60005110b072140401081002c003e98400707a441824502030000300c1c00c0114498241601c25080a00040d50311282d240c3c807001d02c4010302d0342c810700078003007088210700541d8182109540100100380b84921640040c0c910502a0440c000681c0a281000180c1c02c0c2007024140f00441185259191b00c1c080c03d00a10080440c003004043c000d0b80340030801d8a03210344150303507242540103040da03480c3d42c3c640007114103100c00040804110b40c01d04004110f00300307000414074001e541200103840c450748414041303400b030103040042e00c2c1041840c10340941c96000c144040e00b00c402040e0b88143c0d590400180d90314183d031041c2c1012010614142d0100b2a007504043c2400d041c03541410583d40300c4003024016030090103100741d00c440e15594540548290180443e41c600b0f9801c000b80715642e015410b41110400020031144035402c02005804680945080b45103954041340616002808801100c01d14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 18489080 1250 18487830 18487853
    0x402040f090309150c0b130f080a0513140108061207090203011202010206060a0b04030b0c041502010e10020f0409090519050a0302010c0c03020303070f1b05061e04020307140607 78
    0x540000e0a10102889134503600d541c50340b2014a24500001c890007280c45000c02044040c0450758442c6d00e02d0584410085807110581240d9000340c1e4841d154a0721000250260380040e20038500d2130356001001c150404901c0940942c08010b03521076000d40c0d142c2c8280103100c842155413600c24451010002011984e40c0000c6010300004c1041c4003148159200280c54210090440d40c443c50304c600c0b0500c92240f1410a403001c613a0445800c02d010b45445100409a1180383c010030354510200c0b4044181940541010301c0c1d0512500840e12044e88400d400c500300e024020401c0c61507403003040108080140b680100800b0341c000c406460000c04030000c80011810159811505a00002c4094050503020311412100005a0a103107448516540e0000c0d03c6c4e100041155062010412510704035603c2000c008001a0303032603c8d802c2d401c01003802d100d55114401c486807a0003000000035100340c8281418030901880d8090300078160700341807044660480b1a4103060513009030301400f02001049516151 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 18490330 1250 18489080 18489083
    0xc0a030c020124050f060307140306060d0c02030304020a09060f0302040f020c030a081e0c12040f140f0f0304031a091603080a020f010b01020601050f01120504030302090108070c0201020c0105030402040f09 90
    0x54035030380c44c1a060042c1d2013202c20010784540d0080c0204242d050308010705003d4290f40910481e0350703a650100080c0c040c010101c00403031300c0c3e160154118240350000010350141b402100c01c02d14040e941d94003e803d949250142e5540340c00f01c1e20b010030050411390020880311001100150501c1020441c036440c50b0800c0f543c200c0002e00f24410302038030344494601c17801070b400002010f0901c1c3c6800200e64880340b094101100d185080c01c00080c007848010711002080950002100110420781c006030f681d5072036050b00c0c0408034014070280c204180760010441e0212980090248114021803009070080c54008214072514020303100c01d100140e00303017000480a1803140c2780d40c644038a1600320082c079041511b0740c0240d803a850f1011440607030ba000240141100d004880d0060340340000c0d03004071241d400305071600d0a01382c106400d00c403c041d0190042c003600a0280da41030b00d0356035014811103024103040300282c0035800547d110406940700f00000c503413150020b000861a05c40b1214450200d074542c01c0d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 18491580 1250 18490330 18490391
    0xf03060918020a1202010503040305090607050709020c0708190b0405030408010c020d120209090a0b04020702060d060504050609160311090d030c0c050103090c0b0a0e031c020705090c0a030c0201 85
    0x200744045141035003441d400382010f921240c15201c0d00ba40043c0103444090000341c1444400f103061717407460b912081101e49840d4030400390760b080b65581d40b404002c0d400200302440c0c0c90084120115041d88000381c5d40402c8600c0070203400c004140c40e100c0602181011308141c3d518041000042120f800901644407141210341c005c240c05804150018901c000100710f007140b481c0100003407451a42e0b41c0c5640e40d0062030140001600000d88000034000b072141e540c0003904440301150382c00380d00140c0e60100040700c50a8405101d540c0d103110400003044400c03620032020041d0500e100601621035400220309014213050070b8900005180000d4070180d02c0402140020154441d60301004011943c050003400282024005c1c07003903079a21200c54182c5400388420706100480c40e0324100e0711820601c8075415000e02a1416500211892004540750302c07250405807146440000c2da90903c4058144906140500181456010b400480103418a205100119074860340c200b980030705600440590310f800b098 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 18492830 1250 18491580 18491621
    0x807080607090f06080613021309060513050108060a0b01140706020a020f060105010c1104060506040305032805180a05040c03020409060906050105030c030c0c0a0b0702011a030d0f030609 82
    0x180c014078038855500180c1c0402c0643c00104031440c0c22a0083e40c1221003214990085101c00c00d07000028003480360803981c505461500040e00480550200d000da0b0015580c9028080900807018281d40c828401d60386181d01420014000340f50340c4c1d10440300d032101494030070360101c0801e51a406603000007200f42e0701c0607030004400c0e02c0c068040000550300810322000d0011507250900103002e540e403500340686818580700000d2070641e20795226001412004158540721b640b68140107a07240c0020714036090440341e030342514505018951440c43d481c2031543e81c0794030b402c1e000c1c25001404502c0904064000100c05e001081d59500d80c0a00320343d6075610f6400503116454001620b059a500b6448400300307a162100902071703664894212035112024141c00d6031b482e22656400c54091184a4646020307018410300801042080f00c60140246d65a81c000d0165030382c469460010400c203524240d5250f882002444007a50050700e13845118036841c2000a003090b41c44031044281e94440420318011003040c1e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 18494080 1250 18492830 18492841
    0x5031204210201091203200a020a02011b150b010309050d05130b03100b0c030f040605030601120e07050f03150f0103050d05040803040509040c121a0a0e060a0e010608070806 76
    0x304446101c072200c0344001c2c0080d42e4107031208032a2110f003e450404150700c0300500301c628086524000111340c0b119208070760716001c1e50030007501c0d0402e00004a0000d507800782c000c460721051030340341030000750054140d050420f13540c1007010080c1002410035052586034441100030a4091040892040250b01c4582c2c0e505194040c660520400d500b01d401007010070f0052002211000c10720300b0a03101262a0103998001000c076036886e601a41c2c02011303414100150106806902101440c01814280c0b11001d10140002c0100c2c11303200c1040810b03580c0c0d480164104520718010701c00100c5e02e640603040d03c84010742e0150003221042d0499043c040300c40380c40010401c00000300084452040c0a25000741003030b0500c1c400769100d03c42e134890a449821000045014010005601001081c2407411545148164a44103080246842000402e9a2140700042c0581c0c264040c6101c5950071201400b050742d0351000450080c0038500c11054950360342c3d10080b4401004100758806400c04034010324051070076 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 18495330 1250 18494080 18494123
    0x603060105040908070f0c08060406020d0c05030c0d09080d2409020703080a0e030f0c010c0806040b0d03120608060c04030501320604090816020a080105040506040f05031204 76
    0x680c0020b0003a071900d4110004039401c02c0c10384c1c098a0380403140324030301001418104c2d4881780343d030803a000a0190805000401403194003c240c51607071004140010161044165503d00040341c826808540800100e400002e040e400b10000c148a0480d030742c100b0211001c640101d41d41008540c0500301001c0041c2c420000e10300b0710318010f1000c10015480c0c000b072a50001d10310343d005006a50280e8a030342e081000b0711410302c2690f213a204170303208036034885d041004014081c0000030b403045e01180c0d84001107952410130380201c14800718040c0007960b1021255404071107007809107c202d06169a00c0d1030104501c80140a10342c000e0092003501d030348403811800e005003101c0090740d0f0403401b5000030620a0b00b03d035600c0050719406413a032504801603640c43d000b0901901207400d0061104100040480700b403044c040c10712400b1402501c0b5440741c56250b0128a01300c40382603402a100768400800600062107180c0400740322403207038059034240049200700c012a1a0261021a1400310300d10460940209 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 18496580 1250 18495330 18495343
    0x20103020d150f0f0b130e07140d060509090604120e010207120302070305070b090907080403031b020601080d08010308030606090310050c0a031a09010506030709080a0807030906052b090203150603 86
    0x2401148601d06040ca141e180e408400900c20340c00200c0c8040c2c00a20449d004440901c030400c40d00b510266106546503071a0000c09080c010117109440100100344416400140d0f50302c03a0b40e01206800d402e44252070309660310f40c40d41001504511551001184161085284c0f640c1244242c00500c002811481c08030309002d899045030410b94000e022140f070313907541c581c601ca40201d81820800d5658581d0300301100500a03418119a84040304000d05242d61750019a450494007035405561400200e10f00440d114a028417015180440901c0419154903207030000b005034000090854041c14401c00600040e20402c54041b2240c0d0ba010400340d203000d070580150300c600c4400500d5804500402400140165418010300e03018030404800925294060a5000007810484080780e0740c6100714030704840b1540c052030b021400160703c20400101c20340102c00381d46c0451004d01c0010040d00343d1440b07040030728541c02a00c046141e00d0b4031200b00540c4040c4082c1d40b08030a4000000514078196042c9443e100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 18497830 1250 18496580 18496589
    0x30509030304030504050609010c0602070f0506010b09061206010215010b0d0605310f0f020702030c04060608130203030720030c0a060207050f030a0204060e07030b09060904020103020d150f0f 84
    0xc0080003007000099020703084805440d0116a696140c04040004881800001c10024021840000da10b01442580080c2c0030485100300c08a0303e46a0302d44a029880d40079810400350002c4c000c1c010303449a200c0d26440b29a1105062045850303050421045c1e1090301c40a070f0042e41500c600203054908410180507a0000d0b0070165884110368100008603488820b9a80888035010001c40c0448226261900004401c3e0744400042c0b100303981c0400904c1c000d5010103812842031203a030381d401006042500807030381280d80c2c42d1100d01c800d554041003180f07060400792040f6818042041460700107510300076030700c051103040320412407000d903402c0901d468036010542061044011081c00c1000d80d6000880005031841900c003003540a81c0304012030701d0109040c100950203070402da03000c50b060b012556135600c60150345d907040c49142d4228047c4040359505442a0750020341c075000050241d4082d8001b4204d54024450005028150403011440040720f500700041c8014100b000f007205050182801d000780 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 18499080 1250 18497830 18497833
    0x11503030e010503060901090c180803250f0201050304050c0319110406030c06110a020a08160e0c1b0c040e061b031005010c050304080d03090b010b03070c0813080f0706030509 77
    0x6041820004e40205414031a41514680b50320354460214820031802b0480300340100308810b2241ca400c50241c89030400c0564203039000034460040c81c0240c100010504040d0081030f071001008a58004490b11f07840100191420320480074025003540301040a8664160410f500720300000f01d91070450050038491001340c0c4603030b040c40d0060000c03a24000d101e1003101e0a500301400504000c1143c182804c1c0701e40c5029521a070300305c8000614440218000740400003250502450325290007410201110640d072454500c4000d0141540c8100d0285154030415141400c03601203802e2880000c1c02d45a00d0140424141c003c0d000b4416040e4030f103003034141c00d140c510600c28110314001e05009414100ca224280c10000301c1080fa80c1844000d10846001e007060b44182c5480d8411100040c001d003600f21412030f41c84080100000d05843c00c40c1c162400342025582d01c1400c12055111901c95404c540fa116803004503501000590303480800c0340d000103400392000742001302d00d050006001c81e000140043c125 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 18500330 1250 18499080 18499087
    0x17090a0b090c010801091505060301080c0916020c04050a02040b2b0603020319020d0b010806010f050f010210090203070504140a0c0c0215070501150303020309090105040c170c0c011503030e0105 85
    0x2613800c0320205054443d40d000014924020848905084503607a11554114000000201c1c0007000171500101d56042500c103507460791101ca100c0b801d1a004c8551580068021020b190140d1402d078100c240c111150900150506440302d41060003540080100080c0411342441d10b85034051614051940421181c000c0250383d18680119844041d0151100c02545211040908564030005e01d02030641d080129000150b0b1100d40140d0344500c01e000d080c1900740082e900083c1c510b0701d002030440e4183c06901506158440e01c5006005d0000000126818018568007040d02d0701c45202c3c801500c00001050841803c1501c01c1d00101d903141107007081001100d01e074403401340c0c0303a410303482103807402c204640c940e070304010b041c2507006060554401d0040c81d10001c0c00824181d0000141411110842c0d001003143d988008001c07c41e44140454008200da1003245404003c07084c101690088041141d94603103012103448608680e80000f1006030005007007c20310030708d503006001c440c6030031080c24039624 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 18501580 1250 18500330 18500353
    0x60c0a030605060415090e160507021f110f1204050105030402040b0306160e100203040e0915010e0103060e150604110c070b0c101a040504031803030809010b0103020403080d020a17090a0b09 83
    0x8c020f5a0744400c4d000f07018000941404548910415030050080702228440d403050b0030000800821074403000450341c1c070818007007a100500c0428040c5000d148240110b281c18548401540e42e9000280141c0c0c0c8155140258451f58a040c04814841c08101c0b082507400d0428803c05021500e0001105000301070301c21403c1410398000003190f05554501041300b120b5914510305600d80041000c80d61468004076000107106444180780c3c034107072031140b10180455428032210030740d1040c2d40350b10070b81101c0f101008200a4201a8402d90041f941420b000389881c01d0000e205141c610319034400000c00d00b00090031303d5100e0301488981300381005600107003c055000c0242c0001650120111482207503244081342c2014041c514402c1559815215042016030701d0901400e4240100d5a4440075402c0070030180156100c0e100700e506484d80f21210034101401000310900a4000d030489000388121444828061b041c0c1d0f0940354419500c84e8010100c0d080e0525101d10000f1000d080c540340c2d540301c80035100f03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 18502830 1250 18501580 18501601
    0x207050304090917040905010501170405120c250501030606080c03072f010902040e010608031b0304050316090b0406032621060301050c070203060c0a030605060415090e 74
    0x90071902c20000c081248546418100301e22803421020310098800042c00281402c05600800d04803070017620741e01c80c0c00c1b86052601c0340401e01210300420310b8111501c426047c000d03034400381c0180e00801084809900214400c8088034071098010010051030000400040d0390501500b00900014a4040c07002e04004850644500014001000b4045190405075462188220301000c044c45000b51010801082c031444d4001c1c4100c0006a00036410414403030003a071414040c84044848642c021458241403107080650100c0328104003a09000410000606030380810290b1001440d410708400010324050701c501c02c40308a014122b0066080000070408508c8142c2d9444c0000d03550150803003085401c4004031814440c440c286101c0c0403001900c0b40071400092501c0748500d00950080060392121100c0342441c0c040c41d00e001354141c1c801d500180e000399151000e810349100c01d041c0403820075210400603045400580142801c440c203603010400c41079106400ea0028261002400d04605206503001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 18504080 1250 18502830 18502837
    0x406020c030c01021c0311070c060c03031406010c0305030402190e0a06080715030209180112020310050c030403051303080f1809011a09030a02041104061d01020a0f02030f06011806080102070503 85
    0x10404e1566915901c164005410302301d400883d0b201b11280442da803035881c064400382c841d800c10b0780042d280072040040d01d528081240d008d031a05849018102d84641d6040300c0d1035000510807030700440869155207181a20303110b07003009405605000c15140c54100010412254194015983d641c0444000c001c02487c00d11a0240c01c0c080d8900941d50f00c07140c601041400300300850000001d140440006024890075000094240c801c070150ba50070240d0420803001d55000780c400e012080020404140042d006070b0081c42440c076122021407500d962038552001c0c1d600001d4001c40540342c0000c1c0251f500600340c0034407a035842e04654003000d13035061015403032501d003041214074005072002440040c955000c208000b0050f500400500c0000484042c22509400a100f00c03004504c141e03070180007026840e030345a001c0b28810381c0180402c0c0803e40ba100c41e01740841d541a03806000c3d0003a03c164103041407100c10702901e0203140d01c0a00e080480805412618103900400031030b4814440e1000041010044 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 18505330 1250 18504080 18504133
    0x3090d0825020a140714040b03060106050313080301060c0b060102060411120705030106033c0b04030e040c030b0a0501050a0903080a050c070e010302010201050c0f070320030406020c030c0102 84
    0x1d070000300350150000e9240c8030f40110b02400c181841e030146440b06100081a00c2560440300c001d110740d0702034206010a8800600c4010f606401141c014040c0300e103d4405185e010900c200c0002030f800c0b02d929050340b02d61080e00131070700164041444200b44680a024139810060070700c02020140ba150311000b0495a45038481c5d403013407015040b00300c00a0b108004000250500800805c5040d5a81c81e000c806405030f04000046503004644031103101d440018466400707030011240703440c82941940c58400168004104909102c00301403a8031060301c0e2849041e0b0004165200020803540302010409142042c2d40614100901007005002c410340c4103140f0b80c110383d405001e25031208074100041d51180100d041d0302980f4402c90313100280f40c0703460584140c1200d000703030000c02070707a2581000c1703c065204d040b104040403e806c0081a0010744a00b582c000360001421000c05144000301d000380c2954415446040141d00260100e01c041c9000c1c02038101e00402400200010070580003164819a2101c54 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 18506580 1250 18505330 18505381
    0x17100b070b06041506020a020a060206010501051c15090b0a0801020f0f07210203031501031a0f03010605090a0b090604020702030705100207030602040b0c0f0c090a0b060702030a030503090d08 84
    0x40b4086446580040040c00c40501003400c070203483d000c000b9640c40d02e51805034441c1036601070004500c0c0c0081145416200c1c10b941c0c0a01c2c010b8103a501c2401c1200310703034091550700d07503d40085415894a0303580d20f0280000540129214541e03508020f100c8100b074212651592042200d05040005002180d65400550262648440031420030b808070042e41c10180440444040003407014070f0b400b2004500c03a40c405883c44c03004250140045088900540400100400f242620303100c6103090743d01c90308a000c0013000400c2442d2a40c001c2401e81109960086589484039454292840c0c40f40c110303a40a503042e9021400c1c52841d80020380d4407070803880fa060007000002030b006000d910034001680955080b04041d0366965030f450303126116600011034021540541e038000d00307103a20b0101d0380c07403007001000b0515205501c03200040001060001c081c10380c450f01c10070100b801600e0501c03180101501a40b1025100e00e0039021031824042d494600c00208000c88003008681c080006e041890210b0000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 18507830 1250 18506580 18506603
    0x1050f06010c060b0402070809090a1407050708130303020c040c030908040b13030b0c070b150907140c010f02040503070501140d0c03020c0102070f110a0602151308070317100b07 78
    0x4243c4000d10019103801d030040e00001c0c00310b0034441c0100040007507010941d98400c0c0b503510040707118212100030f08180d000744d07205408103003100d210300c003d005990b00840030b441c85c1c0513901641800c070214a40c000c070003607003003041d60842c0c0707103001d100e050003d03825403c00307210322492561403445520603400380c000051804a2074241051b20780300e0641c05194030070940015400c0102c0101c0c16500040811a00802d0090020344d04c2002d046500380c80c21030150400c1c5e56926030038007c1d80c1d411646c0425446628050040325031000d030900034070b40c1d902480704006079140e0409040c58104074031358102e24103100c0c1c0c522040106a416074222070004000300310003d0444581c0800314040c0c803808a9000c0290f0010900d03000340645503203092046880f0702d55252a46c00040140070606035148100c0c00540c00c441c0c0307910b440c800300110030369000c16484180c08500c02c2ea561000b025420040c41a80080c01e140c12001011440050840d04800680e4001107414600503010203940b241c444010582211407 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 18509080 1250 18507830 18507833
    0x7030e07050d0c080a0b04050601050d0206030402040f1e0e0105060604060c0809060412060506130e07090509070b0304030807020c0a030807030e0f04020a030b0906060c0705090c0d0c120e01050f06010c 88
    0x4907043e1024012403419100501c01e1030400000002c010366040e21075002d01c02c0001031602d040e020401c1c600e54043c0103281103a4503038003007000900b01070380704e40074007a112502c218140c0c1180c183c0c6070340b1032008800040d40801c2a40744c2421650010052802801700b040180000c540121860318022790000390265901c0c68040410a24080c07544900c40d001201c440240410440c1d411051050100351a00d51440075000404d03400d4980900360154030340c004010a0181d00d2058110700c0e40300e01004115480300e0f41e03440740190307140d00c1182c042d8001003046060160440d414001c20074508421110400d40701e04580b40c40d171852040c0840182804411617004038561104005c2c121440c1000303204540750300001a0213000b4041c1a48001d00c991107480002e041403070b1110545050b521344c14020700c0b55504001c00c1c13050240000d842c03d00c0c00801032281c4103502c021809900e46502155551030016034103009807505658001d00080301c56410300081140b070441ca40206c0380e100d0400d181032450123815 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 18510330 1250 18509080 18509093
    0x501050f091504060212040606050108070201111b120a02010209030609070302010512060d0204090c050f06070b06040c0203070506040c031118070f03020c010203010905150603070905040218041b0807030e07050d 92
    0x1240e079040e041c6c10f444010041485103540c0090b04960003a21018180e40d5144001c03401c0f191500401d114034542800b60b8526461140c28600301781e554481180c402a45103500c4841507040003c1c0c1c0001070303400080c54142808c2c244400e17030704607101d200240a89400c44c0d0018143c1c1c0616011040c040201200150442e82c642116100e03054000d802040315151500b0b0100c0c03a54158003c260040c4020740164040d818040c1c12210750a4101c00d0780362040c1c48040400014001810b51403085100034408100443d505015490040e0310600300e0f49081891480c19031411200c0c1c4620510400c41e10301501611201c01500319400301d038901c0c1071800c000d000304003603000340108812070b00550b10110000c00c03500202e5104d180107d080300385550520441900300006480110303280300004550707040802440c1843d4010304000320385910341240b0300f030000001c134044414180c1003103403800420074038103e41600003680f180c22800304d1a0074003a081607030740749540e1007401d4840c1c02e001d03052130180780092048 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 18511580 1250 18510330 18510337
    0xe010507031b0b09010b06071a0a02040513140109110304170c0d09050f0f011b021f02010507141918080f0d02070501031b080405010b040204080a0501050f0915040602 73
    0x4656584010b05075403c1c41c1e038846200716600c200662804200340d80764900074054032401c0b0760001940221901e241e240742000980602800c03a144c0c3c0910010a05036100382140800b00c000c4500000e400000b0145040c0000041e03101034502c515207014820100d20071030031a40e0041c3c028000901c4140924070301107891080e500b0540c4940240e0102e0f96905070b10100e41412508100c0b0980358540140701000a80e104007600103010031201c2d0300d28405d1050405220f6980e44c0010901c0f040d800d4001480b1501c0000342c1481801070350b4603003c01401c150030444600c101040ca414803401e010880011140c2c44900f601c19406108001c541244008040b01101003d042c41d002600d14125103080320740e0342e40c0348406402d000742c010405c010070320b54400d2041d495480c001552400f9903c030306420580e10f0240191065a655480d41281d2900b61110300042006202d0a002401d80c1070042c00d0050840d14050000d03001d0440c80c00a0100c00c00d00002c40c608000387e480c0ca14042c54489181c502c0c020f20 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 18512830 1250 18511580 18511607
    0x50103150c08190b031c1d09090d080702010209040c0504081501030506070518030d020106170d1209080c1518010213090209190b0403020405070216090b010201060b0403140d02030a0e01050703 84
    0x400c1c1021440c2002d50141121f6083c2c40c6c0d444060030948901010048030b18401c5400d14086d174044c0c1c2298032218416840941c0200f41c03030000501c1d0042d990301080645180c3c20040001c01c90009003000248820080380c1c0099611418400d203d50642c0e80b101d48542c0040c1c102410000d000c038281a0303410307480e50b0b21002c9c00c81c01001c031802d0365840500a07001e41003030310a120a40180e03c46400b00b4100c08101d444441080d69900e007120310784e50004038020300d00d4442c10303552902d060041c503c142404002c0b0304a0091080f6510f180c1d0b1030100310380f007050492000e205a181c0d006100004181090715a1501601d40005000d0385031144030010804210915404a454000302c01000480c04401c80042003034038001e071014407070741d0380d0424240d0b65500e08401030b00f00061ba10b02c0412041545a018003807945d4148008115140e64101c482801d4006400170b40e9401c818031074505803102d003005542c6582450340040d41c2082200b11010f8440b8110a2034030f81070000026004007090710070365807100340c0e9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 18514080 1250 18512830 18512863
    0x1302010f09090204030605060f090405030712110102030f25020307020d020103150e040501050709030218060105190e1311040b1305150309010c08010803072301050103150c08190b03 79
    0xc4d9a207052400c082c04041e1265405074503101040703082810681c0d5218841e5801c40005e5240141958802c20603101b00c1a12404100009420a044a00a00095000c0c0c40d000c801c40f030607030034421044044d000320040903480355502000f040c01010303004803e80b501260111485444410b032400146c0103000e2f0b840b010700c00c1d8100c40310b010404000e4684000c0c0141c0c014070003001143d503010b5040c1d401e85024000a94000060504c1035102c8141c40f481035071085040c9045801c0c041044d161415400c81c000744c210104100e244803202d642041c0801c14244114400300b48412407440030f54400c144241c2c050441e00000004000d01c103207041d442c0d224001e04010300300d00311081c03940d4448074440c1c005542d14100c0c4c1d400c201c0c034005043d2007008164161044000a1441d00e041542d550340706240740c0140b101000c0009800c003414178001c0c400c0034020750141e00c40500c1c80103400c640320220b4000c280702c1e10500102c40d060008400040c01d102e400c42f11503010029403d03818800091408900050380980c9 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 18515330 1250 18514080 18514087
    0x7051003022a0307030f0503040b0a0f0f050108070602060903030708010513090507030b19050103051e0a0f03050405011403010b07030e13050a020d0b01020c0607030509010c0c06021b091302010f090902 88
    0x1807110010007001c0761800ba6556406c40c2a00040c126003520003981c0180c00160740001241c00d224981c2d100003107203010301e2400903944c42010344072030076180240d1120a00d0b4002d9402000320715018040594407002c004051840c6d454a180003904003241805000e0060707403010b01301201e03400340d50301412920340c0180445e458603960746444038180e9000c0782c0c500c65000601d03607020f81c1d031191401450705032944080a401d4800300d040200110740b11852102c0158460031150001151000385220011030290703442d40e0342c0e141480c00140500000c1446850ba441e000c02c01003040c3c0c191131066030001945864040800c5198000081e92942100f0f50304030381e80c1ca00401c1c0a070300d1803154020404400c0d80c0c2002e1200c401250016078403010528180c94004008204000c0040d1152004090107041410842c00c0703140192120855180c0641013540075074420741d04640101c15510a101e0300c00411034464000d440c0501951045102090009040c80407003202d00c6007142c00703030012038080d10226404548 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 18516580 1250 18515330 18515407
    0x21020a0c0e0105040c0e0a14010e040608010e0c060301082d150604111305040203040f050607020123060102030d050403020102090d050c090109020703090b0901030f05070305070801080705100302 85
    0x100071001c2c0300c0c0703600c55490959940c50050144103260303020380c0300510082c3d8140c03801078410305000ea4003c083d410094034400d4011569078174030030b00d809084281c0001440d403087c0350501e4500f03030329200740b207100702d070103000420150000090403050803680d802841c03401449120440e001a520001143c214081c1000d40c810040700b41907418455841120300780005495044158600d01c929101c02c4c070200b0104070207111764103203600259009813082401030040000d0b9110182420800d031155401030b5100c3c41d0504d10010401441403500140c0340601110341007000020350b0368421f603504d074400d040c2c54100080a0600030350564140704da0107005607514000618000d0303214684c01510500c00e50020002103481001c1c0e20a0715240d036030540781c500c005030a04620740c400d50051b06801c0d0405d5200d40c044180485580500e41c041c807038940b40800e280c105100b024050401c142c02c000c2c0d00e54081c0004002c1d03035540b0b14001070020b020781001a520307413031030003410b69000901e4115101e9640d404001034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 18517830 1250 18516580 18516599
    0x2070c0b160f03030903080a060810090203030702060a0c06060f0b030402010c030908012409060501022a130209040507030506091501030603050304060504150504030302030d0f09020414010807050d21020a0c 90
    0x40f00c4c1b00e55a03c02450380e610303c040781121128080c880ca507601109002c0c0350221964000c5201c940010102c030306010b41c80d80080e5003039000f50a80c40001e114001c00300b04214807401000c0140402e030350720301c0740306003090501c6400d400000c1020b03040001c500032080c107042c00340310340c500a0f002040081c0151400c08005050405545844104880d2261000103601d99988100019168141c0c040d1400480c1007100700300d8450303403480b03200c00003900e40c4045c0c042c0ea441c48885400c05580750700c0980ca4149a20810044a00003014201810300308410172010713035500503240d42d2000c1207046545c90b145965004070000c01644e00b000f0021301c4005804074056411102070001c854046c15003001e1b03501c045608a4240c0920300c4002c0269005118001c4424850b4002544052440500084031503003900041e0580f581c03601460380044410740180649442070114501409094032200080030a039030340c1d550804900e00440040581c2c00d6907101e0954401c1c0f00406070b0541000c07a400c80e2644a0b084e44 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 18519080 1250 18517830 18517841
    0x3031b0c0d1d0406050a03110102121201051804020a0918020616060b0a030f0206030a0e0d03060608070207030f0b10030213020903010b01171807090606020106030c050402070c0b160f0303 82
    0xa0355102c255441c0c2e4000e45007900455066035009081005898910350790890420030741d0201c08c1c198010580160900c0071020064150b445980800c4401da501d0201403208004451203590701e01c91b018410400541c81c1d0045840c12504248000a80e400da0450303085c440c0646484002d5001c07200084052120302c00d0714100600d0760045004010455080701040448016440300501041004000c000540b0741031000d9a84500c0348040828400c03c11a8804d0402d011906660040f9507904428440160f0100d0103d9018045000504041c0e00b1511801a40f00310000000c0c14100c2002c0040e00c2c08850060400c025a030240401c0342c0e54900c00074800182d000900d40e540a58030f801c800e901690b21500000c10000395401c140d24107a12420f003404810340f906d1000748120b00c0b40c084000303035490b19880f5600007030645500005156040d890b060ba4001d02036400544913600500600f400304234445030703020454030550301081d0f442c210458508020290300030b02030900340b100b0000030241038158006 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 18520330 1250 18519080 18519107
    0x606020a02090f0906070f020705040908120106110a060f02090603010b0c010c0e06030612010e03030a0e071703040b07050c1f0e010f0f030e0307020d03030b010f0309020303031b0c0d 80
    0x100549a4820030403c1402d002100c01c01d0a03a0b100c00c0c08510724a01803043c05604000d1072064660240c2c0750800315003074401c4504212042d00001948101d444020004c49000d0f0049141c91407552016010b042ea94441030040a06110394807010b1541100380c1c1e904035501601c001c4c08007503c81d80c6d02e01201120350421802e100f2076500f0302006200a5214110803070b08060010451811510f5a00601c81245c528a944200b199039541414078585400c10182d881415000404104000080084c41c184009544081d6544c40027107420044400003109881c180c07040d200901d40c84e00c03241c0c1002803524001d6006e05410680c121050180f00d4012104584507981300d84031074a01005c15401118810382120a0b803002441c00d540250555121390405030548117a1800c8a0a000140d0001003c0300c044d02ca0841c040390761004080840d50b00300d5601c01030f050072414100300c01b141a4000c2030300c034400141541d0034561501e003044121102c3e80140c0d46c1c035130142400c83d2480200004081d1031030704080310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 18521580 1250 18520330 18520339
    0x60914061c060f060c030804030e06070c0902270303030c03071209080909010b090108040b0c0c010e0c01110604030804150612030201050a0b060c280f030c1e0812070509040606020a02 80
    0x8004ca1070318000c02502c0000c0d1342c5695140ba090f56142c030301302c5030b6030b9490111540c040b00422421002c2880d408040025281440c1d0041e41c0d1406003400045c1220f12000400b101305081e03408841542c0c020090b01c3c3d00445c4072829550b695036071441250401041071a003480540b9244480e81071141450240c000305100f0740d80748003680d80340d502c1821180204014540041c01441c0010002480501c80c103402500c40140e1034140506400c5040c00e5032807040d0048402e501c0000075404642e0b000007103840030341070030001e40001c0c28207440060015000a2010b420b000d0102c0d0340b0000c8600c00d5101c9002402e24407200f100b120010f10300240a03002c180c511111990800c8180c0355a46402021a00030602c2a8001c1c002c8421154001035003004032058005074940304003030a004542c880340350b010320621955412020200070310748242c40f040c03540e04092068110010042c002400c590458020521140740c803841d81ea140300c0304440b644100c68042c1d0b0081d04240e00010801d80010754604060310884e03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 18522830 1250 18521580 18521609
    0x3020a09020f0a0c0c050a0e060301060e090d050a140309010903020105160c02090903130e01030b0a02070b01030221070f0503010615020703030f120507080402040f06060914061c06 79
    0x100008240c0c0980501c240a6203020044043c07010300500850036500d10030100c0d81c0c1c0e0282e84100061b1941c0ea190b010600201e60507040150f05d181c00c1c807400700508080351a682e411704101c90000e5032108080d4070307441444000121030015a0083c00e200c24620080001990f49242909400d406401c1d515012005982424042241100e96003c551520409540d401c4410318064003002404c40000c1d0100500d40410800c07501c28440b4604030a01400c0c4003021140306514502c2c140c55034510041076a5811841032101400040d0150350f114112a0100d81512004800390391040c101c100d00c043d800224410031100141c0022208620070440b40218000c00c40c03d50b50f82c120f090410f6109000c500160402c0d5018000a40140148031102505142610908515142690880700144c40c0b580c0400c4106003000214600350107060041d5087c3d2074207024042c58000080c0204406019090124800c031310250780070f459600c01c2d91103076031000c2035015204020395003150081c007260248000120152 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 18524080 1250 18522830 18522839
    0x18130b1f170601050a03020a030204080a03020a020306070804020123281d0907030c020f1015090902130b040207050a060507090806010311010302030c1210050f040b031504060902030708060103020a 86
    0x4856034466641a180e10f171520800f000104c000f54009028082415803d11020450020410002150034030a80042000d48601d00415103045801040e030410050400c2c01c000051340e1142440c849408070300003280780000c00c03c00d0107055008541003100c1c00f04032002c8ca10f50215100301d8200c0000c0c1c1503221459100c01101d10140b10000b8020041d03005807202d4045040b6600c40d5100035880503a6104cd9201c10700c030454100c0c2010121001203403ca5115580380b0304a0904103140001088804010008200240e0105408074180300d028580903070f0358001c0b0015071700d60b60120303000c05500c24262655003140c0d181190003044242c41c48030000e200c142011036231040004043d41a41d030040c120710b646200f00703c0114065840102408840002802031080340404000098081d44002030701400d01e0381032005200341d410071110302c1880345080c03445003030303481e200407500c5c40e502d0560f86814441503507107080440c080d000c800c2c0020b4161040c01c01c00141e2810100c0d003176040e00d1080300d0460805503034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 18525186 1106 18524080 18524117
    0x12080301090b06041410020111040b03010e070305040510050402150a050d1a10050304060204030203060403050307110c01090b03041b08010c110318130b1f 68
    0x20005000c0007550b40a1203844500c2501c0160809203001c80708500e03001104031050180c0040200d03404854800c0d00300d280ea00b03656000407580c8540d61a05c0e07a0f00c0e64401d00c41d14016404403004910918030130701516024542000c000c011000582e00d00100811010304126072007101907542550700d4800c4030240117815460b4450740d40b9960704210f0181a104141d103400381a000d07507040210300340c0c1e51604a05a5000d00e25042d41c6a507030b83d00d00040284038a0304081d60601c00d81007000308066001c3c0046201d0031a656a42500320030105660740d603411003044c464049400030505114030140319000c0c5a10601a1001141e01101361100c0351003149140c0040c0703043d94444125443d805d401204003c600c02440c0300461806404e00c0000c1c51090310480340d5841112292030425501141d504801d1105200a000c494074510072454820b42207a90400f04c80412940c0c142c20120350030 = true := by decide +kernel

theorem cover : BRFrame.Cov 18345330 18525186 := by
  have h0 := BRFrame.cov_init 18345330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 18345330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 18345330 ≤ n) (h2 : n < 18525186) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
