-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5177
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:00:18.612731+00:00
-- url     : https://prove2.me/submissions/d32b4676-4d8b-4b9d-80c6-a4256ed11b55

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 930935251 ≤ n < 931115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 930936501 1250 930935251 930935261
    0x60c16020a0e36120c010608070801061a070c0302240307200c150307030204080a031214011410020c0a0602161a0d0504030e18060109210b060a050306100801 69
    0x820000f480d2103000701012920b80c0d803d8801500340c003c410118440030100c40c250820b801030300210098550155442e41c84030701800d020301a400e041444500b191426880203401d4404a0341c0015a0301001c03841e40e02808100307581c8668072441b41c0ca0b0540c03c81044c0580c840114001d2246540d200d80c8020100e2441504100c09010310910760480104064140d0b81d01d030b4140c0548000040090307494594440a8009102e41d604c050502e008840d01c4074103064012b100400c4480f040300c4c05100400502c05c880820754002d000300ca07503041504070701000a0410105d6440030641c180111000f80008000240d810788046c0d02c150300581c004420b1b2411100d00d2702e80040201314250703800c02844103410f0905950301401c280100007603966000101814030a0304a0108200302610020038204101718401c80344c50b0480350b40740481c400d02000030f00b07004051410782110114a41c645091504d1361341d60644900041d00b81030b44551420004030302c42e58240f05144c0a0343c42c4000d030801d080d15090130303030f0b082d51 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 930937751 1250 930936501 930936571
    0x1e03023105070c06180212070311030a021f02151302010e03030a0503070819050103110909070e150d1406192304210e01030b03060c16020a0e 62
    0x9041c00180852581c01001058816500403004a607080045030344a640e807440c48006540069003050001542c03a02247c000141c0c4d0081c0c03006114103808405060746d92550070300007074100c1c81160881189080e80b2240094880c1c0601c159504001c2d40100e4000c050020742c0e803500310304a0000c0e484210f682142c4080c81e2003406401070b60600392504c4d4041c1250000522400611010f90005104546001c030132001c15010090200950350310b0341404075024035403102140c0140d02d41404100a410001801c0f01214441000400507a4070140540c0b94098110070103a080903000c2c8031b41c4002200045010540b10072403000b070003240f420105d2181c001c1d0003004480840c52618941c200c0c48a04c0700e09620f40c0880d610303000000e0b5255031a00500c082d101744c03244907652011509100c4920f51106400110981c260b07010300085070500b04044c2c580100781d40d11034020004020700b0b1031b5040c084903d094802e00007464920348a60f5901049001c00f0104d42500c01c024a0380f0201103c1d10381900300010781 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 930939001 1250 930937751 930937849
    0x50103150b040e04140d23120a0209030c0d0503030a0606140301141201090c06090f211e08070c0f1d0a1803020312090c0a1e0302 57
    0x516101d14005280300c0ea018403100b054480d000542032061035501100c0c035824a000b1500701300f03000c1400500c5501e152143c2c1e0000750710800201903040b94003080e182c566005541070100303521145903100080d84403049082c0c1500a01c2414a041d540f83e400030158039000300f01840c1e503482c1251280084484a800980c02d0000d01d02000b40e1090104003503906441e0007000c001c442d00d451100142c1980200c004402c180d6080070010000c00208084441c00c80b8045e440780788040303481e80c0104000c0841809001d01ca4000f40102c0100b035403c681c2c441c980140990a402440010128144881e040b202d0040e01c44201c006810000c00013034500380002003460300021382c5001d040440424071403140c040c0c80c40100403000003050000d803066002005510300d404403d5a05c03503130352401039100e41000482072040798200c00020443c071008174881d40c40080003810b200b084d500303100c40050000382c03083ca6002c4940a5540210042c3c4030919075180304d03482e038156802c0310081c5000c60f0380c06802e40c90f604400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 930940251 1250 930939001 930939041
    0x325080708030d0e010906020c01021308060c1e130807061b020904060c1e09031109040f0201050f0d0f02180a0305061812040e041b0b0d0f0b03010c0207050103 70
    0x241c11408400d580c00c202c01c080c8003040c010742c007603c5180500054a000b40481d44000740c980d5242c0015402800a10b140b1610b440c043e9555020307480d150342d8101da0100c02c0200c10408620031100c02d045640b11103a0984a40d030800c8050812800c1c3d454160300142c240341d000003010320a81e5003024000104003000c00000041324601c0d80410007030200500b0040001d82c545100b84100c41c041c660340d58032081407000047c1030000c24480100b01c800244401d40302002c0007210340010741011680c2d41d10468001280914a10a40d40115400d50022644410b0b104080c00740641003030300780c0550980c003205080c015032503480701c0d02c43e1440c0744421500355220300450746c030420001d81d0104803541c0c04100d084451044424400f406420300481c900107042c0030320001404a400101c4a030521300503030089001d1407800441c0b41d0340107030700c100074081e80d108043c06029001c0010309542118864007000003012510030481e401080c29140354450790030258003e0340781800b0551b410301c50291008004009225 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 930941501 1250 930940251 930940259
    0x41a03070207231305060a05010e0603040b0c070f03080106110d0210020a020304030501090c17030a0509100905041a1002010c0c06090c050306010902030f1311190503250807 76
    0x50798503a2407003110103c102e030003c6120302c00001c2c105090704030b070301404a6040742c124030011001001c045800324842c415156012a09501c9403544082c0d60b0301c094181440c5031142d4030380d115001d2000b0114075141d4070802600d40001c0b502c031400c22740c451090320351210359410404090905003118240140c0e603400701910000d130a070700285000b8042004080141e88400301718080b821841143c001404c158200100c0c20100140072580604a501419184007032b018460031041d141d02c111004a0b002030420b101c80d10540c5400e4200e844c07601c0e00b60400c07401241d40c41d400f040907903089505000760524504032401b00c6041040041c28111103500c002c119100c41200090440c03441d0070340c05403400e42da5045560400c005032801d140546002412200e6560352100403401030741c0304480b004d4103000d10502041031180c80f0654034500d60750205404251075003942c2480401c004a20140302091074039040024540c0f824030401e80d200700c0100060100c02c07151541c0200d400820350007044140c0c04414104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 930942751 1250 930941501 930941503
    0x4140603070507111203070c05040606090b12060f0d030e010806012f030f04080a031b02060d2d0c09080c0a0302011107050307061e091a0901021011041a030702 70
    0xa00c2056001c200e100c00b400e041030105d0381c0840240300c540500d100001300b61060020100007442110f8080b202400129112101260701e40c02c2c03031242111010702808014020f032101a03144d58010400f6243c0300a844130400026055045000b0a40108850b208010700d2540c0c8000116800182030030100d424503103a20003001c4c503291800300e418134014418491900844148200c86825403088070701174440f511441c2450f111248040c04030b001c9a400100c1410224540c1034036415950024441400c1104904840001c0c00040311000d04400ca800440040500404076200703080070810b100082e030010008003c1d00810b02e82e04a802c46a005402e0408243d4030103841c042030f42e5083c60b02c004011074083c1c66a2030464150032940e418050910081a030a9204500003045000c07002031026545101030251032000d03080c001c1c03d000c0c100181140d0f0840c00c09000400304018188101c0700e500041600c114200c4000340000c1c00c0303040000400b044407242c02040c04000b9071750100114a1070601132006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 930944001 1250 930942751 930942757
    0x30516080f012108070b09070611061b190f0e0a0b0f07050312090c18131b0504090c0f060203030c0a03051017070320030a1103190602041406030705 65
    0x300f07010042218644882260f80d0300141000b6400b640c5584c40c0c2c1c00074541170050390011254403a01b8070482100003011489540d052010190580141006442c0d40c88580e01d01003080344c0e4400c010008201001e602c002c0210702c940c1d1110789a461207000c9080b4440204041020b006644c49100342c800b06120110740803044800c0792598040041c1d07201c0041c58200d00310b0007074030300950300b41140c0410020810740c08143d0188280048411140c504140c00704540b40000075141c0020b00080e041104000801d459144880c1030140e00140c420640d56030005402e0700c1c198001254040301e00242040350040b10301d0b1a20180c20540003950840ca024000d0400314080c0ba50040c040607103403000f0403d00300301c0c2c03060017020309820b4120100f0312510b031020581d00c0203d44401c0710008954087c9500e001040103a00c90244001005860341e9a1140c45814098003401030866060140510803102064803404c0001c00f18816503000d80c8440c07802840851151100c414580103070380070410040203940c45011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 930945251 1250 930944001 930944009
    0xa0e0d020f030307030503071e080f040c170115060e0117100e130516261507020a03020708010507050f072301021305150304140a060606030516080f01 66
    0x4060814000340005200541c2020856826010006141040c503603c00001d6100b03d841351545002d880c500c0042502d403d50000341040040c0e02840411050300fa44800c0907080f5029090f40e50b1010744500c010741e4215881e02c5d090046170b5450070010781d8a40d00b42c0c10103000b04910b04155000916140001e0000c1c8180c070401929080b0860004100c140180322450107444e210140c088280340c194142c601540950000399520b100300d00b0040d11103c16805041c2c160380c141010681d1550307000c070403040003a48410b000328003809003800c01c15000729070603c018032850b0b59500528a80906081c080d04000d00380c0c0000f000d69050800f00714035181c0040c00ca83d00804034580c01592441c090528000365503041c0700045185c5c601612550000d501500a05203455654100c0d940c035942e41e00410400503144030300c501c0900e2051001031301207019a0584000e041070300041da04090301613518041101c49079044040865030b03da06000714028002c400100b6002c03031381000130031400c01c050515441c40052203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 930946501 1250 930945251 930945259
    0x703140303151c050307062f1602010c0609080a0f181703130b0903010c080103050a020103052508040b060616060203070c061803020609060f011401050919050906060a0e 74
    0x1810003a0000c4540f00340f080c2a0850140c0c5d0322000c42e85051005407022540c40300005415800f01a03105882c840402d5821035a02041d07480c0c80b14a1040c2c4950000801c02681071141c0c0c4551100840c015010b264400c61290a440750b03151304880014200180b094100d40401140501211641c83c0c10340c5a881961501141006d881c4c0d0408203103450340c800d4036210751803802441000110041c0c941b01034001c81c58214028409060007210890341e901003444041d1447d40101c0c90b07240994020382c4541d801182c0001c0255142c101c0b92030301c1e040c070003c00c68100c00003a1801d04000c240408242c0e802e81000381260054600844007071000c001d180a860040c00c12540000403401c0f150007201e0003551207521040501c00d400c41c2200c0c40c241070f10300c0081030380940988030008801440106030340c1d1150021145002052f42030a80c01d82d284480902c0d03840c10f00c20204410b80e01642e4500010400c0800500060249400c080c180301440002421071401703071130140480c003085078104213030000e25401a1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 930947751 1250 930946501 930946519
    0xa120e04090816060c030e0c0d0c0b0703050a08010504180b091f060f061b062c0606040b060a0f0e0307030204060b04290d02030a0b060a02070314030315 67
    0x34004004a01e4020540300d000900b003010300070210845106079000d01e0007008080090707403054003902c81c100c41100e403e80182000b0403242c80e10b00c10451b4100e01600e5980b5080d41c68002c9034200741d1241500350041b40c404200c0c2d8130b0141d803200d4881c2c00750a081e5400d10121140280c2c2e00c280c1031030360100501065140001401001080150081000c154020f03071900eaa80d80c0808001032800307006100030192441c0f00480d699000b0164002040d00c9020340300104001a1140340051100c035102c80401c60481100b452040e408a0071211503046560261409040150030481101d0308403c0351405210244850843c0d160809240c00c003244030b500b00781c41000d81840c0020700348001c5c0d80001790700130300d0303ca0041a03040201c00a441680e040d90300014030811300d48070000300601a5201c8110a080c1044421405401e5801543c1c000450000105000c01c149000461039003103540040010ba20240e401c0043c00400b40003058003400c4c210245246080078944140038507020f90103980216290 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 930949001 1250 930947751 930947777
    0x30503060f03070f05091501051c0b040f2301060518010c02030304080a03020f030403080708181201020901030f050c03280e070e0c1206010f0908060a050601110a12 72
    0x726091000c03500004060b034100302e441e00301d00c030151440d07801018055051030002a420808140e90b00d11204416144c4508110003540e614404480e8214004102c0381c55100070340003030302c69000b0400507111440f804203000720303061654180c0c03052280105280b04a8500100115504074044030099074600c001040458042d80040c1c8010410040013905031000140000f1808800f00f844040f4034484c1d4240d03001443c2d0f0b5854503680703010720301015200f90300421641000460305c80091440e4068400d440e040c1c04800000500100054405c0c9146650005000d44213580e1510400a01a04d05002003105040c41c0f180b03a8032a0000400c2c1d1a402042c103044c0e07103d051000070300c0582c00c0f0300b0080140082d401c1d5081c41e944880c2c551041858018102000c511800701134800d8801071264440b1506595483d1f400440c0c001e59071030740e84005d0050480c40403c000906100e660b1060403100c42c04541400c1800004062103d801218211078000908540c0012400054020307022200c2c581300350900d0305 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 930950251 1250 930949001 930949009
    0xe120715230717070215130e0f060f0d03021f0b04150e01050406030308160e10030213051008151c0f0b060409080703030209060d050a0902010e1e061c0203090304030b130305030403050306 82
    0x3600030281c3c80400718100303d0327031407050b00e0b91600c580020742d10085825880310610594507001d200040c00740c0c2002c2d203d845103920725640740c03440301c03210034001c50000540030119086501c00881d4540003200310720140451100034080c180142019201003120901e503840007030042c18041c0141102d00f501c242c494200c0f522400d444601c1920081c203800b000c03aa480300290003540954420b0800320b00b840b10000d030514001140214581107a220144541d840700e29140c40030000145243d400349968179606203d11030902c9000c4014811800303160a4100303030414100c4030710004c103c42d00c036038246032080002880d1181500d10580d0301d810090f0b1107001c02c80c0054598081d1130781c0c06031210b03e49010010050215088040c0160003a00c90b4118290241c0500c030355044404058410754070420301180260818000401d0103800200b1010310480c890318501c81039034010740d0707503039820b42c8081418018050f101400503041000030b0f40802c4607408581d009440da00008001030240007001c4002106616 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 930951501 1250 930950251 930950287
    0x705091e04060b0418020a0f0509040e0607030e07080c01020a02120102070206070f032601050f0d06050108070f0f0503100b01180f060e120715230717070215 69
    0x11006009101943c0c60707208100c000e80003486440d804502d840c0e40d541d94140d00d8400c0311030075040ca58442491200380344060301c19901116116030013503601c050040c0c00300c40512105000f1140c959001c00c071804041e0400b46040c81c560428130741500580c4a481540e84c00103080d1549a906451007000400e00343d014600a0282d610301a400601c000380410401c1140c07415101c03618800d403a240c0d06907910561074007288400e4a03402100100c2d203070040c42945400f101405005000400660400180741d60350410348600ba84010400d9005100c00d2000d0307802c00c00d81c6006403107a805040300041ca0704001980c4c82c80300c0a5480056942c403401034074070f82d20405284900600e01a13102402d01d903112270200305800140304040000344c000b441d08001e403030020030346450841d0001c010031060f4200007400d50140e084034030110501980f81c109014040c1c605051907a003010b81032070144c4454143c20188070ba140049983c400d009010854000141e0303034080c02201a10941060940f1040110707403c001c2c1768 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 930952751 1250 930951501 930951559
    0xb12090f060408091f0c1401021b03040503071212030b0a03050a120f0e0603061c021206150d1e06110f03011a070c0e1e0910060e070509 60
    0x801454104002d10a2110007065102025600f100f40500d02003828000c50000300c20a45c00140c0c1c49000b14003148070002e0948481c19400001841c00c2128040e41841d640350364640340c4c075074201081c03c0015180502c909401000c84090f1f02410494594450200c0503074030b10f01d0800d00d42d540742c0c41a21621805d0341d60b0040d50348101102c000482c1d5050044200394100c90040000e001052561801e9200f548208000e81000d000641580c07a03070b004120301803c010500d640f240d140c500441002d6610725402945040301c0c48007400c03060400c841d5425410301070009603070040b000c0d11601e00000741c00610a200d00041800169000800b03843c00f000030700a030040f640e034451404680c01041a040c80c004604a9000200c010008004c1090000719400390071005090100e16103020410700081c0e9010720b5000c0320b4401c02ca1421084a03801088050341641d40445540c0301c0c0d040071070302da8070522654014209648403202d140c5081140103100e031051080c02070140a0701c02486043c2402141464958 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 930954001 1250 930952751 930952753
    0xc100e0109020607140d020c0d03051c0204030807030813020a06030c020a0203030406050d0501050406060c080f04081219170112020d05060c0a180521100e03031501090b12090f 77
    0xc40042c1000300240b15017400d590518001c04161728a210b000060308010408050700e150104a219181541d80c2c0d00a0302c1c5c01d10440c1030318080c80305090701c00d100410141d44214a407584034501820300400b040740041c11421494001c1e404038000da0348104d40002190300b50714010a2214803480101c0c20711800308402074162001240c007080c0d4680200c040e00c905814030001700240e0ba60b40f0100420340d80ba5104101c0810501000000800d121000602c0f171420b2144203e440e160740c03045881d00e018003910080c5030901d40899407281c180c102c0d050b19042c6566502d0600305070700500c3c400c40703800742c1d041c03007030000103411450b0f50300440d26005c0032540c282c0d8000e03040c3d0f1501d241002218017654080c106910000c2c0c19495000b854510410f8884242c840c0942041543c5044002508240b80345409102442c0701c3c42e81c0101440d030407030140e901840603d00286403203003007010041c20701098811181e418005001401d101c00780040d41540d00401d84000510540d8841601840c10302041007003011603 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 930955251 1250 930954001 930954007
    0x13060917031e010b0a03050c070507080c130b0a152105070207060f17060a0506030403020c0f0402040803090f040603020910061403090a0f08190c05010b060c100e01090206 75
    0x80d29030030020790300c41e03248000e004450b407601540390081d4007003d0041240003c000d02c04070700158400e0384810740c0501c0c400d2034945041c140f0740b0f80510703041c03480c0d00c0000207600c04002481d1030b0031b10941075050500209070901220110a0004881924034003802c4400d10304042c5580e10b09204036030100d02c008007a01665180388036000740c0006004115007031400342c410110300045031407041c405100e45100580d10324044254500da4070001403005000356512440d00200440c00d039444000440c06a0f120750000d144c410f40344024054040c0002001600c100e00c103001c2004160404000c072000c0f00400c407003100b1940e040200060007440c45400280d00311f08031508112801b1405d81c4a80d007650025215074010109401801000e48800c448140503034100442400008403111142041c0c07500c07510b0712a007024000c8034900c1a22200c107291000080f40c90480b00d00313004080c4500c100e021415980d603481d080ca90140580d5408040740b1500e8803035510420803c0401013944074107003031a4000c01d2583d03 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 930956501 1250 930955251 930955283
    0x80412051605062a16081e0d02101806021309110304030c120903080a02010605040e030306030303010608090f0d031a0103050105150a091a1b01020f03130609 69
    0x5540d9200c11541d07014100010070115072071070501d0039200b841c60360701801c0b2500141d219405650b1001950340c8941407003002d03e2020030300311484604000e00b00b202d00400048408101180c0d200c1d1980c580780402d50410084482082c0d4040342c1c0060103090a98042203c040a480050308910b02a1000c1c0c02d10348081403c503602100f00c0d21400403251800b01c144180c2642c40d07111041488150b400502050a51100c20700041c0003101e41c00803c242400c201107010390b42c1d1121079042d4460750407400183d41d40e00040c0400d150a20600e001141c0d036000950441c50400b001c02e580b07100c10f000e8681408040070020720032030000c010038a072203114102610040c00c51740740d002d00900703d1000710300d5425140d08200d48582d4400d00c1a1812102d00512000c50b511140a000d4681c3c2c1c410311001081140160001c0741180c0706031005602016281401541c510b8001c2858030044800185c0c2c0711070b0f9004000311071400e400c0b003007680d0300118401c3c10400782450b00e1912400401102800914030280100c20103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 930957751 1250 930956501 930956503
    0x20a090603031215060f021c0f0909201e040608041a0709090b010e0a0b0307020708030316050f160c09050a020403051203090c030a2103020315010c08041205 69
    0x104036407003500da40c2c1d0a0401c05008000f0340d0702c0c07841e07040000f01350305100b00042e612800442000c211a0b0041d101820700d8940d1000707400304441624404030314501a003440140d8040c540c68000c010a4004028078020411200300215480d5030340e00c0c1c0d0f00c1022a014119000c0c0030080f40302005e00c4020306a44c0c40c0d0f201409495064103d605640003050707580450042000801c50301d1140d4401e07660310a42c83d0500e44158001c01d51001098100600f00720507580f0340e1660036020300944030441145460b803401560092506440f0b410820b09a0010310520110b031002c0b0402c6105550745060190304d804550290140a004041004500c042080300c01d8041c44540a00c2c0360548800c030400f4005591454a003030103900c030341e1000501c5039000c1d1807a0510380e0060405180c002c0ca40b603081d5044140c44000091070700d000088180c03162200d0400c0a2003503004a10102d0340d900c041d080035415440c00010140d144614012524148a468003126003004540c500f2140075110f41103103c000411141822 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 930959001 1250 930957751 930957761
    0xf10021b0a060e0904060605030304030b16170c03091614040b040209030d0e04060306050708220b0105010c15020c07030b0a1a0d15020f091008160f020703020a09 71
    0x224003440c0061052222030030006114410740d6001c1c1c450340c6000031024207102050310000c00a407a0b10b562074402040c503030360a000a000071800354014541134100780c40c0204564808240b404140040718078a618114100703021780da0f03c003002c0d08a21b9180c0d5286551107060200d1210048600e0300403186c042004c08551007002d0403110156401c20802c1c1c9210148001c038403564014642c19400000d034088220b2151880c0003d1000c003400c00b01c0c0781c0da941e0b40e80c2d109440703042d140d62000c902a0000c020300048002070404100c82058402c40c0115030980b10b03155500307410f0080a0401070f041d10380c1c0b001e01403c0e042c009200c00303100368210740d1020003c0d10036072509881e0008607031200111000c280004054002c0d070322190310201c0814840804541007000154400e14121080348516030b81c0002248540b01800d0384569104400d96654907020400013025102c508150a0144140510400355080b10052145d0510390400b110742c8214000280e203040c07000d40c0000d5105000e140003040840b03c40e042 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 930960251 1250 930959001 930959023
    0x20909151006120c0813020415030f0215090d06020322050d09060212090609030703150204030c091e0c0c0c03050f010621030f090302130b030f03070507050f0f1002 72
    0x681245560320141d102d05440207099401c000415090204589001c0721507181040c503c010400550b801c4082c00d20081007165034016601c202e4242102401e4dc10010006c0c141c0c403c1410004d480c0c02c0240c4000b9460070b500201c05002c250340440006c0c20f0b1100080b0310707584400710842000c00b030413442c60907030307520054601160001240c1200010f50340d0f0000a20054155880c02c509082c11164024040756400c2008072a0f4103115900c00040818826040e1900410a0000240c0c4c0d03036045042050303e62086034401c4114038601810f1110119500000c1400d00002c0140401d41924014003155140110700014050203481c240000410400180210b0070340907001c000d00c0003c2d035400240201310000c0b008411030a40c05030864000a1041102c808610002d080c0030f1182601c030340102e0800c081c1502c2c21084681e81d14220401880e0403c603110744034241c54011860310407140e5902d41c66000c40e00c1040c0c06084420b00d48003e40e612015a80140031f4060a050001030141c20002d50300d15580103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 930961501 1250 930960251 930960257
    0x5070305011a030604082802010606021b03032a10050a050a060609030b0403021207060902010915200c120a03031b171b04170c060304050a020909151006 67
    0x82d20b010300800c042180c0384018000c0182696603910f483d4807149500180180d11400b50b1141d00b0450084203c4000c411044a90300000c0c3e103034144000607140c81070300311409001c48c0300f03008800c060340d5000044980e010750b459031417241f0603001184a01000b0100c0c01652850060800c4100c0038a416846a071098140050902a03600d820408000311b4400340191070014200c0f100a01c00b159441d42802d03049442481281c01402c60300c034501c1c0c00703a0442141101d170303142c60704018020b569104061902410600126a40308003411901030100e1901049900750203901c4904100000340070b00105070f01107000352403c10f4503841401140d854040c0c184088000c28545a840c16594942c2c104058034403c0685902104040c1c008606426160007050590304a40c410030880030032800f1009000103083d5288200e43c801c1c46240d03903d0400000e080c1e407601a0324180100000304100007a0840c02c103406131014010340d1140d010041c00d000313100030111007813540482401280c0d100c004000003281c4c0705607 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 930962751 1250 930961501 930961511
    0x4060314010b030103031e1209030f02010c030b01080604090f061107200f0405090a0c030c09060b070f1101090b04150e0303090315071719060f0315110909040507030501 74
    0x82404049003c20702000c2c001554504200c0c07805004070101100c82e04080c00c0c82030f03100c0311000720756099990f00c0d11f044000801d01034a48440700d409018200001c249420244001d1078071000007458501d0040c03000d841152980680000d01c445080c450403807170b4226400380300c511081020250580d00c040b1007113400980d20800303604d1102041407020074510009111194407a9070303404101c0908000b81483d9100e0241144501c001541d030701d8000f000750b1040a00c0420549060706240460301258844900c0300400c02280e0001000c0388990711482e0761003000c0c16600c6298400496004226420442c0b095000060106403105154080d25030340086a8600754102628001d0580328029046015050740c00f0000103101d1110440c205a406807051408042c0484031800c041d00c41207040e0f601800a6004103525034207034010f40030384805022028401c1d01118079641e14004d098840d20f0440e491103036581342c000e5080400c031044800140f801000d2000d42e0500d0306040d515500d440c4000c507400e40c030704 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 930964001 1250 930962751 930962759
    0x10302150c1207231b0102070b0d0f1103070215010609030209040204110d09030e031923010219030203060907031503031b06150e0a14060f0f0301020406031401 70
    0x501218450703844040036000a20700000941a182c000080c12500c5503e407036150003407022201c039400c200c501500300400701484003100c1c10140022400c141c504641101805000d0411110212103880c110030400003400c401030755030000201100c5400114448001080c0440141d000801d440d4501030040803d603980d03a18102501d681d2440d100080d00b004034000001d0142c502a8040ea80c0012813100b61792a007480911184101c1d00301400c01c40100300b4810b0110304600341002000c40715030030003442840001450310742448090980c03200c028556404003840d44603070400c3d01581c04404641410b000a1103203614043c000e908212030207801021014006800c481c480e00038402c18005803080ca01e0201d00315141210501b5101c00004d039441050318400d000110030344039842400c1101c810006469007000071010383c040d00600701c4030029013481082e40c080c54100601940100301100c1da03101200c1148082481154030340202a49075101140000703500d509608005140c5144440682c956070721 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 930965251 1250 930964001 930964039
    0x904080c010e03090a06051e0a03020d060f12080d150e0106112d030405090a1d0604081605160b09030708211c0c02030a030b0405070e1507080c06010302 67
    0x241c0b594180d800001003108115907800342000744141040122801d05c80c0d80703500b50380388089e803088540380e00190340042c00c1d1800200c60304c24100036000c1140c0c2c10042340c0c43c040180c0031042880380c02502d9080d0018518070240440d0388014040040114003041550303483c411001007000c244140c03008500d4401140c880d65101181070306490705181e1903904150010440498035446130355500c2028841000049010741d99151040c1c4a82507804003c910a5905001c500d901c1c1225081100c4540c800382c140000035450f030003620194000c8090301641450369003401441c0241e40700c26101000782a5001141090103800104281c1005900700c03580d036951080d8950340ca261440910042208601c502e00308220150000c140a06401d120481d8401950088000710b0f18105088405a88006540420301d6014000e01340c035032a04603001c000724641248058060440007001f103204410641d02d03417000e1541481991410b41d00314180d41d4803659107180c0641c1c0c80f1802e00040e03114a40600c90881c1c0151 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 930966501 1250 930965251 930965257
    0x150e01110c0a03030f0306050306090318011805090c070f03021606090e0f070903081902060a090203100903050d14150306040323190305040606050f0109060e0307050904080c010e03 79
    0x11010b4041c01c411855620100d030008807282e84901095150307000001c095404001c16800f071420740d40510380e100d504030300d03903108115500481818007404008070002040302104580441c1c1d02900c10340b15030b82e911040c041044c40b40c40c2d0b00030481126403420405140e030004201c0c01c00940c1d50310b007245981d204d0105881000052042c1d480600e4070300c00140c82c070340681c0700c919001442da0603c3d2802035203955585403940c00c041034500d0101008038040704490f070f040008039000b6001c2c600800110055801080d100d03000b400b00e5403186600c0300c3c400008c151288007210000071a1000402003210032160510035030340180c50417048030300e078180490350b2481d0200c2c0880c00b45078542c60780c0100c0d41f0b2900e0750485c00c40502000d210007403018048a901c0300c200b52481082e43d445c3e0380c0d0014181c6841d02d80130044541d1600401e010700708000b002e03941039030400201c0080d0383da0344c03c1074155080a000000d181c420b00c0e801507604074a80c001880208038068014181d03880b0704800034049040710710003640d9030340 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 930967751 1250 930966501 930966523
    0x11512090b190f0216082d18090103030507060b0a0521120c2e0c110105090109022218050705031b01020a080a03020d24050a080a1b150e0111 62
    0x80081480340c4001120748006000020007401c012561a1058881f900107400311851100007802c0003600b101b58001c0704403120fa500c00206c54640455066840c003c000e0f000740c01008000a950b6041488181c0d101c1022400038000100051794a03030302940142d6941c01d04211201d02d51051000d01503d502040083c1c6000700c18560040c40480e80260f00100d40980203003a041401000b0601507510000358044c0102c03400d01910b40d0b0110010704e02c0d0303803400c441c001810020f460340b41c80901d00059a40158903501e00e00550501c80300300d507050b800d4800401d40c40000c03440e0480764044007010014003040560440d0011020780b2641b00340e02c5800710400c0030040d2403a0040e0882c03591130001403500000b5140545045c0740050400d030310754000750100d508260b403e103403607038201440a03a480c0040a000d00500400e40794140e26900d040707a032513078034030340324100610714000031002c2ea404142d040c803054000c00c101d4400d02500c5c92021405405154034098617800125034580301c0c0d4891800280307045540f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 930969001 1250 930967751 930967777
    0xb0d0c1d0907090b0309030304020f22050a1d010e071e09021608070507050f03150109090204021c06030204050a05070f03050a0e070b031e011512090b190f02 69
    0xd80110100100020010640c400740580d40b0004140d104003180036500c00d021420056503281442d00400150085118804e44a030009200305c0703038a43c0c54851a0b03900f410300c40c0e1012070b19440b48180714001c0d110003a0090409484080e07544d60410054002d8440c000219080c1c9961944401003202c201c0400000740350f070f01c1903104040010407076a034010102e50403500d051011100040d40d031314405500049082d50213502070345092001c0d1900407485820100f088009155002404a18045105051003610300d916070f0303007074000d0554440e501202d010f0910800d0130344d109038403007003040014440350200380d014514040009400c92564400c181c0103840079200c0180c20040280210082c002c02844840e1035515125125600d13003007041a4006060184003041c0c882c942036101010001050072400b005824050041008815401d078400031384807540341c05010001c21880b03240103084140070082454072a04100a80302c003040c000500880841c100600090780404d03c400e00342d0140e001d00c4441 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 930970251 1250 930969001 930969047
    0x150b03091207051218030706050c0a020f03070b070318080a0209041101230403061506081f0b0313030320092106090a0c12030c081b01060b0d0c 63
    0x34200c444016020342d910940c101d40c6204800070289546411189034141078054071340c031300711151809110f08005482e29292590500040750400350b074074004864083d000744020422907826031401c0c44000041c001e03e0060594521203480c00404041e80614421000409158007141a4001083c8408280e8004010082a4130307192182400700250402c01810301c14102c0505e01464010300c0316200003181800d2054a4514500b046000d94038a42040610305150f03d40a1080039006a1001d8029441c050a800c0311075114038508217900300c0d0f401616041c1e03804001c1065800f40b464203035104070320940e400d0041500c10001910317038009410358401803420a016220942c10315403050701007d5220242e036020301e187c00c0c81c141d0500e5025100ca02c15604051098800c0c41281c0040d14000d04482080b4050300096840040c0302c1018003c0040000c0000a0310b115100f020312840c041d6644214000c00c14155100d114000c0b5138407004044014074100218040600c0c0102d070309901c0f1803800c460640d5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 930971501 1250 930970251 930970273
    0x602070501140c0a140606040b0411040b09281404053d080601060314040809040b0447031209030f0601060507051b030a33150b0309 58
    0x1840e9040f0ba82025444d11072028510b0108a6030700555000d40b05180181000c0d0034a002400183c80407510750034000c0c0c2c01d00c00346101c640c0c01d010407034007112000e000d055255070700e10002805800d0622010825500030450180c003601340d48036048201c0d10b00461a840c0058060180429148200e640d50540e041b02e00c880408015010030050290980c8035140c02e5603409440482e0400c84c003600801d0043e0f10210060222075098803c410081038480c0c6040e5052a056895100038816070090b035000b10b440300d0045c03c083e103680e0406920000404d681650402107400903100341181001c46032a102080c124003414005a12240000030304050301920349030401200c812101d92140a405402d0305c602560b1544420040c84224081d050b42c0e0380701e0350f695419041040c508008901002180018142074011039500000c2c911100c940c0958082c2502d60440c96015042c1c2004810420320701d042480340301081025408594030070541c0c0800c0420948a40e600c0656000c2160080850381c0300400d40740c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 930972751 1250 930971501 930971537
    0xc1214060d02060d0f1401050d12030f020418050f180a020f12031b010c050a0c030309022b0c14090105062b1b141902030c12130602070501 61
    0x1d508540003803c064900500595804121014840b0740040c0f1035880c0a0083c004c0104c1c04e02c5401081c0c11140140d02c1e099503181c040c001403c0c9624281896030f04d10810040803004d4041c5e8000301007a0356240f060410046003600a040110380f50344c40540d0383d0000848204418413038111100b400001401c601c44254244050000600061a404108039482c0044c6c10410801885c0b900c28a000010703000c201c5a0105003503506084880b81071001c20700080742141d41c400e0b44034245e00d4041c039001c9085802c42c00881c01031f036400070342e192070041a030075400c0c8544a03040c01490018070407030381e00c140183e0700c8079240070f0040c0c03000314554820b442c040100580c2c900f00f0302070603582103011071340c888030041c00b0208100c680f107854507922440e4440b01404a82094501582a10300e0142808000e001601c1e119000782d01c0b076924200000c5525182d0011454420004e1302c64000c507643c1103800c081d40464101300312b500910594200044a00c002148591000c11440c0c01ca4406855440c80f4055582545d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 930974001 1250 930972751 930972769
    0x2110020c03161b0605070b0a09030c05161e0f2606010303080a050f070c080f0f0d060801111206010309140607090306060b07030e09040501060b0d0c121406 68
    0x204095110902a642212005802c0e90000a120700c1c2c1d040c0903210340d010180865001070340140c007400390501c541c40110390b2040c0410f07031100c0d02c1800040c0781e240b24902990507820800b0042c19030f103d030050011a0520103036002007920701c1001707100c04030080c8210340f00c2c0c44180b03030290102040c241c16003006503051003814020412400300316a041002441c04552905100764002e40c0003444020910244000030700c03610f90080c101e115242c1803464080001391611145100003001101d0000380310307441035141c0054902405003c820b00d0b64039850080e01d00c01400c500d018082040d480c0100032501c0410740c42c00c030b58481c8070406040e1411fa48800054008040818090b14100c000c0c10400f0800c0c41c042c0070013885580385848d01c0d0085811401c3c500204c0f04203030018400c2100030031003280800e80040c0c442103500c44c01c0303951000c6503596107001405040360398801c5203000008a15003a01c4001d44d0130050f40102d840e1782e0f1824050180b80c564041d03485d103201e040c05a0490784003044880c2882c17035003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 930975251 1250 930974001 930974017
    0x9081801200105010312080921130e0405010b040615080a021c1a0307180911030109080a030b0307050a09020306240426060c13090c0509211002 63
    0x407807181405040c8040720100c400181a07101030f5503a10040c400c01400590300c3d00300605515080e0007600d80085015a54002c901034416500b8600c40d02030710715100d5a086556101080e002e082c10325598008611b018001594100c8003942005562003860409200c0c1c00102e40d561007442941e48108002aa130070003010b49005040da400f041801c405801d0190000041341e151040054002c582800e00e032034062a0180c054802d801c0494208204014406480da0b00d80190000103200c60a0303140428080107501011303501035080c441280305126880700601a03441080c5c44c107007c1425544105034039090540101544624032000600080c81d580e80a1640820701800148644941c0c3e000c102e5131611089080c032030715800007801d201700343c0c46018804100200c00c131182944100c00703041a4592000600c83d800301c5102061401d462441c0114000081661000402180702c244400920030b5109030b0041c0e004032400c001010800c0034071940d1030002c60740c0b44041c050242c3c0d40309025000c0d500c03640b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 930976501 1250 930975251 930975257
    0x20a350d020d1103040308091c0e060d050925080a1401090b0a050a0c09080a03080709150201090b0105030c030d140f04080c01170405030711010504031a060306060409081801 76
    0x404003911000c1c80c4039203500071844004044e16071805190041c0341d0322004014800715041000c040b200882d503078402822000603802c0c09508a40c2c01c0c80031940e01c0c05980911444141400c0038030a8440010945084040c10200e520454140700b502e0745903501c01c1b034424031100c6c0c1d0011aa01021904071810942c0307605a10002194071030342c1e510380c0c518012050703031301e941c00319910028844150300600c1401b2601c152400c00e80c0c003c51411110940b03480b0b007240080c1c184040c850014203614811000480503280e92840c146089607141d000034001e114202c02212080340c554004902807500140c00361f0a0000280140101d854007101114185000c4a400950b0394003446030120351034220000d48003030303c1188002d00b42c0900030703000107000d40ca4400307614803030f21000c07014040402c5001c81140d845941100642403010039810040315503100b5648043c000d0000327004014580d0b10344929441c090442102220300c42d0700e4407000c10080741c05421004100c1d010801028044c25030203840078400000c141 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 930977751 1250 930976501 930976507
    0x3070f140a08010f060512010b0d080304080408070e0a1404051f06170f060f060a12020a0e0c130e060a0e10240f0507150504051c020a350d02 62
    0x1402803e5a84600d0602e01c045d4a5001c14005420480c0445140b240300d100203000e0114013a02091414007034a00103440301d50000001010701101004540041c0601c40440b0b120300d548450041441409450818450741000c7d85010345000045c1c0403802030f608000942202c0f481d0a466621003500d400128000c00e4440070002140d2031030000d0750101a10030b40191034070040d0b016032241808402840902440d10b01002d221580e151024000140c4601200080710034100b17000003515510b071503104c02c41c41c0c000c8600304200e42c001440600305001841035115400d9803244035514904100310b0b0740540042d00c1c444204008401864a140c02200d0415040e1245e501c41c5408681201d1600039035138107030701d2500201c140ca075100c1030000e00e070051803400904082c1c00f980d401c50070183e140c02010707a05407144041814000107000201d00d00b03501c3c81c4056074021070140044d454038071000c0140c03000303101a00340d80040400050000c42852925040e52000d2007045000102a040340201c0c0100c50b50074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 930979001 1250 930977751 930977759
    0x10b011413050a15120e1207030e0a1d090601080d0c14070602010c141935060307050409080909090f060127180b06060d14070e03070f140a 61
    0x92000d02c041c016150076600c90760090310b00507041c0ca1a040038014007600c2c04036246d0300044046000c281602402c1411a6641481c0c2000c0f21204401d0000d594010010100010788007134244800401e20309080000b803041c3c0e00ea6101c03a0300c40c1c40c00d205016440d0041d000c90300045100c1c034001c1c50002e100e4807006a00c3c00000390b00c24a0a24150400740160790b6440c0c6155140d50080444401c1c040d2136540c81e864024414101d0101c1e04800303200d070040c084100ca0306000303020009801940c060610980c541c51407100041e40040042c142d42c2c00780030780101c820100b50780c2014001d00101941100c4030514041075081408001c0000034003c0070315024402014000d41414081301d4024501e42c0c0314018503614003441c0034141962a40d0410b845490070fa2400034100d5644100507000360014100502d50380c030000441c0c1350348150401010094034200309003040407805084140168041d940b030003501c0040d1030a06a039983c150107869902d00c000e00b0304110101d901d000c000500600608040400caa503 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 930980251 1250 930979001 930979009
    0x1a0a06170a0501051b0a0f111c030e07060801170c090901090b060a03021e010e030f060f131a09031c0c02162d05060a080a0b03010b01141305 62
    0x10545a4009a401007641982480024000c0d982c200500391803d120315000c1c030200f1122413042c00034400c2480004204022070300c0c024010350b00c00103070100580d61034094120b954400001d894517440042840d080481c14194400200581910804c0e00d4040c0301e6420828803842000c02c84501844c0f621410020004c661110b00301c850103002c4002c00850400210b01e0150b40c5804010516030160b1148a810030159503080c58981150f004404800601210440121980d02d11588081c3d0184076982c4501030000001070658410301080c2d40b03020301a100c02d101c1c078102c03803182e443c05400c0b04490b2031001d041034001900c0300d401144800460b0710b0103144840d100d049030300c032480c240000d03541c031100302c043c0540500041140768010482d5a002a04088141402001c0207030125094480210880d00c0041e900b9000c5015050040c456525104565001410507200320740d220307401401e1100c6d04905003030500807602c090314140c50302105403410700881149a0800c007403d408142d4004400519521 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 930981501 1250 930980251 930980279
    0x601022e090b10090c0e01030e01111603111204050105030c16080301052403070e03070308070c050310020c03031909150b1503010f0e0c0f0c0105060f010302071a0a06 73
    0x102c00c0c00340307101a181c040c1c000341c0b007003440303512a6415030f0901300482c0c02c25611a45000100801742000102e809101142500604103407142004a100008100c0c1d134200c88bc0c1440c6407030601c40d640e0030001007000c2c0e840340c0d156802c100c0846108c606c140030a020542c058005036600c000380034902424801c6444010300f1800d000c22040c2c82c442c00020043c4242d003007001080745181943c02c0449aa40300d8a50303018050302c0010324030030400c07040e80e041030b400d940c0603c0304000950300b1041c0c9540b5076519007068071810002c1e21403a4402d1250100d00705c16460140255410121454040c60443d681d18404030b0482c0414030700c20200a070340704201800100001001007814045500001c2c0080052040c851521a140c0c8003480700039060004004103000611000c041e00c00c001801a150340303442c5007003c42805a5102085100341c0841d840d079003c401503205621410b0111186031138062050015001c0b41f191240142980f541100c0d50218982c1545060341c00c01c03108013000490139550045039140403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 930982751 1250 930981501 930981503
    0x209042c0111162d03110303040c1a070203060c040504060f1d19020a0206060102011a0904121403040311330c040b04030305091915030b06070623070203030601022e09 73
    0x644da40e040f410a160348104245c50f446a40700007140f03103061603110803c040001c0e20500c421500d402c100c600c00710140c1000e132500183e010703084a4140c01c10380c492450540040c0100c1c0d0046150220001784d001c00e4820200c00c40d400c1c030420a510f00a22a4004444840105022030845494402010240e290b100504011200f54050701941c140540020301f0755000700740d05140c400074119010a580e84240710745401690141d264001c0080210b003e4420501c400d000850644c0d000c4108400e01d030700012007510040d601d42c10b452040a03039203900d48145100490106c104221189090180d894030301d0704a42100b85604090304240c0c2c1c84888050560050f0001c800050000c1040042ca04000717050000c0e00201113180c034a203d003007045a1a501c064060580c1c00c0549400ca5803c09031500d50859403910f802c81c40501c0040003130781c004400c5000403a8241c01c069010800102c81c1840403040d207000e130005038040c14501141d8051240680d80c102c0420001c145002c80c0c0c5265146144520740142e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 930984001 1250 930982751 930982823
    0x40b0d0609031701060c1101080105211905030403060f11090103050405101104140a030f150908031015020706211b08100f14040f0209042c011116 64
    0x492521f1400422907070068401c903040c0805000180450342d2003d41c0d505804009528420002c20f031110010320f440741020325120f80074499002c50f4180900400148103036400307070303909120000c10302288008079110f001480d0304d101d2083c00303030240c1988290800340e0014091022500e008045601b0042120460744079079054040002d000c00118110303400c1c14072500c030100c604c000035510b10348a18000c92207047d0003c10050138206030009820940e8000d200c0303160450180c0d84c40c0d00d400120044403c5c02801100182c8072300e940e601d0a01c0d440000c2c0c0342c0076140f46958610000038445414600074029400c0290071a4803140907489500c011800310300f651195541d41c0c0d045082c120202c4004410a0300075404007251800300348010f4107070740000310070003106440c002030750303900840e120000740682054682c7c0b05040c0320350004a451062104000306801000c94140c041c6c044845500321040d015400c000c0e100180030301d0002001490000350500e0050403036036400003000c401102c00c0070a0540403000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 930985251 1250 930984001 930984017
    0x40c170a05090c030604170f0d0c0804020a090b0d02010806181f060216062d0e0a0b0a0c0b180d0206070801062a051f0209030606040b0d060903170106 66
    0x10300c2034100801c4080c943c2c107901910301c50906880d6040605421240000c01c144001003011000070150201c1e4080e2089510411003056803810090610300141c80036807003903400c5500407030030700c2c500c0c40b44991003600109925102d4607140e005540610300204042e92011090541e01c070142030200d2503900c40c5000b501c0040c1504501d052148800140d50003110445d4010440f0300e070501c0380d50040c0c4d0240e80482c102041d50755170501d40180d16000c203040001d240c840448e401c00301160041c1240781c9244c012160700240c42e889020082803406403c0091001591869100020800007440c294100c0301440410341000c0e000318400b890040030030301200040c0d00003010010042c0d408104240541054130301642080e440c1504403032180362290ba80d1400c040403031040c40401c0f004200d0304503c407900340b614100f03a00f0a042e00c0d500a400401d80075019000d00b00009006180500c641e07549840010a400c1d810340722500c0f00c41c01050030040480034000405003003aa0a400b1245090003440c29540d20f880c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 930986501 1250 930985251 930985261
    0x40504020c01062c0a0e121801080105060a0c150213030305040e0a060303140a02010e01060602070f150906050318060f0603100c0912080d3e030402040c170a05 70
    0x1c4441012800302c44d24140310b1303074040d07064642c0c000140d82014070300001143d00c5070401d68403420700a01070344805820000040301d0b1046040d1138849100e00009884885484e0390716070a000b500c1c40380403c800c002800c1000f505000450720b07015550f0010002d8801401e010940f5400700a1130601c0c0c00030780210740c000c80c0030065003c0b10b4030714a80c407401c0c40a05001091565601800be40744174642d0704100700d80401e06c0f00409100b584540340b0268804000e200140da141006900e89600c1d0142600c521000c0b5004078803e02d00611a0380310090303c1e41d840040c1d41c98050200c600d07410107000385124010000030783d0f84201d0200402e43c000d8002154052144c1404000c040c41c180210300c4a04071075044c42c04400f095030b00100c6440403a80320303480d4600050b1052500c022980f00781c00316404030310f25055040c84005880306555902900a6800300b4841c048484801036100215107484404001000042d0040c20590440e800240c1d03981031080042c0c170362100c801c00f11401104d410340440e90f80c00800c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 930987751 1250 930986501 930986519
    0x310090506070306120b0a021216020c030703171c051914250207082521080d0e341206090309051003050103110105160201080408040504020c0106 64
    0x140d0400e0b80e80c2002c110552134143e0400f503200b07002c50041c01382c280c9940056401281134040380c00c0046603032100c909501c3e1400324030350780750a01c00c02c900051140000325001420002545030540b0380205e0840701c0c0d0034041c01103106a40c00380400d03910841c8440e005210050050154501600307500285100a407200c0c09410f040342e1030b0030b00c0200c80d1201182403000031341c5181c0b040a0884c603921000c65100c0c10303001c1d05900d00b07070b40766202c8042d81c0b04c0d800c2406004084000c501c4410012000025105075480c2e850005041804584080c040010500800081c50400040041ca40400320100b15440503800c41070505c1c0610103030301007140d9000c00004101608410030403d0106039480410010b007006007049580e80f0b4020b004050340e684e01d108030181402000c00f18000c101c014201c5e00c40999040005002d004284030445071240444445002503005000ba1102c2000031261030644407001e400446103500d02500644800c102007001007002e440394001011800e91b40d100105980c2e06d450603003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 930989001 1250 930987751 930987763
    0x8071403010510030809090408090d080702030d03020a1d2101020a09051e15070503030112030801051f0810090204120506010b1624022110032307030203100905 70
    0x1440c1c1443c4400e000307000080200f81a2020010300f6551a000781e80c40c1d140079411441039505e180c3d032085004c0041800c000c9144c00400c4e40902c20b9040c1c0d0241080860160140e015030344d0900302203501c3c0d8001701c07115102007004040301017004014030f54081c0000b41d101a40c890840349050503035000558902e640f030b0040c001c1c10042170b040d0b0740c02d01d080c01c900e4480100c0e100c034114164854010707403400c403e80300f0a04099944807900541601d6480d41d603041000800200c0305030031030200d03c68600000741442c0c040c80203402c030441165400c040c4160380204584103071000300300e8040610166400314602000d031000d08080c05418690586408403400c0403450000c3c1684000c2c10080c0c200101410600028840c0c405560320008490010252042400072040072580c0c0341c00191000ca0f0800c0e1242c0fa024900328100100d034000801621485241c0c02488014080a4205000400101c11400010400104110780c0c40c05490b802d94880d8006420f05145d406903404131038650031100c3c248a03086c001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 930990251 1250 930989001 930989011
    0xf0c080609180d0c0f0501150f0e1b250b07090b1602010507051f09230d05090f092d0709090c0e060c100b040c27080714030105 56
    0x3405240b0360b07001d40310b035a94140c8018040308110f00c007101c480400c8075620845180a510030000c0c4007910010018907813011107031040c0341000e40c20140018010308140c000b94052041e10000140482c0e803d2880040e48d8808801c55a21041c500c2002d00d9000e0045041c02c51240f1411102569090881008110481e5a0022266400e041041b800ca404099600000b010350a0a020340c681c81c0354100142007891749050b581c1d0072001061008002c88603036005012084c072030650203080c04040044201c141382c40359010184c50b844204903403c41030196019040054004041c1c2d002d0310b40100100f081040c0c141c81d280b0410356070024007007001e05401203a00d94081c03c0080300c4035a150065004041a1841c4070740072126903a40d80c20025140f04002745000e42c500900312a94541307004103450340e00c2440c1d0340403210f403903d4114014031600e050300800346450401d0360b81d5142066641040c03928a40c1c84038010100749404800001c0001081c45007070000c0c58515950f00002c0003a200340340c00e680340102 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 930991501 1250 930990251 930990271
    0x90f0e0d0207050f12150703020a1218201c02030d02010504020a0e07030f06080a0218060d02040203090c030a050703140703170a031512170c0a150f0c080609 69
    0x703414449a2035540072101a0001128500c500100601d0001d051010341b0425950182c140b000b0410082e8040d00104404038040c0c7d584205580f00c1502c50040340d55107945010500c04c0144440b01186080c0e40140c0012030750042c00f540c3d004624001190300300c40540f03500e820307000b14040c81c05501d030a110314044080540020300041c5055400554410803038051741c07010320540008244198821b0b4012401014220301c00c114058851045503901d0400040882c401d00c80060420000841f440714203000b01005003054500ca41c40b6400c11000e504010b041d00030328440e514000905a40c100f210308400707406103006d000c0d1300d03046040c0120b400368502d41da2150342e17101c500c0c10030001c0d18071508000281058071644d40c448981c046e046000e00171030740a00310f01e010710b600040303080ca1002903045559440307109042c0002c0007000c0840500d02902c0c0142c0d44a4005030b100d41c02007000300c4440d00c19980b0207100010702d0f0300018010b4040310442c400c180c0015485804010207410001e44e0f40d900013403844 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 930992751 1250 930991501 930991513
    0x605011107060509010804030c020a031a07020715030b0609031b1002010204030b0403081e0a06081b060415050715050f0609060a060f090305060435030c070804090f0e0d02 75
    0x2d03400391181c4140d0f00d00c141000303056070004060510400d03018002c01e03401401059070964070300703106e8550242c0202c45403000c0820710100d40424000100340d01140c1c1c0c200d00603042000b156070f00b42d00074030780f010420380c0100017048090001e030380c01d101c0180e40450070011850320030005802d0043c00c0317041180d05d800b5603104000500104060030001507103da4546003180d002d5440603002c0f00300361613603d20518801624424030540d01026041031043c0e60004040f00e05612183c0c448a400c500c101d003909030002801c0000384040c2130030b0008440700720664103101c0d01e010929554a94803a00d08044d4510081c1e0303440902c140108801c80d4a03810034003c031030441050030004001050500c480c45080244884130131010803c500509506000316005020f840d91032905003403c0c8131003901c540f9414408100c803d00c81000003904402a6440075900c0c90160075695070740d490b482e03036a00415095404803000e000014488266002d54940c5004800c0c0102d828200c0c000c5d990300c0d00001440610031744d0803134 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 930994001 1250 930992751 930992759
    0x100e010c0c2907081804020d0c02060603010c0c11040c0e0603011d010603020f1207020f1006030b090d02060705090a090c0512061e0d110a2c04170a030b040f0605011107 74
    0x442176600350055001204d040508220004000344140392203041240e00f4410aa5005600424161b1203950154001d020803610410201c80c2110013030390040c00602154011040c03400e00d6445054802510301b0400c20308482400000c50303d4209a004040e8003402404950309400813a03221401031401d800c05505100e030ba248040880d000d40f20b4000d60a00002d03000404842c4200074641c0c4469808096410540340c00030718034054903082c04192032204e426004901508800a2600a400942d81c00b80c01551039015003110182d0104103207561259a1010129241c4258411543d442c14035880d16a50740c0405052101401c800820003403085106403203080380361460496459400b00200c1d00e1403c0c2d1440c52800d181403a43d03100d100d41c1c00801d8640c01207014942c0752000c10045000d100d0300c2d01c20300f01e845000c42d51110122030080981e5016800c1c221000780b554090001142c03d8100490300d031401d00d020604a0740340640800949450f140100091750300440e0b1141d20751031810143c0405810 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 930995251 1250 930994001 930994013
    0x70b0c131a04031e02060d0b0307120302030a050a0e091806070c11040b04150305061b09010f0c0f0605040321140432010501090f0b100e010c0c2907 65
    0x1a0744030142c4502c010101d860610824411242101a07000b0140741d10f820301141d82900038160290403e0080c0309906c0302251030b18280484bc03402da03526a0045203880503202007121241c000070707900700c18041250b8540308240d80b0168118484c0508413047d5102050b080c00c40d03480c100000d050b0b601440320300580070001c513100701c01d9220560300540d004078150350100007240c002c0c403002e04102c51124800c0300c007004221010580d14002c0d184545049110440401d40582c54492502e12034081170008207403a103000d0150329400300da503000d001180480021500c44070242c0700c044408600003002100c07002c041c5542411428064a80480200065000050322003070b4000c010b04090100c100707110300e004003c00302c00550b205100b08901090110746032021400e002e80400e001e2944258140b80d48140c0c402a94850800c40100080188544240020050310110009625141048041603618010603034540b84070009202c01800604500d0664002c88400c9200c1c03d450201c10404100c41404580 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 930996501 1250 930995251 930995257
    0x20d180308070f1803060e0f070608040f02130216030816050d0b0607140a020f0103020903100504061811090601030e03043602220b07080f070b0c131a 66
    0x1e4241580d8810305058140c0d4113400c026084800c403c0c1d059404410800c083e0022882e032060072080390040c0402c40c81c000d8940b8414091400010340300c1d030008003c14401807480d00040d001407c00c40204a0858180d410b90703103c0040390825404482002d0101a0b00c001160381c4000300345101203855882c100010600d00c500e410a580380da854030002c4561340d840508450616600c106006459411803000e2074413091104020f9125240404003082554000e000b15034010704000c010f00007200c00c044442000b482d0150090b10b0050b660041c7d285003008030b00360742d08038500030161007a070141c0440c02c200032070000a1495040509200f00484d00300c40000940d8103903400c0c40d4000016061400d0328240070010003e1140d4040703000c4100c0c1c00a0140d541c0140910f4500b0002101020001c0c0542d142500003445145002a010019079001c500c0350300203051105402c0d94850301e020450b840703e0012400940302001c4010002580c80c0e44c002201068500030020a501c2529403403c00401240b540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 930997751 1250 930996501 930996511
    0x23031c02070c1d090c010f05040312020718021c0212010510050c060103031e030e06160c080c010e100902100c08071a0a060602011506270306020d180308 67
    0x94010401d0410000d807001e07048040c100d492001001110024440d02e410001515000f0381400b030800c0b074600d00c0d44078005400307610301d0548802c0d1070070346541d0710151421461803414085004100c00440c41100f03224182e00c2c4e10035410070168460700710918401c069003940000e00f2400e40704001135111102c1c106142c0d41111812140c07203201c1208884151094410b86008400e180621800881016004402c040704005002d552404200060100317504642c0203014241c1158003080000f040281c61800d5010211005e280001e150405603031081d000d604050356841960351180c95440c0b4141040000c504c400701d07807030b00902a4604c10380101e039144498800150402801008050910948004a40c1580d40c40031441d018200040c010f00030b001000d0741c0d105041d501b0103a000488520500030300140700341c50740c2c90803a001e141040507140c0001c070406110404401c44040c0048691422400c0e004501a4401581e21120b882002c012502031601c10300200c3d50700c450b00c1001c680c2c40700b40c0581c01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 930999001 1250 930997751 930997807
    0x3041404290114340201021209011202040305100c0810060507020d0822080304080c061b0604110406050607080910090f0b13090b150f04030c032303 65
    0x80c103041c801225040c648603070b010074031000001d000003d0b040e14181c1c1c40d40783da0075400c031820000000d1046901c0030843d100c041d00590203007901c0c3c2e40d1212003070010201c4410504204134200c200602c510180d8010f9401590707180c015041400322108540a05900045139140c01900c0d0314008804a49002a602a030700030004081000c404645a51041c078108c2a000602c6070344480400d01000e00701403455140d40c00115529000080c0d4400000558081d07441c600081e05c0e041c4480c1061201c607030402a204000711030301c0c0c010700244404c248041ca0189015220700703588002d005c2c00744025070340143e014034002c5104000000120340c080301550403140048071101050007030302e00121541910390300703c0036111004080011301038a51100801080c0660741204225a40c2d402240044610312000603402407100306500000c00c0c00f010040c2004083c4080207820320f40c4940751030341041e016820459011000340201d503001c1e490303071141c90030400c0d69000542c50004501d0200c030621040001d401d8413 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 931000251 1250 930999001 930999071
    0x606090905060402040e13061b020a0605061305010612180c03060c140f0a0e030303010f030201050304080d1d100902060f0d062c07110303060907031b0203041404 71
    0x695032103804860040c006220014402c1c11f08504da155a9154840204d45091401d80f15040a41070b04030031052600742a0040e2102c02039a45038100948001000a41c1c00200445404070303484152042038080c281542d50700c03a4040a424810045802e200b070301040f864030200c40ea0340024082d10b0f08106a035030085001c500e02e0003000040d60010807410b01e44403c440f0103d2800380b61400b0344050140540c5d282c0d51b21080c14556014151244002c0c0912140001c1c01ca4051002d94000c00c0250f4015100381c0c0003d103480c2c407000c0004125850304020107080da81c03c90604c07a088804115004081400c1c0400b0400c64800d035001a01380c0c0700326503070900c1d200b10100c2e000e030241c1800da004c10700414070b161055604141c400e5884904040b08541e180c0d0714000c540201741d90620070000325580c0b4070a50010752071a02c2c0c0e0420040c4040e4010712200c20180c0341c801d071030007010015801141c41003484c3c005644480c00c2481c4c2640411141c03602e1802289402503030038103180c000740458440e105260420308 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 931001501 1250 931000251 931000261
    0x80a02130c0509180714122d012705070807080c16050c0436140a050703060e280807050618060c03040201050d0e1903030207150606090905 61
    0xc8a000d2103e400da8094141064804200b1082c2e1540380304a541d640c0b03c1781a4501c0c1d0206280c41d01030421003400302c01e4000c0000e41c26003071680702e9618460040700300c404100f0382ca411b0414440d0b0300740c2280300300c5c000b0342104400109550301c0d6407a143c8044e000c24030203498a02d8004044c440003d0140080218590208122451040c01c0302d00c000c904032041c880c46400c0d810442d0b40c51075407220031405103161401c4c807a52046904040d800c0900010901c01c1c90010380b07110383c1e03081d80458009403204020000c00780000d6908101082440f4880c0d809407200d01e04c1c50030130400b1035075031b00b14150395900401e80c1961401c1075142c1c4610007824011030208070040c01d0612210700d005220000f030142c481e41c410300a1403402c0303480540d5440e546d4402c850850741d0350214000075001c240d8009002c20700510070b048008440fa0030030100c20013003204413100062030280c0140407010b101c03020340c0803903030024002040c400071141590010b82010b10600170320b85000001403952405120f1091040d54a0010030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 931002751 1250 931001501 931001507
    0x902091618090203090609070e010902070204110c0c13050106023307050c0d03090b06091b04060c05160803040302190503010603030504050414060a1206020d051003030801080a02130c 80
    0x1d1550085150004105494841010084d80195905d8072a482510001402e004000031004262110000e850702035920300000300001c1d4201c0b0408980c0300e40c03640d4050185c0700000c030103001109203080040619000d42c60038009101518080c18018a0804005018482e000200c03042c6a600000814640c00703022040a1000403c0d1001403a590f02c1c60760511008551146c081d0210b9000901134800344041240c06808440078075800508401c0c0f04000101c407850400c542e640e205080b250b251460020305901010250700582042001c10300e44902c400510004016030301704819412003030b03d84107040540703859482c003851000a21072407102c407201e8051180860820300403c8003070001e000c0b0070348074540036005030402d00882d03005514088040950070341d40113000e400b030380c006000c101e0700030708109806480c40c00010007558001c2c1c08100402c0c80d0703042d52184c648a02c80f01d200551701c1d1400c518000b800444107902c90150307a403003540c42c0c20160360340c0c801d1003c1c44240341c240040d14001c2e1020907 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 931004001 1250 931002751 931002767
    0x10c050615181303080f1603091e05010203010f050306040b0406020901020f010516030e01053d030605043005032d04151802060f2505060a09020916 65
    0x2550602c5840b0041c400f400940c41c480400c4548241c9800320550b6070103912100d600004c4070350002d440c1e568090b001409020703a008800c424000d41c00c0401d10030b05c042800e4490021490201c815a41c00801000f0300c104542003100034000c110050101824661102022010040c01c05011158000745030056a8001c002e00001031018038001c0c40701e4500201c4035400041228445004681008090700441406200b8035115420120004014016000c4030445604d207640420342088a40121030300000c880c0c460a40082d4440c801c0443c0d1890589092042c0103c2420301000d08a0180c038101c05c0006115810440f50701c4070310300141c80c7c0d500c4100000c10000c206081321a150206040342d0541c041281a2a00c1140190035420141c02d80760700c6c010840300c0041d9103000804a6105200051500380c005080d06138010344890f00707145000051000d003907490003507070904220186440d800c1081c01d1003400c0c1c2c44002803034200503180c0c9a030080750003c40028010241d01d00c860501c964854021001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 931005251 1250 931004001 931004029
    0xc0d02030304090c110f0a02100503041a0a2003041b08070b130902031801050601092d170a050106090212011203030f110702011e05070b0907031b060806010c050615 72
    0xc46e54980c2c0640c00d100c0e110300f010102680110150124190014041c400f00c03406660310685000521038820284445010023401c0018a40d0b12911b240070544040e0080c0340300ea003040040d036644c030300706440c104d0544280074010426510703c440041000400c007103104400c86038103001880c1c3d60f100c00140203140c0c1b540350300141030052010051150803112080960340f2403030810000c204036104c4000548032200644580c40b00c00007101c00c0c0c5a50036984e680c0c102c98488504002000264035108070282400e030070844204503034000405034007488400d0003100c0003030442207821443c1c064610790720101c120f0140523641c2071a03407682642c010103120382e0051100c4803880b40c00f0400c0710504000280300d03900500c030a90010b82007080e0500703060508418060040003036120689843c0e0b4a03500c056010000408000180c040e0b082e00201042c0a400810f8103201840780c1354078403500340a000b912442020b40010704002107a0803c1c1d00040c0c0001f603482d006100c00c070688040685140000385c01d0780f80e20075 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 931006501 1250 931005251 931005253
    0x10b0d09080307030f0b030c0906010f02190503091905010c020d1a010f050a050a0e0414190506010f06180b1305130c110f100b01090b0316020c0d02030304090c11 71
    0x20030810f1095040c2d00004a0703155884043c00242141c0081694074060710f01119807101060b03001c10f0143d0f0084080443d462281d006852003001c42c022800e10b203040200041cac07101d4100286007080792420200b02d10a6a0141800300b64260034003000130002031012000034040c0c00b008850b00140300f80c1102030403503100321501d000c0140d0b07180c154100e200040d91003418020000740384041102e2030501c6113070003964103803001010181d80c3d548900f409104e21a541c845503004112989611000110050700c505008100421003940741035040820f202d101c0d031000c400c03c0402c900450001c100191404202ca0403078981c03546454800042044d0316450342e01c11540042003280440c005441c0d43c0101c0c0007214113440382d11406401c00c482d1500c031070030400402c1c5281c20805080c6040e441a50040711400410300d4250001f07a01c840400302c42e68030584943d00c4001d00540f031504c040d40d040101c01d25459003600d015995031070b16404a5902e01482c0a041400c2c3e07207c200b007a1045100710007070080c812000b0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 931007751 1250 931006501 931006507
    0x62304031202010e0d0e0603040209060613121e030e01081005120a0b060108040321180609020f0609011d03100c0f03050a021c02070201020c120d180806010b0d0908 72
    0x2520182c02030a90510040417805840c0b41c05007858001d4601101204001c2c03d00361450340c5550812603205401070455502c0b070300c180070340304008400c0c601c0040039002d900015441050103080c4000040030343c10b03109540c2948100303101c0001c2d41c00020005113010a091986403a1540107600542e045242c005a42049090500d12151140096504561800342d070348040c198690f04011140007800b12000741c081543d003443e0b00c4103400258540e1400703150403e000640e1140544a0210b0100c4828064800e1034030b852402040d4540300c46100b000c03141c11200b0614040300d81c0d0018021603422042d09119036002405c26049407418090322111811440080188008881c0040c00b0791021491000c0060302d0030001950b01e000301d10840c0c0454002c0c2005404100c01c2031211030107503001850032411401a090f20041a032507900b440c91030642d500000d003c6840450307100816070120f244814010b0701020a040100c2800401d495044d120f200d000265a81180c0c0c4402010700314101006001003000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 931009001 1250 931007751 931007783
    0x3081c050c04030219081f0e0316120f210617010903120501060c2a2402062a270f030c0306061c02040e1b010906230403 53
    0xd0000c0090300d108440003205d4000c00b8048250b05150390083d01e00c0d55011030000100100c03054403c1d03401640e1702d40003142d004070b44550a4250b80215458107800c95800c1074150421000044c0720b4801c1c08280380209240d81c06040007011540b400d04416809500c0902d00b84201403da00000040c0040186650a0041e1f03000c0c1103000307049003101900010000b0010142031781484c0a401c2c1200d001e03584541c07081200e134603109122080301e205544201d40c01280c2407400651004a0401401100810140d1202e0180a16030341d900c1413124400b150020410850007011080840c14610550000d540e0140144124010207114148485644810f079900c010300c0b1040c000d5410201d00800c0e507104010006010500d50b684004074041503042c2c02c00800580ba1341000e5000c2e5400301d800ca01da0620b14161a000f28007110345403480008182c028604080c2c1c00e006611030059990000c0ca08858854039145000f40603100400716102c0e24006401c00c003d1082c440d5060710040d582100c0511010815 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 931010251 1250 931009001 931009021
    0xc0c031209040c0c03020303040b0a02161b0803120408090d0f0605010617070206040b22080c010b090c031b091e0a080304060f0c1502031e0f06060403081c05 69
    0x7140508510443c180b01c0714881041c0b0490348640f010340c1c541c00442c190f403160394405002500040119902960a00c04c03005001c50000700d108aa9004810280c642c40b80010120440035050f0082e07607065004000e01e10101c01440e046503402a000341901e515400340c0b01c0000c840551a000140504986c1c03a094800e002d03180d44400d040f107105403241000000d2030940c00151100481c0c1210151304417034002004100c50700000b41d80820720060012440c0c822041c0010044582401030354854000b05001420b04024420100281c004403400f4602c4c2c03800d0f0881c0305030392100500100d0445002081174440c000054161660500010f0850f09a074180d001680b80b174034401080e0500c200145200000d440341d01008a9050319160340d92486681040c000555000200322340c1100e1001444440300c54890030703440514010368420044000303802d0040c900d5010480f01070910103100240340140940f90343c4080864040b607500495943d25223a4400071981d007802039010515509040804101c20752907 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 931011501 1250 931010251 931010257
    0xf01060b0409060927210c0b01050303030934090b0301050718060315180506030618060103031d030601090204080f0a021804210c03090b1606020c0c0312 67
    0xd500b07041080a65a113401640c2503401c080495440030009481002040301000780703411403035006200c5070a200f038000144184060fa80c4a59000040c046107803c2c08000c107820015004040440042d811400c103815950303151740110903140000c1001c40c404911050a055200800c00c0c039040c1e45031051035540c1d80c450b0240c502078184921952802001504480c00781ea0680300c0e01034080d60b2403604501340b05c8241c00800c00c1e001c030389100d081c600000050b000c0210b031b520f50500c440040c010445050030790a01d0703c1d1034006004101c2c41c404c40410840301c80340000740181141e8051070180300520071451055040d1896411003034060151600201d15000306400400881e00180106c48107103540204564560150b2040254000d0010210815580400f80d00c0c51304980a40c002043c1c480f54a0100408054103904110200d41d0b0711103030f0003e041e0040072850040140d02416450700d80045411896004400742c01002e060b80801d0150440f001004146030154001d030403640d920048550394540c0350 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 931012751 1250 931011501 931011509
    0x3050c01111009150b061e090f030a080d06120803221b0608010909081e09090103120906030c020d030c11010c02010518010606080a050405190b041209150c02030f01060b04 75
    0x1400c2c168009041d0034101c007110080c000315980040ca034492401403103a6580300700038589e800842180c8100442d9410b00c8078166040c1701e00246a600d00c03202c640901500d00c81e52104c1201a20384104001040f0004102d96004400c5143c154003aa041402c40e506d844c16100c01800061085104101d0088001141015500746859050b51030b80e843c50b2400551302041c40c0101000c1301840185d900640d16112100c82c1340e03526408604117040400802d94107a0300342c0c0207517480c03146031801c01442e0780c02198034809020b540c5010700204080c00b078013950f15841056680c08042c3d480104401c9a441a100c00301da0740c0c00c00c802405078000340030000740079140c107440301390042446040c1002c900f14144035140803500242c6030038131a5039500d80c401000300b4004200343e8090080e47c00c40740c081504202e140729010f1044819140b142800d0802114020130f0440035000c4c020700c80d07001d11448981502c039042c282d4070ba14003400c1200c654804603040500e05281032032650b0800b00042241360784078021384103032 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 931014001 1250 931012751 931012793
    0x1e02030d051605041a1b06010e0a0504030c02092a091201201b06010603090b16090b0d020c070b0316050f07081b1b01020106060903050c01111009 64
    0xa03446064001d406072200b03102e4500400d00801c410000708040000d101c1400c0c4244982d681030607800c5c0c021600c41c003502400725246422440c014894600c18459447d0080c0e0700030b104005900d0719580c0513103207440c40380300070703200f4075882001504c099071382d224080784203800700e4106038024440c0304010707004d400c0b4a9481d07106003c804500304400005100320340c1c80801000b00300038020065441002250700000c28001c1c68441859aa044000c04002c2039000f0b24150f41c0c001040c44682c1030050302c1440240201c0341e00e0280584a03200c5981c0650100d054600d00380c115680c807000008280001e2082d070b0440e111038051503100180d001c0382240a50b22404a03a10fa04120102580044400d84194100303200e503031070107014070f0020030710800140c00c290741d00c200c0e102c6c540d40f40d040e461490602c140b410f01c07400c100401d05800155078217004800091003142803600c03a480c190360702c113900c0300800e1981c44d0400c1044054082402810004901042e1000e5800c010110050501c2403004803040c080401e0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 931015251 1250 931014001 931014011
    0x1c02160b07091208070b13080a0c02040b04150b03090102131202010206131a04080702060313061d1203061807090f0b040e13150f050406061a07080a1e02030d 69
    0x10030f44100309481c0d038a68480d08031441c10b0215541c0c010017000184c00b1465030203c4003130a0000442c41002403900403c50740364444680c00c1c078410081500d210000e89401207003005215220040c03110012800d6891500ca61034070b1381e68603151140207005020402c518541300e4203002030200c10414034001894001c2e401c0e01c41075641c0d0b50040c200c1d01b83c00c80c0002d00e01c0d903c4042d01c61003030821201c4180c1183c400d03484207150103155000240380c0d41060744c0802140390304540100800c0040d200f0460180d10783d0742009150120210115294440d0504002a001000001034007030754030641d41000a10a8145000180c103000c02c005100003020f009100d0a00c041c40008121644000d090307404a468001c0440e1440d0b4454200c0100c03d00380300800c8984081d8500d00c6010b15100c1d00682a091121480010341454103040003415101c2c25444900c8001019080e011030700d40740c40440e0701c072640146030343e0ba032440b0344002155101c181082e01c00c103c2c005000c041090650100003082e442c801003031305000f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 931016501 1250 931015251 931015259
    0x31c0f110d14070f0e010210050403030c12201b010608030406032429041401090906050102061f0305100911120c151b0a031d01051c02160b0709 63
    0x85040c5050f580302010800018a1280c0f0310310a031120881c05c041072043d40c010044858a0105440003540c044008c41c2d21080d8200c000f50340170004c0458401c0c0d512046c010f21840d180c880d05c00024001c25101c3c03107640020040c0002c54a00c110300a901c1c1050000c120803030b900c41009440790018001d0100080c01e200011104840c100c08110b8483c44500180c1c0c1002d1070840260b4030558840c244281403d0b80303000050301441414040c00003409980210542901504001800a070700750f088407249a14000d8203000d02c0c1d070300042c0e0341e030b00c41d00c884100301d500b041c600f034980042e0305a5400100700744908014001c0900303503600301440443c0702d8864010031030200420042c8e618540f4a01c8a1154400440603015207800595080c1440154040f1880c010a0f070740580140141042241d0f02903104003890b108240d48660040705a400410400c0044c0d00754800003491441f61500c402c4103484098148004110503034102c4019104002c00140303d140240351081c0070060440701701002c030b144080009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 931017751 1250 931016501 931016531
    0x80c0405100c0302010b0a060305010501021002030108030d02161e030809060f0a02090f090c0304032307060b04060905070e09100b1b0703020303120a0501050f03031c0f110d 76
    0x2806841008001100401d8203800449a40d542c03200d0075070443d9205d5000c1c2e40d0f81c0c0c40c0c802486d0301826190340d0201c0c0960400b00060f141503228440d00d041c042c4100010000c0b590040f040d075078110102c1401503500d0b0050380820b900c100440e0409090112140044001d0546840d4402c1c0218404e441c2c50240341d403084003841e00e44d9400c03213910201901c005c0c001030301440550b00078040c96400400d554003444a41000ca00d4001e0121401e9255550004c144000d054210300000010640d5600420b00c807403846c01041c2d03240c09189002030400da250302080702c040c0e58503000356011b01080d40c410051840c100c98000c090007041c000704c50241d0300720004501c580d0300758200c04058a000c955030798a4062a55000b940100540d1616111030060303050200059400388000c050f40481c401d090350f03403810481c0d0700508407081a4441c91054200040d016441c0e00d011066646019441c00740c2500f500b9003003255800341c20034401d40c00d1100d00e00061800c19114000151090003501d00f03081100968200d042 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 931019001 1250 931017751 931017757
    0x1103030c030c12180103050709170c09150d080703170c0a030c050307020d051b0a050a150b010f0c03030f11040602100204030305040e07032414030a02150c0c031c080c 73
    0x84c585403401400c0742e4550084d040150400c59500e0080740080d81c0c0c1510301c11a0390f0b0201c80c0143c941140840c00320900c0c040c040e058001c00300310004250300380340300c000a00e42e981004d001080c5200220310703202414040e1100544283c1d100369466814600703101e0400c4039034480c48811000c40c1c60503844d07600241c810030640388240c41e10b800a1261603080300f030a941075003006034908411000e1040f80c9003101c60600c0342c034000c13070f1003080104184c014900e000760b42a001d08460044c0740b4501190415183c1c0d1290b00002a2411410414415401810100c01038465050315980072410410b400e0301074404d034401001214030590990f81c04810f0405510144c0c8a680310107800208140414402e400492001e190071516034200003c01007084061000301030700d01d040220098080c0c01040040302031604900202000440207420200c08543c002900e40780078201d0611940008649012960402c000c03c0148502c0101180c07002c2414003242c01e4001c0000c1c0b0b254000911007400310f64803124280903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 931020251 1250 931019001 931019017
    0xb010e0115230f0c0a0303061a03130b090a050109030e010f03060e04060c110a060f06050303090310051506310b1204030e130b042301121103030c030c12 67
    0x104050800b0a0350400b080e03900445503000c0504800c01c03000424078820441003420320700c00d8601184952078102c549159110f64600a8800c2100300104840c0705203001032100825404210400c8646564412624110113414020095131800080d08145500700b42400201c1000b42e075540d160a2114004070309503040c0344121f04070000200049400110b00c1c0e08402c00070300741445c0803200d1000f4801454a0070074014000e40306241c0d5412310011040313140c0511400303044254011803a02402c2c0e40401e0741c40900480d01907080d559100421220303008200b07108100f01d0010022511002522201c8038000b02007581816102c49000842d095070541c4542a0100c4040c000d8082c00c0194843c1303504100d54004100328200101c070301030f401c050350751403092140d00c0132500c000158000b00d40051000700d130300d019085001014410848400b13501002503c5041d220780c023034103404c00880c624280c0604100b4a821980c90701000c10355450100d40003020741458403500080702e403010b141c00c0f80303850742d4403590708 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 931021501 1250 931020251 931020287
    0x3020102060c07081921140628030501020d0501080f030a08070e090a02070b07020c0a051203040e19061a0d0b0d1e0b0609060604030b130b010e0115 65
    0x25001c642040060400f0901504190345013603040281c0c03c0084900b84c000e0008240c03002e01e8000b00d8400c8030412120601400010043c440004070748011059000f032400340703d50280410030782e00f40204e050640d0a40219049403070b2941d1645400e038040d40000e0292401c7d28600000045c2c4c0d008001004114403482c0310185103450b03c00c4904440525000302100103001c560441c41380b05484032400240301e00c1c0c903c03c0040c2c55078204e25140302000c82c041c200504550000c681c0381044e039540300f9603c0031280215448640c07800f80680107401c50140381d2003003003080300e141c080180048502082c0708100c0d50062080006907101d01c0302c6451050303080550560303490180044d04e250032203540404451200100f1030040681196291180c107039024600400f00c204000c0301c4002c01000c000300070341201e42250954518940240807499030f0145100240001d101e0001240005030143d600c00061034201940501e9582c6070404c681d1842400c0c820b030362069002c4010064040d104a45400c0d2040c007041c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 931022751 1250 931021501 931021513
    0x1121b05010c230d09090509061012060f05070504080706050c19030c0209040525120f0c0e04050610080102031312050f070c0503070f030f17040b210c0403020102 71
    0x2866080500f2501d02c00312440300d4001a440c0c0d18441c08000748403800c40a42ea8517001a410416004240c0f0000340050f0030b903038170075414080040200d042880a90740040d5000100e0241f0b803c0c9070001e031118403602441145000140090b0540c0480104140c80303800c8200c0300015600c0701d0456062003000b000100b180c02c1a145500300120990742d2004040c02071900d40080840340e00082c46842003503404496560101111510a62215020f10070000440d10851100362922405080780d0604d40802040352400c28510010490280e00c244058090170180c2d4040c0d00e05840c0072556000162491150001d01040002d02580c0500840703100d44902584a00080041d6440b04889507000ca01181804814080c544003124203002814401e8003842c000700c6924a064141418490b09030080090f800f2020070901c00b081a03010303c0c8040315440904c05c06020009400034074140225004034005600000c0e0340c1e805a0030a10100543c0300c41c840e0044400d0311403502c0000c1511862100a015070030071 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 931024001 1250 931022751 931022753
    0x1080f010e041a19180807060c021204080f060f010323010e191406071d15040e06032506110a08070c080c03030a3501121b05010c 57
    0x8501d440e0814800e8014450000c501c1100165800f41103842c2c800b024550002030800465602604180c14504400d4210000740e40d200c0c000c40b40704800016001070785409082c2080c510810203180401c25035140c6076200c40e21070001c00d0312442106d07060941c6101d482c1c046410741d8050410241201e50007104080101c2125550b010120810010042e0a541c1c505040803029000d200d1200000c50050f2004003036412868040290300d0560014420303503114104004000d80c04c84011a084c10801d08100614003003600041c90004903105100a02e08001c6400500c440c030584000e0f000d80303403c80955140309603018840a06400869031082c0206200404002a900418180c00f010031f02d08290b59080c08140c43e00392141c1c1c09640100d80d0300464501c00c000150741440240c8044900328041c0d45000300042009080e440e80c020820041804950905800d007906061064040a064800c92040d03a640910640c401d507000d03811b031406022030a9081210313042e2aa40025210141c5031150780b0413013 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 931025251 1250 931024001 931024019
    0xf040603090606081905010501080a0b0c18030a0b250e010c060f061d010b0a02030316020a12051803030418050c04031718010c0b041401090b090307020a0501080f01 72
    0x341d40140d458640d16140820000000d100c001c10700d01c0c000450355400c04543ca003581c00c4680c16030107521140c1100d58094000f914010320540c2206000c3d80e01900c4100c40d5910110401a80003142d501d44162207007841009050301d980e501c03400282298400b07122003001007405902c078180a081c001107009109072215070107001c68801b49070103400d000582890440c4410100d8a09401611a40e01000ca8000e81e80a02c04a81400740052449590030115100f0002c2e55a0001a1040126002e4610303160390032842000428201908070a1520080310b403401c0103407648e404080120b000e8420b03074a210605040000803101101c0010360303554107003002401f54a006000c05840e1000c21a4104070010106140c9440c0030a86803028032415a1201c40b00031030b0040200901140c0c1c14480d0048406010a0307403103c20a9100b90080d000200642d44a4121030041c0726884004000c0c00c0040c050200c12400007005d08046803080d94010066912240151010342e41100d0803400000d009c0014801906 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 931026501 1250 931025251 931025261
    0x20060f0901110c0a020a0f0f090b0409020402130623040306050a060816051008060f090402031c02011a01080108061807030b010303032003060312070f0c030f03080901020f040603 78
    0xc0003000051554034210808100e40c0125602003855110404860661a000e04500010003124107401c80c102c0c035281c44054210141d00c00d04091550300c914000541e107a035000007540c0756001340119528440484000d108440b40e005110001d4055402c00d04150f0741e00c0c010004000d61800258242031442d42c03608054000201020300954540d00b000400c00000c0107100b108a04145035020284c0c02d06041c0518009841d89020400c09540107204c1c8a4485245110007410140c8480d90240e44030700101c0c0c076242c442401c1c00c890220f2a0342803120240e042d44041604074242075400c0c40a01d0103001100e010343c080c02140701c0b80c0c000c0c0000c11800d100600507010080b03c10001c1c0c3d08465500c0c0c517408061a002d13481940404c2e21411362500e2070b21655064500030079030807a541d055042541c007096035000d1600112169001c0020f4410038486c106240301440f42d4403022124045880746031114440c2c0e09140100c01080d16040481c0d2600418000e0300c02c8000c9260300c060909250080c120040d03c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 931027751 1250 931026501 931026511
    0xc0405070305040c290c07080601230d0816031809060302090130050a060501031a07021b060d0f0515030f0a02031f1401090606230409020309032820060f 67
    0x882020800280d508c0180b0a02d0700902600c1c0c3c001500c4090701034106a40d070326560040d44540410440a00041c0c0c816080d210741020006400300d4142d414503050320131210a09440702051024440000c0350907007a00400c00f6a4401e440e9400a0390383c64101203240d5000c0402c080c80d101b900c50a03d0260300310a00150001c500500c1160f0002d1003580352401151000c0c1c0007034501254030350004072400040c00c08260030841ca0310040c10341148020b10384943c2c1c00050b002c5803240740c1c0064014801000c81d008003076140b400900030800d42c249803c6580b10305529504050213402303121140304c018540842c1c84d41840c1d4000c1c000e4030080c2c440c5081000d0a0900004056042c6e6640000404215078804014060325000c400011900c1c101180508514514408250508040008401d014012006440498045500240c0c0780c0d218504440c0c150701610384400924004810107442007690481c8550422419445d1100d1000401c00005000b16050607150800e0340007201203145200320751045640700d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 931029001 1250 931027751 931027753
    0x30f06061c020307030b10080712020d0e10090506180c0607020103021207180816050d061d0706090504020c06070e060c07080c0405180613050c0405070305040c290c 72
    0x200c8040c071001800c0303030000e40f000b00020b5942c0080c2906801c001001d080c0c20406400c10806601d09818014403451400041c0000d1a070082010400b982450b0404200d400e070303d40603516410500b607000b40081054507001c0d10540306403000300d2040d903080a0108520070820300078100b528020000c0c03142662107072204904140d4200720020258401c6041c1600030080c56583d4040e100511020380140c407255080306490381c01028900c4500400d0b1540001291000c9da844184102c180c10200000c14000c0d0000103009441c6850f0780c42c00002160450a90fa11074941041c456140c6003400101d000e040101c805079400403000c143c0f410f000d40345c044c0800a00404083c548071000c50b62504058407a84100d845501c6000300c140c00b49001d002d103590102005170a01c0c1c25004001c2c0080d81c0d0b0f14041d04003c49464980306003c02d0041c1800403000034080940280400e00b0b00e400020020001128159040115104003141002d08040c078889500c40010807012022520048031501d544511507489803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 931030251 1250 931029001 931029037
    0x30a030504050c1c0c05060f07110307031a01060f090b030112023c12070608040302030d0c0e1008092d0f161712070501140411040b030102030f0606 65
    0x1c140ea83d100513042c0401d880700440d540025a1134000302008441e00710501c6054141312084404100070145d84481c1e80000004c4009000e03c40802d0078900307642c001800038454103000c00f01c54031400004904940603907031040c40c01d80010302e048912000d14014211380440c1000108145220101c9030649140000c254000c0d40e00d43c0c2d04060304000607440400400e000003050303441c11303035840b03641081c0544091314000304084008000b582c441c031540c0107841c24403280320b000c6010f0610800565060058011041000d0400803078050040d0b02208a00c520610180c21520304641c400d4217007500172132900c0024500302446040003a503070080c0c54a14442c2803940c061427140c010b000c1050360000d40340706d4007800744660342a0001034a403059821824094840501d0030090b507100040c04000c660046074481c0d00d0f200d40c0d01e0228098408168850003000552050000f0f2000d29074080e10010811541041001c2c0d00f9000e140c280e00080300c3c401d0801c880c541c001103507070504a00518529055542c42d41d5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 931031501 1250 931030251 931030273
    0x3020604020913170325081014060a030e0a0f030c0b0603010c0816050d02070b1506030c040b0306130c1e230a0c02090403030203040506070e03061f0f060305190608030a03050405 78
    0x80011400c846140060079001c117101100110180c0e43c40680070150784900503405c9d041c082103c920a00081d0400c1603031b0b42c03400c8107090100b03001d041c8907181e100000002c002c1d018140184101d185680c01e6803234140440104000c2e180501c2099809217842c2c03158002561400c84010710080d440713241500b4003104000c68289000d182c40282401c41c0b20f80c500248600340140e1aa243c018841d01c02070040c4810000d020070410303803070191421901620300c1503940b0307603850b000b107850301001c0d611198085041c0b4070303500800368000744030a21102e120002d840c203100c82d643c0c040f22904850045200580014111b299491b00081e00610b407060036810034030103000150b03010603180101210182c000a60100c148020040d0511030240c02006526140541074140310010351225000b074101031132421448844450544601404001804c0303007009442a41c2d50b0b480040e003d0802100ca80e0003000c52406442c00c005170703612480c82030750780c44001941030070000358081c1d004200c0948255031920507103030000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 931032751 1250 931031501 931031551
    0x40b06120304030b01090b01051c0504031b0320010b0a031112030a0504080d0905010914040b060406020d170408120a020f07080403260306060f090904030206040209131703 75
    0x10008500c9000a40d044e585001c085008075041c4882c0c03281001b1003000b081504c001d148203450529903144400154984440ca0300f80d41481d6060107405030751000b00d81450034590014585904280812528025201101e80603822540400ad441c1d5000d5001401440416107100007490141c1c00030742811003111034000e409140d90011202000080c90005007030000760f4060164460b82c20082c02e1064540341000e002038034000c81c2e8060300b0000c81030214030007142d40c2e9030b411206010201500d421f40d613903100d41000351034480d01c800160205014200f40ba2208016041880c40780d5040300549080410f22138008540d280c01404a0050603002d008481e50310302104000d00105200d01c0206550394a149094080e02c4c0e83c3c02c481e5110400e5000c5103080307401d4001c003201c0d4422411100540c2c2d815111140b001c00340100380c82150031140c403030108420150000341950080d802282d020385947d444010040d07144210071801005407000386030b0340541503002030255401c41c1c1d031540107141e003000d80c0b60b81c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 931034001 1250 931032751 931032757
    0x100e100c050c0604050a030f080108070509040f0606030b010f05271e011d010b0c06011512050c040e061c030f140d090b070507210e0a0803120a0b0108040b061203 71
    0x3e0301c0a4000180f143c0c10990408d00401c1051040c0c10181503a614102000da15130095101d0680240401d40000e003c00c9020703201000119031240041003081e0310307030a010a02490900803500c400c1c981e20000f1585140440c5d10302800c801101c0d03000498503007901800552003000d481002c1481d102d41c1d04000c082d44018a4034040d10056840003006007110415801012060703000e02010309040211000980d40400c50906407081040f0032500b0500c0c01c02d003229031140ca800d100b01c80c140b51200b44014050007400400441e0390917800c00304a0707224401003190355200003850300c070000c140494520001e0b0190070840000009803c05104024884e54240b081f5440201815507165551400000300307d078030140940c1085003464098100310441d036a10305070901808200904c4c0d80c212164100c094420414050303440da000d0310392582c81d035403034000301d907a904014620b55000310a42c1c0003410700c4002c0d110300540980140e40d4240161201e0301c031286003c402a20b580d8000841010202c8820420802 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 931035251 1250 931034001 931034003
    0x3080d0c21020363030309100c021b03190303090302151302040504080c0118060c05280c050d021e07050a15020c04091103100e100c050c0604 62
    0x2da07491400d40340c401d01d8031049079a402c40010555001100101d4155a00b489207540e0244564052500044602100c0c1a180c08202e01e8802d1000d400c003c00004005180139140b0181240c2c80041d9181c2032005070780d40111b010300183d00200308101d540412403190301d1401e101406503581841c040c82808078840e4141416404a902c506440041680c1002a07252031504a102447e407802c01c1c580c2c4210100c46000043e10803510340700460140081e50342242c51280d8500d0003002841d405100340400c081c00352106907281ca140c020700a4800d0702503801c0f0b070780c00010041c40c5810458a0b249482e00940f11071165010801030040007000180300b0400c40b0712100140c2c005004241011940b00d841240502480c00e1f1508007103002c000790f44500380301009544090300424200110030504070303d8081022486035000e400c009100d0244071b2868014800d1005c25029148004402000c646c1a200502c03410b002e0b40d030064192109002c841c0c0c0c06601081c1181c5802450004509100f80ca05242920 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 931036501 1250 931035251 931035317
    0x1224010807030b24040606031d0c06030a0c020309030610030203071d0103080d02070c03061b1e0e15030a1401060e01020c1302130f09270b040c0b0a0206090c010903080d0c 75
    0x600782027004800700c1c40c42c00c0f8082d040e00078503800b180714011500b02e00024003404000ca0312208a00c12440c024015500c06010103012030700c0d20b2402101c1101c10070801d01c0107901074043c000700800c04041401c2448030581c102d41411800d81d2a540d1210b1380d551201046c182207a42c2800701c3c2001508111008004600496006c6a499200b900340103111110800341021300081c120608144079200081c600c01c40d05c1420140e00900b03100c03010400f40c0401c006000d030001e8002040106038281c1d68860300f080c80a0000a007000d83c6c81e044152404288044103d003d64403100c004032040c0760101d0b0304030a010740c050740507003000112030854000380401d420903040c5440c0100240b0103004507110b0f221100c002409855081050164918091060300c40040c1102c01c260000809103d60301518a000f4201042c046a445d10b807004001e4a40800303a56403075160203401000c01466100d80c8184040d00d402c072800074904200543d12000529000c041001800303030500081c01e841444c0c803080b010700b400b201 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 931037751 1250 931036501 931036511
    0xb040f12080703060f050102060606090a0302060f0a090e1915080a0c0503010b1c060209010306121203050f06010504090b0d1707062301090b1224010807030b2404060603 74
    0x340015041e113205420400110515520421060383d0006106800000903101340d5603c84520010400f00317901900f000e9000400020729250300f0324030800a004001c101c0c1d50303603e03040761100d110b0341c0507d070b041d503a24008001c080f83d02c00300801d043d84905100d003034030710303113001020b039038074509810090511801e5449c903110110030452400e007801051881c800803180546180f0011040d82c40e882d42201025254941c0030544c131506074045d500c0b07a005021461111404184685441c1c00d81440c80100030000900300004519458094440c090150005071101402c10303007031408520003803020303030110750340300c406482e003240032a102c4134a4081600c103d11042c0c0c0c0d81c40d80c40c20b0030810b1b907070344115080c2d0a01c2c1188102500c010301c1d03580241924090040800c0c81e005c1d00d00010b40711120813404140754024441944d14240d4607180d212010807040c0709024903683da40308401c1d11900a0311000d0030a0710314500041000e041405000c003a00c2491202c0b040b0002d910300498126102500800c001c2070340c407 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 931039001 1250 931037751 931037761
    0xe0f070305010e0610261506030c030c0913021801080f1b060406030f09140601051002010b0307030303200703050405092203030b01030608030f0d0c050c07030b040f1208 74
    0xa010b6003440a802c1001080c1c45d08065400c9400c10f4038900c00d6003164640220340b00e028441c250302284a0914a0b03084821440000ca076070001c06e04203482c034910034462181c1c0b805c218100840c404401c0a00141009483c4d40d814034030711021121520203d901008450541019905420181d40641512002024401564001140342c143c043c5001c03041005240c04000c0640c3c0c4110844064070035501e0045110303040405102d000d04010100240f0405295480e00708420740090290b049520450366101a01440c250903070813622401007541c5c06400680c01400400c1c001d8101c0110300f5140c10100745001303401c011740791064020b9032040340001ca00180400c601d21303207200042c1e00010740c0d800380350401d94080748100e110b40c8004401024542c5071001400240c1c040d6100b80010072011040c2d0f035032001115201150f0758460304c0942c100901e40358400c00f0040c4101c1c1961401281c080040c48400e085854910101900401c11200100c1002f80e48001a40076148840c07203501c162100c0d6954100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 931040251 1250 931039001 931039003
    0x308030a051806010e04080f04170d0f050418050403021f060603053601240302031204030203070e15040c0c0c230402030a090b0f15150901120e0f070305 67
    0x203403107840b142c90380180e0041c00f0740b0b1840c508594001d507021241c80d60703800880d0768060b01401558420301d051540c20070880560701b404500e8042c4c0403025619049400355140c0f051300c550182e07008408180c90b1031652140c41080c3e9a200c550454081d00484405500c00d13010207042d04004841c0c403a29039120b282c1000155014052160040c40300c160342c052400210950044c092014845076013122641d80b6039410101080d44841701e410185030310040b03589881d4406040c804404d1104a000c0c1c41951002c0741c070070400005032130070f42e079000300134200d120315284842a40b100007070f107003a40e5101400c20800141d640c0d4428602e2074030310364440c0b15421400e4200b4800e07540031030b40818080240d2844400c405220321100002d1200c0440e8010303129124443c403c00100000a4010580b0f0b4608050041894607402918410401032400d084007030120010300900640f84078801050348401d1000c0d1100e98001c9000f070044041d100c40001d9009074185c200c0d854404641c125a1241c0c0103007000f40180310b0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 931041501 1250 931040251 931040281
    0x60301050a0219030f0e031c181205210109021c060311060f09061917070504050d1106070804080607020304140103112205120a0b13020604030b090d031b08040b0a060308030a05 77
    0xc84006074003404c03003903a01c0748420b07440c11041c10420000005510000b00038802000c20305070303008cc1c1c4014820341e115904480290300c035401400d84012218029040c602c0e240c001e03682a82e0703002540038180c0210070240101c0750003020014602e5141400303200358680b44c4c0c0f070240100001120522062400044001c2e0081001900c10701c84c41d40c00c0303410410000d8006003103c1c210303201501c100e41482e405090007180301c0e0340034500c103a1102000501c1014000204060030645482d80d05076452138454807016031340d80c4268414940c1042c0604035514241d0301035400340c40c030490010849032412101030101080180c042141c210410f110002c148100e003080e0000c2250ba0301b80740c0c0104a40325858031440d4000c000200002204115081d0034011516100142c0d001581d202013019280c0c1080e0b28500c0d210000c0360f80a5000078501103602190243d65040000c100503140c540038080c1d01c2e0341c1c443d0300d810200100424409900c0301d03c000000b03064600118419034007080002400c0c2017254551075460 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 931042751 1250 931041501 931041521
    0x501140c0610141c08030603071e1e08060a1a0409030c050c04150504412508060301061703090f0d24090204060b03060301050a0219030f0e031c 63
    0x240104c03035001c03070204411040d4441950810402611381d5507040019140c49160b4002080c210180048134000404000c8204245c99004a10f040562004041c00500f006d86100752541c1d98461804502400302c582d0110280003803071500780840000d074202090540b138040604030700150071090030a05100c014000a04c1c0031408035170506c44240841c00021031103d05002e403601c915611100026145880703600050b9a17040c106c149001140b401001c12501d402d58040c0300030f180c0305c2c000080c1c420302152181c06010070790326802a21105050341d00b140c1d11140200610b40544d42d811000c6a08000300403604400407510f0021680c4101c0c13081400100e5000705440c0307004540a0400c1c40024081030159002020540285007480100c0c60742c402c083d2415600c081e42182c6040e04c01710744450a04000c5110b43d100380c0c02401140c07140c100c2d4204904c903074000480d0b00c044104071016094400d0f00030000d0b03092951404580482411009811070348000780400140d01c8001c4031510125140c06600851 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 931044001 1250 931042751 931042759
    0xc1c0c0603020c070302090a0f140403091e060c0c17030423061e07081206010e030a120c021801060801180e0d050d020d050a020d0608160501140c061014 67
    0x40183d4011040d613803200c50100a1044540d0400a26001c0c81c507403001403100512642400210100c01f0700c910303002c500782c505030005103195201007010300300f640200c44820070b00c0392003402d100d181c00c0c0f0444d10510b50302c0084030079511122001620014a80417498207520600c059988d90707240565040c0c204200001100c86140503d02184d041e03590743c000c0d1400840c025104814100b801000014544150040103001c4003020402c2c40a4611741840c26101d031703001781c0340c421807842c29000b015075445003003c1c01004092007d0340b02d84014810304000c0741d41807025146030103980c964801d140d02800309070485400039100c000104242d0b01c0062031604915942d2104000134100f1f1400c040d144e21a800c03805003480b100003055021030b5000c1d4122420f82002d00340801203420580601c20107513110900084600781443d0012174284008120307800305810880003035421910b040c3c0151805000c0411074201c00b5811704ca0310801b1f007801c0c04210b20881d243ca088030702c0c84d8240010501e00d000d01080341802 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 931045251 1250 931044001 931044007
    0x90301150807090c050d09061e020c0606010f0c052b0809030d020a05160b15060a090905090102190c0b3114011a0907020a080f07050c1c0c060302 64
    0x20300075000c120306050b51480e907008525880d60765030a42c0c1900c01c01c15210b402c01d1410351007030103005007035100102c03100b00f00d010100b00381c400050340401d0f8015402103a040350846000b0910360760281041c0b0140b00f546040541c4441d0952b05da441c1401c1c0a002e500880c401c81400c078001402c03000001c0e9400c0700080c10401d040c0d00306a4101d41e624050340007522549a4000f03440c079503103405032087d640303e94a2845001200002e910b4080c3c07c42c0f405480402034a0150100001103250840c1a60181100c0d5034071100e0f01454140300c0e0003e0b020141001d15035550130401c0d400c50600103501c202c0c02c1c0296481d13584409010f0314184400b01001000a03a13810903110850140e0f2146d040303440306030f41021095882c0c12125040100e400f01400c01190030640c40e003041182d44001e6001c0d182c50a690403100c50000759104107003039807070300c1c6070050041a8800410040c445805d421001e4229a4001c1c8200c40d5400c1d44100896042030000503c01c4107210308a800340200814481802e010b07040074070382541 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 931046501 1250 931045251 931045259
    0x506150c071a070309090c0c06050c0c010b03010b06070605061302070c03050c09010303090e070908010e070611030901020613061b0302220830070f02100305040305070f11040c0509030115 82
    0x124903055400743c41c0341b441d19054448000352151680c015035030340180f8100f0540c1060001952140c2c4083c14001055082035800e156918040c85101103a6901400d0342d8540b42880c0d03500d2004000041800790701c07011640c03108061445d40e2010700300d42d6108044581d078003811410184d1409000900c0c0c5407155080030018400650720002070412608420180125038455801c180c41c035283d2703a048400d15628100f0084100e0070000f5200c02200c1007511391083c4140107900482d01da02c40c0d0724251f80942c0c421000705a219084034401e0701c0340d90191030001002c07100066402d003075030700f540715403c0025004204002d0b08191a6031140502141c0e2803144000c1c0e10784142d5988030444010a040c81058111055803451441c00800702104a00311006564083d40c1c541000c1031304803400244c1c001c0050030300091000f4020710401c2d00617500760301d510b41410110b5030303031070810354500d081141c014035036aa0203030302602c50b40200110a0345644803140c503401c42c1000d0608588049a0b591904441c07070300104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 931047751 1250 931046501 931046507
    0xa090b0f0f07060b1801060906080c0a08040212010e0c0a0503340504050c2d030420130f0b030a080f210f010311040e0c040506150c071a0703 62
    0x19400354400360501d80b242441c0c2803003801008503845142d080044075a01c24069440088894143c0d0380944a8204441d1070303900494030300314200c82440c04401c04001000006001350803c079401343c801401c0c804150f500f001c0443c2960380034000c560441e40400c4031050f4a00d42400f24002800094006200408002441600404044e641d1541c00e5071492071120300d00d824112905d014000140040c0118140710300d0080e025848100401e410744100301e80751040304e141100c0780306554441140a030550316a41c03a01000555410361103240707101c90344510000341c2c5a128100785440d90782c07074000a000c42080d01e04000c3d22241d0f207201e44a90000c0302440005a24881500c0468a5102280352035191002c82c8200c0c0d100c2010044140c0420582080402c3c000030030064141d910407003003409498107800034001510320310890800180c104110700035031402c05600090344500010070185820b10365010003075940e0700c0f031500d0300d610350401c240a01c642c00420260100c203e418403262460800151802 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 931049001 1250 931047751 931047757
    0x120307120302040b0403141b091f170120190c0c03020d0807031205060904020622140a120209060d060f05070c030206070f08070f14040b0a090b0f 64
    0x415030301285198600d4180320341d06071805840c2c4080e40030b070380d15100e09210441d02c0000360030300c03114441e420307041c81c044503181800990749001810280141c0c40f0b2a21860a1021440000342c806528410004240b544003a50010582d00900000303150301c034104060a2445150303c000228080400c0302c58003003100c070b034034031074009a162030046180c101030f00d0008841025540040c0d40a19911081c00502004500500d4502d209403a200404086501002d00b541e804952541d4052010740018015040420042c5900d0701c40394a40c00c0f920304401250b001d904d0140d08100399003032680004c00c00c6814000f4400000e4904c094049128856585c00100074440041c161405401a02002c1b010003c154001c0441810303103030420711080c07400c2c8100501e1203201c4c450940042c07103580c01249055004940f16546000075030395241e000d130b694140584102c5a09a2054200030001ca40211070f58010006040940701d14502c05995445400c03008101c3d650980000e00400000c0100b00102e01200d811 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 931050251 1250 931049001 931049003
    0x80304030f200d032703081f0315020c010e0a08091e0901090902060c100f06061106370509280b0408071a0a050a0c0c1b080304090203090c120307 64
    0xb140600385d0002c00c2e82202c0c18000034000c0100300007011130030940c0040e810785c420688010200c41110441088501c070000e5488007402e9900f2900304198004001d0300200301072030941c0008210310f40c02d014070074030300030414000365810140454012400d180240d04401d078042c5110b01d20000900030000580e85080c1071081c40041669011284219100d40050710340400b15007003990740140c0321840f018060300307880d50210700032440c00c000030a03281d001d41050090344400000802160351340c0c102000c07a05450180180d500f045152200c0308010b00385000c01c151014650020540341010181946804107041000000091450031000c907110b840c801c0e00e8200d9005030034103d039511a4103018089219030800070700070070700314800c0042d01030703555500c140600c0e40300004010b02c0d6540083c0e00100d40000c0e041800203800c250030007004c1581031f5070071a00f03200304002c0d180f1100e070340348800c511355403099110200003034000c42007004001d014050440501d40641e81c1c0a0f0319048120103076240c1c0300d0000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 931051501 1250 931050251 931050257
    0x60a02210a090c081605010903030206150a150c0b3115110c0c060f1b070902030423030406050a0809120a021b06210403020a080304030f200d 62
    0x80010002405508038a140c5a00804050326650b104c2e000f5640380c04a151040c111010350260020b09540300320154822a40c065003c4e0107180c807418010350070507000d04040c507444099482c0101d070360340c0707034401807005585551603040c8040464901041e050170300030000f5081e400ba000d10320b1000821990003800c55000f50408102c680040d2500480c03a031303030b0a05c90b0400240303004660b14100419900074100d1238a40c3c400c40704040818400c002070340c8240c0c550782c0d4888a0500581c41090720000c00c0d441030410140070b40d0042500e40368004101c1c1c0040710b05580000079645e01204050f20340784e501c003011310000040c40c40c0a080840150141c0b01e01c40440e401c00001000151f80c407001070002c03d11015900b844166107050121000b5640c8070f2051a030541d91944041501580c44c0000403940700c070050f500c001480e00c001c1900c070415000e00900036401e5024104000002a502e24029482144a900c40f0080701c82e400310300424450080322442400258100030f810b025100141000340341170240307 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 931052751 1250 931051501 931051567
    0x10504050603180a0b0105190503070611070806040602032d06060a030912091d040f0b0618160f08091b01120e0102090f0a0e06011b021809060a02 64
    0x541400f440b04628500c0701e08078022500507034200a0b007258035604075041140c001038000c42503040254904800e115056159000707903801c2144c18007681d0341003070142c0540e080d151000d0751905628105101120122100d81c0c1c00810020f41c1000010603920b88038a03d4240f00c004040c1d40d071440f0b5641400342402c1c4c4203d4010031103604080c4250081d070b403090350011804d8440c2c4008000988509041c0c00340c1554200503982048000e0b2089035101d20407908400c54890340403490f2a4042030f1070303002c0d001c135400407018245c102c01803029440c054028001d024060146540b5407100402c50205140c4540800006c1000e1007180c00001426005041c0104200240161f610340140c0d580703400041a0000310381841100310501074198054008104245c0716192070402c144200480c501882c001d1140b2144090701140195101c1c52164070540258030305401c6a003c43d4000640c01250840d24081840e000707020414080c60601019030401a0208154101704402d038410801d0346900e4441c907020400e034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 931054001 1250 931052751 931052761
    0x405151005010c0f061b020606010c0201140d0e0706050414100e040f02210906090706050a080712020c0307050114132d050a03080906070e0112090605010f050a0801020405010504050603 81
    0x3002c0c4d000c940740d8400d0040004414400c6100c1d81151075241c003030054001c0100044482d401802032000c138550507519501e0302c1030110018940d903006200080340c030365942c0d280d0b00c2d610310082088c41d0140c04182ca8840d00c40b442e0035a000e050a8400ca2954010700700711203823514890f081595035120300b1040b03501007244400343c2d000c180240030310103600c45004c05403045110651081c0f08000e008280c0001500c41c0391f07596416080d500c880d41d119800001e002080721468207881b03031101176084000ba2030950060510714031031606980040900c1d052640002070f0601c1000300c01d100d0750003513008410520340c1e40d22707102c24120f407442402400034160300c0346480d0f0201208120909103144403028030030901581100d041241e56024000c01c01c40115695402250026000080c0d0350300c00c0c017540d40c6100d01d90b00070100440300700822142c052441515401000c000132a0360043c18081c2107240c0e20f140000c1e14081c1008250b45140c1d10290803644100803d2010341da104003107806451056550707039900e07190 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 931055251 1250 931054001 931054013
    0x10507050a120513050307031155051509030a08121815060135161701050103110c060124020628140901050405151005010c 54
    0x10544001c2c44840d0708a00a080180c010019211181c018188980a40c0e1140b0034140d59055900000c0d19012072051402060f103000c5e4004807070354903982c0403d02421804914080604d8000b0140b205071340c40000c80007807480001005803094108154000070151810000c1442d0305807041040328698000150080c442c0c4003001743c60041d940c00341c9007540d522041000d03599040d41c141e410208140f03a001c485607110000041c20642205d81a1401400b506c0304001500c41c406084001003640c20f40740310900e280a00413800c01503030050661000c103145440c0c3cad0384080c449490401d4005020b0440c03102481c550b00c0781c608a0540c1c000313007000144a2420000104039000d00420803c41d4450000042045000c048041c0244180c030f60014016800110041e40c845404030792016225503030150007600b141308002117484680030680c000405074000c41c8042e4800030103c0d10240169120401d0000b004020080302d0142c203108000460581400c4c1807202c2e456425110f40e6041101202001c1c0a02030 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 931056501 1250 931055251 931055263
    0xd030e04150f092403080906090d080d0c0e0a1d09010b030304060905031002030124050903010e0601170f120705011104080a020103060b0c0a060908070203010509030d0c0e0f01050705 80
    0x5003142001800382e60b045550050007803119801c8041d400c90004216000e120b40c0404d0607654020490703418001c0c8030b41072001a82104074500d500807407540741230010820080c02000018020303035000c91910071440e8040c021507102d408043c000c450313044041000302c000020403901498070521000c00ca0f150700104c5030140400c0c030240c0d0380c0341c08005400690560081d240004075002a01503d8240c16100100301c220b000900c600d0184941002c100510200c1c40c0d880075040d40402c0c1030050a110701e400100c1d0855804010321601c40e0302140062120080786440340310302e03880800c02008403d40005007952070303005c0415160382d206804101402085400c0d00103820980217464010388481d61055070a40e80d00400e80141e01003464008045006d140700f504858410b150103000704032003c816511171b00117214006040d290310405200b907a00595081c0661070050240030b0046440c0d00c0804038000c100c03090703001c041c01446516203628003d901c80ba40418180369003420450303261303203050078401c0c00c000d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 931057751 1250 931056501 931056509
    0xb070203010b060418150510080a05010608070906030e07091a040506030d0915020c060d0b09150f010c08090d0c03050f011824110309070b040b03010909020a030b0c03040209060d030e0415 82
    0x141c903000c1d01a59090344889c000344607240341030040c0043d982e601000d83d064001034420400054140605203c0a4060780200d41c0203210042100d52041e62010f0801c2105d80c0c2c100e40c03059010751410110503510f41801060341161049007d0b02001b4501540a070075183c091082c60320300815281c0c4511118000c1c0140b14801101400840e0354180c1a1100f07001042c048a10510803542e860229900c07600c810748050a610000e0045014142c03c04c0043d0340c0341c03119000c01c81c4c42020401c074240450f1507680c0801c2c0041c0c0b08201090b441c5046281c0141032030140c422a6900d60b141c0300c0c9030716002d40990400c0b03034065040034003144044e4841c0031440c800714000500141c800d003000012008942c20348000c41c40b54074a10243c883c00c0383c0710214080107110754402c170550001c0900040c415042103901c0740c1a4507100400c0001d10582d03a079100b0750031040440b24807202ca0400b000f000191b0602c202604d620500c00c540b5200001c0b0b003540d002d04140304034110b0500882d51402006c5405240459540240c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 931059001 1250 931057751 931057759
    0x10021b09070c060f0f320a060803070507051c120e060d051e0108031206060c010204080d030204241e0318050609070b03010e0c0c1002040b070203010b0604181505 71
    0x1100d290f0280070050010b030946082c0d007520700440202c9183c1c2c0c3c00c070882005488450761b402100c090003121010141d000e0481820b03207a8618000420120400081c10124441d6001c0d00c00540b90608220380c000e005001c0b0384420303140b40305000000f00c60b08007014072041e4904082010b1800d150100d100380c05100b9402c0340191410090000700720f2904003030800800740d240646520f0383c80d040c461b5201e0080344c18440491560380040345a6142000217400d4000ca0071000604050b0364551962a024500051308040b03a03000606001380351100b550140d582102c1e9440e44c114184642000b840442143d441403506800b038800300300f03468800e80010f0280200c3d11201c4840d00d100381131182d00c84070140c450304a01d2084840002d1592203500640341224076801080903075507180c140b600840e510a20700d062660082c0c24822860301c2c0e961001d003016240c0c0800e81ca071103007814030516084544550b1070320300c226400e110420004000b14120050b1a111542c01302d5680e00100d040342360420036800090744 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 931060251 1250 931059001 931059011
    0x180f080307090f03140606151b0c060403120f0203040b0304020405060d12050909090d0e09040804151214090d0c05100f1b1412070e040603050c10021b09070c06 70
    0x14400c142c12007203c01c510792020f941e07003500d41f40208481758451404a0040305420301c81d10303501421036500c443d4060740c2a029100c0200300c0c0d00001d009075000740c004462640610b0302048101d0717404800700c44901d81d5800214501410444d0000785400010300091099488000050b4991900340321218000e5228040c003140070519000644250460840c00e8001e45c5208000b961603000041c01c0000c042d0386490380b0160503602c1062104054000740f013520a28010003000400001078104c10301041d0003a602c07a075200000030082170a0701c0a41c07603083c24031400b01040c0001001c0105035000c0c0780700381d4140289049007900d015401c021640040007a410328220080c510308080c1c0d00540120902034550340b0b85415500e0f01a90700a4002a214801c0030040c401c0f00d00100840c0c107400d42180c001d0400741c02032a8404000b90a4070556003044846400002741c1c20614244440000070000560018000c50101e00d4040c0043e2100d20100c0751203200100e010451081c00380440c1030419401c6002400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 931061501 1250 931060251 931060253
    0x714030a0f031e05091804170a020d11010c09141507080310170a02011d1c020108070f0206041112060c040f090c0e010e011b05060a180f080307090f03 66
    0x1082e43d071045010f084840c0381c10151141c0720710401c111a003c0e80300a00e4000420310120425055050092040794110040c07a21800c94140c2c0c40c020f402d510109500500348002d00e104001d0145240c01c640e032025a0401c450880b4054000d085901aa850020000d544040a50014513403614080c048a100000081c1407002d1021500c015403160301c8010014200640d100107030141900d2012506200d0381001e0500c100640c07003810344803038481c1440141c440d89649000001c841082c0788070700c0381c0c661220000c1c46c821035802048803039116031503090080d240c881261000c0d465103001440100a034aa240d1300ba2180c0d83c825501d05143c2548200f1600c40f464101d041110951144c0070f82ca0081d0341d48e0f80b00290b54a5207000b1180d480420b5600d103c1094805401582c40040c3d80c105641803001081d42c548c000300180c0284e0b4540d9000304000c20b05810155812021241c4400c0003581c0c803942c101e4030001240b4140e81da000c80580c80403a82d640d230381e0750384130403600e51506410410541e00d070144004 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 931062751 1250 931061501 931061507
    0x7120c020105061f05072604180e340806070c14060105060702010c050a02060d091a06061b12040b1207210f0207020d030801061805030714030a0f03 65
    0x5071240d4020b4500012007503070120550905000e4620107000100c5c01c01440b8002a2081803c24003c0c01d03c02404120001030301d181c441a41041d004040301005001c81080305060034010b1002102032807000d00340030710704550320302c0d03191071031200d40148144001c10301000e149840d01150028103120b01940c5030341c1400d100040010700e07118800d03282e08000741031005145001050035412150000c0c40075103040c2c0e82c0d030700540d40c164090318203582500402d2080400761b2038a50003031015a050000028103c2e113207181081100e055590444150270f06002006810346484044440c6070006000e510703850346043c184189092685024003001010101d0b0006c1c0ca03150880241c505e541d8a4201d1482940d0358440c225030b80060141b2200c0840320203c0c00583c803140a9024004c981c84500380546041111703004140c0020325424101c000900c0700b0010043d0070380c070100d59100d0b01000d80c808a1010b1400001070b43c3c2d603420b805020354603020324075001d07555541046245803490303029803540003144d860b003009 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 931064001 1250 931062751 931062761
    0x7050106030c0f2402030d0615030f02040308040b070524040c14030a03121103150315010b030f1e0703140a021e03040206130b0c100b0d020907120c0201 67
    0x122414090980041400e801491200c1c0507902020041c20340c1d0819000701c40c401e5008014004e0941c04200201c2d045012a030182001070701c00405032014000c40130030001d044403441183c054a4600c1800280001064201250201c0d61343e05007054541c02c407410030b18100603041180920f40490f407103001140c501b00005440c8207078020280b0410395540c41c000c8040d103280180342ca55264100000d0314000a001e80c000351310015103c40300241d00c50142d0340c00b804591003903c41e51804007182280500c1460100311054040304543c2c8420115450000300c43d54a000c0680340046001c000c6000401210324103601451441202e07040c80320509080d80e01400404010380c4602203400342d0300020344514564002c650400400c410f10702c0d088450244015035641000c1c10403a4032070800c00c010404140c1c4850711802400c0d1086025079140c00481c001458080d010840e041100d04009210809136980030038800f41030307010f07141000340303607103100c821656154000000741500d032a01c41c2068005905500c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 931065251 1250 931064001 931064003
    0x9040609020405102913090905010b040c020307083004140105060a030312151509060c0c050d03020f060c1806031b0c030918041505060a170a080705010603 68
    0x820020ba031100e0320f0b44054200740380569070300c40c1000c52030301749120400815410b01c141d01c00341c0c050600c41c42d1400c20043d03910940c0010680e98648a840b400c0c058284a1600b0f0000f08841c200b19140e48454065228012844003500c121070224060141d200396040c0c00140c0070344000544548058002d8104c4010300958003035400d2240c42800c0745400301b051140c0360261400906900c20249035540c200c07444500e0334031046031940c07603c9210305c2040070007840c03001a00d0280040001003080c03000007030a04a142d8820303000c00403000c0071003000c071b12030000c80307403d440007512410521192401c080e8645001c1d05c0210803640300e40820407588215000140039075182800c5501c00c4200b01c801080034900054072190a04100b51a400980143c8203000705404100030045d64140703400c001c000b94907041d91700c1100c00c00b424294100001c0000755020081d16880c0c00104200030706049010800c4147c2e18042c0742d0400210103980740d4800c000700820b00489a0022100341c0d80c0202c0e28195020341290301c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 931066501 1250 931065251 931065259
    0x807110c150d051308030112061404050307050d050a0e0f0f0d0c090b041406040c140705031908070c2613140d120e01090308190815010206150f0904060902 68
    0x3c08100208000590740d01040d4108800b03905517403c1c42d2480030a0284940221009503407062095000507580100c1403050380036002541d01c038400c5e414034500701f039000400d10040040820540440903000018215025001d44854404001b101c001c0340344000c5484425070311509440d5144d0402140341c140a068480681051091090602c180004d482400404142600341c08001031102e0905600c07540b441d11b03031807805d885440701007031118285500000c02560300c0d410014050349200704180c7c450340c440e001498114445c1c50002801403881644100050040d180414030000504105114000414082c002c0c503903100c0c01045004017119941c0301e03d030780550070340c0807240203450200e024810480c0c02c50104000d52020b400104c031410f10f80c043c1c250501c002040040042117000c0c028003001070070b60041c562001380b035020150014000500e02005118441c0d20618940d0703001c10401c3d08a132600013451207541402d4006202c001d5409140c41e009010007041005110180d00503a140f18002c1d6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 931067751 1250 931066501 931066511
    0x120105091b030d08130501060b0a0e0301061a09040c0509040c170601020604080711040f02070602070c05100221040b0a020325081903090b010f030b060405070807110c150d 75
    0x3205242e02c07443d074031004001082d28400001c00e01c0000061002000d88210000103955803103101e008055001150075a00103641090b190346141800d1103400050110400445214028007240c1c040c5d503c04c0704070960003180c44901202405000e442a5594003038020000c0c00032070b0344400010410200e120401c9800000c00c004074820f54004220b940c0241d1700038004510300021626003090304039400c840150841d43d01e0860381e41501c030a10150030120f11451026171740e00c215007040d0304006a035030482d0b4402c5d080010601d1070b0b03070740006121812480c2c15075190201c8070b061844160314002d5620002c2c0c0c1800004900c804a80d000c4001c0025800c1112621502010844480c9407490342e12402010340800700000c544200111460450300e03900e0745008280030345650380c2da010311b24007a030014540c05241c40d0180200300750094042c0d4419401d4500300040d242c0740c5401052842c019040b642848004051601d5204090118403691880502542040f00541c84080070719400703014440f102c6031500d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 931069001 1250 931067751 931067803
    0xf01050c030601271a03010302030d08010b1c090b180f01111608070212011b0e06040302091e0c090a12030f140405090a020702010f0503220212010509 66
    0x2420780380a8403041c1d4a200600a2400e02004a00c90405100440301040c01c000940a01c40002e0b15440d00400c5403400d4403545548180340ca020040c200540610880b20010b00692405d003041c1c0e140d04504a1502a0202d1480d03210001408916005040600d004040000c0442d80307402401040444a041f41e40100e682e0024a080707880000c00000c085804100f500f12004520340484146030040302d0480c03600303c4550009035030301d50700c800c00d0002d0f035101d01c1c51030f9588171000c010340c04440290510800e040303c8600041d505100f0b50000074480d140078804160209907100315001c0c0c84e00c0c2c102c00c5d03130501e003004190280c1d5900640d0304248219000840411481000c03881401c9883c2d241d00c1328407000c81c10034001e448040c160960310010b83d00501c000100342d507a40303001e60300ad0b0003988001a5100d125000040c20f2104803160001444020014001110341c403c1c0300c03a003041d541049110314040d035440050281c8100203c190315541c00d1000b8441c512602241e00b6078001514540c5200348074035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 931070251 1250 931069001 931069021
    0x1e031503021e0a1e0e1024020706090b090603070207080a080304201305063139030f0c0f0801091b0809160b03070810120f1a090f0105 59
    0x1071381c2c83c400504100b000c0c00b00543c584030003460384c011a40c88011007840303807160079040300784140002900c800d22682c0c59038290584c041c01618060701081c5043e402403401c00c02080364510442c1d2000d070156000000044034a031090254802900340c080c1076500f81c840340c0c108a80f0f160003d031070a807504000300104800107540c0d645000201c10020300074042c9045180816001810f004084c030750850b500206401440c03500644140409403d85003c418000300015900c08484400e8084200340500c0b0382c1c00400080003040281102c2d00a240c040c4c4007481c2c045013100903280500402d400181003054654940360416103030548941c1550b5031668503170307888840d0020f48101c1d2890200c0c1149040d000340c2c0451140c200c0341d038440612022101c0c841d01c1601f4080100d4001d5000c1e40302072101205120b0b4803917010300f1260300150007081100c3c4141c20001441d96500e0407080c003d0501c544050350208000079190540c02c4406041114005842e00d40500c680780c4a408412151135440c0400040000c03079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 931071501 1250 931070251 931070279
    0x1809070506090904020103051512070611010c050f03042603070f0309031e050702090103060501260d0e0f091602010c021b120a06050916061e031503021e0a 68
    0x2c00030301e2846640c55980055004103405052401c00051030290300c450b5884a051050b5403403e44070003041c1c068641103006281c0300c1303414400c04050741018892001d1651210a403003840301c602c20182d65a44513450010070150316100c00011581d400881c0c007031100c00340e2001d5072182085841d100003120100108800f00d074041c41008011400e10060300030708200c0700320222540142820a40e01e0003800d40c00142810209a20032100151a04010700100700007031604400e2203e59001851110f004e00007181d2582c01d041050f10400c0400c2d610024165a42c0d17052441d40c190207410702c0294141054030a80b82d45619007490090360901d01703c1d12a05c0e1001441c0c0306a0301c4e80e119010480000407040207041410009645201e1040c00840307004034a081c818503000f00c00c201c1c001c0840b03485054514a00340e07125131291041c007100c00d403d409121031101c2c840c03500509038600020306c0c00030303c03500c15811000780d04080d401040701c11503000300b280030114a507180902140c62a050581c4d440181c0c138001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 931072751 1250 931071501 931071517
    0x61b170a0c03090501020c03070309080708031c0b21010507051608090120010e07051225120606031403030712050613140f0c0307050412111809070506 66
    0x800440024264146950084071035869520700840e03640640c0c0c4070182aa0001e0f0461480754200042e40000c243d04424454020040400503008683c50910855242c0c007400020600150344c05d104103903684010b512504062100078031120249d214002c1045c96550301c2c1119494035072802d0301280300030740070360141d8140c2c681d0f980b401c880e030540607070346d2041ca600300d8124181030140b0000035461580070341d4a98a840140d070800081c0202c0502ca41c5441d00d182c07544198050b440708002444843e0001c01c0031001d03441c03800d01c80000e400f244910000516201c1e40a1252030180044d81fa040080c1d0b41c1000c0100e0b030056000c601006d10054140c2d481340320603160b88022860000c00c1e00c4100c0e1050700a40c0c0c4c060740080003400784800741710000041d1180118080c10410402d000c02440ba1900d054454101c3e0302c11140906620f8141400351540c41207001d6000c04142c408119002c01c564140956688034020b00b1340c540604c00500c60500341142a10b0001c07040c05034017030104031400c18400b034039250 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 931074001 1250 931072751 931072787
    0x2060109110412050102160f060501050603191a0a0b04050108010b131e08032a0a3203040603021309050610200f0c0f0102010506030a02150c0a061b 65
    0x414a407040d511000c14001c201215195000d01c0000c1c01c960700c1f017031b90a000c03500804a03540d03800d0032494040200c070816004548a080140140b15210348010f180c68200c2d020300707200249000300341803c02c071040c0008003d1648060500c1c2c02240c7c0001042c09402140d000307880b44c02d4540d03241c01d07004d1524020a00704035006800c40404200202da814801c841102c4840f5100344070301d0300c82140d642141d01c5054010b8403038000c80c220b03407014070901e00724a0710b26004d5406008440751542d255840c60820b6980403241d503406100e00c501003481c4082c1c001c244002501129071b81ca5440c40301502941045001c2c2d40e180100460024400340da82c0100e1303208940003071182010307085104e015100d50303004c1404500b46603c10750001d91444400c0100350402020600203043d10702c0e000b420440e80c0e0190040103411a41481d0034802c0d030f40c600040100009504842213500d17880c07200040c00d007030700030764020810500c0794a001e6014080f655100e0410307014295a402051840b4540a89001d245800107010b8 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 931075251 1250 931074001 931074007
    0x14151504060e1311060f0412111206070807050930060106210605040c0c02130e10050601021501120308070e01051813020d02040f0906150509011407030503070206010911 74
    0x200307103031011401329500070b0116040c8161101e1140c6150043c0e0892854030180104210500500100380b00440c0011506910700424092050f43c503190060131442c00e02c103075040829800c9000303006031414404080c19a040100c44054417900100d00703e4040585c0140a0421031006400440c01c0b5040e15001d85034140c032081c5d01d5a504601c0880441401d410300c0e07407400d0100b1507a80c1d9028100800510390384d0780007242018010000ba904881c040358a5861070200f10080c00240854140d4180100301000500c81e40d4800c01030b130504084801040030340c103950001185a41386044605c03800c501940d5141d42d03544d1008010342da030280030385205000c104140110201c1c10708013044403a4a100c040c100030041c0c00c01703800c0c20003a41c102000250070142c004c0340c240888600400300ca801890034190602526141801c045000702c0103640010401c0800503440342d007640a801da1311304988140908580d00e1035075080080c500c0d0010b8030380e000103024400002030b510b800c0b0300808414020764154985 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 931076501 1250 931075251 931075253
    0x151914031f03020406030b060405090d0f0c060b0414040506090102040e18010609020c0a03030e0303010b030415021905090f01030605100309170705010608070e0c030414151504060e13 80
    0x1004050108a10a540c500503038044010f1301d8500a901c020751180c1b5628240741021420070007601c00c000e10410050340081c088039080d95124401c80d200740903e00340720740001e40c0d50925002034259056000e8215061814160408107059107072807180d80900182c41c1e46841c0c0020b80c50a0303125520540920070040720102d0b00300c0a14180301c1c50700c109241c000141080c0c0d100d603440240c0c1c002d81018403003030b000012040d0606030103005034080a000303103018500d95030500d40c030180c180c04050005031544106084c0c5e8101040d43ea4100d40c9218860301c1800d90418103141d004000703074040b044981c081c1c1c040a00d040300030b5000c0d0151a040c0c0380b0080c16204c1340300c1d03030082c1200203003ea110f003951002d0441c441106c1c0100760000a0107000d0243c000416001d0511a0640c506140da0303200d0034403101302d10200880100c13503105494125901003010008414110065440c00d10901c5200d142e00d8241024000403100501035001044c0c0299402d024003943c07090448000c3c1400c88098800c80d84480d044c2c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 931077751 1250 931076501 931076521
    0x702060a3f050f0f0408120114040f090302280f050705010908030307020d05130803030a14010801180f0c03050d02031309020f220515191403 62
    0x312002500c0c0c9000140a070030324030802005800070340c1c1ca4071420758900349024152035075020011100c0c40e0350000d020030300303101d01034403000300380184140625900c1102007030070400500111000310640811020503541c44441d00e0030640c90000390244110f20708114061340306568012030702d0854040d005411145d203000301850b01804005111015602c56000450004a40041010040f40200010000142018000340580c4010381162050f5030080c001c20846e41d900060400e6480f00d0751501b25141c41c0c80b18035174140040300c0c0d08a9556808007204015210600d5401481e0b01020012003503081d980c1c074459a801c840b600c0364050b0700c00c00320303010042c0840c4003055000303c0f9034411048501030303e0b9641c0320a4104a2403916240041e040003400003a0500200b103e8005410140c808514100d45d00000f8140c521550251003000c014404a11840d080301c03101190040a000e07054146e03031080030a02003e0b90f405540d40845c1221038020811495106030081181080045001880c545076900c0710 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 931079001 1250 931077751 931077757
    0x2010c02010504090603080403140319260109050a2f1803060414011a0904020409050c03100c03061d0103142404031b02090a02090d06230703060308070206 68
    0x59041c00020440091841300c140b003482d00441c0541d00c420348a90852500702c14100103d80b00c00e485901c203000004040001d003a819080042c0ca08125044c18006540c0e200c00364150144041582820000084e020105410461141c010004200012214405c0c50300701400030300016680201c80d10000040491814010550075002091400c0500c880b4400249000705c00c9408980d00e0341ea140b0b420101c09801d0240d802285090f9045800d0b4100b0f20001c0348082d43c00410207881580c0b54070007801440818440107200c088090300f03507824007c0704e115820140000000e0840080d16001000a414012035082880710403c0035103110541d10b141c4400c1419050188424468003030b0b80602401c03065603429814192402c90100e0b134880c50f0509000c5c0c50081503003c90036020444110900045e56464a01a0301c00d03190400140c0b035a41420206215209142005000b24603048400c404259005d5604458881001e0240c51550f6601e400b10709840003807000500c0072000780a1007006103403400107 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 931080251 1250 931079001 931079003
    0xa09060b030318150c0a0201120b090c09010f0219020d0201050d020310031101050901120c20031e130902031e130b0601020d05030f040f120e0a06030c0c02010c 70
    0x815941240c0340020300316800381254440300d0b00d400c6500121414a810000850703c8200006401c140303451107400c2d100c02c6160802810010a85816500c3c05004e5210245c00c100141c42c3d800d036880c5c0040d000420f0b91000305c04501042d40b20b080524282d20000710141140c1c0d00041005000d140341d0700340090300b668140c0c100c3c14081e0500000560760104d04c041c510881940c41e004035000c0c5107040a52001e0002c20000b410860100902901e50340c02502c4103903440b204400004503072001003001c89007941c1c1061540614843c0b021342c0b0410000020240000c040140305584002075159603013203680c4618100210107034840f5108018201c01503000d1540003d408003414080701210180083d002011581d10400c200e100000d0720078041c056184540c001d000780000c0000000c0640003510301c0c04000c0820b10001c4680c2c0000d020841d0b219280c0e21040c1d805656081503030070713000d000392019006000c0f06000b01c4038103c00003859442030040013018000c0340c6641d00f01d112690011036041c140c183d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 931081501 1250 931080251 931080263
    0xc1e1d0c0f0a05090112020c2e180515062101060b040803120c1c05040c030503030f010815010501050a113906040305061914040f02030d02060f0a09 65
    0x88509001c41c50480142206081035540702e036540842c10002d001d044a1101603030601d03105006201011100180385100881e06003140c0a002042c108600d00b114200b44007204610309159228400d0004512244040c0e0310550555101311110528201e2601003210010b5010b40c903980454085520408410314620060002251071501c83e00506456841b50380480019880060507221801e030300740320141c000d58400d202c5450703c0182421607898a2156109038840f603a6180801d0070003442c411100015544078050b42c1d240c0c0342440c04134641e024244100650360250140140c02600015030f0395040e6035058450b50f08140c4100d1088035424110181801c2c0c512852502c0701911380d03845501d1010480417440b0f8111f10fa40c540708d110000200c0d400207802018103000034070000d500410842c0c0e0280b02048418020721684a0f00b1000d0540d800c010030f8800011000d02c42400042d41d003024505000743c2c102c0d001d60108032403c80e40c90804072520302c1e8200c132100105000c8000ca03000303000811b010301 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 931082751 1250 931081501 931081507
    0x13080c0a020d0f051e100c050d05010603050f1302011d1909020c01060501020705152a07060e090f0a1e020f0309070501110a0b220c1e1d0c 61
    0x54041403002e040c0c500d0540c0e03118002400c42c82040310400000d03c250b03501689205107010525502581d60080e0005111207075181d00008000502c00e00a07101014a4400c092001c0c0d41e50381000742c0208800d807140500b80f4a40b00005a81c40070303d5990740001a8181d590707924009003000343c0e4400041e08241c00360302660300302d101e02407030820650742c0000d844040030040c0c0d55225220105e08442c09944507906540101c3c1003001595925074810b2441302440c980c0d296542c1004120090f080c41003001c04007080d00c1901c3d000d2600c140003950800713441441d103c010500d801c030310802c20b601d1070464a26442c040c03401c0001d1082400b540001894244010311444100120310001060740c0003150500f986a0000c0104148040c04029241c0105001c0c00d200d150f00161030020740e1105c1a035030019211b2480b01011800141c0c111000322a000c4140340b148495200a107000a664903d5100b071141c440000c4490404054109517504100c0b044060040c81c40003003100041072100005000240c070756414 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 931084001 1250 931082751 931082753
    0x1a040902070f0203101a0a060915020102120c0d15121403270405010b0c030a050f0d180302010b090603033010060801080303040c0608060a1a0d05010e13080c0a 70
    0x300300e00d003101705160b00301003000991040e00307a01c1400380703100b0b082c801d41070302504120711508910350805441c4002c2059800d80d13200c25044e0301a101d444100c90f07481920340204031488811034040c3c0100ba54010041c481000d02d451175130341c440301d240a40c0014100c10f4440f0400540307000149003100f030340030341034906201351240e00038014401e82d9034a00e420200548810502d00d0903226050141040c541500c0c108419148001e039203009440c2403905005000480341d04124000058420182c43c2e50010710410b042a10548001502103008401641c20500f04540d180780c05d101c442d2003404d024006500b0503081d9002c1f5001041c0d000b08800000c10203a508409912100003581e11925109142c040c00a1910038000c04d400416071140c840c5400500504c00081c0c03002044d202110b089180c0b200035902d1b0700c2c0006a48000c141c1c00f8520301c24a0044a081190005d005019800d1140001b00080da9844c4840005800d08880c0b0b44082e86016100b48000340c00301000d0704606101c0c0041720746138070340d03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 931085251 1250 931084001 931084003
    0x50a0e030f120711060304080703180e0106032a1215030c0806040c080610060c0206092223010b03040c0801090305030f1302100f170c0309071a040902070f0203 70
    0x1280320642c4414001044024440c0356410b843c940f201c16143c840c42c502d86621351084d01c1c0603081d001001c000d035805404d00d2050b541405070000d040c030b1101c1003215595800d0050001c0a500149030503504a411a03411741c4280d4041c4080c07284c0240d00d4a542010304041804000c01d2000000419049a90408404510300c0800030001c0c00481d00100303820f040c02c0c18003003049400c07a0f101070010743c001c808110445100c14404002c58105040039891040d00d44009503041c044c03010000d4000709000b4281d0720000610000c40d034a05000d460400100680c000504001d4280802100044803d4001002403042100013958440d000b010314152880c0c031045c5240c20f4491444040e00015400b00a100c80460550711440d0405d80d80401c180c5c40756040d501182454682c50860030a00141c0340d10440707a680031390f12030300040d4003103008180c8038680140b00b0311498009039414556441042da0100c1ca041041e0000c215844200c0c03c1070741001d00e81500c54000e903015560483d2420001d288900050320 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 931086501 1250 931085251 931085263
    0x30a11030103060c0908120f16080327030a140a020c031509060703020304020d11041116110109080709020901050d020406050a0e03010c0f180305190b09030a050a0e030f 74
    0x100c00c3da4041070f828003000c4020600000c40d00008041d03080444c45041c0700c0601c0301124030385680100c0791034643d81d00501800c00300c94950000742120304004100aa10245e034940c90b403402002201881d1041c0390940059500e004011000b80400d100c560700415004540c0098404401305104031a51000700c1c1c1d0129080050340ba0742100101d4001c010300440b4001030041c1640503403545821800e41c609900001d821102c0010060002801c0012252158072150800c8989200007510316a54084180e44009055210348090360350016800d07856050758814040441210381408c000c1040606003184980254001040300d8107012042190800a03103281c000381004000f0780d1103c07070310786a010304080e00600781403c01314800c0c0d141125000106802000e40981c0985c607262101400c14144040007207041c3e1394001801c548184860b0311f01e41030303e50f2107415043e841f400042099840b00c0c9545690f901402d684c03403005c00c40038000301c0c0d601c5209005c801c3c114980141268041d51035101c40c542044 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 931087751 1250 931086501 931086503
    0x7021c020307080a0c090c050904051b031005150c03041707080d0e1f08130c0504020c0d0f0c1106211008210403061d1c0e090f010b030a11030103 64
    0x900003035800001e0092035000302e401040d0821b024020801d41e04401416440b03000c2c0c250744038655400119001280e01c07181c0c03e58019404e00c10550302d04180602d15500f030724922800703114840c40000c0340003440c5180282c85002c0002c2d0000c5003428148081014003a8101002d8000b41c45881c800003600c1004104804223102d1540b15030345080d404100b07004140c030b8001a400796000a0038024100c066114401d15805242d03c6528481c90009240241c481c0d2008c2e44010340c07290001c0b80d64861400c0c085000d03160000107485103c401e00c0d10050a5a08800428000e804940880e603018071604180380103081c0714a100300c400460f10754848046603120303415102d0130000308480e881840070390300c2003009020400c402420203110020480c80300510748a68000109120789a191210112003500c0754541c9044003141030320b180001410444480c0300c00226a00001b8141c200c8542043c03d04d040307a54020b07881001803140503820440180d80d250301c094410300c0001e64961004002c4541c840145000e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 931089001 1250 931087751 931087753
    0x70212010f0209040c02030c12030709051e10080112081804051e070302120114030a0b0906060112060b0901181203180f0503060a090f2003060c040501020307021c02030708 75
    0x2e054540521085034401442e180030340d80200310300d08d80c0400006080d2101c0c030102d040d6a589550365807044450040710b900068120008404003100340c4250700030304905003001e5800c134903603868420084440d800c0a2041006046c0e02c0d90700f000214802000070580d0309400e80c0030b400355802d40d002142c02c0301c000b1140036102030000b4041e0485c2580400700076070031000d681740560900f00c1204450390030701e106100d44103c0c8880c1002d48203458405005541d4090340140c202d404030f140140c070340b5840f0002118010b000407408010f01c18058024031483c002d40e580a50f17241d00388201c82d0019280f242e00e026401c3c0b01c9030440c00340041d080ca0040801c06645100f60f84610000d00c9030103240741c0398425a00036072294154401d041c41541c0300080c4455101801010106d41c83e6214200b903a00040c000001528102e141d03110a54007409419031213420010940884280340d44d0740760b03e00e6460142d80505030041c5c01c100154405807520300c0c082080c0c210b110190601d80c060f25800139240c026254494001 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 931090251 1250 931089001 931089007
    0x1e0203090c0603061c0f0803040503120a0228090b190e0904020906091b1b0f0703020f0f03010f0c0c0c0e0403080c0711040603060204050a08010603020a0b070212010f02 74
    0x1164505000c220780098080d5841811428001c0003c0c104101212a070f4a0039030308141c29106005141e950101d0090b009640d441d5a03090505010b17840c1d50002002c0c49180a104011a10b40e1005200f1201c212240f0010251881202d0050000d07002c0701206e0344040011002012030321007600070050026000c203800c401d60f9407a030780d440034000c0f070040309045100300064001c02026803500c170509a0700c41001c179501c3c180d0350f44a0141e60300a103010f00206042c1d02c004103080b40c90a15a0840c03490304403099040760010101442c403c0d640d0511800003d402001c0e000501c0540c0c01c10b0380360840c49040003000420440d000e4064441203420f00d0358040000b485d002e0304402440100d000c0c5602401e9815035401e400d01d0603490140000001801f0503140003030014840046c0005407404205045006005101003a96030078860060b4029000d02c0f0b00c90000c0000c000f581c0c87d014030610007182c0d400381001c55007902c2d1001001568004100c244c2c1c110f0360708440342d00c4411081c80343c018400648900161 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 931091501 1250 931090251 931090261
    0xc05130b030702010f05040b060907020f0f0610050d150c030605090f040326160903020d0b01050907230d0e030310090b06092107080f03070b070206040f030f031e0203 73
    0x209644182d030080417040c3c030b89000e00c000f00e980c3c0d401c01c56100340240c4201c2915103500000701c0c41c01290039104901401100180501d6410105803e40504181001c5110300c80e1500e08003c402030051a008001d030030b099a0f4203150000f1504020f03030a0009050014409951750003140d4100c600700c0d003440c1c2e41c03000c41c0108410150044802c1010544c040c44185403140c1c01810801c89410140518001500d4081d9001d0294410010680515805404d48035280002d05c1c02d1039940c0c4080c002d051041c1740e6140040d8041d8483c01d0078001d40c0d9800c0d001d0090141d41c2c5081e00449521901c10092155250080307801d295400300700640c01161000a001039403450842da0204031441032403d40d01c5514200b01c08805640d541001c5885c0c0c203010302c1d00c02420168204200c0c54801254008055405843e198802e04040030014022141c05032105100030350b17070100120307191041180c004111000003036004010034402c0000382045000da040c0041d41c80c14607010b00000c114000b428008040c0c00208101d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 931092751 1250 931091501 931091503
    0x1e0c08091315090b150711130c02010b0301150e06030f15090f0111091c021e0a080c0307060819020f07030f09050a050f012001060e010f0312030c05130b030702 70
    0x54003c003620001000222580302c00506010b40c944a05030101c0d0022a81e40184564089145c1d16a107000f0440071140c000e610003540a04065200320025500e4202d080d00c9a040600600b8007440031212490181414030384076000c9200d01a000603054824000c0055240c2c0003001031500e8000440c841c109107182564680c0d00d0040d0500c004291641041210050101010300747c0d02e804004070341101d0315039402d0b0f0400518204083c0069440301c07000c9003032611000f100000407601c034810340f01c0c00042ca0721041c00d1580d0380c1001c6c1900750150b0081c401000502c1c4036540854201008142c00300c40c1c00ea0804520040e0381109181402c8104001146010590843c0708144048a14202003000d140b401000400168092060300d0041c0920102450168460208a103610b904104681d00360014042620300804040c003415921003419000800c001d2554140c1b0012203601c416111000b04040c0021405000d501d044c0d441480818030502d80941500d4164802038011414801e4892500c40300007 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 931094001 1250 931092751 931092791
    0x912102415050405040b04090501051906081f0c2c01031409120a170f01033518030a0b1f050109121b0b0901030b011e0c080913 56
    0x10000824041d00318620316005015101182c904480c00192a240e03040850301a020b21880200b4551809080242c0e150f40e900048028900c0707a2010003520791684200c540e21b1046010705004112501c40c24900743c551608500107a1141f880d01c0080030100c0300b0301d401000b00008080b01c00e2180510304001550f80f511506417202140000511a82800c60025032284141307040c43e105448002150690ba900030142d5110f120782d402140e10b05480d14a42020b084042030001b101c2e10000003031498246400000c07600d158005400180603422489c032400b00155004003403c50503407107548803406031030742c2c24090150024010812060030b8074041c500550140d002d00d60f5148560700e40201408075903446000305042d994081b400b150240384d40d0400800300c002c000c00883d4441002030b00400c800001e4005072035144000c2e01c09126040c0c2c03402c015141030f0000c0d11580d02c240c0c0b40c507000700324091060b0200c0b04103034021030081c0c0c80d0171035480115038080c2d001c400300c1d4a01512410f410300c070720b840c0c0c07068 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 931095251 1250 931094001 931094009
    0x4031505010e0f16141c0e07120305160f02060a051801110a08030c090319110603060114030709091b08090609060712020c030414040f1109121024 64
    0xd041c1192400b00f4510071540024240a005c0108401e0112548480c003001c0750036001d04082d1990382c0124002602c0064283c015003030300750307002e04100002c100b00c69001000c0c40c9076040d111103007001e40301946100d4840e15118207035030507907200b0b56800140e00c480008010b1420940e5600743d0b0740d800d4459000b9038810075844141000171841000b200001c02246d0308040681c0584856501d454005041a4500840e504d040d41030040130f104c60b500066404481116500c41e51101d02c1420001d0200800c1d80411600b003030108600c1982c10028100e484000e6074040301d5070034034110840c0c540b0341080032140d2940f18845040c02d40700c80d1000540d0440401356000c0d45260007401e4925002103540e8a501c40908181d080c070044058403009840c0319016a54040f0407682200c0e01e5a549125040c80880c0d40c454082c0164508021060810300c41c5c000c1c030300c004105045807460451940300307110b0842d440e64404102ca004030b481c0b0891030541fa020f1503580103a0032207040d003034484480003802c90012980c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 931096501 1250 931095251 931095271
    0x50d1e020306011805030c010507030c050111090102061f060f02011808030114040608150907030510090b0c07020d031214160f02150a1508060f091e060105130204031505010e 76
    0x30041007030ba035001881c7c00a42c4002c0c41d00c2a10760510303207015220103041e0701d0002d002e54240502d01d261240400080d101d1010243d080b40c065494401c03c0002e90092108281000d4580c0c079020700c01c80303008207902d01801c0001e1000044400b070380d0b42c901821140d0220222841c44000004000742c6000045489024908540410110303107130104a03640c408a5a0300c1002c003d0701c80c4002035080e00284107900c0155008015180803041142d0305000038491850120340580050f80464114120304c42500da22aa01404150704500191000d50b9454003003100c0d0750a40d9140c000e1a0f0320310700340c410320303030300503000107c01248c07030400c110f000f50401110110980031580903000400d419545040e08a80007805c03010300180110281d01c1e1420142d2003a00081000d201d0381050014082504071030510a243e050300350f5a501000e4041c58541c4404030b0b140300802d500180c014032040c07410400c0201280d403588801440d19a5070765540103054003510028000740e0b038a00041020b21000c0300c0c582e070f01c07240100c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 931097751 1250 931096501 931096547
    0x606060a17240307060c1e120807080a090b070804170a1d0f0604090525050901020c190612060f0f03030906050909040803040212060a091401020403030e01050d1e02030601 75
    0x40001b0000829100050800c4204040203c01440107040690350250042c07826052001c0700c2201820b405001d0311107100007401e8200140b000d620510422076100d500c01c07603507021038403619002c98044001400c03d503440007000c0741c200100000c060003420030752502d80b00e0f000840b4a800f40303010036402c1d500545020f81c860040c030044941c0c904040320140c900109000456803100c50380c01d5030500040c001c41030f01050008102c0700c520303003140140c1840b503801da0868465a250405100700380b140d510555a0300041c11405001c040d008604e5030300060b01050002652075a070f44002c85003c252680322030000c3c030120b8000d100303260b0300014100242c1140d04107913260030201c4010890b803000050014200c1500400841d045548001c02080c2d418032207001c0300d12908200c0180002009114421911980000c0d0380d130b0310710101070085c1d0302100d0b0135031192510900090015035040c0d10020712030300c116549201000c2100d035140c980c03884001078400010385038030380f810001d4010840000600b03035a040c4a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 931099001 1250 931097751 931097759
    0x507181a0708070c0b0f0d150311041805060103031e0525032001020a03061e030f1506090c111609020a120e0604021801080606060a17240307 62
    0x3200845280d280d210b00c5039981c488007402e1034900d0101d25040034002840024408916010700000740050454207071003086000a00e0503000c00d10171403444014150081d00c3e88840c041e2600380d202a05007c041309000d00350b48240d594080c14a402604101c000c2002030110111201588a1b10b246603036960604919040d885848580000c034200409044400b000e03c1c6442018802d903228402075039659005540d40e01c040422a020703400c800c0789100024a0b044000840b040039100e103208240254000c9012a4110b48a24143c00901e040a440402d038000001c60030300074a2040400403c4100780c00140a00c03005001001c0c8a18050b4500700d03a40f01c48594031010a041d00400c040361070703d142c0142c2d0380c0b0071980141c9184c404051100802481c0220310604904c000c180103214600c00c84121402c0d00c54071511120f540001c0c019150a0742c402800141182001002040c10000c0350030904050b840d40660100c10100c02c40e180003d02912042c200b4042500c0120b0f040020030803409403c80c1420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 931100251 1250 931099001 931099049
    0x3060212010618120309170d0e060a090e04110907050a030b060301031a180a0f0b1f032a03050c0906010203030c0f090a03061b0e0409081219050718 65
    0x100d0040388a44c0320540507400401d40620f004400078030f4945501e050101c3c0090241d51180d4400320070002007800d90501d48072a107400c000b02d40c055129500c40c4040d2908000242c0c0102500520483d0740c503a070034266200c1603541c40004ca214050f540c0e9074503030b01c1481120040030b0341c07401e40915004000034001072000032000c0c0503000c00d0442100d00c40c541542c512a145441004541061341c090180003007203001d02c2600303001031260901520001c04151a0f22004015032040b82191010300306441c403040c8000f6050540f81c82e03440243e464070b24106140d150246d240b8521503881200c0581c469441410981456002941e2001d0f0034006503086140481c6854111b1048564055104000042598540d0b0b503007100e40c03014640000c030030000000b46100e88034036031704041e0006d00425400d21484c81140703841c2c001d40c140168013980c0036091605030b41118002900103010408248030401c0401c0c00b00b82c7d1480344078440c240a0342e8280781200c5421500c1c0c280195900301e01185010180d02c04180c500c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 931101501 1250 931100251 931100297
    0x902030f070e0a0f0909060e12071b0518091504150c052206020f1c0c0303020c0a032001020301050a0b0c12030f07090b0915160507030602120106 64
    0x4410305088245102c1100041ea02000a401141d9421118080415606490350010520500c07600040014104113884555140050b095420b41601b04001c4440050710903c1c0f0308213000c081101c51070219854a00161041d000800707280f2502a401c02000010f050401840b02121200d44070301045043c640c0b00d403c0c54405040d690345e1490b0701d540760700620900c610221010f0815034810741c0c078009900154200609618890704006100e041605000b215010800d040c01103001140714042100e1240c0a5a0428100340305805040e400e0128540f40c00e41442498030041c826038a01d91220280214510391030380e1014400a20ba10620040c006500e48021040c00c1e80c100341c5026403151010280c1c68504105244240c15003400403085c0400351401c600002d016800c96192042007545170f01c0c03021514040c0e0402c555000e00b1418124079411403000007070508080442c5242400c2207540c640d03901c0d05000394021121582d000880040c0507200c500624003403c1c0525000d60084040c41c0784d010212 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 931102751 1250 931101501 931101511
    0x20715020901120212010e25080a060513090638061606151a03180f120d050f01081002030c132402010509030d09082109070902030f 58
    0x590006800910368020f4540e024401403070007080d591044d200400c083e51000030300c03503401001c80780e03008101d134886901d800d102c17010108200c1c0c040d65038502d40101c4107984054407444150355500c00c01704054843c1c00e6000b2054101c032201180103251480c202003120407003905441005101c0828540342c2c41018a180c40355044514040f0b44440118009511032240c2c16000c016140c001c02d0380800c2010300d0b00711101c82801c080e0340c10300680d134402003450784948040c26414400410000100c030303007812660340200029034008507401240c3c0c4c881500d1030200b04083c1204800e90110b84101e16101501585e940114403c8440e0300e55450154802c3d529000c01c0c000000258003c00040d184048400517100d0300820180d0500304280d84141440d503048011081403103030054185c080441e1401401046e018610303580040d450a210b120040d802444454000c0724002410000112007240c00381c8403012241141140080a0508081c07082c038000140d4041604140107004001d0759501d851038030b503440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 931104001 1250 931102751 931102793
    0x703201305190305060906070c030807020f030f0d060503030a0f080714030408090f0a2306040f0e0105010210720f0807051002040603021c0207 63
    0x492169031000a0500035400a0b9004080314a2014418070720b6050101100e00400940384a030300c5031400c07203032200c0084502c00045803565182d800041e05ca403440c20f91007403092060301d48d0b4008054209040da400184a01d040321404680420409200e20078040103042c211b00440c50480c04520113031001d16211b05103000d02110303400040c0c82c1405000646400281c02000795078074079051a2049a541008100901038550481d048869041801048080d038140100b500000300d52100d0780c001015003991000d8100c10203100c0014035603c02404c0402400040994140d031f58180300009252280313414104200505100c0305200d1881414100346819607006050211030110755400d12202e644050681003000500c00e4280d00c020a540d1040c44603c02d100d00400304071040c200e540007401001030040c1c00307a808510b613000026240e400600c0712512500a48613400102c10181080307800542c085404a900050b8a9070200482d0509402d14000d48404608080294035100301c0303141144049425 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 931105251 1250 931104001 931104007
    0xc020321070503070849020c0303010807060e060703050f070f080a08010317090102060a05070e1903020103291201020405031002130b03070c06150e130506070320 71
    0x41810315411610352540100480c1c1d514889480c1c402c5441d0b01401c0300e4000300c8500c007000800e11000c1c07106420024030003100081e000d900440c0354000c40548030b030049041c0c0d0342080784008452041c8041e5000b82100030241c40c060345040809480f0030500080c2c035114600c00c0280100180d0086c05072049a280441d00c1c40e1615031519260341240f5114502070b00011001c6007600c0350540c0700c45c8444c1a41e00c02d901c0340318203e03c0040a5212402070100c4c51707026800a8000482980e00c0b584165805000b501e0031009100d64034001c24800345c60322111f022994081542441956014064a00c07440601c500710b859812000200d000c1d040303a402200d0f80700e010710442c0b06e0b0f4208801d405844c0a403000405613442100c0300011513001b0350041041e0b0b184180a0100005c44103645000d5901c82c0d000781c0c40e11086000c0c0c581c1d0303c2004020203031034100c0c1c0091000000c2481180c0d0701c0800e00c58401e60400389203192050525a181c80d10040018040600b40580720040e811b698a865140c2e4020301e0450362 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 931106501 1250 931105251 931105303
    0x30a0b0106081b0d1b020d050418090609080c0c01091a0c07030611041a070b06010c05030c03030412020f010504050319021c03140a1a0906010c06110309010c0c0203 72
    0x40051801c0b040441d0345607011030644d20586950348401e40380000789684283c20310201c07100781c1e02d80500481540125400b80000c0000d404514500344401514460004e40491561f44000c12120b541c4c00a03100ca05020402c003c207030768108400400018242490b48440c2d280c10352080500394481d51200e48aa404280c1c5007411400b045450080d50f40505c1c14015450382c0b01103646140c00501ca4480807146031b000820060640c80100d5420a420808441d8a03903203000054400110f0b004c0b080301c0c1480304108141224509201443c000c0b031144551286050f10414024513000e64172460070480c0e490001800001600041203940c60781d00601d40076095034003d40300b07904208800306210040c800481101c030301c442d030680c00013005110354101300d4216280d41c1e903a1400c0ba0003020803024000b210007940041494225442a4402d105241050441d4095510601034072040208144c1d5100b010041c080003140a003d080c01000741c0340341c1a4035480c1e1310f0700043c1c3d0700c040840c5014450451150180 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 931107751 1250 931106501 931106521
    0x30f0905030d030f15030308060f040504051203070507081804050105090907090b120f250e06010e041e05010f080d1e0c0c03050f0d1409300c040b030a0b010608 70
    0x7802c00048505c41d4030310303c1e64a041c00780042c0700c1241d440e4410119144080014a02440781c5401b5a4000b40103081458900b007082c00c00b81e0020b840391040c08030038402c034000a140b0781c0040500500c8128900e454080130740a11003510010b80101e031149803103a04028030404001408400c586001c50041034100090703000c9100802c000c2ca2141050081450400b001100007175201001d1032150b681c0101c0c0d04139201100c062101c240900c0d45140b580c407004c540340c2d42c072820050f80321120003400091317284441400481911b15410440d8003464456004201c1e84520341c003080300401e140784c00b0781060640c03200018584c0c250040d541c19a0b80030680c80a00c1c1621818000000d1070f0310a03041c000c2c803612401c15275501ca00c40f01075440517201d003500194129104540610428030341c100c10a013084000c9082110141d507800c03070030304800403c00d400080e035a12200c40b034034000c05020252507120402c00510055130000c514031806540002441d00000b4040d1081c03504645c00361a12118580b0790b040c400e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 931109001 1250 931107751 931107761
    0x3020c01090b15010c050715050d1e0e07050f1309020d1b0f0510320c06090a0c0e0901020408030a09080c0306040209071b061107030f0905030d030f 65
    0x821029032a098290080000488a45000d0250950710740f0007038846800450f12140c0c200c030014500d0304620410880d0207481900103402c09a0341c1010b0781013420f1029900100e03403040f814400400c4041d0861184d44c1000e04c036101d0061000c1e005080428100b0006c81d00003d52800000d01807800c1034800d00c1550030580c4003074003140e8000d00009000100e0b041c1580c41c0c4142080c1902502d42d07041002440407452440301c011100c002e0105111001401e900b80c4004074403280e81c40b41100021051040d00010300c108072405a15841e103946c9032043c1c00b441c9403500c800200101140e501800c110004100c80c13007002070440710b841c044c109650f55900403860180c060351b403080a46200200388040341395004051034003501c3c07690b011200c90b01800001c069540e034054401a40142090011510b4a807042c4208150054001d98801340700e012030743e5440c00c40e2030725000c0c8480f019000c5045010980e014124405551961030040101c42c280350010307440e12480c030a0001410b5499144240342c041e15042 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 931110251 1250 931109001 931109017
    0xc010c0f08100e1b04080607231e0711091f06050903100b011b03050403110102011a041a0a030501020414010c110d02040f230a0c05180d020d1a24040c0302 68
    0x555500b4180b100014000d0b43d27900101500000508036800504044003041d11020305043c6007142103074129040e800ea50360301508082da41900503001e08885510f82c02070aa0140002d00e40002c40e0191310b84102c00700b185180c00290401408100700380e041d507000580300d03c01d8040040002910002c580060f1464a2a4045040c484015448103018140c0040181c41201d004016040d02540c01d50012800c0b501c1240d55003201c1d084008046029003030a5100c3c1e01d0012660750307404601d0b40c4040005d280800380741c0c405c070386580d00050284003c2c1003070200f01451443c28242400030014076580c00882c0c044020540e0302071045d82010304159035480c2c0100c2d0304401c040000b0030040b002158440b201e981ca185a003050a1a645d011903085030440c440c0e802000b040d9900c02d070408440031411050944d08030509070b03220190510200251f6206aa51108248030352960a200c2c4100c07016036a42c6180140350484070440d14110f40c03042a000d5583c2000c0000032200041e90701150700b0107600900412403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 931111501 1250 931110251 931110253
    0x1a01180522090c0b041805060607232506020604030c0303051e072d050418060e0f160f1d01140a0c02040b0402090f100201020c010c0f08100e1b0408 65
    0x40c0000307109034600d000b00103844aa1211b900d00c03204d007110745000d8800581e10a60807010030050a0301107048112080721041141100c1180d048000700311502d068039039201c102e011121050390b02000001d0300b210000818260018003482c0c40c0584000c1e0500540307240290a050301c0e08000b803540010307141c0b049510000e03448100140c0c1040400107203a03414000450a092049403150b8140c082c01d00082001f00c0d406a072084d14190030708080c4d00c5403007054183c841d003240e15003102084c0ca0142020b0f245c4501200c1c0940681480c240c48504080c4003c0e84e085801c0c0031700311007c5c2c0c1c1c005911001c10040301d0700c0388008038003064a410048500c3d03200d040d01450980f07000301d89021340d10340c00380188507400d008490500107622000d0402003203110700001c042d8014501d00c4070603518103090880f11142c81083c000103060140b062032a078255002c564104001078040078640440c20341200b0b000e90440003030650034100c2810420102d980070005040468110308040722491541d00741c0040b10b005c0c5c00403034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 931112751 1250 931111501 931111523
    0x80a06030c1401080a050903030c130b03131514180c0a08030a140f0904091a0130051b0d1b15020a030914010c061a0118052209 56
    0x1e85240c000380e40350800b0390014a01001040c20305843e130140600890700074002d9403940d240c942007407180742d000101e50b40c08020300b40380005213a52400091031040014054815180740c0928018480038403103180103608924058041408150258400340e00403c0783e120300d04803c0d00d040500d450a01080e418540c010200d1202096080d004000760130458442d480390201005c0039080744a20f400f41c40720990881c40184086403141c074164025100311801280c05030000007100d4024000f800302600000d2019808409100003860f0044601c46034400c2120030880d11072140e83c07040e0700c030020340c0c0f2000d4007031707400802510096540102600302d543d8403041c0030b4102104e4020300c0d010000380d445840320b00c0000b2a4a0003696001181603040707140c1c1a6a0800703a24185042e9004401002007460b041041001c1e218001071003c0c860105800354400c100349240c421240018100d0320645120503000840f05410009511049981c0322881248081c60807d00340a28010005050350b83e00030b03100712201c3d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 931114001 1250 931112751 931112759
    0x50304020d1e05010b120c060307110a0309081605010c0b040c05060a020f0f0c03070b0c07090c1701060e100c020303120708040507050d03050327030d0b040f1b080a06030c 75
    0x90b184041e01e20038002806411108030070820542c45c0720041c1501604680030041240c68110b004540c085a40c0c00e110501a6401d034115240c090340d07035400c9010418511040c08078900c101b203819480c0d1504d144e0860704d1410030340000c080ea60f4084c4000c02440240001c1002c0280c242c803244040d040141c0300580711300c44014020b40d290201d2020442038042d8040d6019008004119100444000340050100300e2504000c6e00c4540e010070706140080c0a80440445c0d400c025005003020f40720140e403496074800c0d030005c034404000c6040e480a4144221321401e06001c0c2c40308103540c180c556060070086003842050000c40d045124281001843d49812804c01080a400004460089010340d044449003501ca100348092120b06a0015000c10810f000080040c0d112a070102c021071161650782c9882e44c0410f0810303243d60410a0071140803501c80321910740a06251280540a10800ba03082c0300454282d83c1d0341b80240454601e1004100c01a00042c40e03158154000340c1c01141c1c00055150400e680d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 931115107 1106 931114001 931114043
    0x6050a0501080a0209070207050901061205090d091202041e060e090607021005060d050a03030507030b0303090d0f140d0c060e160e07030f0f0b1f05070201050304020d 73
    0x340c132402160701c0d200c8190ad207000f403030103172988148403420000e464292040200309800c0c6501540c0c010507056440311440007212580f00f051026140d40d4004a001b60800d5a00c0c05003454400c1140c10091105a00620840d640c20144d02520381b60749410f50788521080c0c1d917440c0180d0000f4020760100d00c05030312454000340000d040000d03042c107941d140b900b0800d04079415400300399524204544113030580140410004210091486c020304040011603015842c0000380500e00301440d01c0c410486a162410349100c03051003240c0c00010900c034024608400d40e041182c1d95802d10341c0c0844143d000240c92001e084c102550781802c6400d03d140314800300c0340242050209600c0b5407424030989100d100c2c3c00d1300040c81c550003040700401e003424450141424000a4110340096052428407a44002615907040d424030344a03980703454a000144003480160030151145407140030304031340404 = true := by decide +kernel

theorem cover : BRFrame.Cov 930935251 931115107 := by
  have h0 := BRFrame.cov_init 930935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 930935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 930935251 ≤ n) (h2 : n < 931115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
