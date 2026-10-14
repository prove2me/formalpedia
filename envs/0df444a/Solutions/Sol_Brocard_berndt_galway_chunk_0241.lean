-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0241
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:41:26.235008+00:00
-- url     : https://prove2.me/submissions/41529435-4821-4acb-b407-48a378f460d7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 43165472 ≤ n < 43345328 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 43166722 1250 43165472 43165483
    0x6050301020910080606120106020d0908030c210906030a06050f030a051504060b10090e01060504050d12030207020607080c060604020a08070806060903010603050f0106060c03081b0403060609050402090603 90
    0x1443e0052484020203070120300c41d00b0780943c450001014142080700418407890000c100740c21000141e445040e0124030702c0c2e005075644d4010403112005610f44100340c0100303a00c901d05d0468446000080c001980c0c1807001c410240d07544c140c1d001d01a1500c03403500180d81406001c2c1442401d000c0c0c030f4101c60f4101c06040104012180d10b8010005000079031111125180c1d40c000104252006075075540d050145135600440c840c029941d5545000585040c000304074086603040c4e00c0340052010401041005403103c80c0380c01c1c2017a070040b0034660031001d00d4006401a00c90460001d510000000c0d181d400c101380c0e007001d842c1d1450004100c80ba103580d074000388400c034030550041c200881d20240006d103402d0b20501c0307103960100d00a0326043c2400c00b031a01180c01e440441e08100c4041d00000c1005621007402d2003410000c01c03840c0b900001c040c03600d4a02403c1c04201408000c0c2984001104e442d220703160104071001194401e40401805558405050003003030140c6049209403621000710718646400104d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 43167972 1250 43166722 43166737
    0xc031d0d080411060f04090c02010b1009050d080c060403020a05010c02070e0f0a090b13060513020d030f09030c0b04090510050a170a0609060606080a020705070605071e150605030102 80
    0x1a400d0032074442c0d489540c02e20710341d0401d865200c0300410035800c0c2c03039110001420090004001c003040459030308034040d003035411200600d4041d105100d81c1e0890a40d0080149045807000e60300c54040184508089426200b407400301c0b025032003441c0901c01010b80c00603019a5141c010402000810700840080362901417501c254909040c000300811010030f0a086010340008003158001480003403a601c4015011080b81e490040c2c11090003003106000d01030013266403007100100e00d14480c0032140e002982112586101601300300d511100102d06a000b15000005940c0011810194940e03540109055900c140200c210b450300b00300c0892200c1c2d1404000c0c40540d0b40040c0070101c00341c140070004000300e2091210440512070a407030040402c0da548120390680d40a04408900c407400d0800c00350101101610846000b40304000d21404500003181c0c41d001d4817840d01e05291744034500c4c10000c0480410b509020140f10189a1450401550040b804480810309506000c900d580b01e08040c200d019014 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 43169222 1250 43167972 43167977
    0x8011103011a070b010b040510090b030f09070b03040b161b020111030409020d0b0111120702013b0301060603020c0304050d140604030201020309011503050a030807120c031d0d 77
    0x40c4000150702a0300c1c2c050085050701d450800405442d410540a001c1c2c0c06013003420b20004003400b00b0f0800d0318004030750201c80d05080c0d2040d46081c01d04412440014910480f00603a280030070051708003803080100074484550001d0701e0307041034142140b4100c1e081d41c0684540c08441c205200e024081e01c0f0041040a0002011404a5240e001913454054542e6441e0450100300004643c8078410b201401540c181d0607000141f1101c00400504000c640b050b00e0120740e070140180103190f10b81e503030460701619420320f40082d000143d4520504aa0511805048900f40500c03d42c1c11a41c0015581c0d03550a108400074804603a0792101902248507050b00701000350401c01003070119003000000401150703c680342031a4003070001c2c001c035820400b00381c908500503500082800014a02405020b032096000c5010a003130510b580c1d52281e0320320f800314009040c0050078001038403450007410101404125008203003c00b00c00d41034014003e00318540010700c00550300c1001d8071607500018030207500c60075a8 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 43170472 1250 43169222 43169227
    0x1e03070e010311010c0311030f07020f03030909042010030b0907080712051009020403150c090b09010c060e01060602160b03041211030904090602040321080c0706150f03050601080111 80
    0xf00700448021314500d000f0b42c00d1040401a0f48070540040000f41000360030000300540344d250a00c104200d01003400101d51080e44140440c174015550084039682090744040c550810140e01d403607920719904020f004541c014002142e00c842c0d942c0580003903030084c1c011a060041a95050000e481c242001e5400c0000501400345000c840400fa5205a030401c9500d03880585c0b1541e1205c2d007205980c0250421911811810103a940c224001e00800c5160001800c040c000f8030304015031207070f09000b9000b803241040208a03244081c002c265020005c4029084024860192281c0303010755148029241c03254407041607080042c160b003002c015a80116805070f1890343c0c1301e01c0c1803803c42c0c40605c04808000c032070104206003420b5513035510884401d5445040096107603451410320b0070b945640c01b9003000403510349003018060a54040d0015911000c0b0300200c548906250030900c5c010142a048490b184030382440101e020303652a1040000c0b40d22900880e03045070789801c041426943c0c0e240d040840017006 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 43171722 1250 43170472 43170503
    0x30c040e0907081c0e2808012703030f09050303150402030c03070309140105010303080114030309180a02070f0602040510090f0b280c030e04060b0301120807021e03070e0103 76
    0x31084c00042c0e0b101549020b2003080d146200080c141120020041928510950b41201090441e10100700a02d924002003052000c03514696003403020502442d6044403041c1d0001080600030341c001d0f1200818100c0c10070406685260103070703595009540803a00c4004045c00040b45151600032684149544041103045403242d0509502a02107120200e41040751130249030151a0248a80c5009500a0f51401740b00d5140c041c9c510300c203045900314140241c008000305012070321040c400509080e02054280e0450340c585050307030300078000c1c0e000051007103032049070701028028581c0141003652022103042c540a101000142d4660145203e2480d00c031b13410300c10030855441a08054031000d00b030344101003c030445541001011801d1242e400000c54203d4074604240b42e801640c4034940201900c0802c40f403400c1455241c8180014032503024800425841c0d1400c0080b004250307104e041d40984510792440801c205000e803800c451144500074032940c20006460711021403158100c1e504202c0c820542d800c1c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 43172972 1250 43171722 43171753
    0x40501140a0e040c0503030a03020301030201090b040b0307182c060103060305120702040b04021902060a0e0c151306092405040b0a090f12062301170106050303030c040e090708 77
    0xc0050041d220f44130200400aa13503101030000b00361141c071565006030740358154070003d400310700315800440000b981880300340100710070001140d401c581c2c1420000c41c14000035840116500301d541042c2c5038500e103140300342036201c200c1d002200300d020310b1310412031640d0700c2c0401101200c201d8800907106a1250080200005046005248590002d132001c521300c003e01010070240d81c4540b0080710b030320706032041d03802403954107020b080e4100e0820441030245c0418024826503602944132001d00c25455007841c0c6440048480845484a0041d050740254642d20003000e40540031622420b150348503141240c0005007040040140040d66603111103003800d082c6102d03c28242c02071220b04003800741108011501100c040074420050000071034210850107186060010b03100d41c05102c0b41700142060144a2a050072941c20341501d146c2c10400e025a00400c1c0281c0c050541c43d840030340c050100005124120a0300c0b80180207442e10310b01d8804658444905850740d40d845807086a941d0b4001000c004407048 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 43174222 1250 43172972 43172999
    0x60405031603050d140402100c111c150e0d02030909011404093302070c0501080c04031703010302150703020c06030604020906040801090506090609070330030b040501140a 75
    0x74000c0c903226040130070081c401004c4940e0160140c250304c0c4010200b000318a407009203001a541c252602041100c40c640c0c4031044c2800700c9040d24803400101810401484950340c0c0b190007203401140904600f1a4556000002d0140e0f030400c06150040d1812410780d00c1c0004101c0385422000b90905207141c0ca88403020449000e818a01c80d070081c1ca0f181184045110788010322049881484c4034100e4070740305032201e2100508010f40130411401804080049200b244c071900458000782007048107541c60341450000f521840e00018640c0001c400c03080000d84408024505076442554406802ca07880004c59106018503040200142c0c428003407002641000c0d8051500224041c00140c141410003000400e0b1f03800540082046a40da1544138007840401c02c444c5421462540c007900340c600381410225150501404083c000c10a02e0310521100c2c0100d144017030b14035249601042c3c8001c100c0400401500e0380c0c103034440c0704505100c00440c0a00c051101d45c080018010400c000d0680b131b001c489940c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 43175472 1250 43174222 43174267
    0x16080306011209030905040513051f14131203050f06040f1d1609050108060106080c040e0106050a02070e060102190213060308030a0e01050c0901050c01110a021e06040503 75
    0x200302e0407040302e4202500c3c0616501513210352143d0380d0300341c1010b041c00103c2e000104402038024201002002180020964200c149060140913001c4d040c0f00918401030b0500407100c4020ba03c00004020151500101c44003180b03100b80b4082c410f06140305412001d0710b50995800b01e0303400044c00428042c0c940b943c0095881b40c0d42c190007140190714049401089441580d1300446500100148541051902d034120007a081c02c0400300b2203941840c0d00c076a03070307420305001e00d9041c13011240200321880d103840c0a440c001c2c094150812190b41e140c03030004140750840f41d9180003502c20b080b00414040780c1c07050300304d100d81c10690080018880d600d11104d071024811030180d801c00304c0c1004001001c8540e0042c013014600881300706a89081c8001018116800390000348900d9151030148040c1e43d240344d08660808909103000c0381c849070030611150040915455050b144040000c811b00c100d034010801c084010a2a44412917900c06001820780310070088900500300d400400501e95440c2140350700d112503 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 43176722 1250 43175472 43175477
    0xc0c0b07031e060603021305041109010503190614010f2a15050108030306120607020a03080a021207080718080a0311030f031f140d0b0603010b04020d0615051608030601 74
    0x40c0e814920409080f600300b50030000009800007441400c402e030011207400200000e690810945d04004810542802100e602c90b04101c40000800c0303c00c202c50b0140c4e42150301c221410040c5075511803800ca0402601d03c80700d40482c9210140084039070246500518208044101c50344450340c5100b100000702d40840125910100c6040c81c105192007485028040c00d00d040c000d41e500e0030514108800b200c01c0310310060055000d0010081d1607075020a008100c551f040c02c10a156440758605000070b80164003d01111a034604104110a540590364030300950380ea0f140e4601540e88030412803110400c6004020b4164040c0c814003000a115401c40703020b820184084c0c0741001584d251100550f8030940702c0071030b18081d124482e6040300c51012000c0c003e00035a28414801ca0304840440c04c0c10030060750241a540c019800180c07241c80a410030390240100801c115070f0381c0b006c1c0204800600480c00380c1100ba00c4000301740303110300c1d01030802c88610122600d40311700d1a504503a600c00382c0303901c0104450304 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 43177972 1250 43176722 43176761
    0x706030b0d0506090609120a0504090b0105070b040b0711031602090402030316080702090f06100c08160f120305071704030e0d0305070b10120215090909100c0c0b0703 73
    0x8241c00f400828080d203460f0001d030110b410281562031a010070691203003042c0c80c4c100603512840350000b08503011070704028008640b0802c2d090040c1c810b80210b0300301610003205201000100b1544510940c41005641c84031422509041c42d20780d628090800b107070036281c2075030f0b00c4030001d49003802c8080c0c0d0040c802000c481c50034400c1c112050058031406812609048041145000c500d00034817502e900156403501040c0614101000a00b83d00c1000d00b880180900b052203201484800c0c01140c0c008a010082003540070907a1a004821014448003600d540c40b500e0314150f140387c03190041c94025811952260801d1080c03144483c0d0546002e40304800b8084035800d800c14680710000000301d901e019444240c5c691406040c800480c1000400b00c182e4a40e007444203000e400040d000810720150161a41911030442c620200c95074450084040d038090071003020070240d001c0019a481c040c680b0104180005200d80d14140c401c4c0308210002003007041420000360059110364000c0c0e0342010958050b94 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 43179222 1250 43177972 43177999
    0x90e040f050a14100203040c05060306030f12090112060503070501081008060406050601020c01020a0201021207030909020c030c160b0d0c020c0d080310081c080c04090f0902040609020c0706030b 85
    0x1c0ca41540050215508110403180e500e0203070003401091513121281100707500d103241c41ea0b50030b040080396000d203910500c000700c042a4a52020414100040040c03000c851001d16105030300c2140390011410700e0700113104019401c0407640c860041100f00d400160003410445c0c00d0900548140d14020942282000d203010005000901044014040da0140e0300000341e90400c800028200400900043d065511103151400140d90010310324954a40420520fa2a00e20300d02e01140c02902690080001c10700103d883c3c0000700d40030004040c3c0800c00c0c3e0071501e00c1480344c141c03540049140d101e02c600cdd0400c10701c4002c810300b4060300f0080d003054030341c41a90000d0358004001200420302d800b00345d070820004801c1140c40300301041d1070340c06007255074000c1281c86920440c20840348880d58411b002c00007506c0200704860310310b0043e240500516082230206002c0e080544008081504003a8400c6041050028640d2001e20860300c0b44c02d40d06016240c25401c02106801510040d95519040a04000c423003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 43180472 1250 43179222 43179233
    0x50702031207030810080d020a03081806090303100816090b010302040503010f1a010201090809040902030f0a06020d0b06030105030c01030b0a05040e030d060b13031101090e0a050f16090e040f 84
    0x18041e9901c01d495072407070b85c00c5c15031031104240e0450b04005080e81c807a8078900308640d0002600d00d0300c65030521740b00c0880d170380369a90725070200001c145511041c4101011301101c904040080c0d882100da000d810700405685d48011651444000040500d21420000520610543e508214940801070502500e09660340c0042030848a21b10f54404401d0b54407442c904800d000d400f5a00c244000910091000f101300ea10b6164140c8240c11400c3d02c10baa840401008544051000060316082132096070240341043c10030801941c4660920419030380b80c0402d40103146840001e60341612400350080c250102400d00550090180c034075101e0380315004c50b800151656031030140303128801c4a8400396480e414250080d03000d030b84098101800180c810304c0442c507000344400d014000c07260002400e0580700541c20043e06c0740d54040d0000c00514a40004000d0741c0320181d0085401119000711440c0300d85c0c0e031a880043d40d1b03584d80d181c000c0000d01e842c0c41008000581241c95030414090890010005219a50f2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 43181722 1250 43180472 43180477
    0x32701020106030b15040e03090f0d050c030d0f0e0102070b0d0e0c060d0605090604020403081c0b040510030201260c0a09051002211206060f0706060906170109050c010507020312 78
    0x5c941e07410620036068003681c20240240b01c540403404c0019030504043da80060700c1c101e0701d07a41d201d0103401b9035141d45060207003c1100707600c6075002a00395035594070807100081002000c0146400031a403207030441c10140d440003c3c1e0f40e04403105d2440107401c004601e40090003801346e0b900c1d54441841200c110070410754404c40206580c02d640b000000e000352801050101c401c00007810244141d105110030000724070780108450220f110003407051010f4001c0c60078500104160300c501d41d045840c2200b00b00d5002c01400e00c11007600c5c001d88070803800164804507820f000c240c0c40c5040b001c2151f81d01c0800c031620100303809810141514206060440d40340c1c0c02065108017a8082e8a00503070103005c9900c51030054161426070703485a9907400f85400000c488150521101828490217038500064240340d0000701003e403040c2c0c40c0d0140c0207018aa50316814100507048600480b0091a1034080c0d035050042d05205a100095000d005081c1c0020100015035040e00115016030705401140c011201c4105582c00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 43182972 1250 43181722 43181731
    0x9120d020c01090602010618020705070306020301091e0b1302090a030f06020d050f07020307110103180609030905030c09010504050601090e09030a1b240b06040b0c010b0102032701020106030b 84
    0x6081c034201640005040c10660fa00040030b5900d0000148141c409551640c500d11035000005a0340b210b0600d0000c0c60426a50b0015081610210000c81d19000710380200f10b44c0d07401d904e80340d00c158011000e04801c5072a85040140c0c800b649900e41d4060701400c2c0c002e0851114024040341c0c040307941c1e880d00c0f01c400414100c1112150790024000d43d48050601c038540c0c0000c1090a44080f5191000001c0d43d0780c401d841000e007280100c4440d90b080caa100360000415000c0b801107902002c4858a0131601403c0040012004a0f119034004605402c1c005840940400010303c0c1150a9180c0000c0c0802044058001c83c10410070741d6001ca20001c80300d107454091142c01e0015076481940d00001400342038585007090121455203404c3c1c0204181e2400080c0402050503103d40481015642c2c2c001402520121500140046000981005018050302c0c01034203401c000d0000780c040c8001242c480c1304001484c16002d0303400d81040e181e041c0c0110a607a01d0130b418000091803a413680c40d0941c5507003040701d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 43184222 1250 43182972 43182977
    0x8090c06040b0c0706030b06040308030c0d0903030902280509060607050105040f0308011208040b0307020703060c020a05150c03040f1a0a06061209030f110114070c02091501050301050609120d 84
    0x43d0054140d4040241100400302494100880710180001400c0c40c452403101800c0c000c000f20201c0c41105214049440781141e130fa10400001c0091b140150150410013400c0e80304403903108050080c0b40351038903500700c000006464400428208404c00c1381c200e8000c3c043d190004000c0c441000094000d104440c051402030340c1101c1e4a0405140042000348160061294602d03498412000621090241c600f924181480e2646907a0b03113190892801d80d1316400505a6401c0030000c612141e0042464580c0c1ca011340306031901140704201a038075503c2c054034002c5894000700300140204d08103404034505c0c2c5100c0e90219809142c0b800c0070002c1030000750b44480c162503507454208100c0707411414666a1000710342c818010b80c50640c50140c6800310300b0048900b402510504100507100a42c00b0004041581100d00b4190900320402054490180f0b8201d01650452011652041d080318120b01c0414059403580c2c030f503030300703100522129400c80920b803500000c85038552400804240100b41e000841c40e0b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 43185472 1250 43184222 43184227
    0x106060509100c0f11090a060b030a0b031603061d010e0d0f170a06090b090402011e0c02060d050601020f07080601060c02010c080c0c0405072f07030b0108060403020d110d08090c06040b 81
    0x801002240706c406808141c01e2071a12000300581030004c42600e501c2041c503080020031140400110f420085c10f035009008078081e8840100411425500182c0c1a00fa00c0c404560f00070101c0d00c0581c00c9600200b880b03601035105212000246205400001031000e0a1502d21903a100d81041e1000e030850681d00101c0301030f140e00381400402580d10419520340720071240b046441c101500080c207000c031100300d0040034007420304640c10301d280224058a03507294003412140d07543e4130f0a01404024007013900c88030300501481c100755000c00380001c0c1e42800c2e40c00c0d0201401f03541c2d21700101a5400600d5000c1281840351032081e000c003254102c2c0183c00c5020024002c0c01c1c3d00c050050800048460050441017823008645501c407440700f10b0186c0d8461441c014142c050340311400c0442518000903584000e003450101c4001050040303010540364041c0f4030a4080b258803020000b01514280c1611003c10311941c0f0001c0c415055902c60070b00c00d50018402402e4a41c4c4450840200b030355580b03da08a03004d9035000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 43186722 1250 43185472 43185503
    0x50405030105150105031f1203020106050307080705011d010e06040303020f010c05031b0d0b031c0809060708060d0303150b0703090f060806060307050c1903030e0106060509100c0f 79
    0xc1c0142039100100194201140c4541c03400a44039020151601001070384a4440003072202444851f1405450103140d02c5501c15214a0300a0181c225030040703d01902400000155000c0b00003542004d41d04142c45407801c0c0034500303100c0168468041c1405d4104680c60201207825101c1200031310296000b41e02405c407a1801c3c4400b1f03400d44607803105810800404008101c070000750b600e501d1584401c00d0040303e955031540c00c0580702400c0701c038030031aa03d40200c40c2c1003446025400c0451170302850300d4442001503555480001e03210802100c40c80041040380d0006515031810311814454a440390070b00181080c9084110042554250083c50302400000343d82c07001c0c1030b08410b08000401c0018a02501e031070501c44010040031001d00340318050301000c8045050f0500810560744c3c4021010215001e4001c14090006d02d03182d000d1040e000300e403401c1d04241c51034406005601c159545512000e250089000c140000f8020300d80000040200158601c000200300508002a0758090100001c21210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 43187972 1250 43186722 43186729
    0x8090c0d1202010b0d0323040902030f010806010b071e02011106090606012c040b0d05010504030c1e0b0c0a0311040f030212030a08010e04081c05090c01020706080103080706060f0303050405 83
    0x60513002c9120f41c024019581c00030380d00c0b2103014281e204c0000524400002d0012802d100d00554001c000b256001104121080b901314141038121960340003268901d998641c4100101d1045820240800301c1004040e480c0c104031803000c1002178810302d003c01d221460340c2c0a09050070030960360003903260070220601055607440302030300c1144040b0034000040c034110081d4482c80d440701e540c11b013401207881c0c04a0410a54980f07040c940503170b40000007401640b41c203103401801c0201c1101c08071408030140e032220401c910350240d1945130640c015410320240e103802d038041400341c00100200c420581c4401d03c2d074030640e903000040d00040ca5003c080882044c254810001d0b1400500540b51840c0d00500c811079605034003e01250440d6030280200b02c3c0c2c0c0e01c540c00c1108040c440c0c0e40d580d80c3c00f500e841c50b246a80c001070fa4413031841410f000c4156810800701000490b25240c0c103100320b2001881800c01800801d20b0311006190145c4200000642541c0d1400b46502c030f004a03900550110b6000303c0c00b00910304 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 43189222 1250 43187972 43187981
    0x5040f060b030708100e190803010e0a1b0c080f070506040c090203040b070e04061a03040b0a0b0102030703032714070f0e01031e0b130c0504110a08090c0d120201 71
    0x40704038080c240d8582405a030540e10841910016003a50701c075240400344082c2400a441c280c2010343c00c0603106809800c0440080d84207205050b0820b41001c00103001d03030304a20031314516180c048159140c00050440c100c41c060507140040d038103c0c00801c040007044d072103d40148107482c414006800140740c0b606244002c031502d0b80c000200c0c0b0b80100100000100d0803032100790300404600b03050b0700300c2c00d05501060041160340c011007014061800d440c2034a10108001d1480356102d8451844103903911600101515104a40386025038030500c03040f40000e01030341094450100b54085001000785402e081e0031042c1d520340d070075070384500750002083e20b010f41401104003034845902d41b022514600b81c00f000811070148070107070195003245481c110200d640b00c40ba141d2507802c9883c818203400c00d4180680a0181c0e03110031aa2a004800002610308141c000c844140383d032240c80d10300346030203031500745d0b0b0207840104000418092282c0c60a02c96494618070403255004403800d100c1c104400c4000390844 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 43190472 1250 43189222 43189241
    0xc030307020603010314070f0e09010c0f020d05210a020702120f0c010c030c0b0a06050f0d05030f070c180b0a06021615091701020702030c09190504080702030105040f06 74
    0xa810400c002005a01c84030101c0f03044940c4101c000c803a00004405050418000d0b400c030710001008004001003c0708642d4842d0f0090303925100821000c18085000c0c0c5500342d000560b41c004d81c0081c8802c42c40d50303016401400003102100c0700344100c2403108000348080c98007120000c10865002c03503e00d042d410000144c41c4218000001442844207d45005e50356034400d05000d030404c8100f84c003040805200742900760045074481e9502010341840d1030140b02610440c02014003400c0c66802511003443c00800750907031281c001000d540340c419043ca00510070b5010040540b9558401d02c0c0c0000c96254905542c401c840b4480800160001d11a04200442086500800c00c5500c2000714940015200800400b103510720007090020700b030304100680f408006948400d02d500c60480c5407400e03450041d0010440503108406841d0040440f41c20040b0040301980d0746814000030581ca022801080e90095030414080e01605040c581c07568002402e40703504030f40c101d03070401c0d07241c41100401059000f0122903 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 43191722 1250 43190472 43190479
    0x7051b010e010b0a0b04180b0303070507080c04290d0b04060510090b030c090601021014010503070b121501020a0c18050907050f06220b07030912080706150f090e0c 72
    0x156845c1c075500c002680254003a0a02d440111003000c90480b43c6544000200100a800d607920360b81281883e43d11407074148500d10480c002d107107849005141c144078801990742565043d20304100031100110b00c0c81d949030811a0000700700e510f1903001c141810704081c1304e5446403001240d41c0c039000881550350701c0b041d072040c805241071411032505070b503000c646100b0300c0b103090b1402180d42d9a4580100d25000f0810200c00200d450700210850134250a06805d041c1c0d40d0580880b04c0941d600c010f091918400c403403c0a041001000119070b070600d803009180d051810500c12901d0006e003e85502207244c0003070740038a883d80144400c1d25030f0b0203c0c9006a0782e000350a54017a208035841c0001044110001800701e41c4920800148064982c615103255000d03600d213403aa24914640750280c00100f94070121054001c6110018000b40c000502c0301d44911300e6a01c001c4060600d8000e941d150090080010308020f8540d03103c502013000005500070342e00030030010310046145d40818500754104441454610700 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 43192972 1250 43191722 43191739
    0xa06060306050f10030912020d02010b030a0c050603090a05070b0903011826130308030613050103080714010f0c090f05010306030804051c0501020a02011407081e07051b010e010b 78
    0x555680c100b100f10303900d41c1521000341e0303400d81c0c080c110b00414044000820030510800f41d215125130006402c0103c0c0c100d0780080109050010825a0b42da03541440106031945042d806d01090034110003a54000030b0350303030846101d007090b991030b5401c104031a044521404008512610a80303404d0085d0f940b80180140200658044d0f603e82d03122110451084c0450546401c2c07000c40401161403c60b001c200c0a0103001c008140c591034003010340d5206480140c03013001c041c10015162074051050300d0490b80e005100e00d1400010747d98180400c2c00f90301983c8030556175103e240451a190303014805000c0c0e040e5584022040c00d1080981c03140c400c03500308904040c41c1c02801e00c000b580780e070110b40544a04447d80310321200e44081e95032249510b240010001c1d4000328800a82e0f98054002465041028802c3d500e030383d031a40c10445241d41c0884031040d810349000d00200030080c41c43e400310740140d19450321a01c0c000a8a10040003080420103034041c5a5594696400c014002e105018101c5000c595140c03 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 43194222 1250 43192972 43192979
    0xf030e010f080c03060604090f0501031403030708061c02041509050109020f090f1c06050f01090c050703031d0a03021506010806180c04030b0c210603030412020f090108060a06060306 80
    0xb802d4160040c43c00324a1200000860720325583c0e44c0a4400515018405000359125031043e140502030038402102d0107580701d01000004140841a24407910090b503501d841c0e81c3d195000c00c1170400071041410480058081c0c5803001d61502d0046e5488420490788070030781c031880c0544900444505130b00c41c0d80460f1060040208282610342150110700080702e404800207400000900c46d01028800031a03184100b241030410032a842d000039108800620796940d0740eaa80b260410103a410300e8004900064080251400007400b82d0b0101010b04407244d50307103d0741902d580e9000d00e011145c18007039026034401010300c3c548680b292083c650015082c0782111550502e000031814100001e80141070f0ac0a140b0300242815452078185c400564011082202901380312401000c40da01c50f890044072086813107880d06000e4042283c5074080d00c000b5001310305d01440c121000000036200041240d00c107130150095043c3ea03464600c0d03540038198150207000c0a0604080f40c40484506920600078942064000c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 43195472 1250 43194222 43194227
    0x2010506031e0a020d0203010624030b040b01080703020310150c0b13081605010b040609060602010c0206010311061818070816020a030f1b14010b0405010e04020f0312070f030e010f 79
    0xb62401507054843c03a0701750a4610009000d07046540000ba2604c0d06a085440d4a280020740303e01c81c54000d031800c2100c070814409000540358085920b07800b0808040100c0c4d905482a401036900400540709000350030388030710010748a21144084c45001032810321924050000e4900f045411407000c0e007541c2c48d2949150703920ba03903078018450340a0180c007a410003401072010a4001c1134240d240144208041900c60241e04002c0501c0e000b0000158a403801542c14035000081c46416a80c0020050b0005070700241003100b0707070b03204032080203290900045003651038650050450340b801021f800703c4620718207410014880320000342010070b004100c200351a522600070603503040c226014540f41c80c24040141e000d035042c80c9040000d207603000000c1f007402c0074810a104000301c4404000020301141008404002c2a02c5081c0190080440f000001c5001407510b18030658107910042c064448a1540403694001500181420f407945004501e82c0c40c10540d100c00c405003180424205980d2624001000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 43196722 1250 43195472 43195483
    0x9071d010f1214010c050307090801050f0c2d0306190b0a0503040606080a03020a120e060904180804030c031a1909020307090c022b080f04060209060a02010506031e 72
    0x1c100b8074054800d006410310a43e41180fa44800c503500c02884a002c58000c02046035004032901400114483c0d000320300c1c07140c180209400358505030404100c1c0c0c0c8400c041071030558002c060105a040303040e02010048148020718116601c00d10902c0b03a1645000420300001020b6000394510358ac0c1c08801c103001d85a10841035510310056854040c2e02c9030745034170b0401e0080880d90800e0005100b034071292030400da03002455080052080711030031041589018150b410383c84010342c0d40e0f4010424440840203084c1603000d44100340c1c182d01003240c41e000c191900c1d07105900c42e41040e070708e90440420a109004c01c11304240c0d40d40e28a03610344005441d18100031410301c40c880520103c0d094079000341c54195503041140401800380c10204004072034000c44065540d546544403807144180e0030712440c81c598580200210114129119110103540b420503007040340100030022948c0b16424000890b1980311100134068440464000040501301030081510303200d41858010111072880547c0b10314510013152 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 43197972 1250 43196722 43196729
    0x31c020f040e040f020d080306010e1002070509040809090c181017060301060e07030204141503071209060c030207050c0406080c0d02060c01050403030516110601050108090a0b09071d010f 82
    0x4900d6050303e551400a80443e01c06038040c2d03201c8818101413060102d000015802440242c035942c0c8441102c90500c2030302c000b070881d4040560000f01e801c00007800c0c0801d60b80c1d4030520902c8205e00c2c1107280000a034900009643c0940030360710101d40112b003141c280051200003002190f480b500a02c8035480104940c040d120341080e4114000c011a801e034a09400c41c0e0041d00d50300034004c4451420071002030094100f8031a980612030b000e15a40d00034108141c510000c01c8803d61550301d566a951802da031580e82600d642c00040d0365940655000c40c0c1d40e4464031496401681d0f02598030115030030082c0c5410124000644990b1400c1c4040005110002e1403541e40c1000307031581003103170100d800004c40c540140400c000d070701d50801003040101641a84032501c62018017881402d00f10f02054100e4007010b41d0040a40541d02c40e50042c8050744c0a140d1403a4030080200032644106020380e2042d020b0b030001c0e2442c1c145940800c109004070345503515180c1c0710780300e40101703000a98544103512031802003520 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 43199222 1250 43197972 43197989
    0x1b120e0a030e040f05040308091204080c120f0706030c0905060901020a120e06030f070f0c030206040b04020f0d03080f09120403020d03090f0f150c020904021020031c020f04 76
    0x1a14441034440d44c104482c01070b40c40404200c40d10b800d04010380048421560300d0003d00850b03401c4074182c006941030b907081e1b03401c3c0d0b001402d20915000034010b141a0407010003016108801400351482d8003041000e000d052583c0e0f0201d218072176a40e0160000601d600301c10310410090090a40b01d9038000341144415800409050910200341d02c01e07603085030802c0e451500008000100855404a003c0c0c45008010710f5607440303440b00c040c04c021502ca40001c04001c0041e04600003203004284004001904240001c0c046080f058407880082c848031204a0300301c011601c00402c005821050096030399004026a000e00962810310408444603c03490000034400c01e00030071210145807103050014007030144c905019240584443c100102e10301c0724450040300300e034040110310519104d210141106603010740800350301e49542d420000d0408000503080c0c20040e548e45c80d09150304000403203d03511205200a10b968820f0b41c0cd00d1a91412106080e0322250b00400c211040341d42c04d0800c40d411141c40d40d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 43200472 1250 43199222 43199237
    0xc0a03050a0210050d0903020f07090c08011401021002070308040b010602060601020a06110d020a020609100207020603060603040314040f06080906150913020603010e01141905010c151b120e0a03 85
    0x2040c1910744d4002c42c00011001031800c40e0a5041540002c1c0c5c200c8600c89500884803020390f55621a41a54040e60000380001c032540c004000c1d03003002d40035915104205005481c15203501c148800103d8001c24000c0d400110500144428002c075480c2c428094443d078030160103140362041c0003035620320b40103500500300e5030707500b512445050804e4203807015203149990a5680349003001d4021346e2940c041c2c4000c0311502540000309901d5503103200300c8100d04d902030051404d40e07485104202d07094000410603070500240009001d5041515030082020b400106142040307d810f04100500c208802040302c0620750114080c4108103011591f000340a080454103003e0780d9071190b0b4034601800001d24025040100400040360321818007101d5410307201c45d80e09460350000c0f02800c00035141417032481c0c41005e5042180c24006940b1460507100f015018403160070100841c642c81c00122405108009040086007039900c1d912a80a0040107000c50b0510003404005400b060040e142c0504050040074003100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 43201722 1250 43200472 43200499
    0xc23221410080628030f0302060f15010804030c0c0b0a021005040506041103031603020d030b03031303020f06090d0803010509090706080c0d060b03070206012907020d0f08030a020c0c0a03050a02 85
    0xc000d0600314030300c280c4c60b000041a03a41e00e00115100a00b042c110003500900b00080c2c02c800c40b1203002485403d03030f1485c400c0325100500042d501c2d0070014106404100b9107804441c081044d003403c14006015200b203540c0d65444000000381001074440d61309840f10b040c03005020124030300198081c4c0180e00a0403541c41c1c0202c03200006e02c0c5100701900c007000c05290300c44000c14982c000ca40159000d50503241804030441640400d0740724411450701c40c551024140090025043c00070880d40c6200025052a2414901c140080c100044042c011290702000100610003401d0090110b5040700c0a10010075540d403d03c1c0018101e0036000300007454412020425510841c80c94000344018802c03a000281d507030070a500025254903003400764891410030007440400740f40003551080300e00041103110900344480c42d801c00a000c20b000c901a15520003642080010540f440300840c065a0b40340c3d401a540e0221103030007414071100d049603e1040301000d1041001c2070307002c290000c0322a812105009080107 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 43202972 1250 43201722 43201759
    0xd080103140106030212100501050a030203060a0e0c0303070f05010606140703050309100903020109140d050a0c06060506040e070e0418020f130c0509030f010c232214100806 76
    0x3e4941c406503024400700003110340034501142c40000070160510500007030380c803902800710f608a14807000f0741650207040021003444c1180c0c07204081940880542e0700640180001914682080b04161408000c0310404010000300b403180078010300003410035440c8482e41d0000018180203c4501506102e00000041d0640d1014842401180250801000901c0c440c5c14000c1c000c11081b40e00b1112840c04009461103030500203412015110603a8a0500e07085d5503200c1101c0707107040000129005900c40c00007107419a1250050700c09090340d91510300141c0b90006000b071a251071540c2d0710f40101d1800e00c009807004000d0001280040d0160340c20212108004040b480c1d030012001c00c05082403801d00750450182d8414010402040110100d540c07844505401508035504010780c0008140a0307022103001d990a558604040c0d40f0b448161801c0c0703041000c200b80001c00b0f0036003d5a90a454410600044a600d0040d00009809985c9540e8600d00c800001e4440e40c3c025120b20321404414071030800001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 43204222 1250 43202972 43202981
    0x4051018020702040f0e010b0f10030b0307090905010c0210060501020705210601030303050912120f071107060302040501030e0d0e041505030a0503210403020a030804030306270e0d0801031401 84
    0x164043e1042003400b17025403115008044504030f2001d25403c042c0d60700268078044041c81010b070b100403d54580d401080d403054000b032071002d4110740c041c0190100019142d1291141c0b861850091002151900c10030b00f000f0308140072401c50030202da1501c5018000e41c0da0001b64a01030714020788004890b00702018419598034803644100b8124070920001000b01603054210074050111101210708444205203010510302070702c95100100408140003480920750400002e17040329031400e00e8215000c441d401036051180c280c0200d80444d800090400c0256818450050643e03004006400040d001e100018146043c0046c22481561500780da441c0c0741444202c000c00a0034010100d50100f1528a00130751250001581e88a0001d0b030505c030388003104080383d081480340c1e90550240010003d90b960a0703c48040290041e400c25030703a282c0218800b0014485680240bc1c0c05215070100304410405c80e090755006200404542c00840200791819000109141900c0c3e00208006054104107030789030061 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 43205472 1250 43204222 43204237
    0xb120a060801020705160f0302030a020f15030117060109050708060103110f04030c050f09010b0403030f1b05031b160b0c0a02040501120b0603010c0e060309010929060405101802 78
    0x15480010441c0c100000003a48541da00401b210300d4502c19039034803600720710b4182d510001c2c2d00764000390160001071030044020900c1c1e000051102e02d000c826607400b54800d4009802400c503102c05803207041401c01003004041e00400c1004000d015503d454240280b00315806802d541c18587c40744c100d01954440b400a440e000103d85d801c558031155070781000b1f42002914800c1c940144410540d64840e8180810054141c0f65454070151a052850350111280100c080c0c1c0c050800001c1403044080c0d81010020309480c3e07001d0402140c071442c520b40d12040c0c003044070b82c1400031548190801c0d45d101c0c00420700c5208840041018545a0f0407042d5094140514910000c0d401840c00740089000703100d0007003c000813406840310f25902e0380c80c003081c5800c8556802c0400c001c140c62a01088403450701400459022022500210710311a203555900f10904c0c100104186498003010b074074120300000c083c06540480c04490510850809406810308007915020b4400c080b04100070101c1107109640440d81c0c43d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 43206722 1250 43205472 43205489
    0x10c0f11041e0e01020403032703050102040e011805040209070f140f1c020304020a2303100209030114060d06110f0c0106050a06020309010e0405090106030204050a0207030801060203040b120a06 85
    0x107418603010142ca14450400501d00040d161210903203108805100351025a40c2c141c80d0b120081c8252075034001c004848802c1c0b041d942c00c0b100c0c0080009071085c005480217060050711b6074400e504100d0b400400103240b1000282ca41d18241c100b20240c3c0d5841d055a40051003410700d85524021401c044030780d40d0241c030303940040200c0016248080f18000005000c030b00d0024000401c1c1024864081c800e900c13064078003951102c00341700140000c3c0d03000e041e0901c0b410001c0c8900c3c0d81484501002c2801c060f01c2d110342e017030210f501055515443c1801e00a01c501c804464441c43c007145007440014801e90080d40f0050041075446200c0780358030000c401111000040c2030310f040d0721900c4c50300d00036000e411180586400340c00d41c0600000e5440c00007040c2e4120810584855038015808801d1100504004009210f2503480e9003000000da01c0d584a4140213100c50140035035110720710f081c09000c2144c10f91014045500c10003040180300c01006c1a143c0031426200510b20603120083c41c200a490f031900324a91 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 43207972 1250 43206722 43206731
    0x30b0f0907031d0604020108060102070f06030c05040302030a03080a110705030708070203030405120c012604260d02030a0b06041208070204140108031801020c0114030c0d06150e03010b010c0f1104 86
    0x75020390000c1d004d407240c0d1003603803a5149507407064012a107921451098403108100d03903e00740a41c50180c1c00505208c45140b82c00b6003010f660740c002034078107041c0c19415804510804103100e00c08441e80238100c0ea0703020024a8901d08850755459980d284030f0100302409011020810341c0031580c041c0100c0c1e00a201c018650741c2440f40c0501c000381c60b8000c840b08640420b0b01c04c400600003900c01659050050f1f55040c024100d270392940c031299402ca540c00d8400c4084114241d0300c907084800c543c09008001255500162280350050000c801c96803c01070b01841087c0c140300400441071940c04c5903000d41c3d80402507903100c58051010a02800b8440c80313206064600c0800072811140c004050040b800026241030f81441041e001680c0b0394a514240c2c6001603808071a032405540028021a00100107030041440d002440310100c040380c510740c208414136200e00011112160b413020b02c1c60710100040340208001221040003070104092210010075102c21032500c40c0c1800800c04401110748000740c410301 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 43209222 1250 43207972 43208021
    0x40f02030601060f02010e0109020117070215090109060b0f0f1302070b1501030b090c030601030228271809050a0b040b09150f011a07060903090e0106030b0f090703 72
    0x2440d051444c0311920066107061180b00b22054140510140281c040e1261703902c105660070307800716058000340144203600c01c25800160a01d882512240700b0b0289400015400030b035807500c1025070f2408124244600885508141540c2e0341c0105400894000c645103e8400c20b4514004040d001e000c1c000342194142004000d036410520a540711825001d80e0104078103e6041c0402c004841d056400000100007070000403141d50180d03008010800e01d84000146c264848440340c0304c031304210800000054503600c1d09403005e09100700ca40100c010310301e08001d0701c0d81c1000342d1040340282001d01d201040f5105e006c0c0c0c6090040a000c59000e5070342011340c0e80b403031346828148071608000955030f030080b40c421088800c90000101ca030301d600440c5514a840c006c3d034603005c907081c42c03030312000042c146508040190a0004500348100f0002c944292504040740d0b180100c504006081603100c0d00c241800c001000d00381d0744d101200b030020110111030450142e20f035618114018410b035401c82d044120340b43e0504 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 43210472 1250 43209222 43209227
    0x70f08031003022e0f020c09010b040303090b031902070311011d07080304030218221202060109091a0406060f08030904050a020a170c1903051503010b030d030203040f0203060106 78
    0x590070b0303900070f50352548010f190140600c400002c41d020b1640e00740d40801c10000740e0b8456201d012030f12016104440344800400009003190b0000e91084590f0b0300002000c00c10507800c0355406000389840000c45043d0314102c03140755a151500c101010185500084c04000c05001d1202c410003410b880000f00212580b12803500135408c0000020324942c81116400a115040081150103499004d0038110401000480310f00110b80090b0a40c1100e0b00001c209000550005090100f0729001e1504550302a600d0302c0080e00380324040e0047c40c000da0415000c42e000c1001b030348030325001901880c9031480301d5680c2d0174000d008011a40025450f01e201a2002840c04400000b41080110890301000640c94809656080740b184030407080100d2018460719801507840e010340341e840002c2c014103518103040d05184c0c5140416000600002c2541c0c5c20922295088110b4820950035040d402080908030130303c00070f5a162000c0c1c01220070181c0020000c0c0420040303074100c016166010741154259610362102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 43211722 1250 43210472 43210501
    0x109060c0819030e0708070b0a05030901020409020c030a0f0810051002100f0f14040f1205040801090c1706060901150c0c08030a0212090a03020402030406020c0a0605060a08030c060c070f0803 84
    0x2080c006101d01c58000c242e000c17010580c07030100d60000300c0d234030b00d000c014200607100b0303410090105600c0c2d5401e120002c1d1400c5c1c1400140b0003070240e40b0155030b450001d48000340c00b03074a44030b10b01e404002805081184040a46c0905020769004a8200c580651b0710501280b030024569010071419040c80d84400601503580c21201c00240b445106102603000c505001041c41c000302c03401b604c1e850089040f43d010641115a1700d0140c002450300c40e02d02511442080d00f0348849002c1221049a81030040024400e03c001c24100d0310b10400107492207080180000c4d40e07401043c003a6401c4a41c90303410345161a4002c00d107242d00d03107a01c1184054569078480c0702d15213940146409101500845950225415900c0201c550991000740002d00d018299020f0000940000300211441d5030300300442001090108000740c0d840e481303070307001207142e02c1c0500078005030400962090001341c3c030a01110f101e0311004280164480148904a901e843c210b080080d545080b081010780480000420b01c030f50405503035071 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 43212972 1250 43211722 43211741
    0xe15010f06080606040501050a0c050304030c090b04090f02090a060e0f04050115060c0809040b06030a05010602011107200f0a03050303061504030809190504060602010b040507050304020109060c081903 88
    0x2000103006640e0720064036440c00445103075a015804110600541d8001c0d8060325280102d0b10b48000922881d60b01c503451584207400945250104900402000110703004409003918281c4041c0031481c1c8981d9400010000e00f04000c1c03054003100c0000e0311014043c0d0001c002032803139401454440c01c00c5080800c50080170799060b115542003d0000850420400c080000c60f1204c0d0340e4403603155400d44422015803c44100076611070b40700c81400540e40c2c2c4041c0694004c4003c07100c005615403501002a086600e040410701c11010300380100c0000c940070704500d200c02d800d0149001c403201b50b10030000f08954503012210f9841030200f000070050010010246110780b00940d500c000b60201c89200710b00e1409184030052010b241003006036168249014641812003e580ea040d4400b600c0e00c0004041d68003940040e0010b030765400310701c502451310f805042e400c000103050017031450600d600000d001c11018080ca0b001d1040800c40902040450001c076541c020031a00100740326204014003d002c0d012115 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 43214222 1250 43212972 43212989
    0xf10050d0b03010c0203030a050a020d020408100f05010b160804050d0b150114040b0901021c180515030402090711061501080718090e0106030203010c0201140f100603050a0e1501 78
    0x200700d1541c0e040511800e011441160011070071940e071150300601624004010114594081c42082d005001900281020340112000760020b0341510210714200c40301c1400000f4514100401007094400c04411940100e090ba030189500d130712203007485161880b8640c0150b800103c034007000e4044c001d40301340c4540908006216195210314210044403401c100c01c480040030750f0100010000420340100400c059601070041c2d070003109007a50002429004410a8804514035500d1101d0f01d102e1581c0f207202400d4112071205000c00b0507030312002c150100a0000b8000c00c0083c000c540440d014a15182d80003041c81c045a4aa107850095091380c030344100c01c1240400e12410108503854052a28001411043c40000540601e0061110302400d00c1c42e852000c7c6d95038034800400540ca0030301581150303c9081c0c0001c1850242c1101e040d41e1000001d0001c1c01d909602d10500c9440c03503084500c82c0844e6400d29000c02c90f0b03110511580300800120414070f0151103044004040348031403042a038100d50040c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 43215472 1250 43214222 43214231
    0xf011704061e1103060904051912020106050103230601050d09050c130b032d070801060e010b120c070602090402030403031b020a0203070e040c030804090e07121509020f10050d 77
    0x8a040005641c00c3e840200321031141480000c4583c00d00708101035205006108a56070707140142c0c504090560303800c03810340c0c42c154401640c0078241d0b02401107200800d001c1c0707000c21000e01071284418107180c80c01140c0c0301c982d8004022038140d80c499400d5401a4105a40800c00b806452078107513a200b6540d092140940414205002c04000741e1081c0641c00c0c10140142c26030307400943c2c104240000090541c02d071410b400300080941d640c10401c18000e04100b00c000500389040038951050560140d01407203e07564100900d074035008010308140d80200d910101d8503211621490098080d024040040341c0240c400702c100020315600da04215034180802c202104502ca14940490f10b132000742c0300107900340d4804113040040a00c50803a1540c8203014220682e21152a9550029287d1099221103056510b0300000c500300c40d03060103581c00500e4201030446000c451a51000c418000712988815080d80e100b42c0342c020740d110816000300941000f01225500c00c0c0002000d4074139000078081070000e9140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 43216722 1250 43215472 43215521
    0xf05010504050c0d0e0345030d0813020418020f0a0b1209030904090f121d1011060702100509120313030507020406030c061106070503060f01170406 65
    0x10300c90140650000030a4034a48002c0f000100b000d072004070325084486c4030810072641442d2444031041d61a40c50f0805443da80000c02c400040401c65403800c800b074107a0961a680703129500021100c0d000141c900b0405419a0703000780c4101072610301070780a0b40041c10480c68503280220018180034991007110f10416040c034080a00011610070b0240d1f1204c90001c02101000381c000c0044980d11602d50f201f203a18008001020034142c0c2c007003280880e2500740500e40c400070030029031000c0500390218a886410304404110111014107440c0280e4050303c2d96510380d01f0f103130348602c0c400d95103c182d18003281e125081500f1300a50b5801c0000309000118030304004907200f00404102d260b0347e040b40e0103041d070031500c44140f0729a0400042d041101808403c008480040c2c5030ba0085000840c09010f40b032241c58504000500340d07070041c8a01348001d400c548200304081e0340000030342c0d81001040e14120301302c550100058680c410380d100c0c070300030f1f403501e00f81000f00304089608010302000c90144890100880c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 43217972 1250 43216722 43216729
    0x80a0c150908090d11060c01150b071a07180308030907080307080702040522050106050906010c0321060b0f0d0608030403031205040f0b0f0708061203030610050c0304090f050105 78
    0x3110703030000b0b100403003c2291191500d44515840003513401280e14645541e880000070344194854266102265151220fa444205540003c00e0041c94071a0b45a8a0408c196903041c040300780703013070582e1401382e1950045154031b84a12080e032100843c41c556600c20715140d041004040e00b00f116200307400e200d184400b040b841d4003c03041c2c519055101d07040c83c3c03c10302241c0c02c120103003030010440f480b119200c0080d118412600c50198024a01034000042d180d800e101c18043c0d21000284928103100d0601219030009900100102c8804044181c2400964404038100c01030100b82c0e00040f1206d80128043c0a0804010014540e0800309102003041c00e90318a42d0b00c2e280e000d288806004502000c805d0b0b021541e680e04410381c8184a2070284101041c184e4465075240010b45040c044e9a03083c800304070788160020601c0307800000440349010b0a91940034901e41d02c0c0f100600103800348425a034140e020782d0250707082e90341101d5000e06030b0743c89035200c0c0302d45c0e80141440da40b0740e100d903400c1c20000183c0c0d06 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 43219222 1250 43217972 43217981
    0xd0506060405010609231c030801090b0616060b1c03080f09010e070915150804030801170a08070203031603020a0b100b0304081309020301090f14061813080a0c15 71
    0xb568051b01051030000e200d1a010742c4401801480e400c1000090b500c5040b010100c56100564440d40315501c00c0d50411782501c040310707041c0c01c80c4ca000384410009030304024905851030b11815400b4001081071028040464940952655500d4500015941c00001c054002c9052131054800281251503942c40f9001e003400e980200462070a250012603007403040a9060308103007501c0c41440641c0d0580c40d03440c101c10018a0f410240d003c0080d10040c140300030554009421401044841d5621100c0b10386d00d108141c45a10318100140b1040e00002c0030302c11510140255114056607228020400c0c0b41402e01a4442c6403c240c100d03101c5c1b00e40300018400141e921661000d90720404202800c698640d90785002613404005031200026804600180c01c909900046000e440100c03c04a80d9144d0030a0070403c0e10f0811900420403415201041040c1e154055a140c9554510405031a251140c990101c203c1d51901c0f40609806400552010a0341c0c00013451000c7c14401d81004800801e0051000d00b100d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 43220472 1250 43219222 43219229
    0x27030403020102150c0909100b0304060608010510060206150d1401060305120a09050603070302190e010f031803050f040b0301090504030e010c020108060111011d0703290a1a0d0506060405010609 85
    0x1644240010481d80c280206481d034040c80b480404000c0da81c45035031000d08ac0c0c1040701c040b90741d161522002d105d403070401c3c003500750401c00ca000d00803125802e106001e51980f0000b40500b940007070745468644190740e81c1e010700c00c410381c1140306c0c031340800d14048145000e810140070030f4840d88680c21444994000c28021940185400c0ea1884230483c107107020004250300181c0300344100754003805240540c10507120011600a090340710080818104400035100d41c01110306a82458608010f009440c089900d039141070b039915203040f41e902c0940c1c0c40d802001d4003490300899220903000c00085011581c03588198081c5020341c0f50340c3c00100e180c81c0110380a944850000740000d50740305c00701e59076502400380f0742031200302d11300081800180d1203050401c400f0f80e00b42004a9900c030782001c2041c04910756203460707980c88003032020360f101340324034240000d0040c0030302040e01c516665181220741e460000c00150007020001c003103031640c00f034a0600719501c0f81e081d40c2c894410340ca044000214035004184c0712048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 43221722 1250 43220472 43220491
    0xc02070b0f0a0503070c0506090606030c060f03010b090604080a0506040201170402030309010c0c05040e03120a050f041202010b220501060801050d020d0507030819020709090206040504052703040302010215 90
    0x280484140b0032110703a000508a041482044403034100010b00500103a842034003600700800507881d280c4101450300c54890607550086000304546526401408222410b4441803182c5d035554070311040100c0c3c6030b8070482c0c0c0522118002d0280e00410001c0100d01140142d0007603803a2105034800c2400144094015103000358140c0c820030103542203502a18605002c24080c0c0046100696694081401d44403081811110b941000038010b02038000644295084a080c900420803450541c00d00003070008003034805030549804080d00c19025100750010a02c824001e0142054000001075100300300030540c0001c1c420701c0c180000800c14502c1108614102c40b4002c3c024180307200d4640900141460510066495000700358001c804910326070300500203100620160010724103181002400c020b11134000540542c100200400581d44810a480070346108540010300c94036142d828962140f43c40c02e9505001303071840200c4c0038458001c4050001c0303034000e80a03107003004d1b694a10141560821905c40ca003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 43222972 1250 43221722 43221727
    0xf05061c09031101060f090e06040c0506160c14040c0806031209031203090312011202060a12150605040501020f0a0b010e1b030924040b0106050d060302040f0c02070b0f 74
    0x103940141d008100700c0c500a04000c0d89900100005500350360141e009440c004a200b9010044401140301d45e00041b020080504403e0515580701080b208044c454544200342c08501c00d0f0804204040042c01c0039444501144440c0d50f401c15580070020721501300c0c2c030480c40c0c03000320b0380c08030700817004280704403001000361500d07004034010710744d250304115201500f5108a5440781d07044030070031001f9400b5105080096454810403482c1e5112040142c10880c0c590320104420070042e2904400d031201204681824001d034481c0aa040d4000c1001021004004803d02030005056404c00000e00654800781d00f50340114113405070f415650561081c00411255400004104d4522100d40e09030300132103205c4040000c0314801c00303a100705400564030310046400c0b11504102c54070340350460361070028010711550f1141c90541c82e2422240814130504080c850001500d81c0403808075446500070703640c021b004004408480e00014001c02610000d82e000d03108008011800340d90860507035142c0e40782d0389035861 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 43224222 1250 43222972 43223017
    0x30105070f0807050c030c06040605180d1412070c02130606120905070506030a06080105011202010503041b0503030f0403120206010b0a03020c010f020f0304050d0e0310050612010501030308010f0506 87
    0x1690b40300000d01d403070200039040c80280c070b407810148000d1000c1c01c074803001048541058282042183c0025180c47c80300124a8900800d103400400c0b0621135804904241040702481d80020f04036200307a003800c0040126200400980b02d4002c012140700600075a505103c01c061242210100c1e4164000c1d5030108a10042d68858040c094102c51000c512030015600059943c1d00421817580050741d07500c007041d441d41c40c18006404248541e034010858181d00f0b10314891940c002804900c03000c2d0024200d201c100007d000c0c03400b00100c000000385805022640d45260081070328044d07030010300040301c7d0501461201311080f440090014165211078a080d40b500b0b251110584c020361244540490347e54845280020840007880682410b40c1008030f0155245440c0c03070002e0516803803030100018807840c08100040c54030005034160385020801c1000419031110800a4401d030b00c1012034282c0e40d82800300202c1090ba0000210b412529848445010b641c1c464080220030300440c9421304043d00d0150312034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 43225472 1250 43224222 43224227
    0xb19030203011d09160e01150504050f060c010b0603010602010f050a0903021f0b030d030207060f0c210b060a020c011812060c03020c1c1808031821010c0806030105070f 74
    0x22504013024408550611810124080704141d581d4451903001001c10010400c1d84a200c1608820200501c1d05d03914260a02c0c000960b41e4031700c5070882c0d00603100401c1c9448420425030040244004c000c240644941e55804000d010f80219401843d4031800c02c40030400d809214082c484809034990041d00c1c88164444110500880d03156002140e15204c01650180c0d0b14240008210020305607009a0390f15500d0401c102174503110445000c2484ca401d03090703420142d10010361120402e6500b4103940c140d107840c01107000b814450340050750201001403203041c000e40020b114000344034282c83d0080e02c408441803254a1614500c030700544c1443c61312044001810303951100e400e0700003509005040c0506201c02a10705007125034610b042c1c40204100400868001c3c09100715a105a05000503c505040b1a5a124000d5046005d8a028181c0c000780280d500c015200c0c84080034008000e5847c0e844d41e0382d950113084900740c0a03021441102c0030440905060040c07910441080c1c07909000510300c0c8908 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 43226722 1250 43225472 43225529
    0x40f05240d0f0812070504031416060f0203091e0a0515090d0309080a050a050606190308090d08070b010905180a1b080102070c0e0a0902010f030b01030603020a0b1903020301 76
    0x4643c0e4a808202130f00861950102c480d00481040c2d0316141c60301d043d80387c078070142c0c0001c4402e002143c2c03000903400c03280f04001e504c620985040e4505448403001058043e0318500505000703030341c03142100b82251034680303402030a00c84d0004125880e061095a481c02d020701c802c4002090308541074200030804a9003406400c14403828401d280c0300d214165030f00070150600c03172409401c4860f82c00081d1107030180941081102c0d0001811111100c1203000103101d2500980c4a10005000c400d0114003551180e8807595103440071900100c515270b94500c40c0c900342001071002d028403243d00b464240864405064911a51a49800500100740c408030a841da1502a400202c9440344070900040200f9801030078005401000d10480c040c584040c1804415184c04800401203600d01c0d103070480030000b60781c1c441a2000b5012040c180011607002280040700584480d40019402101c03882e00000d0400301d0600030840b007021300d08045603501d54070100720140d220038810b4108001d1614154058200c07071221 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 43227972 1250 43226722 43226753
    0x603060d08090a090f0507021005010807051509091f0e01030b0c07020301060306022709060303030c0a0e060a080105010206060409080406050d0e070608040203060109021c05090c040f05240d 83
    0x50002c1c3e40d40c0c903d420350903240d40d41000d600c119161404d04c40c2d038135010000280440c050f40c10521243d1304110fa1242d030303000184542c0f4800c1c0201e4407844c510142c4041200c0c14180042c2909006151201214800001d40c040c1d2805004500c1000900e514034000c003039060703a503c141281c0840d220101c1500b2150010b01e401d99041d5680d010000025126100400302c07040713840007402807040c1441c40800b00031880343d07000b4044e944a01c02c20000e55004012694080711015840e070f2286110001240d94224400d51140c0104000451801e100d42003802c46040350005d900300e9000b969207000340015501164402080004240020f0010502640144c2050601d81400240403201e08218615000180e8800d2002c1240401032000354242400168050320a03c1c000354603081c0e8000c000c0841c40484000031503900c3e607440c0820200c4000344422600301030010300602c82030350003040d444000d0909540b0710380030700342901c610240a180290b4103201e00400401c2da040702d003019112002c0c40443e522 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 43229222 1250 43227972 43227979
    0x50a090209130504060f18080304060e0f060109020301180c0903080d11030a0c0905150909060105120a0605040c0c05030906180901270504050d0c0204021b0109060b0603060d0809 78
    0x1104001c180d0b80074494607204a001e8240800d69101c1a940c40c4205c5803160400000c003c2e4003610440460700c1101201e0f0000da0000c000520701041c0311145081c40307440344031003029015980001032000d580f03030040c60503903002c010b10750b51114084e254403045440024219022460380d400400100f45000b000c1c141c010614a07020601d455410203801003a0320845800c00f840703594507807a01d001507215142d40d02402080d40d403500108200c010300c0342ca0380038500c5524480e05500f0002002d0740d1041c001d072084500c00249407003031401e040030440007030b20943c003c1d14095460212200030551261100d000700136044001f0f107140c115030038280040c40e0700c191000400e180e0031000300b1200b91988a032041c002e01022020b103100141280c80d290701680102c201240761400c1c5024400400c1002c40e0016150f410360030074045000c81f510209001e4041c01c070700c50248424038400e008403000c2c19003000071340d0f52051804018224040042001d940000e0b00c801d42c002c1d00c2e008036500001c800400400c10700c04000c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 43230472 1250 43229222 43229239
    0x101d070207080f01020d0605030a0201083903040203060c130905060d05150403080a020f04050616051c020f15060603151f03051614090103020d0606020303040b0907050a090209 77
    0x6a0071a860f06101864003c0980c2d40001d6460604c0c0040c032404000d0700084001e080d0202c40e980000f40b0540015080b9003207110041e031314900760402d00e007210381c5040c2a010045009003000342c08170595042203e00740d0090281d0340c0006c0d1500c2c40c2800b05d4007040c03520700f00000080d003000100d030000c4ca8000c000541041710741b1840c40100d0f80070403c1511406214807045554a07061400034940e41c0702405000504d0f00520a4010f0703801c10070141c030300b91107058a545031950501c10320120b050b00756042c0078010740501384045c3ca90030200c003408030180080342c00312036074100016500380d5640341901c4c000700d49005d103501080701850040d00860b00a24000100785084410304005a8004d0710244141103004030000247c107026058081c460340705401090a1940b00700c1d40d0b00c003511902050a041d012840300264401e600d0303000f503043d241030200700c1800f0880301ba2183d0001c0d60303035442503a054481a841800182821000149100540b5405842d100840f4070380140381c000303900318811055010558 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 43231722 1250 43230472 43230479
    0x412030b01090e09011d06010305120d0f2f0f040504150905071206060c0506191104080a0614011a090a0b0a02070f090c0c1401110301030803040506101d070207 70
    0x1103000306001e0106100001890b200a565013541b2100c042c0e00d103c61500860b0041000c10300c0840d00c4450075004c54003650703032403400c0384e030410040190322255200c052611580319000840054007940e02907a88030341c4e401c00100072004944600030000f820004100800c01441281481d401c4090001d4000501034002912403400100751002103c241001607000031081c0080384450089800411903418112201107458503815116800100030a04a51400303100e005400942d0303000380f000700c3e05010b61a4032140c40d14102501c416101e84261a4541050385908849401c1c40a5504840c01150b289118801c2021691050b8001c0c0900560054a80c407000862090403002043c1903505035000d04100340c200b06000c441015150000b804003881c0c00e100c00783c0e06801180c4866080d070400d01000c1e0002d20400d401c0c1c054605101c01010314000400000100404400954015486101a910301d0f80e5812001400481d41c3e104140079001c04074504c440c0035041c0e40320302e908401e0b01c0c4141c030540780d00c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 43232972 1250 43231722 43231739
    0xc0b070c1a0f07060209010f0e0d03081b0c0105040b06060f0301060c0318060305090d0206070e0f0406090e0607030b040203130f0204060f0f051206060307060f050c0610030b0603060412030b0109 85
    0x6000c3c01d8582a4001904080320341e4010040c00d42c260460508401803011000890846c4444010040510022030f001c40e15203000030400304000342d9200012130746d40c1c0f60100700d18060101503074121501c403400c0020904520f01700003035540d0001d420364138a04580c80e040c422209a20071a105400340005981141c08038071034180750341c0107401d040d00d0208a500f44000000c0c508241400044110740008043c006074940c48107500030f0401c0200d86540c4207424030000103004003555030001401d42d15210040c0c13040300c0b000c19803d10992168504010002d0064140020f0344012606401c0b207029900d11940000d18558410003064005000003481c1a252403010780011807540180710140d5581104100b24070f08a400c0c8014490500090441030a00e080803c0e0f03114814081d91044c410302281c0000d42c98410303825a41003241c140b04444080c00c11a90214039100b41e40400d031200340c3c0460001d110390800083c1e890007035502440222122248007402c030000c1c442400454100001c0c80000908640d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 43234222 1250 43232972 43232977
    0x405060304080c060604091509020f0907080601020d090501080403030903050705011d1002091804050f010f1e0203040b150a0f14030610080303010612060e04050106030c0b070c1a0f 79
    0x5206802c100d0b82e0700518050b45280000041c21103201d507042903404000039145503151622454070010203d04c00ca414400103074520580100c00d0703003000806040100140c1c0c00051507004103002c2c2c0940d02c8100c10b07190200c40021071030040e1800b04605101003800a8420792201c10b065009151481c2800120b540349400d645034041542580040c1c0c0d15900d1900c4001c0c03080d20311000c0351001c114689114240810031500f04100021741080300752001409000f818040041e0140051000304141c5a411560b180148501d9800c03140e50403e101005400840703034170886e4003640c2c000101070300a0341c8804003541322005030f150007a080890318500055484000034018060402d1030360195403007005038181441e05400412008816031071140030022504c0c04003c07241550018500f1000240004003458050012680142c6114032414200801d0000660200c400d4a200d96102203181da82c0c0e81c1003503403d000e6010041c0c0030700321907081080300c0714086400000b40402c200c01f0038246540840b0100c80d64 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 43235472 1250 43234222 43234231
    0x507061409060c06042d0b060301090206070507030c050108010e15060c030a0909050907030f06050a0b1809120c0d03090609060204030309030606050102060f0705071a01080a060b040504111504050603 87
    0x40c4d00100a020410611880b0039240200174030300713035150581d11403020840042480b0050b01c5204040085a03643d1020f410240b51640c010b000103981c0e0b0072034545242c0e01c00c0c1a10042d1140352000c04003082a40c401c1c20b10358100d9400c1d001c00c9080c0c0e1503c94960030b5080340e000c801540103c080040342c40400d42032010b003041c2a03054031120340340d40c070703005450702a42d1004044089541000300144001081100c3e0803025541100001070030380d0780c250b10000100b0f441d00e0480c1d40709070914503496074106210384040c819040c060644113100d2a98a820307913640183c03020107031550440300e60b10300518420f07402244014040c56001c9210101c54071600c0403a0700130303001540020703440705c401e00c240710241c09000001d01c000c3c402014030b858024000f01014502911140400c4000100d100c184050f003012009420072802410050f5691584c841d80ea034810f0201c02c81d0500d0910004440310301e070602c101d600c255002070700740392134030f509800304800f951080106a54150b003d1001080035180e940245208 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 43236722 1250 43235472 43235497
    0x10501032409020a092c07050c070e1f060e060a0c12030501030c06050708031503010906050106180e0103020a0312020708011803030e0c15030604020409020f03100b0403050706140906 80
    0x2240c2801c2e00013071400080d504140c403c88080715082042907854001380382100784220106c0c403162141d11085800e07116041c01c0703200a2290400124011041c800224007a0342d181b00c08200c50b00380ca18000ba9140d40500ca198042111520309080c142410001400708070200c0c070704850071001e15034809850030169045c000c00669540014010003c0580100b8050316141c108142403150990343d02442c0d01c0001d084510b18411503002400944094000020380780d4080d106010a686502000345081c0691840c10317180858220300040c128510381f11303107060329006095241c25a0854441e0160418200800011841202d10000728113030b0a02c40c00507070510901400b5460307013040c01c1c000e0603607858002c5840150048844800c1e1503541d0350401607000d01e0305c0c4000d13072a030351084006002405070b5070001414500010b04800c4080544000f10703c40c80f040c0e40240c03e40c030303101d00d2418180d000d9400000c00b5a4041d00051000900844101c0d0810840241c5185007064800109009030411320100e8503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 43237972 1250 43236722 43236727
    0x6010c08071209080a0c090f0605090a09021903020604140616080304060c210b01050d02041403070e04021c050703151d010c09060c0503160b150f010801050103240902 73
    0x1c0300b5603c500482c00800025004160302000358940f107020400034450800d0950b42c070014420510590780020006110042003540d4030b2400c6003020000d040c0c3c00c10101d11605000c80d90a410b090400b80205c10303250050150742c00e050500e0101e010103da8445110b601c4001441001044040e201c03001c095240729180c030588909040c50942c2c142c48001d001c10040c081d203490204904010280300351500c11090300003150f458007407401a42d59120341e000c1240702c0d80c00002c2c0807a883ca102810391070107280540403900f0b03045d070381d00b032009407142c0540703009500a0003100b145020301c02c60700f6032111090045040d10442c6603a0758a41e108001540d541019a9490b000314402450403103481c984c48606e92170013400090b032070200003805200c1c20b00a541c14410545901000d200d0200103440c01da0304101c8840f403819030170b414103c81169048804100c1055000c091080b44c0c20300c80b41d480003114041e10f403000d2070307428000154080c0074a03205c8a08410500d08607210b1006050480100600705e8120040c1d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 43239222 1250 43237972 43238003
    0xc02030403050d0e011403041716020a05030f061911070b061e010e040e070b0d060e0a0605010504090b06070501090b01061103040803040b0f0f07080405040c080907030b06010c0807 79
    0xa081c201543e541c0420321480e802c80b0700c1d540e6003002281e121022404034299036aa0f89142000f0030405c141007541c02418081000468007501c2450f00e0381081c000c5818112040e82c5a00b003550765040d4000151098004901090701c1c1d00c640303044c602c0070f441d15140101c0c3c03c004013242040e0341d800404042d19a17142005c00e0241a0408a6800c40041c0b40d04a040070320004100010b440c3d60380b620080380c01995154000746500c0c205200e104007a0411038000c5d95500c400d80c0074640684118020302e4200410742012569018191144070304448068540e2810702e0300d08480480104102e110303560700301c05d0800030280042c1080c400c10312000e204110000c019410b1503001090140c90041c1a9a80e44c410002030000220000940e02180e00203000c1c0c680c3c92603d2981d5800310f0080603040101d80f0008030341801041f003054090429607000b960100718995039100119503c003003e6070440c610ba04050b0741070010800d00000150300c0541810070315890b080e956200107240e84210002c6d1000b079825900c10 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 43240472 1250 43239222 43239233
    0x10e0607030506030a0209071b02090c03040501110408060c0a11150f0711100203091c020a060b1f11070f0305060f1602151b0f09100201020c0304090510030203010c02030403 76
    0xc0d8200f00160000c0480d5081d5a02187c1092005071aa4041c80018004207512038035110001078500e90240c804800c604120000d031751540c105450131229542130114400c60070400d001500c0c110f811440c0246659160b1030b001d6005a40020143c20401500c0768881101080803c0aa024040203045000e120710b4204450341c54030380054a81c1d020004021010510740c00700246a010a920709100140e59803510030300c607031034036a60700440f40043c1c208c0c065140b44682c010482100c124002c1c001489040707034240800400c03031401c01652580a0b0080c420480140c4110034010444030040308690301c0035246d001e0140c2d00d44450b030041352540d02090070000403008003040541c103c01c11344c040794142440700a000e51a2903c9207800c843d41e4103a90002503002801d40c0b00e000e103c8074101e8445603200c0052081181d00e038405050303180104003645a04201d24814802c48881803042e07005181442d003000d0700e00b4080c050203810488840305500c0c1c00f10144e90280724051401d14603030000c59aa0f40765260a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 43241722 1250 43240472 43240481
    0x30a0b0a2007030207080705010909021324080f0c0301031b05040204090902010207050604061b110607030e040b0a150e030109060e03030f0109020304020d0303090f1202010b010e030303160c050708010e060703 91
    0xb541540c004647c10003c0b40d8020b01c00034140e171404800580c40b8114030f6580f0714985400c0c0d01a1103620380c411030000044c0085003140d00601902d42d0b500907240d440380144051081c0c00c0d00d01e21200c035001c00040020480022014680801200c004140c09648000183c16a003003900580c0c01c29981c2d084620071582c0400050004003015501281400e151000180808083c0ca040c03212072070109640c1c60070800c0c28980c82044920003824a03441e02e00c18103004000c00300a81c0074074060391405000c0e074000d1401001d020100c9610169124201c42c00000450303014210045868042d0b40301c62600001401d240111348034444160700464480c40d11126030110140117030b00041d010b40c81001800007685907880e514803803c3d09828041009a400c0ca4000340e10300000c4005401c03443d02d26401281c842d811f41104459101c2640c07010b04484c403c600305500c0c0e2205645040300d038180b07800c2920041e40505017030780c0303928040c2c025a1400340e0f031800540c0c25030381c1086c00c82400e6080302041042244d0036128 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 43242972 1250 43241722 43241729
    0x3090f0a03050316090806130305040306290d020f120a1a0906011502030a05090f1c020108060f0108060f15030c1312020f01030f020c100203040b09030702030a0b0a2007030207 77
    0x810305c0b001c502e44200262543c00c080d05e403030103a036164a061014075000c2d81c100c500540d40240200b2275900201e2088521030001100380e081d84172185154440b034a040401e150768690010f140003081040402004501800000040c11070b0151505e100041540e03225040b0401c02c0f8007802490a280a940c003a003080e005801100804008103407010006600009640c040ea800c1e050565a03200380b10002130300407691101581e03224400c00100040c0d080f031341d0303140480c00d07200380c80340c03189c0d40c903020200800105090501c82c000388441c0c00140c0c03030340742c041c24007190b000d00907004884a060107aa1a41e10b07605c00c440745a10301e100003c21100041d200030800008201c2c5900d1420241c0041c1c1c0014101500c07442464100354030340e801221a06415411036a8145640e001c0b10700e0748644c03500e060701941080310191010201e00c4009101520b02000f03c1d075520354000c0240580c0c40301550750301100c0001810344a02e1030362310114007040e442600080d24090700180c0c0d01584440040c60001d1902e1003a42 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 43244222 1250 43242972 43242977
    0xc020a05190314030c040f090f0b01020c060702090a0b0d1208060d0804170106090e070e1003170a02010209030703030305060f040c080112031202031501080a090309030803090f0a03050316 82
    0x20028003103680006000c54120300c3c070710039590380d0b00d4003581450a07020b2500600000640e01e800042c1e01005540600900f0120403024040303100741200581c0c07101440e1100b641c214808100745001480d00d0031829601041c140d90010310742c403ca0000c0350b4100003941c400c4908007202c104814410b42c1003807129074040002c8034045c42080003075440c0c2c00c050003a84254840e0854005444140c00d001303402c008081c00050100300001c4800300c0c1c8903540c5036500c1c4904c04022a1900200f510781130395070000400d4035004000a104014201989403099026003c9041155400c0c04000c01555040c406103005501903500410b807414002c040118030010103403000d200e2450b1000c0000075640104283d41118908035104401c40020304080c2c0d4533080e422400c44c5001e10002c10441049041c0c0290341003602c00303a880162907541c40701e494041760180030001e0085001030074104000b803c403c0c01158046904d41c141e4004041c0d02c0746591400051b00b9046003c920007108010031040e408241a0082c246803 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 43245472 1250 43244222 43244263
    0x7090f020730031a03121e040503070e04020607150c0e0402090d03080606090d06050a05010b071110090b070f0302061324021902030d0609140711010b040c020a05 71
    0x60010300b45011a00d4620240b50b1165007011401400000c6000c24240180541d081da154540d032101c291350243c2000000741c1030301d0113980b100b000440705a03801d64801034010003140e400c0c020078080b175801c000e1049a0040d401c000010002c0c40110b40320780b8140d88a4408036000300d002801412900002c4546c070f00661040c4800c405550b0740d624881401c80d0075090403020390b01e8010100c4c1c0b95100301c41045401c02a0100320508000260384a00e100d40b01d140002c10099884404c2800c076889900d40241c46d000402d0100758817860700c002120b07151702c07283c104000c1f669601d4100040070380000384144d90505a061800c0241b44d0107204907a4000c4010901d805005074076030701d0050705d914074203071030300350107c22020b036030509040303a044030910071010322540c91140085070000e5582d401103400b82c41090030014005241c0311680030310380003134602a044100f507603128401221030410224500d40e8a6485000e900426191842054002001a03015014010207810210721b4001d03e6000c50207600150b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 43246722 1250 43245472 43245533
    0x40f090b09040212010b03010c1101050603070e0c090609100509030c060301051011010e01090516050915011b02040e030409110705120c010204030204060e010602010f060803090d030207090f0207 85
    0x107201200d80d100b03a0464004054098500c416130062140040c0643c06601c2e001d0035940c0c094108031001d4450342400000e209a40d0352406140e22171105101e100345101144010a9100c4580c102030002044080d01c00b82c1890703443d50000b02c82003070040c8031801245c0d000a03060000d090070701211090003415208246903515000c003080903010400f011a041149401c200700711608290460032503076021034000d0015600900301503841d8080f4080100c2c0d01c0d0120b2000282c5810102d42180c42a514246024440200440155600800c06020b40380d48010810303240c0059480f80b060b91a0074107503100071038545091108400c115001103c0302440800300307100401c00144001564101c145604c80d442e52105004500503000e8001da802c001d5100b400c04e0004a000c0c02146d21950480d040c5500910010b580c0d03402000454900d0b00440300590410080b810940c240000d640900c0d80c800d104a8024941e00c020081c2120b200048008107641c0015041c000e2003826003010742d140d0101e0142d417000b10034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 43247972 1250 43246722 43246729
    0xb190e0706091401050904020408010516020f0604030f050c0a03080106030e0309030703020d020d0614151806010e010c060213081e030405040f06090203071206060309050613080c030a05040f090b 85
    0x2e0a10481010b6036040c400d59116910800c240d91544030060030640d02d940d210142d2502070042100d60070118942e0401c0c003000c60748000b40c0d640e80458160701402c1c0319290b0761021240c40c0080b002c1c2d102805810840c110b45907400b00500c5115600964811125505010000b130a540402d1510b4841d175105001d074100b00c1d03070045610000c5983c12520080c01800314804038082108180b0050040d0f454140d050b105001c06d018080d2066402501d03010038041444200200f6188444c4c00702d4000d13042000184480d400f0350030001c01da42c8141002d50b008000c640c0c1d41c4003686c1c004403890f02040c1500d179003040300c07540422400c00c011100240c0c00f400303910f00d8407126a036402213100380c078495510b80a44103213104e0039070300500c0906045841595249041400501404d007800000391105150800c00125584680700c0c4022032640f220240545884400381100a85040c3c503094501280400c80c0b004811420002071540c2c0a450312000d403140d01d8065440840c40c2254040c00d100750802a03104603070796 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 43249222 1250 43247972 43247987
    0x807020c031f1107080c01150305060a090615081c090e0f150a14010e0301020c0c01030b0301020d150603140105010c151e0204050934020a0b190e0706 66
    0x741c0c0c0756041d001e15203440c850b00024100c90800c0014504001418034184240503000b014100b400344003c1c00700b0210084102d4280c2c806101c050002c0d00900003149901c0c646402c00462a8002e820102c0c030120440e5503640340c00e95983c82100c865102d1910a00410748680040350b07200c900d8101403101c4e600e014240d0108400c01002308482c490744600003240104c1c107038042038100320040e001d08586501c400c5c2d0320000310030f281c0c1e280340814226141ca0100749814002c5800031002c0038044c1c548001d41e100190b019100100322107501d55002d102d44d07241000144140502c100d50048509141454101302501301c6503070400c50b0041401c0c91005110991b005000805c1c07aa13400710200d2000b01441510000500c041c0303100a4075111030504128440314150050800e44404554806d007a1315144400042012000704410340c0300d10704e500d144260421054a44000d4080c0d0042d280c451050355110b20fa40b000480301001c0c6200508006e030401c0500d8465066009030720310080903650b042400203413840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 43250472 1250 43249222 43249243
    0x1005071b080303010b0406020f12092202030a0914011406060702040e0601060206060a0803070b010611120c03031501030902130507020106210308060303030411040b06120a05070807020c03 82
    0x180366011000012410119600028140c40c001d40752a540c4981301003000c0c0c1d0081c0302e500b005100e203d24000504101080d19520160241c00c042d250040003424040c22110507030704840650403400c00d05a28500d1400154895000c12100140070304c0303a440d00c840d8a595054001905a241030b11004502d0380c981007060b005071040310060345441c00c5200050280c007a142c20701d80c00b4090362000160668001034418058601110207102d0780f500c41da00542e0f28010b030840600f480c050600108121801003100c08800104002912261910860b20b42c146900540c9040104e500000821204948000b400d841d40902468140403407400782c0c000501240fa80f582d40c640d0310b40d441c00860f800c035000b5030049000f042b090700c1700350740e0300c0c00100c0500032050074050903004600302e100014218500403044910603688103074030300700040034a410f00000301400e2100580021003006681d121205031007a40348102100c0078040740a0dd00060001c10f1040e01412103800d544c0301d00900030709603801040c4100705 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 43251722 1250 43250472 43250483
    0x10501141219090602070c0f05031f02030a0b03030406120f0203011212120c11010c03060614090607200406050604080a0803060a030813140a030c03020d020a09020d0218100507 77
    0x302d5110510700080c1003c0381d000301080d1002680718100149062900111542e03e203c1c2100d655035141890340f1040389080d22000c4815070b0803681e500c920f89901464126109100001e94194050088ac4c69940076811400110304038030070f04041c1040601805caa002c501d220250f0441d450503015a21202d030054008003998840245c0b601424880c494102d0104884813040c00070258000015183d0b04011042e030003079508107225080207030b002c0d0103980121441a0340784a034a0032013044500058100440459100c2e008010a50201d02c414407480d51034035024442603544403101d000c220448440b46d00c864003862040c003003080003440104280503107a410241c40c0d55240c0d07403000010000c1a03a0b0700002d2201c4004203004c01d40410002e1904182c2d0345440c50401c10802c0b81e001c0045890481c88010240c030201e0b2810301c0141002600681da152000d0841402d2546401080d8181d80110070100b00c0d0a50103d50750004920312002d003144024182c2c3e00349080d4140c40c2c8003e10768420310070003400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 43252972 1250 43251722 43251751
    0x130504090804180e06011d0c040503060106120204180f0c02010504020a060507060204080303090a020108011a030c0a020316060c02070603020f07110d060c09030c08030307021f0b180105011412 84
    0x541c0c00451304110210f0f1aa04140c421a42c1c482d000c290080f401035a080b08048806000510901c4180d011182510fa0041c000c0c8400c0e803914804450584840318503000c0fa5409100014060400d9400e0f00110661080701256007061340c1402011201030102c2c44045a0510301807002607201c00c2c04142c1500d0741860625903561180c02c000e8003070701c20f0351300111640c4030010070040d0704003000c290340302154402d03614114648d80c0c1e07070900d070003c44512030605040701e02000032541142d04a00144850700ca1401600c2c14911420410344180181603425240141c490400c01102c5505001040c040c0c4881c1c1821170408030840e0704d0746410b0003002c100030101c2401000e12810380d6200e00350924090740c094024010350101400003440700c8103070700c03048803011070030030b03003c92501008825a8401d48035a0b00518441549600014003807a00c01c1406500f1b0b03a55486600035620341c03900880c83c3d81001012a1141e5160400042c03143c0542500d9101d10038040c00729170030309007050320190b1704241682c10142 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 43254222 1250 43252972 43253009
    0x1c150b010908030309010f050f1006050702121b28121704030f02090601170a05060a081005150108071b051203091b090910090c0b030c130504090804 65
    0x361041d0854000e09458031012040007041841500169500c0c080031809001c50f4440036401801054180c5035401d8140241d0001d0095500c01c2020304070181c0018a1040c02c004403c1030903040040780c50800030300d50300200d500b5409040400c00b01e6911031210000c10303082042e0068001c85034406005030410740c0d207084209018001904031047c91144d0003460656140e5503450095050001ca5204a0084180c0c0000410941c01500480010301d0250711601030f96581052030001018008c1006500c00d106900100340081c040083d00300750b112a800000700f90401d10007035014041b500c1c10300d60402c54410100301c500c65001181090b0519201424841d0302d0a41c5030090601d10b0f8820305000400c40072003001007401000600690585110760796828854441003400ba81944c200e451a1982d800441c101d21300d4600c55000d03120007800743c1070460000b51504800c040e554815240e1070005140442d890600d0501000c101000b44803c036420005501c081d920b00703200d4080d43c0b1402c00c4881c51200000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 43255472 1250 43254222 43254227
    0xe12030c06010b0d1103010501120b031c0203070201120b0d02010f030f021306031503081821030301050108070905010c030e0609100f0905040605060304061119020c1c150b01 76
    0x8549812205041d204150f0315184140f003590013100051944a0410080025422025080b00d050b0b82c8107a60b0304045141c0c018108025004814030135400d449811020144206802c418600c010300c10b5015655407c0c803400014602c52039924842c824514140e0450843d80d26110b40c41000c0d0741c2070924070303041401d2540c254000d00708444000c2045000007129144d040b004410316040e541c190300e0801000c0034141082001c807d40b4000208142c400304510810ba07c420050445000001841490740b94000350700704249925441050340a68008001488a507070000d01d031a510051a140a400662038803000030404a90504040e0511540152224080d102d42c0700320b0311545000741102c850f103810054002c00202001f21007a000545807000451a07141c140510012110f00500e268190340380c4e0b4507482d0081c4610003d2280d00a01000106801eaa424441d122150707c0d1741c01030083c5031400700030720510034000d00c151101c40c0403120354800007600d8481d408240b44100400051400000300c0103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 43256722 1250 43255472 43255477
    0xc10050907080a1211010510030303020d06050a23030d0e0108150904140606030109081207090512010f050115051b0c0604090608010b0102010905030a14040b0d0903020d0f0e1203 78
    0x14082e000d01100501440300681c2090307131050341e555035401d00611603076440d403c88009540c0c090480760780a030208040ba20a0b0041c1c403250326699070001d40b06542d10000b4110420941c09105010741e82a0007612610b040c4029400604c001e502074030080c441040010040000040c2850501c48080041000c0c18903c50762500c00f2400508180401d081c80d08002035200710302c544c000c2c0e603446041c00094039824180207502005a01203235881c10030030745201104480000800200400c61038050001d05682c40000d6140d00208041c000a541c440a0704c20009842050b085082e60110301803900c4a0650700c001190b11360201ca2201b400c000b00c265001c1818558008902940003101140c00309401e40a540184100d0303809000070000c1084803030044e801e841c180074001c0d0540e0030500000c1c00c2c0b0f40c002e10b20f0300041503c3d041c0c0345142030340f03130010f9042c00d40158114900302556080d200c010150100200d400e156194140301c9448070440c600181314200d4001000d020343c5002040c1003002104105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 43257972 1250 43256722 43256729
    0x1f0207050d2709050603060901200f0d0203010b070606090908040504020a030905100b0405100b19020a020409060b09070905030705060f090402042403020301030803010515070b01030b010612020c10050907 89
    0x2282c0071903568201e071010f0302e000c0d10858070074003031080400c540e224140f081841c2004130215407082201078511041d55500000000404082c003048201300f0801e00d03200840c040c04800365015101c05039400d248040760915001880c07460315091141340450a440c0643d012a6070031100582e031003240781000c901524210758020304601c510145887c440c0b245420244440c4c00c1070314100515510230000340c400311014440d1b15444e0108024248554400d0031103140c445583d8012070b2440e0078035030302082c00c60701100410780d5a05ea40c0c440886c414901840101d80018403441c02104050070500041e4560059106c0d140c030401c1300003800d24030050340e402942c01c0c011380107204544035550307481061640e4900c4488002c11621000014103403900034421382e0706072500044110305680c00c140034040036040500c1c0ca4080503070b05010301e200040085811034061442240c10707170308039490003002038042401c000344c81800d00c0c01400010462030002542018040e030081000c00d00b52036131107185042041c0c640 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 43259222 1250 43257972 43258037
    0x302011b030501080c010804020f0405220c06090b090109050405220516052b0309091a030c0a030f060207020a050a03050309010e0a05030d210e1f0207050d 68
    0x8a118805806901c414129881c2e8405d6601106071800116103d05044030020360154000f401401c450174286d000c50b0340301649000b03084143d01d07a40d17803a200e4882c2c80e00c811203000001c1441440105d9110300c0c954010032269160508003402c060001c4c10601c030b18020390740143ea4800000e4030300e0000c090030380764540c1001d41c282a03007031150500755142e1110b1840340c0104132120360300050034100556450384030105031a00b0412802209003060a00e80e21400550400480301d00c085402100c0d071160b0f0801da68488841006002084189420b184254107102d1141c40307906401c0000c10990300d04c0300d40c0d0360345c4100300580c0c1d84941c2c400106004a00c1e004550400c19549e00841000400801043ca4a00989030442e007080074204006880c070740b034082d244c0c06810075100150000e019042030700141a55400341010301c1e1845504604403450b220a101c0d069210604c0140100ea008440303580320145c406081d45026081e46883c0d507903c074401074241c100512001c41d61100c03100050207801c0103002c0d8 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 43260472 1250 43259222 43259261
    0x6020409020c0f0c030a080d0203040503040e0f07091e140a0f06120f0203010506040302130b060a0201091a01031a0a0b03010204091a031c0507050109050a05160b03090a0f030201 78
    0x64030080c3d5a0400141004404e20541400314010701d80004c000c00c0840d07201e009580b60080c500c4080003e50030181c02203403030f840203100200b080700d0302a07001e5200e5514041400d50900e0300d80c1c0c0040101c105a0b0060007801806030f5040b0503a91124014400d44070303103010000001340000e0202d41c0d400c10035449004140c003c00000700da51a03004040851100048a040c0f1140d21452500310882c8401c0c41142c0d40114200003c00060400002e60004c04055040000d201c0880c14045034aa40c407252507100180d40d604101c0d001c1114071320000c1e2185080c90004801981141d5481400c4541d40c01e0f840300c0e8034000c0c2c0000710620f01580001540c510090000e41d180c40d03640b0112000b0300f844a21411000803401d000b03078090708001458031550070003ca1a0041400d024406894961000e001074451307548480b0000d0115104000d0400824426801006007400c0113900017250103264200800016080040c00800755000400c040c0b500e802c624521310003c510325040e4010540f8000c0300c090981c89 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 43261722 1250 43260472 43260487
    0x24040306020a020601080313050f06071a060a06020114040b1f0f051003020a080f06060c01110d050f0123010c12020607030608030702062203051005060102010f05150103090602040902 80
    0x158020700b2080324242c084807807590f00c80b68900d8490203102c01d4954038442d002e0080002e4030713202290301400e11020380101c4c507021440d01c41001e5000416040c08007140400c06000c81400e000f4944401040b55100801c603800d03400ca03003001c0f4102c01501c00f421a0700220003003181e104500c018500f1200390a6280828195503415071b02c1c1e545880c0c8101445403070030700441d00e001406402203560f13003006644e545855035100502140320a501400044c2c00007428029000400c10034812400c17800703840000161640403011030b407015240020100300054034030500402121080e55295501c411282081602e8080d01c240125088404402e018118090500030007101540101d4a2400f071881640c040c005640c555000395031b81d01c1104002500441d0030040d4100329984810132000342405101c0d040308443c0d0300c2c1c072070600e440031b40203041010565503800d124156030244110307080c400e42d0000a00c45480c220502d103415404410140381416161411001040003543c11100a090381c400215100d114 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 43262972 1250 43261722 43261733
    0x10306050a3f020906060715110c070b1305120a060c0e0405040308040209070f0f080c0f03091005010807050a15030b0a0f03020103140906010b0f0409051e07080103020906240403 78
    0x201e0406a0040012802085c8581013070021030b00a983c10180d00d103e04585070488500906d44c1c503031590307010b1074140107110910360f052040d00001c161400005444002209034103500c51003561005204444c0034504100e0140c000c9001910b103070b00b00e10005149003030300500340d4500c03c00d00d050755481860201084201a004040c1c940154002d807400c1445a8414400341e4007104040d0b10040840d5509079003100d042d22400c1c2c05070b449010781d40440e0a103000250800d45a40003554100701c4d82c0c210344102c40c440c024521800b401011400c0041004914001c045079030320a130b900030345020a0751241100da60078042c0d0061094034201030070500b4440c0e600e04406410400c03601040b400a400c20300702c040c48202228100340285100b070064603a591034030303694402a90240c01e050354101c800b400300090711942407181c02d02c0f40d103400c9003020271035a0030b4244200c1202c006018005002018006001603252481c0c0d481c1e014109951003d49014424001d034281c807070340718400c004840006004810004c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 43264222 1250 43262972 43263089
    0x21509090a0608190b16021629040b0901080a02070c2904030b070f090812040303110d0804032001020309010b0301150e0a050403030609022205010306050a 68
    0x4a08200f664402000c816004000c079000ca48003170007030300f44080840e41c44c4072210215468400c0c4d5004646158411240b480e22414040d40030b0005542c58002e0f00451054610202062001d400181c9281500784070110045028110460f410000d2500c0010b149086640c100ca0805410001000c40e49603038070040740c0c0d220000aaa540082110042c5504c00800c00c0e0a03501544c0e44000c21101e50341d243c29040380c0c640c4840402d1000c00068000000e0300240600122403006040090586e4550441c140070305584800920161258001c1a500e40407640c030001c0030b50000ea2500d0000414420f003070741141021700304040075000c2d51000080c85a4645c0542c451200282c0c280e000b8094441d60b1050070801040e14410340b18803804c0c2e140000c901e02020b80c0700a030300c0b41c030a043c00107403cae41300d9180f1030407600700c1e2004001d80194420b160460601c0e022124005080901c0e0900401d428000445e0500e80c00b48602c1d03445507800d11080d0780b150310118200810f520b8100c01d0f034001068540c9420103a0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 43265472 1250 43264222 43264229
    0xb03060a080a140c04140112020402090a060206040b01060f050a1101020f0a0302040314010c020304180906090503070b0a0c02031c0912080f0c0f1207180603020d050f090a021509090a06 81
    0xa204401c054103050034240180500348649440303460a9030328102301e01d140003102a8080b80d02560812030b408550303440c502601d001d031055a00030040c1b490706241401d600d82060b0001400d1010b00002e2900d0107502901321080c00c691454000840748445d1034043c0a80103d00101a0480000c950b0a80581c0d140d030140c02102d0140c801c00303000c034031009569822035040e00030300c80c0160410401800748129650728000750110600001451540707603120038040751144d04081303078280c000292110920400725103507900010200001c01c42d40701c40c01c40103075413803080349450700b04001103c3c1c41100e0701c001a8811940c8a80000c01010301c400c902e1002072250f40b085415a44046408011442e0100404103031682d0310003400c0020325000703014484850180700200171f0303c10028134000360845090300c1c20902c0001c161607100562522a9540450b00f620310042580b590320030748804000440c1d0b4001482030751241c0680d0011845610340303001071a68803038001c80740e802c04603030001c0c00307205c1e41f440d44000d040b07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 43266722 1250 43265472 43265513
    0x3210a02100605091f030506040f1104140117030c1203010503100209010f0c08160311011d060403032c0c090c070c0302060c0a06090602040501020105010f06090b03060a080a 76
    0x2101030100d4082100c005014a980000e90940061807200c5a2071561110f2042800705c001c200d59a036448a1038483c04031012210f005001076400c003000007124041c2e1801400310307004d001c2240c04070f0f485016240140300d0407007030094962542804a40500c11076403030a0400f400d03120074071945c46409045500a101d8540a4400e41d0301c1075903201034074800d841c80782c0016500c0313281d42501400101c13041c1c1702c40790b07003a6202c3e4410440b202409895001c076500e440d02c2512000341c0d1a0142c4912030031201c0845600d030300041520302c854001070b00815800c0d4000d505003000115503414001e07442076888501500c1c4541588801c0c6201c680030000f50700341d0040d0044a45401940d640240480140101d00c4000d00c0070107690001e03c01850102c001d0701582a00e082182c2c0354603820b1315102e042c2c0b64510380c1903507240d500080034401968280102405003d8140040600301c2c580f443c0145085141d1060340002203000c40801d625070b803002c1105005040c10001c48607015014142030b03015412080b0340da41c4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 43267972 1250 43266722 43266733
    0x16020621090a020a0608040305040e0613140129090607080403020306070c05011b02061302010e0a0b180906060703030c020705060319060905100504050915040803010305011802090406090203210a02 86
    0x617000c3c1b0802103a4407955065036443d052615000250109540191001d544060042c41c0c010b070b081840e114492641c2c50001c81c0d0131040d454620400501584200342401e48034205c920700d02440424000c440f0340b0b46066400d580d072200786007131a10340c43c0a9a00025494001c10b014018000e034000720342e01e15030303000c0e0000b00300c0343e6000d1820000e8a020f40c01103a0168020200003402209882c09441100d4018103100c2e10540074035002500d440c1c41c0d40c000b5041e400000c40c400400c03040c0c40084021841007075500110a042c400001401c40c00342100c024201a2124003c001061081c0840307402420701070440c903224100b50820b501105100c0c540d4400e49440d0540c00541c03c140b60107031a0040f01d10070440d50040c0d0800c000e1002901c0700821038007180c400e401684074110140d1020510442c010501c05403213504602d419400d6906582d42600d500700c007441c01c40050790321307010015082940a1b01c001303280e440c14400300381861400c82c02c0081480898400d07000d201103030390003408021525400e031017 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 43269222 1250 43267972 43267979
    0x60a0c1506060801030f0f0b01060507030e090402010203040e0a090b0703090b06190b1e04060e010810050f06090d020907020f010b010908150c13060203091516020621090a020a 77
    0x3000c0340c649105030310000380640c0041010602c000840320102d401411f40d40d42d03900c0d490f00c40740d0382e00c442039020794000741001a130801499808203218900e040c0480e80e0844a080c581c00003541ca01403030040440e0040e446c004540215181d900000704582d004604141905d4014400f0f8002d01180b07400b6151b440000b80051814503200701c3c185642c1b04000c613498041c41c10012442d0098001206040400180303140c2451000844000391008083d00d0b511102d403a808030000400410b000340c0039400c09541c841c400c4c13191f81d03030700e403200300c0c20b0035095a1403a100d4150000003203514004100203900302c9003074800d0256031580481c2003006080004028441c1200203001103441c2380c4548100e8100360401410700760b81c00b91501d1120382101e100c1180600380314200700205050841b90f400980903130310000e002d102d2414098403d0064445d403100070707030030300e40203007410b200c80345003242c00920441002a0008000ca003d04641c48102c41098401c005403915845ca43c1e0f8070a00d6003c103a02c1745c007040c030002 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 43270472 1250 43269222 43269263
    0x1030b0306190b0109030b0405210301060206130204021c09140d0c020f01030b06040e0a050114030c0409051f020301030506160917030910050d0b100e1905060a0c 71
    0xa00840845000d04100144003601000800f0165100d41c1082107010000010800200009014a000b1805070008240762108603044200c140c0290588000a100400a640e00441c0c0190300c0603000c1c505401c0d4030110300c00500284130b411074502220b080d00900100140050707004c482c0540c400c1a80d80c103060701007030415030360301d40340112100019100c0706000018101003150542164040c1400720b01950303007800241c035640242c1c00101c89001034500304815440da0340505030041600c044801c5207a8030b07880100b600e030025042490700840d241c24803a010031604201083e850340007040050303610540c0d4841800170794001e20055a0a100380c0b40803401c5107800d0401c10185154a495129800d8582500042000260030355141680410b0007000041d444164981c0d5001c5825a52203984540152020040f144841c0410340658202030414024680244102400d808101c8050513010002000d180c8ae041d81500031640100d400f08000c03038029080f464110010740315000e015228800100744 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 43271722 1250 43270472 43270483
    0xa0f030c0905030a1527051603030c0803041a0c0403060f020a1704030314102303030d020f0c011a0a09052a0c010606020706090e010e16020703050d05040501030b03 72
    0x45641c55040f10b410305000400c03009080c1154940c01801051503046c0c41ca010200e994040c021050001c100703e02d850402c4401c2c000c2240d00b0400d5041103006a0660728000c0134400b144100501e901000800308041c841504814500340c0d41e20025054645490b54919189400c1440111515800e01c0241611036541d8001d035141d0020fa07550f500c002141e0401d0540356120007a1081d01810340e143c0711001d42c0c0e03980100c0c45200381c480c00c0c10301d501989030031528407188211046490541d90022036880440d40c02200300d8012680080c2c0142c4c9403407444c07190304e20300d11503445140410f61034144501081809000c085140100844900094598402c1c9103410386030f0440e81070707500400c000300000e40c10070003a00800c1038000003e90f940c00c1c500706100b407e0031604160451030250b403010104002050b0f2155148010b00800b940005540d450100744080034000a0a40080c01403d98040c5082d18804c1211000658128084a480b200c6801c000741180d8450b0280f280001d013052854840e5080c0001c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 43272972 1250 43271722 43271729
    0x50102010f02090f040b060706151403031801030c0207050901030606061812020405040c0306050f0405010606030b010804121806080106081e150f03010f0605031b01020706050c0703080a0f030c09 85
    0x80203041c840404100304c010100d0040c06540310000f800f103d804070b0042d2280894ac98040800e4074801ca00b0444407804500c66440380c02d12076442013000c840c045072803424080305040c0a08010030243c024040607810040075400041d04a00705400000a21401d074000798201d40c45603c0340784440f05800f8003014050110b01032a0b0000054203136010060400764451548980191140ca401544a40d1180191501a1403448442c02030f401440140942885010001d103001d0408016142449001070905580204058460200c840b1030410311402022840c00d54180a5500ca00181d114a8082c2c00d9540070700907100001d0780c1c44000703410b5075030700070342c0603c52810110644110b40c0ca401a4800c105440008176400c25160b5018072141e841c02d0264403030814032450042141403c220602d403601c8421580c00751078150401140e01103136000f00b00c0d030066a40c28502103a076240401e4940b841c0001a50008100110001d0500741c6194000742170180103143d9501032090084100048400107100d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 43274222 1250 43272972 43272979
    0xd020108070c0503040b0304050d020c0405061e0402090d0312060b0f2505070f03050c04140c0304110307060f022506110c06030103080403140601030b010e0916030804050102010f0209 80
    0x204180302e0140c00281d12841c410802c5034170342034540d110110b4540098a0407035841e400202d07003102040d01400b803011000f0068804002c6460200300144486524020301c0290b0500029031240544a980407518040d4000c0d0001c032402c440c519000300b07000758600c1d500342100d2401c5400f049903c80340e005c172407950714a0f20040381003030703550b00c0203c510244130304a125100680c103401d200054030030303c03034032004180500c46281c40745c1c510f041c0181852401240c0c50710a62900103100200c003249a001500440342c589a5a104d41c2d481c94031042d0341c0030301d42c4030303960503c109400020b035590b11220145580b00558280e502c203d0010561080b446d141ca0f0195480e10000c0b0800c0c0802c0d4403c100c00800c4103101c40403910415000e00114405038423f81044d00e12810001c1c050042c810000c0031005038503c0c1d00001e1000798035685400c4820035040c02a9070201a159000ca02c6062081022240350024252300100080d600e240031301c801d5002d4800c003405942000c840c0003600b00c039031003550700685029 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 43275472 1250 43274222 43274237
    0x3020303030a0506010e03100e0d02060108030403080a02070914160503070210050601090905011401020d050c0705090a090204022701050403030c120302041d01050a0e0603100b0a080f01090c050d0201 87
    0x1040001510004013032a0412002c04038441542e43c040102d03441c0b2a0f0000400950323280014900c2d41021703400b110075015544007000400c00303000004122001c403600304007804d0310f800d411582241014000d0748a240050300b490f084075140184402d02c940a0003130342c2031800c00d4842d0a00140ca403404110707046400758000901000d4a070460303410181c1d00020515105030880d03122002e50003100e5003078000000b00c0ea091240c092655804012000400b031070383c03c00c1c500348030010b14000c1e80c03440103008182c080c001250108400e000035402c04001260300401c20344d100d94103000c5540180084038029005074030029408025135010344201c6050303a42641d601090100305445010044440d480e00c00300b01a404c00000540e04200e8064101e0005070603454111945407104210f10f214181e04030310b28a80088052105680e00000e03404039000d207a00c00480c0c00c020b00c4000481c2406030350f00881e802d01503445141d03014103040d40b011600310320884e07480301d981c0d4541c0e0510038400006180240071030081d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 43276722 1250 43275472 43275481
    0x103150501170405030f1206180402091801020712080a270201051c0513030e0102060f0106080402040b06030a060f0b070c0303050f0d0c080f07110c040e070f0321090302030303 77
    0x1030b000300b0343d803182c060411245051452003015446602c05407854a0684650050002a05d0280750038000040b03000b422100504060300019031000000d0040a1100088202200d141000390182c0361099004110300401189011000d0003140d411289180d4580c6081805441c00c40b4991a01c1d00018107a80310281107210f40d4010b55060780904a03107000c10b4465800e1200e030300c20501500344982d840451089440301c50346005803031200f952035150b040d90816001c10000c25681034440381124a82c2c03420141c6521180082401090342080d0942c00110000420090350742c9600200b04582d00e909040850b1907a0740c4400049000d0140014244815a501000800d2003400581085e0a00d00388a40c9844210b034068811100d850b402c01d0302003001c40c2c00b08100c04944503c5150711400e81c2c1085615801444550798903030324404c3c5460b00c1940c0c0c4a229460049040181038054188000c20610068407801d0082880d003101900c102c2403d0b610340404a50303481031540f0340c1200e901034011400c0d600da = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 43277972 1250 43276722 43276757
    0xe0a0509190c03060509070303090e07051213050a05010204050a080a050706030221070e04050f0f0c0d020f0d0605150c03040308031504051905090a0305070605070509060a09050103150501 82
    0x16180800da90b048000c44020020a00c688a4a030150071450010322200f032075450302403c0b0803a9507210740e070b80304051400c010a564003d4101c0b0301c0481e90001144850341d03a007030079112052251202421500c10074100341c040100540c000c00541f0005c64032400d43c2d44c0d840c009180d03a00c10400c4014401e400c00a401c000c0075000b9005801640000d039081703079001505a604000c2110102c9a41c80001e075040860348140c28144501904141614485402c40c030f03110048a400c0340e03001d0110001c0c8030001a2100c6082c3c0564166882070004100039035484107a40c0d16100039148a00a4501c0f419610504180030100e1300211180720100e10090750805285403201034550304000c11041092a220103103c0c00c42c4c1c1c0b24410584142072420100340c0000341002c50744125000200710341d00755031104860300c001c01c0d00601035583c0c46903c520003094680c0e4201e0111040c1c0a8042d000e600305001182d03980c00c240e0020b000000780c4400381d030700704110164281c00500c900c13a5841038501050342600804e0b414007 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 43279222 1250 43277972 43278013
    0x80103030e03070501121a0d0f0c0608220501110703020f15070816030609060e180102040f1a0c0a0c030314030c0a0c170f04090b09010303022d0a0c0e0a0509 69
    0x344201001c10b0041f4004085100303030121072011108250365403030104c20019548108070240a05160030f0b0540d1418032101301142c16045601e044049403016000104070b006d406c14501d449100d44195140d0700d162802070364a0001c20b10f003e041d070241c0c2c03510420514000030403610940301030380ca6003e19207171020326001a80c1550800010103848610109003000f6900580c4000c1080400900742d42c542031030100440b00240f08101407a900401081158180c801003c1080d07400000602c0104c410500812403248103040b00b18915000c0e0044c2c003024480150020812603019498101342582d90040001301e40c4811118840da601c001e106c1d80f5103640c03085440700101d038418954500c01c103050074000a20764000e50040f07254898005824440071030b01e401518072221058885a070154115070b000394503510403040e58080d21030030106100380444004018804441900d0507a1000002c50405031692502401075009000e10400803514401d818410b40d071044054202a045080500f041d810584 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 43280472 1250 43279222 43279241
    0x140907030f05150c030a0c092702090a0303030204170102030106201608240c040306110403060606030c170402010f05030901060509011d0c070f06020d020c0d080103030e0307050112 79
    0x38494150003d03c02c02041081d81e004060002559840785402e0f01d0603811388201000d40303c204800884108035614000e00c0003000340f01c0165211050000700c01c6002d0082c01400c2c5441d600c80340c42c0030000103068242d8024000c1d142188050b814105001c1c1307402e400d0744000c2c1704e84c00005101c406074103503040708444a0301000e0300410584891550485074003010a016400034911074001d07042900da9400720300d0301d1508002440c10a2141450300d100c4e8801d540c0141c0c84003034205502e03000030141d02e100c0002200c0c013542d03000070100500c50b1600001001804000350400c0071076420503284c0d0414902941e418800c6278140e480c040b0340d92072001c045401ea04007614980480d0340f10b20004c59180e88907500c1c94041e24051070350500782c0540e080c6030005c840002e005069940c00810010b40420480c5100211150304094003603a00c021440c6002c009105080001c0f0031404ac041d400d480e0a40c0c8042101d040703d01139a540c996100c000400c05071103624a12840d0301140d42c805c840c901e88400d540004110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 43281722 1250 43280472 43280483
    0x60503090c01120908120610020a08030a02070804050a060201020a09120f110109080d081006030209030709021e04060302070605060102060112030809010902060301060804060e060c070201180b1c140907030f 90
    0x500c030710307a1840016000011b45110900c40e500030880c482c02d04240e11954420035100900f8050040e86405006e88005841e80d0303161900010100d084c01252002c0f038005080c0544440d500941c0c0b40e400078002d420003407010f000a0a815400594134540c0c00c02e120078150064404c140c8807036a6552490540d01140d00c0302d0600c120b58400064250090029400c00c200c3ea03111024a40340c81d000e0305030810410340051040c10710600c2004219280000c0103000e9a6a000d401039603100d103e1103001c0d48220791680c07030035046000180800c8040d070640142035880d1042201740003a88a00300103a850b0b1009000d48400d2145800e42c14020030721520b076030b68201e980311b0300000310740c0300c1c1d5008604d846d07000740c0108012601140a000c00c204540c8500e95800310b0503c050b05103800c01011600e0107100e41c000c042e040051014408400903a0f0020b4034005018000d501e940c0c500a414001d0952001030301c04014042c0b034a00c82400c0001000340d65445409080061304445055507910b8400f00781040007901c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 43282972 1250 43281722 43281731
    0x9040603050615120a03080f07050d11190c12030906020903030f0a110d020703081c0c211104120305120411040e16060f0315030b0a0501060503090c0112 67
    0x3140c0705004082c06242d9180144820341004410b01c52100800704c3c5004242c3c0c4046a4400401e0b4040c0d2601e03080807450040b07452548816004850900807010b4421120b0b02c1c1003080c0307040c1e41140000703180f03101504e50100111007555600b071343e00d5200f07420044e1070711481c0c41c201c02d41584694040000548180801410400502c02191941e0005205903464100015081c0c00258100c40302200040510b07008040c24844c03580020f45605c0c6500c00201b1403030001c0350b0f40c0e200080c0c3c9802c00300c1550344194108282081d8240050495107012440d4200c410004a00d2174060028000c0d003e400710343d010050300d018a0720301c1e0320440001c48082070381001001d2110040306480e0324042402540180d10080846010900300812a489009184255800400c80f20120f0114500c00d40c211261401c140498030366401c130070f8026002a52060001d1900180c01004006540301142d000e81400e42c002c002503a02c508c2c080e1170342e10007526103c14550103c404407400b50701c50204840312500c076500126 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 43284222 1250 43282972 43282979
    0x30b030313030f030e060301030305043b0a06080705010c1101050720091003031d040615080412020d050d27051b01030c05090f031c020709050c0901050306010302090406 74
    0x802000e003038008603440360900d810304007819480078003407170a48800c8503810700d1549556406002d500c80c5210755144580b541740ba02141580d8404000c8000c0c2102c052140381c1d4150007504404090203e0b5a407080c87d28118000c41c903003500040c0303001a1078041c0c45d00081401c080d10b5080e00c10240030038840c1002001c1101310001200c204199010009603590100f041d080b10341048200c20008050441960084500f00046580140116000101e03444802031000a09000c90301603c907580103c40a20b4030390040c01e0349180d10443c00c500c6113001313400020b42d896202030100d032a00300e180132090000d1400c0c05102d401c0d400355842200381e8070002192414610b500052580d0011204130282c8942e0401402039824410400204080000903c2c040111052048000d0711a01400341624042c1441030855025514104a288140d80c43d40074858103c2544200007503030f9181c903018040d1f0640c10400860042c00b6564161768103154140c503054150b5462000440094100d012120340c0952502d0000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 43285472 1250 43284222 43284247
    0x40305010c020a060c0c0201050702010509030705030111070c0504050103080f0c0f1606030c020a15110906030a0b01090614030f070302130b04090c08190b011716080f090c01030b0303 80
    0x70420311000c0d4016200480c0241046400c584c03604c2d01550511281030340090050303034003508594020790b0909040f6101c440160100345410748980003203426619040214105140740740c058040039100b0b00400c1d22081d141c0060105076103003848020a154002e020811004164601078240009107800f240c0942071a00c20003803401302007410000e80440703550320a005890b03140c054820082203a000401c440702c01340c0c0e2210b1080c004400c00c4181c944d41c0311543d80c01e150031304046030504c030030043c08140c403402c0181d4548024900c01d145180469280380e00000c80c01d001c2c04408440e01c3c903440c0001c0c15036449180019000720001d00150401d942045074146010032158031001802e103a03450540c0310350070070003810102d070522500c090500c80100d04000141c0546210102c04c4608030a01140c1410450b0058170045420300300d034059180b04008010b0f041e81c03500c00390a0031400641d00d24440ea20f4036450501c009009860070741d101d810408070001654002c0d0440c0f0070f404800f41c1124907001042d1103e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 43286722 1250 43285472 43285481
    0x20405060334091811030102070c0b18090106020607050304020a0e04030207030c05040e030d020a021603060510120305032701020a030e06010605120f040201050f0c060406150f06110304030501 84
    0x40e141c10518601040740310041140b00500501022030041042020040f1100305007072083d4401404441c00501c5101c1e43d403000c2d019140e1031607200e4401d40070103448550400240d0040200492050703031070b1a140040b0b1401c03460f660704a581d01e8029204a45410004854a1f80000d00c26030300718070129000181c51183d00c14040c03049000b80d02403c48641076140c01140c1c4810381e40107074407888c200740d01041c00d0203002c0112a1800d40e4030ba40140c1e9544034a0b070a07402d1020300e514030060300300e0f20300d4000b0500c01c4a0b0030482c480c2c00c07401a070314003642c3c031303258464162000201d004d0001101480044c4140903880300031086100807002c1d60111540c0c00021a003640d12140750003002917219410740d19980c2081040c0383c09005941452401c103121014140c01007075005048140ea4010f4101042c00d6901803811030b0702200e21100c045580340480e0700319541c0c802c1e0030b0b03c3c01c40e82d16103800701a11001800d507131240c0c19a0458003c1802d051302c0c0041c02c5a44440440011200340400c000000014209226 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 43287972 1250 43286722 43286773
    0x303020a0203010507030b060409020d0e010203040317091603020f0f0301020a03061a0306100f0c08041202180114220e0105040308100b030f09100905030301051212070204050603 78
    0x302a044800c0c81403500303540d800b5110009040c180f0b0303100d180d90380c0c1300380944081e200c2c140c81c01a180c111001c1c40f40040c0035452030042c190752001040c0420305603c200b0761049085030820100f0b25440d03809072140d0300d00c41c0c0d550700b20210910740790910043c030705800001a03403c0c00030000c0400c840d486000070f0880e800000003801007603440c4c82c00c0010204220343e9510000e0940031081c1185054004524001900064801000000320603007030345a001e080c042015540121000d511162581c0f5541155681684240d10070301007060114401307101d0b5040d89040e1461500b900004210b0403040c00003c0084001c00760482c40702c1c54402c00e01c081b062080108220400f000401c10b400c2508000c0c184079400317000b600c10701000c1c0304c0610021100c1402c4a800c055000100cad0326036a501011a030030800041000d1000900b440d00e08414000000081c50603188125810520854500c4c022039680071004820f0308020f10030f101c2940546090b502c003036031164000d01a07403011a13140b205d003061140040c9 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 43289222 1250 43287972 43287977
    0x12a0515100501030203010b0a050310080303010605040603061401021509011e0203100512071a0708121602010b03060f0c0903030c0604030e010801080604020d02011202040902091810120606030209010303 89
    0x1810090001190307900300700101801e007421440c0d94100b0820b2652440342d0013407182803000c000701050301d1460300e100210040c0101d000b666180e584401c8010503036449441070500203402c3c01030210710f001c0c0f260108010b201c0140c00800400505001d448440200200040380555031740d8401003a0345108001520b0075120210016900d240420860204074925002640038400100300310956900000d840c0c000d850800041c0d41590070708030304442c524819000c0043c0f510300301090301102030500040c500d026802400d85601d030b0a1001c10120b08a59111901d158143e200c60081441602d22031242d5801c40103000d891458003011001180c60341c0c2c07105158108541c090000c0000341944022220b65212007440e0490709945803440c00c6940d88405000a8450035081d28003008680c0104001c000031302c1d4002041d03441e107907a1820714009400041f9558004e483c1026101fa00010041c2800d1250111203000d0f10364909242901d5080c68101d40304a80712581d80c0c0380070001d6070311f440e9418021840b03035 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 43290472 1250 43289222 43289263
    0x110109080903010c0e060f0c120a020a17090d0809030106080102070302030a0806090408030705090103270506010b120f0907030501060b0a120c050f070302010b04051e07020c012a05 79
    0x403082c103084403000c4600358100180c2c51800101682c440342101c1c95189011102500da81a4401c1030f03041c20700403e102d0000c0740001445044043e000715030098840d008812109204c131560300c035491180700e01248654403110b03802c94036002642c0c00700034140411000d000040c41940701c2403410b0881e44608004c0d07015a00100c2e240b010540c0c0228810b5120380150742e0301c41941015502c210050101520800500002041e0302520380d01c80e50050340e42c1200700c0d852030340119080d5101c031805850441e043c1c40c14003c0d58004502a50361804403a20701e00007981004d82a039807401708194a80340603083d82c100703020340720000011440034000c0c2e01c041c0c10001c0d8415514052030074041d200114941c840107806040240c24070419400c4019200314030001901d803aa222010b2500301d0041c44040aa1030b800b0780b078003040c045440404000612400c01c51498892243c44560060b0f0340c07412001c907050b002400d0700307000041d20310120440700d03c05000f40744c800c00d008506650303031420a046001210510b04a0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 43291722 1250 43290472 43290487
    0x42d0603050d1e090609030809010203360306040f02150c0709050114041a0f012007081501080604170f0307020a0519020105030402040905120f0307030c1e03090311010908 75
    0xfa549440300041d040c18400400c0e440d101010705800e4007840082d00707a0202140003906a4024030441d0421010382e0004c2c40301410300c0700d00004101100d42c0c2c3c42d0050b60607030415406c600707000807140c0c02650892038442080b5440d500b00101500c2c10b01c1e40000c0e0700c41c144002002007200b0404103002d084298004503045d8145581c280d00e421402083c81e02c142c1c1024001e4030240760019010180120036680303454410702e0100140c0f44511655540250b50f030080440320051600424805c0a45841c0c0c42512070140640504d0a840c050038041c048040d003010340480c00140302e030345a46412481130003481d42803a80c3c5404000c0150000c03503810307015030050180e400c10040103001c28040d4003078080c4005116042500000c21074000104001d0242c0d40d00d40b4407200703118040090388500700180d0070040e9110201050003016810a403448000300341008108280240180120110b41e0f080d04030b010701a011340c2c5005c4000c3d01d88120150244080307a0005650501c081c0a20700615002c2e81801d0b541e2943e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 43292972 1250 43291722 43291757
    0x50d020c0102160302012115030302030403021e0310020304110904110a0801020c030a12020702090c040f080c060307030f0b040606020718020f040513062111042d0603050d 75
    0x40003c403003406041542010f100607a00316000d14800c155a21144003001203204c038010081c0321540c0210707901410b0000000802d40e0010041c07041d684203840c958449000b680d0000a0040718044640d07241d040b40001d503c1091042d0b01440e40940180b540c01c80c20180c840209413480801c3d203090343c12240d41d82003001c0504101000c070b0002e0080d900214a0820b01a86c810307164050361080d0020080084503452649440d074040c1c400280e00103184682d030741014624202030350f0040c8280501d4005024000030304a44c04244944c01607c090601da01c0c0d035840e25802c5004029050320400c4440d501c505820054985205113809451039400400b00c40c1d0801d4128140c1150032000780a12a0040043d440044121004c0d54229541078802c282c0c02d001c80e2074a480640802e800c907400b088002071000d40903044000e200380c0d2050140c0592401e13541500d091009035110b100c0701c0d40c04018603d081c07a02030354080d00c0c94512a0b100702d400289150b22580c80605101c0d00281c1a00020012900300480c40b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 43294222 1250 43292972 43292983
    0x606031b0114040e0717070e061c02120106030b03190c030809010203040306050c030105011d030c090928051603110907030212071e09050904020603040f050d020c0102 73
    0x4114024042900e01480520300c9241203a040350401c580e0035829a8420b07880b10658025010141c010282890450342c0201454080d400349601a6400e8001c518103500030444103070500e5000c1c00b418600900c1000403070b00e84c0111410b402e5900c0c0e00f0000c200c2981c0b00d40022501900869a0118a4849400c1018a84207403000a0000c00d5024400a40058a0b8800d88021240d06c00d4025441d4100f103401030b81107010316400508694203000800c280c8000f14002103050350001d803503c1c0c0441d18283c902111090160b0101c3d601503008007840d03801468a20380a5600076108000c64940c550360300d10388100e0313811052a1426141c0f0001200c420410240320381018039403003400300000c451940d110701d043c204902d003005029140d100081202203101c0c1d0100c03080c128202d40702c0401400c20b000e0040c08010707040240241c0f0040c0e1046294058461106c040803984000d205d0a0760762195003c200d10790b0b101500403248091014814000100c1c14000803d0340030a0703402401c0071a444100290031720 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 43295472 1250 43294222 43294231
    0x903030e210106080d0905130902010c0b0106110709020c15040204110c0a0b0a020703050a05030406061d09060c04080a0809040e010c18080309090703050601030902091807080607050a110a080403120206 88
    0x200b81c0c1b607000d001c0c98136441804080100c015170007040c0d00100d070005035002c60845030054802e03004400003080041d00000300203071344903000b000c48410360350740c3d8501801ca0007840ca034040030707402071070600320108160504950400d00003440001c41564140d03c03404503620106034419103411905500c014070100d00412a030040c0917000c207624040440e50001c00300d200baa840942408000b00200302031003896408400585a06000c0c1c01c10504a1009a4a1100c04a4a1002503c2004001540b0b41400c00c280c5040741c2104005101c9202150b031131540ca034000f07503c41d607002070f0744614282c00740c4c4003402240340750849512661040000840080400002a041950103034003c22651959460300c58140398002030500d80043e0700d40302d032001280541165040a58001c00306001d0240100da42112807041e41000c0c011210360a58506040c2e0300c48100f160800c010031300c01e00c500c500260141c0103c00302d02c010034082c1d500f00400303070f518404e4a812a800640300507440d80711f000d400e83d40400c54584c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 43296722 1250 43295472 43295477
    0x310020d0b092a0a180b0d0b0f0306010b07030507051c0909050c0d091e05030309010c141e0d0504050c040b090411040f0908210c07030903030e210106080d 68
    0x3c1c0128a01c01160a645011454840701c000003100a951031142035207803146a034030002402c58964510380118142c0294182c3c10070986070050100c1c0310700d850458000d1100c00035010b88596840d00700d00c0e561319008008268103102040020702c000900a008550940c280041203400c0c00c1203a800c02418034846801012141c1e24020902200a6140055410040000c50f002c640c4420b549041c0e00082c2138107803216041300a103c000750800070044055441000500000c001e0302d00410411030301912420f5441030307502401c02504100c29030300c0c2514060501c11212180c6040d50505082044410480d019262a04030a07442d00092a040c050313012200000c607006d0f8160b05054079003058641c030001b0b49030b1065580d064908246403840d0040c080564004010b252281c4096215005480f114004541c0f44168800092100d80d44101600c4c40d0680540d90f00100900b540e5042e983d042055802d80d82c0144101d07940140145002405042c4500900000c00c1042c940210384d45040e0580700319005 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 43297972 1250 43296722 43296751
    0x40305010c02190c14010309080a080a20030f04050703050a0f0b0a0e03220f0b0c010609021611010215090d0801050102010c020c090a0914031206060304080403030e0310020d0b09 78
    0x1080c0320f0013040301541c00d25506207142126800068000f000314903402400e000000c906070541580000e1030b20b10402e4280014001102000b5900020f203120003403a5240700014000300c4c440350015076056034081e1148080301c01072900e9443d01441c0000c2e40c041198038402006070840cc12203443d40c0641c00413910341c13051250703800c0d10840a480b80a410401d00e90380c0c85c1c0d03c1d2900344640180c41810018040d07000109409500c40e2018041903000500c4100d6560900d500020003400c24822907012600c514a100c0d00c0848175507031580c010000003541d81c11442180306000783d03102c14009841c02505148011300030040d41180182400005030710140c107591509000351281a00429003820a4100b150495040d07039403841036100411400030090041c2c80725010103c4444400801420a40c600a02d0b80440f5606e100802840740700880f0000d00c0c00d402030000300300090181140d00075101004058880452190130100202d0700203512900c0410384595000d0300a00b86103000c56002240c88881e0b05 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 43299222 1250 43297972 43298023
    0x20301082a091503011e0e010b0a03020319080c010c0509031501050306011206020f131d04030903060b1f05030105150309070b031b0c0106030204060506070b01051002010b06040305010c02 82
    0x50200d6801043c15034042c0181c02c105280d03560030f5000e030b00303180070000b002018502243c403500000c0140d807011540075031a000e0071070010319090114404a81d801001032001e444c0c44945446850780e48070045030021000e00c40d1620055080c01030210390745a9650303260f120310000040500d00841002083c02269104005218548001c11135a066a02d411100e82413030480345009402031141c00031111107204041405581880465121030855a421245141a4030512183c2203031f0401598004c01140740300400b003001400a80001a10314002030081d840c40301c2919001d00802800c0328158000365000006000c6407030100194182c06c40000003540c2903241034040c20740d41d00c00c5409020002c100220001b403880c1d04e010000600302c04018140341e20b07180c14001c824003038030050004a01c19070034240041568207181d0180c1d440383c0c1e01b01e40c01c4111070340303813105000b00d0440020800d81103548400e0708200c0740d21500c0060000b141b00703500000301c214034244d0081c02e04100109041d44401c1804892 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 43300472 1250 43299222 43299229
    0x6090504050a03180504060e01080601330903020402031e090106030f15150603020310090b01020c01120204051801030210020d0503040605150904080a03110a02030403150f020301082a 80
    0xb50401d030315007004140d010507205004403000295100075401402c002d40400c90000c00f540481c103d45101c021510b50b6620340e60402c0c0e21484070030f0015248118040307050082e041c0210203502c2c0c910700d402d0019880344c0300d0300401e090368411510a40c1d0b0720715a4800c0084040c810035007940c4043d02c1c00080000500b142e4071000c1c1c00f480b881c0d01800c132004200d1040e0a0360940c0c2d01041d02d0b08038074014600c2d1250ba510024010b0342089680c00c1007510400340c00201c81800340070745054258164058440c0c1d645240040d94081e505141e1805403ea0910000ca8203072941803050110311104410100c15626610410040307012041c2c40d40d08541140008071015508003082e690040ea1184002c9120366441a00301c0302181814580f9502c517401209200600034060010107400179240d030305005d4649056041091442140c1d80c0d5801079100f00010004183c103000e15401841424402048038103800713102e03c0c01d0340c10a8012941035040320020f0441440c01500c1450040d02101001c4141c08014000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 43301722 1250 43300472 43300483
    0x905010215090c03010207050a05070503010903090905250201020705070902070803012610060608090a020105031902090406030501020c1b0d03080603030c100b0f03070b0306060f0c0303010e06040609050405 90
    0x6075840068540041801d92500344180d229004020b4021912040c10b82000303030386d803048030f401581c86014000b03021600e0f080600414803055010348a018501e0b2a02e03c400f0000c08004000c000d086d40405015004069076110701c84644020340d00241e203903201814a03a08200d11540022038403031040164071700003200801601c0c115800d0108940d803040003002d0210314400003840e0400380f40195040300503daa00c0342d1160703054a0031651103070752030369450220325039a01c450080a40422000e00019150260904000c002201c80440142c1080301d045c001c1070580349030781c00c00c64445c0d4001c0741c48492420100030b03880f04804440c06030b20381c8032803100c00308801c5034000c6000b904000140000409503203081048800391003000d0101d96926000b52036050041c00388239900d038800c120004144225184c001501c009a4041d0101145581c85280800c28107500820b4400c0c51080b0510002c5a902c00130b0014500a001604c080350700d9103800410081112019041802103500e004103000105100054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 43302972 1250 43301722 43301743
    0x91224011e0f060e190e011d0f06120106051203030708091b0405070903150b030d050901050d090317040b0105010801170a030f05041a0403060c110d12110301060206040c0609050102 79
    0x51002030514208007142211882c41407440c44201408000142e104090004074100c0d05040c2d004148d0035441110b141c1e2201c0e00792400f10102481d18013044851411501d040b2180d6083c40c000070380c55580300081545518040034958036a0800f008100040c0d40100001d075011110b10007030300e00c9600b80d503580556004c22a0f4001c2c010380c0c0d5140001c41030381c0203031900400340d5003244808002020303c48004000d80004400a802400344005280400d401042516080141610b80a05000310b1100c0b0400a1829070016400c10800442d8044000f42d00200e260050340640f421550a6040100244c41034206a01c01c4405030840c0710303603940d40c0c0004100041030035814274100716004103511040707415001d42c1c0c0005945030700c0740a001c0380e1504800d0040c022284580d4003800040e144c5141030705c041d500c4070b00041c8280c00c03022000606510540b1049058514018001103841040c0c0f128292508240c00c00c80159024100740000d2041075503408000740f015203000143d190508000135101d1240c1c01 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 43304222 1250 43302972 43302977
    0xd0309030203040b07050102070510050709030b060a050d030210050f06061801020109140d03140903042601050403030905160303050f1b06090d0908010b06091224011e0f06 75
    0x4500405100b0300032a001443c0b50925551103040a05010b03000b03500c0b6031003c40d928400d60350400e00f81c83c060b02840384500c6443e1210304038a46107807902c10341c601c4000d05450741b00011100100d100d9a40d8070101c4155802a03004220905414482c40211140600210352800c4900d0400c819651002e04848007030316405c88944c0010300c1100181d01410400c00000c1402c0d03050341e402100400001a40f20404429640a2160b0301030b506000280701015956481960001c0009004412030b801c0240c4070080c5000810380e0342c00f1016003087c21202c050740d0450010351211030b50750600600b0070591030100c00802060856928559010f45a480f480c11030b11036000b408508600b81d800e104045406800b0030307105454007841e0020446440d41240d11640010400400e00032078500c00500c502e2500f518060082c61401c01c0d91801c01018003202e40703601c0c440c3d21416a42003204020b201e04a111101031528101040d41000200c00202c56101d50480c0f01031a02d03035040102028600e410300c111102030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 43305472 1250 43304222 43304231
    0x80709061a07050f06190c0503100b070213090c030b0f1006030e030405030f0312010f03050303040f110d05010605090a0c02061803041a0a0905011707030e010e1b0a0501020604050d03 80
    0x7441c20a080c4940743d014040c16000320010021b0010200d0180c0c0e004a4040030b040001141000f03041d03403140015030f000000d69251140601103032031203130014500c840c00140038503001ea000030040702c2031f2200c01c041101c088000c0f0004100300400603040c1c0d60029040380d2070068070714141064020320000c500c00d807020540c0319880a15104014401c5501611019061300d031141003e09103640eaa0f40181100100d603034007034000061a0160210040940354030401840ca03603106ca4441c5106001c0c814030030b079400324a00d880005d440c1d442c1d01044a03c1071041c00041981e900d0041080340042e80105694541420944840c024035070102c1c085500406007903442c081c040081c00c01d945180199000340c226071a040204000d482412405002844496a1500354050700c90300111810f405c0303c00c285424020300000310341014040d07001103030180381c40c100015850090180c55403a203100340c4543d18407102048904030a50a0907000c070b4000d88420300041a140c10181c0d5603e9a84180c610004101540d5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 43306722 1250 43305472 43305487
    0xf040504020a050d1a0f090a11010302090a090504030e093702070b090601052b0201030b040203011d06040209030a03050708040e04030f0f02060601080705070f06020f04080709061a 79
    0x54182c0d101c00fa150103082601c00c0074581c03928000d807601e00380d018802d5900e40070000765948041c80809103d030381e103070000d0080410a80d4421080704c82c0034503450b040c15000c0c071042d600da0303c0d80c600c00b0000308107000010849040900340640450072820300d060003003a10000f0000500b20008a80d071040410a5220300c15144805613010b00005240300004001d0000a00d24144031384001054003800b000d100341c036a00c1c1d070384d802003080011444840101e4030407044922490950001300002c0a00d0060401040304550480000e0403688240c02051441490030094a611101c0c00070655110605403401c41c03404691000082c1e98001740540202000000100d180400c00c92000383c030001c0c105504800c00c141014507001d03150707800c3d60300c06000052243d0040b014940c40020802c0c080e0006844a200945912400301c035079621000301500c0309007a28203010002540c81c4020715080c224200e40c01c0e121401c1c0300c4100e04041c410f50080c19000d007003140034010b800c08034400c07604076121540200d641d01c08 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 43307972 1250 43306722 43306729
    0xd050c0102041809120305040c0501030b010c0c0609090b060408060f040c030f03120c0f09050108060a030c0801050a060b03010b030a050406060503030a11010c03060605160c1a07020103060501030603020f04050402 93
    0x4940201050001203c1c2e01404000c1a070040b00e1150702c141307000c00d03e006030310714202c04a58040b10007408502000604105550191340701c0206840c041c504884040020f071218200d501d80e07640440000b403400041084562440c0c805c5ea150a442250f19620b45450410041d41e9000090001c0303120701c42d41c101160410410300e107007000441d4409640a036441141c107000c1c0041140c1c00c2c50807003080c1410220300710588140c00c1c41203191041d0300c805030b90707500380130044400320801442d1503084000079001001041c3c01480788002482c0301c00021400c7d280c0034800e0f4060f0383c0e442c1e1085019a0050006004071900078050701d0744024855400185561a800d105d000350049600c15a01400002007482d240c5034072a0711041c0f10758174030009000c003140215084080b203081d84111000103505000d1141841300c03814900700301030b000d0200b0110440d1150a1485413551110b45d04003294400540c650071540c15000b0b5500a050034201001054a50307004500c0c040084e10f030152245585400282c01c66a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 43309222 1250 43307972 43307977
    0x8250b070b01150c12030606080a02090607060b0616061b09032303130b070201081005130513050f03030403020124030303021b06011202040b0d05030702061806030703050412020d020d050c0102 84
    0x3034001c881703408416030810015005152900458000030383d91000114405028022503102c010060310151505042d0344801005000d4800c03410b42c0076401304a020307840b6941c8100008c449018031800100402c80004042500102c00c100d1018070018000c100045014070324990f000001041140070721b11194064541588138504410844104131b1070085800242c100c060310b13556200303803182c0c0c2268031110b14002c0c0e4910a423180719070028a42c0c2d241040c01d000c54001d02d0b0480480383d1619011074465035124201400007142a040d40c0c404000c1209255090003807406103021802000403010b000803a0100022481c04081c00b4140c00141f049403e0703204480d40112820300d10207a4000c3d507100e2410741c60300c690000040e44554102107143c4040c0c6002c8140403451a4000001c52074400b040c0d0070301c12280c01c81c800024904140c03110021107a29140c0046206601540e0001441d240518015a0540d0205100703030465010740c0101c05000c5e00010051410501070800545a000c0307043e00601a2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 43310472 1250 43309222 43309247
    0x30c010c032c0306090a05100b01050409050921130b1b070609090b0415050906060c010203090105100602010509060402040e01020c0708030a0f170c0a0908250b070b0115 74
    0x580315059500104207180c0c2c003201c1050100c0507100075444132081e4554038814048041c269800c010b621358400c00082d44007030300064041c1001420603556104030307411960200c0b90038020750001071100d0400c80c550b01d5100328001c01a00710508060600d80031000790303140c070b000720b540030000001c460b21424021001003214203101000c6580168035a0f1005010a07501d00c0351040c680d0500c000c00c9407600c0c1034040c01080c5a402082032010310b01c3d08081060012015184640003c004c10922400b00c800b80020b6208408200000c0b680381403444003510f081003d58001001c692501c1c0600400340004901190007903012280400c0e10007181504034020300c6001e000e05240d20455400144500000c00a4500d041041e19610794506a21100761035041e15120b0700c649018042000509095110001e000000442d02c1e03e0a44140c036200d40c545003950143d40240c007082016260494034405c10184009800c0c00009242444015603e4041051041c00b4004500e10628111003920348101c03002da804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 43311722 1250 43310472 43310507
    0x218040207060b0108090a08180d050307050a0b10050906090702071509180e0a0303020a0309020402030403030228320a0815060717031f091a0906030c010c03 69
    0x1540341d9468440020890b580149000c1050000020307003083c00481c80001c5107400c004c44a14040c030348610f40c0c0850581e6901c03a580414142c01c00c0010810070805418164400da0051000c4d5270181002c1c900400000e201c403a0b0540f80039024402c030344030803403c40d42240d01500c40f201e503602c40c440c040e81081d00d16000702e0041d030301901c140803145078048003246c210f41d003081c1c250f008a0301000000c01512040b07664500c440d03122030b00140000c1e03c0ba5008109018041c0b40009500d50640d000606981c0b0954050300042e07004038880031242c450301540c17004500b1101c01034040e0140510060200b903d401c00c0410001c0985805510322074224003912150040c1c20f2030140d5400c46002e02034504070b01500c01420304901008140b001c0d050000440d0322498010102d1020f040c0910b04042c0c00340e0005203000030200c11568054400f00002d2200000303014081030208460400c20b80703140c0c400182d140307a41e10441c41c402c14022103850200d25415440c4007807a0015040781a400d059a40041400000e100d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 43312972 1250 43311722 43311727
    0x80108071d060a05100c060b0904050a03111f090201030b010e0a050d06061502010c02160f1203030b040f020a1206030b150a0b0c06040201080105010527121002040504110403050307020402180402 85
    0x702d51ba001c60f451300c020b442110304115480c808824000d40800071100140158489410348010030b004920310591784126030212480703004407500d128010300100c55051300180d1124200c40841d038150061802c40c410a01c6c0480682c103401000504428080c402c0354084c0c6c030704040365070510016070090409803c07000701d94000d40d45002d4000740207044001141c40140103904422590b500d528055074121614040b060b840503040c003400d00d02100c11444110306141c1e0b034452400064489000c0c06840d6017102400507241c1d403100d44080c141c600d04035409a401c03854140c0600006401a6015400000c9030710b20640f0180c4442c04a0181020b580200c0e0401b900400d21001a07003000550501c100d02c03c0ea12041166a80c000540d510b0007801d400700203040225868903e40050040c0300500c0c201c005008044490302a490541045030051040d240b560b0001020300141c01e181c09200b6250840c8001145400e266481d007030f1700c034042d1980080c0310715000100e682640521000f1312410002c010402c55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 43314222 1250 43312972 43312999
    0xc071a0406060b04060509010f090503190210050a02060c07030315140a0909050a060e0c1302040806060102161404020904050a0b03010608010b10140409020a020d080108071d060a05 79
    0x1551204115000c440d41418041c000c01c80e100c2400941d022a078603501e0760b504118080d030040d14103422940a40042043c8807000042c642e13010441c84048041290011044103524010301061202e10714085083c040d041040209641c1d000544030388c481441c44069844200c18079086004d000b21617801c04260348000c201040c000c1c910715400800000486618060729a2481c18009446030744101034140d8009181c0b000203d0b240d0340000810454400039190f44598500c006a020b59881041e5081c803507007c1002d001c0c1000400626400c80c200b4001403c0215010b03103604021001c9001d00c45406d082c8400062075502ca076016070f0112000100148400d10341080c01c8001000b542864a10070341c00c042c03000400300e8042c4660003040c0000b030003410403650030b84070a8440e006128081d4003480c1040000241c03a9250f0310240608021550140060540c0d0840041c20701006801813011904030751802c120300c0c09609a5409000020030b029501680d42d000021f002402d141e01581d003100e80540c2e942c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 43315472 1250 43314222 43314263
    0x1801050f09010e070609030311010b0411090f0307050f190e130506150f0d080c010c0806190f09050916030302030a140408060708041523010506071a0c07 67
    0x140300325101d8008001280110031515500c031107a1040c640850102c07441400440c6c8600c20102030b800711035002180890301c2602140c02c8a030800c440101000c40070880c01d0007880c204000444100c800c81c000c01a480c1003900141c1106a1640c2c2103100e109141000c0c2d50811a5040000081c0404048191107281c000c0d1a0388903175400f010100d44034007611000800c09111880141d02c418000351151450419402c00e02c00c412030401000d644010050002c211078440900502a40e41625616812142071100910030450300e0035090f42e500c0182074509004403a0205c0c42442103034990740020a16071075001000b820181d1010790403400141401c00171051507000001405010007582d52a1641781d42d074030f004209405240204070081d004480440c41c12489140c240e60402e00441d0540c03542e01e0b100407050104c0b12641961018a00e10182e0302c0002048083c0050060006540380c6180843d566903003005140b011086003c000403160209a03041c08940c1900c0c483c5a0102840540640201e400c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 43316722 1250 43315472 43315501
    0xa0c08030702040507111e160906030203010b0d170a110d08010f0909020f0402030406110c06010603060608070f081803040801050a05010812070602030606090d12030f020c15180105 79
    0x3039003e181482d012500c610320a0114602c40b15515000e05004010f10440104101a000401d9064441c508901c00503442c0b841c540001002c00d91000900503286105250030f49034901c4c14903106002c4610340e000402d624a200600107160309403190756506844c00141e6042c0d02e8400c911105220b40e482e40c0c000c0a401403d440d058842c0300030007610450b078442d40207041d1002004025005084e0755100380207414150007460b0024840c1c00042502ca5030b07411700c002990071040c05031080d0762010004100964251045501901c102e10348041c243c5842c0401030504580d403503800080080c1c5000090f0440440032081090a15031807d036aa6032382d81d1a140c9010b40b5003610402c4810f46088000920602d0005a40b003500da00c03440420700b000001e89842009410007820990000d0f0204401e000da955901151004503100741d516001c540044040201158218517107104542c0c41080705008041e400036004000b81a244481c0203a41e550101e009009494070000178599030805c4244418240390144 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 43317972 1250 43316722 43316737
    0x10801020d060e0702150408041e06030f0c0e0d14011508010605030d0819060f0b07030e0103050402150702060708030106020106080d02060103110904020402090904031215030c05040b030a0c0803 85
    0x606001481e1200e0f60009460030030f8076500b001d42e001d01e941550f4070700d00c050120b51142c003403030035642080d03940d902000000c0502002001c480a0140c0240500ea401d403107490b0070071454070300c00c209802c500c00d40900a41c60003d1a40e210302e186030312900c200030818400d04000b84140c8024001d4840f101c84c0c2c0c2c0e504c80c0990003012441d5007810340125050400060780c800c608046c1d581c40481d80c4481031282000309001030040d03001030b02d503600445c03c40d00c201d031500014810b10b040242d80381d0003824000c1c41d0f00c4034051524101030070001440050313a5101da41c070302d0b04001300300d2140d680c0207648002001841842001040900c000c000002c104e038040d03000004440d842d500ba00d51070710f03894904984031403090000905400c0b81c0c045208450034105125644075101400052800f101c140c001001c404040b0340413000248208141e00d9100f015008483d036041066800049140c1190303900d0b0a51500c6009142c0a665120380d64402950104241130509401140481c022a00c6080c0700c1e850f58820403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 43319222 1250 43317972 43317997
    0xc1005010504060501050c03030703050702071205030304110603040f031b1a01060806060a02030301151b050f070609030c0308070303020403020d060b0f0906010813020a09020f091315060c02130501080102 89
    0x1000040c4a5004104072501001f0382c001070351469680b00c0c0d0980c001c00c1e018210303208601c40c1130f002207030002d405050240100c1c00390000b50346a1a26240a0a926a60f00c4100b80a01c50601c01e00002035603c00c421411141d150401300752400102c0c1000c100b61245981c00341500c0132000545620300b002c020f505040c0d40d00c9a03504d1256607a4502808014400c0302103110060b0700030030040005114169520300110341510b0b01480c00352600840214070f01d480031055507250000c0d81c8695400b48200130707100c000d000505101c3c1c0790a1954840000c2d8500701d11000d401101c0c00501c0004041c4a5411900034543c020103036a414030440c2010f0000f000d043c203c060080d41504048502842c281d044103104000594544d2001d0341d419a00b0103859a260701c0c101d030003814156010030200c07914000380c000d2034506070070161203072401720800c0100e000e01800c0580991800f040e2100000c1000c200340b05840142c20807420a0040d8030204020700408280c0c100801c0c68080003260050064005103807a18070003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 43320472 1250 43319222 43319231
    0x807021005040e0103080903010b090a0b09181005060402070c0e0103050105070503040f03050c010e0d0c05061b09121f1d1515040e0a0b011a03010506030a020f0c1005010504 76
    0x480c0548042c45940100400c0240c1c1100401c0007030f012030020b200015000e40086150001ca501040c0010410388042c0c00700d0b034464121005600305040b400764000307500841c1180c1c00000c0b852036616031200c2d402d500201600ca00c0024400e40b110b804a68460f6809805071850329070341d16075403040d0746080c08110340650820007c55421841001035a0084e50800082130105285640a0b2415402008400d09075500d4904003d50700c0000e02445160752415120760212840507e4160705010000380724007500116003100503103048210f026920300c1c0748103031860a084500700c0c05d45032804012900e01e41030000c00c101d40284041441c2c00c40300302500c2c400a0340310440c000340c20064a0764000c10030514103000607000102c83c251440c07040106144094030006002884e041c2031405e0884500c0c05076450301c0b10340c1c010024404d12000303983c0c28000e855411821541400700042840c48003030b024000c0d07a40c0100781080303115420381c1140c40401e030b0102140d842d103440c3e21154018100900c14184101d00c1c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 43321722 1250 43320472 43320499
    0x90603020306032802090a0c0e06250305070b091f1a06030a0209120705010206090f0c13020409020309010c030f02040b070f08070512070606120503071518080702 71
    0x240240c0b405144003e029003600003102d410210907119070640012a502800485400b40c0c440000003401805540740c08582c0c0350a4040280101c1c0d1242c200703a0040c0020000c2c1d0500f4660b048c079032400f41e00040f43c588650b8605040485240c080e8130000380104c00034000f804108a00081c65401c40b03500d2001301d140b1020081c01c100211750051a900368a003040b054484141c3c90b10000851344042036050040c1049401e00214840d07441f10781020040b41d120000500c40e40d03030100070040e03000701010000c1118500350003e1988a5100f0301c01c050207904e003903041e00b031001c01d41d0b01a40c010b460415000c640383c3c80c000f05100d01a003456508140030910b480203000c00c1816078001c0f507007950300c0400c216241c01c1260380c443ca4421420201036401640901924002031010f103e8050045c88810b035060301c810140c10158200e1f8203035404104140648109400050350120984032000d030048150b0003000b0656038800050310f0642c0100c00b013000c44460002c100900305020700725840c020744115862404 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 43322972 1250 43321722 43321727
    0x5010506070b070305061203071b09050405070e0402030c2709030a0212070c0b130303140406081f0306180506150f060711040501060809191106160b010e070906 70
    0x16890042c0a6801980020b601c99009070072140c0c04c0b642c0078041d0001c480410320128116084032100316211442c20301407003440d03a4116071110207440035280c100400e09250307981030795034107941c452403c0f1030b2900400542917540c01d0007020780500015208403c000c000e42c5541c2e010078180400c540182c2c0001c03020640c1c0d94800016104811002d070000d220010701d5003182202074004c2e400c21a090700b070b0b41202180402e16000607040300c803089240700d0a95419450068000307001601441c10075070090008000c2240c0c80100b03a80c1082c0e02e46808208a034400d00400902082600003900c40e904101001041030b004600924100e030003181656041e03120204c1d007445658800d40d006611401610f40a6403601d1300700003e04d1003070300c40d0b107080030030410140102c4d0644000343d0086000c00c40010800c00e51100034030080c8401d109801040046448541d100c551100c48101c201303010b12000b040141003100740c1d5401d107274066000780c03064401d580c0d504484400e203c030480301000060f1101d1030014a150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 43324222 1250 43322972 43322977
    0x150203090f01090209150a0308190f05071e140106061211130311030703151a0906030607140702150a030c0807050d090c1e0503010605010f090905060d02031f05010506 73
    0x1640100913440b01d480c0c0b200140440d080300c04206e503100e00003100c000000f60400d401031030555050303152010a01010103010740042c20303600901c000c5c888100048000114800ea030480c07a44026000914000c82600f45004c4881813460040855032030418003064507a0000c05000b8080035a02040c0000310700345030142642c1c01822100110003420380d0301800010502c107164501c040019049814407030f602d0300e5440f0913581103019400c40c1030b070303d950394010515480b0000541d0712050700d00d10014144680803a5031840010080c20401c68607110030000005504103d0340c5044d002464100030f00b2098103486541e038004024080403a1a007000c48844c580a1310203e44540701e5500c400d4202803205901c2c202400e8181800c544002c12030f100400c82c0c0c00c0c8284c91052a11021464040d003604100a0500b1100c03140c22450511076107200f070f0610f81e944040c15100352244401c0114180c4c071600003085048051001c000c2d81030007a00d043c00c040358030344103003180600b030034032001e1080d0390385c40c0c0c244041e51 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 43325472 1250 43324222 43324241
    0xf0105060c060a18020901090b150f0313060f0207061a22090c0302220606020325080d0207031e0801120807050f030309030d2403031209150203090f01 66
    0x6402c1600051880350b0240c0c000340703101c1601012404142c0032503000404401090308400826543d40c18810142d00784178500780100c80b00d11011600c1d105403c1d0039a2603c0c040100080340108218003107108106142d003103d0702881030b15205640364a0180341000140401c001d50080a01012010440300e10b0028204d85000b02c10300ae001880c01801c25003400a0500400151400a058400000181c85d01700d5500d580c01110101300c03820707100d054101c4055034050360080b42194018464000e800117500c0b40180800c0742801180e800d00b909141211940c040c800c204007a0500c042144400d254004003c560105800400144840c05c0d01ca0191400b000078080c3c0c141c1c080813041000001200400281101402a81140c158076000400289107900480d800005d5400c0454044900300560052040d000200d9180e04882c90704501c0643c2c042240d440050700700101e24100119051140d400714000541091200c0101c01c070703080d2800301035441a03d56020383e1060001c10b010100c818460110310 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 43326722 1250 43325472 43325497
    0x60105071b081c08060d0b0c1803100203071b0b010b0901030908040b04030213020403080f0304050a0b09030a11010e0309060f0f0703030b010912020904060c09080a06060302011815080a06030204140f010506 90
    0x343e03107903842a048d8941201c00b02591141d8040c0d4604030f569030811405040d084134207009607407480c2020300180302603480c2e0f0401c5241d4000409030000101800709450550701010b040c551195094801200036007500d010181c8490780000d0046814110320f401802640c0c0203540040c1c190821613a00012842248800f408000c81400b0f00c0400d009070200031030300107024204450803003030a500c405a4000080c2c0e140c1541386e10025070f1412141e000302c036a1b442002d070240204003211502c44c05a480744a0030041c207204120010b200e001540b10313101034641741103c011000b81c8540702071401800406c180701600c1d0106a28510004207007550044041400d41d024040e00701e180c0740c540d5249c0240408250049c244040602c000c2a070320020000c800034a4083c0c44003150b41440c5000141c20030300758015841210b40d11280510054003458140c080001940c0b8003802c00760f8616002100800c1e40e03410095101c2e086c0343e90203c054043c00a41030041481d03048000c0340b81d9030f4030100320382c40c41b034082d4104a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 43327972 1250 43326722 43326743
    0x1060905060d0906020313060b030304080c0f030114070f080c190309030207051309110102030301120308060411030f040501060806060a060507150504080309010c030203060105071b081c08060d 84
    0x703060001c090941c002610101160744400d42e555001681c20844910769040b070250088000c2c8120340c080c080d013011054016525060800e482c55469440380c422082c0206003c000346a61501e00358031020071000c5495a200f1241004080288a80c42000d080b000040400001c500c0710303001c0c00d00701d5040354012072914042c02c0180c40c054014081001003642540280140003601ea1a171204114030804909000900e042051900b1044007410001d205c0c1154002c0c401031203d01c0d2031640410000d43c1600f0070a0f590741e180d00000700a454100b000032880c5c0e4010003407250740740c078450401d80641c1c840d1000740320440c1c40300b6001d43e0790001151042d0b40724143d500c00300b1045015800800080307010340421a11049080a48016070f08280c50440d1400710000c10405144420300c5009808003c40c0703020b520b54240307031000900314050048080d04a030400c01c0c1c09494420300102c03000007803594100b5541984d2850000f0410140040080030106003c40005504c0b072a1001c04035241680c4030a001d003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 43329222 1250 43327972 43327979
    0x50d020d0204060803030a060f0b120402060313021f0305091209010f0e0402040803190203070209010302150702030f070906050607331802100c0b06090a090b1e070503010609 76
    0x6a15500d0030030507604280e548801107118001800110b1007601c031070704c0c089400c038035050070040e44085640c045070302580b00340500b4240b20441140c640c7c0042e012500c4544039210400750b02d1800048010007075001e010341a01d4001c03a40042d81c07003510840c00340c60410541d074480900980b191001640101e4030482006220a15801210020602d03605071909014950701900400d0881e441508071001541c03010170f4a2040440000c0c80c86018030381c6202540c104000341d40814418038041c00000c2c840d107000e59120301482116406d50302e0480c0c0050880f4206035003007003542d03140c1e070f110b0240c041e5981c2003480204040c2010b004403144039910400315028a03260700e902000708076607014a050f06004070307844080301d0b140b94050580d0503210a0900749445401d40f04100054034200c80b10418050554041d50200344ca403030040e5882030741502c01e00e5056855885038030040c0b20f102030050221004a05000b21012209075010603404580e20242c03003a03c0d08134064480d0b02003489401c0008042e42001e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 43330472 1250 43329222 43329229
    0x30c0308100905010b0c0d090f0603020a1707030b040506030a0803040807030e030d05030a1d1c120e01140c09130b030307020d060c02010f0b030304050105031905011d090601050d02 79
    0x15884050940e4040784951612204800d60f502a0300442101a0109800070004c0301031080c0c01030070845040254406142c00e0014403091401d1140c0001e05a01150075105540107804280044040f16840c00c40c51401e204003400400c408000030f0700881c40e01002404034200001c00740d40180d00600e4403811a0b071903a8612140340e00244003142081401d84454031907071020400451511a0b41e15155217902c6c2c070014090441d40c2c20f68106516001455411840b80400308407c001502000824090600b01120580303950000100d9201c2c440c1c90706400e000d04000c10340c40327400141c01c0ba80c900f0000fa00d0350010b01126004640d420782d40300f5905050008070700607d90201c00240800380a03641042d4054000508026282c1d80a8810944a0102030011507082c410840300038050314081215800801c007103075070381c0150700134107041c4100000071502c07030100c0f00c0c420281d038040000c0070301240d81c5581030411041d42d0414408410756002003c1902048040b41a9058600242400e00e04003130715000c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 43331722 1250 43330472 43330487
    0x91c0e1305060f0603010e0708060418080a0201060506030a15151b030e040c03050a0c1814030c030d02010b0102060a0e06160318030f02070801020c06060904030504080d030c030506030a030c03 84
    0x441d94000340c3c000400b02c068981101560003800c00150007126403030550800741c112000141000d01c178502d42841e0102210880b4800e88080e604035240359250074096a050b07004240e00d4004940c090008010000445a00d030410924103801c03c0e0314000880d40c42401c641003103c018655804160041020348000c0e0100d1034024605e400f03031910703007518001c01c0040340441d45e42c140b0541c0000c0d00c400c20410001c2c0103028001c800c1105140108041400e0400d8580303030104c034010320710f42c08105400000345940c00c02c171022600d14018251151040344000190003455001ca5081c05030155500041403420300e8400d0352000180c207005890983c0d03c0059941d000c001d10300c545c1c024555107000b112618101c800300c41c894944692a00c06d40300c45e00000280c940000d582c86044180c0c010060025070803400705446410071801e9a09002c01e844a01d41602c00d0300072900801c40381c0c81141800d0705070641c942c0001a41854648040105450b46001e01d500d48a83c1c81c00a00851104c0700700074000782c42084c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 43332972 1250 43331722 43331731
    0xc07060509030622080a0314011401080402010e011106132f06031e0f0129090d05120a03051005040605010804020906150a20010203040302060c07030c0b091c0e1305 72
    0x90b03144c601e001030391150443e8000180110009070780e0038a140c50103590b0208140035003484204994102c05410000740f50030b070000c0c0004c3c1000249000003400e41d000e0b100391003608000500355049403138500900304120004050a440905032030340070351905000b03c42d0480401c05560301c10141d038890b1b02c0a0041c2c5070f0010389901080350344a5084045038040010441c080c000c017040e18035007545000281d15451261601205404042c003042814810b0100d046610120081e142000b9a100d00c0c14194240900c01627a0380341030380c00151519051350b065000302e03c205004800122815287c0c01880f0450310140036207070108040c140403402500e80f010340140c2c40740000309640106140460140c2540d0041e21000001c01e00255001e84141207030640b00f00f0000c11007000718214549900c0080d99142c0191060b2010440000d0040615214071448082242c0096444440341410601c0e83e0b544c49003140400c1041000c02120f06070503100385410030320500010410541081c3e10301c680740007040c0151 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 43334222 1250 43332972 43333021
    0x507050402030403052206051b071502030703021203061003050a110a032702090112062301050112091718040f0504031101020307080a0b0310060b0c070605090306 71
    0x4000545662a400154402e0313109954072501e40810a081c100504102900c02512124200091000c2c1d5442025150001f070722869460980480c0d02c40703e820000990013154040a06501003104150000020041039200307500b1181506c85142881845000a4a00e107034014129024840500c1c0300360001e54000c2c03491000001d000d9502285030616070302603038440e404a52541c102228882e080748141d2003400e84038a0001d0301803442da00040000b2014004c0b01010b6203d00c0f02c1d078003407048a50103510204c820414081b00c007801c5104100c03452009118550000c0c0c0ca801040c0c214912501034070b45410791082481d207070010540040e180702d400030391004180303480120728460076540740d0040c0c007504000100700246d20704103400c1c01055940c8a120050a40c2c0c010000d024080740e200100c40d6203c2c5c3d40402c000742e4a27108000003802c0c907100442e07c500e81d6042c0007000c18000070031802404810345600403181c9880e59117109640138003544203480d61541084000991034004169560750350150704 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 43335472 1250 43334222 43334233
    0xf080702010e06010806100e06060a050a02120c010504061a0102060604180203060f1f0e13140625030b0901030206130803040b0406030b090105030613060b030d080604050a0c020601030f05 82
    0x2c071503580782030301c01d078480003241e84030300d05008548a2050415019002e003400060851030720790040360061003071001c480c0400400040c4500340d14400d1100a43c00c0700d441c81d0140c2d841c02e1030700750140a4681502e06944040c17501100851840d02e00c18020082d113010b80150806645000401c0001d11b07000542c0c003440944074049400681d400e0000c0b51086941002c441c40a042400c03014040c5441c41d44d4010145e08841414021190200e004a9000440700303500705401109241140c0d07007103888420400940724033424000c2451650900701e44640000348054200700300c00c48100d00740c03030100c09416003010040005201600b0035400801c4086007401d00000404d50303441728a8038651003640081e5810a011506120069241c01460104113046031507114950401d030010b03850311009002d10802c580c10b2101d43c1c040240c1d82e08450260310008068400c80000b46601619155040b240d1030312443c0b07030400140c0307030412501c40c00ea881d0b4503a40c0201800d80c01c50b0303a411138066802605a9403271068 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 43336722 1250 43335472 43335491
    0x50118051b070302010219020309010203040920070f0203060a1b0e0d02060a0804050c040504030f0806010e04051006090906080604020603100e01170d0801081b0105040906031110020304060f08070201 87
    0x306002410703801d03c680e00042e03a0307205c41c40750504a4001d0a42130011504100440e00080c3c3c3d000080d1802d5400720400064009910480c402c802494041c0d110785140000c00c03d2014005c421014101260096080e124075a8a0180a0307084071890070002c0d83d91300c00c100e900b02100d44608400c240c01c0d41c0103090342c0c4002400c6e400003003058010032803100010780e82504000c07c000c0700340306002d010a0140c40074001400c0c9035401400052141c409041007001c414000340345607206090400c070300d00c00900104000e0804002550741c410381c9000c1d4070040b90071643c00041072200e500c03441d401c40ba0624040c21968445500b005400c3e880504078203074229900340003042004048492a000300100c8104801d410f626a0f00700303023003203504005482480701400040040d8080071881c0d1074070000014952a5020403000145c50902494114224044ca00140802041081c02d042c805403101284d00013003d00042c2e4081344e581c4110301803c00022246126401e00c0d50140558a4020f076044c000030030b41a06 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 43337972 1250 43336722 43336771
    0x9090b030102161b0603050705040504050c1303030e0109120c38120c0c0706140706050c0703020705060a0903170f0a02010c08010519170304050a030507090c0305011805 74
    0x43c41000340c980040303a020070981150f4003120103000b000c0601b8207002503d80040040c10038003441c031072640959203035800074a0388a000c1f02102e030130518900540007002e8582c100105445401c1d01880d0200e0209040031940c0b4008003145001a9400401c50403150f00b080600b01c140c81441c1d80019108907011141e98100040d400d1404203940d0490002d62034a03840405582202d8000d4001964842d041000554204d004a550000c0d1441e604001540e04680d1019a12b1b501c035800024003c9441c2c10107001c803407102c40000b0059140240c2c01c6416040d1240104200d82c443c0003490404540546010400501000d4119030a131400f6111681000d50b514151540c9901c01500d01e030050b55203003500008280c125080b80d01514050791079132900702220b20305074030b40c04650240c0b0344042040c0804401003013081046402511014114112065603071500903501d036000c1c010f01d0082428041c1ca400e1043c460300c50070f8102c440081070030f002d90040c80f01c480020180034000320fa40c18884080b1110710302 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 43339222 1250 43337972 43338007
    0x1c05010509010c092916120e0a0506031317070c05100305070203120703090b09060402040e0601080c150417060108060a1b0e040b04020a1706040516110a0203060408072109090b030102 80
    0x40c01f4103840c680c803d82825000b0300c445c8810761843c0c4030300181e410620442d198a8203417507206000007289803001110342410b001c09001800b0107030340524006a654108800b81e1800011140d054a070642d240185040513026100201c0d42200145d10038080c40b84c1811003030007100c0d0000c0301d5040018101d040c50321140001c8204462070801d0340d100d01c0c02c3c0011070506210390034045501d1800f03017080d0b50500804645500c1e9110303d46114500c5c007a150840c524101c011940107000c03814810b00c03c9400128413544a0f00240300d1450980030303142c00101c0c410200c0c0220100384d421001011050441c4040544500c0300c03299035075402c6560340300b85100c0c0d9200e6200130210b0341c8164403120090652403018101c0b17140c0c0141440e0281d8205014030a40b00401008998808c0e5503041c0394600e42041c81c9000c0c80d108041c0f8000c2d5251003100d0a010501503004001c01da42806001c0f82201c0f8407404102402c642c0c00c05d480ca1001941d241c200700206841540002008031004001603e0040b0084418001d074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 43340472 1250 43339222 43339267
    0x9040309030c061e030908040b090a0504020d0615020703030c140319110c010908030a0503090a0606060503060406050904020109030201031a030105090c0315010605070f021c05010509010c0929 84
    0x41ca8101d288075010081301d10030f54403d5480d140502064075950b6488885020341d100700e0304240350120300703031131255500110b01025200c0680219164800e15800340040d0806210341070006000d003d40a0003a440461500e040e00d40640f22031828000950740d00e8014101c2d02a0352080b40410b00c10840b000d144070101c2500c60f074060707449203d881d070940d44460800c41d801c85a581403100402c4100b1a2400220588003070f8069414003980380d944c2c0302d0f041400c2c00000700b40188041d1410b03201040194029003e5402130205580070040b00f070325a028000c5d607400a0350040e0118401e00000c00040d88241c03c5900000f0420b000003489403130b0741c804a420740d00d086d20a0040d6422101c0c00c0311050804020420006828414041c02545815000341c101d10400501602c00b00b010103c960943d01d8042881100306106811206946c0741401c10500800098400345040d5003801d1a43c3c0090344100844401d64084804049121020640c1603110807884091030000c65030500c0700c04203d04140d10a41c040303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 43341722 1250 43340472 43340477
    0x9060f1c0212030a090b0a020f030c06010f090c08060405040602130b190203040f0303050f04050d030309050d020607021906090803070903030806030102160f03030f0f06060806040e060609040309030c06 88
    0x542841003200c5078440d50056003050348280120181e80303a0000030a000c41e46c005466654030b4440000403414083c02d691483c005102c0080c0443d001100051054102c2d04421085005503855044d1401520400d82c9890700003020f8102059891415034801074200703116000041c500b403481040d99030015125032000200c1180815400b1503402c092400d480c182150340b014500e8941070039601c90001c003403400082c04001012603003017101059281158042e060060680341001031070b117002805881550fa0440d5240101c00c0700c074850500000b0010b0154000707130082c003514032481d00c8220401d0820b01c0c050741d1094031070824801044072000194002d241c2039071010815815400d01822242001d06194066031041000c1011000e0303502a842140d9844050311844201c1d509048001d40760b003036400d0100615004c0714164914003a031101c003c450741d130b484070b01c0a0740d5003400704021940031845640311504507000040c2103141a441340c903803051003414100c88450300c0b42c0304c40110307421a0b0085400b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 43342972 1250 43341722 43341769
    0x60525120e010e0901030b0f04030903051207060c030903021009050a0f11031c020d14120a0209040c0201051003060e0a05060f070305010e0402031b030708031305010f05030c04030209060f 82
    0x55a00c4154030f4410714003603e0b0404503506d940d0700c9495406c0d0060403903108401c0b95021038205441100316000854103c012a0b18003900000b0000003039101c05001c9401c1840c0c20352409505000f4010320100ba905500035003002c803106000900036101c01541260580510501600050440d00303083c0911401140310140c00f141840c141440c0c54402201c0c40141ca0001340c620040d158000313095040708540d80740111100900405880d114004d00f003038810311801c02010040709000d40d5000e4198a0011101440151242c030310036422100705480080074040f158074140b010278031640003010000114402c0300e030005a01d4030361a0900c0c0e825540191400040001d0007038a0740e06008580c0580b103000071710740d5941440d40c0083d5a41214122100d0519840c9a00107915901400300c04010607016081d2580c603082c214009560b1400d6020740c9003c654540350020309684075038240c2e4480c0d80e85060443c900350030354003000f20020008044540c4800c0c10904600c807a11003200d5072180b5040ea80d852103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 43344222 1250 43342972 43342997
    0xa0909120302031503120901090807080a0206070f0204090f0201080a1103041106040506030c07020306011a071b181413030f0806030106180f061403070905090304080303090f07090606052512 83
    0x509e51318841e80b1070002c55100203018014010046031400846a0445450b580d0702e0103031510110003451140041d51152074048010309020800301d8040078240b0076a200c2c6080d60f110031000045036184000008225028000035002802000721040440b000070013060070240c0d035600280e0194070031203a80000c3c400100e200811400e00300b0040d03001d0b20641489044041e8041e079007048a006401e1702401e070007605502c4400310400550000098141c00140221040c88040020050b01d00346881e9160424154006004445440c45002c181c945c16602c1820902c5211030403607082c000500416070656075400f0001d426140d0407a0700030b020310110404140000301e20794100445556034000c800c80d1401107084850303581c0102e06042510644c1c1d0700050a40c840c2811a4070718000c5800c1502c086c4400000d0101d00c031000201070302d4440203007040324880c0d0348556004060712011300c112008510203026900d451194a060744806040c0100070105901c41e645500803d85000710b54540861480890355 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 43345328 1106 43344222 43344227
    0x807031509021f0203180306060603010303050309011e0b090f0411040e0703020405040f02030f0703020d06050619060909060b030f01060c170c0c0a0909120302031503120901 76
    0x1214000d20b402c1004c1c1d130b242d0102c801909a040400803241c407502d030000303540d80b181101034600c07800c50b441c0d80d5081c0c8840e040030b003440300a035403180060100d03140803031481403d0956000000c40d80c90704a9042c094020006071170507000640da4020000400c4031101034401080003034800040c11190a040b45082c8000c5410080d4024140410302040c00f8000502d114014021415900741d1402c0d1513800d503541d030031440f0003508101d20140b6030010034500e0f440340b03034040380103051307442040c14910841c0f04c141c0c615001440030407420780741480040c050744160006446401c10140c0303076050840503120310b071405110b26810001070141c48003c21030752550b024640c200024020303032141c40840d58541c444d42d000c103640c0c0c02846007030b100103214221401070a40f0b150b04402c8003908600035013000c070b001c0c1d440200303100b540b00340344006410180c508101100e40d18042c4034038552241d000d070000 = true := by decide +kernel

theorem cover : BRFrame.Cov 43165472 43345328 := by
  have h0 := BRFrame.cov_init 43165472
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 43165472 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 43165472 ≤ n) (h2 : n < 43345328) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
