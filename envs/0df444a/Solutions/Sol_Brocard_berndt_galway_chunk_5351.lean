-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5351
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:34:48.326634+00:00
-- url     : https://prove2.me/submissions/c948b735-53cb-412c-810e-e4f86c4a5bab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 962230215 ≤ n < 962410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 962231465 1250 962230215 962230273
    0x2040815090d03090501060e280509070905060f0918060108071203300618230a061a0901020118050309010e03070e1302031c08011a0c1e0708 62
    0x4d04c0c02d2424000c0035800f04000d410f6580d1540200c3c1002c98003000070090b03020024481c03451490300c80b551960280107643c05400d0b0030004003021801c007484071026241c01407090780c02024040603502d40d070b07031107205050003927041c05021980e040d000c1c940c2e1418178005800001c92035206010801c0701d52040218900079907010320f000e00144002e00b046440b01403400f0303c04001880940c41021030021341f80c2c0b0000880303400c4030b02c4402400e45540d40e4015a0203a10040380290107200d03200317404c0c555100c0c400364090101c540000e022521480707080141c060110008020350000301701c1c8501940c091207000e60315982c40e4220004645560b40b8150341340b060300c1c0f200e41089100040071004e91002c1200c1405004062a04491481c0000c442c0f5130700f001e4150260f01c24416440031281e0169420003040402c10b2540e12014140c0c00c02200e940c00c0307142c610398003030440401c100e8040d00b81414041c0000c0c02c000092104554400700100c00e1070b2060302e420a01003500800b0705110b24062441d910040c0ca414 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 962232715 1250 962231465 962231471
    0x30e070e040507140423070f090302030d0c240903270b0a05090d05060a0b1f0c0c1d010519080a06110f0301030b1009020a0203030a0902121002040815090d03 69
    0x200c0004540034103185808204800b040c0031146c090300001d00c0f01d05204d001d0656600d600c6258000d01110a40020310001e5003640101c0c5036510600e01c00d11312100404d0241c0320718000c00380c1c11840c026040c0040301c4001219035a9814034010150b000d00340303a038950020f0041e610365104829130260011500d2042e060200d20004480e50481d026070242d4507134180040560b980e6a4440c20318a44400c0111141c07a40b8502d0141c8001d094900140500f6a42c40e04007082d003401800e0200a4441d41c06240b070540e16124894000129940b591001d0b1518079218203200c0d85035450301080c0400d42c00010284e04400c01300503428444503a000900c6580c0b603801110105490200400e0000785129041c403040708060000000300510100440d414000c468140358511850b03640e204820480c0074107103103400160010004980004080d030408581b00340000e0107800007040d25280030b07241941e910006020705030042010085080244459000001d15003410f01d03140c50100426030b20381c0c101d04103070828155 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 962233965 1250 962232715 962232749
    0x603060f040515060f0c060a0908040e04030c060c020307021003050717042102061b0301050d110a2301110c01083907050c030a320d030e070e040507 65
    0xc40740e4150401540003134419681c3d1410007000d035000750311003140080d191240c100404c1280352036124524410381c00c0004c240c02c040c201058910401c4000e4801e9081006400c2120086400c0340f040e889170000a800650792020a032044c48849541c5075580f00500d4034207400c00116540103240450040e0050101070800d40e038a14268146003d00804000201b4404840039812900000d049028445801c003242042c1030881c0c440c9001c0c402401160b0700505260307019000070307400c0c0009482c00e2070000c180009082d11071400d4005125801c00c14041450599202c0002d941c209084030040c1b442c08000c3c2100c000d80074000390018034081c03ea01d211020066145001c030b0b0010540d0081020f00b03110031010f02410403400c44140d0003907401070720380b0300810f0104031480c900040d02210b0b4a60246130701503410700c0c0c0e06014180000582c04001c1d6160103400140d004d5205101c82d09003a4501e8900185a003078100d1000e1070b040e401d40207410000080030500000c510000780706d0048408901150103106 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 962235215 1250 962233965 962233981
    0x121c0504231608010c171005010c030201020c0a030906030b0312030f1f060504030b15012c22050612100f1404150c031505060702190b0a08060603060f0405 68
    0x100b8101c031650021580000124014106400000200200307a64604a000740d0701030030118071900ba5221a800c1600e02d204102c694014446225414000e00005060203d161201410031004c0401200040d1905005200f2250907100b00303030a52000740c00a01d40d60103081c49200b0740b840701800180c0b1100913140001c14012000a122815100d407200c040e041c144d81d01c2c005031254205010032a09240038000203820050700d022840182c1805965149400800500500c0d1000301c0c02114120301000c04025401030f25041c03549401c104c20100051200c0c080c0c0f82d2104100c0300060318680c803d5604040c500e1000300005001b00703480340766110001d0f8505003070304004000c12a207450303010b1040c001c40c100b00c20305c1610911510b4040400e103040c040c00d8611a800c03411a00e21401c001c0c0010b82c801c409101c1802d0510261480303910240444480a06500354074410f8580e40d0b100700d08010001918149403039004000c680c0042003900c80c0b50450410b82d001840046004100500480c2d0700c400007a418 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 962236465 1250 962235215 962235223
    0x20c030a0f02190807090c050705150703112221080d0f0c1101060e06061c0e1c030b01030603080f0a0c0611130f0806041b0305121c050423 61
    0x10380d000851460710580c1e1803241381d8440302d16220350f504039480d1400c00e4807401d000d0422514200c1d848006442151240040c6500d001005000b00703040541e1000c61255941421000303141d00d1041403c000301c25880200b2030010007400c1c1d0000031001c80c2c05194031741c24243c20780149403007507448154241c441c081440c1200052058103444120b0b00c0c200041c003400e042d0400312903030340020b80c0c4000780a055114981d0030542d030000c0d550650030100030403c07000c0b2090344101c41c1c4801c01c0c09490204d08980c1e4042d0706864405d8540210800f40845107255215942502c10364456507400e0038144030306071541e00e5425003409018200c0c40c3d9040005a8140c3e485c0c0f28030540d1035207a620110400c040680e00180c02c040f03400c0b1100c400c0075106030300c00c08590ac0a5403c0c2e0102150382c0040240000c0e0b896036651244450512000c0d0518000c0300741c0840081c006000d2a80200b0784881d580e9151000c11072030002204601442c144002d26003420700001c52407034040d01144040b100104c121140911503000d00d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 962237715 1250 962236465 962236489
    0x60b121902030406020301060e030c0a121e0b0916180218030106060504090e1c0309050a0b0c0703120219050309030f0319111335070e07020c030a0f02 66
    0xc4188004104000c10002c1e90285041c2c0b0050b5481c031a550000f00107251b82d0701e9401680036404031010800304076031082e0348513020980d4440c1d4582d02c0400244000c101158400a400f11061080b9500b040b0f1060410004111450490b10201041c01e2402d21181441010040c0c040900c41c0c0001e039005006140c4035940b81d0070b010150007000400e6807901c000f0401c0d0402d000345110316042034032102c00e4a500260843d07e1600f00400300c1480003941209900030320302404111507034040c00364501e01044030850124400d10303545078000c1d80c402041c60003c02d8141c10141c0104003510500c0098801001000b4400c0c00d2419030400e582e032622501140392450103500414241d011f000800c008480400c1246001405102d2109016030030041a10594078014041900603160b50301104200c0d48403124002103000315942c07490030032840050441c80c1c0500564100c078800303520445041010350705a841c41a03100d04144007030034100950a00098a0303034100800a03006412010314517080d907645040c0e03000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 962238965 1250 962237715 962237761
    0x4120302040b0313020a0b31031713060903080910051c02040504200313030504120609170405010906050309070f0303111216140c0910050a09060b12 65
    0x3480e483c11310500d940d41c0a00e02c00485c010200b940000034031750202c0041e60413a040980810030404422415030b40310008000d1000104104501c0000104141d042c803685070340d2550264654800a0b0074441e000d401055200d4002c1010b00d03c07003000410808000d98500000c1101c002061040001046455001c2c070b5480e40e025008024028120b0440c3d0f80c02082144ca09450038000080405505506e04082c1400281540c804100240c00d0211030035107000b201e072003428181c0c201070315140081220a100c140448800d60354112407018440d0300e07104503010400e5411154075141c02c0c000020041c1080b0300c2100140304010002c58600c01040c000c0344040c024944000000343e0743d030704008151170181c0200c89054021401d000d078844501d202281c0110044c051103212024859860000e000e02c0e0303243c650003600602844102681c0c805800134024611000d00c400b45034103050808c82c0300b102a500c100d40052030303d00100b107403403001070a640501520075078854856607400c452450b000c441d071040c21 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 962240215 1250 962238965 962238967
    0x501050d0e0706020a03020715020c060c0a0807060906050a06230103090b0f0f070503070e0904030c1a090705122d031c0b030102070515070e09241804120302040b 71
    0x705406130b0009078001442c1c00b9608030b90210759295107036484006150b0a440c0140c0040382e11645500303103039001782800002e45d012202d0300d28258641d0807064001c958101c80c96510f43d480e41080c0005400780f1364211041d04010000b29181161000540e0a144128814280024007485460b8026400a0b4030113410030103240b0b480ca0231901d09141003000311461200048442c0108400b141304000b0342e8410459601e42c128002503c1003003140e807000c020f208804000d00d103160240050180c02681c10407031010150350003633040003080c1034107101d01c5810150280c441d203807060141440004994030030348a207200e20700c02c8107544e00e90a03240301f10401042d02c0502c03001030666076103081280180c00d0740c0b10880041204c000c031102014246c1c482c50710040d0603507000c01d00c2440c0280003c4003140d0000100d092070342000b01f00401060500340202d400149440d00f0a02000307420b4048035402142010468044500c440c5e9880c0d0780001c1c1d24081d102a000340d08000c41007101a0180d030440b80a009105009 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 962241465 1250 962240215 962240219
    0xc0601030b0907030c1508070212040317091c030f0f14090102010b1002210f071202030c010f1509050c07060509391f080417070b1b040e010501050d0e07 67
    0x10240d401c51b00c0816000180790741c800502850320224643c401402c3e00d4440398030345444c548640c1c54200f88100c072480004800c200000a0359162842c1031902c02840142900e0313040c1d24240582904000c80d814400c0c8031601c545156104d60100001c158007440f851001d4841c0f400e00d004038014903010b000f481c7c100962103580940300e40c000404081d2481c103030001b40782c14030001000201e180102510b91145103070a001d40300000d07008075985d403e05031036441220b00f070540c080b02031030035103c0759030518282a95a00780c8100e42d54250b104a400707001011410f0050313050402251050707200d400d2010b80510b5403480840d2520000348038840340881641c004100403408224001644040c032081d00e0f403050030083c244412810010000300c05950b031500c01480303034085a8010b0b6003507600100107c9104480c1c0c003801ca07101480501400655000d1070184500e440c00d03800f02030707420600c2a001ca041440c1484200824051414418156071080c0390079621903049a0320f80000e080364144c102c1d40d0740542040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 962242715 1250 962241465 962241479
    0x7120f052512020108070302180603132f13060f15030b01030b060a0c050a0203030304120212041202130209040603111305061f0c080a0305041202030c0601030b0907030c 74
    0x14100e1096101c440150002d5666442c2c2810380d4040c58003d0100c1c600f10001000207000b9406082884490005a1740000c106000034165038803c0320101507203900c16130380740148808100035001222925242c5000c00d11030750200014004183c401500c607149140b010012200307140c0207040100f83e004141c2d117241d51250b00035440041c0151f94180020f05e001d4803110365610901400a80d200c01600d100c1c0f030822800400c403145c2c005183c09569a1103408441c00042c1c4040004501c5180200ca000e0038415102c0c40c000d051440b4405c219102075414031047c00100ea0303000701c0712461581141d11210300369501c540007000e802240307107903a802880c0c07e200000b84018902c0040d0548c000300c0e8404143c00d4003400c2c981c101d4106071f07901c17a0014103a6100a401c641503200e02c004c0c4401c039040c80001642c1540c1c65070b41a0784810070b0f500000352503405210820a540080914201881c00594140341e039590312181d507020140310242115041c03030081004520140014030103540c100c0c0700362102c19140c1c0d00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 962243965 1250 962242715 962242753
    0xf04090c0b0310230d02060a14030f040b010e0709140a180f05060103061a0901021504032105092a1c0b06030111030408091807020604020a08010b0307120f05 69
    0x11440c1d0382600410261520501080039030f00300510000c091700100003050b000d000b5540c00581d4103d041c820b04c401f83c060109207160295109a0f8041d19000c103d1900345030034100c032032069109416000c1c40318144620150050105025030395092128161f5086c00c400149103410320394001c2c1c21054000d00ca0401503041030f00250030a6800c0c0b041480f450311190700440403030300c00b8031a404600d40301c1d50350744000326100f5005000000c0c0510407036901526a000c0954160810f03501280030070345501080d000003c6050401d02080320300f0904015a20b841c0614688402c84584d5600070601403403000c030707240c14101c04200050340c0c02603c0340ca0401c141000c001e00c40000c0a4080d502041030000040e0107140501504101d0f170504800d441c1180c841d9520242d040c3c201241040c1d2000c041c041d803d0701d9902d00b605140c880c01d101d0740101901d00306030040c000d0001c1c4039041503c144c1d043c20014192510300003841c100326204600c500f0a11840da0400800304a5091801403441c02010001c0907602220f007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 962245215 1250 962243965 962243969
    0xc0631030819020d0e151602041409101a0f030709020f041403070f030201080a29010314070e100309080a0203030912130b1b0d03050a0e0c0f04090c0b0310 68
    0x5001c841d0702002454003502c9070850f00da19103a1194206111202d081c1c0f140e07010b0441c4814071107e00e00f000009600050a884c1c2c91440321010980b00c100300044500300308014840c0e03043d0094100140d241e001c1c602c40c000000d40c40031078014040031140c200c07142c400700480401003081135411916600b801c4e030020000d900070f109882c8600840040002c2500d0046040c1c0100c2d440030034a28407440c51540151540d88008008a503501d40d1401c841e090b210b03206c0074010b100075100c40b820f01d04041d01800076044403075102e00e003800000440104110320782c0250b6103200380b01c021511a4012084c0d403100b1800b40c01c804800804009001c60710101c045c0e00040910b02661220301682c0c201000d031864a0414010a004140c402c20403000400441c991a0010f00d4074624012400e40c840c044664100d290221418003040000c1d81c503c10030104094910452031980a00400382040c0d41071440019101c08014070f44a20681e0303940d00890030428810001740c0140028030380d05451f40b60600b00500303401114 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 962246465 1250 962245215 962245217
    0x201111515060f0a030c0207031205071205191d13150e07090504020d0906051609050303040503060423060c0913110703030e07050a090204080c0631030819 68
    0x105052000b0310b0b00c90181d54800c400901043e041000203941140500041089041540107000003c400f0420301c0c0c03004418007030240c035041d60741d44040c034028030781c500e0018010041210510110862120808140541203010702d4490003038100b91000170144000120410340c0b01c071820000d103511600c02e41001103a00060783c43e0100e510303940c00d000c1c0100ca008030740600024060540c00c5c04503203404d501414500020520000d600c0c3c1c0556170754021100300b5540101d03d01001809982800c3c0c0c0180d42c103000e0481900a0f6003003a107814046590b4100c007070001010340740000310880780c87d460b840700451120440380c12109030f8180f101c03840000da8000690359004411242c5007407071000550007002c0700342400034040703840c1850b141c03030480062040030040e50f8103010300f40380011f29075104403c040c090114107900590310707807404201c5850404801212406140705004000d641001105030264100100342418042d600e12441380c0110031080c0c00040a00801190902100c0d02d0403610700d80500c12 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 962247715 1250 962246465 962246491
    0xb0604050601080c04031412040303080f06100c0201030f15030b160315060e0a0b03090705030106050405010807050d0507090c08180f0c060d060b0c0c011e0909050402011115 76
    0x120700044440c01d80c125130f0341220400030402080003580c050080c0041c0400d44003074039803070410f400c00380186500c1640b0540000c2d40c034038240510b02b18080201d90700060121010b402c004a14031010303081c00e4142d20064141552508407109800721600301126042d011122131440b03507200d19114100010a507062a4443c0c0b1240142e0f61b0325004e840342c98a80c070100c1d8001d040161400c041241c10320303d091411608250300f20070020701019070b500a50b0040d80303000f010b400264200790600d40ac56055a1005106604000c010000c0300800700f41441600c030155080d10b16182181032480c030b000f80c03590141c01340915003040d006000394090030250040700c0f501014242c142d440e40b04c0070b503a8404094038100c141c02c045000c81c181e1911400038440c2e109420408240d190741e91060010a0704214000c25142d0410747c000d1011750781c02020003024108020301c20301041c400c903000402c0c41d520b50207200d464568840218081d68010f501108001c51208115400d03441d00d503500702042c2609844900108107 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 962248965 1250 962247715 962247721
    0x13060b1c0204080303010e060d1505092a040b060f0703090315021e18030111041a040e0103080a03020f0a031d010c050304081818010f060c1a04050709090b060405 71
    0xc16000b02c40031981600002c60460742002d064400035003001d00543e91049035030303e07904009080d00520142421509500046a1800304249400c1c5840d010306c1c181d1055a844d202140000d5403d007604bc8100140c80004480c0f0718200400c415201d2071502c00180040410308100301584206901c003680d115402d401c021020303204404c0c0583c0258411800003503100907400103c080c200c3c02600d4a18010344d2103400e00e086d10004282102c0c1905a201d1134508002400d00078010715101850040070b2030a000c03460726143c000359550054060000510442d0000742e08031060780f01e5016990031055001d2400d95440d01920b000d0028845980c0e00c000c520b0b440f50f40c142c900030f41841a42c0c4001c5168456a15569072555444096884208007804103048514048680e0b296901910f56521503e032508140c1e5040c401d016500c02d000c0c1d440707203080154428a4100292800820814145440803451190346036407038401d0410001e40c011040482c900241d803014010320032959400b41c0b1303042e41c04210307540b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 962250215 1250 962248965 962249017
    0x3020f07090e100207080d2a0306140d020901180912020a06060f0b0901080c07080408030714010c09060f03061707170703021c05151e10150e13060b 65
    0x3c0210100503201c2001404401520035058008450384c400b41d040d18504d042d8412208423849840c40d1300100066519103061100341c1489031028084942220220f41207429070340002e500c500d0500403440620100320f0b145a1400e0541c0054040a900101196455a42680c02540c800f25480b0603228a800c05c031001408401008090301507030000d080492030403020f0401554281c034080d18043c0c41807410000000820369074406000540030010107590358802d1402c1c05100949405000c26903a45071404001403140c105600008403926804c0010f0360b014504019002007403140d01001d07038010b10305078030023020030082440400d6880030588191002c8030711002554900c01400001d4010403101c550300d181c4581c5111540e4194070642c116501481c041094a003013580c2559813445060112404030f022070035a02c00f9541c481c07030405071158168640707a4402ca2481000000f8414443c20402204080e00ea44040032100ca101d00000d0090954079004885d041d440705042520211203607800c0780e040c1c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 962251465 1250 962250215 962250217
    0x90c1c0b03151906061416020d0606051e0108070305060303090415062a02010e1f0513140f130e15091e0a02060a05120a0e0d0e031903020f07090e1002 66
    0x50f441c50340d200c0321111b0301403009a045502488015042c905202c02c00d4005030b035070300c2080c1b141030320851012445a150070b0a005144031a00701c8000c5482502d413403d020340c0d900c40c0321030782c1c811361078030f4085101e448020119040d4400d40050a400a05050703101044400c0c01c0170000c11282146d40308550320031015041500c83d400d143c40080080c80d2034001e2809980308480f0300640035401401101219000341d08800e03100754070020a008504041102401002c44030300d44001846041c9041c040070701c81d81c00150741032844200c030301c0c07299840d50309042c2007050320360202c40c4106042003100ca03a2824040420900102111042e1040c800c903928521210044c0641090b5005084014008902264208035103908241010800c0143c00e219084440e005a100071740200e003110350029078840c02e0810a424100741c8664801030001c0b001c40740403a0707280058a581c62046080002400202030320327049050095a0441381c8040c0705105d07000c03508508a90040d440130000204035400c3c204007081c0719040e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 962252715 1250 962251465 962251469
    0xa030b1507050703150e0601140f04020301260705120f0601150c0305031f15020c030c01120504050c0409030512130b0703180507060518090c1c0b03151906 68
    0x607030064101080016280c045d41100c000e864880860079500e103c040764648a401d03480b00c015048c552045c0b00d620706081e00e40507845041030381c00703500e5981818002c04100c0c2020502a9029581c03074440f840100051080001801d401002803103403980f060300c016a101d440034542d40035401007100000341d000c082c0082c500541c045032107010000409450654840d00014505a1120510551703040e8a440c800070740d1014050755000f0010a40601100900e072610100003a4000e901c0030b603846080ea07800c00c1d440305294511100c040b64554444c0740031818040c10f01d803001c0c2c1040c100608041050b8000024081350201061000e07443d6a81e83c0000c1650454600043e0840e419039012071801032180c1c200c40d040004614010b4000380300307592054070f860400d03400100050350200710300b14203540c00d40040c16414030485400505040c01c0802c00424030415030203550118511503e80040d515582014141800003070030b6501143e00c052103001d2620046810b40b03685106000c0800c110100c0c0d01c54002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 962253965 1250 962252715 962252723
    0x3091a0714210c03281503080d0c0f02060a090f05150118140c030403030b030f100e010615030203040515010b030411010804052802061308160308030f04170a030b1507 73
    0xe001c1450380a40300000b1400c516240740b13901c0e1650001d80341c15201651001f588200c0e100e41c0c0d190701d05040c4404441000000004015445d10303850509680041c00c140c01c0b10381800c001441031610718200c0c03c034070294000101180242444c103c09004844400d50480c1c407442e01e817011500121500e0343c00c5a00610340d032802c4995410204520010745c601075076202d48281070001e910f082910009103403080182d0f11114540c00100940ca402080e030080d41e098450400080c451a401c281e042001902c0d90108502019400300004007440001c00c00901c5140d061564070120396140d245058165000b100c00340c03400054203c040e43c80d5417041d01001e21440e00080a0008510041074101540000340918121503405c4000c480140e95003200900c409952030441500e51443c03c80d54900704403840302d200f07045540c0e07100200046082101121ba0000200011030041c0c0d403a49000e9050724565600c24441c26008590320b40c0b4142c260344090a00c180803030b850003001860700446002d40c4a03002d0018 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 962255215 1250 962253965 962253991
    0x60b0d0f0305030408070609050c0406051008010b130e0c0a0f0c0818061c090b070c1502220806150f0f060c0109020d0b0f060103091a0714210c03 64
    0x340109105601464100e480380d85200d01d4114240c581c03c0690f48045801d41c0e581d00f00c10f6905070a45014403074000140303010745400020f151500f4010f09030207014030490440003000a0050802c1e941e03540024060840341c02c6031281e03030402004100c4aa00300324041e03008102405003200200d405412011041c681c440d02c001e2426901d1410107060041685907580c0242081c04130400c00c03107004c1150001980d05010005043e01c25051034040500094040410301400c4a040c20120750740000e01c58008203043d01c0135a491040720074200d03501a95449084001080c80004500c0c10303408103555000303c1043c00c441d0f60007002c0c1010441c604d480c0003545e40d4040384146401e1140c0c05c20802815260315010000602203407182c011818056060904407070080c1000100702c0315030802e100751034125100380b070b003003180000c0c0d0360b1076111038010580585914000000020303402c034452814802000e080105094441e40400b19002c41c91003030810446031034040000041850001006a0b4401d60ba400c10030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 962256465 1250 962255215 962255243
    0x60509090d1821030c1203021e0705030304030c05070b0f1809220c0b280f0c06090503070f030503090f120d15080a0302060106030b01020604051b190e04060b0d 70
    0x2842e69003810b45000c50911071401c5c0184007185c0d2115412404065076100940d0316070000840b00701c0e411240740404200c040900011000c00c00000a40c0c1d401a03143c1400c041c0384000b81050752522200b40c2c0500d4010400154036490465000d000c0c20103209441080d03020310308004208604030b4001c4851440e0511181c0000714020a20291384980c507016921b414401502c90003501c0321a4002008051146036201b20742000c901c0c18040c040d820906460683c400303d00c800d600a12400f266100a801d071070300c46032894140b2000744100c1701c1a40d0701c510351f01c3d1714050924000d4195002210408942c0c01f80d42d000d903400080101d1800700c181b003901340c40c900c1c002000b403807070000304803050050946059041c0003240444080100e08101c40c06034000301100c1d81350400040a8502d1680d54a04540004003404005040019104000ca50903004502100c141c50f01113540c07100b01d000407107600c254899002030070b4919010a24003980c001d0380144110300e521401c0c04501000c088000300000b03544400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 962257715 1250 962256465 962256509
    0x1701090b01020a17090909030a080108060708040209100b030a0902030717060a180c060809010b0103141812160203070614120702011d16080105070905060d060509090d18 74
    0x2a00303030384804e441005003000b030004082410210110b546190547c000a0300c1b50380d0ba50000031403030041000000070b024a241c40750f0011324907000904024000c00444001c120005460703800030014103000d0109175141d10f045800c040103040b400780306a0184c0110600441c48030001c5800c1a0200022401442d29845e00010300c802020030200c03220100214080081c00181c0f41c844002c01030a190b920120b035410801c803aa821100c8011040f8189464030440c400401080d43c600d070b07171003002014403200d15030701a100b03c0c0c100110040b102030291400900350a0000d94030101d1101e850080c0c00700e4040b1600c4103402c1e145c20503003189121042c142030241d03016215070b00d094117920000500c00824000c0740680c2542e40010b051822140369086000c1c00006146141000001021100024070581c1000300e00501518a1406464056540080c9010b40c26070181c012000420000c0c2078800e86140809030310340c9801c4034644600004904401e012100b0091a48000a858112140101d03400384280 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 962258965 1250 962257715 962257733
    0x2031f05030a03270605030907050618060306150409020705060f102601050a020408010c1e260a1b090303211409010b03190b1f08010c1701090b01020a 66
    0x3204c0c00403041c4440300c0c60000000c92500101007940f40d6640380e080500a16040c581d0030303048940200d00500001d10145410b01d42e41c2c241c0c0d1407d03560181d583e00d03840007080b0848000402003111396800500020300d0115503000300b00060144095500c02c0d20780140041d44c0860070344450541840740d54003400500d0880703018849286c1041c01c6040b40001620742c803825101d08035030003914076a01003070802081d80300780075403074401000f40341280250405160920304021045448001c01603107111518a0007502e1440d440c5141401451540618040010501030100944c00b28205c0185c0b100958001d40a0003150f420b8943c9926044041700b902070501c500b521141c401c0181301502c904081c8207508152001c20b001d1411070f0000b14100c8044d200781441d040c40c14003010403081d007100d6079102240c140840250442108040104004610b01d421241c0040d140c02104942d4070301615040190707041a145505505002e5000185a0b6100e500d10b0440d50000180360144c0c00405031070f40003c0c1914 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 962260215 1250 962258965 962258987
    0xb01020a050f0105040c2c13060207080d060506070804031e06022a150a0b0d05250b090d021221030906180d050a020c0d0602031f05030a03 61
    0x220440312480416254146095540c041645103a503441c818007060003544085903010f42805010745038881c02050644014401c1d0380592500d1640200100e020b0303540d500300a01c2140e40015056413644e00b5420300c000e01d98071503640d104815152405c00903982c00c003d07003075070101a0082c58042c103252660703d0f02d4101c4002c030b001141d415410b0803c24400540903102911840c0527188400d0f01c1d030000c054031044145000b407201881c50307020306501d0740a003552150b01e6901030300002d0040707805003080700420049240228014058020040d00c10340e2002c00122016980000051251805549128190151040880b20343c0c000036090f40c0d510246c10240d004210740c10400741120550305045003141c0c8241c1030f403001c160b0103110020900c816404e08200064018020184a484a502c41c41c030082d03a0b0380d4007403c41c10501030041a92500ea6000b40100d881c0210090108a641942890503000950048503400f4050000940d80c150f1001404040003d07144040c000b07003180c560b1614182c410f04954 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 962261465 1250 962260215 962260217
    0x3100e03040f03080304020406170c21030a051c14060603100510030905120c060127020d0603021207060f14040503010c02150a0506060d09050c04150f080303010b0702040b01 76
    0x20440000c81d4a4102c0c200070041d402200c0c1c1d00d840b81058410841583c04a90010249100e03030004402c00300004200d000b50140100d8402d550b0542000144418401040e00c0e40c1aa000108090301415040401043d05402941c1594142008105182c00326030f10141780c900003404a800040640c10850010751300890000b090484650b91040054282e0050303404250009488100030010440100040081501061900c908042166203442c0e60f6070014452104e40400441071a00c0c800120010b103901c400071680e0a5644600104552024081c1d911049000d03042164600786a9107000c41c19100340d440300e41d111402c004010800b15000c0180340f01081c0b0310f98040000060566091088028079445500688851f0b0860103590b8603580f0f005250aa002d810003041040c1c5994110807220001815907002811450a0401e140750601c80b551254201d03162441e158240920500008115481c00480c1c140040c1c646a003540c1b00d0100b8459000303c81c0042c041030b0b0061500f5040041c1c08401 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 962262715 1250 962261465 962261467
    0x20607020f0d2d02010b0a0b0c10020913020c0d0908030a12050711011e06150c0f0c0e040b01030b0a0605010c020d0204091704030203010b060c0a0212250e0603060603100e03 76
    0x40d4440f48001800c0701d02c0380025030340d00c0030300007100c2c10a0b9000d94010074460003030303500f0300120f03080700754075890b02c0084041e00e0383c2c0c0040d070341d4196901c81c1e1185208001c07088c001c6448211702c0c8400d43e90b909034003000c0c0003c5060b0010000300e904d0008100c2c0d09083d856a516541010b110100c0070240c90b01805900612584440101c42c20f2003d02c640329001040c045100b07624041100d10200b168415046a00c00f0b40503042101140ea81061b02031402e164080940a412a070500702044007550507042040b80b04141c20501c400d114120385c0340c0341600e001e168070b0101750f01c800d2011001c85c0d0140c402c590201d404800604054038203500790301800c40c005000400d600280340d6403008a2803204503ca8a244008034050096041c244519104103d0a0351724a24059482c0f94181e5248a0028000e1240b003a000b20448021814030010440043c2100c4090508802e403141850495050185500c4400504001107191400054480c0101c030f001d00940041c40810f80d003400030b840e291b40d801d252848 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 962263965 1250 962262715 962262767
    0x5070905060d021804060806040807021915030c0305070c020d050a050d0906021005060a0b071a2707060504121a190506040908160302012406020607020f0d 68
    0x316a4020402607054800041c4d0741c00c10000f0700c042440500b1581c0380107030302d805014400d1442c0055455049900410303036a4440d01e20f440001c14008401c440c05005214064000404140c1c0c0780d1aa44004500c0e2014001d07196810421822110304503480700000c1c60001008001d41400191001103074000e000381c0703009501c07079164940350901e20004880010003549080103401c0d41803140510301500c009040c0014180840015900041802860042980069a03400704401910244c150071022010401f461070014000014246420300381c501c4046866403010410b0804a141419907109407a400e003018204581440012142441244c0d001c1e000840e104a00003650783c0184a0156080008e00c28140e004c0240155480500074500880c1011003610004004201b50740b000005605841214081030a049000d04040c000355120f001c108550103440c0c090807610501079071003e808039445074480380012a42c0b03040408c0b515402c0d800c018404071059105101c2903124010b5542c80300303900c00d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 962265215 1250 962263965 962263969
    0xa090c050d0608060907090c02060a05130209010602070518010e0c070203030d091104060e070207060513090513050c01140f03040609022e0203040602070e100f14041d0c0405070905 79
    0x10310765044409a40d10104c00c000002808020640242144140903c5224003004c8040d541d0000a031400415544540010b19256080708030441c28a03002442c9003201d50b500c4a002e500c03103509000d12409020803034a1144c1d640c00307400d049812201c1043c00c00704565903142030003a20740c0050100b2a0b150104000e8038109000601071212101e019103003001401c0f03000c40070001215030303d50220184040308400c0110807500410304404a03840c904001d030781c80b5400b002c0c4252403810354020b0030b00c95140405000d0700e1004104003005030f40c4503000320b0341303c01ba266006440b0140b207842d0302d14024034200110f10f00322101c4001365030040e12500e40814400182e500082402a140d407094125000a070355450914894280e2007440c03100d140080d614007414894000d40f14202401401081c1800b0307008a00000c0c802003a240003403800c1912400903136145d00140d800788604507802807007035050060403075040c0d150391000b802441d1084000d0010003c09d20031b00029100040040082c05110040041c7d55 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 962266465 1250 962265215 962265221
    0x1b0521040810050906460e030d060806041707060b0a03030c03080a050606040303080c0c07120b1012060b0f150403031107060c140c0607110108060f0a090c050d 70
    0x1e0410030340302107600d20380f031810b00c0e10b0217030014251582c480c841c415400c508109040809000c1c03074610f401c2c64100790020100700000c1490001101d129190010603031210502001801c1c2d23803884101c0c01e2160136940c81c6075030390f00e140130b940141c208a14034845900310044500241200c2d846400e0108000c0401400222a11942d50050f8041250f140d40c440400d43c0c0403910550040704800700300b082c1e04189011910900403030000500b0721200802107440700744000d095641400e002e1040b100540d849280303c41030200000403c9695400d1080403a0316204600c0a27001070307901401c800540701c205601d40c0c00c050a41c40f905150407904641d4903045c076481da000c081c9400780e070040b0602e59031441c4bc40d0060450140500c40d40d4641c000760b20902119500114440c9400c2e088001002294142c01040e81032046040303456610030000a07a40b010042c1c0001e1b24a040a4240c81c1c03907200307596090500840c03914074082c4552202c00030505010140d004d500c031030384a6060785400b50510320204559421 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 962267715 1250 962266465 962266483
    0x7020d1814120106031a060112090803060d03020a0f21080108100f0b19080f01020903030313020a0b0c0114090606132c010b0a1e060f0c120f1b05210408 67
    0x5600300d50341c00c07c805960026a2580c1400307210394100540b020f20744810005000c05020f0074402c021807030045040c036100f00700d651401c0784c01c04042d43e000310552030102180d2561041c2c064001800d0750b5051101070040308a03d04907020500134262240441944000400010f50390440b02a81c1c0c0c0c00001c903980350180b419402e00c01d03c03000400c409042507074031b03454001008202400ca030b0042042e444242c9012054a4000120b464001c0e045000303440000d112084580018040304000308109580800540102203400349036001d040d00c90310b91020407521010110b0f026900310009041c18890040242e200d804040001c0c0c040b040c10081c900100741560000007001c01c0030fa91242d85824603480e1801100700100f078240c0d0003c940141d1ba5442c00c944006070322566046c41074140d41074040724010003a6094040c0c0c40b02e0b034076004141116028101c48403101500d00002c03126400251500d100300d00d5029003540101c010040b83c8010400041c408100002c0745025050038040001c07821810084112 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 962268965 1250 962267715 962267753
    0x306020c010c0e06180f0402070803070e0a210b0a02040f060c050c0105160609050a0f060c02071505120603010e01090f060c05090603010506030a0b0907020d181412010603 75
    0x4040c41c2c1044020201001240031601c1075030100310f0010803d840c1c1a0301404071509460f880003004200000400034002c4100190001a000040010711544051010b0002208440c08980c00d0f072580210300c89442c0050140829040d51a05000816013a064040c2e0101041c1405803819458801c070b801c17440d030103900550201c5c0d071a21040d0304100061000c0c0c00c07104820f02e0300703a080000d101c50401080d030b03a4283c09000180d40d91003c4041c00360030300842d440d007900940c1c076100405c0c81f071400100902810110700010b000b080404207a48003003920740300d080c5134103030381d55410114615170280c50040080e0086a15658600c812600100203002d08402c00d4054010440c2c41411818000d0a58800014240404c0010460081982e5600041c0e034191a01524103a40320703507410910308003e11448000507801246841001146940041ea159512000742c1d1341d00748811003910f026110fa035450045103101c524810510900f41030148102c90702100c0100081460307a500e442e03525600b012011a14 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 962270215 1250 962268965 962268971
    0x110315121b0103051e06060706022511092815080d020d050a0914030102120c030601120b060306151b0c100c1115070b010801090203010b01081302190306020c01 70
    0x101e074543c3c040c401c5030340c0f0020716040c04030401c40000c981c4400490080c05984101c0e0080307410790920a0760707815a06c040d141c441146840b4209010300f45614070300c140d0101c442c002252500a440e003480012180070781005c0c9004006028010f54210445141400e00d03542d0a54602a403851107440828241c01088004058a9040b500c2b000007070900296107072030b10922504104516460b0351043c41c030412a00c0c00d0111461900e8040300290180c0f08070705a5000d0116400140000422150011400342c5000d03201d543c8024000340400c010b4500390592207038080400d000040c401d08084848400042c1e82031102c5150242c5030000e5038142d0014454504158480e408244a030700300301e0885469071078581015098030b61699100b0500540c030300501c500031407140400e1071a03403032020b00341c501e607a07400400441d03690b843e900b8180c001c001032102a032107582821080d0126500410f081750103140b640d0b9030761010845d25001d02c00095440c400540460a1090001003c61041d10290641c401000008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 962271465 1250 962270215 962270263
    0x15050c2a15010e0106030c110d090f090b1305040c05060712170405031902071706090601090e0d0c15020a02010c11010e0309010c0203190503040f0911031512 69
    0x901e14100008180004215000c001403000039403800000f41103c84525021502e100c018100f291005980d46210b0114441d280644451540201c00281510402c03000382045070342d2100c84c1d20640c2c0c015440ca0307400c4880d00095002e007181540146500500441409802da59a030010400d1640541c0c415684500c059030010b21085e8448036850342d461101c92000d5907410710340c0781e0903240c0c4242c0d40915445044056401c0348240203204107001460201080000d807600399040d651110340803a01d540090040348004144030b04a0700c41c513600b1002140c000e00d180291040c0944068000030429682c440d6007050700c4c601ca115030b000400e01d11419600204003c03040142c040c10700c01e0050b0480401b81d061844c2c2c40810600001640c054101c01d18080b0008151400881c0c24401c2103010041003a02c8070784440e041c030030000010011601e0030360000406aa552820030210760200c01d08040c200d030200041800b1003890355600401c0340d0010094100c2940a001c05807608941384a400c801c91001c040d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 962272715 1250 962271465 962271547
    0x3091008040b06010903080f130b03070f12060f0e091908042603030703090c0e070302190e030a11011b03360308071a090c0a1215050c 59
    0x80c40b500143d081c24070010081c159521440036019810200c200540040b0b52180c2c842e1710801040c0051880d80b09503a6281003000d00100000307042e40244000c1406070003814001c0a05100340070840d4110100c9440007420030244412046010b0701440841c4207640300303903011034040c0b44150300f035601c200011991145005a804040bca482d215a0034940c0c0d02c424009104c0804030840f43e201c4003a00e00040e041959140032195445260031805a8450085c20441050703007550003007004001d0710300803000d031110241c42110f911002c040060780507002401c0f6140012246914400b040c0814100283c9203220f0748048004400380c440250005030711581803c00000c11400d00f00429801d0440002962642d01c12000280a071031000600b8907000182400c103001c400301450300c200d0042c140700c61039820a901c0c03696079030b4134070b00d0550b100748050080001c41e00c10030f582c16100c00364400c03d8003c40c41d00100da440300406004008945c0c80300208415110000c0710209120442c00c0391150403045018144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 962273965 1250 962272715 962272733
    0x102030702070e060f010c080904020403080c070306241a0f07060b090711151f150f0503150411190206150418110105090d080304030f0201021305120309100804 70
    0x13840d80200200e01d0a10310590303100391007800141d0800c0c401c03075440300e848010030020704c40c070b50001e01210001714050b4048080410144c0849000300020b0005001004c00b00728503010312802d0342c1c458041d400c41002003c2d9911002580040c0241680341003c000903500500c0e0703808540108e50742542e4580b00007161070a000f23002e800400a16000c042c100203042155a218100350003c543e028403900001c0c0c01690300c2101500345908051110301b56036840c0718034040d4134400d100300303c04540d00306100b030f0b0701920910603603125018885100740c099a0f070344c013440010480d040d0045004c9008202800c1051310714141400c922440d58010415403814400007007480007900c3d000e91269003010100b494003100c02c162218600d4005186c03c0d00e9a26000c0183d800b88034440659030403141c00588001030188042c05148181c1c040c0c0c840e2242e03d20500802c908034820540081c8115100c1d803818401800d0100890013162220070803a8500803006002504480d0a07448040012320340381d013088100010a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 962275215 1250 962273965 962273971
    0x30a0b1905091f1a06041512090827042c03160b07030b130912022d0703050313081b01080a0e19060f06050a0e06061b0102030702070e 59
    0x6002e0030580384005101501c515100f0b00c080101621402d40c4401c0c124a1025000135a400070702c1142e8442c2d41d18442d03d5001c540b250050003080340e030307080c8a6004180d4010103003426070140c3d00914091241c03810290f54401d5003121406125401c0c0e0300001c9464030300c40d85186c020b0b003005040000250751403070b10541c00c05a4000d46680c10920900c200c40b505c050011701e400b54807020f03070703011603880c101304900038107084081c141e00040d00001450503e48030760080c801b50b0300a800b040803035110100140d07a03941c6543c00c290100301209429040020b8040c3c40360b896408940244c840340f50343c1c0d4450710b246420803410690004541c0f40200040c80f010040b82100c1001c1841c2d04c501000c040c00060302441008042c00b00c01e645a1034a1403503403405201290b04519076118944c00303414107040090041810b0302c2d6500c0300c545000408102890000c0c0ca0104a684143c5001e06e035949610501000c0d40110b2613403074410040d41d03000680c00ca002e0021303621400042d4010600d01c0c1c43d12000e500d8103031020f = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 962276465 1250 962275215 962275231
    0x1e110d09030b0103080a0525030f1704020418020607050d091e0e070903050f070f0504060f1a0c06130c0e062d030106091401090c1706030a0b1905 64
    0x112804000084000c1e041c5030450f900140117545a011300c0d5402c0d6054032031403030b840c842013084188890341040c0101c1021581d5010369184104621a007906449116004142881682e07900c0001801450150060100c0c28505821100c07a051075030f02081c0242c210a008452682150140f400481da10001d241d004200644894016800018040c42a2210750080c1c2c2c48401890300054600d90142210720004c550000440b0302040f8440980341d2650010300402958800e94140000e092a107802442c1c2500c21420700352003805e190007802401c11140c90f04c2c403e44d00b0010300280549103000d00050b489119180130301c603c203003107910b080c000400e21740d0440c0008039905030074001c50751608030045036034054141d03005c0340464140080c00b15000c0c94140990b4550700b4241d020561038169000b0108240141600702c0c044d98840c00e00d01c041d070b811b110860000030352643d00d100c203d80750b03e052075030001805030944001140c1074889820046044a40c245200e41210402601040c1842000d502c2a06 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 962277715 1250 962276465 962276477
    0x51f09121701060c2f1e10030f06050315040302010506042c01060803030c070212120901082a18090403021c020f010f140a0207170a1e110d 61
    0x3807880c4003140468107000d44010040d81020b507904102d2984014040b0809440d909a24001c01540c2602c01a1101030310303a002d1402255080c088501701483e00b002d506009002c00c0c21103d034660b00324000d00044000d40c50740e035118600010326480038000005e6094500c0b0f1012100e26143c10041d0a59201601c0300c0e0042c3c0c64000300301980300c480c80d014400700d40000c080e80c1003022a03481e442c1c01340400d90000c44482c040001400f100d2049000204940c5100f038414001c0220492038807a00d0310219003801c1d441c1d0314100300070741b80d03984500e156684c80041d01030005480c40181c00c03103000924950a82003103070310700021103d21032264028580c0102004495107a8180b800d90384c02506c49545440d42c0440f60f50a065991010b03009106440d81c001119008000c0d058440c24510090006951500e84240351100883c10041a0f07000300c840040d0441c40b42c3d1180458641c00300c0b42c903408110300f00c0c10824503c5801b051003030305510701505060310381c0c4c2d501d0049444007040d505055261500c02c1c03d100c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 962278965 1250 962277715 962277737
    0xf0402090114040b0414070f050f0306090c0c01060303080a11181c1a060a08120a12091a0f01090207030c060b0109050307092301060e0904051f0912 65
    0x80c44500403030644048108a02000b030104011401828022101c142e01900b0f00442c13400003407400d204948100c4042d550031280548948040d40c0701d00c03507008840c028800801c0061100d00700140c88940102201c2d002030f1038480341c03403450303400c54a0981013100000d0751a000d0001c4030301640134011400802125403850580040c50368030248a1500f503080c0201004609048151407150354002100d42080000c0100610014850b220400480b20a882405400804260300500003103000700040c80812052600301c2564040d520300c070160420f0040107841d04015000180540401191000d21800b0b0705405e080141c081c0c1e036041016001030704c0e524418814200802e42c46860400f2032070300040006040e1078010012079a080305500400d405118004002550b110307654400034190003900b451a0300d24885204520100500b031042c400000e031f403000c80034a01e20f0030101403908140301d182140c2159005000c00c0d0a1080d40b0307041d040700e82e0fa40729001028811161441070002a09150980e660b203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 962280215 1250 962278965 962278969
    0x8060f1f050d090b0a0f020a090b031003060f02070614070e01050306150301031a0112030918150803040f38040803073f050f090d030302040e0f0402 65
    0xc8920306110000100c90040944814021011114502d503180420301001c01c5a0070f018050000079035251100901c1c0c2a070501404000c2d2099902c0300e0002c7d958901c4031031501403080803070b400c0648002e190a140907000800140b55109240007401c0144001d40c0b00e00e11030506204484064a1840c3c0030b8940c40c040181190340f1404c5121040c0c02400c0498403a121000030501d0807850515401d9150300000c0044148640128501e00810203040c0811160382c0754000024070f180c0c00c60700200030410321a010b01140c1030380038810b0301002030000000f803403009810b00000324a8803644054080d4200280c28898034414204503000382c00c071000030084a01200b000540c50022911595950403000f03850081d541004900b12001042c140b81200d80340c072204d041106d4100c0b0078021104000c9244503c02611001c8614440d0702418000c440d00ea045003465000ea45030fa00046c1000c000010401840310300d80ea500c42d009050078001d030f4006032a113044c2600c20201100250a410212a40a04100c016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 962281465 1250 962280215 962280229
    0x60b06041215050906070c050c0603070201051915050d05010209030105010b040602010e0c090c0906070804030b0604051311091008250609030c090b010e1305060f0f0a0e07110f0d08060f 81
    0x41b142c500784441e1b0400342031090a0080c1d001c0041d51040001040c80700c02c541c1508440d01902c0c0781c4c0155100c049420b82c1d44002c42e4101c1c1c509100d1782070000c00c01c10030b914000e10404003207801070b400580360a29000000b0708483c401d80280480c04400308081c403196a0902c40e125080e544140100308038414080010704110004144101c29500041d00e5202c0e1780360340c0103503000943d0020a564861b92070b0303d016034010400322011030145103403000207102a44030030000b4445e2034012490f41c0b424840c09061200d090340045c0400120743c0d444500241c0c1020810031403035050b01c82100740702940c030034900344500d80d9074581c000810800b03815400c3c40494440cbd408072044800308080001d81003404401170f148000710700d000592019241c540c415280301d003504014401c0388202c41d541c0c0288991402c21020144100f00c0d036810640c0c00205011b51008000c440390044440d08105600c0d00d407040d9151319003c1d41030010015074004c1e070341c100903280d00300e00c003e50004001c644003102074241c44c1c003140b08 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 962282715 1250 962281465 962281471
    0x305091018080306210322030305070b040606081203101502070e070e040501030501020d0605040c050f0309030f071208010f0e0703020d24140922060b06041215050906 73
    0x42c0032000000c10525940c1d81d0303c1c882c196803003840c0c2009500540046644139004420360b90750a0031703181600908007541d190450300340ca5054891a007400e406440d26034121344001d00445000f540d0b50f501050540d81001802000000ca2a0140d0780341780403440081c60308242d0f0f01c16458110080445c2c0415500881c0b030030159208040c00d0055550385070401c03030741c003002440c0c04d50700b00786004008030920906400074000c01003e540103200d096502c81c2844102c03801c108001000610510034821440351400003150021040001c6078144006104584031551018000310340c00c0c95000d00c48444140c01044960050403004c4100e05164900000b070910b900d00100303d14109980000d20307400754049540030080000441e4102c13140000c0ba41c010801808a9015006d00001c210340d01344030904e06941842d00c58911101480443c01c603000041d030200003c008100c0e03111340c840c00440540e469000c00b900040c03282010160111815051400c0b001c4007414140d05142c2c146010080036503000038006030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 962283965 1250 962282715 962282723
    0x8040209072606030115140d080d1104080601090c120903020a0f060e0c040605031009050a080f070212030901080103030f0219050c0f0307120f0206040b0a0305091018 73
    0x80306035a10103007101c1c9203955038001840342642c504964010307030510355800d204000c154000c0125031600d000440c5803180b284552104c1a1120300072000342e040245811500c14407844c2414100b100385003405060300ca80d01036100d02103201040800402d0b1b001c1000c03900402e000c0b2010800305141400042c21824541c00b40601c154440c4030300d004251003007141c0780700c1e950409a0000700300114540300020340040d07178440708213120b0401c072403110340b619104860403904c0040040c40360381c040c15251005000100310954543c050b024040380415022002000c80c4880e2205256503088540b042148030351802000442c2a80103001c0200e050360000c08050640b6018200680e01c20080ca400303d01d0841d00001003105c3e04041201d040c100140020720721000381089501807085402c06040c1540c42509200342003c0300c10303d500c1c840c04034403001074903c685400582428503040c2c50b049a0700c00c50b40701001ca0b400180d56042042034185080c81400b045c011092428070031201843c802880c00555400c0c050 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 962285215 1250 962283965 962283979
    0xc0318080906070c05040507110f0c0d0215040e090f01050f0c1e04170a140c03100209040615081501050f0a08130c060c050d0816030504050c04020c0706110607080402 73
    0x70084c0201e62410400070725004200b031000307141c03010b40201880110040c1c10f01c4e0b03204610800c008040d012401944000c40074006035041c010035002c0000c3c1c01c0c0900c044802c080b83c1000049035548a451800d0322922400e40200100d03030107880c2a5084030030042c104600c0d02035000500044401702402c64200072800a507241c0311110b109500600e500c03880d442000341c4103600c105005500070102e0b4400c0c00ca0b0049045120345441400010741300c0413003a104035890381094480ca1100b1850340c5c05001c01441c0074000181d82d035111002c001d6502c00451484002c0f80e02d51040041c0010040b140701c001503800c1c41c2c01424101081002002c80c050360602806020b00f22000610b12603106040340340042e0407140c7c15425640e03400c0090074034000b803482652240640141c5100241c051440d980c0295178801070f038600b5900343c04c4103c00608014004507182c1c001c820f10085591350f035001030441c141038040900002850024041c2c03088020014a00140c0c00107410072051030b40011710b06610076019203440c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 962286465 1250 962285215 962285227
    0x80a18060903081b0303012318060904030314010b0d0c020c0f0d0f0b011d130c0509060613091b0e181e0115120218130603150c0318080906 61
    0x2208130001300c081c0c0200988000320000804c22851b00300781c1125983d00d4400c01b06c00b401030060009420b4180c81c0d442a074018000823918a00745590560f62060203440c00003210007c4a608031051071003a40710342c03520320380400c40010b80e221511800c035105840d400208540d00300b10000c0b070241405540d21500c141075003480c0409005a0304401c0401d140d01c8103071003810350703100e4800d03854889410400400c40c0900d4000101d003078a071000340c1c015154105980c0000c8501e050b04001d200e14004184580000d41403010070700c102400781c01c3e84050030313010f54007056817181003103284500d20901d150398081080d0b00d801041e482d09d8000011b0f02c035043c210400d006564a540c51b00100c01449407040c0806440900005220100000a0300c0e40d44c0c2c803031f941c86258810004c1c0c080309900540e10403072000d400d45a007103007680c64819900d0007000128100410840c1e52610741c075513484500d08920303640c191542c10807800b4950501c904140e240d80c8644800c003642a54a03030100c01d0003640d52040c0603450004807 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 962287715 1250 962286465 962286487
    0x9030e060a0302220e0105010203130302060901030902041d0f0c090109020a140a051306091805061306080a05190803070e0f0604060e01080c09010f051312080a1806090308 75
    0x4444190b00c43c0300c0d84c50311205400c64410090301d000d12840020080b0880007164540c8040100d402c520030901160b03100c82d0442d002c000040c4c2c001e032011414182c1d21342d00c04005840701e0064440d4212550320107202060040101414082aa0008042c5030804841800c03595585425941526040080141ca451012900b40c03600344041042546046c00850786400305580500140300d20302c0e10340101000d290f5595410f8407803d40e64065090f00c020714000c1c07108583c0d01d03544070a030f00c520001c146424415461050304112211a0420602d0742c000500c5c0c00d091090800c0315072090103482c1014041d00d8035503114038015020141921040214244e0a20742558942d01111798421009045ca5034540e660900a00303200c1e10b20700082d02107441500050b42e401c07100821b0307595445060311070700c030b248044640031100d075400a1003400c5002965607001c80e0510ba041e814007a81072288104680c2d541c000e0030b000d003030901180004225502d9040741030050a0707001054000301c90b031000c0a40c1d210903105003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 962288965 1250 962287715 962287717
    0x9090a031211040b04060e01030501060c0f030c06060f080105090607022505100e19050913060e0304090603140303011208030601111b010e01020115060e03071a07020a0909030e060a0302 81
    0x503400d582d2a40204011502000e180001c00444d030032502c07034805507851400107500317660f4240329040116001c058600e0104424201c1540720320710a00d041c640c000c1250f034404040311002e0b006000d140f090041c040c0b000d00c1d03003403140c00d8200c20000b00030302a82c0340180c0000d5403109400d000c004465200c4542d00756204108885070b0203028001c3c020a1202c2d2244001050515030b0b40002c2e2180d100704111030500c42180300d000054440c003401c0c0c200a030380c85c8080d420491000d9002280c81e1691081d4680c010442807001d8005814500c2001c10218a14201003030710310a2540c080165800400040044082010300b900c14154054421a01c0e9a1400c00580d01d11480580f806104c1c000e180000010035001d94019100711402d80301d21200002c1e00c0012401c80300d01200d41c00710011094002d00071031307009541c620b080400050889100726161500c0500e01c201201e45083c1161020400e4811840c04003200c5000d0300c1c6d8610100404182030301c004001c0340210740618000e800000b00c0c2e0710000d01c6a0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 962290215 1250 962288965 962288981
    0x121005011142151c15020f070804080106030203070f0b0703031d01240b040b0301170f0a050a0c0e090c10030b1903020307360f05011202030c09090a0312 67
    0x10040300a9803920500600160f09548a02c2c0d1180d9403001850b01203030981c07504c8030032807074010160708001c200c003414600003548070940d10094404180168030000d860840104045d000140021030343d6403852042c985002540e821043e110120020b0511118040000396003442c1d03011700d00480d0483d4603218051202c41c07900b4980312294201600d40205020303508400040380c1410388030b400300540d50700000c0d031280628001c002050004000402a0108608003035a0840d80c5800741c0300309240f44030109181251541d421186500712a40050600440c200c265004244a000440c3c9a261440c403260700c8041d104001c5c1e11030b52010200c0b04c5801d05c254030041a03008090103044014002c0c17a83e0010321006444224807902c6200d00200d442020302508425202c1030201d40d00d01408880c1c41490a07410060203100804e40d0741d010f030908a0940e0107107500074121051840c0304000580140f41c1403510400080d0301401d030907001d100103028005601843c143c0c16150114000052400050182c2891 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 962291465 1250 962290215 962290333
    0x7050f06120604091a06010801080f1b121e070b04060f03020a0c0c060504090506240f0d110d0b01140d0b06090306040303021b0c090604050c1210050111 67
    0x10401741e807240c020922296000300c00c00d07213550006a9941700d540d5514030760180740000b1034025140c1c054500840c1c03401c0c08805140184032504003180c0448040c070300300d07030300a00c3d00984142c04a080c03203c680038082c44020380340c0d02c1c1510b40361904142c1c001e85821841c0c00c1c5241010340c0015a0421140324800074001d082e400000f002100fa40d50000500503005400740030246441d02c0040f580e00d00c1d028070b40f00700d103190160070040809890110711509401c000300746809840200200c400d50760191066a0b810303105a41208d45a1400545810072102d0302c03650035040c0700e400503034034510022000990704222140d003404118000110003264480c0a010180b03501845000c040c4001c02d41c1540280c032400e243d4611920f80725482c0445185d8601c01003d01d242c000c0b00d0b540c0400d80e07030305107504a2944520710400d0300b80b40c005208d424448275001201c50300644d4101c0b607000e012940e80b046c0070203007013200c59000307000050000003585200d0a40510861241541e4030784481089040340070720b03040801d0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 962292715 1250 962291465 962291483
    0x180103030503160509191a16120c140d0f031e02091302040b041703030103030509010804020d0210020f370501141003060510080a0f2a0807050f0612060409 68
    0x40d07080405041020740121002d1030f00407c0e82c160005408400d88120360b03803041540740740c0e03241501c400546040e00044002007140700090f4101048803c921420562046c2c0000c00403014400001050400c03c0040d140070141020790300c170752042000d100c0100000d419540141d4030302211340060040b00c0c0b1031381200f05a50001c20000782c0709540201400031110100281016161228201030722803009000007804603009102003c100c2d44100b11240d070003803000d0440c400007a0a600060042c0804502c0707d001680911443e840c4401c003840140c8804401d95100d5a1600003d510442441980b050b091041d1100c907690801380b0209410803501c0c005400a05400380c24030004080b80c422190105446072801c100c04a440008403940312022104400060000c4210382d54a0100186000c50213a41b0075072080e10a00c10301501e140c0410003d400203042c0d0454a14100c001800c10005501103880f03a1045504a070701d988038101106c3c11142418219820b03a03403030b10001401000554000703448030300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 962293965 1250 962292715 962292739
    0x20103051914190e1506130501030609020f0109060f080433060b04140103090c1502011d010506030a0b04051609291c0305040e04050c180103030503160509 68
    0x40050010b8000c8010b032400c0790003035480c043d5000030b4421041005542e1713400000003420f51002038050036000702004000043c4908000e840320107441d800e800598059907a011100308602e807503100300100300c1d0b080c01c100050515016001e0f000f0580d02c900741c82449091000601040350341000c001d40100700c01010b64445882030807100004188045000a141c0303040c8000c500c2080c11416075080351145203550410303e80c1c42c0e0045003e045a40c034111034842c4440070201d044110710030320344400b4031207130b00010700241c0c44000c01c460320b00055818083c1e0303450502070224540340460700c1c11916410900e14081c2c0e80310b030724005141c070704800b20310340324260205008680c00c0e089030441c61084c0c810541c000d00c030b1024809904101e4109400b10703a41704000c19001d03014115004004100b10f03009080690400740d07901960440d5000445040316940c20000000105240049541414032110041e29030309605503034002c0c01510029080301c001106200a0300d0a0510034400c40b00301e1003010b4002c200341c103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 962295215 1250 962293965 962293991
    0x24206100507050f0601090902090703140109020a02030c0601090b0f09040804030227010b070b090607090302100509030a0c030512030114041d10060305010b0301020703090b0a02030702120d0f1b0201030519 90
    0x230585501c00ca102c5d140d060b01040b0010b00c41c0c01000130049060700c0c40c024592802c54400c000394044580c040c1940414440f407950560240082070080240704004a0346684540410800704594a03400c1d2280d10b0304401d00010a04480981f010380b03505a40c4040354580007031445501a070174050b403150b00c003a1031002140c40d80b41031014040580c0b04035991030181e1501c4440300d031980c0702154180c000400980703042015141604103182c42100504145242a0700c1c040840c0c18940d40e450306803080720105004004020003080f0000c0302c00c0701e002030182554101030010a40001a2640301e1082e41c80c1c2c00c440805600c100350303100071081d2200c00c44054440744011000600340b0352200350b51070b500c1d101c10403140d418103008880c0010b078581d8512001d2418101c2008c41c07500700d0160181144028003844006882e24000640c840c0701c00c0000700710001c4e54a034000c004800d00d410040800c080f01492040100b00e5001c0c01d5010383d42420301140e142d6412a21410600032112540303550741c1050101141c030307 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 962296465 1250 962295215 962295221
    0x50403020a0303020705010e0406030b060d0309091811060304030813051504110a1406091207090e0312060402040b1c24060311030105090103080307024206100507050f060109 76
    0x81b1030030f03220000083c032460208011030706144006030600c0c900c03000041c601e1810320b4880100603c01d051070403206032603500c2e60701151003a007017101d0b1a9012101d008148841500595202082200d510303107180303000e56009004d50030107020340c400300d91049207102c101700e81408600782e524500c241010503403800f4140041010402205580140d0115001040b21901c0d403e030050890005040c403813030b000965052041411a8070f4080840380a01d5102240d00c0f07455005807004d619100000b1600d0319040b4405003c1c10801030301c01446548104010810a01e00c007040d0380d03103078101c089812450031121101d4006400c102030600c010000d1403003201020f500e00c48011060721100d5808001440407000103a80302d1100703005041c0d00140303600041001850490040d90312022038810344116845e09070240d611040c040b92040d01c0c4020600b8041900484c01b4800301022110806845403030400d4400b08610394030320b80d6400d0810030006889001d00ca803c11400b0b4005006c0e9080383c04642c0e41d400702c6d60003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 962297715 1250 962296465 962296469
    0x140c0d030f181e110405040f0c0b181c05101b0c050a060513080f1c05070f0e0a1802130803030c03061c060507020606030f030408100c050403020a03030207 68
    0x510708441224620000c99462400c242c0c00401e041e040b081e45104424030f5402110300710751880c0f0500d4201e1071510ba600031980128442c3e01c0f403c6108845152106040c034582c2c1100f0000e0b481440030f06d038442024041c02c3c17801036080d262201e06e4039400030480c1c40506002805012449034904031020f0b00d549501500e40a0a1480c40d503004158612080b40c0211000b4009401c952100c038112003c18465886143c01c4100281d150b00190031550b66140079421050070546540d40c081414802e810b03285901c200b070003810306420402c0e4038002030003405c00e58220b5120010002d07003c0c203800e89600c2d400c00d4072001d080b258500103100801d429054000e035101012152903001440b0002640b4000003040c2c0e03000e02c4080d61365500396074441080c058950004040e210104002b480700401003100f0348500345c007882280d806000545004801d06103802c042d5040c803009a88200401c1101c60400b02da8000da54003185800300c3c441c500a14101c90b640569040a580400300f2040001019000150941 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 962298965 1250 962297715 962297741
    0x1a0c010c0f030e030c06150a1203170604110313060e01060f03140102091e03190b0a0e2a0628021b0d06050702120406030c08090a030f140c0d03 63
    0x303d0b002003640c0d15140d00400d40e02c444140d0042010400518422080154411010340b0056146903105d450150401300313840d007030300031030115104000365001030000d01d42d00c40002e45003480020001c1503d0005444010b019410115a040d44441040020380090360407560b5400240030050b2640c2078010b401910340f1040700c0c80141c414000d4500001070007595200301d0000c203820180c2c1201009988aa4042c0400d95414040d80c030040400114810401c0981c0b0300501c503408451030482011400c960041000303912135402158100e84544800702400c1b00400c0ea0210041e00c1022034020031018029044203c0d40001c138114100300106504001080110303999003119030304035550854054180b40c148d04190064202002c001c0070031003c0c0c20064100d205032040b81c03d058180402420a600140c01c00800292503c0d54a05883d600010060b00300c49a00c003d454104825030300030385620800d5030600b05100340c1400c0e18120301007023002c2d02ea610340b8850954203130952801005000303145100e4882 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 962300215 1250 962298965 962298971
    0x60305012310050303030610030e0a060515010e1c23061605030106020d050a020a2f060c060105150c16092403200d0b0708060303131a0c010c0f03 64
    0x8542c1000e8050410072140042d0103035180d0785801003070025035860f4000e8841030588543e2911859201046110b213403502804c0001524184411040349084c0c4080c0c202e41003000c10780310600d03030703568903803006d00310444044041e00c03460500e103024105080c101070501203200034980e004590171000b183c614407035910103c07454400011200295003900082c000e01006034481c5c144140b25900600081100b000075004a960701c04143d583c4080d14440480c0480002160362120380000c506c0301150491444101c0f070480c106002d4203481c903070354041403044070b2103417192208049210b802801111011171021041da0041d19048643c40604510707481021211480c00074000319180141c4c2d2014283c9840d0a00e401403c1c2c61512980358620038085214040f8100356074591003079607007240100c0f10074400c45059541d40340804c1d000e494000024942030280d0000c10142c44540100d1965100782c1e244402c940c0b19005910500300020300070030f0005002c0e58a00201100b49075082112591403100550b014 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 962301465 1250 962300215 962300221
    0x906020d0b011103032d100e060402070b0408031e09070305061e0432070f05010c17032511060a0c09182301090e0303010302010504180603050123 64
    0x440305040d0348148140f241d001480400d002d046849003c00819003020401c1003030b1007a081c0e084d024182d0554038542d13900502841040104000d010040d48101d04507011420a42755803180100d072080244000c203800d00000002d0850b882c0c001049107206403800e2416528586854102d54450460100380d5503031154000050f02c01002041c003030785051040e1818002500c0d555100881421607107616109200403075100701c1c09200012401a0a050800c010006589401c2402b00b0032036490304028104444030664002086003002d03c0c83d0f00d0803a61008640c1e036515801c40b6100b401c00e184030205054113002840c103406d13078401e0b81500120007010907284244c440d6955101100c1c451403505000c034007000010090401040e40c46002e0b019000d1011903115031841e500e0a804e603180324031809881c00d2a0041c00701341e90345e1003082c03501d01542c00214038550550300041c0980c000d80c443c01b040001095906c0e000d180040d00040c005661000c02441550401804d80300811100401c59203150251000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 962302715 1250 962301465 962301467
    0x1050d0c050a021b0a0522112d070312092405100f060c0c0e010e0403020613030813020607020405010902190c21120e030c0d090f030809120d05180d020a060e130906020d0b01 76
    0x7a03e6038501c100d815103403a006090b6005c1c1d07010102300c000100960f65812448010405005100040503000c0a0030803050700814040b90444001811014303032101c01030814800c01e0b41c1014640140c2c1e40e10305200001d01e502d4541680c0d45503582c0c009002c140b04401c0000b800b91166036a45000c1ca100c2d800b038894680d0b640d0030303900d440c1450b070b040a070006050704042005400078280d03c00901d070015042d41d1030200319801140c141e9000ba409411140c2e40001c4d420501446141c170440104003c2c0b80024400005880300c00c40352a40c0c2c05000820100c10740810203072070043c0c24410f0074040c2c0d16418007000400c001d855850703030483c039074030440342c01055151113180340316003d50001d4448400c400c00055046840d04c0855400411500da001158205065000041007280f51046403c681e1b445030750341d602000140000c801c281c4c109014040040e02500141d8407015100c0c00c7d00c00724035000c102d21020354009504000320541000c1e040e46402a08005d00202d90002e000340011100184401100000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 962303965 1250 962302715 962302777
    0x1b030a030c1d090f09070506070515070c080f031918060b010e06160303020c070e06010207062a06061a030105041b05030103080901050d0c050a021b0a052211 69
    0x10100d507003c5072240014078081d000c0b008a94000c0150707000c032081c007034480f408522541d01030081a2150b0307210741919080b1001c3c0d20420741d4060b102d40b13000f501e49100340d0348420f158042e01d040400c1c10600407000032411a56102c0501c4001d40c000000d014600001c417030741c1e0302422210f0b0103852042c20300b684200107500901031b907071807000d001e40064500305442506154140345042c0841c10184c081295512500c01000548040d040b62101340c3e000f03041240003e450100d1704d504c0313482032048004a042d440c03440b092011705a0b00c1c043c84120450300017850000d0081215411400080f81c581850000001d044e01c0594165103040e201004242c94401c1c0031814a178403550148000740c2c00b0030052001980c0c01003d0300000c401814180c1c103010112903080300340c60500c80c2d4003000860100c5d0321019a079040004d0340140040c4406420391811340c20120f20015114000c0e2070240d11080c080d940801a45100220031039611401001107170011991003009038006000d03e90b038030300c1d82d400030192085610 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 962305215 1250 962303965 962304017
    0xa02060f0a030e1b0f040207020a080601060206011a09010c030e100e120307051f150315050709080705011b06061517060a050111030c010c1e0c080304081b030a030c 72
    0x1c0e10813004000040108401e0110802c0700d26006602844103e0050b02c0c0c21200c04050000300300506965810000020703d4500164030010058010000300340d01c2c4030729101166441002031a100002c01c4840c03d041c0c90305200c1040407038120007861650344409505c1a0400d00c40c1100702c0c0e01e8a01d5540c02c01c107041d5030f4010554054a0b640080b00d030142c00381c8034200e8411350051414000300c0c00c445840003030941c40307001d948207a4800702c2003001e80c940c6004502c40c055001900303003050710546040130030b51503a8032003a015460610000c48000c0100310007992200041d43c0d4000b1040c0103030394850340e04000c804160740c410408038149a00000b40030940416513841004050034402260380743c58011510108000e034034910030f00040008003001075082c003848481c000241c036655000c902c59804642800d440321400c00c104054032040307a0009500d40304494126810109964503403070710402091282c507417071010a2051000040d290003050301038001303598003101e03500c8144554020008285c6048451 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 962306465 1250 962305215 962305243
    0x11a0c07141507050c13020c120904090209090f160b030a0c0c150c0917060103021306050901030f0201081005030c01030e010b130209040b10120c020a02060f0a030e 72
    0x320300a020711090381404000310314000b8418400e0054940c000b040990261005032916000003000442c5810b290100c01d0040d80d2900c1e04620300302c906d44a1a444401a01c620303c0c2c2854000740310f100c0b079600c9812114007260000c08004250034640751541d0f07209400103403070040d80143ca942400ea011251440e004903441c1d00410340c0707941c1e0f4001140b002481418044003e00c40d001c04400007207840d101ca46074070250a02400904c0b0382d001c8401800d0304c1030741d500111407810100000e40481c20003044050460b541a522070040418007079002024054980000390065a00070000084c00420100e03072442e1030003a2142c2d203041d1180c95000c1e4a0b00c4550250b01c0e0513a1040340300c04019403103541702c1500c01040d04c00014400c510701c4000b80188105403190340c00b240e008143d45e45249861301c6004e205076400c50b03003490340300885000a007084c200c600001c3c4040341e0f2158141300090003400b5078041d070399006100940d20030001e0010f42480e0401c0414100191a051118031964000640c0d9941e01e104 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 962307715 1250 962306465 962306473
    0x1e0e01140102070306051308031f0b18130f0c02100506031b0906041b0c110307050a06140d0c050703110106181e09050a1403120a0207030c02090906011a0c 68
    0x299103c0d10050180600302000b41101c20403a040418003c80113580640c01000d0641d4041c4d401040e451030010b4280c21042c5c18035000c2050cc0c41031031641d04141c514502c20380b0080994034017901c0300030040c1040c01d09100d045062851524880d03074007042e55118403090100820442d1950014907030303107681c140700c0b842c41a0b0303c03519a001c0c9880d00c98081c59006200030004960f600002c07081c4054500f008085902040316103d141e41003050301c0d203541a00043c10340062a042e807a040008000e80c68a10075401480340c1c02c1100e00142a200b4129120354000d205e0900c40740580450040c159400030b50142c002480e18550440d000d18180150002c0b0f404026000050706000380d0078000921240018054045103403030700b0400507900c1c0c01800020750183c80500503150050402001c0101c0e0300e1b0920125400410002001c01402c840003a00000840700050b00c0e0384643c58143d03070106000b80007940c460152810400c24060001e0314905031075000b4400c816440744100000b505000c0c405c911103181d00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 962308965 1250 962307715 962307719
    0x8040507060801081e012301080c090408030c1b070b0702040f090515130f0b18070b030a021327060605090d02090702191b050a0506221e0e0114010207 66
    0x1c0b545251020148060b400003d12502c000c048206281c414090142004860030040140c10002d0ac50700245032025541460b051800340e4803110070b031100405a01d07400034085560b07500c0c4020500140c81e4800b800048401c2151101c0080d580ca404c2014203c0c0b15600386207030910700f980240100c2d999554000001c01c3c400f50004404858450001c2c000e030094165801ca0901082e0b1848484400d2030055450108a0034a4803000300c0b0346191014221307123071f44043c0e81002809241d0044a90003d441c0200503222500d440260343e505809501420b1b03002003200c0e8045511000c2c801408460804036010010343c4d98507a020307a420300540e82c08503403000044040501606060f84941d071b000d036180c0305031040d0f200c04122076034138181044010b64280380040041601203400341025005444e08954800d0168a4a000504a445203150707803040d00201e95030307206156130103141400c0606450b010761000840c4060000030081118840c20410400500000403030b50751000740e01c15007400690113005158 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 962310215 1250 962308965 962308993
    0x3041e03080915190503160c0b13020a090203160e150a0e0f09070507060506040b06190e060408010b09060f0a050616020d0f03081f092a0804050706080108 68
    0x3c60115041107145002c11a04d071890b01e9450f18008256060b07190781d900c80c00d100050305402442e240d49101445600e004003030200f46542c800683c80200ca191428020040d031021684040c809c2e4001903a05002006000d21109040703403148040b146c0360359692130380e44900200821707094412010200d03140104020781c2d6142c030500c6680c0c420b100240c11504003090604c0462610241160014002040483d00900300030b280d001d09500700707030211418415203025400280c0d407445100750302101490b51512181030035000d10769240c03d15000601c3e0a89440d655030925003c1e0081c01001845a00000000f41e8a450080310105105502900700c0358031500309014044540d00482c2c250410305034010922005a0391a0070801c0e219100c2c1c480071401c2040c0789000740156002400c3e40d049000551491080745032890448000c0b07e040f0a4082030840e907403ca00d14403000d1b68074280810001851900103001e81090400340518442c4049030401030b40e859088031401004c0c003481181d6001118149404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 962311465 1250 962310215 962310229
    0x80301090c020f0732031005041505040c0f0b030907030f1401020307030b1f0e061b030313050d080c0f0a030f0e0c033304030215010803041e030809 65
    0x282600e0048581e0f0303214507090703103180000680c040815090785141c0d0a0a00c404040d1049900b008200d808103203e4400c0d0000b500c9080f100360100d5001e030780d040021b0038031000380070701d040d0411080c104112900b454100380c0200c4600d4010304040c080c101000242405410045a1144420350003502c0601d0942d514102020b0320380390306907000d001142c00e0703880100b0207100844c012003098900007254010103061180c5032098190005ea41e001000303034222456009010608100e20840350240c1d00c1950075221107480e100080c18281c81d120110401075139009100c9201d4465005000710f400000a04d00304449548003100d404c042e5040901c0b12a100084800144c500342c002da00300444d9102e4022035140407290007507141140c0c1e030b0060400d10321509050010008840355040c60709540c029175000c40b065280900f20b80b0381800355020005051603c20320401a070019210056556543c1d12030100c2e6581e0024083c900140c61500d4500e25610740010101c0c0449074000309841c101400c0074100151 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 962312715 1250 962311465 962311481
    0x1b0807020411030a02030a151503111b0105060f041104120302010219030207060c0216170316150c020309100503100510050a03110708190c080307081503070308030109 73
    0x182c552210181260300d95001c0c0d40b007103080c02001601c03850066139240c01e6a4070501d492129001d0740c03500340003400f030801c11074614490b107003008a00101c010360003020510603603a4507248040c10080b440081e61041d00498040d0400b03c0b25a4001c00b016000c0108070b0341801d45c4040800e2082104201c400b00c04442c8840040c00303400010300b040e44040b10b00000384074080400d000240d000031000d041004911452035048600c7c401000450042e03c01040540c0c480d0192040300a602c00301d0b15034914042003101c400103d55480c0110251440c40c3c83c021080a446146040c50304042201c1b500c24400415101100340c020024a0265081d510aa8407030380064008001c0c0400b031040491140c171110350a4083c13040355030300d181e5925001e04009040b034100ca01d507003070140740c200100b201241145050360503008148441c09407500c40c02005443c00030704400000e04601d404000c2100d43c68005048030300c50145006040c1c3e000010408058071080580801084a802400140029030f416441192 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 962313965 1250 962312715 962312719
    0x509090a1503121806021b040e301602010e180403021c02010e1c0207180b040c11060f06010212041509080d050a0c2906010305071b080702 61
    0x18841c4109194811a1040d541041e07480200403012090b181d68000001d080749210050014521800c2c910025110070801c1005038507940100e00592640e40c41e07074484d0011441c10411500d012403103c2e0580074410781c289003458083c100201984070408150100c0d2034030b540516112001c0f807007a07801540c40c00001c101da190041d8004100e00881620320403081d025038000d130002c0105c00e66a0704607030313440f090400a43d000c59040281411480400141410b43c401441c0d1860407800181c500491a1504035801000c48031881221200c140d0020303030102c11501c100752010700040340e203040c2c143d0302c81201558030085a44404001560648501d8945400500500c155403001920680d0b9030401d4201b508034404041c1c082d86c4c03c80c0410f8012001c6001002c1c4e68010f862800b605a0014200380115000d000038094186808000c000d040310f03140c2e040012100d02e026108610a007122403441c402c03218a404249400082600039024040ca8034402d540d2000d140b0304481c46540f010f045800860b0b08903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 962315215 1250 962313965 962313971
    0xb070b0703150905130b1005150a11030a0e0306161e050903030d290919090606030605040507060806060409020d0e1905070b040e0a021309061d06040c0509090a 70
    0x1c1003103c007500030240200d200000e00d590f484c90904000c181e0141c0078182c100e003030845400420890b110b090150100c00081d0700e01030388503400c801043d00c1c00303072001e81c150259000010b00072a1a98112011600602065044232019030303400f140c0440391003030070025101040e40c420055101481e240d4802194a00314a402d500f412101000319156800115171b40408039101c060809016822820380d03003c0e07043d8480c00000c10070703032440881c51819014012282e40d2420017603140010385280c0090700d015902450800c03105030703a030610000a0000b42c50803a0302d4040c0715400140720b446461550702418009003c5031030a86080078040c02948160001c5060f5901e8006441106100340401400398154070030304038071061103290140c00d000b029040b52040001c140070034031003d0041000b096008115110040e565000503001e001c07000030f075500901c105428003001080517001d100c517210b0700454000380191143c941b24104015030300c0041b004400134106100018052404485186d042401e4800c00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 962316465 1250 962315215 962315219
    0x129040209011403011403060f0606091023120609061309020316080d140307050d052502010606090b18220c02030301060e060705152d0601090b070b070315 68
    0x403d5582090b0311000301c441e80700d6800e0115040c1484190f03406110019152910b141c00d00009900d4003880349102e0040149006051103035010304100138803018414410440e00e82030140304103941c1e224a9000310303907040c0000400c05030b080c40a41c0303c0c024003000b03203009d03603882c04a9480401804640416a414410701d00c800301c420452005007005000c0034030140c070001c40c240030013070680c4119a00c1404a4a020020001482d03406170030b0b158030141d041c41c089065241c25240c8039070324540c400d480050005e0082411255501580440115801d0b6241d94080030360b078031400c0019010310700d13402c8403007102e09001002514181002c5400b0100c030394620800c2510340d100300b07c1211030b2020302502580c00000140100e64006001c808000030803140980351401640c0c0d860f880c0e0000d1501c0001034202c200c0800e5080392040c1034500c95200210504400a100c1c4081c424040419035015010030261900440c07929010ba0031075541030780004501c1082e03151700d4001c1b8010408143d0214041e1f2540f080 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 962317715 1250 962316465 962316497
    0xa091d0f1f0305070509010609030b1501050708030f0f010609050102030712020102040305032106060f070f051212182103130b1303030e0f1e07080618012904020901 72
    0x1541e809035004400070b180450610062190f08070061300701d0414040b100d10b0400c0001c03444504282d202100000d890900b142c45401a28107000f01c0c8001802d5032804005c001203010b2000f0642e108035040240303c0c0c41640e0780c1c82d0580c0c081e03c5d40d00441d03006070800c008103808158103d04154501c204e61000514050f904c0d1030381421a00180388407142c41800c0000c902e80d02d1704c2d0481c416000391045132101d01e00401ea03400c4c000782d0f00c84e0541c010b0040f140d2001940c00d0280070704c07d0044482c9201c1450303980314030103030580d041c00404172003c60708a40c00108101d040d003000100a00c0100500248824807103244c031071041c007500000d01c1c17880700e1241c00030348000040020030554010034400029240c0380d10145805070561325021034208041d40161031086500100080c0244900c0c0c18400741252560710745025401c150080d0814002445000c1c01c1c800178015103000c1d400b07480c0300da10003005050704040c18441c900d4007040a5141c854200c2d2000d1041d17241980c024604000141451808440301c404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 962318965 1250 962317715 962317771
    0xa1b0e0f0106090801060635010801060302031c020721020310060e070c0210030b0d050336030d121e050a0f051e0402060409060b0a091d0f 61
    0x10304a44400214004101c0369800481c1c0d54042c1c10400002c3c882070342098402040c0c010355058009014400d000010321280b48405000000008100612810768484005a02800041c80b040340244072b078640c680401c2d440c01d05007610840950b800340c8041841c120a1034544800448804040002a9500070041c3d40802846040d0444d42c000880c1687c030703080b0725841181d0002c0000c0c3c14000d0b900341403001680c80740c40c204982c03841407c000074540e10aa01080d20541c054130000d010b840001500092014400150000740d020340840645520700c039410188444600540c141e00742e0301070164180760f24020303a064030301d50500204c0020f2a2112908098801e4408882c1103112641c2e90309100c200c070154010340801b2a2410414422410201e1030710b15241c2a403100d0606507a8040e01140031551680c0c2114010082d41c0010b003c0076442c3c00c0c2d450f409510909212000c642101c3e000200c01410000c0102c0f80940203503c1100d542e2021710885081100a1441800401410100c404807010318 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 962320215 1250 962318965 962318971
    0x1309210306030b070c030c03180305030f0c121314011e09050a17060a0209040e0f060f010f0326040f0f0801150e01030f05160311030607080105030a1b0e 67
    0x5640407401c0d0b0b103036040c40003500c1006442642000801130303140300841c0c0c11801003c40726a141c68103100b1100613009580e4108040c2e00014041d000000e4540c0070002c099010304280c5205d00142d5000c84644990703041c131885243c036030195843d40030b0070800c001d0303100d0f010f80c40d00b05006040030001d400034210141500d15803008a8404a20900c1060209042c44502c08016044015070b03609402d20414299943da1801003015242d180c0000d211517068a45030060409031030b404003211300c00e100003400d05448003012261b441000d40c3c0d000c00000e440d020218400116a0000068800042c21850a581d0600000d0108480c1d403c01c10000905030f105107004002081000d0340c11800303d08001d41c003400d4030b81882c401c0c0001c1c08030308001e114007035416488604480d80480001c070912034608e0702c0350400701300b05003a0340000c603420800004e024000701e00076a0140104c05807001030740e9040701a0384410f800e0040d290598088040a070002c0ea400350705420f00d100780241c0c246150307902c0181041c589011 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 962321465 1250 962320215 962320217
    0x140f040212100e06010e0415030b09100c020c090f0a110d0603020108101401050a02071d15040507050a1b020301090f0b01060905130c032903100209130921 68
    0x2010010107110319035142d000780c54075803a240380e5800c000d4002400c031440710745030358403070f90360381600c2e034004010180c019004681c000300c040440d10b451454030b511440d1100849451606140c03091010610104025000400c0100300b00d900e91100014040102c0d002040c00030002d17a10070005800700b084002a05001079040d0020880c28103501c0018034803500036003103010510a0700401d00c0403612106400000801c05c0c42c0c555202c080368001203251225503444541402c14034050001c08c021082000ba105d041d42c402c1030040c0501c6207060204840c000c0358103100060051000c0c4000902c00d40162900425604082c150313119280c000a017100c01486048541880e54a4164108a000d40c5503900424403410040d2145103040041014040318021940b6019501d10b451402940281c1c130800c42040d01d11b98400b07082c00c000c45800b1500780c001c229180300303108121000801070041d00072651040400740400181c1c28a804410010702007203442240d0484031159504082e24215020688408007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 962322715 1250 962321465 962321497
    0x20c100e0f01290405310b1305060a0c02120c07030b0108070803040501030f14090a0606141302070201271a030c03060d0203010e0304091a0603070207140f0402 70
    0x40703241e046007101c40312155207034501155800b0075590a200031802c08070031000d5070045041da42c0c10145502e10f131603140c0b030228402c40384403203d82219602c50164420341d10500c00d0030f000d6100c8068003c011541ca05005140354084030004034802001c0d00b000200409600480e14040045200f450090b000b001090b81c66600004042003031000107121a4010012031010b44103c0e42084070b21900ea00c035900509040c10707296a00f40c800e0b070321594402c03200034242c045450f91906050580caa2034141000342941c1003030429202041c94168004602c9009400800a003000d403d050401006500308500907818070280303104109206150885034903050800d00c82c10700d4400c6c02c040c180c00b0380e640c407150068041d034000d1040280c503801840c1166048042101c00c03010fa4081ea01c00240580440c2e158122071f030002040c000b6414003150840444088400e10004400b0607040520006c0d01044070000010f82c05018108007110100d2110112031307602419104a1401e2413000c40c00b6030384034490285510030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 962323965 1250 962322715 962322733
    0x30c1905120f0c04020c03031323010e100b01020d080c040e010e0709140604030209061504090b03061617150a0b0a11070b0f13030f0320060106050d020c100e 69
    0x4010300c1041c00c3d082007114210709007001c5a01c042d40e64080102141200c400807406001402101340740f42c41032400050494800784c021003d0640a42040301442e90280f1401c918001c01008500801002140681c020406c0300381904007140c1c07146024100d031034040410840031440d20f00e1030030314a0281401607281c4c1f05ca0f0610010041142510394003a0b14021010041d2803c250f8035007084404a940480c6c8081147e01e074000040d00030044110746140d140000500004e06203001c3d04a0100d04800700c00b81c601c140e568105903410341d102c0f03644040001300b0040c0c0c01055480c100581c80e07045a03100170b203038110041e4100801e00c090a142c00c070040c045000316072240f81541c4500103c2082c40c02d031010380b04e042d05e80201c890140c01294980280700d000420b10201801d501e40c00c0e0700007540c20903103445507501c05040261001c031071030750741c41041c98680c5417015400500007074280c1210095520035140c080c11004aa0081d045001c181c241806030110070300034082035000300d80d40703044000081c1070814 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 962325215 1250 962323965 962323993
    0x315140901060305190506012006060103060f0b030f040804030b040f14030c1c050f0d06140109030f0813050916030c110304140a0e190c0509030c190512 67
    0x142d0180c000c0505201c20449210094503030221000300820001c14543c035040016110031110007038519030a60003001070400803800048090080c1c40a89040211544441446885042c14041c81460900802c00304e1000422004440d6110b030096013850f04250322070307440e9801b50f40159401e41c0c1d040302c0d5004c0c4c0c0c1c0600c000e501c0c100d008a4607020045240a242c0c003ca01d4460100e88450490080c2c602090784800c0d000f038044443c040443c041c03550780c40d8400c80030000109441d0003802156200707120380c442a54040ca50440549401410030b00a00c603a90b9a40f0302654000607000505100d0410006031a80701d4542090007a0280f102076440401c0700e40c0e008049614a505a10800050800030401044d01204540c00e881c44403452038912003aa0012400450301540400364144100b01003000402e420600721800c419140c0060002c07850b04d5604980c1c5002d40d840e0158550031095006545203000c42822450103035180e00c0340c40c120307130f140005014850900100401c540048a80d180f000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 962326465 1250 962325215 962325229
    0x607080a1701030b06210114011701020a0203030a020d2d0f150314010e1221071d0d02040f02132c0a110d0b091003050c10031514 57
    0x1241041c0c61400543c5162240c00f5400e8001e0405401391401030f00380d2a080e003045120396210301025009208242c1d01043c0350000050900c1610200c2d00700c0540c030782090030180211061012164010b50035a00c2c1c00d0403010003503000c0805405126a19034000c10080380440900b103041442ca1900140390b000d2410090030360b101200007a001a00d048908001103c01160103001d4075044103440085a605c1a0039600410106120a189101d02641d18403c0c141c0c82006000d401c070f0b80007030314142e494150f00c3c105600c401a501c1d103010440100200c214810355010070003900b00010011030707044070350b90042012a025501300c2c050468001800c0000c0710302c0d02c1c0d8030300010300e841da42d1803001409071000b05500740003035180c01d041411800c0104140459503013211001618240206540340100a6160010564005403500818902001811901c0080d555030704494010f00079041751800e000810003003070015501030701816950002c5140c40c0d0019940340014180c802008070115680c20b080100d1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 962327715 1250 962326465 962326487
    0xc03100f0f0902090a0b010201060e0903071203020a08010308070f15051e06030606060a0908030a0903110102010b030d0e011412011d070c061a12061503030a09030b06060403020607080a 81
    0x100c40c1440020700058880d13100d0079902501401c800506a8203410040303005d0000c981c00342d90303001125014440390010200040c004203104882500010341d040310198181d0180240103004504480010800314009800807c510742c8900180c142c040010b503078054105480c1ca424841140e80e071810048062203900340c81c085029061000c2d0321a2806100280d07841d4401440280555000f044c0710307540764007409103803004e0f20400c0705894030f4044642c401024000148400d03150001030258940c1154010f00c951229800301030042d050000100b00c00780c07413134440317214914100315051160640e8403504002506e541c00f4110001c0b2110b500d003900b1004608410143c0302c3c903c0c90b856051064054010600d0064154400b10102d0000501c03100901110b603680002078000070b11641d40140320303074049405445002d03809030071030110540500341540d034014010401d0208a040c802030001c40d401004107035000c4002400700f45019100d5011800c5e0790014001218680401301e044805c0175040080411 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 962328965 1250 962327715 962327741
    0x2030a0b210307022b0b0405060709061e0504090213081501050a091a09131a1603020906040506040b0d11120c0c010906021303030905180105120c03100f 67
    0x1e50399180040303661203105491000744203020180020000040203c0200c1002d98400c10b4240c165000c1d083c064080e1008440440b4540143d40000b800c01c1d001d13241c501c05640352940c070300542081a03041d0310f00c980b040c047e85038140b103030901c80068902c07039030b0004100c0c403501d071810414000d2804044616103008200d0300700e00c030688000140101d8451044a4048420324100480d06c5041d41030322410015050b5044c1e078010071305c2010007070310010103010043c0152086844032000d038980c0c00642c89644d4107490000d00d6000202c1e01c0d0214034400c0d0050820084028085494550b48000041041e400707544914a0b03141d01094580300140603103d41200319841c1c8008628040305c0ba00004900000103100c10b52241000c1400038245000350700840800740e1140d011969402c021311202d2000300540b00480005091030300200300c1e81131030710300007500f10084c910070222a401d0008200c106007400340100103922940080b8000c1d96820049010015803040000810f2207105da980410781d40c1c058a110 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 962330215 1250 962328965 962329009
    0x18120c011409060a12180b090d0206161119030804030f08040203070320040609020d060515070201030e24061f092102060403140115080c13020d02030a0b 67
    0x300054407883c04440c030500161601e00c0640f1440d07001c0d80020502c1d45001c0c160b104820800700c080118400d03040f40240c1d01401104c1c0d2910b00b00000300e035202c0007100c502d0203030860b45419030610740c002e010040d400d00d075040542c1c145035490940d40c000c91130f0b000300076400118000c0902003815009002c04000f81e4603403900500e00d1400b0b8010a5860071584401841d50a940c650311500030b8661504c0409074400030400c1c0212a500c445480181d0440d00c1000152850005c0000e00d500e4262240a03d56008490684c2800c91940054004102d5081e6400c180e00506c261480c2c8840d1910103200c030230b0341c01a215102c5051000c14414a50180c001d46a8071881080c0310407482a040180081203581d12280d001e9103440028040030b080c2100e01e002908000003040210400443c1084003020050b8100208901c00d0341c00050851f1100e107215005964020900e8140107050000014041110302d100151500441200620032a031007140d4484017542c0d107034080d4000b4a0050214420b01004080c94 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 962331465 1250 962330215 962330227
    0x30b01020d0219060b0607200406030213020705010b191a030903070b0606090d0f020f060304020a17162312070b0702040b06070302060a2a0518120c0114 67
    0x1940e500c0812041c2e10303411400e0f40340201000095000440d0240e0082c040e50f445070f042d450043c03410039075210120802c03082c4901043c55420030b445460b007200d4005205e4070603a10f1803c0f01b240254820320090b2095500c41c100c2d20071075100c840301d4024203900c0c2c04851810904d01790180d20324918421140c0e000074cd007001403090380d81d400070035140e469400403003101c00d684501d00020b0700e0303104413043c0e281c20450344425803040c00544501c1882440c002d840758070582803008108440781c402128000c0d03100303004060a124004410030100300742c44050003181d4112100e440703c807943c40015800851203103045070194800e050428420190030300141c40120701d0b0001080e815071111001e008816a420001c142c000079582d580e0040e030300314140071348141d0351202c240c1002910748404031646d10000703003001c0c22074a44540d00c2d10700e03003202d03240901107901143c100c000884540c0e01c02c01c0d4242c2802c540c05414810343d91500030b18034150007580000c04081c209600050301c0c44010701002c540841080c040 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 962332715 1250 962331465 962331467
    0x160803150a1412070305060a1d12070b1f030f020315061c020f0a06030e0d1103040b0d2a14030f0f040203071d04020a150905040e070b19030b01020d 65
    0x2210142d5000c465204039032608451041c82c0000640c00a440b42c41040300380700c0140041d50011410175400111001c83c54607520803075584890101c12040300c10400c00c03980010079000d90f0003507041020700443e07009143c00014191943e14290b0804d44d607800c10312120404500d0304002e40c1181400503000d10742d8615003200059114000410358080000c43c090b0070000315592055080b0310004014030b04c00c806038441e1070007402080340e034070481042d1249107500c1ca60381c1e00841900b00c01c10701d1a0000c0d4501804d05100070102d801003000118040d4a841603010250340c40980c0300810021024001d2a492003840c0c01880c0c001c0c0e00490707804019003081440b103000b09200406501c14125401c1c000c5d036444502c082807a06000b0313400200c1e406500389941543c4411a244d490045000302d5080c410a03844545d80307800203031030313206c00303000b05140450800043c1010703002612544044400e40300a141d5407401404258407607560a0f0940402031b0901c090f441c2c040c491400d08580a200800c8003d90b0a90 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 962333965 1250 962332715 962332739
    0x6011704080a020a06020d06080c090f1b0405100f0e0a320901080d08071d041a1c0c08010b031203061f18060f0e040f02160803150a 58
    0x40040c0800e000040c80c01e0b2400c0c0208444542c4030b52000b001c66560350400442c0b00100341d2030103042c10b01d0055018404c414603004060ba030060800c82c0110b0300a80380d8030700f8072050f00300e5001044c0d8940780a010008844e551080c01c000142415280c1441500307446d800280404801c0300b00522610442e80240401c0c200c264030365451203004d44612699114012240300200c00240d08294031204030000491040404985041000790b55103d40256494101e4295000d481e408007009240312551140825840c2c1900460384c0304000e2040003524030302d03042c0414810300411203800484007818181e101000520000724000b03200c0ca400810540b60072034006034030b403a003c0c0c54001611102201080c01656403400e003611842c035003815841d440d5000c01e4040c2551016101c8a100307000102d8001400c0e5000f0340c0400403090f03460f5680200c81c0c1e40c8100b008000d14503464917081240d400c0c482030240081d4000f42c880c807907004180c401d4492400c0d4280b83c6146180c42c10310750050352a0a400c201e08a4041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 962335215 1250 962333965 962333971
    0x1e0b0c0315060708030f0603161802042c06030102030f1513020c0102180613032306070903020102010f0507090b070303230414010903020304030201030f0f0501030813060c0c1205101e05060117 84
    0x80e00005440400c00c0ac850013078000d64000c010052088040c400030141251600360640043c401c82205540d28201010700300e020481c2d40c600340c10140000590740300840c140800c60030744010409840b01504005500490b0070524404149079400190010000d44000a055020000305d491910f00201c05102043c0c2e03004a200003001c08404800c1901e1b148a08110b00c07455000020880d0020311341344100414002c0303244800e80c055449c0404444a060160040610450880e00e91490051910152480590100780298109541c0d2500c2c0c1c012101c00f020651108043e0000701101c0e800e050800c402001d10811100c8040da01d424148030009401000703403001c507602420001603031141c020020001c1d00020b01001c0009107860004002c04c001e50001e80060b24080842901e82619440165651000780b040500382000301e140410140c080580003100f00307441002078406410a04840c0426200071252040110b0300f01e504c1104040118410680e02c10024a4142d40d5503d41a0034401160006 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 962336465 1250 962335215 962335229
    0xe0c0f1504140a1805060414040b04030e041e05091501150f0c05030304030c03030e0c0102060408030406060e0c07031e1b0602041509031e0b0c0315060708030f060316 73
    0x1600c1d42d030714941d206010740000f81803070008400240c0200142000070801111b02520540c81c03d2224101c0314110303a41c03140b040d607100d034a146041d2070311340f020f03a01d6141d10303120541d0294841c0101c1d50301070310710303071802e001035030515008929400c010369a10704045030032103108540d41003c80100305103280303a810308503030740b1140c2003c00e940410a00204e40030301c001e2401408502c400020f010405500485054469000f590200000001d8404c003944407519020a2801a80140701103808644100c006641161140600240f025510441221202421520503046c180045101c02c181a04580c01041810181000071046401c0310400790051285016800c0c0424503c45003008106a9904807005402c204448003058860040000d120f01603501040b51102c2c8040d000e400440107040760f00020b56030003040310b1134035582d00c0c21400154000410703c640204046518482c1600d41e0801064280d015010441da40d00c0c001515192050010b0101c6000390f201c01c0d80030080d0307440188803405603070342 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 962337715 1250 962336465 962336489
    0xa090c1b05070e1608070504081005190c0f0305060d0f1b081603030e03010501080303130819030f051303050f0f040b0c0f0706022a040f0e0c0f1504 65
    0x50030100d107410410f8215601c6102c00c03c0900c41003520030101d0007880e003c0383e590954655220b12048915014520032021507038000f004002081595400040d0300c2203920301c04428110380f02c0d2501041e24035041480700410f1001c156003004c0e6505005040e40b060058843c1c1c43c24104aa40d03211540e0b544101c09804030b148480c800384403e00c100c500c2c000402c03a21044030b400600300c1c80000a01001840102c0c0459124403003142681010b0007200d040f1751103003001d1821951810b10781003a142421404481a1000b00f20004c0000718900d0035901c1529160b60001e43d60401009070800c684018040c80308564410700e5030000607500c8422603e045000c00c168544442610211000c5801385070400c105141d03003c9034001800400241c0d52803101f10703060844c2c410599508050342c1340d0128651000d48600e000d08544281da074070499071482400040e100044140c80100c12a080340da01c501c420495070002c01c01c902032840e00d8406034403540401c032030120750040c601e0000f00541c4250300c205224034207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 962338965 1250 962337715 962337767
    0x203010204171002040b3901270c05040207080d060b040e0c09131104170a0203010507051e161e06150617040507030b010e0703050c070f0609020f0402070606050a090c 73
    0x19500e4005035000310038040c448404800c0c7e01940079040d4a001c80e1141320800c05903400d49036045a05100c1daa80141044c0501802c1c501404041d43c8014810358445d1400c0004907000039440c8500c00c001c200490035240c80360300303094800c6607100000d800c2c16170018090000300c80660f90900044210603070140d00003032181403160480000d0050740d01c0000d00e50b00c0041e41110710500800c0c6c02031280d10850080015650b140401c0d20036010344040c2840e0f100c1d03401c0c580c680e5203400070010309110140b0100d2a401c90b1a50351400c00e050a9009034500c6d0003150b4000314104a0103002d0375412949100102d4841c5003024002818202c0c010b8017441c012400c0404501031003018840c5001030b50300061417980540e10340d01d841003a820144e0b00e840c000b80c5020001152440d01406550030180e000b009070500c41c07125100d5034007509030004166403003c940b0388112102e6503544020000b0341d11684010810601c1d0408018190085600c81419103080000709442158410307d901c100c03407408400410000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 962340215 1250 962338965 962339017
    0x1903050c21030703051206010c03020d0c05072d060f020c0f150a02060702160303051b0f0d110f0d050304021e0d0602091c0201120e0a0203010204171002040b 69
    0xd2018a00c41414080050300f2420305174081d009203955483c0d841907401949030440110b0302c60341883c4e0b01800581103034102000c01c5114120300300816006c2c00454004a40f0b0301031803040c5040b1500c05002040388210341e9120800441d220340000d12007424210014000d20300d002c2d49030199018180d02c503409004044c52582d4843d5009640030307003011129070b21151070100c01382d659a0103482c1c0d10003603c01c144070090203159020a10090740d5050fa140d038100703103003d455011170000104515040e40190500404121000c20181807115800e0399269038108038155042d0400790441551039098124010f40e58120340c002003140e403c160b0503503000c00074180524130781055503405040580e0040300184081c0621540341c02030300040c0c1007180c442c001c82030070340544000720300c07403d0b00240450720181403003054920591106560000f40030607561031400d658006401ca9025400c0131403290f00c007543e041140c00c000c20510404800b8540d003180303014241030110106e400380c0ea95200911030b03801c1030300c0340007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 962341465 1250 962340215 962340259
    0x10512030c010f060f08010507390c0f06050405100f050717030402120a021509280e010510090e070918061401030b2b0b040309051903050c 61
    0x3074a9503078020801002110980360107440f9a1065084030110a000890f444506114083c0075110320b032078a1004541c1301c00600303058454142840d9800e0041004915070a00c01a0054070151068180c01c0c036143c140342418141602c0c0d6046042004401d110501090b00c45040c65600309415040120303040190403c1100c1c540301341030f00103001c1c8403103960301c1e5284102e0b4400b86010398070860ba0040907001e00f410359961a01c0300d10004e0b5200410801120480a0142c003c144035140681003240685881007419405820392075031000fa120b41c504104201c0d03807280b541501524080312102c4450950403c02002d0382400e0040c1d0031020560350100d0780f0603000c6c00b6650014007603000f03200d5032100c0c0695840000e0029100e280394820340c0300180809988a4442d8003c14000203182000d61004100051840b00b0500300300d500c1814040c82d03a00102c1c00b5802c51511132032195980d80382d102c1c201000d00125088010840c2000041144107000140380814645039440303041e201214410007100d6001c900f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 962342715 1250 962341465 962341477
    0x60d0204081b031e0a03080414150f0702061003120e150703020c03120412230a11090f07030203070207050a12110f0d151116020f01140301051203 64
    0x24038400c002d00080c00600041c86000140e0045040d940e813900404003a034031590070100c000140c0e8210b10700b81c80c0000d0041c500700c0d400078003454a43c0c01450170030440760f1a000b80060043c0e002c0d405042044101e030642564940e10071424805070a070350804c8040d0200c1c444243c000209034400148800c02200d12800c4d24a4100e000140106c02990400c8100c000d83da00010081e40180600c0c40f14200310f00300043c01d488000002d80c41c0c145024036026540c00c014000120403545070890b900080c82400002040c500b4941c00640600300440c002c4c074040d6400d00e40c0d403100398040c1a45030101310750f03141503d0f00141e04c00e010341800340c1c5d00e5039040000c90070a04244c20443d800041d241d4040b4014040944038000300d0f200e084054926484070040150700d0300d140000b07a61000c40d04003480005140c4400a4513040035041001c254001c2034281e0441c150070401c4041c24072404420b60704203502d403503155940300d20420300f4880305960100104c88910f1205019160044000b06050b06450b0010000c4402c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 962343965 1250 962342715 962342729
    0x31204030201120b09010b042d0b1b1b0306131e030314010324020f0702040e031e0d0c081003030f1101090b060a1e032904140129060d0204 61
    0x6025a103c41042c0c0c503d8200703000b031000421004048280403000c004401008042742d003505100c040c54820b0a0035994407039108409503000c603d83e00c1031000c0c010811703c0c503480441420b0003020f51118080c10f19024004050b190161030094180c00410924115010310407440341581c8072058181c10141c003d001448a045d4051004400010502624003450000050f94204000100310500c00c200184d000700503125242c0340c0100001401440d00741d20400040140b0005e683c10403020317689102c0150684a010507104800140052100080d40305030130b04040941004c07021414600c04808100070240402402d00c000864800d5880c0c0c001d1803a1280702000c0002070151900f10f10707102e08080c0d03050f5051030040d1200c84000c9105403605482c50701170b03800000c2c04440940707162074003030090031000b040b40313200b900010030140d000c8112a6043d100d0790080282110300780150b0202401c43e80169170490034040c4c230000031100381c0b0303100c0c140015009040314415181c0700d01a8400300240304640c0411 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 962345215 1250 962343965 962343979
    0x18060b011e080a1803080f060312030a15050319151a09040305041701020403061512030518121b1e060c031908010e0a091a0907080d1d031204030201120b 67
    0x1010140c6c0000110720440e264040c00d00d203911560141503690404c9012241d40d04c2c4140000f0303000c1c80c9a81d01c802540f1442c03501d000e01e001e54450109041c40425503c08a510451600b01c00c2840319110718001281c607a25000c0004004074240c0c101c602d6501c4124920400d052804a0705141c80741703040d10041c0240b08030340c6800c15110750146000b580f00e8401140c0c3c503424004191005031034500703a2130446a00101190520712165011500d80e44500840c0e9600401c911801d001ca4440808020b00c107412400102102c440300104d41c400d584070458094403401010018820507041c07204075196419059414948840c500d004440c150300604141503503c0c4284a0841d04165003c030400781200d5041812080585940e003804080d501c55030409050340c0c8186c1200030741c25116840e500d40c40741540043c0c0c1c011944440000742082030141e4180c00040504400161410780c028000c48e0f1140700728000c1000301c0000c0100400c40c000d500c0041e0503c43d0b04910801410002d80108242d441c00030100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 962346465 1250 962345215 962345261
    0xf0c030b0a08060c090108040f080708180409080f0a051c02030f0a1401170309040c0f0e0103020903101805010f06140103020c28050118060b011e080a 66
    0x100140145140144a41c8414800041252020949600030f003507980c0b0a03464401090b006680499014000b02c1e03581440c400d0540108205a0240507514802c1e02d40c650350703002c1006685404200c104140c3c2c442c5161640038400038480e030049405d003451700409a07440c1d4810340c000381c4050040b60441e0302400c40d50001d03170340d1400203680254800c4246000380041b540380c00c0c0d4920111400a101c0389941003a03100113020140c00c14011000040001003220304c1c0a8280c400300382960752004000021503800686961626041036032000300d65428a021803e08151b140000c2da100c1004040d1410590350720204100d2501c400034100030140c2001c02482400c2c1e480b00c1d4035004201e284500014010103035900d1401e90f10078000c44440c00c000070010072510410703903c405256402a18104e051005440c0014002002030103513185084030800ea4081c2400c8a013000b000b40c50600988904005444101c503140240c0c1c11400940c407821440c1c0603100c1d1342c1d510300c481d00030100c480c00000740712804014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 962347715 1250 962346465 962346467
    0x20919050a060801110f0f03220b0708060d0503031f080318090105040b09071215031a1305030a140f040905060a08010b0f0105091c150c1d130f0c 64
    0x41001150801002003105000046405c0544d0280f0b15500b004105c0400803040c04440b050084c5411500c030031410115142074031020782101509440c210351100d0400b040010040e0804185d80d44424250780809070314515a0303409803a03102c001d14018001c514140403850030724243e42048058141c1d03d0450341c1e0f07038003502c420081d0708103035120451154101d0030000c40c0c8c50509002c2e1049070030010344040c405840b00d420a40b850815a80e10700b0002e035448102107448c601c0d0142880c0150300500098078140402d070b1401d01e0000d0010840802c003820080035600060340007048504100107490014001c42a0081c01e03090f600c02c0000c226044000802d010800681d1a40802e024007400c0300c3d91981d545c3e0340e16905080c1ca030901c6000342e02c8610b074000f603075481d40988010a82c00e40e000740a610015507540c0a0003030b240c6619015281404070284c2680100503238071442500c4000360030841100307a10a500300b0000f008000c00c5078001d800c143c603c0d00000704260401110040101e40c01c1c0041741e80180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 962348965 1250 962347715 962347721
    0x190602072307180b181b0d0c120c0e120304050414010e100f05130b0a03030207170a0f081b0d1214040c060c0c150509011119020919050a 60
    0x10304001c44240c280c3c00044259148229601c1c440080c10300c5041060601000d43d64410040c80a80705c200390101024200d51108001e2a5104820324005502ca0140a005101074030078140003504a1030300c0c5042c4407603504810050f9488500300c0d210a032115409031424210300130b40d4401908a410310311203401c03030305000500302d0588038441c0e4406119520680020141e000901c910f41e118010034030103110a040001c0c0d1940c017260b01d01008a0424458408205510304a92013600140c00110040c81040c0d800c80c8010a10051a4000c0400d03262544400c00d0440102d103000308411400501c0030b07060f62614000112840f440b0050364040c0c0c032400c4c3e0181040b0803e0380582d0019250a400b1483c008100000358001e940124000d2038a60800c4800e0703482c00d2a000d0159905c2182d87d00c005580512445001580445569820744036101c0d000050302100080c0da041c061a000600700d90500a04451541407054040b124000d60f038840480b00880d158021801400b4242804200100e410690b0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 962350215 1250 962348965 962348969
    0x9080c01060f03020906100c1410050c0a091a09031f060501080411100e041d060c0406021b040e03040306090c1203050d0b011101060b0417190f08120a05040c0503190602072307 77
    0x1c002f4890365403051082a424451150007101040f82c0c4141848225540c1ca0b9100d1074000d600305003440c02e0744200000b4030301a588004007880c20002882c09450901da0302910300188001e0130600c1ca02d04150741e0b100302c02c50754212214003441c451340d000d41c09144203034130003401184081e008100c6002d2100d452024081d800142e659076204003404102e5600d0741c01c080350219180d40e40501020309540c0d88980702580e141507000d500c00d4031059034020100040c8024401903108442c000740803220b40c5048200507005502514000000d4a00324011035086811204060844500003504010b1307080180c40e2021201242c44145d03107440e0010458605c0b80000708140d407030380716207010740180001300036545003004c0c0010341c1002148240003000984444521001d503224000c03260405416080c1c4555840c02141ca400c2070713903141c00a04c01800824440c0c0c5019240583c060300c0030061048060414050a08008000542c0001d1000c01e0005000d900140ca514100700e20410706000b40140d540c5501034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 962351465 1250 962350215 962350243
    0x403030605030d02190206040302100824130504210c1e020a0605030910050c03071701050102120f090406080102031e090703020402030a020d09080c01060f03020906100c14 75
    0x180080707068580011848058000c0760b00420140000100d20100280c42c807408a821206c203210200050b40d40707160b40381800007a5603940b0002e280402e030741109507019400c17000f8031510840000445444107071803d030036104c48036800304003500c1c0c610b41546403500017650020451141602c000140364408a1a19054081c0b00b91001315411209205242c01111790020f5000d07952050402c600c03400b9101450b40b0210090030703208410440c15854081e02d404584a405030a40001004170640c0c000810412000310355588448640c1044c002035541c40740040740103070f003801c0800c002034240f01c80e500b25078103404c018009001d9103035100c003038602130b400980d203410040081241d042c1500d00c008900c07e100701c05850007400e40b1882d5809220013540090310681000f81c0812041e1215001d40c0a0610440c0c42040b90603035618800c45002c1c21280d41c1d400003004005100020000b49c1d44225140383c00c46002c903400c00650340c0c5203070180e9961b0780c14a0002c090040c01c02c1042142c85011074984210065 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 962352715 1250 962351465 962351471
    0x501060306091103012c10051513170a050a12033903020403120c0308160e0402092808120421260409200406031806020c0303040303 58
    0x40d002e0920603183d40a8104501030014030041003110a50a0919014640c14081000701c5a28000050340c044049441d002502c1c1c030924100924205107007081c03040196040c00900b003480c00741942c01e01d02480d12400420190000ca405004a02403224200a90303102046804030b11b00b07850685070010668100b880070a24009a2048050500b001100e40740f010301a104094a21480344403c9070881070031900c02c00d9401c1c400880041c80b040880034803038036079071265180c5101e5440e00408041d0000c10035025030010000b45180650440d1201e158070004030350240c1c480e02c212000c03c02610201841e2407400110304440300c001543c624802044d21010340594a05070701e810740c04030300c520031480341c6021504030310704c8044c00e0501d082e90741355180c0c0f00d481583e0240e01c54a40e415500d00c1c1216052400450024040201c0d001501c500621104100500001541804031b841c0550040784220b070281603c40014600c03125400c1e0400b03683e07e43c428400c40d1a42d16100c0c500382e0f244c004840850200780303 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 962353965 1250 962352715 962352719
    0x513081c030c0912030309061a031e210c060c0d0c0305040c120f0507260105010b030402150408120405010f03050114120307060c0203030f0106080903070b07021c030501060306 77
    0x210a00880c0200c0203140c6803e0300c0c00746440c02c00d840d00c802025064040640e00e0003050000f400c0d502815584c0303032140f5043c2e80c000004c070080506045a200109100c0c259a19041241c00c0d0081010480014102560640080c03903c0580403544a0850b43e24102d00680c0e04100b05d0071200c2c00540500f1490300810084400012802e40803290261400f504007c94150100880d14a1103444078060f44998185442e051541d540d561400f0f030a9008582d5112441c0030001d9001441040e46018000e808000c0c452940f6010303c588042c8801703480680030b01200591022241100c10455006082c400c0413100c00014084a0003025009802900e001509440038548110720a00680d410784040da0a010703c101c0c41c000c1006020301d554003900085000038010400821480d100c0c40038401e9082c0c000d0f59607850010141404840140c1090050040c80000d0000351003000007a03d4101d6404564080d0780d0711822400da2a104600e0024803038030100c003040d0001d256150300301d24120b540750b40342480305076 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 962355215 1250 962353965 962353967
    0x1f081b03010e180a15241505090d0f0503030a1a010909150e0a0501031e0b040b06011419020f0f0c040908090d0804031e0203030315010513081c 63
    0x1200a2240e00d460486000c0810245040c2e500c000007515001011190003130101d94880908038180c403003118815903226000701c10000c9100d40303403001c4c4c1075804640b0569400c0c0b044042941051100550400001148454030358548030700791107249811075007400e1901c020340340c0607950350710403102c0344020b5003000303a54041d0904d1005241c08150058580203a46403c00c040c01d40201810314036140140400355000915030044609503000e50f0040f480800d5940c110b08042448010745100c1821901810000002103a0b540717400d181c001e54000c00d1aa507503141d0300012180ca400740102d00009490019120100045404500103441d000d90255003d0b00101c0030340907111030000b143d6110580040564010515042c1d01401c4d12511601132141003000040220f029801281401c5603213540003c1c06205000e50342c1c222498640c181c0c080000040d4941c0d000c29100e000141a9034802000c010185040303a0049090f10348442041e6103030071119545074000e036603c049091040e46110202000c2c001c0203 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 962356465 1250 962355215 962355217
    0x10c0806030d080709170106090b0a0302030d05090a0302040c0c060e1f2c0d03060503010c0909020904091e06140106020d080703150e1e010e151f081b 66
    0x40c40004000c0c005030795100c07109803003c900040c520004c0010b0410040b813400d240d20000a441300b10000009a02c6081c091f411080b03440310700d5510321582580c101000143c0d80083d841682072603034584641c40300c1c001408a40c000d00c0d02e0b00001e6000d4100041100c040768000240010701f80104010303c090540840c0042e00d0344c0040c042147c081c2104a0f0418942c0c40719000310032060b01c0c00c0564111806134000c03840d1821740340f038800c0e0701d590844c0301000c4c1d04650600508016050440082003164590703607016180203494070400c9913441d004110140030f82e480d6407103458403540258443c0d45020b40c45030075201102407404212112031510f0442c24182e0b071400d200a05070764183d00280005c42d501c0d2000d0b110344800505201c00c2640f0f440d01203588125035a00b10b401081c45c02c3da11120782c01c20b1000502d5440c2501d000481943c10308004010b2000c5490381c164100402c0b190a1007801111300224111505020000000200c0d902c240c20103640e102101a100ba41d6402c1e80500d0040481282041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 962357715 1250 962356465 962356471
    0x210403020c01030221180610050303030610030b030607121805030306190305030c0a121d09131e0b011703030402104b02030f07030e0604080f010c08 65
    0x103a00c4100800d071154040d80c0140701c40c0c9140c1c01100741c4860062a8000d501e02c1c01c680c2001160761140c1e403114400f404004050b044824042000451810240440d50b01d00004109901c5034498895441c4894005c0e03005031480c02c400b5095508910704520003500d04041004c107007101602e804070107203420120f0b901000006a00c400594510f4645030100500d520b0240c0480a000070300000010014500704000d003230780800007000d805130486609106000192880d102c03428048002038041a0f001007041c0490180300880300f41e840c0792180c044520421084c540300a2540741e400d1071099850608950f102d250910851080180740e89626000c00d201d442c80c80c440b105644240040b030014544840b00c29194407962400e4400c221581c107c482c0320849400126191048001c5103010010041400301d0030170060a140115100c07601900030350324480d502d000c8514503c0410484200f500c00c94100702c02e0080201440c0c1c680d5201c01d10541c170b49050303d0484500f5880d1086803041c00d4000d00603244 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 962358965 1250 962357715 962357717
    0xf0b060126180c131a090703090c120809040905010f060303020a140a0c53031c02250515060442140109050d0b0718031205210403 57
    0x1d61004c4c202ca402000e00f0300c030107031140c4c20420002c3c0000381d1780380c0da010980309003d155400301e085545410315559100141c0c00c510000c552104541e0301083c0358800319080300c0800d0354006000c14440c20300d030b0b006100482c4480c00c81070a0803000024507a00164511099005291030280a40c2504c02155a02d815520080400c581d178681044800c45031201f0070244401100c024035241001d108a409017803100b804021039001c200351400308410500c500c5400310b41707007400847c5000514040d615a068000d84498180d0303400007048118a800080d8201c003c200700c841c2409421150700d4065160b241f40e04040f0050f121400c0000c3c0c0901d0940161400004032800072030703406424105032860704010403010030024040d848140562240d1103003080c000d1102d04200a500b40b0244001841d0b50b9241e84628810000d0762800030105079552801e9401c80c56504041140103880354002200f040198000340c80b031018006c608020540201c02008012412900c0700c00900c41600c40256110044e64090 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 962360215 1250 962358965 962358979
    0xa05090d11120f0c0609070e0a0b030f100603050f070f09020703230c1209060d090f0807051b220c0c0203010f020c0610030f0b060126180c 61
    0x412501c1c0a5100411140a80030a07100c410103100c01ca94030030341c8120740361500c1040014030a64000c5081c009180c101000d030b4044e111040c0b13807040d040e0906401410240c03d80344d0300e03408510595400c0107403046200118040d2001d07010056404002043e10344415982070040c814241300c1e050010600005a80303010107800d03800d07410222250002d400200301101406180303c10000343c425201c0781411f01401106001e55151000b025071801c0c4030241c0c1440c01d0015041c03225040d00d9407400103079030407544801c0c400103007110242400d071059410a54007605410b400514102482008121a000215410140c0501004180901010860301503078030082c0e001c201802ca003444c500d504040c5d252081b034904074120102035000a400c642c40003190020041d4000f54082a980c01032003184e901078032001650040030700d0740e1500103601508040c010640c0c2040800241d09a0043c100100b00050f45d13101841c6252a00c014070411110070303510440d8407901c0440b076007401540003c421200342e0000d8006 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 962361465 1250 962360215 962360233
    0x60c0a06060b0a0e0a0e0f22050a0c090603020603130c0e07020601151b2003011107020f181302061215150f0912030d0212040c0b090f19050415030b0a0509 68
    0x1051f07003040b000c5c020b16020203400c1c1441100e50079200d0610103c901401c05090b2101082c40e01c801242040c0d400000d034607007025020005031740d42c01c0543e54000d180c8122040c0304c060a00c1c1c00803281c2d00e10b801c818401049031050114095002038218180c0d1102d001d242400c01d6516801c7d20719101044155054000301d0b400000062065220032002010041c0740004403145180001d00396400802118814200450710100358030344214114042e110945041e0091500542440c6809100138120700180044140003404c40d181d840403151820500010741e03100b41800c8145203811588403040300c0c0309441e003603070021280817807900700c0341001c030821006460540172805021840105042031141c0b40814090800d40050500042030751a83c10100e9424a00d09031130140b100301c280b50041c000c098810301016055840f440e4018044100c00c860036000800141c42d40d1031016605d4001903085070918026000791868001c030307801540d11603044000d055a03a0f01c045c0b0b04545080700d0f65180769101c4070032 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 962362715 1250 962361465 962361481
    0x204120f020a1a0c070b031005010f120f0c081f1205070504020d0b121b010318060608011a1c080313120f1d0306010302060c0a06060b0a0e0a0e 63
    0x14144418405402110b845940340039070485070092010000003c04000303044484000c0600a1901402001102505500300540920409881e90080ba41486190602d00540034054000060144002d2034140a0b0342199401c440280c44d18058407408100302001180d0209141a01c2e5100d515a052440040e10300d040d8070440700007902c640a540380e0059007000310340368903140020a00d40048000c0422100e0410046c000c21000505102003540c12662110101d04020000110401401d18001c1202400e805032107a503148103400c000e1800e490f003c40002e0346501908141c03802c0e0303d446805186540b100092041503481d0183d80d0000b222900041d000040c4064007664100d4045501c021310801d40d07540b21918010b07003c03000d4001c558680030911101d40e00480c5c0c22a0300c083e0046690b80400d0200200342d0b00c0d10113020082c03041074041105001e01800300180d10015801041c1030100c90707a5140582c117160f0022484a000882c804514a61810420a0360f01120303881d00e02021196503040e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 962363965 1250 962362715 962362733
    0x807060b011b060209010908060c07030f0207060504180e030c0d030501050103020c100f02072306010501050711040b01110703060b09060f0a0608040503091f030f110a030905070506030708040510020412 88
    0x72500c6c14040d40500c00b1595010800006214412110a0f40d030380e501c40c2e04020701042400b20856045510043c814040e0650000503501200d400340d10000403d081d1802110141c600038400302818840491f40100300c11000403102d46003807040e242000166282c4004405a100d8040d044020382d01c140422181e00040c1d030312940c542c120348000142801c81e1550399a800c0c1516001d80c04800509078940c011002d008d0bc2018010242407c0c543d02d0084156119020903840e81c0840303101d44da0341e0310340e10761590103029105030b004000c02c2a541460707220b11f4400000d00314071400e18021002c083c009845400d210001c00c940071342c000c0001c1c0b401c0d490f20000b11211303030004104940c20702050010003031549079044241c009050205601d0135580c140c3c500101111115680607142d40d04080791203030001084c00c2118400701d00c40c6804204202c490408030301e09041d0f507200b160848400030030000c40d50780c00102e850055200310300b504c0082c0300e00005c40703043e40951300405198440981c7d0130400210710300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 962365215 1250 962363965 962363977
    0x151908060111030f030c041d0f01081507030b0127140d0206030606071b150206101a480a020105090402162001020f010501030b070c080d090807060b011b0602 69
    0x11b1940c46c80e00da00c0341080310140c408000350303c1d40500a4010302102400a0501601404900c801010345081d00c0c044407500813005440380d0181590707140400b286910a411107901302c440744100800026215620300070f0142248612080709040300784000c000c2ca018900c456283da0000c3c2080d0854440c9030411011354007603241111950030040c1ca0b4084008000140e000400a10b94250398516000c400641040c50040804414000510b018009000001161008080441c40503501ea821142035090603502e4039038902e820407024104100740e0b45014a07400340d0301b07551001c020402400b43e89415600c521031036009012030741c02e10001c040c0d800c00e5406030866603101c2444c00440403460300d40b4900041f40c0180f26540e518a4010200c0558041005c02440131111008005661558840400c58200034180008001e01c214401090043d48820350707000f01c080820030449441c0c2d40c03401d440b85601c1002c00300d803183e08003403c4200e2513025106001400318101c2008403440155902c05000f54002 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 962366465 1250 962365215 962365231
    0x8070e09060424060609090c051c0c11010504050c01020c0613060e0d02091906050f0114030402060c12040510052d0c07030305040e0901021c0b151908060111030f03 72
    0x260b074000094510f203010320301c002d0a0740d444110040d030900c2d0300078080d2a074420220013801020016604078243c81b4601d0042d007042c2e094001895240c0f81001c540ea0074064a460810303601309400e000c14081c001c82c440b001c0300c20036000c44511098a01c140501d030b000f80704249007031449900f0b04220060290091241464000308044c100c10003650004003028800d42d00c82007070030020303106084591540d12030706014200c1100c3e084c0c011104032000074031540f90202d04000c40c400201c0404c0440d00d480c010340301c1048034003040d0f418005030f6060400755034209200d04be00ca4003404600104650154048038011300c07000300700d10106d6001e11502d5802c85881100c46100b070000b00305c2918080800c0c42040d005d140701e95030b0316603520700c0c04d15001035450b406804440640d2040002902c0070426021005501260f1140130400c0c0010500041459041507880c010310170000400c1e52001c01c898500820840c1341ba00c40e1070294498000440307180c41500090308981d80100041035241038130801855100c415 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 962367715 1250 962366465 962366513
    0xc010e0d2007120b070806151806211510090324020a03150f1d0a0605031c020d020a150908090307060903050f010b0105070f23060108070e090604 64
    0x5941003c01e680079103100142c074158007180612a0480c0e01018058204804813441c0602e510581c0700350300f40b882000c0800741034201e964243e52036900c951081e2413010340708400106444090500c046040603080310070701140d95003030b40101600e2034001e982d00802003442d038135172611906580c0e5410f0b840b541000310510701c2c0085e408200d803600c80d034002400348151079500032417109054402c1103042d803101c0c0c000e02508651901c0c20b01101c6070f0b02c0d094046041c10001c2081d1a0b40740d030340b000300081c01d6a80110f5018000d03003401e4001104a030740c0051440c03c01d070342169102c0030185000c82e11031030300b184001e040c0c000800071404040c0b040d8100c607603100e006403080c0386802e15400010f07140100c83d51041300465694181001400f105000c0e441041b001c070002400005981e200003001803003148802004064000030030002d10a900208e0b00f01180000401c020f100280072103603135500001d100d12002403040e641301155502c40385050500501703082006010725103941e07451a80310700a100600d400148 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 962368965 1250 962367715 962367719
    0x15180806161418030c040c0306180e0c15071703060f04050f0f3c01060f0c02010f0302070213050108100c140304030c1e031803030c06050a1e020c010e0d2007 69
    0x1581e4451007103c0d0351f1035100010394901e0040107208840404003641d0000e450f00902220340c545c042080f0054603411201c0351034001c034000e0107508074040d040300904a100b10705010305464960600950107000c0c00c07501a03500d0300b038020400c0155501100d0f00b50301c00807000089056000300c00034103034101540e1003400c9000944498180703506640300d04600e040710074030380f1391409000b40001d000e40948454500059400c40c0c00390058407009642000904000b10013044144c2d452003136058594483e40104242038840c106c44901014110a0145402a00410301005000c41882c41442e03e0b1030026100c4010b0100040310300354050700020001d50501c000482060002915400c030f0310040d400c00d180031071450a03a41001080510080c200400c40c865898050010a805c9240400303c917070710842c00700c1c0c0b507541c41e00f020014004120300d030354042c0909410202212801d4000c0c0c0340c03031043c40c0000c0003a0880030302000c2c0e450b440c100907c1c000c078100700b00c800302100c0710801f2850040740c900200c9280c0c80e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 962370215 1250 962368965 962368969
    0xa06060f0f0516050a06050705070c0e100e1f0503060105010909020c010f0c0216050a1d040611030c070302060c030f0117030c031306081b0415180806161418030c 71
    0x1010180f0121610b800c0b401d004c800f004404d100b110340000e91071510701c0c100025551800d04940741ca000d01c0384c0502602001480b86410348060001400c0459484400d505120028803010b5142c480c80016100c552176001c00c441c10b001413014101c907030507501c00e40340501c0d020b0040025401002c203442155200c1e0b4081b401038010f802010240c10380c42c5d0040003401c3c0050001308401034550400d0b446081e00040030050708510807032444240901514402c11520355160200082480420083d40f00e0804030800a50342200006054a18000e400381c45940e5905c0c104103403288030031140c94031015040e400500100e4030040002502c100d1590440e443c0c1050801810324640164400790906500c840d4240a1940e220903000d81041410307100008601e10094621418003541c000e210030741d00180b40c0c0c60b4040d4400c803182448005032251024103103481e44d5a1549610041701e91000d45c004501c119808503100d002c0c0302c80c408410324003c80c144000c1c0b0204000718400101c2c103690610034000c0d003520316 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 962371465 1250 962370215 962370247
    0x1b0904022214280b030a09020406030308090d080f0a0c2c0a060e030a060e0703080f0a0306080601030c3b0603010506010201020f0304110d080c0f060a06060f0f05 71
    0x161200368502a01840450304001040190040900b02c0305440c83c0b00a4001c140c90700f41c1010354030300d240d40c80c0d1269200c0044e40024001030b5006540305042c04000800d00d81c005407520301440208040e02c0860702c00030000e42d0100c50580c0d050320b5030212607000401920181d880554108814504540822908401130011010300c0701000440712041c4c1e40422540fa00000742c40060205007401c000008c50200040d840300c00081010f41003607211080460261400d104403400b4613488501c050700c0b44501035008045030400d14038807000c68503120b00030411400002d82c84c0d048030b03880402481c0807810108003180e12845444c9901c0c0108803150610803c070780c1035072508404148490512480c1c136190080600390f620240c19075041d648100500713001406204101c0340d009800c620003020001d160004605642001d006c06441040701003900000e144e0003081d500e8103000b48008882a507100c2c0091142124698440c240c00300b0303144684140b4990040103003100801c0142099410034441c5c014044038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 962372715 1250 962371465 962371469
    0xa1b0e070207050102150c071401150602030304060c0201060503030a030e01110415020d1409040b0a050607030c052811010c080f0a17010e041e05030706141b09040222 73
    0x5a0002d000c107010559040000900c0a500741510000a0500d82203108003131040d1840a4a400d000c40c0e0f505e500c0340001d4008840c03035442c89882941fa5036460000a4594205440480b003803810b02000e02150b500c1406501e041d118018007071032030800100e009900403e59441100c0655494040d410303441c40740c00740070303000600028011031300840140314000d040559441541c1c045c000316400907407046c5960000d554001d0002d85000074900b100b000010070740c2441364010741d80101e0014a0004140c0d00c84401007195106108568035941070802c01450840c0441c1d03002042d4440b501d860300480c840441d02c0c0710b058818181b0043e00f00f0325440e0239109600c28102a001e01c0000520303901000da100d55500b03114014500314410755418000d2410107100094000740980300118003401d90440ea0002a1001c1d581c000d044070b07580c011701d02d4030304054400028000882050480058001042211403120180d100c0d4520b910b06050303001004020340090644c65442c2100c0074601924644040503140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 962373965 1250 962372715 962372717
    0xe1b0f03250c0b0702120307030b03030c0d0315090c0813023f060412030b03031309061a0c06240d0c082e020306060c030a030f0c0c050a1b0e07 63
    0x112094090416a000e541c016113210300b154402e03498004181c80d00000e60340c02001c1c03031502041045400300002d00e9401072444c040300f580500c02140181175015800f03040601c000600108420755261202e00448050f03a0041011909810004e10b403410f00700048200c0c0d510003042d0061030380124442e1359400c91140c01005440d8003110000e40030500c07440784440301d0780d0740c00000d20071890300e550b88150180916482c003003030580340c40200c01035030340510a48207005002c070444114941c0c2c4d03070240e00c040c0400340324089003030300a0314a50040c48040c0d001c0310480340d0010028103060b1100000c007001080d601c0500b808042e203051100d2000d0b621080400c0c0c50320700644281003800d05100b14039080594103003120000045000001c0e140414806902201c680341200041e2680e40700000f00d101442480058031190000248084180c3d406521140f003550044a00f08042a000801a00c41c3d00380c804000d0201e6110600110028510b0740c03940f42c0c03080f80c680802410565a221310352024100b520024 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 962375215 1250 962373965 962373977
    0x40816060f0b12010c120207060e0d03020a030b0a051f0905121501080706121a0619090b09030304030f15021201150c0b011205070806100e1b0f0325 65
    0xa000d140c0454000f41d4030b4080002041032400c00300002d4544000700206241c0e840d0045406410301105500c088298080380c005d4400e4818200f10003002503105903500c40202c0c3c9000b02521003410084107100580700041c1c6003d85c90040644000c02caaa61508202d08000c0383c060082960348440035040c0c02c0c2e4490000628080c40034180c07929507120140c0103500f41d9404000d003048455800300c101d1000303140303002001a00c190504140b8001c0700440040315041440080c0800020032408404c841c804074555403c002d1a844051702000f510410ba469a81540140014000f0130403460884445500c05c501c52200c401603d882c400c181c1e0048441c50005159038001041000018140baa401c0562032408140c0380328190b44a0f941803c042c002c0010f071018102e8003108000d01042001d01070400b00003100c0f0ba41c50310302c1401400001d5405203030a080788210105120759180010040c003d10548851428a07041c2045040c55400c000d10509000c464030030307101902000700101241e01e4030320303030f0f0f40c2 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 962376465 1250 962375215 962375231
    0x1403041202150703020d05030907120f03030f0606020c01030e0109140604120c02010915020f070902030105131107080306180f010e060108060117090a0507080706020f15040816060f 79
    0x20001161804401c0180007003001510f002036404200c016040429060068407a15070600300e0f4502001500701c2c1c034102c4880d600303420a1000c3c003000c20505030f101c0c2c0e60a12902074070360002e5090781c6644c4035010160f071244480403510360081d0032492407010210000695003c1c0c507107607410711980c9001ca090498012405000c00c0c01a441d400401080319801e004805160079400200070748220700c1420182140141040c0241d4800d00c500310100401108403101d85803640501002035100303100f064420f42030400c41090525003402268040c211030780364642041010744584581d540020903240d84140800c201401a592032610f15004041c4003c03090119810104000b01548000e03040300e0601c0074610070004183ea021464410b20b82e500408514540c8403410114a040080180248180200d0030003145105000400c0b41c120f41040d401c0b1040c1c100c080100d20746403000403010321441141d250024002c5101403008103610000c110307041d001901d654071140200d4500f907039605c150903140d40359 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 962377715 1250 962376465 962376469
    0x10030e03190e010215010b13090504390306050603010207020d0303050a0f0902090420061602090c040b0f0306131404110a05100806060d05040b100803030f010b071403041202 76
    0x44120b0010003800109001c00c00780e01c0320349128005100701201c800b800918014201251100d0320018100704500f803000b400c0c14508202c0b9801001003130141c10300a100a0004801d01c0c0c40c28a03a200340c220900c60080f800c50310795a0240500401498156408000c1c400c0140c40c0c0302414648180240e800013007a040c4002c004090f00d41003c0e09400090a04844501695403007800a80041c1e210165500195500c1907041c0401d8511082e658811008203840c25075804015600041d41c1c8201c2e0721150713580d01d005100940e8002c2c1d00403508560000d00c8508105807100c1c0003550030013001029030340e03a1a441080c030015141c40000169600300300364244020030400c0c07036030042452400c44040c0c1001d410072011842d405500d201c000d04200036000401c485841d61011140480c207200c40500c090f24050610308054003083e10540761084000d0000102c044c0003000303a03400b0301c21042e025a5583d1030300040007402c4c0c1003600300350b90304c0c80452040112004c041004100034401300507203a40c00d05041c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 962378965 1250 962377715 962377727
    0x31609050106020106150809160b0a12050f0402150c0307150c0e0105090d030909020703020606100306051e1201050a0501050f1e010c0f0606060302030414160510030e0319 75
    0xc0040256170502c042800703046503100080042001a2030540844ea0351810f0329403030a5070358407504900c2c004040000c1038001e031550090600564a45800a150442d20134070000c070741c070480b0f0203c00000001e000c00d006250100d10301455419500c0d00a0800005c03075200d50031070b807003000102c404440808881c84000010300508260b844a42844080d0754060070000c0c0651040c22011485030032412440d004060060450001801741060115200c2d00c1e07900c0c0280d510742c0141d4a6a208444500c1c9080a00c2c0c4a4007858050320740203410092110380c5205460038480d140c0350310a0780070a0991b08410300c5e143c248503c074444d0803800000314aa5251203707100f10410b00061030350040b14040c0d024001910424004008040203290000f496605420070100b2003104007802030209003440701c0001c2d5140d142c1c010718061070081c2441d0b21046515201c56503141c040c22004011050921000c020500d0100711749040b140035130401050584488440c10f085511003450300c0c19403801c070000e440480d47d1181c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 962380215 1250 962378965 962378969
    0xa03030513020109030803060103110d1505150910120e010902010e030327040b12010501060818061f090603140f2e02070f1118070e0913020316090501 66
    0xd5107540780105660002803140415010141000500002064803a440fa61202548500560b0310a07290300c1d80f404a580034001e01d0500d42e044003414040403d040c80e0080c00240c8010000620a2500b03002c1d10034060508041c0c0c400301c4c00d100d0016000462800c0c240254030585010500000c0d603251148000b6244400c40911140a540240b104584100308000d000d005810070180090b4078504820014000c1c007040c804031a0000b841310a01c41c501e842c15080a416100035403280b400c0c1790307112900080c01510300701c80300005500488c0401da15452003200ca24510091440800ca039580f41c1101906030780469008540051501c1c141203545141480840302d26052000608000d102040c841141c030b01c40d5400c041c0b503904011b58120704e100181c2e0b044840b591350140381035040003010f0400c020342c0710600e0440d070b01402000c44278000c10058441c1041c880c8101b50ad8800060400e00c041c0103e02d00d00500c08021180e01c1c0f040c20300580e400300640d118402c140c201c0c185400e4100101c2e4001e8550603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 962381465 1250 962380215 962380231
    0x130f1401122d02010c020d0611040905090316020112060e070c050c0906090403111c030b01020c2d04060b030406020c07082407020102120103050f010c0203180f03100c020a030305 78
    0x1a00c00c000d00b80c1000860241c1030354092a080385400c03184d0000404160006500800e503a1904040080d90269500640101c401d841400c101d1543e07900e6801d52a445418124034005031501100030056000703c1e1400c403021549140000e0300d43e00c802e00600e1119058238824003080740404d9442c1000802c03c00c10041038815030701c00c6e0300d50a20070301140700d9032070151005082c009003483c0d01210010402c1070319401c1c0e10280340742d0485140307020080e00134088400154014080d400f000c80090401c00c100c2540104002c6c90984806003041201c0c50b040264003a9590103171316410005198001c001c0607601175401060b0040c0e5902102100914180e210340c425003098125005040c6103c40d1007500d804078800d4040d81c0950340d9034481c1c0c200d00900c605001149026803002c0040180f00340010b80704006102040200507942d41a10140da603409201e18002265000c1018845203080105000c60018805004c5400c5001e4050b9490251004501c0401c010b900450402e02410392500540e50041e0030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 962382715 1250 962381465 962381513
    0x21c230309030f060a1812030e0313061808060717100801020c03031e09031c0f051303030e2d0f0a03120b090c03040308150307090203041401050105130f140112 70
    0x70347c1d61400c8109041100c50516644070704803585810180200c0b80402c941c50300a17003905841d80300103081c480313440c02c02c4a541000d806010420820004071103001e800c107600c2d0041e94268200d9008603075800106911040068030342c0008a400e024005401d900c07903054081e41d01d900d00b50520222030031059940c0c0583c0881d801c203000481f54007104482da4145001020f9a2040d00c503112440949040d40703160084078940001c200050402c0717109aa8510300c03a503005d0100601d40f0784030320b03610741010503c03041d4110b80e08c140b050b4103007214651032060154402540d907181c052009150400c00e0041090700420f1b2070541e2451041d1480c42032846144c021640c0a00350b007000d64015102e4040104005c1c14401c5000101e030120b0000c503081003500700300400302c406c4240c0700c2d0700c490080c0d04242e034100c503003076201001c1e41c0e40d416040c05100e041c0c0d80060b1035901440e40d80c0c64000c0103440d0a8040210f0542c0d1002074049501b03005080e5800f0b4003002c0e0344646010b501e841c090252030103020030002c1400d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 962383965 1250 962382715 962382761
    0x204031a090c090a020d020f0a0503060316141309060c05031603020f0703050318190203011506320d020a0e18060f060c19021c230309030f060a 63
    0x794100016801004d85140140c0307600345031059100a02c1140070718000ba10001c0f40104c14581e0005c000c510546041d02074480c610041d28901110501d01d0140704000c10b051864846581412800780348608841080450f10340790b103440340400c03034404159040010340d000080120a030403800504030003c540d031508500d000c5000c4c0c0c0e806500d018002e40142040800000b0031640034524244480218004058031740c3c09050410f00c408030701d0306ca48228029400c0030b8400040c01300400e04042150b0303d40c0c99460402e4012031110301c0c0e130030030501c0c00802600c45242c088c000c00d0300071000d42441c001c00b20303005070386084015020780601c0012400c0ca00c9158000425215040c0403451140c101d04d00b65111000ca0050000082c00f41c00f408003407450340c1c440d030301d08103036840c00f242c400011a90080d5050010102c0c8814201100140d010024088420784038400240600c98601082081c00007025281040c1441d0000390501022603030000003944118244049403c080c402c8800c02c0381007001c01e0700082 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 962385215 1250 962383965 962383969
    0x30c030c181201051f0803030103020d030504150923030c010f02010b1903020a1a1227010504050d030b03070306020a0309020a0f06030b0d110907020309040204031a090c 74
    0x210008149661a21000c1501c24400300e1030341e41180d00d15030003445084903441002505000f44000c07900000c44202c0d03c20300d45074076031a24000105a40030315014500d542c0c00c0d5020700c040460400b00c11420002c040000207142e0503622200e0915034070927520ba0809902d070105919107880b500480010070045d1600681c115580060200300c1c44100f0300301608141d84030346050b40100089641540c0222410342d40c00c00c400f8000b000318040ea842211394952541d1241c0442007800080e45105103641001c00c00d480c40c050601c05420f900050348007494080030b2404800c05c5035801050462241d5a45030f00034042046000d0000e0b0710262001e1504000c061034400010703907078415a00c0050055540015004500d80c425080603509a40281000c50515524520280012200d2150b100000c1c94140c0d040150b180010f45d5000e5160484c003089042511030301000009a00a0318540a40c0300c00c114031200c81e00c4d64009040190301920405840060000c2c8010940d48020110000707a000001c43c44019 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 962386465 1250 962385215 962385217
    0xa2603010f0329040b07090b0a03020d1404020907120b0d1202010f0b0a05010507060f0905100b06070206070227090304061d01090e13060603080c160302030309040c1407050d090605030c 81
    0x46900a5122420382d2070b0100d0543e00846c50f034005042d000c80002d09c40c00701035019001005003d04e005010000c0200039580311500050507600258006414000714000034403403900c0800600c541c000c00141c401c000f40019440c11031040c030840301030700030407120a2026028811505240120081805aa49241c0000b00f4054142c000c00741440b0300400d0710420b11019602c0b403801e591191504102180031801d05603078842c03c05c0c00c1d0f03c501030f05010313075041f05090980a84001c2036001e0421800c0050a030300b00b20700440c850800d00c00d16440210709a240700e007030b01084c601840d0380002542e6105e00300103008082c88a14103116103580441012540c00e40d13802a0f26004031a50000c1c1e014180d00d0315a003802c01c80500e4400544060700b0b04c58080280b084190040944140c2d40c001c60704403c02034502130884130690b2101070340c550014400d00e4001c0c1020b8005c0b8111861510340300c84045081d0198a10540100070b081d01d50380d20100c81d14a00d03070f42010144015048a080203402c5180450a607015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 962387715 1250 962386465 962386471
    0x1205010803041205150907150e0a03020f120610091103010e0619080d02060115020109050a060515040603060509060612100b1c12031d0a2603010f0329 66
    0x3c00718031642510a0041c140100307002c4980c40d070075010306030034440b40480d5100d0140c000c03800020540d4846a6107507020b48200c40b00e180005d4980d051003480d54082120f095540126260080c4514150304140d000601c6850321138940c0b190140100b0b0300309020041110101c00102ca0289010001404850580d0300040c3d40000203d846000b40b062040400000c04d9095000c00202d01c1081c00c8186400e4001c00c2d1241070f1030f1274601901d08200c0303481089003030b195003c00262491b00400d2101010522a42000d1341c400c404841c003c46102d0008040b404503402ea90050710096507440510946c035409002e03417038002070100c80e00c0384c4040c0078140d041e85130024a00c000400503502c00309201c03184c8945036101c4c800e10390305a81140c00071450030509050001c1e0b078000c0000a251070f04c540340303400a4600b00151b8690400c0204807070b22858ad20440010701145d0486a410005110070400c14040c400840c040d110583c0380206117840c40ca0843c510f074200ca00c040c660001c20858000e0303460000c25030254 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 962388965 1250 962387715 962387729
    0x71d0102150604090804050310021206040504030f23040f03060501050105070b0f0402030a0b040b1524030c07050f0a060b012d11070609060206091c051305090a050601120501080304 79
    0x601300a00d241aa0340f502ca26400244c00d405900030300c40403500c055000e022400091950411250b41d81002c001c11100203c50081c041581d00691030340d045c0c800c41a42c61189102a040009500021115201600152b0092549070a040014400c100342401113500415081c03c007281081026510000e0b05c00d00100b014100781c01040008040d50b40c1000000000c0760020800f49490800d0700f4580c0f04ca00007102c0d180d80d4956419482c01103030420140d0300e000350103070030044c8600444000c402842a80040c02c40b06035413005114420103e0018403001080640e20401440f4001d061f01d803039001e0381d00202c05181800b80a40c0c2d40c9901000d003840c51910020100400c1d041016a40029140500b03224504055840341e03036004a074103a00035101d030003662a10380031285d00da40e8000c1001d656170040c01100350341a400d010486603590154016090032100c180130040788a40318804907030341407012035005418685410501005503084525000426420501071000c0d604090400d0381e64842e620a9407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 962390215 1250 962388965 962388971
    0xb070c08150414120706050609180613021f05030f0f01051509030a170c190203030a1b0f150b010e0d0b0711070806060411130b0d020c0303071d0102150604 68
    0x110f800205101c4411103d1200b044113850303040f20308140c001804100c4805000c3c00e101400304411000340f1030000c5100c2401c80091145030f0701e04441e40b03010f401e0003a00700d0300008246612092000e40d034810700016481e5654054682c6807002c201c14060401030004a404114240107002c5601c078101030b85401e10214190582d26104900400cac0360454014010b81500c2c008021714250303094400040c00170010980498100412482d00c01c00a0320190900039071540c02000841381141c0180603101c01d000701040c0c202030a11a641300c404055191210031200380c0c6011400c4030783d03040d043c46120703490a000e180041202c130403d404599820445100600411114030004080d540b0403e107141c120741c07201042e16200303a540c0707081541c3e50740c080e60568480c60420050300d5601240c0000d48401600c0d90f044500414545440030b12560f22107806001090340810480301800c108100844c06030b109960b07200c2904144c0c040c60040d0040d80d04a040c110f40080b940d8040d102c0e948085c80e904a03500711000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 962391465 1250 962390215 962390243
    0x170c0d1401020a0906030608072301030209060d060503150f07080c0d0f0509100203060d03050a0c08180310020f0406140903070308070308060301180b060f0a0b070c081504 75
    0x205004100380c00150a00758000034910400c03039032201003030b400c0f10f05030f407414804191105042a02c3c4d03010b50160050561403d48000d01d04241400c2c603110301e00060500600e0b09042c1070210350154081800500b2107516204200000d0808002248482014000d0727142c1c0c0d8184a9210b12100720080c04a0041004110110b004140164100d401c0d050360070360108001a0000c0d101070240004032a82c408501588070404c0c039400d69402205d01c103210003040e001d216100b41d6002c0c1c1d1603800074440078003003226030080d070740c00107030440014100c02003003103400c0e07000c40c1c20342080510706070300c0d070000404060050110703001d00c49078142501c080c0c2c1c1c041d082031140e040d55200400d5003030050701103156251040304800001c0c0302d1040014211207022355505940e43d600c60b0103040c2a0344001004160300c00707048903040003040b41c2c0b40751144c1001006061010781803034000062001905500b03e4003d01100041c2c000c01c1000d8040128006d01201c00544942c055120841c01d66840042c805049d850b041914 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 962392715 1250 962391465 962391473
    0x10206070e13110a17010b0703051603090e0109020306041b05041514130611070b0a0c031e03020309010b0306090715050c010606090f05040b0d030e0301180506060307170c0d 76
    0x620f20030a26a0502611192015801403810004000b4014041080000814050400022210f4054250300e40d2450999207500c0302c03500000c6440150100445541d010403034940d01c1301294001c0103001c4015881e400c2c008108001c0f00c1765091a9010410140d0796064501e1300001500c0403503824100c8035520004401c0183c424083d2100b1041d0007007400101242c40c102c03400032000507114195280104640701a10041d503500150040c0c0c84052000e100700c0042c02d1150015000c214424a0103d4050800f80752030041d0391400065840482c0d0017100700302e1310040900c80c445110908400500d05410210100c1c0e0310b075041400f03461003602818600780304950144080322903400c420002080550340d03e00009007034004501a09080c0c504c0b03840005001d00d894092450035084c001d0a40d544148159000d807506c2440811007074041d501c488003e0706850400d075030301e0401d078014406800c90b894001c08060818000350440d84803842940040341c140d0800152410800c041501c910448a41c9418 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 962393965 1250 962392715 962392721
    0xf14064e0114060603190509060403020c06041215091407030203060709030803010308210109090b01060908030901032711151e0d0b0a061814030a111318050c010206070e13 75
    0x40403a41464207009440c0c8c0d002455a2181d8081e82c266140e2244c500100022446a8854601520074030a88000800c00c4e10b500e0440d2440221170004019149544007106405600d00301703045604a5002081507050170300420380d20801ca46020750486007565507001c0c240c001804040c04411000c80d5460960703442c0d5000c020801c503100c008000035a91410b01074040c04560004803140c0d544480001101d07030140003214281c46101001d0750a080300000110000e00e000e80d440003800340060203003903100c0f000c1580b8000c518010080340c05100180c40030300507a01c0002d59100c2c0482010042038003580d0b00e168a41404203031182641d0b507a180d04c1c03200d080c040d000350710406074410790301400003404682080c54100803403560920101c0a5503108d404500301c254088605802d03400410306400040c15900d0400e00e4180010708110440c0d0110f038521044496070303100c00d8a0502ca007807602c01440400c2010b400440424802800c0b5490a42c400030042100070052602800c020b0380c001000e444590 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 962395215 1250 962393965 962394001
    0x90d0b0a02070f1209090c0e0108130b070e03010516020d0c110a0e07020f07031106070213020c0606032e090819050307030f14064e0114060603 63
    0x3801c3c5030300700e1000e41000c45103029070f0300180c4040b92070654001090a07060042521282007a158001d203041c40310019a01c0d00303c020101d40c801c149011107203002403480f03010b49000351032507501d20259140d0380052501710394000d000c480060041004900c95a41e0029460483c0019450407140070b80c194901041c0b02c0e0340d2401e0965104042c107078003107100e131010800d0030300c00d081c15402c40d00300200c04414151035009900010b030800b8040f0114800604202c0b0080540510140080740d00701c542101e20001c0340c0283d0300344841ea40000c4103000d00ba1a04110a04c01c61440303405104444030890504416605a148001c41164803220044144088002583c1c0e0500b0115000c10308507045c00c02c010f110ba072040b038404002c84d00e05600d03c0c0d5021160b02c81c4420a0040d01d0000e460744e1034220402c16402801d0a1880880010300c12010030f01c035040881d6004541c3c0401c0080403c1282c9400141c0d181d0340c001d08050a0385001e0107200c2c200071103009540c00c1001900e01945d2511109a02a0380c40c44034 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 962396465 1250 962395215 962395223
    0xa0c050a030201090c050f03070608090c0303070c0806060108090303150604030b0a150f050f060d091b180c020a030309060605030d0e1801030210030507031d0a06050903090d0b0a0207 80
    0xd0403000d024150103410480103180300d40e50140d403090700e0301c08000082d01900c4c2c180d0342650041340f00b841800d000d034404582207200d002c00c07103085060385400a0b14550108004a440248180381000311aa042080341d0b0098000d00b40120703d8a400100da0f0382d81c0c0001407101c80080320f00c110026403601d649040754041c2d03402c0704804400d443c00c401114041c083c19400c555903600351500c0062040099203640e015141c0040011a90f9006481080031903007010a0055005070b0b900c100100180c6485001c4844144204100f882d80e4540b03e035101091500c118018a4070b030030005400ea1180d40813540c95005941400d002a6185075810240d0040c5541d0f0846078151003176035070104081e40c0010340d0110300718048a01c0301034011400b0310003481520a1000a420a003a5155050224060303080305500075141c1ca00010124122800313580010000c00383d52900e83c01889450040c410540950345d0b01c00140300080d45411507203030200e10034051008015003120092008506000c1035601241d10711608 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 962397715 1250 962396465 962396473
    0x90406080d1101020c0a030e0a05060c0a030f180509071403071d04060b090d2607020f0a03020f0d05070f150906080f15031f1b050f040b0a0c05 63
    0x48114096440c00300984070000300e40c64407011200708905008940e0707010700304405050a0500c03990f05459001c01c540b8030503804525004003203520349071100a030001058503001007081c8a40c5040160400b059010344400b0403030941400b00307044081800150444005850b00c00040e6103050381258002c94007420070b00240000030501c0080c1d40e0203054154010604920303101001c00c0a4100700031914544a061007140041c861110649004102008030f58010b100082d0801c0501c00041c40c80c168006e0000d80c0214040355101c00c0d402c0c40101117800c510142c4003a0034141c11070f00050191401800c615100714250120082005414030a9100606011071403100ca00e840f0100d2540400510758800c0010700341c03c80000e0b00c0e9102d4001030703005105040d0f020481e80c60b141007208550703403107401a130703018451844043e03601044544120403001c04440c000a5180b00440030241034100040f842c03042040a000d90000074403c0012a01111703203071414142c0d01e01c6000d1050366a40030341d080140807405 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 962398965 1250 962397715 962397719
    0xc02030f01061716180506010504080a030c1403070302100c02030903120a030e0d0504141f0c02190501120e0a140709150b1801090504061805090a031d06090406 70
    0x1d03484030754a000d0f91003041910104290304d00301005425040c82081c1d850740b182d0511240c2c02d02907034086a00500d040c50600e02e0a80c0b81c3c85d2541c80e01101c030200f24001401600c03c0c1e41401041034865400e43c1c60040a58945526910b0081d52403011b035054034585a9580c0c00d0040f1030b4000c204803505e008015007903840c140c07a042e11590b4070341c01440140010070700b8030031403139000c0002060b44050040d0544400d410242030510242e142c17030b10044d5540e00480c501c41c1d00d070048005c03840303148150441d0b540c9040740c82510f0f105002c140701c1d10301030300d90f0b15001d0003405003c3c0307a8100005105d02188400d0000389604402d44142c9021020000236001c0c00450880356629100805c94100365103000b2820b01981940c030401200d8034065214018090001303000d40000450b80003812004400140b43c0441e445441d44000303402c4031103070390101284080c4007031112500c6500e8014180d101d1400c3d0007030003000581d51000340080409194106441881c021200e0050380d03036071b0a070360f040b210291040011075 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 962400215 1250 962398965 962398979
    0x30b040c120b01020c01020a0f03050f3106022e05010803190f1b050111030c0d05010b0304080702060a11120c010b0904020604090c0909090b0f01090605030c010c02030f0106 76
    0x1410070a080c0307203201e0901c5212000740d40001001840b025069005111481064130388695a10600100710208031042051200c60910b620180003113110019114156000c02594030200c01d01907400e145040b601c1000c100017071a00891658801c880b03400008404d041e40b19104107c41e203001a0f01080649401d00128010000001074204d1210b1342541c001e803c0c007011415106802e12008520001f1941c048103034144070030b4010203441a10810000c600b40107800903a10345a0400c40d1440f83d050004580a01d00300f40d680246801800000c03000c070719504160315103401522440074007a00039640001c1081c0141d1040010080364500710066400c2d40c80e031803c00c01c54580c8030418210302c0b582171040e5030b0032529041214a000b207500800523441d0034689604100501090030100341030140c03983c0009804042d900464030180c2c480d00703400340b047c94203020005d1a40410707041001280d02d400c1c81401262800211300802c40c009080c2003074820003d1001a24044080750a6400c42d420700100113a86 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 962401465 1250 962400215 962400227
    0x50a1a042f0c120a200303130f020904030206070f03020f0d0e15010b04050906040e100c0306081c090e15060d0209040905070e0a140f070e1027060f0f030b040c 70
    0x300406950300c4054507002c1c42a80c028085d0408450001d030001c00129040d03040302d41100440030310822442100c1c074010b4000400c1c501040f00d080d4096005003007046000d503880b040c1201c03820b034103050031400c7c842c52000c80c0003240a0a00080303c5561369400310201c0ca0402c100307004c80720500080d860440d6071200c9038452550050700c00e4600030840d4001203002c07498240200c2c00e070460044002c00c4241c04103410030001d8090205004203060b40d030500407030001001d006150100081c801501c10386c1040d8035000b03110340001c2c0d001c0301550b002328061002008070040310345d080c0c030701c00c540705603c40900c0b074004130080c4503010315103521a03e0b01c3e4006042000108641e000c591101503d0711103682c80207200400d803000000b582440d8400c0700e0004240c0078002400d29008110f80c54800c400000307200c0802c540c3c85200780c0301c002040d10041c0c80c2800401c01e284041d003400c00144003204051601310080c013007080ca1710260041c4118500341d41c002c24403079480300c085420000c106201e0224507810107081 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 962402715 1250 962401465 962401477
    0x6030f19060f1b0c02040e010903030b1f0c03080c120103060902010f050a09090207291005012102030601031b12050c040f0303110c0301050a1a042f0c12 67
    0x1c8508000d01c100700c1d20480d104000c1452900c1c03400321500070642d08112850014640200ea0060342c602030380c00b02c0182445030501091280d1000102002c0182c00c0050140880d50352041d0804448042403c0e642e00c1a4000202e13985424413010645840d45503c04030700503d4800540102060000801d101041d0040c0005034000e807903002d00ea58281408885602c02c1c030310713024041205d15100700208029075008001d1140121003072101c0380d1f494240000702102d601c4941e40e0858131001030202100902c90303494014071090071f00620f03103a00200141c50525450019495040d40400019000d0b40240c00403464500000342881078070316908000740141b046100a0341c0180c3c0340c03000003040c003003400e41280c041d01c080c0861115a203107155404c0741d154140e0828100715001f8800f030061181c4003402018044e003a03511020078031403a0803d2000d00503c42c0440c413032003141802901840c2c0c01c104009200070615440ca03e241114650394210524418440e48004900c1440328180300035040002903d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 962403965 1250 962402715 962402723
    0xb1905031903050d1e0509060601050a0c020f0301020403060e12040e0c032701060f050d05101104030803160f02030306091501020c0604030b0f011707120309180905010b0402130e06030f19 82
    0x400e1f02c4408040b552810110f9240b80414401c10000d60720f02e000e5503900031030500c010160400001c034080803a0981e001755200b00d4016032140c8403a22182400d0225030b980e40038807005a81060301d4425940a10740d0045d03d00e0030000000000f0488003c0c104204095500c0e0840d44c00284503030a540c035500800044c86007200900c103850012806180650000b800e583c0c00c00014a640c07014014500c0050442c00d10030110044e0800001000038a0100550300c16078030031411255a1544440c003a081c10700c0711110b4000c40d0000c0040040075a03c078000b041d04500c003503020090034120701c80140d20700031020b0402e40e441040841c001040000c1206100c3c81443c22403a110126642c82c1144681544d49e0203048140303400003c000e0094031185032040381138034007901d0065100b60703803507003070300b101c3d102c0d0310305070027044d80c884507140c080c400300b40201c961541040c2c40c00c51030102c007230081c0d0300e5000c4640545440d25210380d0200318259010821000c44c06044019148840802c3d449c0d000d100c014400200c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 962405215 1250 962403965 962403971
    0x60409060b0d0b06120703020901030b100f0801020901020c06040b160503252306040b060a03080f070b0c16290702390f040e0105010602010b1905031903050d1e 70
    0x1c0105c40700800d8040851ba80030341881d90303c0e4210f40d03072074541c400300074000104024a1480040c0e50f01181000b90010b0400e5000142e0700ca118130002400d206106002900480c000c010403c040501c3d07004170b4100c003244d800c50304064034192401d5801c520600b0781600050a8076850201c01d00010880c0501c1188a11851b42d094500012150010100740d04010203035001140010003091076144516401000204100e902c00d8980d65012900e4011144c41c00c9209800309080040040c00c80e8040e4001484a9441c1d06003d000b44510706180d00e101401400702241507042c00e541c909800740c0140c84400d80595601c0c40c030744482c0007541c3d04503603500ca28410090400800441510f8840c80000c0e0074801d40c101203018082c0d0034030104100e001c0904ea0040e60f1902c20204402081c071901d40a088140c1c00801d101c441c100030070200020440c40c4030603a0440400800855400180302000451000c1440071200031a050a440307501580b2241c0b514a82050060360101c8000300c101001429261410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 962406465 1250 962405215 962405239
    0x8060105030109050307021908030a03050405060a0911060a120603080a08011403030a14070212010b031b06030106200604060b120a110108090f0f010b03120a08060409060b0d0b06 78
    0x10700382e44074080d014110317803c200b209001604144201c20a8000311441c0310b42400d030307151800c52940e400f465482c00065956024041007002c18048141c000c81a4802802160343c030742c0380c001d05e00d00c48440761481040e0004da1009605d0040c0c500400407032410004010090760b03400c045100c1e0b400140c0410014030381c0000400c0c80e980032b452203841514080e00035414125505415100030000001002e0180410700c815001a41c0c0e1603500000c0d82040000400c5030300f188024586050285d20381a40c0074200c40303000340304540b1007070141e81c1140d02034503118400d44007001982113411901c030f80d011864003d0004020a01c98035070440005540152121a000140440030b41d48034880441e00800c40c0103401c0d00000a5071040c2001a0014400e5007681c1c8100641c10b4143d20b0100782001000303841c0d444107454000c40c41c2c144644a90364101441d40742c60b203045800d0040c091070004180c0d91140d0b83d10491682031105680c000e40c0320250107002c1c00071501003814107288601c07007220b0702071040c0000004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 962407715 1250 962406465 962406469
    0x60902030106050a0e0a0218090702151503150604110f090901090e0c0d061811100203120c0a030902062a0c030a110607020316030b01150507020f01020f120408060105 73
    0x4100100d94403085c0d00f00a0307072240b0124001a5010450381d05544107503607420002984d40c1e0300c0d0207015000d66002006809200c4400181000c002042d030100300803650f1008090751400b007080240c41d03d01c0c00c11030b00300c0d580f0280003900034a40c1c456454400c010101c4e031904507001540c02444030001c219502c0e136050381d0340c0c200b03042501c441189400990300b01081784161420041c8400080318495231010800e01c1d40c5444510300008181c3c000d603140182003110003078500b4002c20180e4031812520185184c603034110140c141111016101d9008132134005030200c00039100360301c502081079005004550390000c0920301003a090304884030103e04c4040386002030302c0301d00000f030183c0d64038009405400f129140e5200c00680100c1501c0046d0800d004100e4000140da05200c41030100e40508420f100550460401d058260b4050304401d1000b07901110030322115030060199400c0d240d044442103042c40071000100d040c03685126403071070035118000f9101801020f180140c000d0701d00c00c0741101c40720385c3e0ba142 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 962408965 1250 962407715 962407729
    0x480601140a030f0203010915150515160c03081b0616082404050703050f0a05060d0b06032401051e131512120f0c051f0e070306090203010605 62
    0x256003a030095541e202000020303a2074407554980382c001400050f2880441e26032660b04081e0140e0b03110080e984119001415074240d00e148017509060300c5a9552001440c0c0351942482110580c2090700d0902950341c0400540780c200d000990348c400625500c44130900004030707180d110080c03071200c2c0e8003e40000130959681d52240b001082c0d026524042c5a0700c0e0352003c0081c0c1d201d824513091001354050030308041504c8038003499005d90059a80041c140c94402d011000c911400703880b061041d41003000380207850b5030304840c48043c280c02c400780c1403694481c08000703071a01203036582d00318103510092003626800860010b0301341226019900e0118a003c0100030850b0404960180c80d404011807000030b612440c5544034404175020310100c4450507407546241061303911100f0080321445401c044000311542d12406140d041003190a21000b00c08280c0d07109034403031560f01e44184092103000b0244045103003c4c1c109860700c01c0510140c0c1d190544030305091015000c40391042e0300940c01c01000281c2810401 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 962410071 1106 962408965 962408999
    0xf0f11030405070f03050d0e0f0306150306130c120302010204170106140411221e1508070516030c060f0203150102060606480601 57
    0x454450b01d071001d03c0c0c0258000c181880ca0420000b040000d00410400050914040d60340d00c06010800d10440842764540c103100340428030840c0841024040b1041400380d0a0b110240d944101c0315000f00c0d02d80030000c040080000042003031011800140b00c0f510b00c03d00c005803910740c1e601c00251100388444e004540513592035904006002c1c0b0704034956070010050702c00f8045070802d4801108103004442c84078098108a80310741300c0e05c04000c807501c8060000b40c80e101106011066031076040306402d01403c0384170043c0c00300e44820b203401340040c280315640d56a1001e2401d14170881d940d4160392003c00441c00e100071a0384200003c0c0c0c850003080302000039400010780b00e1801d142c1c00e1400d0803103a400d050554100704203000e00c072348070041181c0040c8641804002e0620340c410011313140c22901003442c82ca03240004944045c9d002030420240344c0607a004100c07400b990f200c90310200302d00010 = true := by decide +kernel

theorem cover : BRFrame.Cov 962230215 962410071 := by
  have h0 := BRFrame.cov_init 962230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 962230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 962230215 ≤ n) (h2 : n < 962410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
