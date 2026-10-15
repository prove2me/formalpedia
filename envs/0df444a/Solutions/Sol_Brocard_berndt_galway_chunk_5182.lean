-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5182
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:01:05.710875+00:00
-- url     : https://prove2.me/submissions/7d9b5624-f01c-45e9-bb2f-0b1e2bbaaa1e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 931834532 ≤ n < 932014388 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 931835782 1250 931834532 931834543
    0x120d060302030a210c05070603111c06050306010611061302060c07080115051f0c02120a0302100b0409030c120504090e070302010f0f02070506030604020405060c0a03030c03060e27 79
    0x50180b9000c0944844c1d04065858581410360140d0522584881c2140824004205001112803506010400c088103040c0590f2610404100304031010a04030344a441e0a00d680c0510b00f540d9094048800c2d907600c4034401d6540408d5110b00c02005e92001c4009034030350b01007824110899102802040c01e0100300e440240c10000160028000b80e0364a160810380c05803129014402040300b912262601c59461f440361a180c005e9014207424004510071030003c5403108446114002c00c51400c0c3da5110802d07103030081d00c031000b010468074014108101c800d03092805102c2c1c2e195207036042e213900004a00d0303951409003400c100c40791001441001d000c00500d01c0a01d008524052040d00e000c5c01c0c00c141544000342c81e060141c4607034000c1000a0710ad51101640000d103000640300119015501c90b5034000025010b44030300e8029a0704005c0220300c0140c411000281e212500740300e602c041c0142060388a00300c04854007880341100303400200002c544410340c42003610007a80c5204a540100c480c407249000e1420 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 931837032 1250 931835782 931835803
    0xd0f020303120f070e21122d09031915022d0f0417010f14070e06031608250c120e010f1101090b19050a0905120d06030203 54
    0x28140c0104001e00d008096050640c000014200b061003150700c0404648800034046010400e411003800035041503c0400030f6044c1040840031448d03a61500c10800c503a02c401c00342e0301300201d00754030b02c0512100c015030b070070b0b13840c900b17405401842c00540403541000d102119100a88203150030301640c2e00c82e11030710300041c1002000e0f880c0c6d220070702c802c2da00d131120f240c0120391005900d02030511000000c0850300084400722090300c040c542d0b440c84658051401003840c01d021481c0303c2c0c5000030160907002d102d41528030488464948a80720114081441003600c8200c5402c00f0603910352070b181048502410203ea00071202480341e514883c4d46031520883e543ca0103d51202103480803a66008105d0042598031624005e880c0105c500c1805e51300207011600103410000a005030201c441c41ca03c2c0742540010b032036540106034400c2a0801c0b44e0318510003400300c56424031860030103002a2010120b03000700e5000c1d941c040c00803c007100d403084510f1120b41008045580369519018000056070341005000000d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 931838282 1250 931837032 931837057
    0x902060f070510020c0d18080d1715090118090519150e060c0703020307051b030706080c030103020d2105191704060f06090504050304031e110d0f020303 67
    0x125800750500900d044034034201401c40500410600c0d0126a0200ba441d1710030180307040c6440c418042000440794002560461010340c420012907200080d030001d041c100100c0002606a155107c2e6000c40c2c10f0300040c1c440722600481200010442c1c0040b480c24403040c05044100006c2d082d220785c0d106400d201010008152519050440300c00380443e134202c140b100da0342d030032080100b29030b0340c80080e841e114010f1820344500b00208542d81414000e208481c070540d4400142c4082c0158030301f800c0043c00c100c47c5083e00034031031410302103080c1d40200c5456002d1400346205c1030640c2e185500300030b043c190800e0100c1d664058892a100a1064280c0c56041615162112030305c42000700103845032003413040000b504001e00cd040102072142102102600b041d0488400b0815010814005001c1c0203503074003801d500b03443c0c0b00802040c014080060801c0c0c0380321360f40e8016284c00a4003480445802504050005960b0000e95109403034400301e5007591500c18200d80701d9540f2290002825030708a41d1300000d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 931839532 1250 931838282 931838287
    0x2e0302100c0c0324140121080904020708040b03040f060b0d0b070f0519020304050a08070f150e15090307060203040617100f1203080603031c0f0902060f 67
    0x452400300e1105400e041145800400380c0d80320b445944107550107101c05010102c045a001c042907252200ca50350316500d0f0745040c480000c2d401540040080c00344111403c841141c08041c0455110030444107485030054106030520840300c00300300007135000304002c036100307041000001243da001c48003442c4114004c52448601d1981d07820990103503030b00c0810280c450755019074002c00088010702519000541803400071203107010340c8002d4800c0e00c0740d440040c5c920241c001c40e100400754004000d10542d1380a6402e07000f80c980d104807095407100e07075008940c02c2120070f0500b0710146004800108003200c0601e08001d00001f032101080115681c039160b0014480b000074025520b040c1004101c0040c0001c0c4011032401c2e140076801000100000040c216a0341d0744004250504040d800c0c00c0043d102c880790b06101e00c0d541e940389251448220740102c0c00710781c0c1c400000e00c20745004030a9441d010340b910303010480d640907445810018048541c03021030441e5500254400750b240d140140c59032007521613401341d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 931840782 1250 931839532 931839539
    0xa0c0909180c3201050316090302030303010f0321210207060203010b0301060e090106121a0306072607120f0e06040503041e0302130c1b0c051e0d0305032e 68
    0x15602050f002c810060030380b0079010340303415903800350880368001c030785002046a0810080e82150150301c607071f01c0658507100200c0085410300008800000f140e104004418040801d03d860700740590190601038003184c452030000c0c569007886240c40742e24000b0071000514040c210303950641260801c0e0000052080c0100050140350341040721500203d0044845e0070701985056802071071b441c019180008503640315403400c82042c0900300c89070410b46008090b9442e44c600480010150034031803034510720050401c00514440c0300040c84042c000e902ca640c50300b01c100e0501c40000007a1008146110b10203542e4142e041c404002440900d0140348224051566036260080c440044c074543c610401400d40c0000b0f04000580e151001c3c41c08030000c20348003155104480100b551314420b15112291448102842841080803a04403203003560f504492030740c8500d0602000c43e9214400284654021140c03040803008280030740065944940c0700c0d244880400ea401c485a80081c1100f008494016a003040a2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 931842032 1250 931840782 931840829
    0x109140702011401173412050601051917070f0602121b070305030a1106130308060f2206080f0303070c030c06060b04080c090a0c0909180c 61
    0x20340002280c80203004803030f00100402110081803050176210141e00c03000400c110360034000418074008016509038620041807901414150310541944051021100840c40c0c207100c0c2800c40350780344c00800800781c603824501400040001c446680e111016510ba000501807058480030182102001c09004024985004400410503580000e41590451040d05c9800005441070b036100300d0a0384098161000350958180c00c03c0c00c1d03600054243c0c00000342004000740c101605800d010f410030106d44031075680650282a0000b00d40000b030019030050042005443c000c10805401c0d00014514940c6003d42c0c028886e049000c02007a440040c1c66440810280005220300c981d00c00c175600180d4994503021500919080081c030000b410f00047e20b020505124040d4000c80241410841c0300d90344903241e1800b56a5960f140c9205886540407400141c407114003802144950a195200c02c851942000040c401a0000320000901344c0200940300000c510903000c080000c11301041100c2d480d107090880e1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 931843282 1250 931842032 931842071
    0x40f0801020d111615150e090f01020f0a0c060605040203070e040f200c030d050c1b0d09090b011106070e01080f010e070f0507051203090c0103050c0a20060109 70
    0x30209003010301c40401903005290013503403c60781c8000d4184440005400400c0209508040912020035181001c641c000c0c039110070310b000c2e1040c0c40480e922045902c101d20300340e1040100c0e43c01d6001003882a1500540106042d0748003500ca284041091900d80c3c010504980085440c1c20011721499000951070610b4440c06088800c0d541d0188402018040400c000c1d0544481d400072083c0005440410503205006480544071804001c0c065410704058080180d004401140d000001640c124040241c3c0040c04032080c032116122a01510f241080e181c008184014070340d0306200700358120b00300f20300092040f148900096100c90f201003e4420004104010062010940c0d0f4030020050003a0007003d03a80035400000c85c94000700c1c00200780d100325094019900c0c024203a10501d0040304002030400061881002080206d0313605401e07000046040e103c05440703208524604000e035102d8030380301d04903044544080340f101408058180c004185840802d9001e5503c841d51104d0350b0784209603003101c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 931844532 1250 931843282 931843301
    0x80307030b1212030705070611040314010203090717150c0c060601080702120304020109362c0102040f08010c09120b0f09070519150306150311040f0801020d 69
    0x400d242d0240c141044159240d0b411440040c40160200000311340a1107a0304441c0d140da801034060100c86040680042e994000340000c0301c090640005031954000140300340c0340318014000080c000c45181102403104c2d411200d001c0415400344e03507050340e0010a200e690500511034401601c1e036812003900d41c01c0c10403002905190422213603406000d0000c0c0d0008480d5020100c1c032420b966a0707100d5100507240302209610040100780c044505078480d03203a4000d10008405500c0500086482442d0118210380100320a4205080403100030410f002d03025440a9050030094001845c00752900080780b4414130035400a11103a44031103001c03540340d0380522000000e04d100040300c064080b080c0d4a004180324014070342002c00d8000000a003101900b0003001004045c0a0804840790f180c0d06e6590b00720074040d0142e032151061a0541c810303030310700c070b44241002c64169801118809200d2402140179002c010516244503100307020100f81c018001d540e60700201710510005039a100f50300c250000303441d12144c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 931845782 1250 931844532 931844539
    0x20c0d05190302040b041a04030c030b0601080906131b0f1205010b180402060c070e10030203210403080d0b03070e011e0311040f020d0527070f05090a0902030a080307030b 75
    0x720800805d14100c0136203041e10010a40002800c4500b101030049000d143d0000c0d0100c40c01080010600030f0b8801450f00488081c0d03901512655480c1c4140c3c0d036801c0a0b2801504892400c0010f800300e004100384818504840305416240d5982d0000c10001c0001d0390046030049100e00d01242c100042441003d02c8e080003950746102903855001c0c030040940000700045c1c021400011203e1201005100348805450794901c60000350a00e8240c0c02c441c00e02d00d0001724028440c90003100080103002c40c0082c01c0d00540b070525860241903a5604260741c10056501121300c0c1c903010b02040d40d64091000c0c50180042c03c1c41b020700c03589004c1e5640c00605041c103082c00c0041c101d050510100d1200b091003900510305440c08191040000300358002803042c0c094600780c4515000601061100d0150380200244d2010846a4454450040161160010700c03d5401c0113034003540800450402d0a0344503480100303104000741c03000c11038000c01d00b03109500743c040f145000b00104010500781c152085151585056 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 931847032 1250 931845782 931845787
    0x111030408160528060c15090804150516260301080d03110c1c05070f060507080c03130b04080f03040501051f030b010e04021203040f030201021b0d11010201020c0d05190302 76
    0x2c00c04c5418103480c040c0e041005803c140703120600c05405492070b070001000c030040002d0b19031820640c2c01034105000d240c14500c11034844046407445182030302c60604002d00d581880e001c40703940308900b2031400c1c03500082c05060104080c0041c0b00e0000514000c1c4440c001a1182c8110300c08001d08951252b01c07100450708040c03000c040400c0000413070108100750541d480b111503a0840058a850050a03030040c0921403070640c131310400c000f03030308818010301c3e2648460b00705407200242061680001c45038103498481d400344030404103e0000040350001c1c09140503d00d00a10f4244a4800d60700484090321140c0d160414041d08000c2c10900350300560019074661021b905640d5100c220310070600c18a01c9010160000c20309650725441d8081c0001d10b0301003103070b5030740d6035a0001c0320110881d40f0041e80136020700f504403040101006915004c00314000d00d010385030b06090b41c1d40d40502ea45210207038110342d403c1c08000c005031010044103800d03080c41e4564a89072100f2483c0d08603003107043c90000c420140107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 931848282 1250 931847032 931847089
    0x106081f080d081005040c021506040b090f040218070e010e031f0f060506070b011404023a1505090a0e0d0c0f06020406090612061401110304081605 65
    0x4250000141d0640c0f41c00d00d11601e0f0800420340c1c4010701c1d040141d005140602c440302c1a81c0000301d4024074071490007480016034490082008079210043c40f10b03045103004001a426500030f8190703d907c2131000b0300b501112200c55aa03003100c2d40003100c003103021400c1c80b81c07020000d40c0c1090009503414000c80c000c204c0f140b014900006403e8180345041e00356621858603115880143d0400e10141c0006040b864036403c0c24102885094420f100d203000c607070150740c2001050b06050003142c0c2002400040480c1c02c03c2d1401410450121084110f8002c031a081d400007001c4000c0d008003161050030380d55030090a030030320041015242c805444440c100b4640a030318813100502182c1c1c900800a181071150300450941070403c0b99481c594001060319100140c0402e08a4028044206460301035490714120401268071008a801c0b9003e119086500402040f0b030940c4128540b900034019101640d0801da42c602e0030360b117070409a10054040c416a04c000340014140002107e000c61600342021070710110 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 931849532 1250 931848282 931848299
    0x1140705030f06031b0d03140d0c180605160203030706050a020a0e0409120e0310060e150609010903060b131b08090d0806060d020408031303060c0908030318150106081f 74
    0x845e44080d00640c012510b070418075006101c0c5000204160510740d03502c003030000c50312001313001c0c182016002c24040d40d0000d10300304520038040305850142d01e51070304c0c0c4101c414250517560b00c0038504070b0349840200582d20028015006182c05134104040168540f48a00740180120501c821f5040c091031034007900c007001c0f95008140014012041c1050b2064032030200200b0b0034105604e8403090000d04203800015005105907186121303208402021080344000c504020031403081010361400a061008240041480c0f9840180400e200401907411101c1c407813001c4050f9055208207000002d00346802c5200c95820a4107140e0014061000d40782000e2180405031400d01c1c081c000901414020854900d400700c1c079412200036081403070881313444040e941410308a500190000702e03034150800c105080e102c0d014103007800c1603406c488065421a42e481d1b00c86041004000340905140c840c110554201040e0159a01c1c0680303056a1070020a1a10940301a88030101200e8072a200041c420308100b85032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 931850782 1250 931849532 931849573
    0x8010c032306030c030f0f01050106110d030c030204051002010902030601090212130305070f110a09150e150d0c061107060504031101020c120a0201110601050d031101140705030f0603 80
    0xe8040c01d0800749030300c418000c00d10303205200e4001c85c0c0500ca00c02840101190026002e416060034400034011682c81307080807500001591000e44a41d4801640181003038025004007a003800c0500d0018145950340d00050310107280c41c914800980d644601c1202903050a00149014101c000070940c60034035900540955814000e182c840f02d1685405168105445030080b1030705580c0040302041d0050450811040c90040401700c030f4460b07014254000f0343c0302254062407400003060102d501e040b929000220116200007800790000c03004001c501d41060b031f160765681e070015004a0a40950300c0c00c011010306811110001d81aa65100f504100b101035445022541640d900c8003404403101c5020f8011b0345021030380300401d07034403114523410451958400600300300c3c014001da0322401000b031440c0b030711516820203018164206403171f0800040403038042e01d5182c1c1b2508003200001000c1d2004c845100142e44c0540785940011070000901201d25039005103280c1000d8102d01030700c40e989440102c1401c1c807 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 931852032 1250 931850782 931850831
    0x305060a02040f06050a0201111b0d0e1c03020705100509030f070e060d1e0303020c01180b070c03050d050906010f051e04320a0516020309010c14011508010c03 70
    0x44000110103051602c01e40089c50008241e0520b10380300c04058a41154103622405101080d210307600c1084080c0e8032510b0900b00c4c43d14050308180c851044420300f0709960f1251305065042d88a04e600001f8691603403031039030031104040c3e61802d0319580200d00701403c000b13866105220307035400342e4014800b2401c480b5100760001d0381181d815442c0000c2d07180c075004060400c1c40c0558040001c1e59110b0605070150000c002e0303d100ba0000b0000c40d40c2501d40c0111074000350002501c0130000c1800251840c0c000c01d50b09210a000c0d0a1042c14085d070351030060241c4504841007a1070b43c221400402882c15540f9000c005444201c0d440d500419504940c40b0301303450064070040c0f007580c803010304a0b00300410040488080c030020760407c80c80d032843e0000000c02e480980b05940c50030b00d004001a014111600740c0320a1002943c0030354500300b41d007801152025042e04055900307002040d40003951801c2407007080148e6803801c0e0700740200e919001d0f546084070f01501d808010305052185881440a8145145034503 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 931853282 1250 931852032 931852037
    0x2060a0203130618022b1e080406031a04092118030605040218010e0c030406150806071103040b0a11010905010507050408071d0f0a240305060a02040f06 67
    0x80ba50303422032800c1028210800030b04000c1c58054288041e040780d0802204c401c1c002e68180880701d0101558048010030080768038071150400380e802000418021660150161880440c0c0c500303c400c0e03c07128010f81c0203600c22000f01c0c0c3e40d01c1c3c0b03941c4801c0c4a12242440258220350400c00401c45884d4204442010030102d903d88900411014180d4040d84891401214072409140c0042e100d2510b00c0c000d000507030341688581c0a886d404142200000895410707514500b10050181d01e03207a045449581014000b214020b4880c4914044104450542c0000380b04100c02441c3c107013400b2402920343d0002c02e0404545800401041c480750b00c4000855000d4980340ca005094800424441b07030042510400080c01c0f54200030a0101180e4401c0c00362050720303142000d558505654144134a0903140c3c2c40a4034012643c0c00b000200d80008207624180c2c820344a010129a00000300d6000310750b10f5030842c448403241d00c3c500090052140801409601051a040c11440c0a0030b007042c0e06c0e264542d41c440c1004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 931854532 1250 931853282 931853287
    0xc060309250e07050f04091e0608011e02090d0b04080f070303050403170402100c08040803030c133809102c1309080f0301031a0f060d06022a0109020a060f02060a02 72
    0x8003d00240003e24000b840323404c0042c6e0703840f02e240b18060300301c043c4511016111804501c0e00c0111501c2151720f0148001c012003407442c13a41d0b807000448072000340196203240c0180800e4441740d1240740184100c40c440e540002c0c00d403420345005441100001004900e004108003048010707200d000241d12000c3d040d05180818041c03501d000c282500c140c1c1c101904501001c4140004482450043c29801504007060a14181c03145c0e89000700d086031440c00070103024081c1003034181082550018143c00d1100160a00d0410b8203008a9601c031041e10184001503e46500044c04584130b44003110440800180745081e00098070001d1804044000450041d0340d40b58800c0c1e0801160034219591400302d404065182d680d04d080c00c645004075030310300c1e0601140c0300000450104098070220f208900c020030707012540516481c1d06000750042c074040c484500d141040060029214420f000d68816010300100700d00420342706006a80f00b207039101034140300580702c01d424059008200913503c07034000d040058 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 931855782 1250 931854532 931854551
    0x29030903070c0305151e06190320120d0815010917031c0c2708030409050114030a053301030b071805030c060309250e07050f0409 57
    0x18203500c0340c05401005407004000c000204900440d03140c450780e08888a00c0f01c207941e80d0452110080c04865805c0340350405c50300065003803400b9489100039000300003030480d0080d2243e5a00c90b454036a21040d11200300403042e101c1e054508500300405001c400400307401a0720003510040c148000182c807a4a00310341d26507182c490b50340720780344e194001d009010205001c1c007140d0085170f4481d0320140610100c0c6440e0090031020b0840341c00b0310030000703603035035103416082c039410104100c01842e01da00d0100d001c910b1400000d40c524101f003d000513050741c40380000d4651400403508007103846a04458025002502c1e0440402d80c0820020b02d002e102031040e0343c4910410b840c0005024511641c11000701e0b400c0004428884400d00c0240300712600d80354100d01c661007820004996129208556140c0c1c488500640a410604065074102e03030510111501c02303c0891a010b42c02085d041c1e052050b1b140700c0000c00021610000150f0000780301d042c2540f800400c1d911000e054426030040c1c0d00803d40380c1050a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 931857032 1250 931855782 931855801
    0x180607061b09030b07051e091807020d021006030816080409090f03110715050c1504210f080c07110405070810060e0603011e0801060f0f2903 62
    0x10000008005080c0309189900080c02c540c80034001518014400c8001a01c0a801a01118070b40c0601000040d112240c140340b41d0040c0e4801c144d40c54001d405120104580c41c4012035950250b6429006003c1d000310b2035500a00d000c0144026004043c10300c0750400c0822040801c54484040600a80c1122406801d00c01d90b203100d240e0041c09898a0584d080091005483c180d8000a100b0750700c500c00303100584111580c0d804140101810700369800a00d0f9400c500400040c1002003080c42501c2d12843e580300c0005000f54112810340d00c07001c0840c20f0702000c104900c100e007030b0002c0c0e50929100f1285084001072103004000e004107a16580020400c00b1700607504002204000000c106000d18540140000c1003c18182e4030880003c90f0480c1c007241490103080e0682c2034550150a680c1940c0c81c003040400340591404c500001c4444232007020407003403028040d50b805001c02c1c004480c003507440c05200c0100c030700850744544000d4421408480c0791220790902815030300d1003260f00c02c3e03c03602ca40203035 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 931858282 1250 931857032 931857041
    0x14161a1b03030a05040c080f07090f1d0a0c0b0301060206061c0f030909050a06050906040f060e13030f110a06051f090906060e0708070c050c04110318010218060706 72
    0xc8000c030388004010480703180d030b4503040700f8861842104403d0003e0394502e2815030381c070343ca84e03030507500c03a000b201c400e00c041003032030307005007400d5400000200f11804178035494115460401d442c03e0058000074100d80c148001803001c1c4006086000a1500d9507242080c000d40742d50000d8185881040e0419903000d6084841c000c0d50822608000701c1c600b00c50262401415000e207511a40b03c015083c41e00003003030003545205040883e00c015041d51490343e108420000284558100e000503541c0e034003008140e844460070300511a000c4841841c003c1e010030300b40500103150b01c5d80503004200203000815540600400c980041ea98009400324240d200d44041072500b141c60041c84e44991807113540052103001a40106c01c40030702554041019507140c0c410ba1401c0802100d03c180401c4072680480c045078402c0098401c072030302500503904006072100015044c0c1da241c1d01030800150001c420320100d290f1110a800d8030f210321100131803418070020a800120710600000501c1540e001c1007140a2202039080b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 931859532 1250 931858282 931858327
    0x40204031a06010e0a081e030c0607110c091003020d06060b0a050a031802061213050d030e011a01270504020f0712210504030e0d14161a 60
    0x11031101d040060498100900e4048900e140061602c41c10401d00781000c0200070242c560050240900071112002c07401c8581c620071100354684000c110410050074103005040c020140c0365078188511844480d50340c5840c51014425200b40700e154123000350780466030b000e10212070b4140c1d000201c6c0d4030207040c10401002e15520400c40c490300028021500c56001008000c100d859850803c00780c0e1403000a40c3c0c0280ca4244020741100c0304011100480501000e8207901c00040b00031040c210000d6078400f410303c9003c0203c0750101c1d4039945510503c0c1420700802c0042d00c107280b041001c0840400000b00700e00400b00c443d2f003c3d0007468141529051884849002402c0050000e41d564003284824500640c01400240c07070340700303945000c0c0d21103510550302c0c920314480e0700d00341002254810710500b0080c1000b03403044040c010240c42c0001142c99101034082c40034024031445100040034251241400e8803c080c130304000d0010a400e000040e0840e200c0e03544607602000381600c0700d05e40081c413842c0c0e180c00034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 931860782 1250 931859532 931859543
    0x1020c010603030906020d1d040b19060c170c1002031803030f0405070e15010e0a1206061511070905061c080405030c010c08030a05060f060a0302040e0702150c0904020403 75
    0x14004030a05422013401c4040780c1740340e401c86a5035014030f5001c8a00b0008200d40100c10381a068500c038031460290000300700c001000b89106107a03501e900c1301c02144145a030003a408555041c2c4410280003900c0c0e10707103420a9054902e5450078448070851911001c0f100341030a02c181d40400400c8403203500b418080c44032402c0b8070441c0d989050404580010181c202d03003c41e15803041d540e02262203075045410a0040983c50591406550100c0042d40d4007140d03c1c1507603400144201d000a04d40243e0855107038a1230003008d00003401410006030b00d140f402000b400c4002d01c041d50300311241d18480081d0310b034201c0b41d03418030006207a110180003482e180b2017801414400d90b001c00d460028084075800030000c96108030201c0b0011807407000152084680e0315402b1f02590380510002e04150025001140e01040c0208003040b001d0001c80042c6558010b0168500000d42c0800c083c0021250307a1540303604505140001c22811900d44203140d018032000b443e20f0140c1c5004102200741d81c40d140c05490107181d214 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 931862032 1250 931860782 931860791
    0x10804030512180a03021006090b031e0c1f03060b25050309060c0601080607021c0e031c050703021006030f030c0807020603012d150e011e03060f080607050d0b0301020c01 75
    0x41c20700035510320b0703100d01f03c81404d40790450024007036916101d0f03440381740b2020303010b84118451003200d107040c042d2200d13020710729001e031412291081d030780c05011082500ea030301c1ca003519040320400002c08817030064001c02c0c070502c003c026048207c01884510300900100c0e03105200e181c4c0030780c035059086002c0c0300d4039642c1014010a00e0306254602003441c0307050b10180e500322a0a0380d00d00d0030499a403581c03512900202400040c80c4059144141d07080100d010303003d0308840e60311800500b0040202407441390398000a43c0800c0070800c00d82e041c0a845203066001c501402042c3c01c40c5c40c1c509026031051801000e100d130625400b0208070100b01a07984864000303020316101d40c4d5950000c1d102c05414041004100e894071108034805410b0568801501c200203907480000d42d4511098a212f01c0080880d03051160071051035001040d4400554041d40c002c4d580820355a00d04071809100c2d0304180c00c084000d80003d01080509030b03000050304c031075030400980800d441c2400c01c0868024030525045403025401c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 931863282 1250 931862032 931862053
    0xb03030405040f05040510090209161707021c030b03100203060118030602041d0403230d02040f0905010b0c03030f0402270613060e0c030c1c0e070501080403051218 72
    0x50b07104c284034038040c50940b04402070030100c0d6421184c2d4250002c0d40a05140003003543e0788601c691101501c5040e00b002e61007070301244088145150201d0740100103a105600744003910528440c400181009400c007070100d5004440065100c42142c0b40f034070300099001c030006a55a00c2408010265500300c0e1180b0342e03c54603030a051000c1e6001d402110582c0700700e45000c21890081180c1c5030b116503059990001203060075001d80c0c034103103c3c00b40c82c0e01c980c80c02031181040050b418401400140034106004807482e2504040070b0586e08140d00218580b5414400004a8440401100e602013100d5034a00c1d1195190300c0015034400280704201b540c40440304040d1003203260001e120780144000c803895201c0d074040161500603540d60b4000e405d2040350103404a41850029405142c00c59034001c42c040c103140d019a4140c824001010714aa0882d40710501c2c001d1a0070140300004c046c1801703117060222464662405400d1b8410390130b1001c1c010310320500040703000300c401100ca103802501000f03603542d8014 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 931864532 1250 931863282 931863311
    0xc1b06021605012003070e0f0f031603061a1f02070b070803040606050a0503070501051c2301050402120c09191517040308010501080c07020a0b04031a010b0d0b0303040504 75
    0x154000028554804e0001ca04504101c40691784611411b9582c0f6103156912410b01039411003000c2c50ba034004025200240c21540d05020324445035840022810342c0c0f078558100345080c0d9003d4030480031030740c09000142a603502c50060207035580c00c14040c40b000c0e81c107008104078a00301d40d41d13100b12503032200401c900c8100804040158001c0340540d03002d020041d2a00c01300490001c0a202e0940d2590060030108100d50041e000b410132924041c2c0281c850186044414060310003810500c4251500500512201e00c5401d90030b501501c800e40e401c600b414242c0002c400700d4103000d0701d540f07100c0002146244056540321000317100810185e01c040121543c13043c40c003403002705c803c1c1e00c0f9012840b03840c2100b00b01446407500a1180b07070541d0720b18160764a007000540c5c0281d009002d101005208104140140c0c46140001000b00f5180242ca0340d198a1030914017036190150341444001441d40c401084090f10400541e000000030b05c0300090f4500600d00000d00c1e511135503020681007410718501c1920030a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 931865782 1250 931864532 931864541
    0x1060215040f08131d270c0d0b010e0f1501111e0c0a0603091101230424171503150c030a0b01050c300705011a0102010c1b0602160501 59
    0x78002c8050751040c1001d211400d00781242220386c2002070140d5501d40e5400d000b1070743c503014040c1c03c43e0f040d54000d0010300d01268a0030f0791040140c0d0100c03e030714010002500490070340c5902c1403031a400a1900d041022480d0205071010a240d8108060944044032001c0c0c00c0c001d003106035441c00700c581030705044c1090894550310b0070b1031114454407907207000180e1580240a84090651700c2001904155204001500c01e0020200304200007a1a5003019449422840082000e81410640005004980f81e141059030405161100c01c01c40210142842480030581598100014402c00140464020082482d101c2d0500359980c0d940c1d1a04140045881004000d50281c1002001440191030803801513880e441070710b401c445198068103501456002840340d490600c0769600100500702207460324415550800e240c15911359564000a02d8168201c0d8212400f040081c002030204d90701c80c00010f800700c0b0598441d199141960390140041043c0d45d412103241120822400002c00640d0800c00d0091 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 931867032 1250 931865782 931865789
    0x5040b0a091d1212040b0a02042c010b09030a151512050f010c050a031a0406032405010612020d06030218011a160219090203071d0901060215040f0813 66
    0x80c00742e04200c3c00d0b4141110100c41c03803c100c0410b10740c1c035074640340d035402c500ea540241891269642072202250814401c984c01041e2250701015203030040e02c03c010b501d0302010607404017000890820001d0a65240400c04861040e0090422030a1031045542c0101070302c444055031161808110b00892020038641c0202c0110780107100702c6030314000c1c4c0e660040c00c942d103069140021407402e00c14640c14a2081e0440c0821000c6001c41038a9a0750030004034007075038819042110000600102042c08161603810741c03013461003100c4244925454a00050a0f852891060075655500055032000700c01e1150060320081d580070303201c00030903140a0094840030400303014101611561f0fa0383e204c1075041c1481501c1c0c070b40329a0103c103c0c2c2d00f004c90307080101103010100b034580f02c4060305100183c06a001d2000c2e5120303002c1511188510118603d00460308484100c0c16403081c0340d9a40148075460780001c000941e003200140c81c002584890514a4414011017401040100009002c0580c00d0140891501b103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 931868282 1250 931867032 931867091
    0x3040303020114100e181c02011b08010501050906070f030f08150f0d140706020d180806010506070212031c0f0c0f0f12110901020f030307050405040b0a09 68
    0x4910f41c0c0a6000c1c2500503241210810031048040c0403921903544c03555006995a4864a0000721900c030050801d0404640d00710a00d02c43e245d00d050503a02170242c035807166400e540b0100d020b82c2c842400390144906018140c1048004510f802c10b035100e000444003046c2d01700b01240594200351400030302e00c3c140115150b0008003140e001c580040d15a800010589070014480c8981150000034006651a91841a22600c1030381c0c402d04441c10082c81504040c105c03030f6010f40350300c540e240c5010f040032009038890000020f8601003089502c801080542c151842140d20580c8c0d01c64500000300300341440406100036000015040b01c4401020400003010443c5200074040641080403c1c411601100c014401040858012441c4c840c4614805c4040740c0301414102000041e12056004441c1d4241c040c800c10034000800021543e010800f81800700d521100540c514a45000d004000d80228494107024586038075500c04165a00b0034164041c01144100704010b20103620403d0b208045a0310704880c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 931869532 1250 931868282 931868291
    0x308070c0f03050303190b1c02010e0111120c0c0a0f05090a05090613060e0a0b040213150b0a030603060f1a0a0b1209120304050313060503060d080d1409030403030201 73
    0xc9140c1c007511080308490b040b102440c115a00d40800581c00140d40102c05021030b036610f0060341135690420313501860413261500c40220503041c8009483c4100500b00389060082c008042c2e0b06401c0d0000b00002204c51402d44e9544840f5034a904d11718140c15400c0b4079510001c0c03107101144462100e0680030803107508071401c180d2625130300c01d54804c80b9030655034800d0f1a04a4800140c0a1081e0b0300705180d1030784140c000003642c0145c81c04035801d004202504440c1c1620706030500c0250b01e40001480107030008800c042110020510740c40c9010505403060a00c5d0984c0451000002402075000b4001550018800d100c03280b440c80c0520f0081c0701038400e80701010880000c114a82c01d09040f90030a03500400001490070703031421001c00103210010301800e0144282050078805103c102c0240d0b000d244240c0c003e5481d42900c41d02441e901205800c09000c0100900401030196500181103185580100c046903945424404c0c590241c11051a281d400100d10b40034804c220300000300074412a80650b00070007 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 931870782 1250 931869532 931869539
    0x1806250813080d020d050708030f06012a021905091810050114040f1a0628030b031005070f0507080c010606050c15040218130506040606051804030c030f020a020a0308070c 75
    0x11b6560044650252100d42c042c800924191216900c8503044541410260043c40081d0220500c41d03600e0174014010182102110046040480190300c4a0318005005400642090082102100005c042c10144255002001c20714030080c0460040b00c14400d400340119030f154500c404929401d800070358050341c904448140c881104e4820604054240c1303140e43c013003410b048104801074000320764100d260002850700000302242603030b41000c500e8070703600d000c250074030007200301414107000e40204017025003080200b005507644403203011603c0b152810055101d15460500648601504510385803640c03070598041030b6241c000001d0016500c0320307400c8550704182410491178000701070302c000350055030390741c8410ba0101b03621040641c4000079040d40d0303e82c00825240d40d450306038142c0701550025650b44d4240410b050103140046a00c2c1029094070792800c145d0340081031b02081c20b03409010840003202501c42d5a100740007401031260002d00348038415880f030030040039070350100c2c0b42111801203020000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 931872032 1250 931870782 931870787
    0x601080a0e070e0717010f090605241b1b040f182d03050909101d040302190c0f331b0501021806250813080d020d 50
    0x8108a180d070025042e410303c1e00008541c1d901c0040c00210a110b030303440e8004a00040c102c4030390700904408240102440c94042000c08440d41500014051a44080350140120440d1071005111103007038640c0d680c80212000c1e00d1507001c54040720b20f01e18020809402c00e07851014109500d0040c04940c208240304151a8940031541d8a40114941c0346490000c00046061440341e101c0044a40c000650881e01701c00846102800e602011800700d03801240112407400c04040c01030f030056001503111965170801c886481c0401100c4804c2d4031400b404030004041620a1045d0742e02c01c49800404400712805161030700c0b0410300341c00b07000c808ac0d003810300004450b03800002280d665040c0b44801c201980d40d142031a00c0d1404d885188000b4003450308071840d80014040c2d18420b64900070b000042c0c54440c401c1158000404502c082c1d03105e03403000d1226441600400d411745d0031103428098060b210420f0341c44e00c0401170041141d28a030140000f1400200f410022844d2a41009107500351610a07000d42e206 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 931873282 1250 931872032 931872041
    0x9010c08060f0d1b1e05040c05071509051e0f01060605040b030703060e010311010305090a080d0207020109030602191e0c030537030b180411150c060601080a 69
    0x551240d940103240c00a400c090f4003600c03009014181010003091118403513298040242d102d554244511240d40340076071500b89564000d80f80499051190b5200504024914040e0900c041c3c8411000140009104c601740c1c0012a51548103060b2a0f04d40300010002c00c50020a41035240b50740100180707854a0350313040c4580410f42e801500c0e07150409040215042c43c5420050200c0700b4165264004071388440600005030003544140c4028207405e65480004054401c050050f4006a0110300700d03000040d01070040e1040d08030801710068690700c240c00102c0710042642e00142c5568070018404943d82643d40c429902140c9544542e8080302c4c1d42c0c401c180c0f03a50310540162002948600700400000d110f400100300002c14021030600c8400035004100c441d20f20381d40c0030001b2640301c1010b040c255405018414038403004644070b6002155009001c3d805000c020300043c59400d507106e00c204039648008007a503016000b1500c0a850f0350505186a5450343e003a184540450000e03000200300541c240074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 931874532 1250 931873282 931873291
    0x3060f151b0515040201031b0e01050c0a1e0524040b25030e0706020a020d35070b0105091909081605030d0c0e030d0c030504030b0c0309010c08 63
    0x51034003240144940c01c41d86400740105111075844801040e40c0403a80c204005800c0e580440e4400c501e500b0144000340446420641341554442926015a10160040d4004081400c00e007080d41da039160702c404c11418000e4409000f0224090741c10100a881c024044c19020f00d0310441c1100e081c0c0790154102d850420840c1c1001a240e0628800540020540780ca042c1d080303100a00c0301401c034640c018078006120400c030402c06c0040d540d02942d50000f0010020840141800d001500705641640c001c038039520391804000d04080107000711040300c0036240d034212541842c54035140c048850003901c448107540c0502c0c0c081c0c03a08061240082690715044024500640c5410450841e0b02054030f8801c01a00c0e0420099600500503c403a080d0b409420b007c407074400740f040001d16682e4000e18080c070201c40419500c4810064012409007032501c0004101d049001e20341040031203503041e840c0403036451040340c1004110030202d8003440b4891040101440c00750040100901c075243e4482c4045031440740464 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 931875782 1250 931874532 931874549
    0x608090f07121e0f110a1707061805060f0a0305011413053c18061807051305010e06040510090c030b0d0302061e0906070e12010f02030703060f 63
    0x2101440016002031000f0500ca41520248030685215214106600a01ca409580c6000401700d04034042c903000f1444e90140c1480c044c1d101c1f512400f40c01050351000303140516428415900004001c1c2040f191141c802000c004026960324003070113075220002d07013040410801180c01c003000800e48052040d40c0c02501e0380c01a080300221807801c10028090407020340048070080340a12507104401d10910309403110700f510f05040503421000c4402c02c2c0828002000402c03960200300a07440d02110106242d42c2048001c4441a00703005640c0303a0324185840340e1b00ca0303540800001040e050880701500664121a0321b072140300c0b6655121014001075600841e030b064082c1c2c019140500800724030f6404011210380030314000940000210200303031041180d00c02074015a2040d010031440ca40703c0e001201106490b85240350741401c001c2c0310141c1c3ea402c0a02144280318190640c00019124242c0e02c50040c000400240904418410040000d40c0b05071401000a0704120000c10f803951b80640107012161440d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 931877032 1250 931875782 931875809
    0xc0a0804030c02010c0611031008120901080601140705010c08090c0a03150902060c01060312050c100c1e0e03070801020909150a05120601091505100c06060b040608090f07 75
    0x341e40407a01c00d007a404080341440b00341708118020402c80d200300d410a09040c1d4150b0b64a040c01e5281c81070300c08c41680100159480300354090802501e003c10b80701d1840c02030910f00ca0b95110800180d5180004601c0c0603070754000481d0003c01d100c3c0c15041080c8400f9103807103040340c54072610030080e21800030801e201d41040b886942040019112198901020400000025041c945a0015070b00e64080c698080f0b00340c0d1182010300034080000e807941d590460900b40740789040c0c0e5160800384c884a40d060b290380d0140ea91001c005186008203010f0300e0314020886117555a04600c900500442002c80c80980a40300d045000704112005108652540000030402003448d5a42000702d40380162440741e0b41e40012a41c240050f040e1600c82d42504800102005000036604001501049074041d070000e6072100b064840410190301e45501c02e8095017514a0a01c511710403034202400505443e0f0b025200c0300c940028000740310340c1d00506c240d00030400e060558180b48503490801d56102c1441c0141c01200070f22 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 931878282 1250 931877032 931877041
    0xf031503031709010f0e01021c06050a0b161203090b011e090b120a20010e0a06052101060906080a0204031a130b130b06040608060612030d051e0c0a08 66
    0x20407010340d01c80585000800d541800c40100300c29030310b40811031b05983c3e4001c00c0440032021114036012045009803800c0011038940300c0000c448941c58030030210071610009142006034030254640d007046030800c140c064003082c0700000600900c00042d00740c0b1401040360000c1002540c100c080d41c240010030002c100c81900300007212004110a401044d400581c083e490590300000340203082c0741f139010715002c00e1078481c1602c81c1200c5608003030305035042051600040304180c1e10880b181085d151145001074039251a20800e1420746c000c000740c5c03590400403100000309070ba4400b4418040c1ea0741561030b214a900d540d002031041e8041e40c04000e2240259040c080100882c9040c81540a191980703160103200482d101d464078032409941300e080c0d0407964a560401e2059802e600c0381c0040d8141c03010401e51f80781c190029220100a0800342c40365000101c01c1c2c40811080040d0350940641000400c51030030400c0b080c00c0c001800003d8500021003100000310060400c0c000d4507050007103030311303811216541c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 931879532 1250 931878282 931878317
    0x70501140c150a0501030c15170919060b1215040212070905090102090a06021906020d1401090e0d0c050a170c030d0e010f06050102120906190f03150303 67
    0x359012103074a1080341e01c0004030b80c0b000710116000700c000340800900d40d41941080380d46414141c00456103508001901d505099201c4203200946140c6441990300341c4480d07000714200861001c0200214402102841c18052a81e0101d420420b08a9908001402c0700680c19201c2804107070404c1011803c10005001d4105840b1080b134010307108c02580d0016071181d612408450b41513500383d080d0780d40800c4103040c0382001c040e0742010f08454001032002c40c01704003d83e410302c054284018070090300803440c07150b46000c41d0000e109906020b81312a10701d60711030b103544000380080c0c00444650f1051010317400281d40101198070107950040064501a005074580c0031908000580b015130029080112000020b07090000d4000524014404103103403010384500740c2510301c0300d01e10441d09864aa41040b42da81c0004480700d9410f41c211260380c035040c81c0c07000128140564041807078000c000e9442039102030fa22044880c8066034980f010800008c0006c07160500d502e080c00020042442229800782c0201c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 931880782 1250 931879532 931879537
    0x1a191212020102070803100e100e071d3a0506010e1308030106020c0f1e1c1a011a18060714010615090e0f1602030412081206010207050114 61
    0x3a0a80000361524251740d5580d407203903104039008800503071841d105022007004180280d810500d06901d028002d81440d90300c0e103154501402000502214011025000b024056a0507a04a008200c1c0c0d180302107184401c29480e609140362210166070300000749089606807413480503690014001c21180e07080104d9800b03100c0020b0000d5810a074078001c81800035900320000e40c0a4900c0b540902510369001041c42003031146440640d00c0382501e64000612100303100040d15902038101c1c2e283c42415025094180a1199032030083c040210018816034135411801d1440e040310205001c3e8603070f1001d208100442c60154140e1035901d04c017a40356403c1d851420001034002103005d1030400300718540c0400e580d03003106d01552000c034902c064548891000e079003102001000301111540103025141052804484003401070000307a080300c6501c10034010600c02c1090310040c0200d4000c0c10704030308031410407000903000700c2401c1c0601c000d0361000485c19440071030f47e10100d80b4181c4580c6080140964081d2868 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 931882032 1250 931880782 931880813
    0x40b0702060d140a020a030e0f0c010c030507020d0503030105091f03080a0e0307060e01030f0e0a17190207170d08040308190f020703020f0f0705150c011a1912 70
    0x242e481c3c2001c0c8038140d81d031410240c0622414000169540c203c2680a030584540b2301020300d09400c040d103250b000b00c4011030a5112404246801c0070803040a140c1034825016440f00a0b401485038a40c2c082000300020096040c2c440890350b40d11285d45030f0202100e60059000906850740c14800c0c104006824030010f0590180c1d81d060004903d0302290200b490300201e50310020005652080307038180395815119400b40703078600407024400302d50210320841e9a4101148014002d000459088684003108000d4481000c40306c407100d0407006070007000a580f031301c1d01e000348160782081040d0016101c40c0050780b107200401503155030155035207544041d2030f2040014803101c0ca2230251b584001000030b02d407180fa40505088000180c98101900b0000d1074590a855000d920740d00c00140c02c4043e8100244035411200d0444d032401e031005043d85c07180107a01500007401c03041d608054005040d818240101e5a50240644804402e011460a00e2051b4026849210a03507044d103002d689c0403d460b8414448007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 931883282 1250 931882032 931882057
    0x1c03142a09030f0c0901140f060c1f0c17090d0309030909111c11030114190315052a07060e15040606060323130203161406040b070206 59
    0x2040841004a07081c43c06030040c88031960442c1c0070940c0c9910300b01080c14090080f00500ca80207041001c045614080229080c0e03124210105d15180103140420001e0194403034402406031411030294800090310010410070081524070040040c1e100c800d2007036903ca00d0b001e500038450104040d8041d401441c0c580300a03010400c4114000c121080c1ea070045407406090f980d071960352031140550240800c41d0250403036080e0342c1010308890b0016007400c10740e03054602002c82400310040785c000040521200007041d0341c400454040000c103004048008148407281c2d42c10074041c40d80c0348100e030400070700c00007450940c416002240001c1c0d2001030001c0d14820340300d4040003644480303030100c09181640240030020810b80050800007044901d001e020001c240904043c809803151003a201420100c034244103024014000000391284607258080c050607030003609035000c141c1c451030030000c5a2080e0040300d03c1503048410006a03400d2107011030701100d88100320710b4140b0710b00b030f400c00c03099901c5400340c1c980 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 931884532 1250 931883282 931883287
    0x17010b0d1b0f0617100e010303080c07060606030504050c040e190201030908030f071d0102030315030a0c0b03090c090402090a020a09091104090b06030709180e1c03142a 74
    0x280d080c0c10003050720140c0266281d00603820801840038060000c014100c1c0448040a54104418003031b400400d410f4980c1402c203541c0c10341d1001c140a0090140d40c07805400c0300c0c108040000c115400d5131100c1c1c040d41c0034100361412950303610b06000640b001e411a900c01036118000c1c03140740c10b190350702020307002c0d205240c0030031810070f55143d40300d4580069481e0003444a20006200e64150400b418921440d140e0500203054194000081c0d200e000042901c0c002c0c101010300c0c04031550381404a0040c82c0e5102d0249007144d500c3e01c2c2c2e01c1c01e00d500200c078400343c10b00c2012807a440e81d2070800c078514443c660042c103803800c995400f16407801130b400004620b01400301c45c00d00458201c02e20302983c80380031110030b45940c46510700810081600c590f0203003240512410000c0c0440641d00c15083e01c19248100105031108840400710310003810f904191420900034105d83c06842500040c41c420f00c1e800300c0d0b505000300c1c158881c4d4650340701002d4502e40140050841da010040c0030707006503040042c000410590 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 931885782 1250 931884532 931884539
    0x27030a0206071a01120309091d030304030305061207050a0b0a1e110106090605090a150b0a110c12060450060c0a122417010b0d1b 57
    0x2505900090b004030782600c604416038411540c107501d01401048202c0d0442c0b0075a82d1074030040c10038183c030f006042d00103032a040402c9031110a840142e405501d4101140c1c2c1d43c0c0341606005004120940f40f4502c0307480000086070285e54001102d200360740e0028104a03100745001424911070f400910030701e040c4441e01c0103400b6200500040c01041c00c01d1074485039820050040500e08542058108a640b14030701130041c045502c03400e805990080111100081485c07294001200f0400795602c0026415400500b08040c168841e4900d041c80410a00722803600d00c8840401c40c0c000310a01c2c001807260301040c0040c01007621200001d10100d030980071011171381c860103440c1c01d00d900407485100d210140d00b26a035400500c2c0c60b907040c00c030040c1310014203c035042020303540007039110310801281000720341d8070b07950100c81869000b40c0002c1c25610440180450b10715210b84809803070303c60740301a10040001c4000e041018059200301000080c44250b110351256942c404000c0714680b540740c090714292012 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 931887032 1250 931885782 931885789
    0x80303040f06141e04020d0c15030608060106020c21010f0e0c0a0303093f0b01080105040206030f0403020a1709030f0f0312091204030c05010f0527030a02 68
    0x45000c0d50090360a80034500003030030301d41c0c180e5241c1400001000240300070004030030b9105440c41c045400703201e003ca4031070702c803400016070a0403030342000303030086a0803d0300103100440c003603140902c0e456944041c45219502c00302c0e031b9200c481c00d205040c0580c00180e0508200c0c500034510b01000c60400c460038041c0040708060f80e0031200703030b000300081456a4443c4070342641010070844c488035504944510000741107035130060200c641c82c030580014001c8001405c4c500741070b100305040c5400d901e80700c004400b0148400056000c959810a41e580d05190002282c518010700400348a590060842469503c2c2ca1400d102801002070098045000e16041d06000425542c003001e415050180896240c0c0380120800d814040c1e41035811380030703a01845260100f08000301c1600c000c1c0004080c00c000c1a85c41d40e0074103043c0880f651040c0c500705c0000601000b007100c280c84a0054510030b90b10146968596032041c0c0b035510072000440e41d400c0f0082c00e48032180048120141c4003040203402d0b40c08984403076010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 931888282 1250 931887032 931887037
    0x3070b070507241a04150501051c090f02210607050a120903090302040b010f080402120c031507020105010b21091f0e10020304080313330b12030d020d060803 69
    0x6071452192204070800001980c41520b00811100325806c200c110807500c01400441c0c0e080c0b00780345c140900840c141030840d03164041d03002040f002c1034081c000b0040920340801c117000e090030120320078101441d20200100841c10050400304038200145840c2d1100e1109503074641118504608200c3c0280e40ca02e01e62829010b210180c501c00c0c1c4031a502981103104000c1591103003045541000521408200501c4d03003c2a480e421940598406c0f0104820903282170030a01c1100040f0b07054030070b0301e00c6d0f490501e4481d690344e41710343e0301c40d4000c00190340c9501c1d01c0c4c00ca6106030140d034808404504050011403c5064030701e5042040d41c421502110344132206102004041010503000719070b5000c0500c03404000707011402c0b40d4040750700c08614502d0036a460020a00002c0c103030380040b0001074040300402a07281421288484000002400c0006510982004440d441e100458150a2955521103810280d40b4051103d048101450806004030300000c020742001e8404d00e05141c8400b000200300b54280b00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 931889532 1250 931888282 931888343
    0x6010b1e0a0809010c050309100e01110f0d0e01110919051302040602010b100c170d1a0f22020d110d050714040b0405311a0303070b070507 61
    0x1150b441a107081184142142c6a05080d001404020000c200201a001c074071617045202001d000910105110036007801061002282890f00c100060070a1094106074003600d0441d26049003400f0b140f0011030701d40e00341c80700d4500300d036042d0740e061041c04814903010942c4018140f041142c44ca14139942d40004400b4420110303140400343c0c0c00907007404071941c2030040d80040b12040ea59000c11400c4084001c0c030078117150a000e80348022500c040c00c1c0070072001c4115100351080f0300052101c001f443c0714203090503111640044c800d86e5404081040c80c20444100e00002d40d05d095414104001030201c00c020354070101e541c000305a6035410a07005262407a0240003800e1a08400040781e103024040070b494036003c0310000400719010b0204212070150b85040b40d0680394152003071002001d0005182c103103140c0040c90004081070b00c00d0041c0d160300c00340e44084c0c0003108035000c241c6401000d8007810703241c0c842c4040103840c001044001076800d0340200010010144140e41d0010302080390044a84144400503 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 931890782 1250 931889532 931889537
    0xf0901030c230310090c0b030421020a030e190302030f0d030506010c11060f0421030224150a0302030a1104050a06120f02060c0d21060806010b1e0a 65
    0x201404a54803000407a00002d0500c041c010401c0200030019a03680042142080800d80b6008000104600c2c0a012030007801a00390b01900c07400c2c2460f0515060401c00c2a05003200f02c042000d08a10b0b1001500000103901a10366002c50312168040c400c0002c1080b9040e4480c4011150010040c2c500f001101d0142075240c01424280d0241000101510805056541005006a02e480100308013500c0e100e034803042108d515035142002c65000c80319014552000b5012540408082401100000043c8803103100fa4240c1d02480c03c17410b01c02c007410030300380b01d4030402d01080000201d010f10740c4c282003031110000800600320a40d030b981c0043c0c41e0804d0840f04446802c418080404981401c0c0100c41d00101c136028180f00c00343c00c1600e600020b01480b44050820f007441d151800c295118030707003140c008000c48000c2e552483c00002014010411170881448403c000c110101c50028042c8a0881a51041c3c0090941a4600481140135400c40880c0c3c600005000f0301400c2c440802c403008100c06610398 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 931892032 1250 931890782 931890803
    0x615050d08090f041e0519050103030c030207060318410c01090e0a02130b0a11070b0403051203090f0313080f010c0e01050a031d1f0b0d080304020f090103 68
    0x701840300054880d506240114206051100d42149800c403035145810300a0002601e1f6444e00da4081255410004140701180ba050010003490b903c0250100c005000b41c080b02c90455503108210200e0380c43c15020003d210b0500300d01f40006001c030306c4075146450710802d10410401c4544495081440c5014200e810b44031540e480c4c1990a4203000c0c0c150300032403d0034608105032500d00d03044104039000f061070100300d900103070b141c2100a064045d000501090740d50b50340c03a8002907801600e41b4014415008051003980d038002070404528040304d00f544c0d4000082e240240c03150300001050b82000d441140540190a45440307506810001b4008007260034800001c1186003903451410801e061503101c266034180500d484116801c04203001280340286409661804909030440c000c14034111811003490450841131081180001c2250b565200b20f06807203603108418803040d04079003c114102d82c01404406424010801000c0610390103130016080e032140740a00c40014040c0d0703030309800032210340c03062 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 931893282 1250 931892032 931892047
    0x40b03011d0709110a030203040f0b0f01081203090d2a0b010512011b11070902030f0610020d1211190801091503030914062109160b03040615050d08 65
    0x400c501001441d40d000100490382411394441040c1c4030700d000d84802c2c50b40010204017000303030950418031040d070007080e55182410100300c0d848021070f081c031500d0154812031750100518048401102e005600450003080311074151002a00c190580600281c010314007821000b110315a640c0340c0c3d5040318410740300181c0c0c9605040070000f51010240e902180e0b41c0c0b404001e014071241155004d00d18121508141d110a00d9030342c10300345041469002100d50b5070010050002105629074520300946c4211140041d04505400c102d07504c40c120720650340081d1080c1890b28245009a01ca2204818840100ca2601c40b10f201100002a034031210540051034440041295241030b10800071116000943c0c1000146561401010b564480c09160000d103000701d1070301d0544d0b645c00c1c1128540008039442605107860082501075049080317a0042c01ca000d44800661001c2460840109440d92a00030074203680722074460400a104d000106000070400c8079000c50a40d441701809081644159131580d40d5000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 931894532 1250 931893282 931893341
    0x80709090201031b08061509040c03090c08061017010f110310170309060c0115330f121103010b04090605060304050307020108040305070f08040509070815010c02040b0301 75
    0x807142090406a0039003203540309179110f681250092401c80d2010780d07400500b12903004900c0f030580c11a9100c0d2418a5200e02d45815803c0006c0180c06200350f9070425503142079050300d4000071100b02042c42c080031010300c00d113501b40390211500700c0000300005400b20054590701c00c440706422140300e01c107004000c00000c0c52481c4400400303802c030207200420301a081400caa82da8003510010500c14070000c1403945024009601080c00500361401e041c15003980c5a40b1241c0f03200100c80024060068204141140e940042c1502c0c65420540d50340381d403001d035450046806429281d003540a00c0e031244400207103568110082c601038111000c4e6680d460386803203000c004491555000c0781c090441803041001181020040e281c0e02a020b0a00c2d030481c0d03070b55150071140c52207000c070b0080035409501d04000c1407207900c4010f403007a140d003594004443d4503000815039030100101c520080c136215020302a140c82d4410402c070140c00b8806403011681001140c0081e0075038149030041d400b241442c880400380f289 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 931895782 1250 931894532 931894541
    0xe03010f14060402120403050304061112150d03120b36070c0f0b060d1208150a05061911060a0614180712020c19020a0506120109090c050909060f01090c020a020d03020708070909020103 81
    0x13502107400005403000c1e0f580c05400381074003003470203102c143d03039018202502d40f00c800b4407080100d0404100c158a1201d202d414018900c01190b800d0031140c41000030312503900800c4010f41940d00b01504c1c41034084503a4441c15140c400400c02500041052060b00000d890080c98841c8041c1c0c54442d52024a000c07190801050030200c040c500c500d80780c400400c070759182c0b6800c6800310340f50750356070005000c030415041e203460a41c012102440e104050420081100340e51200701a98070700d1013011a040070b040b00b0001016101c0d070390610729183c14004181d01d83d015144407503409a2051016051010a008140c00c3c507030020500d441003541100300100710b1a06009110103007800f181c00c90300b8a144c0c5011440840c005014807100c165aa02d00300040c040c0300e00c00c080c0103000050030701b8020303c0e00444558550b2410380304140545034120002c1134504582c01b071140d01c0301041e402407243e850307036408000f11605660030070b41c194047c2d0b00300440c02090600261000d0841440b02141500d800c0c4001002c89 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 931897032 1250 931895782 931895821
    0x9061306020f030f12070201091b0323100b010e100309120807020613061e02070317010501020d03020715050f0711030a0806010f0e03010f14060402120403050304061112 74
    0x76082000b0341c0303490b8a00042902c17804c444004810300140d45078101070340106500318024050b14090680c8944110400c0103c01c103030380c4540d1103022500b0b414914a102d182851094041d40e03000001d01185c000b05550000007207080514001c85034000f110040340440840b90341c7c2500007512030089005100c0340d011129a0f028052600c4003003403070082402500c03004050f14480040400401c01c4042c016a60020203c40c40d20088000c0808041ca00c450001e41c8000811400310b10021a820110009007410310304941c0c1c10f80242100b405030020481c002c0d400014200c1f0140303440f103a45c03507900c8558412980b1800313194000d545d00e0b08000801400c00d14041c0c0e04441541d0040010784196031b03000703d1a07a0132140c01c0c203280d0b002c955001340036101c00044140c1d00386c140d803902d06c0303146104460703030000804143c1212101c982501c034942400141c0c0301d03120401c400c0f003840707401050010307101d0002903607c68083d920005e40d042481203030380719a0b8000007101100503035400510000072104014140034 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 931898282 1250 931897032 931897063
    0x60f1404180b06190305010c0509030c0d170f070c0303030e1c020c0907170f150607080a05070c0e0a05040b01050d050a02040f0f0509030406020c0a06080a110906130602 74
    0x841e440c50ba101d840e035581c0140303024010101038a290b42c4141089110300c0145620800911205140a1000b44690003800145200744280c81c46981c0c0c03414540340a030507003904809040031854942c1148425988000d81c3c0c10010501002a1804941150b030880c1c0514480e95002c80c44c80903180c40540707461000102055141409940124403e40000f500b0341c1c0e041c010f03200000c0d0740c1d44020301501d210098064021810700705200304405440e52130315451049087e0480d940d441703640c56040c80303461701504600500441c82040500e0b49a4015009001c0c200c0c85080c0921180b034940349201d80302c1d9400d9a044203c1d58551080c8810007601294035409000305840c0c052450b2041d880d115624985058040e00541e0b40d0040c000c240150b0350011110070050140c144441c1c20310042465803a03016106540040c00361800c55049440e00407082d004540c490741d0b480800e0f80b100070104000707281103607840d52030074010000c1540940310000500081400910001c03255072601d40c010b0b06100c80703240d00080 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 931899532 1250 931898282 931898321
    0x9050f0f0613090f0308100801060609090504020d120302091c2006090a06170c0901021f06030b0c1b010519050a06030813150903020a050105090301060f1404 69
    0x60069500c103015809102201d840c1d2003000e6100c902c42c000d00010601803c03c96046040304103064104501602491045000e5841a5611001c4508a41c41c5000700c0d40001c800e03410820114045402064215000901486681c080f40c1c1e2140e400782002112000840d4012421160740e28001c06642c41020f44843e8030303d088581c613603500501400300e141e9030b15441408020800c00792075407000e44181a0780508151682e50703e645000c0c1c5014040c001c010550040c0c080020001120241690000716043c0c004100c3e002c820354026030990080603900280d13940d40c14001010407000c6014900500c81e101a403581c414481107414000d084805800b90140c0c18001401070585210200c41000762842c0000a02500c800c0d0070440500350030340c00a800100040ae10ba80040703080000d03641100e191408080c1c880b80c2100095803920003522020758042c5e000c040400c850f501407401070245107001000010141e031a07800c008050b210a8111005520354010145818101407054134561030301e0301e00490 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 931900782 1250 931899532 931899541
    0x141b04030804060810090c111e0c0d05031e0d14060102060c0c0708070e07230409021804050a1b0302031003060b0303120f0412050a1d0607051609050f 66
    0x34500d00c50b511078030003000307040800240381e2070800856030040c00880c00706221035401580010b1550f1191001c0c2c6400d0301640c160603004403640640b0142c05403031540076042c1c4000e15020000f0724400c4030400e50f49404100b109030074a580c1c4000103014040c820305420b032110410341030881101c00a04916000400794814802c46a03000669103902009040c0c600d0303668106480d1507800c0035840c1d07101c11114418240003091403410401400d129110a07919085516080d440803182020500e0103000814820401444900b003150010500120304507440d0703811201007000b0404a0340200e540000c0565a0070105004240c80200c900d80c130703100c03483c082d803c0d03042408010709800031621005180c0c540c1c400c0f090700700391002e005494141000c010307942d45600e000d1010b103403072503011030b0100c8000200b07061484000e4020000e40c1c0210180d5511260b001606150703680c804c81d0050803d0b0382c070000a020820014030100321000030480e400c185c3c10041490001b000080e100050f00c0030241d0b4412a0402 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 931902032 1250 931900782 931900793
    0x1050c060421030e060a0e01060305010614011b08070b061f0c060c0306050a05040c090506071115031509040c05060406021506090c1204020411040806160201051303140c01141b0403 79
    0x440d0000c48201001411f040002000c9004008543c8000d0143d424104d00140c1c20301c2004031100001c0081e01c44008098034801c11988040c6071040c02802d040f814030a24021030a840043d951080000e880750712264800e416035150802908142e0000031061410b0400f040703424040c0300f0b40307980d00c0d00702441034605110014a00003201d02849009076560203452240703600c5019a0701c010480907104650701c0c11241014414180c0016400d80100c03507803810703001d00101c0807048078416080c11883c2a01078082da010064000d80c064400d4444211030b40010861f42e850000030001000a50010400103241600785101d10710014111840740800301e00304114050b6036000ca07540d0101c0103130704808a6455100103402420b600ba212036010201150200b41200000350003400349040b42114501e80c3d125800c00c900380c45040b102030a0380101b520403140001e00a01c40c00c0d0805102c0c524050805044201003401c403002402c04000c514110000d0040f40300c492981641e01c1d4004092683c900f60845c0c0740c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 931903282 1250 931902032 931902043
    0x12040b0a141e06030307061e0e03090607082a03090117040f030c0c0e040312050a110d0e030403080c03040312050406090608060d0f05011e140a090201050c060421030e 73
    0x401da02c24030040004155070340900807100c9103075000a0400016590011042e18540f0503018010140d14107085c1c01d00c80c59000090f2110220300400c814504542d554400703599400065400b402a81c06002d031854011242c0b0480354a5100c00c402035859409601c001403002000790003a0b1002c44030302c000e00003c248429460480c10360141090304802d1907030f00d490840a05a0760001007595034a000b40010554048440111001c80000902241e20340300620130403140744a41b18402e04104102c92107000310035400c8011710b030b240001524145075a0703840341c40c600e03070200145c2141e0b40c0000800b4010003042c03803400542c06406240060906040600140c0a40881c2c080c410a1200d44130000d9107d0362800fa40c84011680320690313607046012403a01c540600356002c9c595a0b00403402c01f9120f0740054074401c4038030200e81062103035030a40b107101c8840000c02d00080c040c0d0400c2801c1100c118100c0c0100540750040344501c185489c22600e108101c0050021101c0034001c1609180d0404c5412070005007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 931904532 1250 931903282 931903321
    0x50a29040f0f03091d0a112b020906070b01051801082505030a0311010c1b0b27160b16060518010c170c040315090812040b0a14 56
    0x5481c415542c0d42810b0301c01c0c884560015403011664041c152130600c45044c16401059440414805c6480703081941c0c045000c1d0349080a40c90042030342105e01c03c9001440c04001c1040e6020051403d0f1120340400d0580c0d00005056404205200041180307040c40102500c1c540c811040005055041003402074079405603449864001c500d02c03668400000c800000c0c00010300c002003c8880300c00151070050492043d40f82e16041d075501c1c004604034220f0080c107940280001c01205468803103140e036204101048082c2c100324081c190398050640f103540e1a583d6881c215840310080010b4024983c1c0b8244820054008002d015007e001d020142d50509640811040c0d2114011072696103400c0c0380c042c0c421400b24211025070070802c500f501305030070550000b03006040c0c40303403120560745444140d055881244002814050100c4180310b80c807a20358418000b207845074410510300101c11000416141064034140c13400005034080c040603450910488084080c290841c203810301d00000040d02e401403445 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 931905782 1250 931904532 931904543
    0x302060a08040812040515150a0303080408090919060b0f090603060d020913050601080a030c080a0e1f0f1e0f050f0c0604122c030109050a29040f 64
    0xc020500300900c1ca01640e1042a40b42c00c1d00e4801c0c6001c0c06d010340d44085441d81c0e005800316901c0801c081003a055244500304202400d00540c0c1e0f465a0750072156014010425125070100388040c00d416900d210010740030346038804040c0c110010300003200040351161742c0040c005007820801100e000f00c0c4a0143c40600c0c408560310b6490313640700340c08101c0b51000120b0095002c23a486003040309549044850142c118050b60480f103150303895500407a03441c400329002a002c40c490400700c1d40082c40c841300030b101d11031040ca01052001180780201c0c3c03040910300c450304140400da488a03040554048504903e00805181210724070f440e030106819841c030241e0001c010800e030a0440c2403400d00680448008003080c29015a0b125000c055542d1220000c5c0c80807600c418001c1007500149200d003000422010b0381900380d1700060200b0740700060700b002031980981c055403110800c01c081f8205215400c1445e01844070701c2401d0034011155800d048407041c5828815a100007400702007030004421a00c0c0d258882c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 931907032 1250 931905782 931905797
    0x1706132301061814090a02062d1b010c0e01121d0304030507120816030e040518010b060708040506091c1a0601050c060f0a0f021303020f09010302060a 66
    0x250402000034030306810390362996090203800290b99005502c500e04059005008111503100740341110100e1340252403458090340b0220f24000945040c00040c000504440c102e9421003606001801d041c044018503100c0032200450455101c02040b50321070461840d031b4000b001114660400a010200e180b003a050402c19030f00c0640c01e000e09a5800200240702c041c0d142c407134804901c00c440e956617225000448541c0203040740007941c2503030550b02c03903081035001075001d0516075224268210407031428000e90030880041d41c03030780c0e80f91130382d1080d5400b840003100c15603a0041c140a0042c00d44044001041c040c2c03104015000c08a48450282e406969003228541e60750004075000402c00030042d41100080d4610131805401c001740d202120328058043c05500e00380760744400041d2007500031000034940c0c7e5044580018482000022401d500450645000072440c502415150407604040f8135900a000580c1c41030040d441d103c000c00c8a0a4811176401c001d56045602007125030240907076503c24400b0a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 931908282 1250 931907032 931907063
    0xe1501170712020f0c0102071b0e0c0d061703070b010b030c1c0603140d0906030b0904080313080c0708060105121f0207121d09060303031f0801060f170613 68
    0x2c60301240d51003110203180310740350703039810307040038001c4d841440102d90407500300804d80350f1901c0f0410010125030741d803044004140d84601c0c18410640c0b0465503444940e0b580c00012403850040b503125000b011081c001151109410701c2d24841d0b8030700c1038220350041d036003e1040000c4030104004580592580039031000745101c5030b40f22100540310b00d40000300f404590160580e10341c0302c001826050f00d0204d41d240850240d54640660403140c034014525002100f0034002008150500001c6420180515940042c0d2203180c13034403862604407549102e02138011034000c0000c12010011355016140c100c8a468001d403454468650300c2406c2c0b040c00310441c0504480b500410348540c1941e40040d008051a0103804e00460001d02035215192500010381100503140264102061064495030700030b801945192a004144803502c042c120580c0704d54217a6890110b0a0301c07082c004c4c0c8001344820410302282070b042c0720344401c1560504220040c558084420811481c0000301c540340303004d1300f02d903101800104 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 931909532 1250 931908282 931908317
    0xc141c0512130e07031b03060f060e0102030d0509010b2103181503070807030606390213021b0613020f21070303021e060118090203070e15011707 64
    0x50b0b8000c20f031402150040052640e0150000501180d5601d610303071510868203000c1d800c0f248a4098400300b001904020f10555019244043d004481401200c3c2010318104030042500c0003240e021206075140c0004242504207a49101c02c201280c0205c250740c0361400200300d98901071b8046c4074407900d0a581c400205038440d680d91512104201c485130340e981c034088002034244501500d003040020300d0400d0008031244140a005040c03054800d071b0000103803140000d10a8215860300d8842c00c014100c3c811401a524429031000c40c407070910f80940c54a107180140c94a682c9542c40c44003142d04000200090640c81c00112850700358115208600781d500300780407070318100901042040c00f01101e00c0c2c8400001d000600e040c01c90f03220745d003201c01c03030030300d070203d11041841384401d01c440c9522110060204240101c0e00c04030100783e003480041d01105a0f00000c1c0b400e0220703403013444043c1c898428400c00e5600015900c0f00e10400382404000034880d80f0058040c024010262810410000202d83d1101c4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 931910782 1250 931909532 931909567
    0x40b0c0412060c08010e06010512070509130501030c0605120a230f061915080901020706060b071421130f1512050f061203070c141c0512 60
    0x1144916401c1564000d1400c00c2c003d0428048035030100b00d0320000091144030500180c0d104100c1a510f2500f41010b00b02214400c0342e0281220090001c18025403003151070303d084482d4042c96143c4049201e5255041c20405021035030400420410204403d0130090040444283c002080d2100040c240248400445211310480d184a02041ca000140300c41c510144003824012003003190908200c004c0c130464032102040c64410040380e04080500548411b01031400c05d9800b00b0120000351404180782d40b00c10443d410394022036403a10300895002c0c203200c40140864404100380300140080d02170000c05440b4150300300314501d004640010302c200d46c1130340c00d1110b400401e690302d4a805038685590300b00542c181d03500d0347d0000240078810140361050850280358019120607544007a6a10781c8014083c0300c1c07408500c0c1d00c415200403c400d030000b51605412500504980301d001c4452030503a0200300500e4044011891000c10342c1150001042c8045241c20340b403103081c1d80c1c0719655100c4040e101c4002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 931912032 1250 931910782 931910789
    0x4090f05160c171c0c0c0308061002030d0608030a12060b030a0c031d01020a030f0212010509060a08101512052503020d0501020d0e0708030406200f0f07080a0b040b0c04 74
    0x540001c61910a40c130359803042c000c041c240700c2c2828000000701d10001c80355180712005c040c002641580100e209070414484a42c0300154600c1500e1400c1da285800c1c1060707924a91002e2240d9000045566801d503100105c40f000708185102800058608103005040e800f01a18041c1066a1101211500e40c060ba20101e10a8925811005058080d5104038000d40001c1e4695020030b00344241c503001043d25100b00c17401c05c002c1d01c0719040540d00305414041e600200401c3c05410000148010889882c200040d5805170600b0b0400708070f0250f1094038514020a65000c1c07640013540449001c0025400f081c280070b0501803140c00881075240791030003a500e100552020750050544441c031001d020042d0000d040e8103507100e50034821040503844c800d17580c0c40c2030700c0f071031940380c0090000380940c506c134107507204a041c0e1403107400c042000810320050415402100c11103042d80060700d41949040306110440080242070301030840b00c51507450b006600e4800900080000c80c44c403002440a58400c020384024 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 931913282 1250 931912032 931912073
    0x70b0f0603011508430501020d09050d08090d14460809041104031704080a0605070201060f1454190b0604060e0405040f02060a0504090f05160c 63
    0x1241d213600031511107817500c0c040c01d4014003444034501c3d800c900032000c4500312075006e40035100c0702e0b4082e02d0381d042603002117410540c030100400c140404980d40388458500400d1f40300103843c500e51100d1041e0152103c5166641403041c0d0314010042204070354005280011070013507102060300b294a4506418441c6905440e41719140206101281c40048090010780c0d10940581804022006260041e4003443c40745084541c030020051000075034640283d41c0201c994000451303503076110703550460324600741d0b00101c1440560f0810900a8904842c0da4a10030f9030300900901a46040710a0490400b800900c0e42e4136203d20f0341a628541038031110b0b80b00d60620b690500036071828141d0f1998100544508421140380c1081203802c03940c030340300d021501150700903190003c0c007601e85014040a44001041582d03450400d00036600940c5800c2c000f030040e20000e42e1032603651400c04803130710100c0350200141e181180ca010304006681d1200c2c2094081c02505041281d21200359261290100700c0700b03081d0100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 931914532 1250 931913282 931913383
    0x20c1e0606130903020c19080717030a141213030e0406050f190f0b03072006150319061d010b0a0509190204060905040c0f23070b0f0603011508 63
    0x103501001f41200030036528484180c4084550300e9040104580d409060320301c8070340080110091450040a0f100c1c0300c4030408007554101001589603000b0043c0031501d03041c400d10700541c04410164401e03290206143c040324204002410100803a00d0b8807040e03507509001f98084003042c2c8880e0002c1035030100a05617944840c0c14680c07210ba980c01c1680040d1091400303d14100c440d00402031021803020031951502d402440c0c940e0303544000d2020110300741e4006070180109407c00b035058100302d024030b81b1240940c6e000306410000b80400450b2030704003442882d03180d24120b0b550060381d940c0031038a02164800c50350100c4a403a003007100a0074844520403241050300c001030004806401c5001c1c9400c8440c110350422404500401c240c0341d0017000c02c0c42c0000145107000c9004401040202d1650031620141410308200c280d42c1d6103c200f61090307980d4200c500310501040441d243c00d00514801d45079951403036405034034004031a0b81c2d501c0c80035105040a100700401c03040008101d911428045d1000200301c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 931915782 1250 931914532 931914559
    0x10506030711031b1509060604020a0504090e1506030c0117040503130311130203160c170d0207050609010b030d11150a051021020d020f04020c1e0606130903020c 71
    0x88214202d1079201300c44c09058840c01901c5a0000128807941c0c1c070754054402d0b540c42d882000020b61020f0b60031014090103000c0459841140d11685c1d0031601c9a40c000c0842c13481c2c401c014050710a00502ca14404d038022100305c59203903403104c03005440b031041d031150303e24545403403800c2421402807010344409001c80f900000b09014400000703141c80350050301e0958102917581d03e50001d900c4111102a074000c0304140070000d00e84602007842000e802410004101d40c404401c1490590144044d084420b4000c244401480003d00c511500005410002c109241c0c2c1c060200303444003c980300d900e007130207104038003200c1d043c134140513000400c5a980340080d001c2c40d0041031500100780982d000c0780401030040010a8010f81d4400040500005040b0b1800106c180d50801074000c0720240b00b02c1e0800061403c070707034203500d50380040c01c0e00710303140e201520b9403920260000e04a248a801c180c06a03038801d0041c0100754444c44114044014203800103e8801c845090691a020000311800e800ca8a100781d00c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 931917032 1250 931915782 931915807
    0x4050910030312090f1b0b16022b0201080a110301091a030105150d050c03060703060806071b060e0a020310050a20040e07120c020a0204050609040b01050603071103 72
    0x410549109450704000c09070700c0b040f100100c40c00c0c81401000707119094000e501040b00703190362450034035804490101481c1c80b03100100858110515022041d034864100f00214980034503510b01d100c0f603440c42040d01000e110354100320034081ea0006418080390101003001c0d0500350700070303031414001c00084503038079607550907504001c01444942e201880303205520781d2168038042c05484d0160610000e01200101c04d0400c00507441c48180b021074040c0304210050f0030584061210781d104e00308540340024200d10702100203042c698010500810084009404a040041070883c3d48010342c0140780010f4144901ca0701614040b0300e500c0181d803612410b05886244411504481d200d41e200c41014410840c603140c08140c044005e1080601d091010b01c01484421000d0415a50000b200d1405045414004110748210341c0d41030200700040e0400d00350070081d82018040c42d40c1001d416074600b026803400e0344400301c4803035041c040d4501c24800040894041442500020003540200007625511000c034004c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 931918282 1250 931917032 931917061
    0x90903120608011404110f0a0f2405070f14030d06050f0103020903030d0903260421020a020d06150e0a05010b1c11071403030612120f0f040509 63
    0x10040680d0074020041441030040c051111800350018085903035440d2a6140c0e400b04400e0100d00d80c211850715036903006a51068a200b0007000c1c0c01e90032100d60b9007011681e2100e2422184180041c60005401d0303218240d0010480e100d4580009602c4d02c520341c2c0c1d21b8840040202c103da2a01d661001180760f44503420f80f075203c80100c40c0304848600b030032801c4100540a038003881e802d40d40e1640044c86090305d14440c43c0c01000c0001e1191a0041004c5007002d8130703032100c0100c2810740241c000000c0070031080000c54a40303000d00200074040340ea40081c060300001c0d0f68400940d802800b40410090640c1001307016000040c1d070201810304e800385192240318448240342c04031042c80d1070605020000600d80030140c04c1305c0043d102c105c2c01070310f00c008400c0c9000143c00c0a4083c002000c000300107413004580845000c2c81c0c00e000c810b0141d076503424a8020018140c8120010500903040b1510146400103d401111000030340381d00300d02e0711080407030400881d50145600c02a080340341e0380204411000c3c0500d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 931919532 1250 931918282 931918307
    0xe16050301050a06450f06080c011d0a0b0703180f030b070507140303150307090b0904020d0c0506070b070f0e0307090b04150602060103200d0201031802031c0207080f030904020c0304090903 83
    0x1b0820204d41d5840c01c00381d4403041203811602103940c02c000702450600215010040030009812816855620b0207110740d0b541c8041d9040d40051071142c02c003040d000c400c2d0500c0005010075142e1240341410f58540080c08140600b0480500c17200007400c204000c40000002a08941030050b603883c0d00e4480000035125600320381e07541c800e002e45c0c0c002003401d28a5104074940d008000e0000304259480d030b405d102d00d4080044041d10a030282034130010311030f90780c10002c20020384618224075007400e04403c00f03046640545440c1c000e00c602051801c80c540c80009200085503040000410240c101c00003190090a0803001c0103044000900d0114029800080b000d0403a0702c0b40c034806001c2d500007010861240541155141c1c020305100710403026602ca604640c40c40c2ca444191001000196130021786442072410f407807813007110140c1c0003d40142d01444200020310a00d0094040c042051a025403644030310351469105a9000c28402403604041041c1ca000d405061010410b000950401504641c1801c1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 931920782 1250 931919532 931919561
    0xb07050d0b0d050c180c0906130f0311100c0f021e12010e0c010903050c09070314090601062303041b0510052a0d120e16050301050a0645 60
    0x100d0040c201c05c101d8102c074814180300c0c40f440c0c20500e00c24204a2542c1c0040000598040d640c080032505841c4542008015840b84403401517040350b8005100c11514174040580500003440c10440c08280c00e6600781c0d500b164110b642c50b2845041c01e442d0a40245c0a8080705c0d00013081111200c10010b0550000c01110980e104071250300103c00300440c0c1110603030200620380d03000040b507070304941880a9000d82018981c10003050950200c84070740444082181c6041256005074010410940c11680807003551a006060140e000c01c0700890032054803014000030255000e011550340c4138601d80d288000500002003458990100c44c0a0061454016071011040c881006041c4002109030107c2c42100d04402c20181c001c2c080c000b6000e80e06080c00c0800554203940341e409542902d00c0c05e01400c0400b5500d0000f0380481810b08040c1760071204001c08d003804c1d8510b000004c0c007101cac4590b03480c42000d4034540c00003000c41c8110341c05000110382038a904e210141c1110841d241821180d04000080c41503c17 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 931922032 1250 931920782 931920799
    0xd0e07080105040c0608041a130308010b04210f0f0b0411031f051302130204030501142a130f030b060108150103020a05190e011b0b07050d0b0d050c 65
    0x40e001a402c8038010745000b00003d034120000c000450280400960160003281e001000258011568082082c01c480c4002036050383c80b811810981c1140c0c3d9203000d8000c1c03004185c200750410000050b41520040041d54010307070280410100125440500104c0c0d071700228520050215140c400d500750000c1d03d0803611003140d2031040707107d4100020480250314000c40103c18566a81110078020800507100f0300005400940d89005611590754040a0703d00d051001aa91803031806d0107821204d14643e02da010081c400c040c049071016051440940391691a030101d00512060040e20b8107109a010030301000c0c100030000900105540b220340c04403401000182010341d1078100441d46041c0440d44c8011540f280100681c440d480707030703018050a06145c20001d2400c0862826004088503620080780003540c00c1a4459103541d0041001082943c141040750310820156600c600109004001c0b0741049804a01d40c2031340403070343e007010031440006401d80420407020705180d62140100102c15000301c80c6c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 931923282 1250 931922032 931922039
    0x60302091302090607080307020f060f100f030203070510051303050d0e040207021f051303080301050324070302070804030f0b0708070207290415080907060e010804020f03030f0d0e07 80
    0xa60089500380c0f400200800c3c0303411800d41d0b402c01d45401c0a0554021232144d54031241c82002c0030000d690050440080c1c109039460704007141340c08140560440c40c2ea46101600803c01a02d00180c00c1050358821a4100d08014a485003160725029003261441d82c803420b08800400d01c1004a010f0511000c9641e44006099111091105900c00d24000940001100c03611840b8420203000740e908212091403d00d103003403c2c94103e1050b02c01e04d90819128120000010043c03441c1c200724030540c0f01d41c40c454007000d4801140250508440003085142031540016000c0c040041d2030084501131030380710202e62054a0982000c5c1c2c10a41c00700d8a00d8040b5030080c01003081580001100c8084032401d00c0120750880d0280354203e000390301e0103404440c040050001040044081072040711951065a0b001d007685080c40000340742089540c480001e00000c110040c102e42d9020021a500c070740c040e0380e0b484201284001003440c500c500140581c143c2c00201d8900c0c1d01019903002210564100700440d4100c685 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 931924532 1250 931923282 931923319
    0x10c060e0c091e16080f06040f090302010f1b0f1b0c080102070201020c01050c0d0c05010906091b1203050d0c020f010510230109030b070302210a0f0e0d031d0706030209 74
    0x1c083c56900814501800a00c44071841c1c0070b00d55115501070408079030311094003c01c9c0c083d9556000c00320090303511209030070020007040c0719151502001544103400152401c1c030143c1440c092111110800402c07080c075094040c02c3c43c180d0784902c0c1c3d0203a5181086955006018001c2d0080d800c200c0c014080c0c800d04c000d00e503100e00140d034001c0081402078900140320b40d0041d60030b1079134500112403d54807900300341c3c0812184e214250500d4080c40c16094160440a400046540180c0250344910011100f21021070ba015040d0382415a8005001501500f064010ba18010404269102540c02c0c00c1c1000140c400004c9007104803070501c800003404002003c0300b1800c0142422004c2d000400c007140070008a806841d0682d041101070a00500d02035070410082d008280b100d1320050b082e01d21405001e4481000d1044c123104015072141088004018a03072143c544040794180e01c20581c4800e00307078610082c955203038030400e1050300c12240815500c0201070702941040c0a041d125081d4514104640e02 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 931925782 1250 931924532 931924561
    0x305060a0605030309130f050a021207021902010c030e09010308040f050303090d0f020d0c0801060e09010b030d141c0905010c080115121112160c02010c060e0c091e 72
    0x218010080d41c2000e24405c01c1c446540c02c001d07828009907844840c107003c0090325110f4a4040c0154040142c0d40b99a64803c0c0e544041d006000c01d821940a0759040164442c4d5007402024a50709184c03c507003c110702e0904658180111050550100466000004004030130008208584004200140725561101056185d01500205c10741201180200d600001e11402d10070813028802440300741c00f502c003a00c4102480d00302d5000400107a56030b9a0520800d0030080d40654040da060300203100c1c50301500e01280e21020320040401c04e00001c0304451600340041c1c002c0d41c00b07148908070080010415a6a8074001d44103600f000e80e000e518041a06010a20070308101e411f071b4691f400f507041400120030f412120500422450107805548410800c10304001d04010041e01c00d803280b1502d19030404c0c0401046048400d00c2803000d201041120340010703600041c07000e0500e9009180019110417004026081c640400c81d4154488540d808000141340327844035043da40315684140c030b100c13540d41916004000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 931927032 1250 931925782 931925789
    0xc010501091d031c110705160b03090d0c02150c0a123002040f032004150501050c03040302030607120f05600636090705040305060a06 59
    0x3e4000f048640b0304031095110f80c003110426408000313054158801e0650403038010441c00c40392600965070301480e0701c03c2c1401768030141c0100c820052641c02c0c45110541d5402955008005100e40000d8810a558401d0071030910401403003c8a03684100c01c64056481d1440040100d54074100300c0034100e0060721800d0001c0c0d41041c102c0c40c0c0c000303440880c0d00450504500c199041c080c02c0d020000807d09030300c0f9081c0000194442e10020038121079000c5000494404035040501892411001410720141c248081c4121902820480d94512840c116681548540c0d00041e401d48940001d00c2140e541c849007015002e00030840400c07005000c03001e601306454081e00d40644100c00001060140a0481c405c0202c40c9051000c01001248038aa0b50b00510784000224107041c02d1841618840204440808042035003100d01524015403820440036484501141e511002035084030b4504000c0f55622446d00c10400411101e03a03031429440041c40342d8403070300045030701e4014200070440c00c034241c0c041d95068 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 931928282 1250 931927032 931927091
    0x3020609240408091e120c01120207111c031404031a0712050c0d0b01091206020c16030605070318030f080928020909070f0e040c0b0c01050109 63
    0x74128407010000707800030701a10a032440c2d50100034070444d030b550f400005d40c0c404c2480b02d00700c041646020204100106203000403601500620340c1c28949a03400302020304402e8204c0c000503200c84641c10301c00f03003040d05001d4054102851424440b0408034101e0f64240749442031f42c40c200310404480c110000c5001b24400101503441000038000642e000d1142c00d81c4c014001c0c50003103110040319401c2410380e0700c19a4040809540051460400225405400b929034030a00b4a02092450b0544010a2110066015016944c0455000e1490000f0b005a5445116415101203031645900b4044001c0c0340994420020900d400b950002c040b2001080d000c0341c1e505a12000c400d020003042c11f1f41c46c1071006046c44014020310781000c84003561065582d4003010920f08006521950744140607880c50094032100469214210422446502c10109019600c002511030703280d4039585850071080340385400017501f108010900440100c41540520b04031480c0d0708080c0503411050b0b81c480744004201040700c48 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 931929532 1250 931928282 931928323
    0xf050c16030b0c0f0a030908073002070b0414010509060f040f0e0c1602010306091a030706110304120201020304030807030c0203010b150703081308030f0103060e0d050418060b0c0a03020609 83
    0x2003084c021f500c003840c11400b079850640b801e9601d6403407029401c401c80303c075040394211500d00c110307100e1800c24004490b41030f400144070761400d0070801c00b1140241d20505500c5e040080e40f0b041c241c3d2003032301940d000034000b80c42603490719807400181545401074010341d814820000030003c2d80369009460305005070841e03c0640e14000c0380d41c0584102120400b01a4141a1584400550301340d26204a0390405c80b05200d18082070841001c00d030a00489a01600800010070356030004224044100c5044500c5403514100c80591880140d04602070b81d0700141c44407801061034410b050700048040d000600c00c500070450186c00b00304001c0202d40000c8828100c140034440000043d02a0801c039030021000c0d08018801c0281e503890f03140545c02103410707900c2059403800400400c82603000701046c03c0300401c06401508c0010b500103141d4011846000e07150000d02d04540c08000155102801500c003600240c4da480300c0003c001030765544003200840c0103106100000351026400b0849c089001c004158061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 931930782 1250 931929532 931929547
    0x70b150f0d0b0403091e030204050c0406080f04060f05010b0405030d020d08131a090c0a0f0e0604050403180906150203090f0909030d1b1b0506070f050c16030b0c0f 72
    0x440b000c0006104906205e0075140118600541d600015880034542da0780c0b60060341584144815540090321a051440040c041403140079040352005a101220602060781c81d544c03030a242003d021455103419000d03207070a00105007915081c0007041030714410390440d40c0c3c075401303110300f02ea445400d4041c4032300142c1000c0100b00c80413488098170b4095806008840c2c0e4040c804600030000781c1c01a605201d06600080f0401440d08020140e00010189405600e8850f40f03042405100a0b100920301c5110702c0c0e070b403400541054003039a0480c84011040c0300b0100c035141c03501520402054107004030800c0440d05540b040b5014800030840d2500ca0020f400088610400c0c0144442008041d1058900b40414031801029003d0351041c80340201040111240520490380083c0260b00da43e50700450300f100c000c0102010440000c0c41503000240d0303252405400b12180300807500c0380151050b04035907024403c0c4103c040101c50340e00e03a09880c02407140840503207400c01c66440d1445200e040c00d0340c0060030710801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 931932032 1250 931930782 931930793
    0x1c02030709091118100c0f021305180106140a03020d24200a08072a080c010507080402030709090809130f110f04050f031002070b150f0d 60
    0x85400000a0405004150711040311800b034a4030f228014000c182d01041e054140712070283e41c1560007a0a031480c1e13003818564000200801c1e040c4001804441c0120561030171034940884000134101190410019400e040f1b000740d8500180e00c2e40b540c215800c10001240380303200300800e4008100b00600c100310071440c0d0b9081c4210804840c1051341c9010110f0603081c4407144e50076040c0c062050742070000800040880b035000400e01e030305001c04514501484810f0006402001958000700a0305080300c10b08080e100c0c01c0500366255800d00c0315404080005c0c010400d02d88050540402001c00034003c0741d50703106044804060840300a035040d03220302c10401c0401100d41c49409428003440c01c852074000d908011600018051645201c103da42d00203080401c24944184061001f0101d0b40c50700e004441c8200d4282e60086000711482903003840072155030ba5400300a11850000b4a1000750f458016a08118000400469182e0103021990703a4020f0b41e4a4095a07104400c00c009101200107021510382 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 931933282 1250 931932032 931932037
    0x31e060f0f01120e03031609080601060e0d0203070522050a05092d1209030613081902030c060717180a200a08070f0b07020d121403012301051c02 64
    0xc100ca596120a01d005180341030004520507a00788504090701c501c1f81c84002d00c040082d900c2181180c12210051250540c8003e8075400c81c5d8040b40c40c5005108a400003900b00407556214030f521160042c0b900e01100c59180c1c041c43e0b0114100803c12480d0f0362030070428256001200c20341c3c400c2d08050201288503d030003e4500140c0c1c40c900c6580500d141c030404d243d2800003805010001c110010401800034a410040c09130300254a4440c1e0750380a0f90359440040c01d000780d11f0085141c462240c12260018800c00c155030388000000304503899400c0c1541c3c0070f410610b642404074900502140010051216080c1620041b072031100201911005038a03a2211041401c4010105000d952041e0140340e40384030a2001401003a0301a2111a10340005016003146a60240495400c148010009607441c4404c018040c1d42000b4a10020511801c0465503046919a0002e1141c000700001c514024041020340d20313a14120140c0c3e90991603c0f0043d41c090140240c181170102610042c602940c055801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 931934532 1250 931933282 931933307
    0x5030304060f09030606030f021314060f040f090f0501050c030f07050a0c0f1a0a110729090d080105090f13031b0819111011040b031e060f0f01 63
    0x1400050743c0c0d2242c3d1024291121903109803813803046240044158600198240751724584400108200381c540b1070319840c00c2d4001000301e88503203420902e421040c0c0b100e4010141d0801e130400204003001e11407901d1081041c02f22415a074640c6040005641c3c40f03803000031a40641551a120006680c84820071526640103180c1d5030104404075850100161742102c12824162265003020300d000810480c0c80c05540380102150181c030306101e40342451100d01403ca5204540203002031401741c094114004488108650044440359250104015918049000100032000e0341e110040307a40d80e003041184440d0160341c41c01c4010011000b1421803118903070901d03403136031203420b2202694090100c00340d030300310f01d5050686500c800051b040031144200f200031041060349080030102040c800721f03519a107682542d00d140d411f03940c2d0481d41e51807110500588009011785065540c2e2403800701d07000c80088003c00480600511070602103002444c0c100c040000101c1d02900c0f102c000a00040111541280d203113 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 931935782 1250 931934532 931934537
    0xb0706090b1501030b0a050612090c0d050d08010b040303120b01020c04051306450813060206130503190e0d05010c0f08100b030c13060818010605030304060f 69
    0x161000c0016011450030340c4669082080403280702d8100001409039801a80c00605c20200c00809001c1580c81100342c50b2111080c980002d034039661130411034909207182c3c10b403540c411140f091040400c0320002da42c006078803080e61030a1550b681c0c1c14404495000f01d000c0100032407521056040740c04d056503c40d5108e42e00c144120307902d00e0541404142110001e407000b01d01c0715504ca801c1400e000d480c0c05440b5200a012061000701001a825030241b55800308040ca201d8030001605c80c100c1452194000c0ca540d0003054495a4521805200100030914458200035002d039400081700c500584032851100751b004030155290441005180f070041c00010102d0302445413200b20a0740c0b81c0c40e50380410070802e01c544000601a0240350000c2c1050000c0340c41441001078101c10007241102e0b0200900480c0c0320f0210032a12901e0f203050904d560302808400780c2c086e0310442c0340083c10030b0b4010001d600460b840400c0760340019a8942d11803d0b10001d0003015016402044208001c0b41714800d140348610051 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 931937032 1250 931935782 931935791
    0x1006080c010f030912180b07230f07081b06070f03030b0402040b0c061b0a02250e1e06060f090603070c0c0b091906080f09011d0703051509070b0706 65
    0x2962218003100c410341503100090484c10b60100e86111b10310710040a0103564508504102107035440801180e0b406800d460b441310140e040324021001000180d070103030549030a5400303940c1c80e08182030381c139011f40302d00786070724210102f1090b41c1e8107080080380c00c195005100d40603110450389043c1c011b0507540322600d4215508000c00142c40780000080c00001d4200005030a60b81414501c88000010b03a4008150400c0200711030148141c000070903004400b413200c1019400e40c03c000c000711141703d40c0d911242101014100700305e030b40d884420194068043c224860411600c440f001d00c0118045d04100c04c0c030f1004104801001c0d480c0071006564030403010300d032448850f05540e80b2640c010075141c0c400d00690b000842c02260502c2c1800c96140303070b56949840c40341854904a0010f043e80310203070808288450480115003d0f110039001445003500d00300180130b44c0004181300c0b65036140213110030388a034000c0c100803003240009060054040e4003000014000c180c10704441d003910764041c003011100340d036a4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 931938282 1250 931937032 931937051
    0x90c04090c031e02040b1801030f110304020907021c050903010207020d080d110f0d0f0906021305011101090b160315120323030c09270403021006080c010f03 69
    0x18001c112850706555404a4148404842115504002e4032020740460040c841400752040c0754003910255803035000006407949044006070010700c2c0803202c04880f103040c4100500590101c100842c050b40c8207075241c0900e40e8031800c0498450841807500030a54001d2004031140900c81c04c007810340c100006000524183c1e183d800159074100225003260781000200c1d9000c08111507208250b1100251b81805103000b11325181d0003040d2040400c95103515543d8803161110403090360000103e03a6101b0000c541d40d040103a084d03c000c0944c0c1c46510300195000d000f501400f1410b020f01a011580201d54201d50b88600744520001c0714007140b050100f40c1d0714499500b04845400a10009000226114503c1001404e0050816000b110b841450070905c0503e11026113a5004403640a4001c0c12826210403800340014000c01d580d1018485607a1118454100c0c1d40c01000c1c458080c0c1e00ca5022110840381c40e04145043c2c650600c12050035401c00c214160040d4010080800b2100c2c0600c2c000860120 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 931939532 1250 931938282 931938299
    0x914010329031f06080d031a1003020909011e05040b060412080f131a09011d060c0a053406050a0306080d0305090d030603050c0d080c06010e090c040614090c04 70
    0x1989071034140c43e92510000c1003501424030201809920520b03081c0042c0b007120b4500c440d50301d00304140901400c0400080000341d40300761705403032443c5001440c8103170950391105040380c00040c9981906000740b50f04400034841c40d00d4401c0e1510008084d2a00c0e0500d460f12010f103484210504043d102050104108007019000000500c0750404004041403a181001d07036444206406d00a0003000710000c001d0701000f81e0308465601030311200b0381d00c0c10190060341d0010505034094080d40003038600c14040c12204100d0302140d420f00070380b561a02003400356514401d4030f510112840002c0840e080c05039041c845c0303c3c4207200910508607c1e080210342c1c42d5561b580146404240d050000010740d0300c100340007842e01c05001c0c4c4030030100c2d00e14060200c1400c0d602da40c0d0300c80401c400e0032885090207401b1081044518002d0303c1c400d0380c0d070006a40e841e6a59001c012100c940880f6183c12074011001c03002da461030248640c0094a1007505140070f80140d0405203c116100030700300b03288000050100055008 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 931940782 1250 931939532 931939573
    0x12060904060b03030a090f06090501200705030d080a05060d02060f0c0309060c1507020601080309120a02061204030e03120d1e05070504050103050109020922060b040303091401032903 80
    0x14486e596421200e241003035102030010203402050070403920303800030480c50b80e10030305591b82ca00240300a07403054040381014529083c1194019901809080c44607412290000b84191140040d45024402c540d1003a0400c000d040000800079808081407040b691a400c181014200640c00101240d1512124100186070798014509541d82c0307034130102d0740d5403c4060007110f6035080301441c0000d01055041202007a241c1c011072850314012809040e004030000000c1200300d1100390007801c450b5881000c4c4403d0318004404032000d03800314580c00a284071601300003a20800c00ea030141032044c20310410f000140c000c0c00040c0600030408407039040211220300244203050003051241c80e0725940c0ca1802002504bd100b05a10500300648141f044070000d454000c03002c51404020010103d800c40d0a802c290010029500318028841020401100b055006500c0d1070645204440404a9601c2c0000443c241c48180407200d034504411101101c07c1880d4800703102c01c641e801400da4104684100e586e50002 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 931942032 1250 931940782 931940797
    0x7061407111e010e04050601050904090c2c130c061b12020606010f020f0a08071a0718050423060f040f1508072412020a1206090212060904060b0303 65
    0x1039200ba01880e806681025503664510300c01c1c4c80511040c42d10384006440d6000f9800b0080c016920740c41d88000b008042103600000c1d040c24914520340c0c00c0c4001c140008405a5007081006100300808124030400e100701c0c09031956803140101d83c4450820310f003121202d424001c24101c410b003c1d2014070000d0710303a040f00c01a4052a600403c0b8500d0841c000501c1e0541b01403264041d500311000142541c0c0c004510006003a40000c60b00740d6488551506003900740e951011500c0f410034140911a56507840300f062290500403803405104580c4481c00c0008039440740e1034490381d01c414812045c101880d005106da90110004094030000030341203012a060341e40085045070040d03030b03030410b4041c10350100e09000045c20402d401440001e050004000c001c41008001010300e1440a4a85401c18070840700c1451b4103440c0e000664071382001c54000b4110142d40c01d54110180d0401d180410b40c0b007914404e90b071139032051180c2034516460712028803c0b4480003070001e450582d16031200724103a444c204000c1c00503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 931943282 1250 931942032 931942069
    0xd020f120f0d091a10080319050c07030506070e06190309170d06030c080d0f181203050306030607020f0706030209060f041e1202060a0f020a021f020f0706140711 71
    0x56881c13400004200c403400038020405118449800c1c40084c6000058030118010418000c0000f02c107c1c10541e01c80c080c010644643d440f54681c00300030070a02282c4580500b92640f14560404290020000e5038001c0092002c680e1080000800106e40320b80c11805481d4000d020344051040060803a441941c40b9205c010501c68807241c040082007800071205008200c028013914800680d11001003454440b500d24100700983c03e0202d01000407200031a03001802d00d000b0710100d80b0000e140c0503200f50800c450040c828051300000940d1680081441c40000710090007a00d012801c18000703500a410902e48107412aa00340510040580800010405003415680a58590462400390040d0074515004081c034500781083c5400141c990200751105031941b4181444507030a038280403840c05071807003070182d4002038071600d800c074a141070451400850402d44c00c1d98603200e071100c9030a680f990030344500b800044a04030b88403803501050015103080f6214521081040120900040c42400702109a019 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 931944532 1250 931943282 931943303
    0x18061818120405030c1909060e0103030f0905090105061605070605070c0b1c1a130515090405210c01020406022b080105040c2006090d020f120f0d09 65
    0xca0100c204011104145a01ca41c035207000e003088042900d0351038031000c590060b4001312030b143d80c51003d0000c80e4060040d40c5400c010440c0d82c3d0201040b154400c0c8400c0e4081501442ca01254600c40e4003503070165240500280a04d900e0503052007015404218260081020650340310001541480804010807440c0e407425142d502e54204004805541e61005020f00e0b01002218001e20346814946a15100c40b14009079100110480300b00107540001da459019210b50007410200c1030b42e5102902a500b1111003110815100c81840741101060360007034050b500c0030514900f80288004220101044240441e05180182044900ba600b250300b010015030482030700c00c0c0203103810b03011044011140e410520040f18000c107001d4080c98060040e2030007213403039a101c86603150007104841c2400c0f451803c80c0f0090001c0445a507180c5a041e02d60750000e02410081100d100d100050a40001154201400d106c405003a00921103038400350201c14842c07000e01007540c83e424603118416042e80079154082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 931945782 1250 931944532 931944571
    0x503060409050109140631150c1205091b0d110d0c0e0c1c0e121315020111030f040201031103040f060506010302032a040509040c091a180618 62
    0x5003001d40041240304080c081a20505181714002c0046007c078468126410a015041c10004040088208180c48071810544800d40c080e62200071814100c4890100300485e4079100240c3e03880d4082c0100c08088080319003d803050610b840410388071010700c142c0b24068894042d00214a4503c2911819101c002850b04200111903070104065441203061203032908c1d101204000c4039844442000350800169603815501421904110307000c0e403200200201c1303865809403031480c2e601080d14040c1f0352825a1040001c80d1081c01401002e0034000304046843c207541c3e846d8020007442500070800d0741015140c448403080740d090b070801940582d001d140720701d840d01640d081c02c030140d40015001504042c8100100108949c3d014840f96180036444c4446101541160401a160060380c0120750300204040c02d00c020000240541c0040381c100c0c480c284841224222410f460b00308000740290403200008401a07000000f00e0201d501250081a440008009100c0c511074604101c86070050401c4106058 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 931947032 1250 931945782 931945823
    0x2060405060f01030210050d060e240f010206130f0804030b061c020303030601051e030c04050a091e05040201050c010c0e010912170313200f04051302010503060409050109 75
    0x10b544031030b5902c41000c03a07501d194086840c204d0f100e401c00c0d0801801080800080c41c680d00248001c000c01200107000d0f0074184840f4215503115059104c540c0121070012855040007111110b0102058014000c15907410607901c0c2000b0300b0720380440340b8086240303c180020341c1c0c00000d00041c5001c4c00303003604107117071142c18003080c0a00c90381041035001c100720000005950010032641c0c00fa10a10340301c1d8450760380282c0001da40407114032807102c0a03c0401005540c54010010380101c610417200700071a03541d104882e20464040082194001c0300c94072000406400390342000b50050b00c189400c6180403100d04044c0e0840d041000010300050b800b2207505890342e4031890940260201e10011468925155190050f500c0144240f40f01042d000c80042c0540402d0300d81c1c1c0303100070740200b81c02003103402c0c11a1541c403050030040c68034030030301c00e081e0200600d042902c034251150200d038114060803141c82e001510142c100520700380d0b1281e01c544030240040e60a0040c0c01c617007849162000071618040620 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 931948282 1250 931947032 931947043
    0xa0c060f17040209070509010201060f0e090d08091b0a0b071103010b06040b25170c060a0902010c060b03030915030114030102090d03030c050409141005100c0318090c02060405 77
    0x4031001e000000500000d40d55038205180c1000c650700b000c60341c80d03000034010307400341070b99a101d000c0701c0d900e80b0000944d1200036070100e0b10903074445007070390120b400411041e12204c03c00d41c1c0380c00560b0702c00d420304443e13240484003480784540002c2071440c2090740d401584985601c81c01088500d60b844a900714080d007024025046008811103031103040038182000c0f08650300034855201c1008c0603048815072001441c840510080380c10030318103a5049103d100004407a80448a042401c1c401c03400000d48003480b61090f8140705a0580d16845000c6007500e404002d003800c0601e00d94180000c02201c0d0725035030386a0701004010380b0814013503100d40c540342c02000c1e08800010664020390040280e06003c4d5203074042220500e40c5820001003a5482074000c45040c09103400180c0402e01d0404816182001013105038407585650000b851000c1d126414821320000c5206200d001c00c002c020782d2400207000b4458030300024420711002d01c6c0540d6030003440040c5c070400b95a06015030003600500c0b0a00406001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 931949532 1250 931948282 931948307
    0x309030d1b17040c05064603090c0503010608070306180209061201090b070818151801020f070c051008010315050702030909010e190509030a0e01020a0c060f 69
    0x29070815100d9146020b030400c0c0840c01d01c1108050100300003001c101100ca1008058140a07003030350344a20f604549101d49951401060781c00008040518000480509150312850f0b801c032900102c18500c02c400742c001e0302495008036000d0318640b801060a407070910441005111710801800303024a941480300459200c2c1c04440b100f80c000740400400b60b1a14040c55400c1401620304418590001e0724460060410740c0340105000000018000c48a80c0f02401c03d000c0d2070600320701550030707241003403c80e604e4a02c18403e900c1c400c00b0f2000212401c81d0802d2440141c0c511f4000036213030050a407400383c55680006000c45100040c0710042c4003a04080d502140c01030403a08200101d0750560b15203001d07a14a02c1c0100a9682d120400604190b00c00d02c141c502c80d5a001d0848903240d40c54250002c1030190031250590035807103076101410081080d0003007900880002000c1d515103010102c04035240c0100c511458154820420380000150504200c2c4000740300644c0d410341e01e151400c00c0104a0109d221 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 931950782 1250 931949532 931949561
    0x4031e120e071716031b09050712050c0702030c04020c01181a0603070f0b090105091f08070323040507030f06050613020f121f260a0b15150309030d 65
    0x1604c900c24450340700c01c070000c0d01d40105824180390301041081c0701c000c1c03c42d00700c4030030641880180b02c401504500c6170107803c00609402d1100340d841d04040c1c0c405020700c2c00043d60550244450328402c0c00c05600070300703100c5090400410105a16082400545414001140d810300710300e003200207121340e02c040ba43d0041e600720007800e1000c1ca40140c8101c0b17805a0b000c1c4061040c0300245032002c6038001d0017100e042c1c44000e00416410140c104d00c140c82c1180022210002c1441c04000444c020320a202d80c103082d03104c4600c0c56401c0c0c01d8071007041500f1000184101ca00740701b0360f54040003160a401d13100428510405001c141d528241050000007508400c018140754018424409104602d100740d0f1140380e0f000349807038030555030b800700788502c4010500d950000c814040c07408561400b41a006d981208000040469201c1f88010300c10750b52008140060b141c0041200411103072040f01c0c17034618800f68020729000000c4800c0c2000e002c60741c815640c24200da4030014030b0100802503400b82d1000a59140d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 931952032 1250 931950782 931950793
    0x916081f18030305090717030a021204061409030703050105090313060c0f0b06041506021b0f0a1703120f071106070f0f02030f07050303010314010504031e120e0717 72
    0x190140300300103081e42802414142c4580000750030110801c8810300629010070302d110038a8003890455282c0d4000880f90006000b5000c1c1c1c0c6003034019030000c507030403610b0350740d2400040ca0300c45a1240e1550058502c0e55818000d940c1d001001c43c3c024001d80d401541803002035651010f5600d000c01d00303e8240e600580600036420403185c082081465081d5045400c241142c200f940d50070001001015941c0d00750b400c803000c0c504c2c00700301d40340e000500c001419242c0b0150818486001c0400c1203440d505426540e1261b01501c00780000002c0b001c895900f0000482228140514034401d002c45003412160b41040506100070020116070101d0020080285900603000b00e00b0151002401d00d0903603510300080c0503007551f101b007845208004031644030482d805441c0c4c0303620040ca0200d031243d1080c4000d507400d107500c04910100407410f1184500407a41522034045032166074a80b1407071002d500c00081d00b4011a000b451007100242d000310b602c1c502580010f0a000323810401e081a51a07a00e4800d4005035009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 931953282 1250 931952032 931952051
    0x7050603010306061d130b0601030b0a08031308011107080c07120b0412080f2404050405010e010e070807060806060d050a0e06181203062202040f1403150916081f 71
    0x1260f0401b0240c3c3c2c10001218095030b0700001640a420040300007038004001c03407c009404070b004006803442003000d11060685c40d41d21550203003680d00e82101c4528903081003051100140c002002004400c910034141c507400c541c0c03010f200103542980c10f8252000c2481c2410807080042c0d04402c5c1300c0b1000c550401c5101c90514150700c010004004000e410001551082d0382c2400280c00500e801c142002001800146460710301280a0300401138045103960800501410b0400e02003141004d8a00c0d2400174031840740780c800704440605016101c0c03500000108070704018613180340107072803140800745000304a520303590003000d2500c0b2009145481090080340ca01100c500046000746611401903e01c42d1280c480d140001c0910f40c0308035041410100d07444c41a91541c050b500680100c4079510004184a690750641024140360060490390503040680e41c44031800302e400d51030303401041c50803c8070f00c06d001e900607560300d00c1c40d1078101885079449080242810006050020030180d020703c4280701310a80c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 931954532 1250 931953282 931953301
    0x62112080c0324040f0f0608070303052203021509090a150306201b0c03030a05160609052409010b0d021521011706010b0405100207050603010306061d 66
    0x2001d0090300941c0721080401104500b0303d01c440ca2a420000c004000c0d0003108a550002000c061140d45d00250401c4800241c00c1c80110b0b02c08101ea405883c1c1c14a00355040d003802110561286408084200e4a8030200160b00c0300502410755964942c801a0317100f0040301003100901000b0562a002d0b1b003000702298801e0740c14001201226030014001c90607030311941840d110090805400c69601201043c0d0a407842c3c424210115041000b0f400c0d600000c05000503d82c80f803065a044d980492020088060000c428140306986940034640000c0c8440e420746d143c6040c001041d42d00170084102440109210503214a4150018190b10007000b5019011000c0b0b0521000c036000603105400d0044401c107003280110445240c3c1c1020015a2000d401100788407008075801c3c05408940007850002070f403049c1d0f001806034162000c4043c0182058038180402c1405031030500f43d2401c40c02220b00c00611500e44c0c00c01345000c2c40c030840380403520300e042c0068244041010701c003009400d010503040c40301821 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 931955782 1250 931954532 931954537
    0x40308060411090402090105120c1e0708031512010e010219020109020a0302240a050703030507170f100905010e04171305210f0a05010506030a05060f0703062112080c 73
    0xf4415600580c031140c2d00c8005032414010411031401c0ca260200400c004004c02c500105880c20b020302d072581071072030406507004040c000d12a0047c0182010130124000c00b0201659600d60300004142401004122507240d096400c1404e0448440c1c1d004030781c421080040100200c80780c14944020406403080b500081d081405601c000307401405030426010050307480369440c0000c4841015043d503100d803050001001581300c5001500020301d0900841d208a204204940391500c44032001e03c45500c070341c01d041c0d407800c40142400e00c2c6a0064140000c081d041d6000f41c038000c1c5446402c1408602e8282020203d94101c48050510040100200303544041c0d04400e60065617000d44142e070a07605c1c403560714841d06d41c55503a008900e02c110100141080c07400140000d60764410030080c06262981720516035245000d5000900c2904280300041c2028414100554031541c035240101e0382582d02d00d210303524808a107186010b61150348003140203101d4210b262004154043c51704125901d40150142c0450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 931957032 1250 931955782 931955797
    0xa0c0b06030d020307110415060c0203011401140f03100c02240103081e04030204020d20040b04030818041103011d07080a180c060903021207120b0703060e0708040308060411 76
    0x108003180340629201c0c1d030302413a942320340c28240d10200b0380ca40c0400317070808a004601300c1c4a5802d00b8013041d031418284651038120384540c1e0114400c207003400200000015000b807982d030540309e0340c0d111100115940c0a401d10050b0303140c0140185038454102000e80640d5089185a500200750040001640000440e0380802109240101d40aa42c0b400d00c1010710540e88040d5002d400800c02c0761b07a4141942c8960102c0160901c00c1d070380400c48000c0042140030b07610842c00e2043c01400b0410109140c40014944e010720f411400f200c03500c00130b0006040303855641000050480200041c00184c41500d43c1641071400c4144102d403502e8070b078000501c154402064128500e4a070071001441d031b40e00c03481050205c0ea1007400000215141c44c4010501d0103144400c1e8031440045000e16604040401d0303580507a8032060000f86050a59100d00303c2c2140068259010075649540004086501d050414010b02721651601c0f01420681002031640c0b501400c0584070b9031074144810f11502804046031007a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 931958282 1250 931957032 931957043
    0x50a14061002160e0f0709050105030703090602070c080304170f1f020d1d0d0306080a0b0c1c0c030b030c0d0b0907080303100509011e0b1e0a0c0b06030d020307 70
    0x100c60441c4412418a0080c54812220b07034030fa0000840c001085600807032054000c3d042400e500e81d9260700440d10b0341e9183c41443c1c013141003040440d103418400e0300140c41040c004c1002510700000e42d81d07a140c031051507a0103060250004a818001c0c0c2c005000e08041412400000380b00c018071200d0303050346400a0f4100e42000004214a4440951b09501034900b0513010110420682801c0c41d0014140006941049210302030120f41a5106000b0f01c2040283c40140e0001c261a1400b07540c2d0944803032003c3d1000c20700101c2400003440349501440f00c0842102e611b0b401103000170b4041800b80aa0342c0e0f04a0852080c0c001c3e086280294481c400070030800b03508451090210344400c02014101041a000080540000410070950b0007480b0701441c00c941c000d440e0344040380e980c3c0050010001241d400c00318142d44c00d44040029510300c5000d001102c280700c48c10115603403004044000f5901010030007012074002c04901060005082d0f85560100b0180c0140030110ba0304000203440c3d1040c000020301 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 931959532 1250 931958282 931958299
    0x317040f1a03190906020c01061424090402090a030305130504050108030a18080703050705090c040e04031d041e060b0a27080604050a0c08030901050d05151e04050a1406 74
    0x105214603000020207a420000442d47d40349400c029901a00d410302902258160540c01000304d0308000e040c0394042484084503c80d0000143e01e10074455200204159021343c0078806c0a10950340c0148050045100c1c2e16843d640d440742c01410508401c15070700c0244164036240c010001203030013008591105505141c101300840c03044244400300071107500585024030a84901104006001a8180c141e600c212400c00c11503540307007402c84240c03266005402d200c001d03003004031300021b00914518a8092418064100014404d400300c0d044a80400c00c038107000c039040b07420843c83c1c1418031401d402781c850300701c019281003c08540035068424402c4010b85c00c54080d5400444c3c4400c503095603020303000d0041500c14034101810020764414140600340d508070224000021108000000c40f074180f403060f1222414410300055038001454021300110020a40c0805c0f00415500e101a07210100402c0c0168454400307154140000c88600402030029249018412034030a05d2008207568041c030212051007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 931960782 1250 931959532 931959571
    0x15390702010f0c082b0504330f0b041503050c0f030f0a030201050702061510141902030a12060e1315090c05090705071212060317040f1a03 61
    0xd40341c08036140701070000140885d4000425031451140c107240298607024162580e410030f01641120029940106a031010049140309103846210700004c800f81d100f04154aa810108401c0644e811085030030001d0f80e0710b40618a039850980326242001c00030740042140941159502640c80d05200c8c1c000303214400500700216584c1c3c04200c181c8003c550303100bd40c0c610803103510f0068081c000581b010f41c058010000040c00e02c0030800b10207000040e00130f03c0320100704851402550201035588480741c0c0d1000c20800c2c1844d642d00c08040c403450f068903034002c0d80d41c0c41c1d64540c001c0a1150400c150503106e4100b0390100400e818150683e038010b82c418040c0034800440703242150590710740c0c444900c8030504000709401806141034151003240c100390b4900705903544040c0c0403200761140f0400280703000401c0322181e89a900c25014a41d11410720700300040c41c1a12500c44003111a40321410300c042e9400000d092082d803012107007072001808104810a0031220302041169180002491009110016001030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 931962032 1250 931960782 931960787
    0x2205060703051b1306080901060f08030414220b1c0f1403121605210f01060507051c090810020c01180c0e060a0905180d1b03030504020315390702010f 66
    0x1c03001484a140c84180c3c403507039520514cc4035001303445021801c2c5044c1d00042c03098140494400d000340c2d50006c5802c003110402c84003500400b104404035030030030610a2030200c5074041c0c0b070306500b405020b0030308201900614941841840301c103a80300e00780f0750014070071504549280c0b9142034100312408401c20140904440441d00c074020b10344007110201078800072044014401700028010b9600e07036241942a81c80d101c041d2040d20030342100801660140101100444004800a400c03010320b00d440d0710750594802034503113400d50424988036003a0340017482e032210352405d1080c6100c4a850307040b860708011050300d6a05280d001441840c41915074034000480c04e1340c030a00007601400d26000200405e04003802d14a141c01c6005c040c070221b51160b039010803810b41c02222103054409150b00d207440d0400c140d03a811006410040c2049030184074000c0c0e4006d00403c0c0f0749109100c1ca101c401180e662551801300703003e15800c2d904402070b100014071800e00103443d00740c04840360290282403c08002e0f020130000c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 931963282 1250 931962032 931962041
    0x10507060f0c09061b02101b06050108010c0801050901050102070b0c01060918020301050f0c030109090c0e0a1b080105010903030806030f250911032205060703051b1306080901 77
    0x140154600d003544102c1600e07040440d000546019036102910000d03800f54241040d18040c501035400300701c241d5404070041c0310321908280d010500e52840c0e040c002d56070b50182651400e030003014a5945440094210f80c2e444645580180300131a6001c016514210020303448014a014015003403000198a6000c0341003500410020024103408000350716416900d40244000203808a10039400c10001c0750f40b5040768611280034155000c00540b859203860300190017496580000c4405036107052001500c04a5450712074418808504040f03000001041d10b1142d4121041400f414810344400501550f6070199140c0241da515060200440d15420300080ca8030507001400b4900341f03c3c50a22140b580201544ca040d110440074003482c116888a00540598040340c1022503000414400075900849118044031980d030107031440c030b45005280d102da5081c408211440004251038600f8004c01c40704849a81d0f0454075054849170804201c0c0c0031009610800344100700070007000c0700101d59590400c2d400b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 931964532 1250 931963282 931963301
    0x24120b0601091203090e0a0c20151321021209010314040302210c100203070e0d0605100e04030e1224010f080a0510091118150103021801050706 63
    0x1403440b60f5000078a03005101c2070940c000d80250401410200c1e05190140c05080b480f00010f496251181803103d02041070705c00744081e1410240b0400f88045410068540094061000c251b0742c101851f0050a0844070305c0001c803002032402450300b030307031304c00c8d0030f03404202c480c02c2e403440241c141d65540e10f00004030042c155142210000e050208140010541c0000708450031100e203024195406e4483c541e030384c80360300070034843e0101900030440d0015404403e50040d07034081c0303030b604007a1120051080400c03820620002c3c2160030582c8d41c1e0a100c0250040c00780b0800600c2d00c00b001141701e01e426540100b40c5480c00800038000c207903514140e401c110090060300301c009001d4034401140300e0b841442180092081c855104d50000015001c60080c10114113165429000401001005040e0300200000c08200030b06540540802e40b03a801c4640d9448002c1c40d80450030441c840b11401c240744030050000c1a000e03241c0c1810b00c1048080d0304502c3e00380095940ba102401d25940b41c415908042010300083c14 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 931965782 1250 931964532 931964549
    0x302032109060c0307020a05040507021027050a1704030809090702071e1a0403050d18030507152c01120906020d05070f0302130b071e050124120b060109 67
    0x3e00e445502c000040584107050003100d0700340002e0b950f502408100e40c015101440103030001c04e401001813000743c01600c00b8031400b20340c0e0b89181d01d0061004240d01e01c611802c80b220b400c5100ca20090003a4400d1440d0802c02c0740300d1152030245155204029071142d08070060041c03180a00040d001c5009024060050403901c2c8580b110183c00e88615100106c20f01031103140c03003502e0b02c500c40340c01c00d4241560286c80e0311100074110600c00013001d44041c0c034004520b210030120890040f0000310140071101c014810580b8500c2d082c0d003965005406807021020300b14412210842c42b04014002401c02030b0b1b8542c3c2800c1100302d0700c0c61002c80c0c401400e040c2001030301c1d60b40002410070500c105680558860401c560b690140d0020032107080341a40b0441e000703139102240c001b0b01440185602001085424880da60a411400c2e81c14110703e1054104482503800b43d43d10303c040307046114000c001e039000da844401c4641142d802c0011080221407402405001c0244510005440d42d001d454107901030001007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 931967032 1250 931965782 931965787
    0x302101b200a030b0a180b0411031c030f0605010203161e080c030c071203050301090c0e0405041b0504060501021027121b02010f0c170a030e070f030203210906 70
    0x7424030030396064040e5082d240c0f042c90702413071b0030760b220702590a440d80c5a440b14882c1307080d03200e9413500c055026150700c054ad0306024100c0545190b1901e020924104002903c01107000c410b079030b40f46c1c03084980981c051415900200905121815004c56010020b540038407440f03049421035582c140a0412500e000b801104001102e101d0b008002001d0704110361000112080c150316010004601039102e040100800c0c8107100500452081d50000c84c1d070103c035854403074805a2a000010141d600c01e031070948088054049070a610f0f0900802000034120940b424400c061800d00000c1da21140d541e0006e0f00c181c0d54501003090005050440b0070440101a4010700340343d0070342464145c4032140c54400d00030a0150400f002c042c0d001174550a07070301d90142c450f03081019400c1004c1d14014000801150040e54804240d81010001409010049050741c2c0001c0d10f044140c0301c403840e003401c0385c022210000e45501c04000503034001034141c0b2035040d000050750301d0248140601a160089140c00c99000201 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 931968282 1250 931967032 931967039
    0x10e07060c060c09180b0301230403020c03060622060942050d0614100e2a0f09030304030803060103050622090f05160302101b200a 58
    0x14181d01c031100c0c000c1d201001409540301042e960703407016200310410003019500a042550f03955201010b640300140010076822240c03100580700b416410850000f05006e0404d1100b0306904101d44e00c54810b0544c01440f440c2003020000da0b0070b540d0b50062116001c604401e001c90340c0d80030b0304030360b008040008050105010004880002188280149158510501c84120000691010451945145180ca510103400c00040c844081c100107000c3d51010703200c4a17682c40c0c42810082e594030440707002d817420007098104030a44500f000e01512f0100100481c030b038002042d901e1201c543d00426a00d03203003a80d8618008107600040d0084800c115450300020600005000c0541d005600c01e103004d90b000c1190765503107400c015140380030302801070652054040000c20301da02d941c032000100b4040c01c0704841241840c4d4070a480d11040d09108004038544840403c1181411003100c10440c08608104605c6585001c552001800c1024064100520903500e01c07035860410ba041c0500c408041c01c1c902400e5107 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 931969532 1250 931968282 931968287
    0x1b0d15020a12061413150b03090c030a020f210607090501091d0a020f0702061305090c12151201050709030c1e140402090d0b070221031305010e0706 65
    0x44005440c010a810b800714044041c8144544415113850510716243c0319010350030b1100d60352022820a07241a40e85900d03040704410403104000501c0d010740c54994900c1c1c81c5e28401c0c00d000304034400c1806a0701807889140140c0e10b050a141427014141c506d04d18980a00d040451400083c2e81c505a00380201418818800d0b400700d820300590f6001e0300c544280b00e5880e42d000c0043d41c0103043e1405000d0000c0003041e0610b0440d0014140d040782d46a045040c00610b0b000241c0d0342c1c1c08502c09421080301d107441041142451b8171103e9121000d00e50b100c2c104040c90084031061070005000c0c0801111140424805581d200d00d41c174002c8500c0c0c0001c200170300d020200078103c843c103400141ca1a242085c1c000500000c0148841d80083e58551904002c0d4030300440c1e028180c603054402c0da4019001e201c400d0152710f070010000240c90052114100909000030080d08220b131080f0045401c49030f5155505200c42c030801241d400c16484d0000b610891000d0600a005120b91400602580a452000140d069 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 931970782 1250 931969532 931969537
    0x50f0d05090105010608160e2803020414040b010315090c090504021518090603030717070308131e020a0504061e090b010905061b10021c050402031b0d1502 68
    0x80000704041d90721408151a06d40003140c2610b00c0610b59125681e80d10720403a0702608140340500417940b000e1282880445040d90b004c1711800d9194250402c00070342c50280548a8401605405044941043e49840c14200300500000d0f08541d072058462100c145d55520041c01203401000c112511a01d034880c500c00781405030740a078407500b040342c80f000d04807071030808031034281608642080705201848103100d9201c000401032030f4940814071048001c100d4148140a88080070802e880ea5007201c2e180280908602824549a02031511642c10028a107841240c00240031245002d401d0701541c40040c690f0b182c15041ba540240c2071110010302c0a5000490b1880c3e10168a00c612600b5103c01090048408241e807050001e08a00000c20a9007008802480c4801c01d6111102142c00354082241c5040215a1031100c55030f030000355603040070b01401c0400d4501b10320760801e0003141481d800083c1d864150780d50020368451140d002581581e2048607001c2c0c0300b076000000240307031000c1810110094 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 931972032 1250 931970782 931970791
    0x30810050d0c060e041401050f0a03021002012a0504090203060415030c06020f010e120306011404180c020102030610052b090b060108100306050705090306090d1209110d0201050f0d05 80
    0x30012600303c0900e1820340111a142c01b6107140103541c9070720703000c2049510110b075038880d6080721007903a0100250b11a0260940c56103042d40000c6520002d800039917046030341480c00f003480c01c3c0c858a05505401c2c1d1100c12103040350b03034032000544c03070b51620400240104640761942203140c854100010421011103030107001c661054003030f940707a40132075400d50703007650b41604400a441d04103149800f4122118006180c0162040c54002207409001103889410340c029040014120703161204107a03104001d0145404040d01407000358214141034021a5002519480d05030510001184031070464003c00c894010315801001c0d800a50340d11542a0b500811040c0340545440403160b0000760300d03501541c91140075201c04400c1c141c42310324607101d1707100400001d007800003004010458080d031a075081042602a114036806407014480340e440141c0400481ca1894590f1b6041c800d045002c1038840d9080c2c0c0c44080c05a0391040500c000b40b0040b41e2a104a00411a03045808911f0303100d420210b91005114 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 931973282 1250 931972032 931972037
    0x110a12062a0306060f05040503030304080d090503040815101d0a0b150304020a0e07170a1803021e0106180e071d04060b0a050907030b150a121d0307030810050d0c06 72
    0x1c54100d0a170403505c2c1e100c0d6026007a01940100041400030310410000c109007410b1100c0005c0620b2250746142c1582d10030340c0300400a0780445042d50310800c00040681d044032054a00312001441c0400014034441190000804100841c00203114560940c03c400a903c000501044a906d000c0702c1c91969a00140c500741c8c042d90700103001058541d80010041c2c040c080310f40794608200ca00d41041c0440150080c2070481860b11000b000c0c82c0802304c80011a80302d0700c01e8015107032804811401030300500c81d202c000d00c410380c1000c00c1040026648002040c80210101c030100b0b02c005c15a062038502001644030b0ba00d454411089101850101074015000d030784200d00130b1001c41b890350100704000180340030f6194883c0344c40d00811182c80c041c0d4000e50312000050060201051070034134001c07140c0c00100280000c204144030003000103c05204400c01c030700840f86e450800c1003210040581d00c1c0141640141813244c0744000c941c103e240d51103d1401041e000b480d48071f00d9415850603c0b0000120306c02c1e54007 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 931974532 1250 931973282 931973297
    0x32f070e0a0204050108190906020706020306010e011d010e120f1e0c01050f03041b0b0a2a06020310080708011a03010b131107050f0703110a12062a030606 68
    0x9401d4022a03080314016924843d01d45ca81088040c1206032403610340d400355035180c5402001a00a0000d042100c0c0540c100585915081002403c0d0315078018080b8104500401c0d91100c07014a802c0c8000300c070f003084ca03042d68141c00010100341d5641d01e0070601e84080c491040c0300d40300b030440000d103140481d00319880e4081159101c0903603070b40c400e64984540e0200714203124030a124180407010755449402240c829000b10614401540c101c20303581c0010320036020004844071616007214040218800140811080013000c0701040001103140740020202134000002c00c0c40754005111290240604034141c0d0381303184c0c0c0d40100e45d0003484580030040704031540300c11101d014a03040c41000346c0c142000d001c10340b1440246000100405034080103c03100c0d0410722815001c10b03010000c0e60079100c4240300130a8050b0442c14a400720300e00390052280f0403007022100b81f11070f00888c50a503003c1d039071100313010900c0c004c803241c180c500c491084840403400b0359451206070510b074150411307011150303d41c403083c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 931975782 1250 931974532 931974541
    0x170a091208011d040f1209030b01120b010905070509030f07051509031e01110a081012120305071403190609050603190203070f0e0106031a010903032f070e 68
    0xa03001c0400344542210903048400501e01c218060b040c0d04e501510803000c00c100700690366682c800681000310781000150081c0024410890400300c12409001500d041c0700d00403034141da408004a00c140240c104207a1100c01003250bc40c0100e0a90701c114800070300750381034800c610250b5681d0b44620710404c0d101c0c6c042543c0d004c070141000340403102440c2c03025014000e00c80c8201329000e428610008042c0b43c0b5941c85511503243c0c140c003000703403001e42025520702d001401e018500d030052003a00d40101201542d81d58140700090100140c528040440307007000314203543c1c2ca040030380b000c0c603182071018084000081081420450800c02d1251450707019010040203031a036454030100c8204561701ca030141d000c040c40108041e2540112180c25100404503040541c1362940c2450542199004442003a142c900511406426004c0c5003000c0c449109610f50103c00ca40008003031754442c0c413000d414018015002400b00d00e824090123201666001c42e800000c2031003d0060307903803849100e9a40303514241404603 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 931977032 1250 931975782 931975787
    0xb2d0d050a0902010e061e18041103010609051c050d0c0b0702010902010909021b1c020f01111204060e0f0706020f0304030213050c070c0b180405061f170a0912 70
    0x66120b9501a0b5070008118908000c0c4000d07940242d02c50710600c080c040031000d5541c40107008104d05581e140c0c542205a504100344000c4e47d1900d6105160100c00340014044075510140d80000c50700b04403400010801e24895440b1141410b0300041e1a0340600c001e2103c05e55003080c240290244286503240e8103a89514089080310034500000b0b00041d800d00c8100034148a94019002424001031203c2800010290003458010128101482c0c40e01009202c0e160540503c510003401c01900d000b0300041c503c2e0048c03855144202c00c0d03039200340c3d0a0013010a0900000e035004290011011045605441c161045960361f00803170321a0350010b200e2030500703504503c40401920201c1e58003074042c00d003140403004840094000108034600c540002d0050342c0104140c988128000d003040c85000c0d0b540e4040a0b4908182c500010803280182d003441d0a0103070076283c1c210140c03010000c805140c071020101000031100c41e400e00308400d200f51186002d0020fa64610390290003040e1040c402c0400e18454a40d09 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 931978282 1250 931977032 931977041
    0x6130203010905040b090307030206161701081020030109020f090d141905060c091206010914060105030108031617071b0603090b010608090a0f0b150a0503070b2d0d050a 74
    0xc00507003145000c0cc0301c111241910160783d900700d08000000707445c580000040c0160036400510356038800500c5081021851080041641403034011a04008000350900442d00c01031241c2c00c00381e0f80c0000e6000405017003a0907503440180041940000c0e056500300341e20b440c0c1c126141d2014502440001c0081c00b0310038a0302d44d40d0142c2c0480945020b54800c880b110260304040c0c3c91a4008450135a4840000c00900402d4060118248005412a050444448045c0300186014180f2000b04010b002e804030000c01c0e101880a00700b00c0b81c048591a01c1d0043e40d04480b401d0b40445041c01141c6001080900c10301440c5016450004c040c2e0f5940d1818200e0540b481144041d108100d20801803041601c54207100e50301541e00c20444031a012156103d00c8042040a03040d1950845041800700d034040000c04401c1c03410080318007012807428540025114076030b41c8602e0240c03d8001600306008144501c080c0b01e408140940c1d188203074098054004960320200440442914140002d00ca052080c0b14 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 931979532 1250 931978282 931978297
    0x40e10080613060b0d0c06050c06010501080f1f05060a110f0102030c04120c0b0a0306080c0f01081819050703030206010b0c0a0204021c051609090e0d0806130203010905040b0903 78
    0x81500101e580741c0c8404004003d8000c0f225000348400121341c02042d096100c0306c00504055481e55544c41d0388400b41400c041e0b043c1c106038100704051080c482903171000b007411500403e422000b5100006039840d1000880b0a5620080d04201c0101d80d20052780d0b0401e2945e0000050001a20586000652500d00300d12048905000240c020720040c00242e20000c000002a0310424102c0000f5440703038600c1c0040d40161a668000030707220801482180703070921601420f0001529482001e411080005e04400c1009000040760017010500f0600c83c2420018140b11a018151001c3c11514a00300b45445001d00e00058026100344c00001078480191130896000f4192503002e05000000c0e5130812010b54044041e6100710510300e110855644054071503507000701a0003580c8860603100c04005440001c1c5a8008410286840c034401c0b441c01000c0f800b94995803070351602c208a0740d2944001a440542c00444810042c030120002c07035203e5980e801b19020324010042c20b60240c0d944070007036070782c0c0c456603c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 931980782 1250 931979532 931979551
    0x2031b060f041403070501151d061003180c0314060c030c0a08150405090f0c1005040504153c05030c04051801020703020c0414010501021209060f040e100806 69
    0x10000b0340030411010540e1400c52030401aa0b24008044d02d680c2d003580c40200c3c0d6445c011420b80c10412101d03141d05d50010300c1c0800105541203d1904000113003801c958910410305142c2c0b17031519801c081e240c142e040c0e4201c503444021603a120391a4200f1704241c4c40c5401c0c40b02510311610700403c4210756602c098a21481400401c1413401344075203004ca035004006403240b90180004400b41c600741d52640104d41c42003043d04018100440c400d048249030501c00d008a90281d0781c18942d05407029848000c039410f68805840c0412071380c00d461250070078030075150b01a03840040000c02e400c0610b4011078801d1b021a966220713a1844100a81282440480500c101649903100d41241c1c6401e05250b0407580c0e101050143d4014180c00420070942641d200507822001078020038402d49451400d44103803030500702d214801040641c10500040e540300b5282c1d031301c0d1070301001c0031039401c445135218000c841c52844060340003900d45a65406003003138200199444100480b00b598080703038455001800d94403030071302c0c803 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 931982032 1250 931980782 931980811
    0x120f11010201060324060e01030f02010801141318080a09080106050a06410a0306090e06040314160c26061315060e041b05010c02040b03010f060602031b06 68
    0x18003503003610030411040071400740e1a004001403050844401f54000d40c041c02c3e9a5441b0403452000400070728050b041650b0031b41c5210200041c035201c8402c0c3c00300e501e13814034000440c0e00f0a0038256104400301c44005003800e10000b1010b52655001d0b140720102c0e19848000d100c516161000c02c50a000240100d000140080801d0250000703c190360840c8460301c0311500d5a1010003c00c0c5c4a001550b954060920110008013030000340e030715201e240010708044008101a5000104d40c580340d82e0040d002070204408610044010405001103554403510300721801070a541902d800600b0840912a0384140c80031041c1e8a0342c074440c03600c3c0c449001c0c4800c1000d80340c1a51050b041403031500101e00d003600c00c59601400f200303062015110303c4c0041d20484004d50218941403411440c442142e1815484103502d01208001c2642c002c00c80c0780003994125808a0b10300d0100d40424010100080c1c1c8881d014208800051001c2d004002001502465002030840c2c038849116240c2d96002a50ac840130301c98003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 931983282 1250 931982032 931982063
    0x16230415081204080619090c030b070e060c07030813270e030c0a03030c111605331b031305040c020c0d080a0507050609061603091208060a120f110102010603 69
    0x140300031b402600d082c44000341d4109551141c0040d90200e4108443c142090824080f1164003c609041404000c40701140b8014102d41c4c10794460a452000401c01d640214610090a11000d4001c0261400c4c980d040e100c5d810201c00d0042c00800b5585180c0c00e1882c21100118542d07001c822100b007040d15030000c6c0390002241d58110000d0101803200810448404140394004205000701400030303105035142078a403400c0c071040215150134250145888024010090525401c40105101c65107022008940310807000d202d0702c181c1600001c41411078000000e80c410000129141641910400d640c10040b0000600703081e60780c5c07010010b8569124003010170807000180380b4402000e40791032a251a1f41407905565415103800b90540340014980c00c00f40802008a9001a150305980d40310300c0c0500003140c3d56100c46036155100200c0e10104000309000031380c00d0715580d0391072009010758980d4840119035818140d25100102300102e8111030059205a0250310501965094079001510018000c0c0e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 931984532 1250 931983282 931983301
    0xb041811090a0f021204050c0f0a09020d090c06110615061c020d020c1c02030f0a0f0e060307020c0a090207020a210c0620162304150812040806 63
    0x82c140c0d1409900ca614128400045001030203410080c03041100e03040c10b0074a040382c20031850400c120b00520060b0292602583d03501c10110441d41900001a510b105206800010706580e5601820700f280005002542540c010002c2d58140740c2801550a680c54299034030f0720b0846618415680804140301031025841441c3e41c0c0f44550180e0032005203043c1201010b94107a0b08900e8024071650000402d5191072612600d40c004400228406546011984c1c1e007803990502981c0080030800c031081c01c0c00300d04a4000d00c050040043c000300b2454032403400c2d0000a40c1c5208104400e80181e00c00e01002400784903030300035509100e5000300a04091070130f101d0804500001d0a20441114070525100c44c08102e000d05820050041c40d5550000c600d00141004101015410f50000c503030700c4800403c41c800009114001a607080d0305104041d42907007222000002021243c117580580350235000444514444449011038410314185e03080f55414038034451281c0960310a044681e048280000c80c600e5 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 931985782 1250 931984532 931984549
    0x60f10060e0d020d0c080d08161d150310060c0506040803040819020a0b0618010e0624041508070203070b3301080a0c05040e041a0a0b041811 62
    0x44028090010300340b560f0300014800e101d00c64068803c050768440a001101c01440300e000080d40c1c1d4207040e213090520842d443c040b0045031903542c040011950031030800c0c540e0140705544076540180b610f66000c00b4071040103500d600517118143c00c05040c1c0c90005159001d5a007414905400c003002c0e1600c0e9459841c0d0465650004000700c0b038648080281d15505465481500e43e0f00203141d00900914410346015194044050181403049074460030f040f200c1d031500402181500c010003108065910303170901240004c0000c1800045ca58405c8a491644a000c01c010300b0464041c050101040600d069003070300d142c00c0030303500d200068104102520210b04454801c90304001500d020811445641900d603442e0110121921034121004d06203444640c1c0c01046240c00c40807080003003102e4142c40e0070145c1503124038490358109404a03800181072041e2428200e00c1046c10489082d42450107542c52030040c450300c0301a0b8411840c0840103c1040c542d001040b10643c1d01800101c0a0380c420f03810080d900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 931987032 1250 931985782 931985807
    0x11701090c051306021f06050603070320181f05160f140a0c08010b01172a03010608011a04060302090a03051014010b03060619030b06130305060f1006 66
    0x80200d10703524401541110020401d560103842e0b158170703080c0786c103d041c54913510403a103041c00d0130001d02880d0340b24012a07070003404030308002a0100c0142c1c2c5c009a0040c40d100701c1a603e1074003280b04050014000b01840600b00c013202e41084650703624494944100103490b06d040000c40600103080f00c5002102181006030083c00814848c5025607903a1102014146258900da0059008030003001800300daa5005807541354000c0c4820115400020000c0d20501550b1102000d600089030300d01640c810000207159000c002600c401c1c90b050058a0168001c8c0b00c0c80f00083c2c000c0c0b000103440c04c003960280380c107a6610010245030505c1c2440880c065049042402d500c503544030400400036a0402040150700040580031410015017036103003450400c140c0c010703040800d04008000c1c0c980d030f45408980800c08100f903e02280c41c00c00d5402c40041c16081d14480d0801000140d0300408041000e074007084030722a000301c511590725000b5010b00c601d020354036140c202007025028806039004e202d024100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 931988282 1250 931987032 931987037
    0x915030606120304061d090a0c0f0f020c04020a03110d060312170c07050f10051608010b030f040503160302030324030a021e06071110020303040f0204020d020f030f06030c011701090c 80
    0x2061b03003240010030340441540d40308079050781c2d901c5c14103449030007902e114030000e01c1d81040c0c440f92041e40310107503c0e50382401403544280d0b40099140b00d02c034081e40c0b0203007814003964070702622442c4010b05503000f050b65000a03150112080d841c006614450030500049441c6000d01c0a40f6858200c800500c075040b5030422111809040c4505158034410440c440d00c118a9040100e92401d08405150b000302e0400c0f482401c01c0909801404100780403001c49400007002d26240c00303180d41d103060090a60050020168440480540c000141a8008051030003180800c542c40328400c0c81c0d1a503943d1110701d000d503064264018400703035000b510f05584001840341000ca500c2051054a4001800f1a0301c0000c044442403c07084809007641409603503201d0400c060300007103186040c140c0f2035040031200043e000380b180382c0010301141c0110690301911014445560155205d08001100e06195601151614081c0c440c000d4880003640c40703180c055400c0044010350040d40e908100348040603100ca40718600c00d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 931989532 1250 931988282 931988327
    0x4120303090b100509010b0c060105090703060305100507032a03090305090a0e0f160206040602070f0b0103060906050a0501140d0203070b070803011a0a120e0705091503060612030406 80
    0x420060040e0b03034840c800078403c100c680340c149002c0002164041c1c02036030701417005002c0c00c0c080c030b400001c20a0540b0021140d0b100b41e070340c9845040307000d0452604010304074007ca42450300d1411403608410300602268905000100b888001c05600310705219645400c07a00ca4a94010014025408020201c0c002d2401624160803600400c010400310380c0802c951b0411a4100508010b01c00100c0e41c02c003517602c0b01c1c07103c17002440710000e6603a040504054061030f40003480400304007801056469141d4816500e28042d0303507a04107c40240002d1005a0300c032410034000031340100c500e114450503103401940e100c180305903c0061060303100c1110012030f0507108102e40820620508805004254850343c0410350300d40c10320700c0101460b12440c0342d00e1410325050111091b00d5800040007480c07004407910014010174816401d500d000c8256000d95000114182407005201a080940550442c16401c0700c19984030034082c486908814814001c0c507400c288801d200741403056804100944d2851071410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 931990782 1250 931989532 931989551
    0xa0305041815080714091b0a031401060509040f09031d06090307081c0c0809040c0e28050105120f060a03050118020111030313141006033504120303 65
    0x10b0000c0c1d0700400316030340c055502001222070281c034001100005892042c0c1600b404000b0301c0324441d13006091400d045000c00c201c12905e102e907205801b1075454010340440c65a6504010f0036507030150707411602903800c03c0a12440c0e54070300e001e084d200c943d00d5a40e07200000d5003540c10b500c0007615895030940c045010898680326550030030003030740640052000340010030300e0701c03c000d140d0500510120b41440f071490380e030101103150740c2c00761000c1c40410b44000c1203540c40a8030880e00c012907045107a90140e6181420120720f040c000010446c040140411800707030741c80d00e00540d0180038403248550310550703480018403911810312219404c0100504441c3d0780a07160354845083d00c0d8050886d148804821002ca410344d03902c01e0a917610403001001962440c20101c08480b506542c2c528007624a43c3d940c840da80d80501c00b00040d00410094282c00c0041907107900c1c0640107a8001e140784000b01d641007400c01d2140010040010303401c4159220185018940a160b0031101d4240ca000d8050594825802 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 931992032 1250 931990782 931990811
    0xf1205090102090f0a0806060d2907022404062406080f01060c0803180c311515020c04020301090b0301060902090303040e06030c031213080a03050418 66
    0x490040d0059000542c503070003100140454440c0d032801452090b010710004000340000400d856030021000e880203428410982450b00248aa101420781c510304001598561460303c5110103016200030750a03514401c01c6262000c50b044d14502d03503400d08010a0307011038002400c5900245010320f440d81907441143d11003900d41c0740c000d5154002004201c5610411906400d03050070540502001e0402000c20b00968664041c0d41c04001c1c41ca11000380c5040107400c3d807010400443e440d254000742024510026201d0610308105816002e40d4100410f4200c0440c1801d180103907081c00d91109000010185030062460102d005075600070258082c83e044803400341c5803800118080c0017540d0000c1131210643c0181401c60f0456842081514410f0100000c140e6020081740e08035640c03014202c43c42e44803800020304040007031181503810710070455410100106d11700600318242c0d042980140c0b040c0e0301c20302c0c0c64441351b00780002800544204018490b5103401d290750500c4c40701c1c21b00c00081551010070745 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 931993282 1250 931992032 931992041
    0xe1305030a050a1205130b0406060315150801140613020d020a090806071d2b050601030c27050901021902281a04021c0c030b090313060f12 61
    0x8441c0028000650080d01c150000d110b1072402044410030443c502e0700d541d5020b0108501100100341c004e40c1400300b41400101e8105074007540d002a880d1a140c140b100c188030051620150030f810307002c0700980004400006114003059810101c150f200729030388001c1005420704840503944541982806598240c140d00c1c4050144000b182d190801d80c107086c01802483e00400810107030410420050b10740e0500140404042c1003003040d94155a90000c40c05940000c51815035005207410408020300c09124001401d0b604890240f4226442030303403a1442d203115201d41c0d2101207542251700803000c0c41201d840c1d0156622654200005003402950601c44040041d0441401b00507408032220ba8900b4002c44001c05041d5100e8035032281c0400d490340c92580202a9403445280c1141c40b01c0010b0035174032001204910f00300311003003072910b03010340d8035041c10094903a00080e90a2410000001c580c1400002224005d0b540e002c4405103091030490110f559101c0c245103c4c1c01c10145000c11510b14109029 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 931994532 1250 931993282 931993297
    0xc092803150f1a060f09150304020f030d050a08040633210602030a090212060403120504050c04110c0f030421120e0105070803070c0201030f0203060a0e130503 70
    0x7a0703100d80150080109075940a000a58210703e45012180c01c2d00c0504a8050b42c1c0805441c01d946844d042100300b17240b400351b02c16442c0c012240e00f0b091081c0c444035600841c03080c6d200702d5240440201032001d1651310311036004100081f800411100400034001c0200c141e005209d000003150084030388445100800c10704501d409110000c0c0041441094400c5041018000c096110746511800c0101c4941122244001030000d55000004c00d107044502d0300715030310f00c5801604420055006000c441c3d9151801c42c0c040d000a8030420703400c410005c0f41d00403140103580010044c007885201200304002051440651003000300108040c031b400c5031051151030000780740740e0091526030b0f02d80307004030120100481d103214020f0402e455100c0000d4800001080d20301d480c2c41d000d00715650f2300005031031a224401020b8181c00780402001030455101494406140c802ea9040c000b811224204000b640001d91f0910340c0660101410700c0003500c50030841c1c0c4c0c030100b140c41000340d509160300c40d10300356030107500b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 931995782 1250 931994532 931994543
    0x5130803060d21080609090706050c100903021b06030126070302041a0f240a0306080304030b0405150405070603020c0a020a060e09010f080c2808030d060803030c092803 74
    0x806103c40c0d035001130489a10079000d460304400c0b4038101007181d880e400103019640c103020000c00e88103216901040110f03a80d40e03502c1420080040e0302d05020390b84c2c030600051581c0d0207800b80300c015a5800c100d0140e038101c401c41c03040082d1a22619003903103804521000c80c0c07000c41c401c468001014ae601c41c00342003810500b2040e2075148100c0c80b0140302e104c0c046d1004141c05030078000c207106102c04440300440342d20800c5020003030b10f49206440481c0034045a41c454001c501c8046404801d1004645a03203009500c44d6040351044080030114118294007103501403c0740d04445020803040380290010040044c000c0d0680f81e640445030b0001d482ca04180d04038100040240b029554a4103048002e40d001d86604d020840c0e1041c0783ca05401d03a05c0500d501e43c00e01400251b40303801401c200c00507965080c0c905541c0d04900d410b480d1411960741740c010700b44440a0505003400000c600c0000310072240075050544d40c40d8a806e01207010702c400b0001c6030618503900402c1c65901c24120200743ca050018501c0344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 931997032 1250 931995782 931995833
    0x501030b040e011e1a0915030a0b04030201020a120c14030a1509060503061b07110d05150609100311040c05090d0602030106030c0e090601140d02120a060905130803060d 74
    0xa490810480e1004044105d240c01840060309860b82c80b080815030141c910110882c00409803c0402d0a1086464009042000c0c90081c04201034040d009010211011b90300d0181a50542090b82c05403650601e85001156600e40441032010400c801903030300411202c0301203178107201501c509445a15644c010040b4996810080c052864180040380d008004402d100706803404203204564107104061000b08a8281c00f05c4080e42c546540d02e0320001075403c1310684d20301210500502c0080801250036600c1150a0030000e48011407441c112000d403038001003524901000082444020103048060b42c3c1880001d009502c50765071416000c1540c107214001c00350f00c0e5490b010020301610389003c10354092100c400310360b130301c40d450f08a0034607400ba00c24a00003591004181e0761410307034812240303085581c500004d455408050102c004900034410071004025013a51220600101e4200f92038800c003425000e403500001c00e40d030300051500940010880c846981880c0c1d680d5500c8030104a8540203041c20 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 931998282 1250 931997032 931997081
    0xb040b09090702070f0b030411040c020604060b10052a030408030c0d090e07030207111207060e0904050613111e0906030105010b09120f0d0908060a060b03010501030b040e01 76
    0x1004464000b40d190005014540c03c2110109032110349001d602c8100340048005400e020900415917071024010384108a102ca1254009454601c21241a03c2d102c0c103019a044040c10001c003040c100d0480e5590702c41c14980140e040e00c445201e030300204810490711244040e11420103000910041c007080005503600c0d491000c1090404940c148064203002c140f00b01000310102c00038145901110900c0c0041c0d5400742458000044145000d170319400c0701c049100b0500460000945409aa045403201406000381c68204403035010300311001412034110002152b0610301c9410b003503003058030590b5850103460008020581210301500443c80210740494900c40b5820003000076900301070203400a00c02076040112001080c030600c02c4050040c441e00d151144024000e0001042c040409803d49040312100d0900408800c000d008140c92401514041a820b6156100719400c031802c07000030314110ba192000560051110403101c0d070300b00b915402568481b420078460440e000c12884034181d491040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 931999532 1250 931998282 931998289
    0x3090303040c09060303120b01030f0e030301260714010207032f030d0215061903080a0206180c060a03060914040309060c02030c0f0402090915030d1b1203060b040b09 73
    0x10b15886030703001d03900d00201400407036401500b00c2d5849500603004251000f900e40101c00400425020319000740c03a00c079034051181d00210046040701c0c4000b280d208a0f118043e42c086080002084229480d40315110420950701040c001c41348000050045c0c603e030580d02e031540c1d0090b0074404600341a08800385030920388a0451070030100c20400a400500403482d0380c1001a54130901003c01c0c110b0001c0110006001d17544042e030700c03003030040712a940d65201d03952031421390b20a0304200d9030b8402500502000a2910071480301900a09803104020706a81c101c030010310031245c1c001043d62080603221880820490f09074010620940c090039003864840c03900c0c1c14002c0054a65401402c10809a01c0f80740c00503903400109000c41d58400c60b0307510308002125000500a00c601c03181540c00a102d030041042c5140e040300060400c2c81d054041c2d0b20700b116040c0b03040718200c000313540140b0300c2c0e4414000d10010030360174403909880344800d0800084681c0c4071204aa4070740c0055224003a0b04000280860703540c03c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 932000782 1250 931999532 931999553
    0x809060d0c0f411315050f1c0617011a01180603020d0f050115180b0a1d0a0e100b09060304030302070c030c1517060f060a020c04110403062a050a140309030304 70
    0x940c90aa420082c0541f402c800754480e21b00c0c56035242c24001441039080119502c2a0024412808208481a41c0150840c0030300070601c40c100704240440d940803001d5010701003054010510b0681004100d04103c802c0e0000d402c505c008100f2960b6598110000c0426071045230302078015043c0c40e001c3c0d5003090030f006041010480c5407080031007003090204540e1419600382c0f0610740c018180220320a15280c2ca18035401f0072441d0469015110901c0000c843e0541e6107118003d400006075011200d4441303192014601c500090307640c200c0000c00000300840e201e9400303440e0142c03241e5a40303541e01e0f1b80e0f52541d10000d182a00b0007801580080528103101d900f0201056090850b050700c000280b421500245101d42051b400364001d100000324480042c0c42404154800d89c40140200440134a0035490080b40c0c00c04d010440303c01d403411100310b01005841911040e044036041c1a6012070700c04000c02c85294101c4001039091000b401200940906100050340c0f06400d00c038011612840c2c54106100400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 932002032 1250 932000782 932000819
    0xa090e06160f111219090b040806040f0f050f0f0f010b18061302030703020d060b1218121603020d08041e0809060d0c0f4113 55
    0x781c00d921188081c0c02e80101e40988400b00301d0800940418000150605041444407008501c0400051003400960a03401c2c100d41d02d0229659550349540342c0314013640130301c02c5001d0b050a550118000070001101da800051034588074880008000400341c1d00c1c2882c09803110300170f0720140c00002e80c00101e10030400c8002007540c5407000900407911a5004165544880d4030044011101000000c00c5900c803c00d0741c061507103500404540e41d241041c1c000b0000c0d002010102d82c3d207414042c00140d440c1c070035001e940645140820311110f03900c5181d11145511303024800e42d50b0501480f50b290103c8550640501080c0307140040280c0c06800c9441e0007400c2041c0304c0d000400b03004204083c040440c440e00340c40503a055004080c040e80001c1428013a45501072000031507032241000800c60104030842d00308400303007026516a1a080589004290354148203003200d42d5124120f4865400c072141c40038100e81d120a10070340c28180f800b41042509801707500907190801c120341c01c80b204020b03c8011180c40300386c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 932003282 1250 932002032 932002051
    0x40f0b01082206090503070209070c170a17090f011e14010b07061e09080702011106070c17090607030801080607021506122517010902010f050703020a020a090e06 71
    0x2581080c0b40401c82040c4180d80180425a480304100c0030000100100c80142d07400403d007540520b8801c000508035581c003442201c401074950b2024041c904031109070340010035075448400b46612a81c20f65140030307100502514441c426007600032240042881402c100548182180b051410701e150803009803020088441215a2443c0c010003040000d1410b80301034660107940401c1c1075402e510090b0b904014459a89101440e1400000400c03203010010607916100303807520700d80306100b9100c1d01d4550004891482c0170609070300035100007416182e048509052400d602c541045046c0703002c1036480d00000b07811808504008d006002d82c5004010312644071065100030700080c601d0035250440001d010b0f0950b4001c00040b0724800e1041c0007804a14210326004405003030913190300030181e4001025120f80344001c88005c080c5810f1001c10f000e0048071940684541e1012030103554101c035213521105050b01103000f069a1007005a0b1032211340c2004000324100400d43c0440e04071a0b5003041c10140c8800c00 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 932004532 1250 932003282 932003311
    0xd02181509063403020f01050103110f01020708030f1e090d030c0609120f030c08010807150918090b161e030603050102120a0c0216091a040f0b0108 65
    0x3451003804111240c0e60300a48840c0d0302d40c1c0c6807040d6040c0c41d10400140c446a61901d05840c0c108440d541c0e55070512501903400c84d8111010194080e003220004c0c00040d10041c0c07900c0008100b4100f0740000382480310103204075015160780300800ba056820508441d1406540040c003e2002070b0840130040e60704241e6502503203401da07444001107408424080090910001c004003030148100c5902080c500c82c0c12828089071031a015000804250080d80a03202207842d0a06251a1911940d001e9040e00c0030300380103014240c24015000c4614420200140c1005818140032420b203d49a55811400c40300c00404100180ba6240031640b1890042408a648549080814505a014520154a00302c00c445850304c84440e1004038040d080c944c101030134641c00000d802c244100050560341c802c0007000c40400407070615602c101d071a541000e600380c8480b990410140001d41d00e6034001d5560b020400040e5040b50103c4002c1010f6072903900d011464182d84081c2c102c0303d5604602000c0c0d008611205810 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 932005782 1250 932004532 932004559
    0x10605240301050f04110d060f1e09092a0509010b0a020c01120e03120a050106022b1707020303070e091e09010f020f032a070b060310020d0218 63
    0x81590105100c1c0c07900c512610030300901a80c03650360005410705442144036070341d5401f400907100580361505c03a07000003003444400080e038001482e14030a202c0c2e100400c050350840c9490b09010180002c202c0645a6104c2c100e0b02c044d2500569a4060442080403d0407000902d070800700300301c80303405038000340c483e5001b0040d040d0300342e50104da070510703540342401c02030f40c480c03080310f00c0c5802844900c0d445041d83c40300007100741d0040514920340c0c3c4519007500c02071145a172944000c9880300420b0000540c08038a070180003c41c40c040528000610810389071407000700d40403024450070f040d0182e4500c0090781001050004544e401030261804c00c405a4240449040401d400700003101c1704c12056001405640c085510b04c803003034100380800f800310307117055440e51004034007200c10741d0082d5181d60410200602090380b84102001d411594101c007882c0c076040986c541c4444180c054010001a410f02503811801c40c4000d031071011f0000070f09500c40040e200c0380305850700131100c0e000c901404e20603c0710080b0f80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 932007032 1250 932005782 932005849
    0x103021c1a0a2a080105150d020a211b050715060801140a060f050f0607050f0c040b180a0e1906020d0605010519050a021e010605 57
    0x103850302086818044140c0d115810010799801080140c40c191048000610101c2c2200381c2003032009000b09598102e4103a0103d0151211020011504000c1104800104403503e030a180268100c0c984440c01403401c0c41d00c100c06012640600c0c0c0400c0400c1710b40c00460548464486240650103815404004003ca1241c1a041c0302561018210400c00001195010003103407039074150b4421034450f01030011380d03180c1ca50316020708000c4002c52805a8600009902d611181c0150f00465039070b4102c0e4900c0c2400e00080c40751840083d8410b03900003000700100c4c000900104515132000010901912891200344c081000355459004801d1040d4038076545001c0d00e502c904451038102c00764060002c1d15040d61008a81440c4068001c5075080f01c100c09178a00303000050700140244101484100107140d152401036420f400350000113180006100c1c400706035107001d0001059031042c1030040f19050341c0502c80c4a01244424480085943d441e40d404211604020b0154900a600032218800c6180c051903803 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 932008282 1250 932007032 932007049
    0xe0607020c0f0a03020d05060f330105122a0c060a090f0b16030c080c1231061109031b0f0d060c02070503030c070902130e010f030501050601020105010302 68
    0x5040c46070b0a20302d00040c1e10340d5001c000c00011907010f000282d8804490610170784850084420500202c10324000070b841c0b00000d00809105403584c54100c4407000c409000a100010b0442d040d03040c80400c00401504802ca030702d120f0b20a07151000c0c8046461400d1030b031100a040200c100b0078856005202400c029440030400950052245a0000303d210709802c0540004600141c0608005800e4050142000c104100d005140381103440a1040041400c402c60f221001280c2900c3c07201d0040c042641e07000d6801031072542011f201800c2a07a08080102c0b581c8580c0c102c5800082284055240c080410000740107110100c07101071a000c0c00c01d0741480c003182d01c0e108480c0c1c06000a81d8031a03482034a640d134a540d4030360b8031500641464000600c80c90983d0003003183e02c0401004d803154400005035440c000044907107070b14074100a00902890400814065080b044070034001440058000c940c00c14080c40c114020800010102041841c3d800d0a9084520142080d41164180001800941c482211 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 932009532 1250 932008282 932008303
    0xc010906150f03150f05010602060f090c0607060914060108010207021c2307090c0906110601030210050a03060510052a1903110109140d03061805070207170607030e060702 75
    0x26041c3c07011202c20320004103000f110305000c886c0342c0000800c82d26400110503106940140b0180d04503103448020507a070b09189243d059008908001103400503a55400280c441403246500e0a041001013600b40d044c00e100740c01084c0d80381c2d408541e00c000d41c600001001104505003c01880e80f480c0d94032130070900c05a02c0e012084c2820940440d1048440c1040040c0040040c40010840c1d0002c01078014031514183c4030300800100003508012090074040740311030480e80d00401c40b0700c000c010620190780c29040b9900c80014580c0c0e4101c00501611444020007210f0250390b500d40d07503400003045590140079101b00074030b000c2c449482070017810a400117820710f0b812210110401003803058130f011140708100c0744000401e9400c00d260325040001ca007011000e40b00400b415500d08004000e0202c044640511408140303481009100c5429100c40c0e000c9030304000c40d4410f440d800307030300c031501366000d81c0003030340010b0342d5034070540812a0b000c1c1c1c184100088007148202030700060525460084d0b03181000d04 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 932010782 1250 932009532 932009543
    0x9110d09020310380d0308071b0506040b13030905010302030a1806060305070b1201052b0b0f0a1a010f0e0307080c0f0108040309030f080d020c010906150f03 69
    0x382110075981d0401841d11950540c0209102e640c4d040225910f01d0442440c0003c000c0080d4500b0418120902103000700f8880060711038440c0c043d41c5e403002c5661130806003203a800d008040c0001d4a40309903da4910b480c950003070009040c641880c4c60980c80301700006000c0420f460007484000002580702000104640c42484c002d6100d464144040b0000d102c42c0d001484d0030081e00c040ca000f0040300e03410500031039007c0c1c000d0302c040d00c1d034a00342609603218010100c070303080c2300b4a0300510403071400c020043c0d2022202c0081d040348140702c40b059021080c80040c10344d0542000300800400581c00651994044542e100600c00c0446040905403070301c6049680605014a24084c04001351042111040b03462008080b14841e07681c8004140d181d0001380f03030780c501032100680001281d50141c641d2900172a455903508030786a1071500c4c0c104040c4015541100d0540e000c000140d40c00b52903001130909900340703e0000079000050310781102118500030380c4045009502c00c0070030090811074590310440f41c000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 932012032 1250 932010782 932010791
    0x140703031407110409120908120d09110603041505160c140a0501150303080109020f03040f03020330091b12010e100915050906070e010e220609110d 65
    0x345094030a0000c65401a508949000b1840c4248000101400d06c424a142c03525490103444000340b940381e062003420801801010070500b60050170395881036103a50300881007444060380540000d4155801a1415950100351401001100c402c62150356009032500d045004101b6000e44094019418601d02401070071060210400c00f4006029111450744d110000700040c5508440e03c03111090980015400116030a0001c039444a07244215030001480e06000d40c15955295541c0c40c640600a800300c045000a00c4459600700020380f030900342d0300000e0b01c80149041d5000c01e24202420041410b0b440380e01204100d001d41d07003180d50b2400042025103110601019213044540135002c4081ca4805a11650715240d042401aa114540341071180307100b10340406620601c00c007642ca081e1182390981d000840413400c20750081c4c3d810070301c0500c18100781410041d600c00180600b014404040b1240c0220b200221204000d84143c50107400b0007002000041c2d071020020916008116002c54490780c2d4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 932013282 1250 932012032 932012047
    0xc030a032303160305041113020309010f0e28060e060601080f1302040509150109020409181106030414030309010e161a030603011506020a020f0a12170415020a1407030314 75
    0x1c030142402d100c0c0048c0141071303441c4400c4101002940100d41200f101c2d440e101c4031800d009040c1c0900242c403502403000304000c6007481d601c0200b200550260300d40c04c07098521a440010703510300540019035040c40140c42c1074038100d0005442c0341002441111b44440302401c0101d00c6a814211404042d01510000f56039500c0c0340700546090502c0c1c050707400d005000000000c01100700c0c0c0047c415607403258001d00c040481191038480340300081c000101410807902700d0100070b00703224000c0e56011703008213038120b24250030001a9096a2041d40e00700303840d9465205c4c100c0c529004115442001e008909003001b038501e440c0c0050710660f849071520a084500001150841d602504880641c03c050240c02d0700c4039a407000060359410008404900030340e00381540c2c0103185003205a0700c003182e003408840c4401585035990201c1c603140c600c0c40c20300c44200501010501d6080c402141024000070b0300100035814041c00c0c144900030042c0342c040c40950118000380700013544200380d400450301195234251150f61 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 932014388 1106 932013282 932013293
    0x60c100912050901120203060312120709060e240909010e090f03041d07030e0601060903021203092d0301090305070b090f0c0f01020c030a03230316030504 68
    0x80101394171504d500ca8000b164010002070541701034649a10b40340d80e0640045031032003102802c820801552a4002e55200c01a100d5410084500450f980014200e40016a00c2c0c0c0c84020003c1094002e0000b510250746400360f00400c914103643e11240a85820881264104924800c0c50049a480080881100e06880e550f200ca140303000001c14254000d460040d1a0b9400c00d50ba1714105c0700c0114003405a24082c00032030381c1d041c040c103240d030042081d81c0d00c01e601d1000750794004000790b21032a603030192402c140501c03042640001c2c40c440c5504051088400031519090f5007802c0c5203404240c0c0c088002c0500b00c2c441c0114048946445c02c40d43d59640401c46107281c540d1041045180505e4046802c035000c600520441d0750240da0f410100e401d0828034203084000c0303640f0241850508000d203810070302510100444609614040742e11000000e840700121040c556110013040038000d = true := by decide +kernel

theorem cover : BRFrame.Cov 931834532 932014388 := by
  have h0 := BRFrame.cov_init 931834532
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 931834532 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 931834532 ≤ n) (h2 : n < 932014388) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
