-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3354
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:25:16.730491+00:00
-- url     : https://prove2.me/submissions/d43a0c0b-7816-4550-a7c1-f3b31bfd6a19

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 603057553 ≤ n < 603237410 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 603058803 1250 603057553 603057557
    0x50c1c030504090e030f12090606100e0409020d170307080f01060c081605010606021f02210a0f021603021006080c011116121a0f180a170d0b01020307020907 69
    0x44130100d07444091440c000c3d07000312815890005080344076207160303031169400340040b003045485a07100c1200304401007020302c003003800080e07070781c84124038920700b0b60030188075240040e102c5040724059454040c3d1604208040300000c034000028009225440410198441c103a44101e0001d07504111008104c00c100d024060300f82d01c1d0110303000a070101106100180180d0040c002c001e00303540c50101a45aa2029410003580c0705109500042c5000724001c40d01d28118a000b0303070002c000c03048003240400b10702a04103984550f443e211090458204e1005095410084c5000d002050151400a24220010300200402030500d6810000e0348030000d072040b085032003401d014000300c6a8500c0245482d1481403050810140070900003114200d01c0303114103459010f2812605100b40015540003060000e4488900003501d04002404550b0720742d40c60b0442c0341d0203100f42c440245240d100c80c10b44114546030030000b0400050134a000740610700c1040b01b82c090038000380d8100310507600098143c0c1c20051160382 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 603060053 1250 603058803 603058811
    0x40c0e100804020d500736140f0603010b0906040e01020c070b030105040501061821060524030c0105030406020c0c0d1203050109020c0a11010516050c1c03050409 71
    0x18075804100c2c0101503d510039842d000039401c00c0a42400e80e240d044603030654103084044400803402d00480d245c0e00303844c0c042c070401584502c2884c1d20072070061a14109882d0300c2450a00683d44101f82c06000480807143c44504050f00b800c2c245d0034802680a48424480c2c0e1403d00700d51200d03160008065800001100c0001303441614aa1050191280d05208070725802814000b0a014040300c0c080c5042c0c032010f903810807103aa01d81030182c501407210074007050001e0207000200040c025400d8039010640c2150341e03600c0b840005a0b00c00003580c0c030542c1e01002250202e2150444160224203060390b8501c00c800410900142ea400603006200c003034405071503580c00049042407590b040100c4002804040d007030403542512030410740700c1d11401074014400281007000000341c0d24554001d6401c4403281c800585122240f584e500c0c0382038040c14400c581440800c0c4820031400d02a09074802016000f04080d000b0708035800204040480c0259402e800c5003080341043c0003103036228065409a50300890002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 603061303 1250 603060053 603060083
    0x1030c0302210103060518062a0d020711040204060509041107020d0311060a0b09010b0706110c030a090e0c070f050a050604030309060c02061605090f040c0e100804020d 74
    0x4019110310001d020700102d69031080101203840d0300010781202d000704003c100c1d0b40c440100c200c0c4415601c0e0070304c2c03103030358020302c04615200c444980d14007401d25600c0446005201c070840c00c0c40340d50001401114419401700d401818004141e8507840360604c01c4074110b10302410200050314500415800340d02580c1c1c0d5002081b44100741d0b0080f41d03406074001f842d40340b1040f450b05c0c006140076161010301181e40580701c04034501f44010b00554110000081140d20260709100e030381c141580000005882d0b05844669035003291040c84001e002d600c036088080c0d6074401e038030321001c2c0c01120f00703178001c20185900c41c0c00c1280ea4181c05055640b00365003c1c0c1d901403078180e58103055150480900ac0941203010300c0e4240b0003099010750010340c002d4800e24040c804c410f02c19206070389a890440d00082c180c508017848000072441a0300404035203500400340c908028084c0c0c041003c49000c0e800540c04500ca013080c240c00e502d00101c10380809480c0d46010111468207601083d000e00704a00c00030511000a1009 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 603062553 1250 603061303 603061307
    0x60f06140417060711070b0711040902041d0d140304020424060e040516020d0e0102150c13080f1c030603200f0312220b04080309030c1c0201030c 64
    0x1ca005040860141041018000515403100740944403000840c03115100350b0f5281c0000f0030500121101e0b03520a82c10110300392900464942004004c544c020380d00c8c0202401650751b48115244000100c6c10001598402c40003585030001e050750520502c03403002094070000d480d00040740d41c0a03a05031404503400d500d03500d0800102e140307030485e100d070101c0d01503010a9013648419000d0006034211010711060300da001d1003d64040e00b810701c4000580201c4107040b4040c2c01001c40c9500280188103c0d2108820010a010400c50030782c0d054407489000544214041c03000c0240001802035440641490204071343e10f80d5440f003e5101c04e2801d180e00400da1ba400b0b03402035001600442e0841080000a6500c1d00300c046040c00c0844654820a24500c440e0400c1c10001131031001008400021494186000702032003203540904000c01e076501507443d000c00c2001c4545c0140004003091001182c44000307a4040500b003101e030040d45801100ca01e90134240e8803016818a5040f0740e028200010349094540d01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 603063803 1250 603062553 603062557
    0x10507021f0203040f091b030b1c1b090b0a0f0501020a14030904050c0c010e01051005120106080111030403020d08040b15010e03010c02070e0a020c1e010212040b010810060f0614 78
    0x1c0031403005d00c10002019125608170326031011455500e2109200850000d0341143c1c1000e08003034101c01ca242c184090100b4024496139030382d002e40941c1411450307050400803203959035007214550355211040401c3e1420701c04c200d000034004010b82c9100041c209030000b980d80813030440141c800c1c10030260f00030b0038060900460303901e1280039000b88028542a26103244603881881c0360041341d86404d0101c0607047c01842181c1c000c00030341d019040f8841c07600041042624041e101801c070755690383c900055402e004d101d40d83e140a000c44450fa00c17403915050203410301010381014018041c2e00c03010840081c4034500d103154011040d14001a440d0b100000403251044c01c1001150558a0400083c0d082c40d000180081210b01d40c649040083e82c403104080180d00031a4515440c81c1e002e500300b6060044003e43d00b03a00800c0440005007006003800249141e41020340e0241ea1484c0b1a00041c44001c005000d241c1143e01c1401c0c003403014130300d486140c4000d0402c600c92101007041d600c4810000c1050201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 603065053 1250 603063803 603063809
    0x807030e0109030504031406060f10020f03070c1503050f04030f0e09010801020408010608070b07020f150d0912080f0403080601020f06240a0806010b0a0c0f20010507021f020304 78
    0x30085140c2c0ca241c00380c02c80d449130009481d200b5402104980c1954000b8085129060240c2601701c00b500101c184008000190038103020750040001562031400200080e00d880c40c00380300c404108520f06001004e0312041180c1503410142000304004151007103101c80e90700207526207400d100c500c21080e004c45c3d04454804031903500c000da4500000c0c1c5800e054000d44107440b40100204001991500c00c243e4441c1944650141c0360402c1c050780c00035291840410300748803006046c42000119822584440c3c2e1310502080907402d40e03480d8980c2c14861003070081c081d0f07244c940c01c000e540c80c00c0c911182e03400a00300070b10003010060b1120000d8110f074402d104004550711090304031509810b1034080510052407210700412003044081841c9500c3c6031400444046070703801406024a6404c0154906540e0300201500e000d0120204184001601003141c40d40541d0146c114848001d40303c03201001030380a141281410803c052002202581e9031720748503002c181340b00824801c075075040007040c1c2c00d6000e0743d4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 603066303 1250 603065053 603065081
    0x90603070f08010609030b0103061d06040c0e0604090317060f0618040b06070f1401020f0a0201140a06050a170f01180c05030d05090d0303090b09010f06080319080703 73
    0x220500c81440e420184002440760580ca5105141c1c0c0c03280740c00c48042d12184000707080189014010402700b41c1c554002da81d00301160b0000c440c0d8980c004030151405c1400d81d001c480d0010103e0007003200c40480c144040c2c200c01d003100c040c000c492807a01d00030120220120709001e600c0040780459040e644485500001003400790019483c0c85120300390503114140421424092400e0104103280c44c03501e03400f02d0b61207030350149909d8240c01c1e0035201c072017054030b1000d0101e05c159400c0000713440060072600502856906035002003006620500204410704020748803641190420b0000e00003655009004c105407000300510300d40b1045401841880c02c04c00c05041012540790110302103540d07082e00e149a21940c0a049080700007a0b07201e040c141e0310024002214001402402201020300d4044540034406000f403801182d0301940e5101d0301507060003514280300c0761399a8030083e03518243c18002c1d68010506400030b5810102c010600c0b13096000104104070400c404031001441650180d84091aa10020 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 603067553 1250 603066303 603066307
    0x1305030d030e2803110f03040e190b1e0604050603040506040c08060402010f0c02060d1a01030f09081801050403050304120b09010c3e06061503070801060e060906 71
    0x1450240080503040b042102c80e015039045259400c240003440c3c83d03c4240140000407009058508031483e1906190140c5280207103000c0202403c4108050700242003100000310507810541410541c00320b01c0c08032060624188901c07400c80345c0e1003107402c08a5a45488030414000140d0f40096142c0c070480e08003a40c4035001201303000501ca4000b4195114920402c0c1920203142c03500c1002d69900011140240010165280d500c106403181c440440303080d20181007581045c14881801094514004d005180c154100c0c5110345650391500508107140700d8100f007044007030030302d85405006102d9800e140d10f409007104054400307648070306c007160000c6402506407902c0d15142d5054001754032020a09903107440c62000413490006041c030540705401c0182c0c4525006000c1402c943c014150f00d14091003d0f44200c201c002604440800200c42100145014101514090042005061035640803c00d505010306c02c010f40a60441612415204141407031a003461030000000c3d200d10800c0460354001c000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 603068803 1250 603067553 603067573
    0xc270504023304090c020f0304032607020303190f0512180327130605030606040b0127031209030519020d120e01090e060a03080f1e190320130503 64
    0x1d6a00c030098a403025401d482942c00c820401d48d03900d0186020141c441e0100d440c0c00a90f000d008008180506441d03408941000340c60340020f8150340100380d000d42c00d158a98207204e94103500000d04000d00c080c6092060500c02106082c0c0c0c0d90f010014100c40a00100a41c0da2403a08030420a81d802d043d8541203051592141c040b0f07011903414141d0220740030b1044071440050300441c2d0301a0400360743c0c014006101a950300307000c02c0301901890319140e05200d840a030b10741307902c0484201102241012480204101d00c0c0d4034013490880c1981000030100b003007500e41400000c2021900b40b1403080310303201440891550740002200c1c14007055000301000510b2202d00b01c41900a4041c40094500762103241d5102d44c0e43c540d001213404126030060340320351011420320024503031601804604020346100c508044041400001c0e03141e100084040b400030115128030541442a40708075a00c403a8a8140b05660081c03407a802003440cc514403510b02403000c603100c032401c0c0d11500c1c0d00001340001000c5480c0c0c051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 603070053 1250 603068803 603068819
    0x9020315010314011104030201050d090f0b0903040f05030a0201020601030b071107030b06130e03030a0c030b030114010806180d0c02220b010f080c030705160c270504023304 76
    0x2d40c2c0f6450b5980d401e064084844049a0080c3d408680d011307107402e40f0309560f010403079006003054541240c007074000d125110041840031006a201e180610b0056940301d051413000c2e20710b0400c80e480380303200b640415a82001070360b0100e040e6045036400070400c186030310303030311401e5a4040b212020603240d80300b030f000d00009202d20220224004c50080d602d24510034104814030059403a2810315810f05d62040000c64000a80c0f507105520b846041c1c500011304201a000103401d60301d4000c2c001d04901c0c0400700500807103805110094004800d040408001c034289081c7e5a2200242168102881110b210725025034075a9500040c54100342211000024650800c00c402420650042030001c3d1421503841d00d00707405030344403c1c05490904040f9086650320007044440d030b0300c003104652502d80b2500c100310000700c2446c0c640300504140c2000c0d000b01c2044113680b0a400c01d81d01005003034241801e06100140e140c0030008161201d160392240c544881c1442c008140f400d40044042181400040008000b0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 603071303 1250 603070053 603070073
    0xc090618040f05010911150c070b0d0608030c1014040510020304080c0a0f030906030227040e0609010b01030b101e05130803070c0f060f03020a021c05030f0117030706090203150103 79
    0xf0b800c4400360300c200d1503504d0407d2140552014004c1a030700c8a442800070304641d00c05000c00301c80e41d0728085142034440d003800c0d055400410310142c0c641d200c0403003007040c1d070180c0c081c0f0f04510260307503e004178038a82900e44c10b0b500c42220000d046940e90007c00b180610411004032681d04035000c04451144106207402d0800040700c01c0142c00007102c8030804030701184070f4000c4501d841e00c4d041c4024200b6940300c03809518200c1c45100c007640aa030ba070010f0803e4210034801980b16000c40c00002540b044104000350655081c9030b5010b20400c483c10004a10941100740301c54070750002c07107043c0e004181202e41a292440f64406050001a20960000d50014008005d080d440c1c031a441c2d0a420300e0351140304280382e00d030301d01400c07012481400c2d5030f10040d0f01ca036016001c12255841110f410345110401498148884c400084c0003605c00400c0012030380c1c2100c8030030300502c031180e805030b0703030000724910181c9034041d0000c01082c07540c440c1312070002d43d5001c01c20501e2110000300d0300019540c1da880c00c3d600e50307 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 603072553 1250 603071303 603071333
    0x110a020a030c060f02040b0c07060f0c022718012f03070309050118030201110307080606030903042310080403050f090607020622061b12110d050c0c090618040f050109 73
    0xa8820500040ac08920400d40114078554176192030303640d851a9801c111080c84141c500554081c00c107918500100318007511180a840c542403294803984041d1f943e10b017502c20419150841c3c1035803030b140b0b01180100c542c00d8500b9000c00043c041c0c481e00e51750300850141c4041040130b030140d820410b48440c0102032142c00201c070340c4682c00030080c1c080c8a840c00e944c81e0008895800204219100180c0d01c0e0505000440e40714008006482c41c0549a044404040c030303072028003103941e2190307524a400350700340b1060340e40200541d4100405d47c0d19065078000c09038030801c3e1850b1000e00001c00c81a40a486610a8034100c90b0700a101c80e07240c943c10b000d0509018001d00318140d03c91074070507002400d14018078071070f0440014561840d180000f00d888015083d2131400002d410001030107001a076100d01400a200d060005a60b03075a5511140380314607180c80c0001410b030744100303004e50611000d9912104400144240c40c0070403403403a902da06007100d60f0841080040c015500f044860010402144001d03180 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 603073803 1250 603072553 603072577
    0x302060105040b0405010f120f050703030804020112090c05130906020c010f051b0f2a0a0b010f0e011208130303050c0618030901270303080a110a020a030c060f02040b 73
    0x390b03d554508000a442c0d00b8440c0741d070300e407080d00f809100e1003400d03405000c40c441c000c40200750100102c0d0f841e0751400b21507a009400188001042c40215a4010250600114044000c0c066612141c03145242010940319681c861003503c110038100c001980c21005003d40c00407000c544035190710145601800c1d10307003074804130345113044000365000d1210b0b400749440d08030f016803007400d100385502d80604540c090241024801d200702480301407011070b00491001000080041e010200042c07604405019060b00300322580845550103110100740c000707005044640c2e401d860101c0c1c0003a8144110640710b501c0300a40e8211f6400000b2013415040401000300070000c8049404a68500c1074202c024800d03240c49129035042000481c0c0070350b2003072035085054240010300500180364410b14941200480c0d00460102d000c0c0c40400c2040755852150b1003003280f042443c1482c102d1403d80c003c2d140d00c1c182c0c20007820b01210044090a00216a0190310704090a00d007c5688a032600b0100001c1d8205902c5c11030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 603075053 1250 603073803 603073811
    0xb03010f020f0f0304150e0321011a030a090b0f041e1101030203060a180c090f030c0b0c010b0301050403030b09090c091503280203070f0308070611070609030206010504 74
    0x1400164600c21148209244107000d414840001002c0d8025880500160f036041b01158001070b8403a01403142c10300c400150002941e44403000502c1b0302010240400042c582c0c4c807800010007000c600044000401c0b503142500f56526501c00e0480e10040c0b0500901500441119080006854a0384501070160f80180700c1c412000740328060880c0aa003c07441d00a018503006807000583d5406a009540c100e90018003e4203640c3d00c0d108101d8191008000b82d08295449040c1d25010b00c0e0014141800340521443c408599810340d01c0c0d0045084c900d00c5005d002e82c400140d0f10701815000e502003400060000c0082c4118109404c00901130214090b403944590707400b80c00315608000000b004944903c000d4914005642c401c2e00b10b0000807000405541c050003140e04902070780c1c1d681c0b11078030801d2542c1070b41c081c01e025060041c189083e00c1c07070f005048002c0c200303942030000c1107286054a218607400310000c5558820310304030304510301600354001c02490a0030070003800c154021613040e040c1c81044d41e01700 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 603076303 1250 603075053 603075071
    0x1141005132606071409030c0d0305180604050a210606060e150901020616050706090804140d15020a1b0b16030b15070203030f0309010204240503061e03030705010b0301 74
    0x6a1982416130b68807011582039034198001182c0c04000c4d020480006080c0c40b14541c6050109065240000382200040e000243c0c50b0303c00141880300c2161008140e4a190070310742400c01041c1d43d28802d00805041d00c41030300c9a8144904031102c07501450341c0c040d40510186640d08000742c210190242581d20071070111224a047ca40d412003540c080c000168000d00841c3c51b0501d104012015000c0320104010040000d0700100e820741c0107580080384a8462142d03200c0c41e05126091011081500e944101050074034280803038032141c1d02c034804080820ac0166500740442c000c2d83c035030006118841c6056040840f00b002c0c0410290494802d00f08a40010b00864003903c01710100ca003402ca51941c0324540360402e0706c0e405500800b800000348040c0450b80340800101c90785100307030421200c400c0569000282071104003803103c8559000e00e0040b8580024038400d800207001030200400c1107004403d0500682458422038620014141000d41a05e40c3d5254600744640070300102c10219000b0741c03c000240d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 603077553 1250 603076303 603076379
    0x60a0f111303021503160809070f0e0115020604030c0b1e0103030503060f0406080730050304170c0105091c060e01140615120709150c0501050f0114100513 68
    0x2c80c031812006410380f0000b0382070041a02d01c1f0b98040c0c54a106881801004200d40840302020400791000c001c00032655890244a0003040c2100c940781003c54100c1024031002941061001c1511580144201002e5441c201d03128000016044441160f6000400000070305800038019406100e080d03d40200c00e0314018107100c2915a18032940c42c1580c0041c4040089040c1007091142c18071135108012500000d82d030f6080d10803101100191043d41000804002c00074805807901040b411180c007604044d040c0c1c00c000780c1907005480d1403a000c0c5451403014080c2810204c058803103580d0000b800c01c550362141d6003041c028052074030b0303612011441501240036460610440c42c04004601c42141c580701d50641c031154011400342000090003a15580812180c40c050309401c00e000c45543d070814400d119060a034250b44000d008100b48170280d0005000e42400b0394141c6144401c06c0e42c00d0002c49e500342204644030b224042e015000d0114085000c15243c42541d00411220000001c02110694011030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 603078803 1250 603077553 603077557
    0x706111c14190e0604050c10031406040b01121a0a330903080a080f0a0203160305060a0b0f0a0e2d060f0c0d0306060908060a0f1113030215 61
    0x1d0242142200008080002c446100c1002600c4410042407000400f2200c51802909403412529a00245140c8a0074102809002e0000d146403400740034244c080b14510110300c04c0900041d010355200c18203c040c59015050111013950404000c11100711a4048007941c18105002680b040ca010500040c08503000401c0710002060301d40308001c0c0c555a80c0d6541e8007820b90348031038401d12000b050000042055900a00b01e601c1c0d80c1d13180d45825151001c041d2004020041c0000f4410744103106002ca500820014907000b4106400c00203181c2d01c3d034400060340c0e184690702c180f03130740d240014a42c480c011004018003c020b440e51a940c13a02c8420108004c1d070b09034080c10000c06841140244084000c000c207603802c40c40c401424142c44c0c4560303858018180d030301068160509a00c0300d50b104200d1903141c03190700014003052601c0c0f004039050081d026162440585194403480d210f460f0b01400d40c1c50b42c0c0c40305645d1741c170580c07006545010100001046e01d500340301c00c0c0e2003074010b103080042070340807441 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 603080053 1250 603078803 603078821
    0x905030c0a05091302030106082e140f041728030207240615081005100203120c040503030406020d030b0406030b060d05010b12011a030d021906020706111c 68
    0x204103141961084c0c0050782c6003a00076016031345503499080004150000340150714040e00b102569105400845401d0280403503011130b0600000e281806201c40c1c203421441882e084000c00c941e51055441c0d50500d0420507403524a07501c0841800038040185003d2a0003000040c00701c01c0500c0820550080c082d004c074020740e0009441880140e00d0b038a11109641880303401c601d09800005403050312101f09050000788100340c3c0c2c0100c0e00300030502090001d804040001448100c40c082400005200c1c02508c90051902d01c080080c120008940c3c9544484255000307072002904403511941d580c0c400940d43e000d52500980405d10303101c0103c010342803501442c800c0da50040c42c100305548814050060343c410300001910075541ea04281c4000355180c4001c0c01111200e5400401c9a00c1200e200d02d501032000c070030b0740e84a50310420440305081d40200700c11215041c144800f0f40d01d240c0ba070800d031000e8850000020525450215039007855898030000c0e100b1036004192008420008600c00011a04201 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 603081303 1250 603080053 603080059
    0x20f031b0406081902060a020a0618020f041b0e041e05101e0303050a0509090906070f08060918030d0c050a11031305061c06091a09070c020d0c0e070905030c0a05 71
    0x40c2c41e11301508021000348603440851040f10080390a0b0f031540d0040744d0310f0012110001c15114204003d45c6444d0701055a80341c0c1c03c0343c04010340c1d500ca08180005a490741e44160500c145c4460092980ea01e0350303c0169a140d151000c410b140300c5080d035003c01000d04a2b102e203460f8524103000300d002c060392035003607205181e00b1010b001d50314115102501d09800c0100040100501001660450344407080703002d0040341044002c1c00b850030300d6a40a0310816808402d8020040c1c0f0104000303041d5a031006003500198501a015086941c00070310a01314070508480202c242c0c1450001c400c403550040c020100504a941d0381495100d0a6211b02d449100d9017108000140040505000f1450100028a4509000c4c0e1054108013a1420660195502c40c0d028041c9541d60f05904c2881d030310a4504643e208078100d640401518003598050310000503184040d0046481c2000602080036810003000503040d095003a240a00d46650300910000090203114000d0090000d5203606040c2602c160b0180d40b001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 603082553 1250 603081303 603081343
    0x307020a150e01050d02190c06050106030209011b060b09040c080d080103081b030c070914010f0803031b0f03010e060a09020a02030a0302030a09020a030b0f0c090f0904020f031b040608 81
    0xb0044665811965044d482c05508100c1503001ca91070700c1503682e0032140d41c0c5031191040d445080610441d04140d004c030041c1401001082c1e046c1c1e9001e02c15441c012a98103507112102a282880d074018070302c1e0041190444014010300c0103101e075440d0110115568002210750b43c0c4110001114241e4003840024003031031041c00301c5034650003045030070348151004604507030810760315010080c64010700e0381c010160f80f50755400f0b269180d103401d41d020b8050441444110403d5140001c503a0303070f900c00204a000c0d0081c10301c00410190b8020001c070f9400c60564000c11791a542c4818469141c24015501c407403245860150004015015000b512076024240d0080c41c1000803548041c1c1c041d600040641058640d01e42540d0010394039445020040c5020710700511092804207049003840e1805042c03041e01a13400d022062103960b519681300096401a240000562180e01c04540d000e10070070300d0b141d45400350807046001150552585882d1360740403941804540d07078681c2603580b02e8104c00100c00044c0c5603 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 603083803 1250 603082553 603082577
    0x804030f15090b16020a021302180406060c03210f0204060f0807020616020f01020a02030a02160b040306021b010606030c2c220509060601090b0901080402040b1207080307020a15 78
    0x6036001400e00d5401c4c0d40186c44918032103030300142000e040d0034030b200501d80c0d0115010301161540e0658120a500c1a101001200d0070030002801240000400504014884142d1091112803054840d545c070400d20003848180ca103804004041e4109008420024030341036411900c291113010f40c1c9000d481c5a40180c0030586401400040440e010359400c015032285041c1c034418040300f4402030082814030340c061500c5509a010003030a0444c008002003c1c004040c1d4140f0070041e0f554111070440307602c040700503a02e5141c40c0554004c60044103001c1100d5182c050f00040e002d4054101070021080c6542c0e00603520b03c20b44100700000390a0710048154021300002d036950703042c4800c02d41218100d8039058188180401c500c00d05070341003241d8080305508032000740003043d41c2014942c0302901d507001d65241065040f800007850444000d0010388955100d180060a60f100c01994081036510311054074142500c50601caa80d941c4407210490141d417200f00d0004110700c482c03010f03034030030b0805554054130804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 603085053 1250 603083803 603083821
    0x2210703050411061e0f070b1320040f020a02060105040b0402040f03022103070f031818090c051203041409010f0303030e07050405090c030105010b0c0a14010204030804030f15090b 79
    0x340b000c241e0340ca620131801705c411591000181052100d040400c0c0c0d031728039403840c0c0b40b445564044c0201c0c040c0090442e4090000e4840c000c0050000d2840d000b503c0c554001800040240108004000405100242105c0465800308034070303041e40c805440074001c0c20524800d100c01c0b03115a03c106107042418107414001031074604c02c411101964103100c070030b956920b00301e0300703041da885102c04903010842c2204480825400090000c4201c08522040c0300c114640b240c402030a480001030102d48907560f2049504000c0c072414400013400001e085400030044030130703c0954aa101c2d00036151030481030318100c40d45203030001890781611440e035203460b1074500d195800d4014100320b4444008034040d024010616840d54454148500f10303a000038901c0d00c407903800b4142150011303000700350140b004019450304e420f00041c0041035642d06c40038030b070b0040701040f0900d802409650001042054001170000600c86100c440e040c0182c0594020741307031100460703018800c49440c500d0082078030400f83d000400706a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 603086303 1250 603085053 603085057
    0x6010c080c030405060f0301030b01080109020f120a05160e0603070617070e04050408040e060405090c0d0501020417010b01120b0a06111f05070909090f080309100221070305041106 79
    0x200d075420440e410961100c0c0094030a4004502d4400c007044044010800d0102d40c0781c00b81e0041901030000c2040160039004a21390f000202840b6001e0900310200c0c52003100d040048188a130b401c4401d90f01e0066a5400180d5000002c0c070900108bc2003600100b106464042800002c60709551102c6611500e50540c0f114040d00081500d4207000740b80f20f8640c0756407142d0142920071442600c40a950344c0c200307205000656030107006d040c010303450300c810440d0513500090300700c0c00c400382106c0d0004000503034070304140079102e02c0d040740e042404812150300c0c000205422004982c5c4003606c4000940e4103e211060071141842079050b4071031003490f41004007074010114070031041408015603004142003a000621100c61a042020850751340040200065105101c02d0107403c854405015860300790302c03103140d404800c1502070480d07403001010564504003000030a920398503080d030554403840070158441c11660f40118111440c035211000480252182c465144580da01c1086180500c202e00b003806569 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 603087553 1250 603086303 603086317
    0xa050d030809100c05040302180f070e0d020607060504020901170304140109090c0e090a150528140108010f0b03150604050411130b0708160501060302090712050f06010c08 75
    0x14040d40406502100081c0101c1c14900400e0b02c071750f5610361075441070090700180b40020500030031054080c00502d00303010401c07a40166291800d40740356008800010610481118000e50282d800102171003042042d402c0188120300032220a42c2a0307a032242c130f2501c0740882c100c0c400e0181e00100010f00012444200c076160b00c400c18500854180d40341d001d25401c6841d41030003a0701007901d060800c529440d1284034036070310010303004041c090142e205494031a296000d01401d03201d0308501245903240c42d00e4242c0844803254100d10220203980e110795810303126004000090000b00c408002140610700307080f0300e100301e49070003011500d1070f5103400e1910aa061800c000725485030040000160981e5a80159200b003424000d0390350340d4510380d003c00d110165413580219440c001c1405802e0200d200102655800104d8a40354252042585000b500403e903c0d04025070100d10343c1c0502648540c48004c01c0122013421608203c0307500c0705501d1400d0080c00700c40090002c1c460190500000700c400c4040d1040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 603088803 1250 603087553 603087571
    0xc0a03061e050a05090c03070605040b03180d09080f0706090b0901030e0f030a031406091f0312030b1311031f0e011d0c07020d11130c0f020c0a050d0308 67
    0x10900550701a8410342c0d0040e41c503000c556442c0c03030602c01740200c10301c6100004d020403802042160318040303024105c1c1c003491082801070540030002544050001c00c480013003880313140945070300414500001c0c0109205024000701c5101d21491204818000620305050310801d40328214060b10700b400c030313101d1a0310100e032540c105525003ca1880c609010052503104501c0203000c1c41c1c40301450340d401401c61300004050104001500180656503c40011454001c803001c00c01c036030b054032030035282d20500e03419a00050030b1200306040401c05943c913902103114a50708941c2d5056a480d082c40e200e080e605021014035960f502003000c03641504810803d044942052844031021555958880c0c51380705c0242d000010400d085082c034010481c0794040307150b0184a0015103030400000c4c0d004200301da07041800c000c040003116000c040080c2c2d2580c04c407098403560b600b401c0c4a81c007200c43c001800103960503245c40c0940729040c80c2242c00e150242d0400140c41000d445c044a4155a86080303600407000340025032 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 603090053 1250 603088803 603088841
    0x1609031104020304050a0f050f0c0904150e1204030b0103032705190e010b030a14012106020c0607090801050603010608120703090b280302160b1b0408070905090c0a0306 74
    0x400a6847d1008140c0300d80604041c0620b0302040d15241d04200c152680c03184103114030020800000c01c44880184040700000d800241e0400082440c0e1805140c055680c91880300410000b0400916941c41c9059030300c20364820000c56032030200c0300780f94001010f0780c4503150070056051002d4100401d0b00000b0749100c40810754036594682c600c09070150282c01183c40c5c038000100b0400d041d12940a079071042e001c2551841c4a0758544000c1c002c1c01c040d00d85050030300922201c9030710280074580c0c0569040c404c1c90130a86200d400c000001a01e039078480e100d41c00c010350800e8006030092030180b00e03c20031901260050075040d82d031078074003603041e90120f0b004400b40b28013103201203410200c0801410314030110000b0400001e01d031707400c0c1d544841c40f006108000c00d401003244803034404a22148020090380b19980e20b4903500c40082800480700301c3c44400c200c074400446c00140e01140050b100086645e0308404110a888446880d520340700f504101c5030f0810041e990800c0015950390046a802c5000e8581d0b130 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 603091303 1250 603090053 603090073
    0x141519080c04050a060206090c0a0503120a140a0305042a051504080a150f09020a0504020c0c03010e031201091a19180507410c0d08160903110402030405 67
    0x681e222404c0e81207600140d101c6030400804c4201082281c2c14503104888540190740fa0000003680d9440914003006600b1003c55841c8a05004440354590441d0310a403007511100070782e40c001d006003070440c0d044e02e1a920401e201e0160f1011122104400210981c108440c80d052100340040c01c03480c0d42661032444010000060b40c42d00501000c4a1644154048001101d9506405080e20901c0032403a60311843c159145006950b0b0110140840d034050310096125080d1442c000c6c00c103480e404440740c16500340f003003e1500c014088000c0251001c0405082c075540d8903880388400312400c00c0000b10382c2603040e0190700c9403031819410315007103d000c4101030150340e5203440c1c2c3c5210400315150a007026039154010322116641010241140c40c0440c245004c060807121081c402c03a100c0300145004079000880f0340e114820a28049440200400e4101c40b80710b2078102000741007000494203007506082c03660182a4080c400d6008000312034010702c224401300d18bc481000b00a60002d04102ca542c82091080 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 603092553 1250 603091303 603091309
    0x1110d0507021f02240601020307021516030504170c031e1903030510140f10141201090b0a06091406090d0614070c05100504050c0307141519080c0405 66
    0x800c0c01e12580c090195652240090740c1406004c0070b00152017650001080b00d00e0f41d000003901e8019404407200c03084140c242ea410300b840e1040b411102a000300c019445024140c1207401003044803d45810400c0141c3e041c0c0d100d58940c480800d0080d4142c04c401a00b8070b5028540e600000c810103c8010b48044000700c50316102082c814179002c40c0440e883c1d00401c40254010107210004001e43c00f11507008842550000d40000501c81019102e5400c0da11103030f00700d0f031040703410800c004c1c0460090703070351600c1c55040468410001d129501c0070605080b50514641824400202210401e46034260018101813020343c15004419102e41c0165003400a02000e907902a0b041c24180e000b0000000d000319800904042c0110080203c0140460510900000303500050710740721b1000c1c00400095070340c9403450a40d0810302074205095161007200350110313544000e00d1880810f00012900035600010803100329226014a048140b0314910701ca440e0f501c41d80c0240e01441e40200c072011100d181903128000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 603093803 1250 603092553 603092599
    0x120112031103220b04050303340b0405010b0109030f032105130213050c0702061e0c0f06131211120f040e060402031006050d0b1f0e01110d050702 64
    0x1081039400e04403e075030101d0071400400c3c00a401050921481c2c14184000310b5948d210b400300a4000000442c41001d0b080c895100742e01240f0f203100441c2060004609148003464401d407025205940b90015540311507005900c841d081700d81c445d218214100041e102a905c034048206904030312003512440e49c0041c41c092107074034441c12004090141420450050003240440807180ca40c0907403501083c070080f20900c00640301c1965044940d1640c1d00d03908101000d4205000c3c80380303060703071001058000d200040481c6540c0054800c0701140e032166100400d02c00090100c0d50082c0480c4610780001c0d400510405003c641c41500303000b180c03034507145c1032056419a03001c0310b2500c1c0003080114042c40321050b840001030f00803104841c15425800c0214a050443c042442960203100c0001945030484800e5041680d40c188000d040e01e2000c0c404a119449a00d88415100000740c00640d091a00d58007a05502c01d0080c9500000c007019540c01100703807515400217000b66030022080084000104042c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 603095053 1250 603093803 603093817
    0x11030703080403030305070e01081306060b0a030203091903050a120e0f0d0207060e0a301a0a09110907090906030c06020f0f060403080402040e06180c06120112031103 73
    0x2400c02d540c0c5143d81030003021580080d0400d0100503501102001c00d030391000c900f5401090048081e071003100e461a240000b44220341c40708008034404a401481c1c65010760140d0b10851210058030301412501071100c040000000b4010081a0140400e41f0718074441c0340500c0c40010001c10005100030503140803854035540d600c40c607407a940010003009201d80d0601c050320040846003003408480c1403d03000510403604038002e104001610441403215104003411040079000480c1c00c01d600240c0e41e0034101c3e03002003095051204800e440b40400d04102081c450001040d030000700c40e60650400700100504860040c042d80200000b940c0b001c901d1040780d2048030010341c817a004407556989815800790610b403e180111400fa0000d10f41c03503180340b2000c41c0a660090340b5140c02d40d020740d19480003600030510b444064ad460310450041000c440700850342c000344120304100f00c0d00094180010040c191045189003c00c0b001c4034401000f0420f180e20b00e005601d482410407110700305113100d10910b15007002d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 603096303 1250 603095053 603095063
    0xf01090b0616050a140c06120403030b09070e01030b01051c05091c09030507050904150506040f09080d05370e1606081303051b0f01061e09090b1311030703 68
    0x610401001002d05103c0d1024440d82c4c041c01b045402c01000501500840b00121001904407000a0806110b40c0c00449100801000502c2c14209a0b400405000c828420399010900e0082c040086600582c00c2d650a203404140030b28004440106400140402070403e64141c070402c030b00549a480d812041250210703403980c540b65030600d1420410b2400d0180d9102038046c19141b014800456201c00030207d0140b100e40300803c041d100c40740070800401308411164001450034942c0c208002140c401001180001242849151240c042c254408280c40f11402c0b0990300348240c1342c01c0c896007140b03044203416500a000440014500c00755080080503840d070045078140000c2404510340000c84a60404c0c01c404002850341152758014200344206440480305004801035041442400c2041140e86da920000900265503103494021281340c0b240041007072800034400200d1119840d1003500001500302d50041d003992529140012920300c480c0c800d60b209000584644243d440030418080158450 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 603097553 1250 603096303 603096313
    0x304080a02010b3a2f03030307050a020d0906050a030e010b040204140108070807020606010c0f02120102130b07020f151207090312051204140a14030c0d02060f01090b061605 76
    0x20041361510701119910034650002103092003030100380342080e81c605a801c4009140e041e0b01000354900d001d0a00d001d0019894440042049100c503444000303444c00c08655001c6a80080c40c1240c190341810143c003e41c400130300e0500a200000c2c5c820f030003821003642060700000c0d043c0007010201c3e060383e0260700078902c0783e00c20410300842541c0c4034211550045807440c0c01c04482c20b0102000b9110b11015001a0420404060318004e1165050306241c8980d40208922070080d55000c001c0e01075041300c81030f46c100c18210342d40001c2040c29182180c101c42c1c4c2c000c04080d06401040b0401c425450300c4024400b603c0414000118411098824a40202599110030f03c1e618039518000d0300c4c401100f02e14804000d0244000b021120011084980050307000c404440c0040300303410185e00e001103000002e0001d11103070503a56070800012004001c0c0c010480240c8050142c00c400c16641c4900c1590701042c4485113500401c103c00e05603014401c0100700800c80f520303040311215400d445450000b002d54040e048 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 603098803 1250 603097553 603097609
    0xb070b01060f0c060c0909090f0201021c17150a0915050103060b07020907050d090605010e0901051009050901021207120b10120504060b030601030c06030609050105060304080a02010b 80
    0x124040c01403441d403a082e46409900c0c60020224040e841004140729158040d0204042c050998a40581042e02080040f4400c6040c000181042d41c10164007502030f84c0325402c140c0084501042d0407021316110041804540b115503003901d9401400000380218000d000e20140d920044010020000c50801103103c00568400e42d411032007961086040c980782020402540c0b10807400e5642c80350b01194003100c640da8241c3c0a40d09842003800300d180052400d4102030030001c40e036010606039222aa41408241c0d80c44040c00d080303400540d00c4030440358141030200240d05141d084154070049480002d170602c01c03140d81c0c159003503106581d1040805c0010b41d010020388203501c50240400e10031241d0151030303081c9103406050450503100746e22200f40c50348001414022283c0183c01801c03009401c8a03090b43c0d60381440c90103500207000f000d00190034401e0014801410340a95410b0300c40c020851391440d03e56503149082c96000b8426030055540750001d0300c3c01641c41d0403620750546102c9244803a5104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 603100053 1250 603098803 603098813
    0x10303020105100f060c0606030b0c0406081608010e0c16030801090c031a040209040e030304060b10051e0a02100c0509040b120a0212031228230703060801060b07 71
    0x20020300c009649003d04008003c000b04005000084401c1410000f18030999401c10707401400e000d40025100403010401c0c0400c14000700001c0045034156510310580d44c0b9030745258041ca0010098010014840c640140140e0f01e10480d6142c112460001c13403850300741401c100c00d4100f001d03500141e010400c54401000002201d000b03244012400e4501080107aa032407903e880107034402139019000e5039002c191300000ba01c40d0b50109014068074000c40e9180d10b41481c10b20007900940310a42d029043c040000006103000c1c0d000d4aa40b030303114040503507851640c49d110181741d0304040c00c24402c600c21806c0556420302d0341d103d80304015a495030b415a40d08234000074042a610100080d90040c00100b138280c00e4010301103016144940e04803000a41d00f42e1002c58140355014880050116044074420f0080d01d642c1451554440d01e40700095111210107110300c03074100c1e040c0307034030f401a001103180c000f03080c2287c0361100315405001e40c100000c41940301d16030182111155007113001c0c0c2c800000303a1001400703 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 603101303 1250 603100053 603100061
    0x5070501151706061e0a050402040b0a090b030915041707050703051606050405040c0e1e01080c041202103e0c01050a050903070e2401050a02030a0e04061d0103030201 73
    0x242c82e2030000c20700d6083c8000818813292503140410034424200c031141c029a034800c03540c0e10003001c00420540d00d541c1c440000c1801944000e400c400841c0c01c1d500005041002d560035a48900e9608010345549403000d84491459030000300101d40386079901da0348000d17000e270000180074a180034000601071941145091407502400d40106a0b030910f04c141d04001c840d522a040300d064034425140400c0040d940f000c103840e015299400d02d944481c00144214842d06036406980c40300d4000d80c0c0d5170b40142c65480c0208060b208501911070b404507010110400340c01c145c0e50b28400c001543c078282c845088040328014910b0700b082d84001000c1412480380041c84240309403c9051031a450241141010130310010b80302d845079503c00014000e01140c806490f540c00c0c040000103048000740c10001e4944030129400d140d5030141c807020100d614444d0009194410010340c0d2840d4500e030011441c0480820090b034039508554041075000341c4030500070a90199004c105070360200092100801c5504601d8081d00351 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 603102553 1250 603101303 603101339
    0x408070f0b040c1a090411090d050d081311041e1d0c06030708040b090a202715060c0109080703110c1305091603031e030b150a0507050115 61
    0x2810000801c0300d03040c22000455040b10803c60300080d03150f581080ea4251f900509002a1380a0444900310083c010041500ca07840e901d070740d0702c84580da9a000066040780c0d8182001a00c003030225008031030f00e41440d922602d4680b01e50340c410740c41d010303e6007808419101c2c1e5404101454a08a50a400304281008800d00748801114124190328081d20000c01281001700040c00c80b0b96a440442c0004030284000d0260540006107800054502c021080c00104400070440c0550100a8100b01440c1f18007242c400781d01a400403490340b51612200b4016220031503841950040040149428282c400d03c00c20192074030400c034458079102d0a0034003402128400c510042c1c142c1010148101d184e42d403107010307503141c5121007000407680c40b58008207207002e210311250840c82e0201e2001005054000c2c102081103420030400c130001081d030703007400c400742c90950a500790840a03500c1720108021800e00505283e05c450b00e0110304043c540c0d150301c1e0a580b2004110024403c0e406018824a82140c01030500c1c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 603103803 1250 603102553 603102569
    0x1d07050109030f06110c0307061508010203040b01060302030c04050a03060b120f060112030c05151b090603010b0d0213030303020306041109031005060118031a07091a030408070f0b040c 81
    0x5810b02c1c640720409145001c03100101a503035292414100056480207070b03004a40080d0480c2c1c2c5881061800e00010200c3c007140c541450014540040d40b14414021a032286500c582c282816920b0b01c9801d07000b1f50005481e41c01c24507000e104c007040c43c0c2c4400f01884020750050201064040005040c05806440003100b80c0a41d0024803511003648070024550341141c17503c00010001030389074101200e034015405001881401052b2488100400c070b00291802528551882c0224024200610503035200303142c2c03025048a02403004001074450107000d4801c441541c000585420441c4202e03200d46075041d0021800303c0d90101c04c5c0100750420f8480c44d40e0310404d40c1103051030b010520000a6403000d1440c5c0308080c1030744403000901140d10503d11135883c0105481c190380101d4503403410f5145241c06c90459901c20a000f0000b07003200384140160706c00c407000300aa01080b4000c2e141c40b4902079000500c1994116010844c420004000c2c12007411080d02400d1510a2400c05c3d10300600316880c2c0f82e1020f00303 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 603105053 1250 603103803 603103817
    0x3230a0201020414042f070209010b09040c05040614030a090c0e07120203010f03061a0301020406051b1b0907030621060c020105070816111603020910060203190309061d070501 77
    0x18900c09441c90700d20f500500411b0418461038640c40c1d1151007214070082d0403540000c00010b24840c038101a0002060455050110341050f8008480c1303405180b0841000400000740714140110450040d600200300f0070001c80c0180c030076111440c070095103130b1140b4140098001003020180d8091044030b071228554106503d9545040006181708447c0c3c00090074450780d5402e221101c0d03164004554491001030000e6413556503039480036080340c0040000003d000350101c2c00002c0d903c0301050003c03400c11001803502c0c480100005025024100400820506940d800041054101d02941a40000100880c01001065890f04c04150751210507560203582c104014001c1260b00255074642c084000707c1f0341c1c00c406d81142c0381110085814a16030303160303001d6100301e084400000c1d540602924001e07a03160004d81c550b18006e103101502c521407607005810034041d88020190b2501203400140407464007094a0159484040072101e80c075800700501002d034500d502582500703001010040009080c609 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 603106303 1250 603105053 603105071
    0x1140a1508010b0a11100501050a050409080a05090a030f080901120203100303030e19060504140703030c021903080c06040b061c0b060117090309090f090a03230a020102041404 77
    0x3070811841800340b405034440c00709484195620420089a901a174582203420380d103605070361400100800c0c001c0a008848054000c1802c0c2042d001d001d0481c0d82c00a1340030b00e0703e41140c00844041d0449840f255010a036890000041440c8080c50404071780581c482a54a00301c0c10700240405201c2d540c1c1011141c0140100810448442d1440b02101e0309401c011580040d010700840c00c11403c0443d0013001c900c2004410b09000da03562095100307511400c1e901c8410a000302845546a0b0507201c0100061300c609100401800d004d05100c0c0d00400000341120001c3e102d40d04c9204980204000042550061f010070081c03041280d00b150300300609440c0c0a83c1d50301d919010b8240c0100118015081586407400f05d002a40710f0f0f000039200c800700c200100102e080c004502a16648102001c0d0310581c6100c01240703c14a202598600400022004102e0078985640642c0c103012440442d001c1224544a1700085080c0c800c0204400e000303590006a41e141040031020715803001001d01c1d8003484c40c0035420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 603107553 1250 603106303 603106307
    0xf050a06150c0503040b040f090b0a05060a0c0c03080d05100e0112080c07050a180e0d05070f020f09090106061409010c0b0c1606090b1312200601140a15 67
    0x1070700c005203841d0011441c242401d1240c9140314903800001d0403c80014000341c07a0300006280000d90320310340c17414000410600c04008590301140902a40023070104181502180966030384008140720b643c1444040b40c2d04c2d03c82d00629040f0f00c4103151041d490b0b2080010707003034211400c0e1011307000c003442903501941030181032100121100d0005224a20010b41040500070402172100113001c010940301d6030340d0f03d503000e000510f61080001030100c0d0801801840f00301000c0b5004a103998540c0d18139041a803c2e44400800080070a0140e8015011043c003e4103500d07802034003803184003483c0000c5506860880018205251a5050718944c1381c2840140c23050b80e846105000b44981169403001c890f2103020b1010542c0c481d40703203200c49500700002100208501d0f41c01c4442114042c0300c0d002075030350f91110b010325401c4070320030b0042000940c290020781181c000d09031141513485000d07039900441d02c0c01003046e01e081d00c01e130412111000781d602441303464030f07200000d08064007020711181d94040382e401d40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 603108803 1250 603107553 603107579
    0x18190905070e15120c060c0102090301052a12040303180b010b1905160f03090b03010602061801020a0c0623040f021c1a04080c011401081603020105031620010f050a06 73
    0x2c5d0b580b29000010ba0b544414400350103170741030740000030020041c2d41040c4801c05541c1c541c1e25000e600b118040340392070007110703a1101500ca80c070880b0701c1045d02171780d01c9a5084005022840b41607030702d11010226140401c0300c01580c18040c2414140306642c4840460a000440030495041c20400608000ea821002c203a1880b5034041ca0f40a09103071450b0907a441d042e03034014066000299000d00200002446541c00500c0713078003840ca407000c03804880c103012030318500340c0c17007251603000115040044500010700781c6d500894102c1c6119120303d6203001e8502c95280d080d00f09640c141c0e0300a08007650b1100350b19000041000580c2c0c0c0180008000c0c1031962403840641c0b10344050305000c0c8a1400140c24032502c0000c49825400b841e008020f405030070950008603020030b001d1148548209507038407805201e0300780d100b01502e405850345819907407541d00c840c2e8500854404c10080000900708480b0034505955004410441b00340003103548008142d1400c102c550042c0405c540302d041680400c40c861812340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 603110053 1250 603108803 603108823
    0x120c0304090e01110c010b040b0d0b040b04080f07060207020a050f0109171e010c02010c05030c040902091f020d1b0f020d0203011b031a18190905070e1512 68
    0x1c030220702582c900c10907034010058450603e0500b200011042003601066002280e0751500325010441d80c1c41140c180b002c2a01007810040078031982c6c03c0401e0100d410030051325841480340980900d46800c070703510303c030b001d4010300f50840f00c241d008a03a04045140078440301014101c00d99003031044681010001342868201e118140f20704c142180d07089203031541440441d440b0100e890344030450403201100b080c024070400080740e006510f896802201c05111b28104c9008880c400d14080c181802c080402d0003d501c90f003461548202c803480c101c010ba406030070049110401d5a0040e01d40d00901034800307040a150080102c1034100c003100501e000900d036840481d03800b40c040c1c4040d03425998134400301f8010140003404e00321458652640922150b41a00161490503140d076480c0342c2011404c080c066040c5100c4c1090600c0040b0800154803c0c0d40240c106107240c8825001207410000c54440e241060700d00d4100c0c5900d01030b12000c0044280c03080b003010b00c2a8130300303880048041c52403090607521845102 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 603111303 1250 603110053 603110069
    0x28030f12200a080f090d1b050106141801180f0b0a080312130201050a03091109040b0702070608040b06010c05100603061a06090321210609070503101203111905120c0304 74
    0x24a03002c40300007d820000380981c0031008010342030701c03076000341086200c0c2544d4074804c0c4030a07400c0300341c22807280f5a66412507413801d4005804210641c4034101619042c4070390360403107540710901d0400750b441e1504000180560030203542d4416000001c1258004018812490000180d952400507640801100c80164052800088401c41403400c023070300f9030020841a90000e0380707600f0f000611040e400c41c6070192440d50200c07070010740d0b100000d5441d500d04503000740c014901c04000507095401241111003140c4070b103007a50792402c01208001c040314a10b070010790340c00350b40e0b803605c4030300820001c8003440030b490445226040040d00000a40e80d0052419420040d611620149400d09856029101614039245002050107046107020303440500803a81907100790001c1005c14501c1d800382d01124021040300c3c1401c0d001904104034084000420301044081014000c072242c1e51400500c042e104070100700d902041c003000c090504500c0c1c260640300c0354251500c2000750140d01280001150120b900413 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 603112553 1250 603111303 603111317
    0xc0b0601080c1c0c09140d0602030402040e0307110a0b040506030411120d080a05070e090f13060515010e0402040f300528030f12200a080f090d 63
    0x300c90707620314040c45829459030003402141c14841c490b0f6421202c0400601e582e0b500f84203580380c03122035417560350404058005481c01c4020010621a03001160b00500141010400402c00e9070400c0ca50b91200d03805840301e6505652800f071a14142c4541c60041642d9000141418184400a40c035032101030300c01440c514844003044560345942100e00450b114010564407807491124014204450171550004d1052404001400e900e001d00c4041d4904107000d81601d12590720140240301d21000030300170042108003500c5081c000380704c1e130003858450a102d51280b40c4400c01000003401c0402883d1080380300c0c90050200744103040b1020030002c1107a640f50038004491a03c00b050884112400c003040c1c1d07140705000700003c00e1100c00501000b5240642e196038260617280c203c0414004000e1000500044000d0100c02c0e6180c0b1034412120101080540010600800142102c0752800b43c40b40d45095440441d03031070b0f159034221503c10352001041500403110f16201429685468091340000284455 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 603113803 1250 603112553 603112561
    0x150f05040206030f0714030106031409070f0506071106040f060206180d0f0c02060c0304050a12030c03030504060b0d0c080c010305040c050108041a01060801051c0f26040312020c010c0b060108 84
    0x11642d488070107030f82034121b00360741c0e961135040c004d000c0c0c1a00d8421140045000010a01446000408008071750582c840c0301815400d10040040991140c44150303183c1095600c00c000a50701c0c24021700080c036603054200d20702071402402a04260008000880c081c0c0c54503180011101c01042c80080300b001842d01e0f07407902c0c0c45544252156011248065081b80e4081003003032042400200038820307204111480703000c5944d02c0803107450715400710400030b0002c0d6000d81a0340001b4003a800c102d401c103104940110300e02c4e58040100f00346200001b8243c0c0e04048600f002c02444000b403246c000040020701c2c040c80185019118480000020710605042045902c001405c0c0320319283c0354601100c4c9960000400e507900c901c0101042002c1c081c00c2d106800f04034a030480a540e100c01003071300507400402003508450030749a04c0d00c002e4850a00301d0507100d1a000301107080c1030200040001e18400d882c0c00034040450400240380c54009001c0c28103026202a8950203d00c040c10010382c4a0340c02d10344403a143c0c1e1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 603115053 1250 603113803 603113807
    0x2040e15190609020309160512030d02030604060902070f15140c090d140615014b032003011d040318121a0112060b061303150f05040206030f07 63
    0x60364000400d03d4400300030320103080c50110b060b0603e052103910340304a054684040048000c000c18640d100707640104607006418070031790081d56006030002c100144141d680c850325010707640144407c840485082070650304001343c0c041c0c0b26406040c40001003041c0300041190000d07400001d8500042081e01240c2d02d800360b920507180d080865882014101d404101000042c0d88040540d880d040e5222400a107a8595105840790001045001c07802d0840d1810154801c441030340802c00c02460020645400103804c0c404120084904010390300000e800803050700400c0c0c206403420940421010400040051303102d402040e1381c813100b2020340c0b11302c1d41c1c586240a81e41c9020703030300c0e21030b0072000300305030024000c00d840300e090701c0c002e000e844451f020b80e0f0322066564043c0024001c044101d01c28011f400049000c035030059042900150a451500e02c0520b5010700810507548115007007051508401501c000900480c05849040300c418850707410b00341c2c0011150b000082c0707540c0c02c052000c800998028 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 603116303 1250 603115053 603115061
    0x10c0503090a02060927012306040e0613020a09051c05030901050a0c1205070b06010809070b1c141012120e030c10050901030e061b130806090a02040e1519 68
    0x14621940056241031b4440c034088140200748102c40706118410032500b0300c02400003403d010720000a04103850b00b8140005501d14081c00790030260022903040400e801d01d071040c4010040142a03440750790400b85004100300c01c00001c0e0440041504500c8581c1c0c0c009403000040d10701c01c00342401d02c0368072803040d01800c90345220640c0000d07019601081c41c06107a240c21070020208507028088070185c968410005480f401c1c01520200030070b5010503c02c1000000d0031001d03280318040c0720100024980409d1180b01a034203031440ea42d6028415005000c001c00c040d908400040a1042000f1084c00d017944030103003c0c500c1031505c2c40c28031020040301200e554081c00f461418070710091400100b03800b58900144150088190980400d24220301100a640001461131150003100015616401004415016134000b452000480d1041400c00700b400c42050201c54400c070507a000901c8000790302d004200603a203441c1081c05d0382c0d8000f1440d100d4256a00d0282c2984064071200c07401e40c1c0c0720300420b800c0c028 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 603117553 1250 603116303 603116329
    0xa0b0d05010b04061706010b0a0c210e0105090a03030503090c040501261b0f0a05060d240e0612010e06070e15041410020f011509054b09060405010c0503090a020609 72
    0x2208a002f08900810800020607c04c00200c1d903484a0619854006542c144204c1006640c0080c0c2c0240c10000284600001c5500182010558240402001c04241603039000c0c0c000b51003200b004001031204001181d490701100762003000030441c0c0803039014000d11445404801c00d0007020280900800d50300c44030b1a00c8002c00300038040569840703402c05403000a01001c0e8a9031044004c0e111a40958152280030f181980c034154680441502c6074002c001a41040358680441c554031514410040c0384144a40c82c401c410b16190046070202e418108880202d40003810540070800384000d0040405405203c5007060b03068401d43c1021604080507458441c2d910455a000e41c00c00f9607880c1c0c3c00042559100803a00b0001c401c1c4041c0c0c50360b1040042c1281e0740ca800c0810003100d200f100040310104050711038409000b800000c159404c0118540501608685128807a4440d03420b10003007080900c43c581580461345841070031818403860840c1c03035040e40e8101074412840464002d0040e5907580c116044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 603118803 1250 603117553 603117563
    0x5100905071b03020d09060e0105160c0f080307060509010218100908060c0d0e030301032402040806070305090c0d030504051e040f2004030b040204050a0b0d05010b04061706010b0a0c 80
    0x14440755443d000f503507020400a03040006e80b10310f400144c46409031003010096041611039a0404030342807c1d500d031002d1940015030754030340d00180006d0540c081c601500050070b81c001c09155200010306020003580c5000d08624050780c1f04000e500142000b003101721041ca10101d44504020000d480d040316064800d80003240940136500a00841110b00c00092442d0800071300140000990032920b0754070f9000c2440017a01741800700b810702810492218041100e03061001005080c192240691841c0000c00c86801001c65511070034410341c0f03e8104802985c0040885654031702105507a4001d01500a500c115405825060803040280c540300216200e0400d02510400c258140c0030040e00251004c403401c1c02032820360040081c82d9408410866064079044404143e00c0e84a682c2400024200180b484403155541d076035802c42c0d650b541d90081c0711300d400740c00049440320f0078400b007108450090f4001140c0307503940d00d500707400784101243c51030444845801c1c940d212040c40d94162584084c086000301 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 603120053 1250 603118803 603118847
    0x180f06120a15062603160c0b0307170c0a021b01031d071509060c020d020a0902070605040b10052d0a060302030108070b0a020307200406090e0606040510090507 70
    0x495403989900100454602a210f40c01c40c000f40711131a03561403003406644100b60000c0082c4001d14607100d070140701c1e1a104451071041e01e5510241c1000903041a1a00e0300000d0a0107240303600c003220709045580001c00030b40303080c3c40c0041e01c91010350707146114031003000e44a0030384008004603802075100750042203c9080090101c001078103400e4460200f8007a40c4900381c000c03880d403003d607407203500501c0540c7c259484210302c1c100f00e6020031140c8028548101d0f8850510000441d60390f0090002e820700f5845000049414140b502c0e1490400c40d0041c466003103201140c0d001c1010b0303514049925441c05a90000300841c0c07107141c00b00010b10800342606504209407010014480e40d255000b14122525242078541d42e94031041e030080c0074829801d140c07006034000d0000c0408100403103070207150b1514841c05003005400c11008a01902e115900650126960300440300340d40d0007e00026a0001003120208510b01d03094480c02070b481c200707008070241c055640d00065004c9000b10140006a40542c1c9810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 603121303 1250 603120053 603120083
    0x9130b040b0a0801060302100e01170402031c020616030e0d08060301110a200a0305071209080607020c18010e220204020f0c01380a030c0602010b180f06120a 69
    0xd0f01904c039904c400c901414001000c948c0d0940324908110010388160b441c0c0b50f0410080c020003032000070281050780d0600030301120040d081e20301058045c42c1c0901d0b402402003403030101515102801c10b03031740b40401d02d030408140742100d01c1c0c0811400d80d40c0b401401c0080060301ca80c4042401881c03030443d80c6030010780c001100020700d0740041502d078000100100b91598923010340c107038a0300c880c541100100452028002607000a60000c03020400c46198138004140da90f07130f59181d91070006d00380e41c08400341c1c0000321010300e03a060001c6c20807012041505c50010651402c0d00030300800400815034901c00c0303010a007036185403003402c612820322a0000d1007551608411402c884031a4091001c90061f9841e01010300d2918120242e04c20542d48400310030b2002c0961540c081d1081d601d400c0074130750b00215212001c0005071202c10000060f007050340c00050015200c40a20400c41d083c00b180b040b40e000440b04001003510083e10503070b8004026189080c100030040c0480b40340140380c040013010840c2d0086a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 603122553 1250 603121303 603121319
    0x1e0310061841340e0402030a020904060314010e0127140303010b1201080606100809010b0a03051624121d150703091a13050d020d120209130b040b0a 65
    0x101007051540215407001040d1100c103a03c440b01c00b842c1c4940820651a40001030785031aa0245900c62441680903160012420000c0c0864420760406c0700e5042d031702c40012a0849091180310307000754528000708083d1400003503161174598006000808180707000ca07203008001c40c0c0c0c1c001c0c5c00360390300b400126600d0b075031503405021321a002880812120700b603520000480740800601c03c1c5c09040080c1101d101400c007840c044a2a240c000d01441c925920f0300002c2c0c1203070300d500d0001802140140c0240c81d5400b080b07402003540605592203442170300d80c0c8001c8000c0340c800254052058080c1030600c0c5903144070814401d005070020306005c05203030040d20340c1a0076144010680d0850030900c801404101e030f54400c0164101e07041004040c201c0f0001801c400c202010b0714480315000a400030049594103910383c3d4080c0b402d644030341032000580040445680d4240c10000c1d40003480326440081d0300380100000400c10000400b40c01002c6e4940b00c201c0301100d5111544050210310000d0850a0403e4461070b00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 603123803 1250 603122553 603122581
    0x405011a18221a1603050408070b27010b040b01020106080607030905071a0a0306050a0b0706020f0d1107030206060a030201050d0b01030b0310090c0e060f1e0310061841 74
    0x71004484042e210051004c0303200b44117591203142c2c0052218140b00d0941c80da401f00303d000900d018203169101034500b501a03820b002c24800c0e003190314004034040d580b000c02e0100349c0300b0550246040d6030618805025124010030b41c4c80d4001c2c06031800184a0a150030014903001c0c45600030034048154001d0000c9034407040e8000d001c000203644091003029952400c2c01040d6a0a11444009400c28000c0e400001d4664001380b138060b0660100c075082c2043c0800c498115540a0900ca000c050005040010543c060082c580c0c40982107070b4503903580303186800280052049001810541e55a05429000e80c0c1c002d0303101c0180320002508407070303a0044051850004140b40318058540c122200c9002800400940d045841800094170803244440c0074400d1218412341a000102c02c0802c003500d454040d1810051114010b6110101082c1140b600c0350f44440d9201d000383e204402c50922070480b030700f07100d0010b201142c0c036901501d10b0020040009002850328031410071028078030841c0c003840300d00c0c07140040c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 603125053 1250 603123803 603123811
    0xd1404020306070212031303030e070609030b101d091923010213060c1e0b07080117210f4302040c03090602030405011a18221a 56
    0x1040311200e8444402c2070365074110f05c0501884002041000421308024000c15482d1140b0030b04003c9812034282c7c3c41c850401724150031503400a81c403454100300303000110502d190003400a4803c1203c8604001040501260415070728500a44a0700801c40b415410042c0c00c200d485c03400e00000e9511500e01d0150540a08007071018001a0901d680300540740b818803c0701e0946008139480c0d101149040400d5072070f0441c0c0d50b800e43d65035200c0d801c0c605040c0081140c0346030440c42060715400c68608044007a2000506070040300c449045007503118065440007540007840c04282e50341862140f812a001303403451195065480403610b0100d02205168503005540411a005d40402a0039580d5840c8180e11180603484038208000004450400741c00e25600a60102040e480c01003107540340c40c0c464034140d074130070307181281d41d80c2d958034010340c44519010010b0300ca008101e40c1441c0560211000303c00400028003602031044071701031252024800c150080300007a511159804030803032000358440c00084221 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 603126303 1250 603125053 603125059
    0x3030a0914010504240b011b05010b0604090b0901060504060518040b030a0c05180702031c0b1e0109060306080d08130f1b0602060f0106030209040e160f0e16080703020d140402 77
    0x803101201d031105038040c641b030b42c5806030740e80320b454110301d2410100e0000101041d40e65540e41c1072046c0454135183c0060029107500400442c1145003041482403040b41680030008001040c4801d201da25440310490300b0b03402c4149051412801a800081e000b0711560300059494458409241c042009040180c41190000c64001e0310717485a1401c20301c41c50a048440c40d005030010800b00000014101c0e401c0e8031034884250000d10136100c440400d1059212254156400892041ea0342c03441d81c1c056000350250005240602c03182e440c0c50045503640e0885080c100910641000040c0b400300c202c00407c441c81c0c0c01c0301c81000000100d0918a02d41c0c2c001010401484400050100e0380310300000f00e25001d921020001c401c16032078808110020741042d1032840e405a264880003c110204012a5076109541310b401300d41145404c1d900315419099510417810b05910004000805083c0c1d100e00f680c80c01541444d0000d87d8400c0c200314001d11540980c5049140b0742060740d01c00602048060b40708603c00d03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 603127553 1250 603126303 603126353
    0x191e020a030b040e06130201120b10030603110a18020a021005100e0f16030b03031317250308250c031a090a020f120f01021305100203030a0914010504 66
    0x14404071900e170f80c0115001c442c40c0080c0b415220041d407040c51154442aa50031002034940064400034407028103441c0841c001985400c020b000740b040110f030150302c034081190160520b61408074544400c0610b41401e4480350b0380490b03001001802400940d89100811004100d40d00d42809800e0307a14140f40544662600d41500040ca0620f07841120b80c011400c03404428852034140034203c01601040c1121078041c0000e200b00c5602000d50781454026111710381c1078001125902e841c5924040d00780320204c0b004540240700340c0038081c4154503401501c3d000007910740e54107021000d805110310b101914400d4008103030b0951052005c40f1580c2015039101d030101480c01013002000c1c80060105403010703c500e81260348224010300d00b40c1d82242c0c01d0b84c07000d4224840b8902c030607009410a18061540102a500007600400086e04206c0820152030b085800c418005440c5034000c0d9240401000400e00b030740c1d51540407003400360545503955581032600007400719160038984a610b011000410581d40c03261 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 603128803 1250 603127553 603127571
    0x1508060609040f261201050306070203090607110a08070902040e150319031b03020f0c090705031609050621010b0306060f0904142d191e020a030b04 65
    0x20504080c0540e4200245080350740441e140d1380c10800a207a0100c0075508850040840c02c000c3d103024200040c1400840c0f681985041c00f1301d410710340010300520854204001c154615a509400d03941e480c2d40100b0303082d170503824000c080350313032801280c110b2645445840c0c03001459100b00c1c0c00410580e03108128400132912540610341d181094254490f034141c000b220b01101c1300c00b0716030a00d110b0030701a107028030418500e00400030040c1107480c1c1c154016004000c201440450400607409485c0050714890b1151801e200000d08030f00000d003112001401982e02e1210203442500302e1005044024a0180d86215120401800c45d0340c102c030b003401400f08000002042402e4209503407240a001d00020b1903c00c510505084990040703000070350080e528000a0b01c08100030055500c01c03103001044421000d0712190801144144c41e040c02e141182810402c0007260b5400000c3c00d4840c166000810140d004440501c0c1c290101e8070b000c0380403440407d0301c203005580b50f0031011b00488291010440040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 603130053 1250 603128803 603128809
    0x7051209130b040609020315011407083109050f060103141b0408100b033f071a070f090e040b090a0605010b030601030b031b060a110115080606 63
    0x15003286035500400601c03410260318100c1c1c011042c0800e00510005500c0c0d00c0d040c420307040340c00035641720840d0070031707811542100e5030410401c94100340401909410041c5580c2e0f204090b22440401f41000364102c04a290a5600d09001030001492041140241a285d50b68038000301811994030420307010742404150154028401d2200301c940781141000b4079510000c8003619524001c26690801e5010040081d0144080c040c03e0b0707003140201404034100c4868000c02d4940207462045c1c0c0c042510003407025032610b004119401d604c026440e9110080e108032500a04640205400504020100d14024040d0200c0e02d000c54400c207100d451b051602501c0b07250880c0d0f409880d010301000c4103d608081004549800040c44d0300250030400c0f83c0341d012099442c44c0c281c0f4400c0c0c0c404050b0a1020003803001c15030f05402208001c58080d0010405843c40819074641d8104200a15015003000034044152a02ca0700e001c00d04008154028413440b404216902221140c070300c5200454090040410030902e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 603131303 1250 603130053 603130057
    0x14070f060518150606090a080105040b0f0c04060f20070806010602010903020c0f120706020106060323040b04020a09060e1f0b0409020a021c0e0a05010806061204140a08070512 77
    0x90700100101510788088102d0490142d0240c070703840c0c1c804170920411459681c0c1504900192002c82d00111b040d0600307203090401080080d2425501c2e0320a030041080c00190383c02918101c91851411f10480515400180c030704140c1a071028072b0701c0e1880801194085000208281190b00c00310491351300c0d80e41d400741203007241c05240300140181c1007484289420710b055501740000b40703001030a504500c2042010700f8500051175000d0340260b5103440f0704002030740d090711860760b01c14070310b4207036176020b01c1c00005000301031034020001085d007411403001c1000d54480390351650181c00604000c200c0c03071303481d40e6072002c00d0142200e12456407001702c0c1d14000c1a4000c2d46201086520040b10f1900b00741c14081c0000181d00300c078654504601c5402c44c420344180004c81001e0f5840d01d5034483c0c001400c6580c061000f00c10035034206605020b136010a000e0592210811907071032004100020b0b400340c646180c03100c1c0600030f800825115202e02406801800b1080000f0030006216404513003d5484405681c0414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 603132553 1250 603131303 603131341
    0x308060f0603040b160f20030d0222050d081903140a330501050a170a0c0e181302030106031a0f0906190c110d0306050a0803070f02040c14070f0605 65
    0x925050039083c1000704c6610103501168414140c07400e2812090270501203030000d408101d00d030380010100000b85140c0d0084c000c00b800080d40d000891841545a10840f40304485150800c058010714000c0340602c207a0080e04048145840c140050030f0000c100006046262880c00e20307030440d07800380c0074001b2a940c51201034100720580395031002d19000040d102ca4101c815507000384040036907550b22a5040420a9115408901c0c00140c58445000002c207510404100c0c18094080c0c44201103d03004e40c411400c1c3d10078404900008159036520209025014a61000302900f0608030751114183c0c400e5003151103048001464141543c0d101c50a55030380c5429550001030000c04030070000d0514080c0c014030a40c1840d070402400c0f02c2c0e02407401d90b180ca103004244c0702c002030303680200703004620b4002240340c01046004000c5041160544600040080c6208028810340e0f5a152420078140544000c100c01e4403031141641e07c5000342d04003a00c4030800d03824110b9800385444000341d260711a002c0f0348200 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 603133803 1250 603132553 603132557
    0x1030b070f02030c0d03060e06042a09080f030d0e03070b3c06030d090810091e0308010306060f03050d0f030e1f0605030303130308060f0603040b160f 66
    0x6161954a801e07901115060036070740840c0030800007085400c0d82003004002d07021181e900001c09a01d00308101290071000780000744201e080100881a4021204622640b00b084c00300d15140e9a5000c030080c2e4401c0c849620100c0d09004080d600c00801c0c8000c40940328008526030300388541c0d442c100000d6144d11544100a0160321094041200340c0841c61004842d10520030303100180d14100182c404030380c03010a5200c1401d403100d20400c1381078101071240e01001842030034028403d90803c8400c54807800505402e005465440942c00c040c080380b114410840030342d82824145000c010b0800030a0f603182408162981420134100040302014079681c01c0491360001d000e860300b02c11091080b12280b6640007000c040544038404000707001d10074842400c1410039540014018045031301c280e400e58207168800751103500107008115100c80c0c805c205800c035552501c0d00c252070781d5610000941240c20f510520390081000310801040091040d0801c0c011520159030004603a814101180d5240700d4004040c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 603135053 1250 603133803 603133823
    0x506070201020d0e0112110306031c1409040f022a06071d040b151206030708210408100e01140402010e0f18040c0312180b0309160b041404050103 64
    0x506a04c1002200500c3e101407504540f821000c1103a00c054905200340e20503125000024000c40745002c0241c0310f9068000000905c6140e00701d1000fa0443e6410011641d4165000901c18210b0f81c82d54009400261100021501c814000601d0522607072070f940c0108000351300c1e00c642d00c07020600048442c41601240c0d601200010144074860f209003043e10115003180c0c07120b138002e0041c0e6841462041483c80400d0640c0c0314801c10501d0941c405014000740d0003500540c106006240700400c050f108440f80ca5040b0000c04140c5d01e160303000d0721899210b000b29008a035528035182505410040d140e1000400078020380354180e40902d231030481034800078049050b41030300e0003190802074124240000010918000d4080d1603046030005081245d04884e40f008051301442004130f016001500c10100d031502081d05d01150391a80381d400100c0c0a400c0c443e540102c0055403000302000407110002c55010341c10803983d910030055407550000c3c05441e2420300c000c07205280c24102881413904803908602000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 603136303 1250 603135053 603135073
    0xf2a031303030e120310051210020903150f0f071701050114070602070f1403071e060b0628020d090b0d091a09061b121005030d08010f050607020102 65
    0x100c0d03511810411400c0c5a111010b148a000080c0710343d4000501d10192030341d591528440b1907810510303d402081c1b00d100c40c0d601c41440321b0000241254807040610005960381d0740760b00024540b5030041182002810356034100801400e00360780c1e0301e0240c802601400f00c6a00c903500f0079980b02c0004a144941414008010001503101d80c00c07034400d8030007003c0c10601e4070590b9100c0500740c0c0c0c0701090550b40000d082000000b08082074001d61000e19034040a5400e021003075031403080741c03110000e141029818808190084c0306881d03100e402c07404402010142c3c0c2d511524100602a0807600c94151002030190161148134004600d5180540082e96001242c83c203056607020641c0001003444c0d4490740d00e229140c00030701d15080300313101040780703585404d00e07480c0c2000150301d0300350001c06202013070901e901000c091307510400641d8446620001004c102d0750b6007549503014055264003490f03143c420805c003845107a40240300581a598240820659241c4500510045102c0c404001340140d220301106 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 603137553 1250 603136303 603136321
    0x30b070f0f121b020a26070b150603070c020a060f0c06050c0d0905030d0f020a0e0f360603071a030c0405030a06050702240a09030e090f2a03 62
    0x1044030a14040302c0080d030710660720001030301c05102c6014040540d000c0b00d204401d0200192040c8514040380411628030140e030307894500f86000d5404010718049911022030b180142070407071581e40e51000b800311070300c03072400000081c60520b035450b060b8080c00b00c400021813081e01c1901c83d0500715100b6200c1c440409a66031381ca0300104802400300b80c42100921440c0002200c07070159005003030042c402075840d0004000c44004461440c1a42c82a45104104011991f40c11904020702d50340115000c0f0613114101003c200b88000c0115942c080072410041c424140c030180351940d507440301c8524007501325a9054141951901c40d4003629818a80c0300f5000c1107080907400040d07a000c0d4100103111b040582e104046494030380c100c0400c41d2115112030402610725410820003050b00c3d03594003207080b0700c00000c0c000c4d00440030280c100c24009855009100515002c0e0744403130b4060001804802c03143c942851303000403810095403540311404808101c0550402801b518515820706850494510385414100c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 603138803 1250 603137553 603137567
    0x50a09030206150103020c010c0806011409030d030c030f2f1c2705030d1103060a050105030c0f0d05040210050c0303072d020c010f020a080301140f0d0c030b070f0f 72
    0x5044c1055002c10041004180a010b107819a01c1e0944600c0100d0800d5000909812105500c56018100920020105540000301045031040c40d0400007000d140300b802c100c01803c0600c3c0034426990514154200121040020130f9006001c42c0c0ca1982003003c0c115075001a00c1000c410400c0c02802e030b840481050080d03400030b0500d198080c0d0300c8581e0040303048401140c01c5401001e039059000442c3c0310b0300024042c0500c44400c02c0d2411094654a03000000420f21501401b8180c100800403000411100c1014103d550745038610a00035224020b0350b0010019000488080340518443c42601e04150b000d001921203041181c1c01031415552204d1382210394080013070082c2c004800c135201c40303424001c4040e034490141440f51701901281000310000341c41e001e404100130027154030000c402d0700807410b03800070340303040d0390021b081c5107514010a00014242c40e5030181680d880700c02003d032901040071031058441124420390003d0401d0381d50210603603202e440200f034200442e450502201000d4441c00c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 603140053 1250 603138803 603138841
    0x1e03170406120f18050c01174005030702100201050c0d0b0d060c03020a0e010504230a0b1204150b0a030803191803080906101806051009030303050a09030206 69
    0x290000d01c40b02d041243c241c009444802c2039450b500240c6013241b065a0000546407050310340c0045a003941030a4a0000050304044400400310b0041d80305111038222080004000003084c883c54183d280e5142403e60304c2c0e9008541c2248034000404d211032030240107014030307841926030180c2e080c1007070503240c000d0010381b04030701c0f6071980007100340c1b40d80001800724403d250320409503580040c0c4030300b0102c00c0a003600f2403507034403603052100900c020030005400d4010002071554801c00d034042450000081104001d45411104000c5008203210342030400381e10720a40714a01500d0029003a80c034500c031301001c84002c140129001115004140b0209140800540d0400f68240d01e8820681d0905047c03011619070031007a03072503503140b44402c50601d913100c103582e50040f0406d005081282000809030201082c0c511813450300391261440089066401e03070200000f4030015000c070b000103920b540003e0100306580800ca001c01d00d0180414140010b91040d540110b50580090a81d0348038040c402c401c1d214007031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 603141303 1250 603140053 603140081
    0x702031c11041e0504021605060702120306061e160312180f151103150f0a0314030d0e010617010e0c240706020723060f0c041e0317040612 61
    0xc10000b801d0312544010700787c500d65101d64110000b190b240480c2001c10240c0010210740c81403d02a800900c004101c1303410900413203c666848880c030003a21500311124040c40c004020101d450b0640074010304641512520036a41e0b0010450320700b4100302102c0d0700705840140940c00a82040001e01e840f10381d40c0c907141c0101c404401c136280d804000d206607907006806c4800c460001c018460008d02d8040340c408030103000c60700c000c000103484001c04c01c0320710540b20282142c2c0c1d0f00c18100354250740a201320f0f043c40e040c1c40c20900840150200382800b03803015200b5410390341c1d0a01802069428103109400b000300d072041c09800042e02001c1042074030303006500c080d0002038000b0600d501d40c1d03041100a107142e900c600030144e200c01090078038184210701d03060080d0b20b40540d024800040c0e035011804651051340840f084074a901c40c41100840341c05544c01030340107070b08100b0120002041c200139840449101d03020000b9242480e812500c003c2c09180708075004140212400f1804980f10303004041d581343c0b06 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 603142553 1250 603141303 603141359
    0x903030a09080f030a0c021002070213020a030905060403030c0212070f03081f06110606060712140910021f020f1b0a120504030605060312040b160b0702031c1104 71
    0x1043c40c196070082e9441c10074242d481c0c0b224040f06406020310803052482d0030085007004100d0b000f107110841d01c0b80e00d1890b4036500144404140e402544004811504031044494515103407401500030a480ca5101025110f41410091a410398804a41282d0b600a200049003207141d501610284400303410750860b5003d9903c80d002d0703000303025040c41c01071905030750301030307454884800540c04c049006e00114019601081604007149151420052403080f91034250030002250761251014080c0e81500d0341d03c40001c4c2d030034580d10740d800900f91084420324030009101d9001c0a01e80c1089208068500b04000f000748109581c83d80780b855013218001d19030081e030301c0041e0b0b42d41c1d49004261501d00c012020a102040034010b2002c54814103070311a0040d00108420020210b492000d80100e00c244120070344005100400f106448140d200920751249501e40d5600342010b000e512030b04603005101c410680d0000c403509005880c02840114449402000c1c0380908001c0040c230b104264a40e814481d110b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 603143803 1250 603142553 603142567
    0x6010c050d02101107020a0b0307050405220e0a260702130510060906090b0f070c091e05040b0112022701060f0201092a08010e0c01090e0903030a0908 66
    0x184000d03000006540e000d4039281c0b83c01034120049640d07101100c14484024851200180c0b0741520700e00c01d03a9980d188c443c0e202d03600c0d5036003103420b481160001030f04645041241d0540000320000034090301094101400100120b0301c505035251101400500105405544601c5043c01007038050039000c5400c089602d440b002d034008c00d00c4003000010707004107595107404101e17084840d001f048000d401c80b0703c1c00100c0c4c140340400003000d1800c1802081c10840d0002101c0408009200846072010f9203c140c0c0364000e9511170070381c801080d904045c803801c5041c4801c21604401680704217031107641d03c07408550443e402d241c0603c00c03005103001e0807a0800c070030402e032008869400c02c032050301c0a0100c3c030f2006a0f40c1021402000300c040702100c003080d0781c105001e100000d2007082d00d40780d81075611410844042c00000018500c04883e500820300365107840c0400e6091b090214000f03800503c280c0b06c0f102c0050783c4894030303280c9640803036096000d1741061001c90328107107180d0802c0c10054000c508107428004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 603145053 1250 603143803 603143813
    0x123060102150c1206100c2d0308040b0121060506062106030d0c030f120f060803040914010b04120507051e041413150e0d05030901060e1306020306010c 67
    0x1029102c20003c0035022411206a01c1e5454109900c9901520103c03144c40001c3c4000c0c1c0090715682c030080950f51111413190205041e0101d12038414081069540c034109541030140410301c041d0f07419034075441074400105122881c94000e1181001407586440c0146d2030707444000082501070a1168003040420250a00e21002d4180310840c44558002c00c1049c18250704052500120700054428001d80c10402c0c00444c1c0c02c490013050042d000d0030403071500a4404a504003e205011800c5100c07841c0680200312800004090700c1940d001050401c0360744002c0c405603000c2c510920415450701c0007007000380100190807202c1c2c0515481442141c1a031074036200064036040643c0e903403290181090b040c8000f54945809007514950920840301c4203814a059007044030b48100002a0101c024407040c207141f80700c940c0c005000c0e0282e00c001c2e107024562a007070082c1260300689010030f10b0760805202044110811032039501881c82406041e42d40c0881c0d03645c0f000a504000d14076418402c40d504084017180d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 603146303 1250 603145053 603145093
    0x160905090a0209042003010b18040212030c010b0913020919020715021206010e0f0f01200313060504060206010e090102070c08030306030114010b0304081309020c0a03110123060102 79
    0x26225504049500c0d608101711101036104500d481d100b6814040826503039183c03685100301340304280b81e0101880d41c680c008240d5124624080600c14400087d2014101606503c480f00840084074012010781b510400c82c4c0c0c40f0303a142c0e0301c040c0d48803141001040c0105903561502001c0b072092034015080c008980c461042d22a8060303201d0942d25000101c1071503844100c5d900c2684034400b405c003248102d00090100d000010302130801806203080d440300c01003581c0034007041e1501c0c002134400c1042100340319001c243c50390403015400068810b521800302e11b4601480c182c0381941c0c5698020000c981c40c00000403040c10000e408039540d95420000000400d00c0c521450001c7d01f2200000c43e56400c004080c5821034144000c2c03261881d00310401030103080e03002030499400075004880079441e84884841c4c0340c140445a40865801440050220706649020507201d50781d5009450f4081c0c680282c04041d03003038030108651045c1c20602d64100c06442c1c000f204285030003a8040c370480d00210f0410340d10790400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 603147553 1250 603146303 603146311
    0x1f08120901030b06120c0901031811151c051005030109030c11030129060412050d030f020f0334083c0714030a020703030509160905090a0209 62
    0x4000d02156018022541481e805513000c41c0b91001d410282c00c0400e4002d002602070362000200e020907684a40c100303480b10754003808440c210f01c800349454a40c080c42200c41502403050055861051503007034060303130000c0c00010a2900301c041e20319044002001c2c01010301a458218440125407a10244a1601c220b84a902c514400d804e4600b003d400868403a0a200d202ea030410481c043c4003403c1420b2417a4a07082c64a1501c07a0050100c0011068001c0c0d40041d030a5014242070181400400510070001044503103080040c1b076001c1c419081688540041445040c1d0104007240d40d424086000c4006c1039081c44486c4a5025a0030365a110050304040c000f0005010758288510005060f400345a1204100d09a050424081c50003c00078051842c54640003c00080043c94242c01a64058201540c418205907680780010307910000b500201c03416800646080001900100c00140c07415508288030b0201d01c0703035441d01ca58400a03100040000c000b600881d18074500580b104060f103030103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 603148803 1250 603147553 603147583
    0x6040308041d090115091806090b0a0b010903021c0507170706090f0f05090901020c030301060c050d020c0109120614040c030210081302060c010212090618030301030b1f08 75
    0x3426070110050508540107000f00c0310591510382206000b410303920007041110294807021820f0041980e41c1c89a1103908200a00910b08010f1b9007010046480b1110b44a000749440c1042102c8062004540d1b40c1c0050100a4021907034100e03034030401041c100c1e0000e0280c172400481d188541c42d501c0035484599540d80284803580021024040b00d604041030b080030345100d03218502101d107040c43ca40c061226600c1b036103004141000c04039003000429012501d4190b607804c100c1e943ca5940d050020056006c0060a41e940e000c0d160751070170324510104071903140c00016904c0c500000d023000795071807011100d0303001112003960b00c09030940e80c201504046803007503000e450401401440d5006021082039400004410410600100010544d4104008080d1a01540c00b50385528024460078024481c003003185501541d407400300a901c50300000e0301403140a520b550141c0c00720f43e2041842d501c1c00280001000c029207400000e030340c1f1199048200c808c0d0400b01c10b00440b980e980d640c07c0e017001c0e850100442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 603150053 1250 603148803 603148829
    0xc091a030d020115090213060c020d120909050f060a06110f0a0b161e260a05090129120114090d0806010e030c040e010b0a08070e0604091e020604030804 67
    0x104480141044c00102510803083d454181d410b4060441040e09005103018001100d45142c00e64580b4450000c00961192060100384c040840c05442c0003254452814a03038100030000b150304105841d031900401c1c002c0d10082000781000340654003c00d06003090703c43c6204200290034151410005042418022603030001c182c182200c00d074410812000440e014440ca0030a9a410f448082c40d000c40c0145441c039050440c00d03000500f5440b08001036030078403001c040003c1400394804559202a0144041c6402000542500360301c0584d80c41c0d0140c50501008600c3d1078100701400e2420756194030407400c40c00002d4104102140500801742500c40c001c8542c800070a40c00510303005003840390400700900b0002c0c1d070803a00a0021f941d40c1c421a506a000b0780e16901e0744807038030303509400c00307442600003c0402d29520b40b40c030f1105603110414800d110a28484101144031410f0034410340700ba8a4000354403000e442c12001024031103c24180301280c0100d010400000411400800341015080001c9040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 603151303 1250 603150053 603150071
    0x151911010e0102040312051c020a03050a0e070605090607080c1f0e013305040c0509031006060e1c02040906050105100215070e040b15070302190c091a030d0201 70
    0x80d08440049901080030707031040106101007203500410f4882d061840c540140c0d1140300d524640113903605094a43c51040c000b003110b04120350540c000364844e401d00002001681c0c601c0d15220f0380c0320a540b2410000c10f8003000305020780d003050030081c02a40d019001d9a450b0100814609142521001600384600f508145d4001c4400b201d009943d0781e1005000244440141c8841020080c0701500d084000f8032003007400c0076031b080001c00006005201c010010020450305407006040341c3d02c2032045a10a022781c0d04444c0e0b80c800c03241300b0503040d184182d407050030301c0c581101440744888661000715102e00c01005214010780c0c65004032124103200300804a82d035413500052210003026544c844040d500811100d085050f288503440750f1008c0c0310f1510021410406004c50020220703164607541000800c00f4002500c07013200010801c0790721907421208039402203650220000e00c605801052444907040411480c3c1441e0081a0100c01c80d468483c41c4c0b050a0002a19000c5c81c80b4030240541d44440c0c2070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 603152553 1250 603151303 603151337
    0x306090705130b0907030f09021801150908030a0302090a08060403091d0f0f130b04120e01050703020705130f0e06040c090903020604020d080408070602031312020d021519 75
    0x800150042500c0070303c0101c2801c40000d40782000180380c0c0040603510384000c076040e02c0d65000300b180203401504200e40d19200103141881c00c4024050b0080d0045050703180c001c550301c289141000c81d07003180c01550170700802c0102100658041c054043d03112810080c041a10076060003498003885c480d8499600ea54504400e695074040c1e40e051202091100908201c0c101c41d084e41d455601107072410030a0714541c1c40071028078080902c2000901604c120404110800c08402490b9180400540b12070141c14003450045940e8890000000e006800490080140b030901c4a0001c3d00f5804440e0081800d101640b400c130102c99003c090310f0b07855031041081c0024840040c001c0c40240011041c140182011920080d58404001d0402030003200701004500a0090b00802e40f0007500e01a401d80303072416900c00000b960382c1c000f0380c14051003c0701d005d0002015046000c1000d09603601030007034400100c13640c0030013810448440b841c42038560100007441680d08145002c42c420f0701592500819030200d4050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 603153803 1250 603152553 603152569
    0x10e030f280c08010f0c0e01080a0914011a04060f030503070f0503040e040609202404030b070810080c0120070f060306030317131502090904060605120703210c020306090705 76
    0xe0018041d51507451f04030b03641d01001040d4400e070f50382008070305001c440c40c2c01e121458492803d02042d518258030100443c07200700681d109000101d0702840002e1311181c824540500b5840003c1c51548100002800079013030814051105001b101601d04140e9544034021030141c04480480305141e8800c180d03810404007202d2000b642d244203280c90003041c014000b007411a030b14140c6411120083ea010201034450510842c0e02459200810080c64240b404001d0b01c0350000b40c580c0400403030842c0002c030300888005400150b41d90142d50707442c011800140d0241c2030f1103041c10b030f400d25405090004140e540c9002c80500c01001540e800080952030340c103000301201243d5401c1c058120404042c40078110800303040107205d94001e24491411104048081c000b1710503852000c1c0c210280700200410b0104550000b412610240c0f5019a4440c845d0307030443d10f9820501000f80038041c02e10503c000440c014002e03150075075007030a0003d40b55000717800091604408032901065903004000a014905011710 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 603155053 1250 603153803 603153821
    0x13061508071124150a18021e12090c4221090c04050c0d2c0f06010618030507081c020a03081b1209070302010e030f280c08010f 56
    0x902c83c1036801300000189000310b10703110700c4204641d071641c414031036842a41140d40b1a812840c0d44070002e10035082d542e0103a0064000c42c030b4081340d2040001e030703821408182c1341c1c403844009003120011802d1000c4840d0a140b0a055060010084400351a0b40c0c00115030200842540840c3c0a4a8000c801c074203000c0d20107449542c3d0311082c06c0d2028850711920006190082c56001c0b01c0100e200d66580500d20300c030f40521056410342c075040c0341410030140c2040d0050206541e0b07585400e00f46103030307202c150b079a6035403040322003405a40101c0040090724450443c4008076443e14a00f80b41d02035590b05c4031442c0c11403542110307495820074069032043c461280070003042455140060301c142005501c000d0301c00b140040c002c030740b8690f1146a00f20a99040c070200c80c04049511502c14841c1400f040c2075a98004a020481c08255400c0d64144103190020701d002420303005100034001c01c44102c1404440c044441c5240c14040c0070b0090000018220b07200702c40140c680c00703000146200c1c11020800c240c404c1c0c89 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 603156303 1250 603155053 603155071
    0x5010501060f12050a0e0703060c0201150b0d0b0109050607060605090610140a0c1e0506062211070206221d010e1b1813061508071124 59
    0x1149400c40e280c2c003e0030700c5504250f1590001010350f0b40f20707100c00142c6021035a810b001c0c002e801010080200301d920040c11111654000c21000c01c001d030f9801e89005080c050341c02c80710000c4c0604090080e454001030b0408006140807680c040e40c600100f00d0715003107178008413800e544840b400d000d0782c05d000e40713403943c00182103600d88440c8420810107400e014241c541044c1041c4001900d0000c14001c1100b40112030380a140524400044041100038041060f011211401840e000c10494944600255003001344034012000c41c000d144e00f614020300c0c420f00c0808101c00705218000240e60303840c003d003403001210014040300d00031150030f00a105505400c01c1c4600030f199012180e4104c540d060442c1900c110450355101c2da1036011890802c0107014440b400750910000c0c0103c00b04040348140070001e0310a0b41d04d4580a500d02400d081680c5a50150740e084410419600c15098400c00346c2d80c0d00701714a4100080000032190045081114070b0140000000c3c080d50400e20038050301d020154081c00c4c071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 603157553 1250 603156303 603156317
    0x1150e1506190306080d0804050d020a0c061b060213031509050a030e0d0c08030c1e3301030c0e0a0216080c0708070906150807020a0305030c040806040f0501050106 72
    0x60016100d405003400009075201030680b041e01c0a4043d6100102610340c07041210301c0e91140b00c5000301015412134085a89024412501c068580000764070b0504940c0544600e401c1e9041c5841100c40800d0100790b611250b455409180c04510305100400001c42c030401c40380c2c0a142941403041c2d12007003800244c212185045c4040700400c03400f050035041d030b66141c9841d5a203200528000341074071280c80c00192210074086030010b40c0c1c402c00401004650390748019100780442d041c13055407201655202041682c1c01541d48420100e111320065020034400c2250446042081a400c51150009804c1100d107048000b20522030a0303140124142c0c031001c0f1903000e501d084c143e01d0403603642c580706030f038000d0211001080001301d00c070702070000d48050580d5108440b01a0b40e15007078800a01410b214010404807800c610082c20340c419448184900344030b80041c00300482e075170b80032925544010181c0903458030178003005c1599403007442294007590207402103619021040c20440c1c21130748182e00440500c03240d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 603158803 1250 603157553 603157591
    0x60c27080d080c0706020310180b04151a092d0103050a06031e02210a1b0e010b070303020f0403061a04200f0403060e030a080903180f01020f01150e 65
    0x5000f0485005540c40345016890791190840000b000328250016940d144060b04550070680581d444190282c1c012a42030210261030f100019250030300f40900f03411250104841c18006100d20001c01750440c024250400b0300c42c1d64501001d040303003024a43c001520000701031034540d69042c007903560015070100007008010711316520f158043c03411503600c9003d143e041e0b07910781c255540c0400d1111100c824462a00000a20720300c0b0644a80111604445843d6040d0000c0f245405d13139001c00c01610407100341c5030070a90a100c00114541c0003100e00f20201602000002d0048260401070030095100b900042000030401301c07001030401d46c140d581ca00035843c1c050003d40252a10400d10100d000c001c0c03101e0340d40c00913030354500c20a110b6504044c24850034440c00b1a000d030400002001c2c2c0ca0429550340b0059100d241141d81c5901c18528554080e00340c12004103960728040754901d40807803050046620725450030310100d003562841a02d0440003058520104445500002225072208404c441001e555038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 603160053 1250 603158803 603158821
    0x8041a04290c04050d060f051303021b010804030c05030f12060405060315160c02031204051c03080c090102150106210e070b1303080c011a030d020604060c27080d08 72
    0x289100d458445c40411440034103025166120141e6400c1c01c51040c03015144c120030100c00e14404c044100c0044c4120404100000380d080c80300211100d05a4601000ea2100d84049852000300c54003940d2600040040d04020580e89004108640342030503004e88918200c000c102c1201c40c01803a881c065041181041c060783c4030401c00030740c4a21000c0030011900c0e00400100c441811034240290103128010885a003450305030044e1084038001c4070881e80712002c0d0030800c580c128403160004c001c1561540030940003540440500b8040c0303c10b2048800540c85900c0c6c281440d50f0a0b842000824403480080d00010300032900c19003850384588060040c0020070030003541d91440c1c1d11658902d240017055000c1060307800c2903c20003c64001c1c80880e290034000c0400c600030198080300022112840313176081101e0038045000c4a201010313030040d060079655622403001502404220904000c0e461410f184901494840003c0031541d403a04120b4050a050343c0c0c1d841e1401c808200800d0050070400c100a100c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 603161303 1250 603160053 603160057
    0x90a06060b03161101090501061e051804110103021908010e010902040303021504020319111908100e032a12030105030706030c05070f03080f061005090108041a04290c 73
    0x4181c51600c1312840c80c1c95010340d401400e221000a04550070a180002c4070646115a112190080f0640c010340581d940c04000c03e40746101203202649540000041c0403951041e0300e08040c0da0103040140c905030a00038086d0f40c107045040b401020400000050203007402002240f23000d0105c01c0011880d0a046403000b03952180400c0c2c480b440c800e100c1d00098110349090005070306404412102d6140e0030351380d1401c07501402140006a0140c0202c1ca99062484801e040020032150048040d11416203558803202c0a0b11b0301c2031840301d9038481044038103184004441490700c2030310311140311607154000040d0b15042a5040a00ca03000f9030081c801804141d4010480342c1c1201c440741070001c0e0390b01e12001c1c191003070300501d400640500e20309035802d03003810307000b5950503c6041d11a500800981c0c60104004484050800d0b020001d10144850040755005040241c1c00c035000341c8044402401c0d00240f0702001c0c3c02114204c982d100821a60300d2500181c42031002e0180011440700762914299660011038 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 603162553 1250 603161303 603161341
    0xa03060b0d08070f03020f010b0a052709031909050108071229090c030115050a090b030f0601021c080606090415090e0618030d0f0b030d0306150201020f03010509041a090a06060b03 79
    0x1a042006681c10000c03001d848204080033341c641d43c85c515107091070301d0796100d0300210b2031f12a1403420301150310390040c0b080000e5002e4501c16141c1d100300d0b450b010350442c0c120305d039681c030300b11019610011540c54400405904806160b19894055444460f0050001250015000c1c17800c925003071005109150000300760000305d10b118500540c94102414084402201540c004e071041c95000080c484181c103440d494510826080e0200c07441c00c0c00c04155008074414a01030b001c00604100049419031030071000418080700010404152a0014688034240400640c014503a45640780038040d900c44c8103002c0c040e40040c0001080d140e01804803034403912403040081c071003e41951a1108540640c941c0e100d00125100501107600f00d010509020300201a0780c0034081c404202100a070102d03a205000311030071904148080f03810359181c60103005503210040c004846403421303000c101a0000d10900361900c01d074025001050300c41880c1c02d11408403111a005009941010820410052843c20502e288 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 603163803 1250 603162553 603162559
    0x7020d0605090a08191e09050f01050d0f050a050603061311060d05190e0c24090d08120105040e0a1b050a0801061508060a03060b0d08070f03020f010b0a05 68
    0x100c2d56008241414070660070002859100e020807110000e07080150041042c80f0551900540d07451030100501814129401c1b51000640101d404d00c000d003412410b1f0103c030782d8181400d43c20a8000280031094030000c0b0821a2803954682c20000301000d40d0060700d2300701030305401400242c144003400b241080c40e140070107006a490501c1020594544501700c500c64264000100440d003009000c0303a00e140c0003a40356120140c104036041500307060104207402441340c020110b0030394485400703002c07424448032450000014403c4c891301c00c42e80c0703401810031030040c030410182c1d5880c1c01404001440e4001a082903002da480e00c814036602420000e128080a03270840c00c0c0641c0001c0b00340744c1e250340d088650402500400780520008092005410460960305072200d0140e101d940004211004003040315501d0384332007054010004140660f000040c46000039010110b60081c50700c8003039465101c14802c07500c6203106003840b000e065040c410200880c000d14021710a00ac600b80c0001c500b04410f0044500c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 603165053 1250 603163803 603163811
    0xc040606080a1512031106160c111206010806011d01030c0303050904060b04060c11040e060f09011404081801020a0b01050f0319030201020915190509040b0d0c05040605010507020d06 80
    0x3401074100070b11100509000204104083c07481c54020003080c40d82e06d141c2024410704001c03070480f00165079645c0c102d003090b50314000003008030740312001c2d50000c80c03060b6604419440700c40a804001030224901a1503400e000780043d5140c0210a60a00c208104521101d00700000600c0042c50b03802c0400c08032901b40c5000c075182c84e00e6200240003404a42e0010491040000d00004d03101d0f0465228500180113905501d4003191b58811f000940d1484000c40a1a801000004400c0710013141c405030004d41131000040c5c44526201412060b0f081940c2c151f803d401c02280116641c0d0400304444103d803000c1c40074103000300f060350301e030390440d00c0601486118105e60b40b03a0a02c191010001c20800100c02c2e08004c1e103107407135030030b0281c001e6000c100028010324001d03100500d85403503401202c8101031168441521040c8100040b240e5410031021264002c0d100c0c0d408004070f60321080138210300b500078007400003054648010407084905551016050003020702540d40507a941e024040180c07900645c01203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 603166303 1250 603165053 603165071
    0x10e0612030c030f0d0f09061d030909042a060801050a150c170f07080c0607110a0201030b01030b030f0115090603081909051c05070509040b0411060d0609020c0c040606080a 76
    0xe0015601500344191901d0145000c1c05855000200c4403270031280303200d03035195442c1d41c480c1e10703407003106021600b003100b10780030900103a075611000d120b400b44040c541c4103800c1d1603a035500d10003207170380e005000248aa5005000501d4050b1026009151040000c640c1c2c14602c0c10140a243c104280a4069042c0c8190744401100841c101c50a18640e481c1d0655107a940c0d250814081d00001c1c0404100c1c424200010103140c02100c07004403410020006058081142d030044010f414881440b030304140e204c002d05a01c54600700810402c00002800110b10010030350000e00044407030340d106096070340c03c0c94002c2000c00e400b0012103e03400d40d0a060442462080c0c8070a952480c0c4a6004a030000b960401c01e520300c1c903508426040070303072050703082e201e217250f444040202000707040d070b00034100b11014004580000e030800b4008220040180109080c184001e50010450b012540403904182d0000781d860311800b0244800207607064101d030204105410500d0017450b01d4001000050855a9002c0d08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 603167553 1250 603166303 603166327
    0x11100c11031e070906120302070905040501061d09060702190b0c0906030c12010b07020109180b030f0f061b040605130918150603051216050105010e0612030c030f 71
    0x10340548481070030141941072a00070301943e4580342c0c8a85141580f502c00086403072045629020042509540145076180c144003180c0c0c003c01018104945640d03036600b0010701240f04a0641c40a44c401007282080f03807078044006424048028540002c5400010000301003c0e00c0c46410b40e030154211001c26690750310001c1401c0603200c0c03003403916840000401000030b891080340061408001210080e8210303680c94206220900403170000030b010458400090081c0342c058040c4443d884204600490f240c55400003180c200320070503103c10180c0e088041d1039080d00b8010040300f900b080c480d0074422000c843c0c1250800c2d0074081c44c01640d00f080f0000451400304044444040090807000030100304104c0141c45e0480305038070810084032070001043d5440d019040e00d225000440303030040c1c042e0980300010300c050b910039484650092084440d900001011400c00d00c43d03507000e88100c118550441c00d00100700004c442ca6072144031030702c0c0d0041040005208002c002d5401c007403044200c45443e80940c0042c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 603168803 1250 603167553 603167563
    0x6041e0c09050f01030212010b0f01050a17010e15010e131805121206060c0a1101120f0903140a1b1401050703051504020f0403151407050711100c1103 66
    0x22540741107051000348003800c07072601080f84c102c9108036040c0c40c034103420b00c201c9400d0b43c0100c108264004044c0c440340505500840c01004841590f02d00001007100700002c5210401007038015550003010b080811032803140401c40100c8215003402c10601c0140c41000064111841c1004084801d840f04c0000e02d07050018450390000c0f55101c0e041c0d07070300c0141c45420780800c1c0d00001c3d100c0c164152000042100c42c14030b4011605100d42c0c41019004408040c2c03070303d00b82100302000e01030400451104189801c05103228504014014080201d0161111708004100c01342120140420200405c584074601c0d0b0000300b103860080c074050b142c02d80d8802034208800d10090244100225508250810005e2039041c1d10140c4114840c410a404103100e40c400c0c04200d0080075241c100c0050300300014400300f59078069603c0180c800380c602140c180880010290f05510941e4050040b500102e200783c100a18100407900c0766200355646188102c83c900c004283c145564406080102410176404c40c640301441 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 603170053 1250 603168803 603168809
    0xc030c0a052503050c01140d021303170f04090b01051209160602070f03060f0b03031216080408030624300c1b0a0f06021b06041e0c 58
    0x1050320300100a03820450384615203446409441c0240500814280142c0c0c0340c0c500580e034100e130041ca154502d5038010744105607088078002881800788440983d402c0540010158028048082c1a660381b6602c0d08003442900ba42c0395504000003804403040050085c1c054500319000018046907200304900165080d110b0514010700707208810701041010040000c03d10b102c0e52070020300941e02603039a00e080b03803606454002c072041d0305c1e00170804101145c03098000326905a0042e000041041c1d4010000f4655404030516080344452074042220398100c03060301d803680c0d81032814608401d1805603510021131100400081c0b16914040720002c02035040c110041783d1b96a1880560b40e83d43c20030254003d0310342c9141441091044e40300c00400a0683c00a0681c00342040c40302160411a4003400030b000008400d01c02d15191041c3e03081000840d115043c4d540142c0d00420005a9900e0402d24a221452848000001680c03006080c48002500c900200b0702030a10201140d040e03810a14168403508441d174 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 603171303 1250 603170053 603170077
    0x61401181820090c0301050f0d0c1e05030d08160507031107090914060c0702061c09060506030c01180e041a0c0d05090a030f030506060903010501030b010e061801050d060f0e0d030e0318060c03 84
    0x2e0000c1032f020202e98a59026948120129400c800344004201c0705964112041a0f640d070140342000d084a0051000d030616034440e0515441030380c0030000703e51502405a01030b280c0e5079180c181180c14004a1406158080d403e503001e854580380201d0364810a118020009002e0074000940400c01071310a0004031f0031400e80340042c400c544613414000080d00e0700343d8156100c0d00855070b51010942c02600f03529801d0a024041e110100d01c0d0141400941303000030300170b542180740d500145042d244a00f840c60300c81e110890605c1d444840020002c4126017000b445600301c0d46c0b0207150200030a420090506103150940782c0864103650b4600400d003180144060503815600300310003c020001030940d1381d4180c2e0030b6085115255074429040200c1900d402c0116200f6038043c42c01800780d4202846203014241c094440030640002e206150380448480c9100c02c40380342c104005000b039182d07050144040e0403502c1c8000314207100c482e5000b00020703100240800c0c03007403100148400e0104002c0c02946c42e4009a0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 603172553 1250 603171303 603171329
    0xc06030a0e123601051809090c04240e07170403081b040308030a051f03030801050f15030c090d0f060b01080711101e06080703061401181820090c0301050f0d0c 70
    0x8c1030b101c541e070300745916484e0b200b541000d1006109890b41c4204500586c45d00003076054481ca40006400a2a8041c100030204030a1b10030a410812032a21554011807280d5240c000c13918020b902442c40303145c01d0141c0501c4c82e00400040005c180040709880d08001072603c00500d64940d6800030030020b6148055900301516517100000f0326420800da14100c803000d5400380d455208071000c120880c0034800381c6030007809080c004a0b0030803000b4006000c0000c00a081c0d641c403014507840702c82c10314215620031900f581d20799003d0559540d11107011038109105081000101c817800c080c031a1030b110f604c3c502c00405a0f60311203035100300b012041e0040f059103000c8010808151a50b0599407280581d010589010382420201c8451000c40c10042c1e04a4a040d045022100c02c4011351801902494056503d4200c0c90744010012903011881e0501c8901c0282090031502e10050900801541c000d1080702c1c154000d0004000544404a68442c542c0c82210500740c1c13005145000c00f80543c15802c981014080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 603173803 1250 603172553 603172561
    0x4090c060201020a11070b070b042f01031407050a14070b0103110316030b2e090203431205070302030a060e07020c06030a0e123601051809 61
    0x660040c401449160b482201858171408110780e141070320302c5103807007506082101c20302040f01e42c6150327900180301c1c02d4000380c00e070142e500010111070081340341150080004451011581c040c0b00c0c003c5c4a604000c160b031003a1500c4040607000d4002d81464406000041e9801c0d070f0240c0c00300d4100c0d1704241d0300c40b01c104525616401d010745410310343c082c214000e21449680c1140d8406205040084070350041c44000c0b155a020001140d400c4103501d81a5481428080300031100100c8081401800700d0803001030302d070314246900c0d403882628500f600782c1c1e180b070054041004c3c1900c0b40c0c45d008004804034801c40c2c5107260150840e0520840c20b4120915403805c01804104c95058000b5801051041404d02410b85c8031021103003450340680716070b00541e200f042610150b080001c0555442102c2220000340110081c140908110b03540c00b0f00d04641c3e034000b0391a120743c90708007d070a0004048106503543c05c1ca40c40b08203002011103102e224188000441c2c10801c141060a4002a580000c4c0c000e5015040c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 603175053 1250 603173803 603173807
    0x70c0b09060f0606040e15060c0a050a0b0c0c060a05150a060c05100c02060a050705090312120c071203021309090809030706020303060a03080d023c041404020904090c06 74
    0x7015504840010070720780c0450303c2450501e0070344040e41c00030102810a500c480012071030101182c2c203a1504044140616620340300148070030301c2840c1c0290050003c403075862410803a0080010861036145105000314984880c001540c603038000008000042c070303601d40040401540307220110956000715425808100158400c1c110784100d4490b42c200c4020b4020b40307040006035000392240c100107038001d40004411000c0c60300015002179650400c5880e0410380c0001c80d04150040d10a82035000740041c1c03600d40703d0b00e458100c0382d100c0c005074420ba050054540c2c3e9000c095603801c141404251b004640b18503407280c107401110081a0000d020000c100191801000640003e1b49061190081240007c2e0840c004401c4910555004010800b4142940c1d6414501d42085083d103080643c01d10000f980c408851305e03481404945081c0f6040c90945d2034075080e20038500f0000d07948100000740010092401d0100100110750b80440e80982c50365940004038009000b5520003401400c00f8800000310304d9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 603176303 1250 603175053 603175063
    0x40e10090c0206250e090705090a080714101103070c0302180f070f03110a020319020c0303070209061306031b05010206011a1b030301090c03061401080a05070c0b09 72
    0x1845484140640010948160f880350340443e002401200421081561540546240c0780d00c8103242c107003441403103020340125540181c1100c1c520081440024190075520380310004800a04100c0001c0000b00e0070100c110360320340000d1440a004400020b41d060045000b03880320842410b040c4222504c8204d107042c8640f403c1a075200581c0504010890380188141d03810503039105400c0804100141d8459003c02c076080808052240f040540c1c4942d48079449961038018503006109a00840d1a0050f0300398121004002c0c5230703103100750b40c044030038446c0e952000301c1602c0d07440d42c0444141000750345031004509944a90041055242c1c503182c000310800c48144180b0001c440b440c4140b00c0d01c2a124801a6903c100a00070403e40480c800698070390905080018001040d43e2440483c04101c03109070a8659003081c2c20403000141c6400180c2c0d0343d00c0c0d0503c9820000e085d001c61010549120790f0010301849000307401980a1600d400002c1d21690050b440b08a01981c002c01060503443c00751f840c03546071 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 603177553 1250 603176303 603176309
    0x80a03060e0105240c1f0608120c0706080408220e090c01020a06020304060207020d03170a111c021c0b120105010501210b060307120f151406040e10 65
    0x5007819200114040c1820a50520303100154030b220001c000150706076040c0fa400012041d40c9511601041400070580c4280b5503d00c249285804180281003454407414403000c001d051444400500c4030402c44075001600400310780c541e04003102241c580e0b0030900310501c1580ca007081c0541074081c210028030501c030755403030031a04000059100c60f10307031450158496220590740350041c3c0c0040000001b2520030750045030441d128403001450425654007040303001d40800c50940c04a58401c50002c48100410384281d449071440c0c2007003107014003191000c0e405000b0480c1e514840705290741450803002440c0e04032807004a40318004420041c0b24011400030340200401c05010b030100340010a40c5a005000d0241a5401612122007000442032000140100b6996543c0074a0725800d10b8205030303e8a000550041145982d1000018112442035055440c0b925090074031901d02020003000d01c1d4034003800d50545445441c8404400000c2000440030700845d000a00101c000805005039070601ea0171803011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 603178803 1250 603177553 603177569
    0x2150903031005041104180b0301090b040302100b0a0b09042a030b0406210503091305061c030503061302190f02060a060506120402030f0a030201020a020f0a1208090a080a0306 77
    0xb262603a040c0000e5a040e11410000c03240300f48000c0c40103030706d0718400305000303015200001010b240030300019003960300e00c17007040d80c041c010a0148024194140b0071500e007807041c030106001d000e603003e010407240306d07440c42a038040700e001290403102036580380c004503040c94540c002809400340c00c44031500c0c449400381180700440e00d032680b09003040c1014003964048941c40c2483d0035401d52740c014176046da4107030440700300e40501040010307840c0c5541d00e8000f4029250f94280001da85d25241007480140900d40c154804d60700c1546007103c00007a408000c4961204041d902c4c00e1880740314030041d2010380aa00411013018042286101d901907103c003c0f400762840680c2101c0d955105d8000c0103040b2100350083d00d0b0004010005c8841d41003080c28403a8202c0d20250449481c0b00c0d1400a46080804404046006035000503045000981c100f0020b1019400d50b070142010076107940c0d464410040d41007024090041e00380010b2403840b02031180308405a00000c00d50782d102071000e0018002c002501a00310 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 603180053 1250 603178803 603178831
    0xc020609101e05060a03080d020301050108010e04110609010210090503071b12020f1315090c0e091603090b010e07030f27111917011404120215090303 66
    0x1c40c6498041c15038982c1c00a0001d02e544840d4101030030140c400142016000b09103c000000011080300042040b486000c1e00142c5a505280c0010104d5806034041d0502c00035800074080807402100d250200440111045caa881c5081c000603814120382c115101f80c0545401c96070001d02c5004801071040300e20510504d020610030b0541c00c003040426018080c5881e030104458001800d114003d540c0840e0000c1004840e0312071805840107407050310000007502c0c501c08030200081a0a0b0045100051541c1440c0030600401d0300401e4180e68028030702101071680b9400c8004c60b500944c0700040b4541c210b5070b480a50b41c0c44444110003d681036401500192424400030306d0300807248905000f0b5250404520700748a1140d200d20040b03007644205548141c40944891140d07a914845e0020410040040808031341c80c0010140307250582c02e86c074a082d42d0628000c0c4a501c080b030b50382d01da80507510040c152441015400100d14000307181c18803580505003131090140b400c000001443c418111074608417 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 603181303 1250 603180053 603180073
    0x4091707080403061d0712020d080a030209030705041e05150a0e0405060108070e0105011110150503010e030901170a02160b0a180305040612110406111e0a030e060d0c020609 76
    0xc1011710505c14140790130040040c17240408080040440d14001424a0a04803c585078554590b002d41c420f0310110764000703031400440c281402014000c10085a007040000384011500000c4118444d0304449a9601c0340011001610045201400d00000d00240002901d54125884810003580d040d207080c81200000209a003001500078180c8403240b6500c0d1440c0d19010041d10402c083c0412b12102c2d008400b03500101503114030130104404a1303511640802482c2c80c0503d800c45080c1c0840d0407450704104140440303641c002c6800c05003400d81d0340000c19584c0e15080118020302070440700a1070b020304040e946c028000d02000c01805000c50f202e0404c500e8030a03011078002c0110508005001c90403c0c0401c00c001070149000c40c0d1180403090020583c2c00300c49441e412180d01a41040700419410700030031143c5c0408000010444141080310405440f030803600380d0383d50003213a038010100147e0b8040201c45848900665a101105500500c80d494110001a40303c2d00c040314100d645100d02400b103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 603182553 1250 603181303 603181331
    0x1b281413050108030a030b01030212091006081c0e0102071d1603230604111315050307050706020706021b01090302010c050f18030a0b01030803010905010506180409170708040306 78
    0x110703040341c1d50f181c001c41c034000e40840d041c1e002d00305241c610750505500340001c0d00e4030000107083c2c1d4400c1802902038160141c00022440803910035801550031781d80030f9a411036155203464500300f000b0081f4103004130614140c0740100c0c5010031940207482d42e098448405440c88200303982d400c0c000c01d0821250000d02000700b40032421107190880340100c0c00d865110704036002c00c0325000c00e60056130243c004100005281590780541d4031084440c484d5070607820041158892034180881c0c1110b8915000b4550704080c4401041030103502e00140c0020360005040003040502d0341110710700181c5414422f40e02c3c180c10501802064a8042a0055401c1000c5540518070541c101d03070b1524108201c15040c807802042d5075503041050003940385c06d4410425100701007042482020700071485a041645e0f41c0d0b041868800c01c1d240c0691001d402510280100d80e10b950704461103c40f81c003000c7d03500043c500a0341c140002440c41d0012544449940040d804060040c1c1d00001e109680c00781000b404508480440 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 603183803 1250 603182553 603182561
    0xd0f0c300f0e011b02040b150f120109060f030b0a021917010e01120f05070b070f050c01050403022b2f090c03190e070e06121b281413 59
    0x1348042c6010021070400052925500c200190007005d040c500d0800b40c9408802021342c054062441e07889408600c0c81c602001d0081e000340544000b00e0103101061a00b500d1801c06806400000c0c00d290040e000074140d0410740d0b054032100c0d6510080c0c2c102a0b5440003014080e1390038920280b0910601600100d41204018101e50485201e0049412900040c0d22410000352213005c04036014081c040c00080c1001d04000541162401070000300c903a11210b01d051403400c124559071074103210741030004001503920360080d10503129041e2044134071000c0c0169000504140400000c003101da02d4180c541c0c0a4583d101c2c10f680d5916050100c00355500c000b000c00071316007400c0301c0c0801c48000c00c1001841310030180b0600003c60700b041030041026820460313800e0404005030000120941d07020108000c501c1d0062120110040c64000381210070b0f205000394a640c40d10010755805100b541724a00064043c018086100c1e440807492808402d03254a501c2d00c0d01020107125511880c0076466012800405200b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 603185053 1250 603183803 603183827
    0x706080901052511010b04020a0801081501080c1315080601090b030303040f022202040e04060c05160209070c06050a020406020d050a0507110406030b070f020d0f0c300f0e01 76
    0x41c14501c8090f2030b1400b12900384440f201034440b07540b9440740c81403540f1680083c00c0d0b00c40c40d5495000b40c56041480719460421242042c030b030701c802031000422101a020441f00d144074000e40b5111803901000142c3c2d070140040b501d2805800e5060940000c00550204849050720038110051210045903009c059990200b40c0700580400751a00d00c0030010301c2c048040d0300c49a006200d4800c1c10003440010181243c000707901051540300c91400b04010005240305402010340d25090080c180042c031400c8000251030100001d000300d005038046400c2c1e601404807504242c5d880300003880f2520b0303e0155840a5005846400094070880d0740107000c060246055510100652f0b844906000094030381c01e9000340020b110681083d55008007102080c6418400d034410142a120800306d00303160407000307150440307100306441003281180f485a94540d0105495036040d40185c42d0740300481d80c00044601c0b004155403419501031503100300702c1d10150001c10805010303071240c86805088011200540703035081441 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 603186303 1250 603185053 603185101
    0x5010207180207033b0d080316052a1605031b130911010f0e060405130b0301061508340309080310031401090210081305070608090105 59
    0x1181018807005580034207442402407030140e840c20181080288141c0207040d040b00a16002c40c1c0c28940051101d5030a14002800d07903010031841c01649421200d80805096040486130030103190030b0041c816070503101c4141c40c0d4100401d09007210300301450303c00100449202c1341c3c007503500d000c0e0700e03c100c41c0c02c0c48080302c2001d4040c1a00070040c1e807205460208141c109a440740b41c4503a48903402c5e240d403080155052042c020740000c44070800c00074064118040c0c219040151aa03900480d5441c1c1e0710545045540c19941d5104018000342c54801420200300d140e90158600f100001da804200c80740c018007040c0541359000b8540310f2000d032006149200740d207402440b0601a40c04203002c0310001c40c4020520610f00060905036941e9086416803041d100300301c1301400c2510900c1400742c02200e180c0c40c4a42c56000b000344103103990201d011000c0440740340041c45109000160002001507050300c080d507000c001c1c0c1d20301e1511104040c0050780140d402401a6181c040003402e03101c1c561107000c219219032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 603187553 1250 603186303 603186329
    0x3010f02071113061203090602060f042001120f051e0709150c050604050705030106080c030604020f0a080604050a0303050901090203061f03060f0203060324070c170c0c0a05010207 79
    0x1c0e605000d43d944610000d2801c0e10b40d1380710009110320032543e094111520030341c0c804d140146020130007490b220020b05150505046d42d4140000141300020849030340110101c05441c0852480047e07440c00f26908841000c541084c040d1082c88506510691041c900200d803415441c5031b4103010602001c00712071840101e04000e000b0f0010405c4d8101c0c000000801e4540f400007500756a41c1c2c141001010b58084469034412101881140303403e00460b80644a14401086204a07a0340020f0756001c0c041d0000e805450942117102032030300c0700314004000e020740004541c01c0d0b04161a00f1661200500400c4c0c0c0000d2030400800d1901c841030148604084d00240105090788032103440c07052804100070f0760034039210b00f4400040041c00e54022200008a003d40040e1249491418103060441c3d9450051107603149000588041c012102900c2e004085440d00003c1800245040c20401d4001070085001000105081c2c0301c4840008112015110680d01518615034440c01660346202c5070080c4040311043d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 603188803 1250 603187553 603187583
    0x2a0c0b031e040804030206070317130302030409051503030c070509060906210321040515041e170f07030e1207050108040f060509030c1c090302040b151803010f0207 72
    0x1c80707400c030707015400192806690354009211075000e010214003294401a44c464581d182904c0158803000da100700c850500d001b99002500c80c825806190615503842740802e0001f110324280c840a1a80030701229039540a441c0e00c956100204e00c01e4030720508903040001d00701e00300f0f080d1240c01008003070040e0820020201412078401845003951445110038000181d00c030588915060365100001d00e071a03400c1c00c241c2401400c04011030103c42e08603c1490501c000a602519101c41c001d07141c05c01c0441c48800788c5071420038010710500003014809c01055000c444420b840003000302d6442511001807850b0202d041c004450503500700954203802c1349404021035401028910762203403140102d10741001c0e0f07035565141294015684480190f20108000d00100b004100000c0186801d0700300c0d187c480c0c03010f44000c02e02c0ea402d00009000c0c035101d03540043c1c10f44451040c41c219004807022030762101004010100c81c0031003101c4080c840c0d801e221400c000c00116100700c4000c55008542c43c150310403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 603190053 1250 603188803 603188851
    0xd0509040c030f060f03110301020c06131505010f0e070c08160323040e10080616020f1506010311071e0503040305070b09130c02060a05072a0c0b03 65
    0x754181c5440700b0b00d40c442181050602252155402420b940a01da1a0f02821400c0132800d800c800303801031b80a0b82c4104251075460900141580d40f20301d0707121041017201c925160580d08400c00d9002030401609000000c15031040040144040c1d508080e210308281c2d030342ca4002c8615114a00340541620800c10403861034050343d0301c0a85906000c1d00340174106c1420300405d200d00302c2a502d0744041d072000116041c031141602c8141c0a400440e140c00061a03541401d007a261200e10103451400070f00010700e0900b4405000f401051820b10384c0304240c1e00444085030030304201203001c5a540d80064070307084030800c2c120140000d0b1400b064102d0305c0038440004c203c07c10400704070091015101d40c441808000005842040031201401030000500c2d00c9280050500c00180c0f010701c11a0003081c10108000b11440d0f0005003994050404800421542c40e100301c06e4584444000d01044200707801d001c0c01d031424210b05021a007a41c03280c000601c01d643e403032449413994081905c3d11041d0907244000c00e20002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 603191303 1250 603190053 603190061
    0xf040303020c03090a030c0e0c0f0d1d010203040302012f0414011e0c020a05060307080f040303022205090705030603060103030507030909241401020c09041e0819020d050904 76
    0x25841811a490b0031207000c00240c071720300941c0c0101e82000c0303000c1c014021141c01500545d000108d28a4060401c4100b11044074540505c004d903800c03159031580d40c000c143c651420a9102482e201000b19503038101420000d01902811843d12038180e000c81301802c0c3c540b0b20140602d5405c9000a520f0309040c20001c1e809041c060008400e41081000b0340c2e044590340050fa104407041030240c40300f118200305441400b07800c107000e9000a110300d00034000c00a110360040300b1329500c090843c03403208540c1d0300c5180613002406405200003e80d001c0609030038805844150407026104100c5e2042d42a40d0390040c21034007403004881080e0990014001000040d00480141000b940b10b41003020140352140003460446070249095198450180044140368035007075800c50282508104080607801141c001075510780090b0806400303056410006001e01601031a9040541e6002e250070002101508068070190010000745ca0000e0703a590344105000e0000400c843c540c00b40b074650f141000c222600b044010 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 603192553 1250 603191303 603191317
    0x1404090b03070b0408060726040809192d080a02090a0e060f040212061b07020321090310050709060f12092114030a020703090312080a140f04030302 65
    0x140b18010b008034800e01c1c0900588003902c0d40308020700d00b901e40f041c8001c01100e002008080c4030040c0107442035040110441055020381c0200b000e03655040364401140c00d420114001384d40118007204041003160300003162091456044d07801c5444548911080c1e05200003074401e41845910038086240141854607603164805da41d098006162941c0700005c43c01c241c0f040b10b00c02d03529600c0300300304003c500e0903400020910109000800311442c002290413540f080c401034014419001282540131982d04000b03e82401054040f8810080d003074510244043c0c00414895101780102c48692902403803a1240c0ca22a15241d603602800f1780c03800c0e00c20344400084041000c104424084000c00b00c603114002c4103ca1441740c0100c0d0292509003030b0003400d030825030350b49004010041208030340344140038040d20780214032003d0060f500c88080c42c00390381c0d01900307500c01000c0da040f04041c62503039a00310410920502c04044e003032102c0070144c0f10411203414125038813040c0b03001880100780071a10a0303000d030410f = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 603193803 1250 603192553 603192559
    0xa090e0c0f030c0f0d0519021f12111b030304060506030d120c0507140a0308011a1909030512030901050f040209040605270708010605010216030b10090204090e06071404090b 76
    0x85800e103a20303a01e08081d0000c0f02c87c900916607110300001c5041c0141004da81c040030020107400c490800100500280c09106446040d503160b00a208030450034000b1502d40e034600300e801304d40043c00080c07803607101d410480d000d035012454800020558140400d501c6507901896403030146245150120314001c1000031b001c042081000c0c0301082c0011480c164401c1c800c40072800401c024982490000d000c00f105030050f04041003214001c05c0502c0080c801c0d51030340c1c09010a0303404114414102250751810a07030000d84030748182d0007512880e108601c011805000800000c0c03045030703142d0a40b51801903003034400a4101c1c22000005000c20301d603512164211010050450b0542d4480804c1404007000c0c4040c07251542101804000000003480b44000501d070038009020702c9049030040460034242c03440040c22540c0c0c400000b46e44010107102c001e0140210701c60441d02c40c2e80b5110170000820306051001414412000800c244038014a00180005082040d15240c1410050808094400d014059070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 603195053 1250 603193803 603193819
    0x30d09090504030e18240a050105070602121609140a050f0d171201080f0717011512021e0906100c23070e060108070f0c020a090e0c0f030c0f 62
    0x8990f17551a01c50b00b040c80b503000015181d60800581480181010000c11200c00c0d60f0311148111a0315005d5200c01100c0007400e0a9890350000d05102c4068421403031200d090140c00710030001025107400b2103407030348422a903e0f204141d4550041e64400f52006c0400356002c0f420620400091403c180108450000548949407805040d690103043c3c0b44900840b0018841c007003070b8080da4200251205004210500017400c807055125404c0e500c0300c515010f001c0046c1c0000d0344031485000e0075001082800c21211046c1c00544d5a4034400e2201480c0400c203c0c8500c1840f000d0041603000c40740d0401c0100c20083c4800038540f41c41c0100300100e80030044400600c41c0304100000490210100700300204d8000201c4607180c520a05840c0c07c05215403c0a81094110f100740b050300d0b40c2c85240d8a90010407424000013981518406540181d031030b0138000c0d1f0006581d4008200c400140d080300468810320300441e041c81e07415108220340c44419010480e0103074400000c8484500e00070b41020202d68024007451 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 603196303 1250 603195053 603195077
    0xa0c050d0903030f0e030f0a0c0f1a040309080105090d180806100305010c0804080909060a0b03042001020c0112090221010c080a020a0e010305070207050d0b060906030d0909050403 79
    0x8030944807861410b501103035649041030001840c60090702c0740000c2c0800998940800540d00c18440c2c00b500090300e007001402c815490800c828250000030513904074004c4001c07091030b01c1e54503040080484081700003c03031041c0c0000c0c0e040d0341400350038001d11407500600300980c1c5c1d4450880d084198000f0a0703207101003090b40001e040d103051001350300450540001092031802e504145007035419110030401041410010880410345102c140c035010001111100c50507141c10740050b0480c030254001e039400000000034042003102e20040c1d41d8041356115141c00b2018460300c01a46c86640550701107000c210f080c0900304100c0043d030f02940c280c1c0c2c8000c220913a0301105d500be8000e13594001c0c091406580d902c0320034400d4503400a030340c2c40d031040c150300e0305610306054140c0c0245504031107002641030645400120b40d81e40d00a0040c60080c040c047d22003041b620013410051200e910076101103014030481800300351182030205050240c08229140d444041f0310b088148002410001c100ba02001524101c034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 603197553 1250 603196303 603196327
    0x15070b3405070606050a0e010b400614090d05031909080715050708030402181f080a0302030f0c030d06060c0b0f04150c0e09090d021203010e0a0c05 65
    0x1140c01001a554290312025a4a024001c5595941101c0e10401000f8002c01c02100ca50419905580303c40c0191074031514a2100d4102d0501800400591000c4121070180814030b40088072000c0c0b10282c0a58408036591035050b90f42e0350500b100e0480a00e02000142203508044e410280d901d48a80d0441b0b1a10854070118000440340762540070000c4c3d01c41a0811000100700000000340101080d00c01c102800404007a20521030054000e081a80220004041d982d41c0200c4608101001c800305001e40b0f4650000c1005448101c001c11143c031051802044495000607504440c41d45500114904188403c40c5c0125410078011441d10f03100802c0581c110760001e0058000800030340e203800c1442481c5181c0700006000042c85684140d141504010104807400101c01c200044a4800100e40540c000204d0f500d200829070b294200d85280140820b43e10000750303c81e400031440c1d080d01c941d07408018130441d01c1d21082c410102d18102080c0071681450440d8028403d480181c10100c0c40d000144d124 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 603198803 1250 603197553 603197641
    0x3c090c050d0c030b011509140f031b1e030303070305100b0c15090a2a03140309030d1407020f010507061d0c0a050a030609060209031b15070b 62
    0xc02c994410004200700104506034103040c0c00b41603818108002c26615200040c2055202d02c181007503040c004d0300c0d6a00315260100c00003207000001d0240d4020341c0040400e44128a070044000c1d002e92105020102103ea03908002800488003c1c05185903032120072048020300005418800d500703180c03240001d06e10b40500018044501c86002605003810720806a114200e002410719000da0000428500014143d400f00c5899032501d91103e101078010b02c207209881000c2ea00003e10107206e41a10844460f00000984007024084044650385181071108444031540201607500a003400c3c00003a0040c580202560322211062500d0b0342406480d444d184241d451040d40d0b00548282c0f00d92140145009104c000801c40b030548040200b40d19001c040342148450340302c090705a5540c0c0c1c8610b020002e0310780464100c450001d00b1941d466883c501a0424000800c030380a1044a8505940b0860354040d0103548180341c01c400601102d80c0c0c0c0c400614240301ea907100b002c5400b0914000c0780c40076100014 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 603200053 1250 603198803 603198829
    0x10060903110906031509010e0c04111207120207050a020406141309030c0b070f020105060118140d05150712090c05060318010203010f03020102160e240604093c090c05 73
    0x10011800300340c0c08c0341032400d00e01c490180e10b01a600b403101c03102107111200e046640313464805110000d90303600c0700c40c101da402e81d0860036000043d00004102080c0040026441c900368001c481c2003180954440c00403801084000c0c50540021001203032010014181c0d000720344880c00390520b80f0b034161441d52640c50498049400c1c00204000c420012905070782403040c02c0c0d0120007030800e02a048001c0b111f0404a04652081d900385106a40080b2040d40751842c0c10503a11350700208032200e240440c0d0b01c0c80b034406411240040050314105070b00e10044501d0159241c0c640d0850341070400d0300c0c106414050f8a41c40144204c00701d842e071002d400138107a0240300550007494030030300d1748000e18118800242402020700032a01a801a0202404420313440e85031107410011507588910740240c0c01140e985160b03030494002c0d030310020214002808000a03007140c2c0c2003081071200020b04030301460705104a0005440e5038640c45c2c40b86c1c48030650889840d44031100700b80c0204042c8111607078900c0091032110002c2 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 603201303 1250 603200053 603200071
    0x31101090c090609050a0506090c070212030a0503191a040b18010b0c10090c050d1407060915051c02090f030313031a090604030f050d0212100609031109060315 70
    0x840800c0154503500c05d003500228211000d004a08180000621000d0302038100504140f00182030004c55950056180c9140060340a803602c2c0d10303003c6070180841d001158000300200c01d00c41e07240140300d090312524480241c0d03280d410703013290800c1c03007071200174a802003d403908000d0000c94075451170f01509295000309000070082e03a648291314003403801c2094104d802411a81400c00b0200040c4400030752006452065800341644407107400d0149900300300300201ca110f802040c501103492940405114155904400302e0100c80d60100e6045600e8820034440d201c241b00003e0000b03e500b030f580e4000b0000e014000b0421310381c400c6400b00084c1568008806294410781c060410420861621003030110024010b400c000703245403800680c0d4a81000800040400c40041051100705015800b600e0b400701140a007151540481100303046880720a4507512001d40d0240390000d8041e2040c1d028074252580701040300c140c44c640e00709020b8040805400140d142c000ea01002d0844444400b456104030604 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 603202553 1250 603201303 603201311
    0x50f0d09050f0307080304060b01021e0607300b0f1c02090c03010308040324050103060504140331030501020708040e090606090103140a0b2a030105030a031101090c09 73
    0x340741003440c009070103800b0890b80d00148222130100d5a9042542c0e40f25402c60b4000c11410303207800040303060007844010108503141c40301040040ca00005402d6101700881e44451209404030f0094040307805000c025a00c5c201e03640c41600d03071403d2298002054010014000000c0c089070900042c2d14210341084000b016610000d105040d450120b090310f0f0405175481085145504680700d080b213034495400007074201e420712a6400c0c008041c20781d00007002202e0304030800c0386584074a00b80019150569081e03420215050003502040404403c441076149481c142d00e81c4800181d01100c0201c04611560848030744e410400000305e030084c0010074800d449421160364590038aa000c1c2c0d10740034003030180d00c10703035200e401081940d44820f914581980d4111004055020910590615080b24100010700c00c0c1b006a060100c4100140500c120002040c003082c01e0a030001140388400780000d20503680c4c90750000c1e94441c0480e00031868007141c12140c80c00440e2a04481e1100203a20000b80c2c0000c008541d9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 603203803 1250 603202553 603202571
    0x90705070605180c09040f0615060305060f03070909110607030905031006120b040f150617060907030f020a08070e01031406042f0d06020a08010512100507050f0d 71
    0x391150035031118000c100002e003100f20304400c82d07440035040380c214010342400c40820240a40c0034841081668040d100b0b01580300d9864828040503170074400c030400310382400d01080c03c40c6800c0a82079100d0101400410400b4517002c40031001d01441c260594140c010903081c1c80d000d4403094000e0940300c1c0292a02ca5080d0710300001d00d803a161440c0c101c020440d150580903c03605c07140b40000003005030007510204107a1110300380b0310002c001c079480080c50b80301401601c4000c604c0355004034040741c6411070403040d01c5002540e050745600d8116045152078208100c1070000464280d070f100c10f400e00240a1000e9035072074013140b0340f0f444101d070402c8100e084401c004104001c082a0f00682250f030b0003000d042e01d03080c10350f11500240500c03602031240d8403020010180090b500341c0400f41c000c000500d010903400703880c24004025444000d8410009902000208590a0424401064400e000010309601c00071400550040401601010420000708a101c00c44218000541f0070654100c40005200c11 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 603205053 1250 603203803 603203813
    0xe010509010e070518041b090905010c081e01030f051f090507060c2004020903032d070b18010f0606020607080708190207080f0403150b0103020909070c0c0509070507 73
    0xc4643c2c0602c4c0b090b441c00d402c0310b440d08000c0011031b4110750f01c0044142c492802c2c003071152408030035400000e0721a1400688405003c01500840c69018007504c6400203500c80d240a032040d58482da80017a40b0341d0200c0700400014000710150380000c1c0c041d20903a125150042030285103282075014030304900c0c0d15101048140310b82407010718002d00321406c6c00d00c1c246425070340d00c51404207001910700c0d106c0001550302500e602ca0350111401c1050003004d49580c0d4245102031b61030b00d52091100154483d000081c4018040321100300e40d502070308028000d6031030303640300c10525920300040a01138855403600b000c203046a28a00a00c000307040c8640241c221450191001010484014456000c0003054000d0120860f9401c03003408411403500800740e59031a003420280018440d005001402a0001500006029200c140c88440c00c0c0c0040051000c9001d1074011030507409144800d80d48001484042038195010380046110070388151103207980c0590703400024001c0007089a8581c0420b10000748042040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 603206303 1250 603205053 603205063
    0x60b220c050901080a180203060a0c0305090c0108011503020408120301051314060621010b0703020f1c03180b0403021f090f03050309120c01060303080109050613020901030e010509010e 81
    0x31400d01e8101d00381100800000d0400101030a82500a503507034140043ca0040241c019101d9500a41283e01c035007801c03950301d801410030341c081c41c1c0000d02e40804542400700106405008500503518861a44d003081094404203080c00895000c2c50750030040011406014000442080c005601c1561258504014403200c0a1a9440e400e401c0785800300c002d440b8114403c440e50015000d4410391303218501c1d2500341040000b544000244408a60000504600050f000703065061103542502d5004420f502250359030004001044880c86052404003980d51096010524410b00301005c004001516199090155010380b000e50040e0440c0c1e00268012541c000100e00078000d48504002c1c4940945500b1b01503511000f00404100000000c0356501c40200481030880e100b641d00d070b07550380c020711203198000c0440e4402100802d0403034000003050300300c41c03180324815040034200d4580401103064100c001d5200083c824103041d85c0c0d031a580d040b20024420984105054000051070300c644001e0319140c5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 603207553 1250 603206303 603206321
    0x507030314090d06020d111b0d0903050705012d0801090e030702151305101101051b0a031116060510080c0d0305090a35031e07060b22 59
    0x400020042e00c0240d4480e40c01d10242507810070030061302d9001c4103108134040c118005140c02000004146501c6e45040c411601014824039022201070904038042996078070902d11016240b078204400811295002d07000c2c142144100000392801a4904814002c1d1070b070031101c40800280c0c00b03000510103020144075803002c1c10480c40c000c3d41010300c103a000441c040d030b4800d039400503c0400305000c00d454200031024006070000070803d41c1050035000d0014140d0280860740c0d480f644c00d00300407541040da0189400c041d8041ca0014070700d0075102e036009501900c4900d0460008900c1084405081c03050300c00c0b107690452142c540800d140c240300d10fa820b000d4030540c11103861500810107e5060b50344001c602184c50745d00d0b00f001070711072810f68001000820207610503005620326140040c614240c20035003400c0c00c0b0040c419160703000074000000381e80c0d0088100c0410f02400d030065414030302c0b00b0040600003071031080c0d0001c203415408c0004600400051101c070301080001e010a1707008500309004403156 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 603208803 1250 603207553 603207587
    0xe01050435010e030f0714070b030a18021005090a0807090f1b020c011209080703030207120e0105090607140703120923040c021015080705090c0304061d070305070303 73
    0x8444450314988174031403448200181c00c00015450f081142c0882c480601007914000c1c0c030070a0381d0ba4a040f12156004840201791546800340d0703c14180e907100c01e01c020b0300340c01070220300358010000c50503115a0703c03a50540e5403000020500007091101004064007601c000c0601055810307003000305505071500d2110048014844031f0f20002d44035400a5050711041c5c00b440c01c10f400500d001d0f0b40c1c40050821040c0a0100795000491905140c0c264004144403803003050400246c814000040b03613058004503145e800907c0801040d07400d0720345400609240c4d805280780c0881014203007034071442d0210607402147d640c0803d00b2101e5444e504050748200601c441150911311880b81e28000000b5001504918440d82c1d6032580060468130030810320080400062041200000c1d01121400352903107841400154030980a002c038441c00d03d032032614069030f08000064199250342e81c800b0003421403007101c8580025100280d0581d00000c0208200941c05100508003060442c203004083c889203030b075500f007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 603210053 1250 603208803 603208811
    0x6012f070e0c0a03020702121603021807020c093d0b04060c060f0e03070b0613020c0a0b04030e090a0614010e130902061b010f0507031b0e0105043501 66
    0x40d42c014950440315000398600e0010781d40c610030710015040943c4681005413500c0b501c221220700c814006002400d490003100d0b40525845101784848030910100d0701d00005030031090203142107080080e50150014014a008074000d00e814081100c0030960034021400196414a1140018904100744000d03004003c0458585414190080c1c45400140401040380b9a200351144d00440302ea8019003080412405490740d41d00203040001800d8002d81d080c52144907960031300800c21b8003d100300d400d2074840c2c601415001d8140d4407007007060300b401001a000e22040c00c14a0300c1c0380e0f440000d400c0c404d240007500001c1c040c1c101508039a2030410a407405042c01902c0121003a0b5588030728258090040e409800708282e8014400310343c2074003a28840b15151461440310644a41040d00500745082840d60100610b03a01d007041181900c4108240b000e03000340751401d4440851040b004410b41043c107044c010301d01581c40114090010000440e64000070300c0c0d802c14005000f030786503004c03100590800240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 603211303 1250 603210053 603210061
    0x30516080931050601020a15150b07060f0c02100b031c020a0c0503010c050412140d110609160b070c0b0304212f01060305030d090c091a040506012f070e 67
    0x2075980d90141f00040c0c14008000e114000d0b0110507004071441d00c0150310900c030050346c1c815211400340c0000c0404c60b500e5040c5006c82800f40c100d03104620f00c60f60300d5401800c603590142040f20041c400c914041d500343c0640740002c40c0c0111001400850480d5560081c02014254200007030141102d4000a04c03e03410f2a40580702154000b003a14203450410b0b401c0403040e078161130958070f00103560a24005a015610080ba101600010010141a1b01d101500d54550310864840d032031707103001812a01000c00c01c80782070080f004010041c045c003a02c95003109812545941e40711640c3c0c0c108440458018480405225440040102e400d00b000040d00341110008100c0b00c141540c1640000140720450201040c00c0507078009402100003103401c402178075a110210740003140a0401c070001503641500390100002c003086540b05400040160042c0c201000c81e054040201801c40504030300c0c10844000d038003044240a0941550b41c0f418810104590804044209030610080f5444043c009403d0001c00c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 603212553 1250 603211303 603211307
    0x12030702030706030e0a05062503050f0c0a02030d0213090c0809120d15030501020c07080d050906030417030f0402040b15030f1e01030803060f0409030516080931050601 74
    0x403401e035500741c1801701e050321154040d14a401000c2c003002e0300503c601010b00100110702e03001c5d1850400d00644144411030b6400c0c05078152802541c0b10128240003000017041c00f01c17041c1c00760501040c07a10540e49040c0c1040b43c00e606a03040080714004a0400f00020404101c45108a044031406401d04150a280c00d0200d540c6416000e145508000c00c005200c00c0003010360351120070042c215240f0f46411b07503103d00300366000f07400a01c49045180704402001c6044880000e1040d04111159280e502e130000034030a0100f2504041c00840c1c000c512410050704140500c8042d500c00c00e50320512044610385801004240ea941c092032030302501c29245401c040511081c1120b9110b442c3c0c0c652411a070702d4001d51817001c1d2194029019441c00c40b84000300803ca4038030001d41c02500c00322100c049159000c0208011500d0303c1d50000e0120354200428030000c4001c02c98240000c5c01240c0c0d550070400c0f0f900c045032109950004035401c103410b2041091240c40040351203000031040e00010005440c1101c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 603213803 1250 603212553 603212563
    0x30507270c02250b0a0509040506010309020319080f0408160e130212121204200607030809010e0d03020901180b1b031c0b12060702070501051804060e061203070203 72
    0xf9034680300b10b8030420081c0200640103010300030040322100590350280c0b03a40c000e045404c00c81d8000e108605000115134190b10a00983c4a0160003c1c041d00d40041c00f40590b01481c09080c07400c6903844410310415103500c450101401c001c00094016045a000e0f169502035020020742064020002e00424005614000d1500580465054681c0c1c10540040d00e01d1342c1c54410700700c841d42da100c00005407442410400c964000c0c003c6205800d0f40100b515041c1906810781d0003a138009402100900039280400e1190200e150080542c00c000503220000c14800d5007400080049840401d40001c0c44503d5940e0000030000400c00841d02c5601840c2001c0c0381010600c02d842e181e41091803003458280b42003105001701e45010f404d8540a15115440140d420040c00340e40c040365106e10040f055660404d03001041851203152141c0c054084107040c407005586c20b810688078561102c80100c95402c05440700c1c46144043c001890201e209031a003a410403517014184520850660414000c1000584002039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 603215053 1250 603213803 603213823
    0x60412030f062603040e010f0302090c03040f0f11130c0f1d01141201090c030c020a11190b07080c0606060c060a0504020d02100f0807020312041101030204030507270c02 74
    0x610b5403d2810082c102e58034500135a00014200300060000250160701000301f041224401c0d43c008003240d40b100300341481c5000441d4080c0c40c4424404211740007900c5a000c4902251080280450005411001c60f102800c1007103204555540c50030040040e03500000c1d52106914546044000610301301d035100752913541c0713000f110705000303d40f04c403007030407004000980300745c81541c198910080d80d440705601c015018094089020a19040e0410f18040c0301044901600390000c0e88103480f8000d0505101e08842c00101c815013010b172820003c07468049030002030040500983c0d00079100c01d030300003a80781800703000340459214035010007236018503300100c1c4e40c90340316000020020701ea50b1207002040c91110340784c0e8000d44c06881e080490340515004007803c2c401e00d800e685d407031200b665190816a40c034411043c00281d407021303074000640040c1c28140440c02c41c200625000d414280d4940d905032401c00d19401a24000f24004100da56102d8090681030105d807c1101c03e101074001041c02079140c4801c01c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 603216303 1250 603215053 603215099
    0x206040504090816050114010b120610110a03111c09062f0a060f0509100513060606020601150212040b09030703200a09050915041103060412030f06 65
    0x200c060381444810404d951580342d159102d5100c4500302d01d803c60007040c2c002c0d4032241603901000040b60440703042096458690040008101d961203460801c40280a604404810014160945c5045007814858600c916109445150540004504030760901045c04c842c103001240f050502c9480503400b0003120215000d5081911050402c1c540b6040034561070980000b0049003400c441c0034070b100004090040c10b0007080c04120091419100100350f40080c2e55058450703100f9116841310424907444175401909440224811000b2551040d050324000c0e4080005600700200400c03041310203582e601c00c00941d03840940300c1034141464226090103140540b1100040100d019121514100502c401440e00a410801010303142e84080c7c01c84201c1e003452500400c03c490b0005181440d6000301c50003208000c01804001404400d48615030f00d00410603294103c0155403000a03440c00d100c8036004500401d480c0c0e052030307203400e0301034103643c601354005202d2494000c00300603100e0045846c00c4c10360882 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 603217553 1250 603216303 603216311
    0x70c03030b0d0f060e0d410406123c11090118050906091306020d060501030e031306050a020709020c0c030f0d05040905060d050f01050910090206040504 67
    0x141000c40c0100801d2110941002c400c4800030144000400e003454510b200b20701c144a40341070707400c040740ca52615440c0e074000b09070900c5070761064002c0d6a88440720030000b00d503010181c482424524180340800002400340340d4000038103108407030303018100104199803144203105202001d0403d00c22070003201e8282c2015071405032981c00208802800c892500903005040c80554030020b03140440d54803420010340850100054508011031203083c00c02280c00046c000c41150b13071200d0501102843c000c240100000c000f016403400200305201410808204a60003e0382906000c005400c48101d4007040c00b04d42c1c414081c0043c40035034240a0300558085140841c0c44241c0084140d240c8050b541101e0250741c0089010700c600a40010320b1106840d08408844200703400f20b0005c2c1d158a002c403040000160200400d11826416410180c0c0210000e080e000c004100c0e0303140d0608001a41841d404565104c00c244580c1450400144a094070f000c6810440d0720410307800500c280c4603510403c0d0086850b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 603218803 1250 603217553 603217577
    0x6090e070b070309092c010b0a05010f14030c04080f0a030f03090b070c020301150305061515030c0a170a020304200105070b040606090504050303100617040609020d15061409060907 79
    0xf0284511b0071404280025014001550140c080d05406441600603a540d1100140b158800c4103600f0101506c0e0715408082c2c122a00612560350005142c00e00c0100304000006401c041006050701215054014046c07e420500d001400034028012079001c140c00c6c401c01101089102c40c8064201d5840c0c1400455007145101103409440ca50807440407094400c2c0001040c8240407900b244601010b0109045808001c42048100c9010b801c6407410040c0500004140044078030090044035020308002c1440343c07850600181d400b6085070030b00507094000c004d010802c1004c40a0304030482103034041c00390b5a040d1400080c414020401c000d0220584040840c050100715030000003d4040c41c1c3d4280325615090030900d0380e030b80c010384601551040114000803054801c1c0200801c1c2e0042d212540591788441c1c49150280080d90750070781c2d0004848103100009054001e000350490303044400811503a00d0400d0034031444003c0ca03000e50083c42c00808100280e551301c001c0c00d910451909114200040e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 603220053 1250 603218803 603218831
    0x4030504090203060a09060b04090e1204030330020414010e010e010e060d05090d2c120f07080115120209010501050c12120f18060c180406090e070b07030909 69
    0x80780342c1c00308406511f8200c0102e2524807807001082078410f04141400140f01004c1e80a07502d19000420301c000e503000b0700003880060301c510b04010030825000d161304c084a280055000c40d124845002c1c81030142d00060400c082544018024040c0f90709003400f098407070b000320020f40012000c05007241040000f4400f00c94030360700c100c01c1e56400415910100000c0c070700740c0112640c07260b0031400440481e07a101d8031a040100d503c49490404045152001c03a2403440b0418404c0064507076006030043e00600100000070481001b410700103000440010ae4484100f00b5840c0d0f0906a0340c10410a0856801c0540090f0305d4843d1902e0454030213103005551040050303405424040340fa0340466070191b00007420100501c403045100d000d03042288400d042a11041c0d07404130784002c00400310307145801240001d5000d090840282040e50041c011170320860100f08002030883c3d0307194000f40d400c5540c54801c000e01c10390400400f40500400c0340400d18104498030013034100442d920820801c251104242c0030301710 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 603221303 1250 603220053 603220069
    0x503151f030f11010806091012060207120905240f07050a0b010902041406042102010203090a0e0a0501380f030109050405120a0c06050426070302010b06030403050409020306 76
    0xd03410100b20600e10b2102c0c40c150b298801c0d00d900c1280090310900109846140a2100301c0c003c20004214052035840c0c5514805012038800064411710b90a000c0c0070042031400801c0301c111505039440d031580c1424102000b01404a8442040e13803ca00c10701c08081c000340702c2040781c2e2282d5806e800b5546400162412500e80141c085000344070407407082c00041c00c212190068001e40780091a11119a2503410034807403640642c1c03141040e0481c040000d1906200c1280058440c2401072040e40e2400502d500843d1000203258072000e0080b1500d02080409016413195034007401030180f4100000d401500da00b8108111792520710305041480c1d8040c032449204d80e04590800848002c11900d030b60751031480360000c0008542c00d4840380100341a43d103a0392500b00803280c0c045043d4640a00700021519040010034009104494130042280f91140c0208098045480c100f5121401556004685402425554000c2a10f8001e02c1c083c01408000b0341c10505641c1510380d41170b4010307126960000010201 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 603222553 1250 603221303 603221309
    0xc0c03050106080d020601060e060d09020f3109051f022a0f070515130909060207031101060e1810050a061502060423030c0f0c01090503151f 62
    0x3580b03042030026520340d0101d121440003001d41c007514180eaa80d686c0944041c9014058954884000c01c49048800e415170301805940f0f0001c0c0c0001500c0812002041c4000045049880400101081e01071412511404094803004805090040c0009a91000d54600400504440c1c00302444911030038bd814943c159138005080213002ca13141c041e00c0101caa51600a900030011500a00c24000c55452000134001d084031005041c2010240c842180800160060700d12901d044401d4440058480340c030340a400c281078010030740181c1c0d403100c1e41740c050720f0502c2c0d00b213079010643d041160030001c44805c9500c60ba0b210809020b1098004103d41e078090038a81101016095645041d0078041e000c0384a50005081c0c41f009518207d00564188041ea0358080c2110014001c14070030001d440d003002a802c0c3c6c0d13075041c11094100c1e4109800440c0da14200105a19a00d045a00617001c004071903a00801c0c0000a05040d4098031b04020000566200190003d00000d00c1490400000711550300298401e002 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 603223803 1250 603222553 603222563
    0x18040b03120a08070f1e03020903070806010305030301091409060402090c1b06011e0e0612070807090b0306011719050708030705011a10050d0e121209010e010c09060c0c03 75
    0x7035402c081001070038500058076400c000810040e0110865805a03c105041681c10000d400448980303890881c041d40c441c18082d40c16000d80107001038544002c22100b4061840b842c0038644942c1421541401c441c2400481a01c80e04c1c0742060082c4a0000700707000307401c0794068413184215543e010342c00d0028030481c26940384083c1403007404c400030180441e19605a03000a81401c05020040d102804032644500603031080088000202d00c0c0c0340340c559081d45520110500750b503005aa00d20282e410100390750710811119449101c00251441e0900c2140d02604c5412442c0745041900308540350b03180c1003e580043c1d4010080d90403000d2200c10840e42000300461401c82e03540b50b01d14540280a00344800c60300f445451840f01c11503851606103040c800c00394480e40d41e24140144020100090310004901d00c1241c01f8915081440d006d01d1001001c2c80082d1078003050300760500443c4c8030300312030480e03406215991616031110106680213402ca01107449901c2c1240e40c143d00c50a0a00071b030003003584010701d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 603225053 1250 603223803 603223807
    0x150315090c0905131b2a0204061e030309050301051003261809130302120d0612030906110d0905040e190b01030c0e0108120a020c1908010f0218040b0312 67
    0xd24045c0c0c2002c1428040f41704010703100e6000301020744514680c9103000540305e06400100c409205481c01d01307100310b40003e201040d6165140c89c480285403400c103128008464001c0d051040c1900100f541c0e0081c003081d8001c20448c680f040e010700a405003800020301e12051862603c0e039088164040085092091921503500c03010741c401d40c4003c0701072600035405040e0000c00904180c5070081402c0d242c6415130040c058801446082d0f00301ca9101c1d0300c441e07001c1c9589000c0850000780a00e06100c0003482521600c4116082c4800680014940c100c0091581c0c000d500045c11564405c80090450300261800700349444030100317543c104070001980000f22200d2110710001d07c03104e040d1040c103c034000c100f100112a100c2039041c02500d005d0040303120039440000c5119414803410003c0000e2112407054a400c07202010009100d074108440016200401140c00c2c41020002c0c49900f01d0200ea00b0303000c510307149840c420036040850725540c0500c11075039100004030a490900120100c5c4a00b034107515 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 603226303 1250 603225053 603225079
    0x9060d060b03010501200c0904020a0807080a1a06010c0825060b10050403050c060d110a0f030e071809021c05010c03050601080708060415080f0304150315090c0905 72
    0x85075810910810b800640312214a24038403081c2c0c06a046206514400380440790030300014441c01e5400a04100d810111800e03001030302035010700c402c0025062000141400d40628280303451981c6c803001643d020300c1c018009105c41c0b42c4c4c0143d003100d906a8006d0005488400c1041d00c1722407502400181e800c80a80d2070301801c1003007801c2e0300600325201c0c1150000783c07400c03100350100c595020751302004201d0b500c14052401180351050250000340c2c003141001c00d840c5040919400690081c8294101141c003400300f80f2403c941500418500c4050003005107541031038040f42c09540410449140e03901c681d6252803034255101e60701110445994040e440340c40070082d00c0e03c58002d00b1040e4080b030000e8900404110990b00c6941200c0c010301c2182c1e14000c02c0d4403031004110042078004541d05c0c030b4a02140e0300040022040c0007079401500020042d5803503d140c84003210400d07292070801c908061070100a0f581402c0140f0309201550841100000c00300140740c020785403074560b5000075070300c821640c4603030b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 603227553 1250 603226303 603226319
    0x81905030108010609020f030c070503070f060b2e1d0913060b03070e010b03100504050703020a030615050a0f05160f03021911060f0f0c1606210209060d06 68
    0x541c101e50803035008001003561041100100e02800074070302c8450504202140c201c81824010708002800344081c0c03440c00c000d950f180c81000e4542d42e0104e40b0a40c07110380c84982c901c0c00995031902c40480c030b181a54204604521040c542482c80b101c501404415030403807007c0c0c04442000a54020003912003c500d062082421020000074030f0121a01030070070b20114014200030503401c048517541020190300f43d080c4030b40000c454000030040c1e107140c00141c4002031659258011240200710710b880059031a004d10700d00030144d840903000001100b06400c0c1884690358400f044911481c03280c80e004409800c00182180c407480703040082400200114201c60502002c18020141640b29408907a80841d10321910f0070b20705e09010014101c004002c40218203414100c0c0100403060b001c44569103440c40c20402404190402c070703030071416070b4401c401d2031402e130419600e190003409e0030b8148a1003801540c0f4014031407a500c03885541550307401140502c042d0320b460050390842e41d04c0d528180311864480030b031 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 603228803 1250 603227553 603227557
    0x5031c2708070603020406020a030e0111060a0b0a060e060f0306030f0a12112a061b01060e1b0301060c030e0409111302090102030d15080a080901020d0504080c0d081905 74
    0x51407410340200d490000b08a4024400c6500321819500030300f0030b584031a10f06031050510301d01c1131410701c1450340209422900a1080c40c0c4126400c03500060501c0b401405d1208558060300518140140600000316035a03d8174260f0f128501d120520710350300c0d034465000c64186a11502d2007003c034810030948000704422910310040207041030350740884541c04c2c003040035600c0c0c810600245500701c10f41c4a505120b0f02840c0342d00352980c40039002501d80840040704840c281040161a5407503555004103000d1060807002c050340004a0842c0c0c00310700410304a200c4003520062141d00c051251411210041601440d0702034060440280100040f900714244250140c11380d00f0070301d20034102a2021614520148291011104180d00441c2072048011303501d80140541c501c8464181c0c103040000410b000200301c4a27940c1c5100d54040764a88507a10006490042c280c542502030010500081c04602e40000340f0b150b080004844003490a00e803801c1409152143d4040d18034442c0300c20b4030b180c0c0010340106c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 603230053 1250 603228803 603228809
    0x304020f0a03031e0201060b2209050708180705090406020a1736030a0207090f02030411010c0609120903020906040e030f030a1103130201030b090105031c27 69
    0xa40484121114020000c03011030900000b404181d80b4004d428460164010703441516a80340000192151598503814003030300400001034075447c502c0d090070a1016081d482a00609513031105000c42e040c40a009041c01c8401401c21101540c0d59503c88170050007080038400420000d0440324081c146420030f070000c0d41c4115542d00c04603000340003086070482564245445000488542e1311518500070000c03110136000d4240c3c0c880c51000381a45182d01005000410f0440201d800418003146051140d0b01034504048840702182d2041c420030000c120006004030412000b440c2218000901d032501400811403d030020340404254001d624905400000807016a4001c548616603541c031a81088151030409031400308a8100b0b00c10814422100e82c065600070041480200e800000c01b00b02e48182d8008440c87d010264580ca41e40055503018852104014816034508031158104000309503502550114103807404202d040481c40035109540840445a81c0065004165071480e0741200c000340340c1c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 603231303 1250 603230053 603230059
    0xd2a0b04090e06240409020901091e02270607140105071106040c030f0302100504050303220201081b040302060f0705060705040f0b1b251d0c03060f030f0102030402 72
    0x11006821036200015a14840d2650b80310b01244c0c2d540d584200c940801a140a89410548070200c100040c0d40f00700125018000d030220015022015801800207944001000309003544100980c0340e0362000080000e040d40c00840496002e1034944001c243c481c450040e01900e80103044c451928a50410b4002c54000d131141c1d540c035070003c680c40c440e0945400040e40d0007001015907960800001d00c0740b19048290034000c4c0180c0b038860030810f46005c180c4d40215030848458000008200c0c188a00c5034840303d03450454a40320207012007542c0041d1090300054940340d48040c0030024103d004281400715406980e028168a0302c0e55203144491000340c21005c2304072036a0140b80c1c001410315200d48182c03411030320412800b03694240380c0079001d18158000040550002ca4403071440c1c04c1040204408003080c40c4003080041180c030390b4030800e0205803903500410380d12003440d0005844041142d4134150800c80c0140e10641d02c0c2c44045c000ba0200c03000c41c0c005600341c02009440301c00c007581980a14031450080d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 603232553 1250 603231303 603231311
    0x806060a09080a1a01090204060c11010c0b0708041b05090a0e030d020c15061c0f060b040c0c1505010b0a0e03071203120f2c07031704050a0e060d2a0b0409 68
    0x4107050030680c051401002d0002b940f40c086131001c00c1071445c00210a21060620103c0b072078542d00c03060601e40003101c081d004100b40d0800d1008010b040c024113450aa88503030140c1c403203030030880010900c02010b420b0039645902c0f4402041c100c07409104584a65400b201c04540c0e80c41b684001d10b4480300c90b0a080308008582c100061520b00b00160941003981000f420b8844001c010381c2c60604500c680d07030040d500c00d640c031000b0f00e07803544a034850500a200f10382c0b128158140945014503610340350801c19075055090200401c0390501002c103031502c2001c0c9043c99920082e4400c042403802c8102d40c4410020f5000c0201081030503009645000d01b201c90860038007540c520301200500356100b00380d81d51070031702c541c8560048010801d500880300080d03c105581040e607582e15441900910703403040182c010340003e810081460680750707110041000f2810440540b43c020b0000e000c481882c00c01800c60b403c41140c1e052114a00f4a20020300c103104501d042409854090a10007a0001e000f8504914a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 603233803 1250 603232553 603232559
    0x103080c1902011e48030c020126180c0d02010806041a060a0806010f050c060c0706140108060a0b090103050c09180f010c0306080604150f0b0406030803061009060806060a09080a1a01 80
    0x310184c05da0b115a0184c880c0c080c103001582c011201540d404081078038015683c50b004c00d00c803604c00c2c145402504203000490000800c0710b820380c10410440c06081c0300e203900341c00140050b6002000203030f00c620100c40014418401508881041042c4c03d20194469800203800d4081500100f8075805560300703a80740ca5401c410f40713001b035030641302c0e40452064680c42000050f6508000c5401010014820340300404e00c0e01c29848c80c0100e41d28203800811468208800308030722140e9030f01c144000c0b09821074a4881652650702c400f80c43c0c1404190160013080580000342c000041c0e0381000c848040054111843c480004030715900804d02da540241c0000e0502030000360100b00020114041d075002508018124400b0a4103401032001c103450b001c080b61142d014402e5540c0354805d0740e0056001e1040141c2d60310704101006400f0b03a07150032080c00e01c00000814006268000102c0f580103005036409950b607030580006a90716610f0b80e10042c070a1013419070841c01c009400c040d02c220501040741c1016681d807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 603235053 1250 603233803 603233927
    0x708070206070210020f0408030c060406051014100e1e18150f01200a02040516020607030e03070f1515060f030b04020904050103080c1902011e 63
    0x7041c2c03042001039008100c80744c0c1d42010f55008004842c200005a407406070f80e11442821900700d29000304142e0001f00c20441030041c03500965a02c913805000e40400c23281022505845a103170041c080e401404100c840e00741040c01485e820385500b50081400301843d090640d0b070403040d40c002070740c10b004421405500990110411401d80580921038404468542d540103110401c501101c04504004a000072503442ca13190b400761403101081d55000e85908800c3c0d00501043e90fa020b48001c0c03808803000706003103400e5408109140c008030f042c900070403100305070f403085480c60140c0c06014002003040d181d020108504001d8451040800c00f2003801040520b8050b650100b24501c1a0170100d02200403450403d41300b64810704903090014001400d00d018200401d0440720260400c03501d0341c000281808091500b005443d0345052206a001511031581e0300007491048141480c100090302c4442050b03a45000d00d601003000c066441100e10038802d5050501c00c0b5045c03a10b08200308a01040d10010000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 603236303 1250 603235053 603235063
    0xf0106020d02030901270e0901020d1b0504060c0305070b01090c0e18060f0a38070807030e04023915011208040803070507090605011b080306030f1507080702 69
    0x2c505031500301b180a05450fa0f0f4080256500c502480c0382d2060002090950103244030a0080040c100010b0302d605414200d08129051460b00450101074400c040180c10b030303c14226000d440e01d900d06103032103402515003640d045c018410010302c010040c03030000c140310b045035000f030b01a840d160f9a80302021013168240069481c82030005010503c80341d002841d1410001c052410649004e8150340c8043d90369102003440b601d803140d071094000c50024010694000401e00c4c10688800f0486e2586001d40c9030f95400c1071445400c2004082c0520f114001c1c249a582d6416580c503800c41065070781c1e200f8608030070181e149d4041540c5140c4095950403940c4c003102c000486804411044010503001d9081040e545245010080229a146400c020120701e6140a001030b00401e0300c00c5006006041c03e200c0c803c025114a5009541000003070500c800494014003020010150009851aa40d803a01e10200381050000d440c10b09142c81906144441c640d1a0b806240c0710380c5040d903584e0800d40718800100d03110 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 603237410 1107 603236303 603236317
    0x8040f0314070e07030507090503061306180b191b02070503060703050603060435070605010f08030f0310030f03020a060609020f040b0d060e0f0106020d0203 69
    0x100441400840041d801070310250810a00301078000d030341a0b030014013030001c054480010603500c41c015404a806030201409440d103034039003905101207060750540200e8406180c40e0b1948200e0200501c0e019125612945081d520345900d50407602e058240175240c6c803e40d580e0442241d8240e4014a400b10300360391900581800c601d40420141007881c0103080c00185070074174040011030750740030070740c50307401640b0994900d5407190182c880f0401c03111018441ca80e40e540314041d400202400805002480d1050100384496a00d8044852600041380709090141d402440a40e050548000c06554071202c1d110708201096502d84400180c41020300c810703005604040100000e04ca9a030040401130109114290701d0700302d85080285180c8900d00c52443c000c500445c050100c25a9034000d8002044408041111800e040c0401007020900b032041030054803907020040c81081c00801500d0b40 = true := by decide +kernel

theorem cover : BRFrame.Cov 603057553 603237410 := by
  have h0 := BRFrame.cov_init 603057553
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603057553 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 603057553 ≤ n) (h2 : n < 603237410) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
