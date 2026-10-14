-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1738
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:29:32.184205+00:00
-- url     : https://prove2.me/submissions/5802999f-0cb7-4375-a33a-0885e08384b8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 312410071 ≤ n < 312589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 312411321 1250 312410071 312410099
    0x605010608040515090703020d11040f0e07060c151e051302090702150406050601050c030403110a0608040b060105071401020a030b01120905070e090f0a06020a031a03191e050304 78
    0x5404c52070352901007081171440091440300b12178054400701c0200c2c00600b000310110850040b95034005083c081c100c4d102105540c011281c000302202500c2a09031103103011100748001c24005001c02c4041480c01000600d182d0103590b040c0e149180000d4034000c1841410b040d940d0840d5503808203c454000035042d410488031440d404880c51002d01030341403589803a07540c0700384043e201520040c1d49000150159003e00c0c22070320345203010800c0300d455541c5c070700e40340701204e100c0c130269070040d8100c07000002c8081c02880d0090145034401440705141d0740d0070340111404e0300003000a980ca4641213400700456802032000b00f508901d166001300d07124406100142482d030020450404452606001201107440820304100343c03482255505000e40b0703460002842c10810001d60611800703074030140e0007003124580c0244041503060700d040c0300d8407455000401c0c00e00980c14421341c254202520000c4110318003208500458420030102150000007aa408880c000c000421921584001b400b4400d2020390740c40 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 312412571 1250 312411321 312411343
    0x1a090a020d0c082419030f060c0219060b04150b092107060e03160b03100f0e0a18080c100b040510330804140d1b080706050106080405 59
    0x70520391814610f500d15810300109440903018004541c00050716a41c0c0407650b00c00e50501030401e174015449007809440d8030b44407401299510300d004549601c40e40080754a0b03003001c5480c0f221800b8171805440e400050098000c1e8154465600c45030780b0081d1403820311140117000f813140c0a5031030354050014024074040d201950b480020a454000d0002040012010b082e100303203141910703035460a90086031030910340c0c40e0a6020001441c90104441040700040c510421240680c0c0c001e41e03030342d0008440c80e9040ba0041d0409041071400040a482c3c1c030741c00845488440c250707015250380c0e040d1141c5459030040403188030b0f550010003490040b440036000301d01180c542181e0030440c0d410039208500c46011a403140c00020440d4440101d2661145296610326904055501c2d083c420b942030005c00c00e603001c6904503800c2107038080c4214000400101807105404540b2500c29005c2c0b9104c41c0b01d9968546442244c0404042260600244d024051580244070320744464020713040034035041d4249001440d07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 312413821 1250 312412571 312412577
    0x2160302010507140d0b060904050403050316110303010e4b0c121308070b01030209070f020c0616080408031e03040305030105010e0a030615090e03040e0a1a090a020d0c 74
    0x191380c03000c1401c0d501c1150f9100e552002c00040807240c000c00f0030858040c152100364011b10300030400051580007401544035550040102c441507000303030419200d0300c00d56401c052032640f040c001480000480020f19803c01000726000e180e6a1006c8440700307034400d0103000c110580e00c070000d41d42c0781d804a80030321840302810803000c00780514101044280d240a206811440c880b00100850001000042c0203071059812600d02d81d5200700d01e04007442c16900c05e10049004080c10400a00c06902ca4081400f0a1392130f9405072844807008000c0064680041d200d000d00c504d005426200016604c00050000344041c0024640b100a01e0203c0b851b42c407009046440c800008004000009510a0032a4150348090034140c480e0590744010a100c1702036030f00000c040034606a041c4407410401c0c0d101008031001e100c014040c001e0900c0220341c50740203074412583d04003d200b01040034401240c00c0180f5641d8038207045d4405d1a224000140312386800e640315040ca940c00100700000c8203450151104080390f41c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 312415071 1250 312413821 312413837
    0x602070315020f07020a2306070b040b06150d05010e0907060c1502070b040602070b101d1e070c15020a0903031206050306090102121b07150b0402160302010507 70
    0x744400d08129801206000c0ca1603002070805110035000041e00c0c070310398010b0300c00c683c09511800c1712080300d5402c4498000d104841c440b0311486241c05011141c4103588070880c2c020075200d59a0b0540007400107426940d110b014080096a8140c844000d80784191040101280720b5150541c0c40360802400380c140105070708480e0080c0942500801d06111650b03011040303012103040c13508007030000c0c00748150092108141d0380510060140310f03000703014410702849520105440303000c1194140c1c0d407241b18103100b00c0400c24000448003210305005600501c107984401c41c0303075985808c500c034100080b154003002c03e14482141041c44000307429120001c5c0c20100443c0380580004010300000064480141081107500d0500d9410b50030350060320040c88041d08880c610b0424500c030710301035013200c2550003230956480e0000d440e0084c03940c00c0c50105280f1031100d0b0718020f21500e5640c0740c4820b080d88003007403945031800d0001c0c070f40340d0340700502d4400030600d4036691440c1e55280017403c0d980c0183c48002001005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 312416321 1250 312415071 312415073
    0x1211120117030405210c0f1e010201110301090606020708010e07170a2f060702060906070515010b04090606170a0f0f02040308031b030c2502030a0507060906020703 72
    0x602409056400310341c1615032445003865540e10350301c80e03034000c1900440241c2038407080390840c4020a8845176548141d40c100c0b12000c3c148504842070320200e50344a0201807800304400e04869501c16407640620022500c49104419044580c0c002c1e80708a142c0c5943e00020005981e0511525020702455402403104650040081e55290700601440503d4800c6070b5003181249410803a40800a902c5941b5401c2090103992103044110a0082c1c1440541c1d05000003a10b0315003102118442030340145020f00b80042002407054640002c5c0080320b0310b01c501c1d50b508200d6040c80c010305008000010b03d080e40c0e01c2c1407020705800e40303050380e0150091005074000060200b00c500700242d4000c400200006494a8184088001d00200d898610840748000ba022040c081c68400540c803c078008c1c0e070366200340c07a1910790740038003440100c981d030041050500c21000c000d61100b583c283c01c0c04400b000ea11342150035400007800d1800d040e4040310b140e88015010807003141c00c800c00750010803050011380010f52031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 312417571 1250 312416321 312416347
    0x11031201060f1e030506030124031506030807060501080c0105091011030d0e1b01020a02010203070f0f0803090a02100306060c0602070510022d030106050706050403090806071211 78
    0x1041c056401882844000200441e01c202c000c0a0b04000000d200c915075444444060024401610650300950070148407007500c0c00c00520700600074031041c0c082c80400e46551555480e0850702c14481c60f08c0340d00c2c3c071000008189000042c0042d64043c40c400a025454075080d41d203003400506078207051001c05e108030105640c501440c826507003140d040c12030b00e4200c02171441e41184108424030000034503004008505240015507502c0d448070044800007403d041600580e9140a8060020300580c010882c050000b5441c18042280600c62802a00010740903900c010054108032407256403a0300000da850250f140030400345445807400d0908000c0c05003401d800401000b4845405041c40d500054050308205040040a0156145046c00c5455807076000c0ca128a4280e0807001900d44583c0000c61400d070f41d41902141d040702d1980e11081e02c1d01c0210781c0e416000e030000420a8042c00312a0f040014500c1d82400b00b80d2186110380d5900303a000448601c13003c01c0b41c40b95000468071410070f11540381e00c0c141d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 312418821 1250 312417571 312417607
    0x2090a06020d180f0611010f0606030c080604140105060705070f0b0a03150302100c08160b0106180e0415020c0601030803060a0e0411040203040f050d05210601020a060b01090909050c011103 83
    0x203035103021b6840c0d52400d202c2c0d60140c1000d103002c2c407545240000029207a50f06501c144500111955103001c50f0701c605042009845e00041c4030807103141d80500400191512000810b42c1e0b078030034030564481c00c1e5220b00c6800b102229600c0030104d00030002c1c0e41040315600d846420038800c002d00750108014196004140501074480c1201d042c414040c104409008408041d1031010351946640e00010a1034900a0b900070341c01c3c0f1071500401c036842c0c1203201c0401c00180440664075981b0281800341d450380c0340c075040d00b140c07000380c600265820040f004400e2414490340e400386008500841e0703603081071420b00801030003962190815004400600c00000d61826201c203280d10101c90150316501c450505e0300d00326183e004024503900c554606030119980004c068130590301c400c51a0014000c29842c80d80802c801266641c0c0141c0291076001d000030040d0740031400d901d90614050700082d483e2900101203030780c0e040c0103032025403207881212103c0da4030003458014041041d02450400350740400e07000c1c01300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 312420071 1250 312418821 312418829
    0x210c0801061d09100302030313030b0c070b070c0305040b1b07090209090406020f04050a090504020102010506010f0f030507090b07060212010f060c12030f0f02090f010504080706050c0102090a06020d180f 89
    0xf000b098045421100e0008800b40a990014150390303403a000a071f9141410313102440101d030103040c00e000150f09050701d00f05850b00aa000703028901c40d6036420700121076201488404400380002403001150400344540079041e0000036922000341c08941c1084145080c1182e8004019180100308a14254841020b2640c10aa00a0001d619180341080d10380c21806a5007001e07404c0908000300040f044095040a402a4002c2c1c001700069240d510044816201811400d03002c901000280000b1510a0340b2007580003200e490500c05d115103400101585a0100700241c40d06600480d1250a10140d07601d036500621480c0c5a10180d24500b6034050484078860802824800200740f0310010140203030420421031048980800560713420010342c00007504140746140c0503503006102c03000c082d4020001c60302903500c02c05c000d1110301e26105007142c00350310590790090295020b00a003450382e01c40c132060710042d0946401802405004910041c16142a110303072103101c07a04030008205107080401c81c80f00351 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 312421321 1250 312420071 312420079
    0x20c0304050105091c0302061b071106030720030c011a15070309030501140108010b0306012402070302030604030807020607030501050d0f060221011d091b01210c0801061d 75
    0x60640400000c0c2d00401c440605c030050b450480b035440c105070340416843e11415603d00006040740e414034000e0480d005a02e0020152070b40103488692501d01000919030011003403400054030759140c10002d1034411980e122100795400861215601303d4203006013898000002030f545141061070001404c565900141c081e500040001c481050621881c0400051341d00400213010034115014100301070707882481344c030040e5403030a00d80c0031a528000c203009049a0110094224860710120124040041d2500c01d20951090310f2000005031810301000b0310680c040d403141029803512031070107410854018940b808151600005214980d12001010500e40e00000000c00403010741c40d00400031301c2079035141c42c40c1e43c2c40c05109020a0400500c0141030310031a08042c034000c0c660000c040f03001d00d4280c03184810394000c1c0205001c1f907548200c24008201051424290742e100144c075000115400914002610782c481e041c11042c00e4014098a00400e110301c0c1450b40074041d102485070100c0c030031407003e100d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 312422571 1250 312421321 312421327
    0x307020315040f06022208031204030e0616060507080708040807080304031704050703110301270c0e090d090f0b0a080604021b01140a06150e041d0a0510020c0304050105 74
    0x248040b0741010115903510810441d035803602c00141c02e1781040781b2481300d0a1140e020802040801011040d1a0751161012070520f41d52682e83d415076140310121039480d0445800e01c4400580160140400f02c9140100b90002c0c280c1480b41000301501002017803001804003050030300001540e4207040300c80e41754021500a0700e9031901d10b012280f0440d40326040103100350b55130500c810300002040b040c0450384030716010307041082088241826100c2400ea403400294083e295060751007001000d283d01c040c840c20381c0e141c00503190b0100c2d07080b0318800e84085440d940100f0303401740c41c107821901c403501400101b1442e181c0f2a140901640b80b80c499480b0300c44c104a1503001040c2d203a00d541c0c044d95a02404a605000d03c0024040d003280280b022131500481c0c2c80c911404115100c0d0180314080c191004071845d1680604460300544440c42c40c840798542080c3d1354240c00401c1c90b030651040c03410120040c083c202401e4507052851508962107501803031030b0b104024824000300008101c504035402820700a031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 312423821 1250 312422571 312422573
    0xa0c090302090f071206060c0f080904050c030412030504080304080a0c050303160201060b0306012007050a03060b01030509010b090a0e160b0c0613120e060910080601020c03030702031504 82
    0x1142061684000d4000765040103002c1c2d0001242d0704640718009035907910816249100c40d00301a90300c5403199401150350003a45002141504001d207040c0c80c0030f144503618202c09840801e040310000c0b200c9900809000c424041006080010f649880391249414083d81c2403a894100080c480903000030996a03000500303d080074003921064038407a42140907240c891508800d6401200822031f4141d005500c1c100001c110880c3d090142c0740107800680d2056008001c138002c0d00c4000c3d1900c91003401d5031043c80360015280d5940300a184c091841010b010503400300b881c0015060b2000a88206c1326a410104804a10f450b416008c40c4d104180703480c04950003030710148242c240030810740c400204c1da072140808100142c02800034440d8112134012121130b6962021200c2c5004803492006240e515041d1140120a01c02d14400f940000700030310052401508400060024400c01c1700300000c50740d48001c110302983c051100da041a00c044e00594035101150f030002c1d403501a40c2c090b1000d4100c3c0203000c14 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 312425071 1250 312423821 312423827
    0x3080f09010f05012315090105031803040303030c1202030f04080a03061d07200304140a120c03060b060f0f0f191d04020703080f0601030b0325080c01080a0c 69
    0x60a812042c00c03041101d561281c00b031490410129003803000040540c0801e603d541803079100d400c1100c4401d207006041c15034050044400307a00c040c0403800c0b216070784039142182d9001030004100461082d2070000304a10081070140039074000702000c2c0b1181d481801040026051040b0341d0750b006900400d90f50b51000a1a030603402046c1320341204c0b011340740c3c030951003041403440c201c168014111501d0b92600e00c801c18115449268841600247c0d54106002c10042e8200c00d031010044010001d007d16015138440c061211038507034880c003d540074900c0755000c0082c0321507032256001c034941c203450030b07072400564120403400d901c01c044a0050510000800991601ea13800543e03d0012140039011091202c0031001040080c1c1c10b918420307500a01d4107011340e03500e000c1c0b00721100349605440307004041d03481108050401e103004060034103041e20b43d100103885179000d0001070004102d1000d62104002c00880000709030030140c11981895108030988403580e0f8100703442581c408921035011800b05205103040b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 312426321 1250 312425071 312425081
    0xb01151b150c0c0c0b030112030503040519060f0f05060d020603040501060b040e25120504150e071a0a02030403021c0c090501170705150a02070f080109051903080f0901 74
    0x740c0106841c1c0515501d05070f078020300c4400d1050261841100803510340d07080c1c000c00d20080c03180b225501c410151300c100003800341c00510352050040040d19406100c81421022071082090300716409a0381d42c2c0c003408201d415108072103020f00c1d0b4400c00c014a24060005c20810f81000388044e101e1400417001a042041c2500b202002c0d040303107801651142d941d00b8110480340c0056990f1108569046003c448010714180d812840d80110741c0c6030000d98030140c82200c010040030740265007989080341c01410040c00d03400340700700410b2034a000701011403810840004010030002d410800130420003440d1251980041540e00740c94049070342078000304c2c4004040d8640402c90f04020405102e24100041c800c2c0958042d904031180031404c001200c0a0311011ba84510650060755071007019100802e542c3d55465000c0e0065410341d00450b0901601c5510880d25050541d20000f580d1703440c0e1200c0c04c2002424481d00038110300700806000d464015a8015084403801405616081d0382e0500007140e2800075040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 312427571 1250 312426321 312426353
    0xb0609130609060f0e0916051e03060c04080d08100603050709030f0c05130b1f0c050109060c0905092e0308071b080309030c0d02040b0a0609030b01151b 67
    0x4200091035413258640c4030424030f4800d17940c40352000740c00180f0030b102c00726042c1e00c0410008070011009080c481000b03064441c502c0da1621540c14a007480c5c4281d202003201900510500e10701c035441c1d600d0001454a081c01d10980ca00400c610f039410304c4040c059403106074090710941d040100d50ce03a14240216850440c980c0003074180340030612003806002c4c00f0180700e0142e41d0203441c4664a011000f02813000c0e1035901100582240c0c1d030201c01d01015085505c01e5a400102e8642800e140c640c035280c0500b968203c880c1500c00300d0751401c00800307060300031480c00c00501d0141d48800c143e180c0040c401d81044000000300302807108040906048140c03005030500616440610a92206158100134640000b0080c5500c0d000c03280101c08500000000181e03820b4100050060081208110a004103401e01080c1243c0281d05c42090000540d2100008405000300d6554040850f185007019041c0000c180d10915280718680e040440a0740d210380800d043c040480c24001d9000c034645003030240a091028 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 312428821 1250 312427571 312427589
    0x20f0307080c0c01030605011e140714071d0f04020a0f0602031207090503120706060305030406080a1503030c0f02010908030a09050a0b03070818030408010c0c03030f0b06091306 78
    0x4600d01006009006044034140c11800c5400c8055002c0064044071081d00a4a010490b81c240142484105030110b4000410900e090741d5028818105001140c01c400001c0319031800b030b4021040e0748080ac02008000701741071070202480d500d840480e01003d0700c024100030810f620903000901551101c0420707030014102d4000c000c8510b6901c40c2d00948075001b03e00b0b180020b1b0409004124203c1c41450148165280140500a07040c00840070315003c3e030104400b180c0741074035900e00101180f002d001038001448291903c00320761605201c41003c45481400001c1c000307003800f00500201c0d0f0f03c00052003012380d1140c0030190103801400103881c400c0480d402240c3c184800196002c44c42e5000c0e09850844d03c0c00c0d1140841561144a400598002141c1110000c0c1c103440024604403090912140c3c1c50303001805407032071f1a8450703000d1425100d00c80c004d8004030b9240f2401a00b0550306201d0026002540b010820007090107a00051592050008140c0711383ca1740502c03501d015110f070744608000c0034802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 312430071 1250 312428821 312428827
    0x904050c03060c07020118080d050a0e100c0201023c030d0504060b12011122080712020f040504110f0102031303120f0504080a0602130b1b010506060403020f0f01020f03 74
    0x83d001200b640c0142c02c1240000c3d5007040d0070041d55030b0f5460500680394910043c10606540300000c035450b41020540f507007080507c500b544d0389034903121100c4401d4001035440715101c10b941c0c00060f03d8107254951010924001c1c1e03650441c810000b50903840000e00000f501c00301c501c0c2d44c1d17000500e103014600102d04528030301001e10007044525404440d4500b4207131001c2ea10f00b001c101025003207038600a4000c10000d403c1090340c45a01c61030a5010941081c285200381941c0c03113060381d900c1d2010030741000d42c14141da81c2800055103402c076040c4510070f10031035013800746d403401d070785c40301c40c501302c04100c041c0541c0003078800d4501340c0e0007442031315000348a450300c8200740c0c0da4904003e24000d07103840010700403810310341004800c2c61040003250180c580c25002012030300302a5490b0402540320072851800c8402041c0c0221744080c409008104c501102c840110240c1c0d0034100950071078001a00c418803d007000c0008100684942c11036130501c0c0f1b02100c418000c804058010703410100c8903022800d01d40000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 312431321 1250 312430071 312430081
    0x40f38010206100603020d06052205090f0303150d05120901182103050c0f150708040b070c05030d0c1d0102011506030b0a0f080d080a05010e0115020c10020705010e0306060108060904050c0306 84
    0x10384040708209400e1800e210681701c1c80c0c3c2090700c42101437044001a0810070000b8900d50141740704040142002e0505079020813983c845900f043c14000d41c10b9400100000d8080a640c1d06c00088062001d20940c0e11040c1443c11540d81da00303142940349808030301d62912121041c54082d000350350940e98a40103503030740c241004e0100da8494400c0d1103450508400b05001c03400075486040c405108641c012513501450f11100b0b002c1c1d07040c9888210858480c44100035010500d0006d010708000d8207010313105c2c051001e07611130704400508407180680c0d0440e80341400d0000c44100c944030140031036646007000189841c400380800c040030016084582d44142c2c2e420006080b01d400224911410f01e07544d03030701f40135846000d002e4064400a1081c0104000d80030018040a45c2c510701031481007000d4011034a081c2c0c0c56002140080c29550640383c003582085e28200700d1946c0003400307201c000d0300c110084d08040c034101002034044a80900030902070340e22600007900300401048000080c45005080b181c1c60315103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 312432571 1250 312431321 312431359
    0xd0212010204030b0c0c030405011101020706060e180d0503130305040803070803060a090501050a05090601050909070503060315090a080c070807030b24010c02040f38010206100603020d0605 83
    0x810f10044030740c0301c031444c0024007104003081580c0780c00045501441c5401e1a0200456109203022905101950f003003213034400040051198000411014500c010607180081401022002c2c40032103030f0f074540102c200c02031407035808000c89030b00000e40e415640f107503103107400c08a59901540d00828014800040c0d03010030b0100403800b031841548100c4440100c0c584032004642902d00a206042d04804d10000c24019450405003440d0321040600d000e82c10151880000749003900140c41c003030302059000041c09058102404100702080704d4031b189641604120078126510412504050146940896501105003081c08880000e0248070100c916864403030505c0488507900f9a202980c9405217091114074001424400d00c15601c161180720303044002d0703002c2c8405040c0048840980c980e80e1080320701c00f1081000c081c1d00c40c000030b2030f00500500d541c440c00d900b82d0300c60000c0141954882c0f010005649008042c01e400c0c0e070303d1842e0150311024910051005044a900600e40c8141424501464440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 312433821 1250 312432571 312432577
    0x150c06040b103f0302100c030b09070c0201030e0f0a170f0a031a010f020c042c0c090a06030f080a0207091b03060b03100506031e0405100e0d0512060d02120102 70
    0x4111882086071011200c074000d050380f9000001405604152051a03082d041544011411505410042005801100003554070381d802c5500c0000304094032100000d550b410312400d10b0014102d0000c061031260481e80710350352031002c00010a81400e2070041302d0703400d10079410b07500a1489000082d854080403100a405000701c0680140402000f450b100e182d58800c2c3c00c0403410f150705401519400340c680080c04050068490b0f84444580c1083c1410000b40185628007060301a280142003619030320403c00c180da5034054482080e003800e08100b400412980020713044080c4e48981003541e10581c40c1e209038145117150744a00480303490003404110898903021040c0c8141f1041d50200078268884902c8141c5020940e03045400040c130305028400307410040000d5030040c2414203946d40781070303038040036103602c1c801200c0454081d049050207404401d814003c01c01011400c40180051000d2260014064050304040141201d40403021030507641781c80d03034207051080e00030341541d002c90011040c40780030f54 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 312435071 1250 312433821 312433889
    0x8191a1003050c030102040e0a1d0601120b0604020f030f070207030b040c1d07050307050d1b03200901050a2a03030c12060f0314151302150c06040b10 66
    0x4007441c1442e24840c41c4c10320031202035402c07610001010b07848001c000c0001b4200b12014803d403003040c4082514900c002c009490013009565861a03114a003450811420800941403034096401031044030588551141541d03400749140051941d01e507541e6500700d140201580c006007100c005002884240140c01a841c0103845068154007021920325040491006044034040c0c0007a20500103e54101e03c200018000b1420800c000300d200c82c040a0074501070010040d00b440801c0d40c0b402110700f91607100182e0403101c0344914950782131590000c0041c1040c801c01022008101c0d141c142844a8112406182228a01d40c00000490501480c0240c0180038a07440324001c1080205142070140390740c01401d0641d4080484010520714540d034a0060700194840f10640c1d019011003201404480030039503115020501400140600700d0040c42440000800070041c1420100001c40342544000340058119034001d81008241e621135010a8024100760840d02d000e0041c0114400000c0c3c0003045840d1031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 312436321 1250 312435071 312435073
    0x190312050c0a030e060402090619091e0b0a1203050306040603060207030c020a0503070302150703020309130b150f1603030b03010c12140f0c16060e031e0408191a100305 74
    0x8013a2008445640d51005c6400a600425050008020741004e495034103c1313030a51003004c0b86032500c60380d40c0c00513281500c80410502c1407011140301001c00398016a19420001e40b5001021424540202c0f007160250780007409002e400004135501d626a0380c0035900868002c0b80854440000c1c0c0760043c0007100d00c0c20241e03c50320300c645002c6214079000c030b4000c04813035000303001e080d01d401d0800c01c011917604161030950640c042801030030358035210020038100011030300030000f0301c51400104000c8010f1310220014285c02081c0413140d090407103201262016001d110241500c01e6107440e0440241089410302901542464100311300c003604180030881c140019082400101442a110040c14200301c802000e11681c50020914000181004082441c4a1001d10303030702c6a840d07110541960102903c6000f2940002813915a9005a0905214105103056050720301450080c94950751a03e00c2a940d9010a0a80c0140e0410519003403070200d815034409052a54905241c010380c607405180b00560b02c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 312437571 1250 312436321 312436331
    0x40f0b06030303071b0203070e040b04060c0201111b0a052d0f0c010c1103030a0c03021c0906050a0309020a09050415020310091814060109060504060305190312050c0a03 74
    0x309160210907640708101a90b158036861886600c251502005444240d0701400f0b424008111501c0f40c100d503d20640c024203001d10242068a0208202e941c0c2c0301140c000c40e45410720b070340542408102126070540c01c804a0440e0074000816540c200001d034a0700a240d84502d02515074041c1040c0103000240d14a0810074000d00310300c0b0030503a154441000103200c50f0b00024491025503004840581c0d9041c0a580c2c000910401640401c2c078550003910b0007000708108042c101304150f07041205408050f50746454002c1040f911302d020340764005901664091000120300c4120342ca01c261b00940342c25400074500400bc0d41d0b1020036200900c41601c0c25110f5800d191b00c040951040e9001705c078010503145802c14440c40c0b51404640003400d50020046c0f21031408448040402c5a144071840e5080c244009000154940281e174001c40e0010b1b8271540c0aa400d203407081021400100f40e0019104e1b2100c0c5150100b24503140072903120003900c42c0040958035041c14040c1c1002d102d0040d00060b040f54a00300a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 312438821 1250 312437571 312437581
    0x1080720070608060301060e040f020d0c03060203090604200a0e0c120c09010206070804200609030307060b0a081518070510030c08071d04090201020309040c02061603291305040f0b 79
    0x1511b910205c0d400380030b05082b40c12070001814800c02649209024000704142140c40b9940c10060764811303141d0794031302d502c40001d2000340b00040b47e40c1c551003080c0c1c04855800390126004920569420300c00c4860040d0410000350940980c0d1088412400c6a030801060914160b010290940c11002c10140184200000908164028103065010701d401a501e140515005031041d580c00c5980704209030081814403840c00e0035142003010b044098400c40001c40c0d0400200e00303200e0a20301641c41911035502154040303440302e0052060503001000010340703451035003001c0f0301107162a11070380c815600012010202c03c2d01c40d5142d40720a01c01c40040d61010b905403140e80084400c0e001342d03d142d800b071400c2c111810550b440c1c02e0f400641800d1040c010307642421b00110000d02154103820080001d80c0201e410841c1400507408402d03040c0010381810070107510b0f40b10030000d115409100d50b10a80c078001d0490001d5a89a840c0d0389030007010151706000301d24040c5403400214850303850840310701c0441c2010032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 312440071 1250 312438821 312438839
    0x3c121f050714180a090504141c180b0c06010303110d050d0f11030901090b011508040b0714043002030309040b040605060c28020108072007060806030106 67
    0x3070700602482e51101140d0110511540e01c0c2d03800500050b500148030502103070a5150119200020050f04a00194514203402c090b4032038142380e4070314030740c0d900440c041500e851032001d040c1c41c0c0c074001458120541e10039641c50751040c540c66001003111020106d07102e6074150780014054142d81c400d99644424440d01c2d8040359543d8205120341e0f0210f81c051221607125403095005a580c00c4000d10f02180410081075101d29540c020750701c01640765143c052160134007801e619400e00410705080040074012000400030801103028000400c1d07802075001050030b0600c0f949003003a460f40e510911b2503445a403840030490040c0400e80101c0c5c0101c100600311210000c00030000c01d40e0f60081d000d90320f4942100708010017083c000070860360240d40c440c0c002c203043d140d0401401122903014000d101c080c0150200c1c40d0a801e640a00c01468070503491725400603684241e05581041d918101482094000782e0600c0000719603003d071243d00d100b1810001012507010201901580c0168001c000b0942c903aa0380c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 312441321 1250 312440071 312440081
    0x50c03130c05031e1e2e0e010605030d08010e180a1b06090512070315111306021612080a120e01050105191406030408190c020901053c121f 61
    0x10440c0346d0851800040c2c15240c120280e80e100450443d4203d00a110b01c0000b811a0080341c84c588090b990b403503003030009040030400440c89542e83c1c00c096186600d400030100400c1c1008000c0c103031894044803004501c1d0010031200c0d165a50051400c6111079070401c407170410109910403100000c0c040d0304002018100803112040448014010b08605803c645400356027082c10300a10348101c1d912484401d1015441d400703400c0085245203c03507215071130800000e03d131070a41c2285186580c8034480c02c200c1030405600400c49154410a81034440e0305006c82600c0942b9001c42c3c5541a41c00d1000240155106500c0141a03c100700c2e00b1050b20a560084c50311810382c1c5004400c211405640e0019251602d04050b5074400d01c40d2004070324100340d580c0340324030305560980074401246d1164034040c11444d2102e1401d02405065a05c80811401a20980d210781e50501d4a04100e4183c1000f0005c0601e24419007085850042c10280c520503261301c810780d846250316080688869a041401c1c0b410449d4020 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 312442571 1250 312441321 312441373
    0xc040605031302030f03040303210b06180d1703100b0c1e07030f0b0f0702030708030c0702040b27090601030b0c0f040f090c0f03050c03130c05031e 65
    0x5200d04680d03400516002d9540380d10802ea03410322076810702c9001e018040000b400954481d9403105542039046d0f444030015800502604000d40c1040c04040454541c142507461040350030400c0f821041540307003c03600030143c0c40c5011701070491406020144490f0b1500642c016514074046041003661154280340900803466070b20841d0b04200210000310728502020840040d5140580308540e41d03a658202c0c0c060349141044a200446000700803080710b40f070f820b4590002243c0003070b40c5030103007555520041d4840102000b9143c480440e58105540301c641c04144070040103032096500501d80403240303404047e0703104145080c071740c2400041d8008070702090740fa0480b644035045100c56104c0841d039040642208c1c1c0b60b00003d0700d042c40001001145092684010a40040d0003e400c1580b080002d22150301c00500c081414142014807904690000450b039011550f0300d20324100c0c16003850f00c8018606598000c0d0303814821030380c801d02c203e0320044650840540040072140035080e0550707416210030306104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 312443821 1250 312442571 312442577
    0x19020a092a03050907080607080106031a10050319020f0a0806062215020a0b0c030603030f031f05100905010311070501050702061b04180f150611060c0406 68
    0x5400c1040c0101900022103144160715480d5040c1c524008194000d07904005100001c3e40b10400c3c007200d00400d003c10000b40c0800f8001d0300480c5020740c0003900c0c0c0d0506119000c109aa0341000a080e031800c1c80000e042000000c01d1000980e8421100411a40090340d4208410002200f9131291140902c01c0f1911101001009410954400c20a90f07202e80024020351300700c1c500700078101200e50442c40c2c0c1c20103c4407101100d00d001d4200800100040440c0316001d040d940300346003920200301302c4000d0366807003e81c242940d9035035a0346401190841c000d0340b0141c0034020010081c09206950382001c2c0b0303444071003a108040031990f181e00700081c294500000c0b10100d0074508040c08594801e400004220305c104094500d45507196803101d08503203040300c0340c900581258043c01804c180c010000218280a800c0c850308040c20101502c03401c45170030300c1c0088501d564400c0b900144906400003074449084200c401c0740f05555000243c1044d0841d0b140341c07034900900002621400741c140c10b480030741d00076503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 312445071 1250 312443821 312443839
    0x905010c14010908160605070c050606090402030f070314010f0216290f04052506110f0102030f0103062909090f030f0a030b030a05150403110109030509031902 70
    0xe2103500070015640e040c0c600035525501d1520101d8500700041c0003081c0000c400c003074800c400781092400c49034040c180c40c0400c00b4a42a00020a000040058102c00b04030350040c8141c07074910009280000107620175605000ea8000001130040149101080c1944c103402801031030b100c21a0a8228032401058150400e03500b5480804501d109441c2c0c405202038404103085000803012035002c0c101c080b10789541e01040e440030002040310030b0240180045880c4c400710301c51f014070061240e04440b01d004110801840301041c4007503940c10041030b11801d0840008564a082c1300a0f5134050600c03d0105890003070031300c07402114155407200940030b070080d011091540100310000308611000050464401c0d4402d400600408000900050112907021030710b103a40d42000c01c001a00361140440420302c2504080800e1000c0341001c2100d1160611414440c107071981c4a1078192808018900302200540c0707807148030070806030442c0007010942c0f0128201e80244004036032020111801420081d0000060 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 312446321 1250 312445071 312445073
    0xe09060106080702010207020303040f06031404350c06061903110405070e12070617190207030c0c06020a02130216020f0d02030105040b0a0c05040303021f0b091303020c010905010c 79
    0x800d55030383c0191a9100141c60031070684c000a1075500305030000c808269643d10700300521609445084007000d842c80d95104185400d0302c5428481007030701c5107000d0211040c041f000300d01380c20a1304404003114507091983c9852071501940e03a40c8400310380f104d0250000200c000e4461010101d90f404581d4004e19001c03034806c050051101600d0003920b0141030000014210364155203041100c000701c41c100b0010481d80380781000040015008a5074502c9445500b070601c101511000103132141610400000b513aa038096250803911810504400303047c070000341d0b40c08602d1030760110300707050414021544084409482225203040303125448070300341401c0b10561503a0050901181200c82e0305001840000b4000450300844d007034550449044039003003402d0f010820270707000310f10070044030700c8852034618205070441ea40a55207180c0b4400c401c101044190812100c6c1c9225045146c502a010b0040306150600040c58a00b44190f081c085025004081c09403031a948101075805c203d690513504c1d5200074101e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 312447571 1250 312446321 312446327
    0x6030b061c0c0e040f0e100c172502010b0301150e04030806190909140a020901090908040f06020a0b090c06090112020c03040f06021605010e09091f0f060e09060106 72
    0x185503059001e10000440a07045a602e61041a099810f4200b000c1800581a46c80b2030074440901c0000c1c00c1d0a260000e54180315600030301000b216004030420800300d40f203400304010000e80019800050320031380ca0910340c0d11503040d00070f0011142b00303500038010401480315072143c1c0807160240d89034032044600010b0110b80b0a441d125002180540440324100035506d40c002c10704d0942c1c01505000c0e8843c1109000c206030181c2c02100d11a0050140c1000c01050780081c60461041c440c01508a407109890002e000160701100c0007021004140e60311a643d46601a440300c4544000b039440000044c00507942040110f00202504001001140b4001c454001528204070003d081c00c8101e60034407000f51a18400c10003440075000c07440ca85860113180110003842c0c054034113034561600c0c0d0b0055003000642d0300701c0c6951740004401c0718030100396510071002d503240c8441c0024021240f4100f008a0341c01c00801d0b03028494441440b03006109072515413034000c0750f81800340d42c6c809159100000411034244 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 312448821 1250 312447571 312447581
    0x30b06041a0415031406090316031202120604230106050c0709150f1703070f081306030b0f040e0a080c150a02040e06010309050a140717030406030b061c 67
    0x10800690700c010307000620100e0100c46884810290858a42c08244280520101075440c2070040c0c20091045180000c00b040e101d01500815100e001c0f420a20700d81054050f1114500e940d010000c1151075150504107101e20751800c1e11028041c40ca001711440ea004110034214800798982c1c0c9901d0b41c66407812408a8035a030003142100781c82c0c010301801140c060220700a140e44a00701b09005025903040c2070b0040d000e2030150b4000d5403201070010305a1200340001c0280d5a00c00e810582d40303480300c50a824041503910a03010246100c409100000c0780c26905544460b1072070409651a00b4041011070510040b1780b1542c5040b00c0d1580945d20340360014060790300034904880a201621440c03000240100c0003044181c980829064000c20140002038400c4950ba510080074a4148900d000c280c4485e5100d2803a803001414178100c8904055440c0c20409c07506000b130031800350b00c551488400d142d035910b0750407900540e0006420300006a13000e140c440b007170300d282d105148100c10312103190140d1840144 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 312450071 1250 312448821 312448841
    0xa021614030c15130b09040b010c050a0b0406111b161406130b070503030f0f360d0504080705010e1f140a020a0302060c1911010603060e030a0e0a030b0604 68
    0x1500130030040d96551213001d010303030040070505407050710b51208008200c143d4820040c034904200c0441c6a02d4007107440001c002007420303000411820f0a40303803810140c01810301516801179000c00003a6004122403030849500c10303d40310100b0303a00c190b80380300108900e0b940ca61150000382059071664940e00d1404a0003481030b4009003040c10282c90703840560140caa00701034002d580d150004000c100a408010286035030020f174030064040e03a07161001107603040e11100358848036404000145032243d14441071416500302410781c01c0b105200c03181302006065a001d805069801d01801500240f0781d40140910108108001c9c0510725030000c00e10140f0b400000b000e070301401c02c400c0510010209504000a00e140a00c3d54060700555006081c043c2ca0440090000362142004000d811412004424081d1080300146440c41914a122003034901405180d00094a168608400076030340800c008010140c0f800c19898410301c0400c07040c100001c2c0e00301884046c1c210030b00c01000401a103800d5025540300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 312451321 1250 312450071 312450109
    0xb0612040317091f0608121312031403060d021509151905070507030f0b04050f15130f02030d030e190c090207020310150503010614030304030210140a021614030c 71
    0x5994500030649412110b81c0c1f00300034580c00003980000305240c034018030094203003104000d000000c01c2d68002d1802c1c1851049c1e00da0bc1030302201080c815940c4510040c1002e4000b0010650f0414846031601aa4084009103205150b14001000703610f444009886da1402c41103040580280704680650302640012400c07549030007126400701c00160605500d44942d80140d045e55954a000d180180c036011100d546000c00340c2c4a207414040c2030b0b10640301d080c1d0144000441e5258000749107424400c0c0c02c1000d600a502d406003d003d020181e5040e8046c458501f20001102c1402a21309940e19443c214000c000c0c00340407900a0030b00404505030000d2030300e144054112035800c00d40c0c104c41012202c0680c007454010404260420017854240904e42c080d113000b181d840007110703010b40000e0307407441a40b0000703000300380014042031000e000d0130700100401d0403d0429660381c51020700086d2901e0b419425403240c0c503403030040031600700d0100c4451100c2c4040074000740100442241044a002005c1c5192404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 312452571 1250 312451321 312451331
    0x40e07081b0a0e0f060f04050603101503050601080a030315030b01050d0c051002010f0c090f0504050603010e0a080d05010b0306061e13030c230d1101030b0612040317091f 75
    0xb8451000c3c1d0864454080200c4c84001810090104000202c205240a1003142010180301c4642c0d404990003241e804c00640010b8000001660840d0007011540054594000da4000043e0442c0104105500380e2003030340c0801290109082d008070620b07040c0070191244201c80c00510190400206544101d40100008140195241c0001d44003a490205200c01071b5140c181501ca9070000340542010310715a4100300c8011400c3c949a43ea00d4138061084d540b145484c0c00115666480c00e41c05108041018000c1d40d40340240c80c01c01c0103c41c0c5c40310340c49180346c910b800300000f10606200c042d2030040c40001d107000d140000c50710b043c100d54003072007a08400300d0070304028178200030138180c401100440c491024860401d140180c1c0c40340d200022840ca406841005814410603643d12407001041d943c0215414844284007004a0082c00308426554000c4000108130160455461485218521a039508003885000d079540402400040d0b07900741196009402900d440c05038004421101810118000740e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 312453821 1250 312452571 312452579
    0x41b050c0109290709080c010509060f030c0c12070f0308041110020f060901050103030e1210051302090601023c0102030421050c030a030c0c02100509040e07081b0a 72
    0x24008203c00155510700c059400a00f00950000c0300c1c0ca60150701d904040f0151482e04000d00d454804443c000f504000e00000c40c1c0c000c0d40c0e102000e560307203a044030a005d40c83e46001c00b00280c8076884140a540036203d16040c0ea60700b443c0c4401162859544610003031042070302c90f0307410780304402d020744204d9001c41034805640c2c085d164002c0303041c0403055a84c028051a80c10f070501909098024140c1084c903411302005101087d0801040283e004050312680454407182010504020074500700e540e1043c03c4c00144061510480000620207000311140c040d90b460380b07001a607680351250101c610003180f03805980044030981c6074210b0709991140d5441003407400e4000090032a4412a41280c8460318165001e1844840f1201d0803081401800c0491606000c4506140d8a006095811003003507120000c08004034801c00410f510154003038079940d00e0700303a225000342c402c0d0031009a0500840ca0705075004e0304008005480400c5500030405090760700282c030003010390040c0c0d042007140c020481050000d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 312455071 1250 312453821 312453833
    0xf0f050a200103060501090b09060f160f061b09090e01020909040b0717040f1112030a030606030b010306030c030b040f1a01030312050c0a1812030c060605041b050c0109 74
    0x291569400700c1901c41c00852a00090211901c40d003045040040100e07090000d9003001003114401142115100d8603003224644041c2c1328072400e94020341e000d805840000401000b00c1d00540c54500c02d502c184082c4420948941504031900d84407400901042e008112715401980030100c00041100090320b0701e0207400206c0c2c040c0a00341c40c2214510040c0b8200801c080d030108100341c0c0000c03a000c2413905814561900c0100c2e0300d8410001d04068100900410b040e81c0301c192241503110b0240589440ba40702c4000540140114410f18001c2424180d079006250301c2482200240c0c0e42c05191a03e109007103407100310070020003c100325034503000c030306964010805841d40e880300f09a80c41401405581140b4000780140d01c08a1140344c000d0504040c0b043e15840c40c416100e0203940c91030b2001040344400720b6007031409074034ae01408a10200340001c8080c5640b000000ba1039501580741030100e00e598a090004841c150200641c4c1840700012141c0c640b171281c001030500010240011490b105240c03202 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 312456321 1250 312455071 312455093
    0x8070c03020f0a080306040c050304081206030724080105030613080d0f05010e040c0509040305070b07020c060f040801051e0103080a030e1002070201030f05070f121b020c1c0f0f050a 80
    0x1303459110010080040f189080e02921801101600d041030444c2032075900e15149001e01c146140d00c450ba031000103102c0d0b40f0308100302c4008010707800d01d4481d40d400c0b280c554002008a4101d030000542c00400114890400043c40e40c0500b41030140e0a194a07031503212040b02d0f800a015900b03100362102801101c81102c2c2c080c01c1c1c0604a5035540380b8150800f4544400080080c2c2c1c0224001d00c400010000400c1d080015150340302e4216000d0216561349007002c034100f84c00e03c600c0c5544080d000c070b0b40101c0c45002c3c0d00034000b9039007000002c000c1612800d15070ae101c0c480f01c07503148110030650741c014000958410041d2540300c1c40c9080c0401c2400700c00f9081401e01210540c0034449640c0410a007056613031500400340600083c041c100014140100001c0003041091100400d04c026035542e19200c144a130b12894411001c46000c0b1400007030850000e44803001c00841e07520440f030482e015941101c64098500d01d4662005d80e43c1030125042e03072403c045012407003082c0e43c1402400d5082c00442c00b001c0c44 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 312457571 1250 312456321 312456323
    0x312040302150106030c05041404020d1104170a02150c070b0d05062706060a0c0f0b10080f190309030204020c06040c09060b03040f020d050f0703060609050708070c03020f0a 76
    0x40c014080010200b0201a20141d110b0020141050265104180c02000300c0303003905c205c43c3c0c042d140c5501fa8008107010344100454040068031781900034060810110282c4142d481e0000360300d0440d6041e0b004c403560b0b901d010b00b001e0b6100d5003440c006e40c0c1c00621400140321340e03071402064a00c0aa5240d060180903084265800c405a031a03400708085803500707100d8650780404103850401c2c035042e4401300301300d00c40005003903900804c0300042d8008624010f030326809040e070713210903014080d40440ca818020308a00303490a60014800c03000c0828514004980c00580c4c040d008014120245000d46440001c44c0041041d000d014820390040f0150300ca0303000410315182031200501c0c00f410145400c44000708207601c13040d2210b180035014442500100d013141d8125070407443d100d001914900001d29107500c960402402441104030070840918013003100c4007120301584003088180d5951071003170169001186d54000203411200028400c41c00340003620031150080c4101c800115004000920b0030240d004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 312458821 1250 312457571 312457573
    0x170d0513120503011815031e26120901060305192d0f17040306020403050d0305070f0309083001060e010e090a1805071701020301060f050c0f100621050c1e10030902040c03060312110312040302 84
    0x10c3d55400b4049803041c55030010305821008002480c0102941e1714001c2c044500404088060100000b88035108442541610400c07140a0741c41e030f034a01d0100c0003940030344801c8555015564410050038040c0c421584a4102a10b406d0885205c5903411402810b5002040b500324006200800c0580a104100443c4c1c0104004d41050501e4100c00c0d5024610164030107030070080e243c48100d451343d0340024174040b03070074040c2c80700050364607030b070303803082c01a117242d40501d100845890209014003c002400e0005c88030508060106800000403a90170707480240100c030042024641ca0202c410b101e200105440821842075649984148045900f0301c13a0800d03a91840b00d071180f20600c41031880030184255005030b60140220b030030309980d5107501c55000d0300c40e847c40b6108800100302001820b8031040c181580c020300e418030710883d800c0b02070000c0840c0d0300300b40d0055160004603800d246c024407510099176081005540d405100e4a41100c40c40e620f5220014035020174052a501c0201c2a19810300980c03107a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 312460071 1250 312458821 312458863
    0x6090308180a2d021c12050f0313140106030b06133b0607020d0809030c0604170d0513120503011815031e26120901060305 54
    0x246800d015001c15071a40016508a05000c000098100c07403640030101e0461950f07201654070700e0032104250740e901000381d0840380d886420070502c20070380c58840d80c11b8400d49403011120300c203800444481c011540702d950031900403c003054103007500845c0380c0d6800b40b0808445810030070615407142500c0c85039008031440103403503092024520345030104004141040004000210503142148400c0e50404010508129a00c8000402c120581e4000c0b07884400c00017250214103142c07400a64503070541448000088034540401c03007641003c421540d12281041c02407100e42c0b200d0f1904503045414100c01400d0503000c010b9440003a6442c01207520078440900710501c1c500e61030a08548003007100b60310b0401c020042005004050b10352004820584041c07100180f9141200341205005030507400151070152084400f4543c2c85450545c05602845600c0c0200410080b50b44400c40861200b00c0041c050001d2000028040e4100302082c0d104503028004180e0659070303100c0d41d0401c02200c0c4112019080c607 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 312461321 1250 312460071 312460081
    0xd0f0c030204200912030909090d0806011b170c0d0305040b0f012103020109060e0c030106050609030304060e030a060c0f1b080a0c0c0906170105160c02091306090308 73
    0x900c10018002003c101103000e01d446060442c400340701c3c1d4240207114015410300904480c1c000c000380c070081007015100800030700b0300401d0b459a51066146100000d010140002c03025480f1703112800c00c01c60f54092000481005e99540a0042050b03403648910724002d10150040000c200f00038a42c2d500c2607100098142400e00300400044030040030280f240800000410601d8001400b21809550011070f41c0320350000c5150403030140c90000c1c0060200783c2440d0f031005040e60042a44010387c0011002000981c1ea124148021809499501076154005000c20414140140424071800100401356810640c5039607903a4100d410300044000001c0065156400460f0801c3c007064010351540380341c00e01d80f407041d51442c4d4030b8825851000100103e0404100030441000b075603e0103041311000c18010725032180e20341105030703d000d08103028079800c3c400840c0c040310481d00d0407030588085903903000f00c0b0281da030284116030070050856040468142c4549010501c0c41c071440e810749100e50385080c603a00305 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 312462571 1250 312461321 312461329
    0x30206011415030c0f0304120f03110a11030903030703080402120615060d0e07031101140301050901050609150f18031c180512070303031103010303020a020607020d0f0c0302 76
    0x580100c0074912400034495420358941c1c01e60341c1e1282c44000c2a5950741c0d5040c445007220f0048060031003200d074000c410b11003000344c14100c4810111f0180e40d040048903800740c04030156440c400441e146000704110707801c0c0c1103200303082c00e5042410010071a8601502c060100740b03103600c0804150000b6401c031307003404110310384031800c15801d120002c001e00d581d0130100f00709449a450403103101c0c0320f450002440722a0307902d60b03000540c0c6040550140d405039a90390804403d013401444078503000900d20881c050500303490005030380c1a248050104e00141e0b080c40213000a40d888096003c3d030118000200510b114001c000501c0081c102001a0b52030b42c6254150149441c4032480c500c2c0b00703402c65100c00c64030b0703200c0110010620003e407030510381c49000c40c05200144c0c00250801a04410031072403a0b01c00c1100041c1c80c80807684240e50400420072009201a100c1c00280001030040c2c020024010252a01e40047c1c00460b0000744800464000350381d5111000c4e140c07407001c90300c0440504d810419860 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 312463821 1250 312462571 312462583
    0x70509041511070b01090506010c050d090302030c1009050d03030212090f15060d060f020f040e040b0a0c140f0d050108010f061413050901060503010e0f06060a1503020328090302 78
    0x2c0b2403008508010303440d91501c40500050286c080a1662000040c001e40e100b034101d41103040d0090241c400f45c0c1001c08008112160500081c0d0192084070032200c1c890408050901000d11183d9030303000e045007070004202c00c5407015a400e40415400713005c45441c040c0c480542038001c00094008250000c3d901c0c44917824681d03034202c0720341410111800c10000f903c8a41443c009650300c118002400c0103001d0101d00280115102d40603a10b501040121b20f003040b1800b0b45008a0150400c00300c02d660b590001d0046d12800401100024040103140f820100c00901078403821950300b84e03c50400b01c0911035081100c0c0264132201280c4c1d103035006940c0702e9101744502006003c4002443c00c9502410f804500b911852100144005a44800140005200b940701001400b0010000e100802071271000701d940e9400c02a03c02e4180c040c80012a25615010900000b151103032607400c210102001c030107030b00a410041524080d0120006c4201c1d0a81841e8888200030b5041100029030b0841403e0003450030b5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 312465071 1250 312463821 312463841
    0xf0e0d17071707051b060702030409200901082208040501110f0d1b170909010f03020d02040905011808030912180415090e0607030c0e011e020705090415 67
    0x121000c0d40d0080200c0310b0841e1039038000b1041c148203a41c1d80601c40103417a96900070a08100714058241400503455002c40144226000c2d1003003800b4119569503040484030020420b060842020000000781c0d50040348565404500300b603c0074245110b101c140b09401b850400304494107030002070180101c2d0303000b019004940110000800c030201a0388200703036841d00516880303014800b44242c0074205d41d06941308066200d900250049280d13404072041e003600e400881d01c00e4810341d092400800e91503a000b10040071250003d01002a0001507000d200c014800302d103055540f9500d522001040380300c404d04045806100b00d503403656900c0c00481550810401c0c1c0075090101500304400c400d802d0402c000441198411900014902c0224250040b25034032684400c40c0c440c20240b41701a040c20200706584189081d80342800300c142000700c03ca40e02c2002840150100d0162a126a01c07402d290002d55800d401c1d6004a6090548400004921510407038040351448444030003c01d983d14280114aa48 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 312466321 1250 312465071 312465077
    0xe040c0306051e0601211104030c0b0f121e071706030a05070302092a0a0306060c08120a0b060c0714062703031c090203011103010b0d0f0e0d1707 64
    0x3800101c0030f44440030a01500040c100b114030701d4514205030154105050b08a52070f00100801c45480380f8000180e0018881500c02c0c0448030b0340020040c00742c01c03c51b80c5040444003035616003941882480c4078110040c00b061038021706802079001614200e03140c103010301c0f03c030740718000081c450a42129902d0401040180640c203d48004c4002030b000080c400c051300d60450700c03164244c2d502c440111240b0391540800c4080358074084004029074070a0020030340c01100e56010f004481d281c06050b03e5555085d40c000b823420b031082114181c42620082030940140c11040e0100781c40700b14a0000e03006400031040c564640e0481c550070051403605603034a0107a11810707600c850500154081080e0020b07500d01a6008001f0080d50168103560300784220303210181040c88001816850020722002000754a01c101d0203980f0781070045480300000c40c00c1c0c034100c030004924035107032000d80c40f01003014160038000340150700d448442900780c10f0340a010510740c034145540c1d016540002c0312090907411a014101600b4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 312467571 1250 312466321 312466351
    0x20723011d0f0304060c05010e0601150f181202040b1302040807080a030806060706060305031611031f02090406091a090a0b090a0c02031c02041502010608060f100e040c030605 77
    0x90300000f00642d02210103504006504409900307000340940039041461503680a0340c0c0c004104001211aa25041c41c032030380d2014008500b40f841515520844600e040d00c0d4502c502080202d0140403048610051019001052200301800801c03000c48001244282c030319001300f81402442810401f440003005102d00401e150045500d024111580141c91980152000180300e000d100c415000b4030010740e13100040b42e540d40360700d020307804075031209000c01c44804501e071400c5295481c0c00600300346c02d0062050f0041004d82d805240700001d40c81421032b2b9030031030b03216900000c03842c02e50722417a00e10340d1a1030020050000301500b0403210500081184035400e180c81c00510f0241c40340413000d1b502040d050390000e02c9d860482d0080c3c0c03540c0240c001a03007000080301070308a041c00c2e240e0060701c00c440040075040400300060005a00740c80440c05050980d5008000181c02d803005030011325080100012009482034032427004504404080b201540c0d00100c80c0020410416188600c03640208115101c0074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 312468821 1250 312467571 312467593
    0x60d0b0c0a0e060306150f0705030c030703170906010b0a021e010603061104141915021501080304030302060a0228050301260a150b03030703270612020723011d 70
    0x101500c07981480341d04c59440480d0151100040c08108e0313406030740110890340c8580d41540e6060350b991004504500049484248810520800c0003107401242c1c5030002c2c184aa023015040c3c3d9554200052980451060b1010f03089200d40d6094521590040c603130001c0340440c15402c2480986524407100038100500f04000c00645038840364803090703a80201c494081c141d4030320b455016141c080350040d801c240c0303280103d40085900000c0c1d44810054220a5001a0703917102070a68490280c0d11010303001d60080c00001d000516254001c10700b090480030280300d04c580310009030050b00216110740300424400401030101a41c200342005914001c2d480c00c2207034032101e10307802e6102c23502d8040081403800c106400546100346504009c110301d034090110707501c801450500814802c546160742c0c555003051026106101540700ca0482650b050351201c040880040341c84e40025801010195a000c0f60312841540068a0809102d06081018000300301801050400448a000d90150407855801411050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 312470071 1250 312468821 312468829
    0x806060907030e0129040b010806030c090a0608330112060509070506030a0c0909111e0c0102030703020c0d0906230d05010e01060f020601030317060d0b0c0a0e060306 73
    0x5035001c441d91401084082a086240f4050003c2d2034464217046000076181e0101c1e810004100d10007007048406215032640440195400c0318151050303034254000308454603240c204952010342145109400003034160380e400e02c00d4106104403401a42d141084407402603001c0100c07110441c03580f494000c04140c2e5141c44120080389840c0003000300100d40302e01c00512004d2052158070002c1c680580b04558919101080e00010300700102c028010696800000c2601c00706441640b9401e502240007500c3c1c2100310390304604420304a1000311010030100001c01d6403520138009180694004c1d100980c40e0750103400c142d030501051181120801c6a0070000704091540080894420140e130100b60364550042c070001044d0780700b00a601450707507003000000101705001d100268101c858580c0c030b2018030001420101c1c2c440c0002e100c0a000600112241c103021110030326626044600240b640d6050407007a600c100c1ca5040841e8001c22001c008075403008510703000440349038002401c4603102d166241540c002 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 312471321 1250 312470071 312470089
    0x3051e130609150f1b03150509040c0b1828150504050a120c061403060621040f122a02030a0507030516090902060d0e25030606080606 59
    0x7401003074461450009001e4a1015442c031050302d080280702c0c007108200c010001d00078200c2d07200008155101150541442880381022603041c240140c1070036840d160412000d0000504151103203030a038000016140c5600c0c0c000c0030151012407071000300001010400c1b0482401442c600080008492850900c035525440c40d42030303c000b88441c00c88141c0c81f44044420b40956000035803c0140d40c4004107010703580b039070280c000358440c010200707a007a01c90f00e080700e290b0415100021518000d00125140e807030000301904d096081070314814003684145218511503102501c007070b2400410110000180910940604101c039a103092031220354819502c0e0261204501406c03c0741d4201c41100c078011550280580080150000122621a600c9081240e21415406000c003c2031207203a20004c1d01040601070b20000d9500180010b08008004034044050185013032500380c60f010b0081030400d504d45040d40c071401940c4101d202100d003411840c00000720340b0190040f8402c1e9001070104880c540d191001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 312472571 1250 312471321 312471323
    0x7060b0a23130e100e0610051807020a170304020102060106021612080c070b030123090103150b0603011514070203070303051e0a1d04050402030304060309080405040204030303051e13 80
    0x4404040482c003201c000c000d150350601d82c0701c00c1c064070344400740800490b00401415180c000941c0c6031625000c13146501303e1500d214464000001a12500c0d4801e0545015544601c00740140ca050010b00d56070f01c84002c0450840c250480c5000c001e100655904000d220b0160400380002c0124881d20040501c103901c141c450a0101000101c0030400c210304d440070383d140c19840e501190701c56a10703016505601d401c2400780703252041000c90740784c003110a403075001451100003402039006a400c5403140c001000c03d003a811b52030113403142201c04881d00c1c0c41009600802e00c0c80450304005c4170104000f044100e1003c2100c5425806000e120056640801c12004407581400d05541e194114640b0005044100460507030801000c01c41a4403a50000034211075102e4000203240d003200880100411074200b5100a03406900502c024080d590003039116070141802010000d0900d0796907000a01640e100c0c1c0c200303e0010b40c13900240401c20402d0722100342c00b03000c005c0d5440340324a810f12600e1850400054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 312473821 1250 312472571 312472579
    0x3060f1118040204030206121806071e2309041d060606031f09060f0b0c071a0c10060504140c0a080c070b160f05040503070909080c0307060b0a23 64
    0x101202403960b4990498004550250496441d007403e01060070020204981c1c1030b202580c046244100314001054480c4110002d40b80c0e4003441030f03002c02004090407026003400910061080814400844e4a02004140e92820381d0076589c0c000c4409001c1030355240e540c0b480e074100000c80080f800903404210507a10010940300f0710f8581c2d56001d2040d4030b0b000404580c01182c0961240800e074920950082410f0310700405000420541d6040c1da03404502c6640a01005900580d8040c402000014035a14400c2c902d90320881c10302100c090f941341001c035490185000540d03101010001c034180343c0180c3e0508099003014001e01d103000b280b1544607200340c40346c1100b001400c0e80000d0b80c0c0000322080d100e2007904010b4034a014913011544200c0d11000510400c040340392540781150f002e00c940101d4040e02c401130081d0503a01e2400610320040c0044510880300d0100070b0020000c844010006002e01d907000d0765002c01d05401e44424440758056507008034001845c004c1c20f4a03401e81c064050750481038000e80d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 312475071 1250 312473821 312473857
    0x120b070903020a03051b15090405070e0a08010203220c1401090b03070f11010c0e060f0408030f0d06060e0907081803030112110d050d1202040803040306020403060f11 73
    0x11585003546400c001d60103d034a0001105000000484103151490080800101e04041c1d0800a020710b0007801c05040b000100400e01642c2003680096410543c80c2c1060040c901400c0005080134495400a845580d80441041200f418008100d00306807000304480c129200c2030b88803054440e00c14012112450f0300c0900503507159200780360142c01032030542d403040d4590410030707401031449406074003250015001e00d40f850b10145061003003198907166900e4160142c1450024480c1d1a0010080500f44074010b210016a0b10814001000d035900480c1000760343e00302050030781c2c00b00c50a58002c0420050741e80303462103c2d504c2c4c0d0915541c21007440e0401d8581581c404101c514961000c00d04882c0b580404400000c00403000503070f00b41254032038220075030343ca80980b0a004015051003c0a0801e510000250303034110302030455818091340c41c2da0094a00ba0315000202e1031584554002c8640960004042041c040144034445e00701c0400030f002c2c0304c111179001e400e09140c02141c0c00c50031040d100c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 312476321 1250 312475071 312475081
    0xc0e0601050f03092803030b012c010302091003140c04032f100918020f0d02090a080a0803041a06030a080f04090f060807050303070f110d151d07120b 66
    0xc111800d00c40c043c820003825806120000300c80705d1003001d80d0450100c3d0525042e600e896000d14403a00302941980c0101000080143c001034a011020740d904d41030603820840380c1241e4464900c803031800144c54a0110b03103036540400c3c00c00180781c02041410402c2c2d06100500c000ba4400045586440590741c10a101d40c0c04002d110203848903a004d00e9600c42c28145058070000e41109804040f586000c5150080041041c41042644910040144c221504100501c10402a98003500d0740140251540d080c06443d0b00340540b0303050b100c01c402c0c2e818040110410040182181c680501d40c00c40028252540c1080c20109a585901410040c10380c01c0c01700709c0859640111041c0c40051554038801d012000c01c43c60350100408243c0900000d41c0102500403485080c00030031a0b000d55480131041c8448441521031034145904440c60941c04040e01640c1c2003c120340640ca01c645000d82c2034005942015040506805046181d045140b0741024108110740c2801401d850fa4240e0081906030555840d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 312477571 1250 312476321 312476323
    0x20607050304060930031d0a08160b0f091006083a08010311010e060a0323070302120624030c0c03130306110913021305040c0c0c0e0601050f0309 64
    0x7401801c403a410800110840d100c54410143e1082c0c0d410380f0308000c80529800350307540c084030860481f082a03200500500c001524640140400d640400c2c024034012400d0741c52022281040c0c54100c4201c4c0000148070320660b05000040b0b42032101e820400c04545088407690302c4010b40b00340480042d203d02c082d1850300c00500069000c249100700d0242540300107440203082c040081c0000d13190800ca0f215114040c0d409540f4013010500010a01420712441140c110083e110f011894140c13090400740760307040f00310b14a03c1640a9451600c015803a0210700034030900869000380b17a24440c003903804858158082003070020110b13198500c4180d5880d50f078860300c284244242c4290500f0780c070002520500d07400c1d14403030410589105450600c603090302404d968189002c1d011056070300402001d96840780c3c07551a4002d05551440014042045694030000b50803103c101d1506800305a94409400c20002c10045d864090142c00d541902103081401c0000c20600a15420461044000001c13900b9118 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 312478821 1250 312477571 312477593
    0x30b0406180e0f100c1701060e0603180109031d04050402010504060c06180309050a06110c0d050c330705121e030c180f030c06030c0708030903030402100206070503040609 75
    0xf08042103940c0d00301080c1d00305006000b02502c0d0f100107102c10000f01e035400315200e1554100e075110398418501e119050100042d9520150a5041074200d808400746203a2082c060f14130038a019454960b910710910884d03800d80d12001c0c0c400b0388180e18100420005030380008c295402c0d130380c00e4500a00c4049580c94000e0007030100e1000100c0d28800d4061100070558445162401e80f00181d51710714045130b07120410340304c10180040300c503803582200301781c0700d010300340341e552803034080e0165007140c52020400c000b14400c0c0100345040c6207002100188500f1000c004c0b03040042900e05001c2841c43c226041d100e9544509102942d01c14443c800a0340302500da25124421b0340d44c0386003e110503547e041c1140b05074183ea2000c40401d8120800080b2401d5900d1b152500100b00c80c0c3c06405048462811000c0040c0c40d8401045031141c4041401030f000400c2660300950300c101ca00700001c56490a280c01080746a40f0302814280c11580001c041260156022041da0782003035000401003414006c030319000c94581 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 312480071 1250 312478821 312478843
    0x12030509030720041808190c110f13020d050402030705030d0207030b18030d0b0f040605060702040c180303020f01050f0c0717070605090d110c060406080a1119030b0406180e 76
    0x30304900ca50409000c01a070040080c0804811f40c140c00c0f000c3c034001138a20012405029200c84000d020420309400d08085e00342110100914800b481440a029403040360041200b2502c02d030f90701c800b0081142420006880a404104c0040001c0d02030b40400940e909001d0000501c0700d4800804a40480c5034005680401c2c206181600d8998200d14198401400074011051007070407900c09640090030300340f10b00025284e019190501c0c0001c5902404081c252200c009400c1007000704002c5011041032071020091446a405403001c0102108083e003507075409869410540000014050368000c03020859421551003074040075080004401700c01c55010780c403c098215801c1c0800c029101b8004203441007684246d1301c031200d42c000c1c615209039564662180544d00444c0c03c0005000c4640681041e50780303c0d548080100d03401c04541c0004e400b942044086000b07904d25070807554006901030060009900f0180c1d0200143c0e850481c0110192428210120100740d5441541500c00703000d1003031a4280c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 312481321 1250 312480071 312480101
    0xc060204031208100504020306010e0405060d0b0108070513061217070503030c0c010c020607020639040612020309070e0603011d0c040605040b03060f06120a1203050903072004 77
    0x442c08600082d025580c00c480400b005400d566000c40c0d280341034403e0724000c0c2c00c113944035101142508207000040c180913014039032245040044500144466250728043c01c90b0070301402c449880c040520040c41c1c000c01c022181281007840500603120307550301c00c6400e40d80141402d2038995900f172860707440c0d100e041c401401c540000404c01c07001151000050010010440003045103962201080348c50b1b40c4181c0310400160001e84c0412075552a08410b140300c400040c803003c901084018080d608884011401d2615120118042042e941c00603017680115003251020b47c61740c9854445c841d11594a4040c0700b07620302c82d10300810a50b450951004000d0070880c81490340c5240c5410b0300f40d91343d9410781c005c7c6100301e042810115840c01c140c082c00440c4d40c00600144030940711900765a5150600034045508006c04100c08510f9000801c118541180200f03680700c49400c0c014401000d03543e000744501c00580c820407440c40084c0300b07440c0d400c800c0d0210074811a8140558400240a08804c12650401c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 312482571 1250 312481321 312481343
    0x90e041b030c0605070c08031309020d020c07091b1404260313090c030603020913030c081306090f081b040e01020406120b01030b0631080a0302070801050114010c06020403 75
    0x40303800a00410410b401120020b051b60780d58500141d07030784100c02c850041390580342010040ca41540c0c014200f03a006c007002c05420040c2c07508103079203040f0103940048070098440c0c92030495842e03200b48402840b8910700d0249901030100102089078070071031245400142034190140182e0304580e80c101c0486c0c2c040011b90381c3d60001c6028280f80329a46026075a04145000e06101c1401c0c084c0c4580400c0700d6001d40300da5119a241b4100084031801d0450582c00d004c608018017000402c50401000a10078080700a10b10a042c00d000401806041d04039013602d56600f90140014100006c6941030380d41c51101c0940903140340001301e00a0115000d0080e010b600100300402c0090300702040450b80d1110032003c0202001210046080d62210f0544a0308500100180842c1801c0e43d102c02e2044230740702c0300409001004541c100c201c140c00780e001d54455000f0301c00300b404055042c4000c00c003c1406078000e20040d41040b0f11852123480030320125041c440c00c481e45204001a0740c050303d00964101c3d040c846 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 312483821 1250 312482571 312482579
    0x4020a0e0708070f030209011409060705010c09080705060a050f090117091b0f1516021e1c0c150c06110406110a0507120f050f0c040b01090e041b030c 66
    0x111100060760300a01151541c0100c04d01c080c800d01c203031a10768105135116400000003a80f540c0b400d80c03018580e2500f10714200300d81d2010031024052001041c10540d2803589180c5010f40039400c0032099000b02c2d109e090200000304645a01c8000d40d00c01070f0061001c507544812010040e9011558500d49042c490050010090f0480010840001000401c0441c00501c103a6000700001480a10003da50140310002e0341050b140b90305000d059101c89801300e07100c0d021a60340004418010000781e030155100718240c41c180d9410582e03150b1215164541280900510a0359000032088150007865518100e681c0c0b940c01040c8101101d032000c07508000e003004001a03600000384c00364410b00803400841e013516081101d804001a1404d00c1d0340d000000362648600b0b0800003842c1510190068928220204c94400403550502c90600c92034600130050141c00e140b1018002030b03c010011301d40c18482001001c20803020404a078503803061380045894203050201c0d00201c1c580b145600040c10382819001d0201d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 312485071 1250 312483821 312483827
    0x70b0c0c060106120c03060e07030c121b030605010e010c2414070e1005040303121d1b0406050a050d0f1a0601081003080d0f0608030705011a0406050306040b04020a0e07 74
    0x8504c01040a000c40d44410000f9400c3d207140340b0170024485405030010701280e201c0d50050500945505e4003071b03161100d0450041c165401d1041d400118880c40401034022505481508003c1800782056440b007000039001804c2081d030000c4c0900560000c5e03055200b090ba030446000c0101042500401c10814102c0c0088051070b41105d00340b000c50244a0000c02e00d28080d446038a84800d51342d90301e8030b07040c15a0f80c12646034005003041c03200755480b9000781c0120b60900c900c19070142c020200a142d90600c00740c12104c503000c0140c2c00d41c040d41c0340440074030050301d4217820942030b28010748103181000303002e203408020446d01a1015155103802142c00280d442e015a01d03e00810007666000c1c1c0c039846030307110f00d007407019148401080701c0006c0020703044610251b040200501c621081c0007030410386d100411402d40d030014208480781c3e55210b039103039184414101038184140f01034508000c0b050a000219030380e004003030030140c16a420100043c0440d0703a0041500040c0451044081c59410000b01c05 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 312486321 1250 312485071 312485087
    0x60306020c010c050720180106030504060507180603110f1207080603011802040b01180603020409050a091703040f0204060f1d040b0610030f020f09190b070b0c0c060106 74
    0x60155003002e025215441c80344042d00e5000350055480c21b03010351908145c0a0000d00e0a294503082002402c92203014265000f10f02c1c000d01c002c5d107000c1107178681480c3ca10700b1140020002ca0500a017482c144035501c00c100500400d980c40c1c0d0400090344c007900740e9148480d00801c03d00090001e0001581c05030740182c04010707400b5003043e40b10a001a200d0500305401c0e10408266041c840c00c02440c6c0c1005460300303401925014006042055000d510500f0600000c4160b401c801d0219800040400060820307215495002841380300401c48850a541c83c400a0132028006071040031000c004201441007900b02d0800d0583d0061080010954034040500e20343c140d440307046007060440ca02c030382c0080e144079070f100d2081c1e0740080502c000382c1e1110104450040508400b60405a03201c0c10f03480c1c0d039031f40c40c03000300b007035000664036240c64500500c2000300075100100700342d44031102c0d26802c1081103103210540d03000c0b03903000c2c5c4400021b0346c0b007600d4031b0f00320300610350050300a00c6202c0c000900705400202d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 312487571 1250 312486321 312486337
    0xf0917030c16061e031409010c0f0c0503030103240207060b09010621110f2107091508072c04050901090b0604090809030a1101080a110706091506030602 67
    0x781c0b050080441045141e0820398407440d0085510152800074481500500090300303546414000741818819110000380e60b41110000900e0f075541d00c0e040e07045504288842940d00181c0341903908041d03169149030701c9002c18070004010804016a0398110300300350f04101180c0e16400c0303085440f01c54a0502ca0083d105a120060003481d41d90004100700b071054240000f249002c005207024954410038441c01024084401d00d280d22051042120000442c0000c020721103280c0c81c002c903200c185144445010303030080c1c414400c0c80741c040010481d2140002c8080c1184850741404000c0f65100319059582501c8400024650300c00c40c0072841000c0b0b09120743c407040d910103940401c44d0b60345031030000e400c82d1403441010b05401c03200d1001560524264107c900c50718410400315007041e4a850220789440d800303280c101e0b208203120f820b11500d0350f1311001e01c651001164a051041995022194409100ea0303140503013007a4031414003030103105151400700c03640000b8a00800503250349007081c00094000540d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 312488821 1250 312487571 312487573
    0x30201051603110d2705010e0d0213020706050108010b3a020916120209010c060f020d050c0a11010b0d0f02010306032411030103020a0612090f0b0702060f160f0917030c 74
    0x900400d54240246402c250703901a101c41e01d5400048c400c000c441c104020040b64444040108440c1e4143c0900241c9039151052070085111750420f4075450944403151203c0e40500081c00800006204030b01042d040c6070104a9044d105ca2001001884c41c8031742c00c00080c0d00a10020180100c0ca4100b641d282c0c1c10104994880303161901c40d0600b00180c0c81040c8205002405004010010441c00d60241c20000d480e0702e0018502302c0310180d508240c580450710b02400e0349000c51403c10450300151080cbc4071140b201d0081104121010004a041c403c9850280001e203408842008590080e03002c40041c540244614001c0c1002264000300c810180c60a0a611410403403040c98907642142074a041e29801011400c0c81410588210780c0399a01c900344c40055a228090103002c42c0b240e841c41003545008a0741d070350440c41c100c0c0d00030380341c4440500740c0c00b01000c112080001c0142c240412106a400c0717403038010150710182c00c048561034034179084580f01658404070003490880000c01861550034040c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 312490071 1250 312488821 312488867
    0x16060207050d08071b0803181e0a150603380a051501090b03060909100e070e181e150c0306150a0507021003060e071116030201051603110d 61
    0x2410b0f40d500241440046c25100180041040c00981d410b0742d88240003450201c40b15902c03540c481f01d0000d07081410001090700000c021400b4004191905802c54503800e10601c0120b04c0c42d911483e6184192000011540c0c40c1c2440c0091240c01020841e0300c410300500c28142c0342420241040148800d5940c00f0a003880c148007803174254054446002142c65401b405401c56070744c002403001d1900d009080607200c2c0a800f6080c90303003902071b100c0c420b001c890440081c1001c50a10350190400c0350003805400b00c00d0050303202002c40080003d0040200d290080d20034809100000c910347c50091160406110000200c0400c0250580350014501c00e10003103400c56070544c0d00c0101020607104c1d10100200043c401c00c07100c005820041102c0101c04818580000d4442d41c3c2c0c1040d000e07141003500c1c0d90f4006000e1802020b0304203800c001d4540340000584000c2111450350b80041d1903445481e82c2805c0411882d20761809050084002d00d084407007820944400004501300209608071844050311840552 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 312491321 1250 312490071 312490097
    0x90203040c05041808030a09030c020a09020c0d05250c050d061a01050c070e10030c141311040e091606020303040b090c0a090504060b12070906080c0616060207050d0807 74
    0x48a160840c45d0300300c90344900d59201d080d282806885012070076810303c0036640640d401a02c0e003202c540f000346404c860060711400c3e07059a140c100840c003d04402005818080460102030001e10310841240d1120100c4115260380760802e60000c959004640c805a45070b0401d06014454000c2ca49608034007400300303881c412400040d521402003620b10412039000d002c050100001003d046900608142542859656242e44022140c009a0408400e8407222025a0840c0c00c08802a10068050b18414480b07011040780c510b81381e0007144141c4800c1008540031901005091195100c0c00381820b520105058444101035604e80c01514220b0341001c0b4600024084100403e46400e1080020040c070b4800c0e01e80f892110280801910170382c0c0c9141d485001c400e00c1c0e6510084200300d40c000384040e020b26071400701088115103c55108981d590007410b00c0043c288d4654085420a0001c00040d2880f9409030600038028014600000d00078440d039100c1000c00c1c0e820581c0d662045d262580d44900d0000d013 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 312492571 1250 312491321 312491351
    0x60307030c09151706040308180102070f03022a2b03051c050910020c0f070602100606050301260a0605041104050106020c012c031f110c07060c0606090203040c0504 72
    0xc40c00104c2440e0024800324002903c500a2140c02600b4101250500f042c410156822a8403400c412145081c100040a04060301402412180c17810700c100005c3c0002c41280003854100e240d5900d5129840e0340c0300d08111514940c0d10295441d000c0c2005509403540c3d840c0252156008808c005151407580c040c01c0080c28407401080c1c4a01c141c08041c1c042488d080b119800603401022581115009040400c009144204608030080ca00b6500030b000000c000000441220119042030381000003c01c01480b010318403584441074130240130081d00446180d0000079040c40c031002c000a19039401d24050005114803040070406c0c0e10000c90b810070240e42e9840c0c0c1030b80c1d02c2540c07010503800729030b08043e00703c1d14184084001c0e05008031005c403441240c9401c00000d061071445c58100f1070035200c00020050480c0148541d40c2c008071004049450908032075085581c030310305489250100484204914100415500410300422160742c1c19500c03410030b460075000603238007030040d40d0043e49021200211103032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 312493821 1250 312492571 312492599
    0x1140f1b011116150204050301020c0705040b030106030b06060903150f0103030e0a03230304120516050307051f0203040f03052b090504020705031e0d060e0403090905060307030c0915 80
    0x1400600f104a8844540ea02c040034240151540905a030030300c80000d140c2c40a00081101182c10005071038041d080004200880c0c446008d03490190385025014000030f9800c041194005c2402c07100517444040c0000003a1500c0042003882c0e03e20300400b01841802100c003158541624440d490b0703034000500380380c00d2182080c0d0314840945250801e07914200800665444554204901d10030b90f0302d040d4641006034020000742100310789a611035506001044045900f43d005050700b10060b01070145010001030082a494015144042601784841c1100d03000f081120010f11000d80c0c0305000554905000d40c403080084144040d00d51620a0005040c1000c0034422854005895442a0714203100070300c8001d410400301100c107440708000d00008000081443c140307903030404e152a5035420320040118180c4800343d1100c0e00e009100014040020b4001d8000700a540310000001010340e54480042d2810541c2d50002c1c100590340e00c00810307180959000241000340d40c8203a6940d540d601c001804040b5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 312495071 1250 312493821 312493837
    0x204080a0b0f07050a0309020102010608060c09041805151008010c110f0705060a0507030201090206161401020304030503070c051609020c0f030711010e19080c090717010501140f1b0111 81
    0x355082117615003d42c0a6404284a0b41c01840000743c61500c07070789658a0000f064400f04142017001c1603950351803516004000c3e00008426009180c208166202691040d50110a400c400c00e481d000802d14241d0107900130042a00790300900c40703591180d50250041828a00a903028060346940b80c2507900009001022540060200303841c04c3d26500044446411080d4114110354a03170b0710302d50240c2e81b000c0141400114605190001104614040362082c8600d090a002030740103000700030200e034000741920b40c40b03411070030692000f1038507280c52800c001100c00b0b0596400211800881c00071502d07030250a6000c1640d0440d20003001e0322204903903070f00a082d401040380c03000c203c400b5015446003018820b400ca020300350410341c1b6090030215900051a401c54522a840000104002d28001ca0080d0b0800c2e030702e040600003002030314100b070b003291414051981400030000d800c2180344001c00c111010300c83c900810a4440090810100618002c0151100a50708103546100c0600008080707132080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 312496321 1250 312495071 312495077
    0x80711041b1b05031c0e0d0206041112010911010e0301140604020a0e060f07060b0d0201122c0c0405010503070b180604090204083f0f070203010204080a0b0f07 70
    0x240601c00002c403041041d10100c11048014100d81c1c100169003040a8260481d41c0005003014043c078000c200b086406080350134003207038001120500b41903008503034950490781000c50007002003140404104503103240f0382034088641c03914a6442c14807218403a5000040e400745d0360498a4a285402c0501760f03101c0340e1001c2c82416804011030f11034542607000f4002c1105504101222452640002e01242c100000807800710b00c0001d80601080368500c100c01240208071004901403c0d1500002c0c00489110188101e1aa44944140c011494841352280e04640130342e180307000c0d5103c900320381d46a40051032024080d41c207210000c622440c000c9209019140c000d2070140c28071348803c44c8003400228540c80d02e80c00900800c40890000c4460009101a003140c1000b030400210702c581e01026800002641c6888031200a07185002ca142a00001041240ca0050725211880100d0382c104a00c101c20000b9070540c80050000f40380f00300490300d80304071170080c40e501d0100c4c1d40d40000c1d40f0448008440b01800 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 312497571 1250 312496321 312496361
    0x193b0306061e0d0b010b1b06070824060d020c010506090106021c2a050c01030b010927050a05010e011202030601051c060507020624030c01031d060408071104 69
    0x300550038491035826800070000204410651100601322500380c00c040c2e0f0314500000c0d040c40501c8104085482e220614000f00004e01c0e20410081100da0050884e103940c0c0403c60142965801004026171000c1004060903519100f402c0307004001c0d4004003490f10b0b10b508100006209107040f02010341202c015802410000e250215400080011a0350b400c007441440d188000020361814144003158826004007000300e840790510900d0b0140c40300c01d0728100360900d41845580e0740c0c0444440201c411811580b017094424000c400f1100c55040d600e0364981d032812081011034001034100504903082c0c0309007014641d13241d40605086944000300a505644070100400c400c0c1010000107410a032203502c2c40e01541041d0b5507100c15603000b0340d0507400503031040c82401016400d2500315000c00c3d860b00030002040201002107a02c901203102105c1c18580d0340c01040303c1014a1032403002102d0611800c1ea10701e442c15141201d060780000109a458451582414016003058400c51040340310300c13640c03109 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 312498821 1250 312497571 312497599
    0x20c0f03180301090b01050409050a150f050f13060f1805010207030801060203030408041a07020d0c031704060c1e080c0d0f05090f13111303021212193b030606 70
    0xe02580c9d0411242d0b88a1080480041140b41143c4c0e100312020400204800e08220526403e91340c020b0f20b40d410106c1e04e0000d0003200030401100d020410703484000402d5007400d807107100004080000325482403070020140e600410a041d4014000240301c0d0b01e641c003042e62601e40c220303030306d000480780140f0b0b5000801080c0405001004010700264036420103d01c0d015496012079000000d04100b15860b0036018010f0003004500100c40d4254014000176504051a00f1402059081400c01c05006c04100c007604200f002065500b03643c41c2500010500d43e110380d0f551065a46148401052001031030780c0590b20003ca102e48201e41d6004030082c4883d12504510082007100001c400070f02031303140e40c1e54840c4410a044036010b8408424114003615405141d801801040d800001e0903484d0f03a00f0800090b800b4000c0034051ba860041b14042482c02c1d212000f9041d20503599484001c0140d0759a800c07081844402d1480c2c2c1003e503403000104a080c003c1e01014180e07030701001d60b0240d40c4007170025070400e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 312500071 1250 312498821 312498829
    0x60e01090209150f0d060b0c0c060d06031a0a0c0e0d030518040e0109030201050109020a1b0309080312150102010c2316050303010302030f03030103050c090604020c0f03180301090b0105 81
    0x700c0c02c40002021a922204041c902501c0c0d41c1c031984108424640216007809080080d200780001851078001c50b51030114054040c80d05c7d6810350040e503120303070b001003180d900a151a40c00f00c8080e60f07006201440c07201075480e203840c91043c2251220410390030114442c0c01c40d40b04941000001700c0c044c03c080c84000160f64140c0d4a50800c00b8407201403580c4000b103282590300c90151303038034000d20080006000e4400b420000e0a40720b05800200034140100140400180e121141b0703200324060303103507070741d0a0403041c0f1381141c08110a6004c411300384404146d080041ca44200e507640039800700000141c8001c403182c01a42030b50323100075800001c07840d100b46e540ca2100641072505200d04240003450b18040c18008400a0080d4410041d16198004401402141000c00401800c1c0381c2400c0158250740c0341d81d0301c059a400441525901800311035010401d01d0320b0301d405480b502c0128006882c140b2450800040d902d0300985900b8180d04240f0000d00700c40d0406111750311081e81c01501e0300540760308100a01c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 312501321 1250 312500071 312500077
    0x316060e090c0c01050406060f0f24020a0f0303050105011d09040b150406030f0507060c1205070311060f090c240c1e011a0a05130b1c03090f09060e010902 68
    0x39085582c007049424182d40c000e05c100382c42248214800104281010000b039203074009900038000e01a8100c0007400070f200384100001540c455494414803019103203030201d0801c2d86241f002880c0210741d4141800b0941c050704418103859080c0e84650342c100c05485d2500a910300c031202c45030400082c0e80400c0c0030130212014294070601a90040303100802900224080741c0c01a0310960b108221407015004014090000d1002022145402e041841c100d4540f002c683d5043d1080c0014020001042c90415015244000144400034103803040e500d00f601240758080422110129203004080c604500c51418641c02c0d001801006400d0800c0c0031001c001d1000ad620420340081c40d4411400c01d90041101b20840605070041c4000104886003511400c02c035580103810706522441440d0014000c5031079045822b0060410706c18080344240b14080840c0c50080118801d81c18030454034424814560481e0082c1d04651007a02c084090310740d900f80d2181184c4441c024009000030300c50041113800700507006 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 312502571 1250 312501321 312501331
    0xd0806090703090c1a040e0c04060f1817030a080a0c0c0b0c0d0e07090e0c090a0c110d0c03020c030303060a0b0a020f19020f100503061207050604030602090316060e09 73
    0x2080112502c1e078800b040c04a45c0c08140e20040c8000090601200c0100c515030f40e0000c05003000d1030b003001d0074004040c0c09180800305800800c10b41d1040b566200182c4400100202001c110070b998101c2141d41294030f940c014040742d4049a040008a808000700d48254400044941d50b1000c0b10036003a07a4810710600080c041d404002d40030f0105c100d0070400c0d80304101483c0000c3d80180000340c6440480d03402d85a015142a0454011103606401e940350342424a0340200a414001030200304a9410381b004440b100e00301d0380c20705c0f401d96555140c0b500036080c042524000d408482820048a041550343d120071034019401070006101000b0001c400000703010016102d00681c1d4a020341c540d0024a440c9a00c01c9606050321105101d4065090100305017000030401d6400c12004184100060110b10020b00a540290f5540b504110f05a9050180302e01900004191307c2d65241c0ea4103000d800fa4214401081c4240500100c0040d80444860280100c450035220030000d0040e007410070200380c0d03000784 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 312503821 1250 312502571 312502583
    0x10030201140a0504090f020301082b0305060105070c0305030c011103090a1101050f0703181e0b0a11120714030c060112060608010e06010f0605090a050d1b030b090d080609070309 78
    0x4008102c0145c1070242c982d00072a42d840c01070f00c940c58415411b241171500a00d100c2c0c0340c034880c8a40c1c422207032901d5445400c01031504010507640c40b854012642d610a04401802c1c0100d0450080100a008802000c841380560001d20001030741340c000180b1807106a45c02c4030554003a40e8510700040b50780c107408802140505259042000c040014880c96022642c1200065030784000601e030840c110001c5406401500361203110b14a406503251140066801a100c0185000c070b04200e0242c45404119044408003080c2e035540080440e4120680d0411041155800d0400d500010461000401e4500404010004082591a1602494000450040c01c0d204d5075156000840c1c011000d0044082004c1c03460003d02c104d40c500074031b50201c60340035040b40040080410842c040382d910080b80105131076003113583c01d002d98468035040d06d8180620400c3c032612205100c000090000d40b00000748540d40d40b000f901e9071020030740c07421240c9801c110755040d8090314000214060398031035413100610300d00c40c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 312505071 1250 312503821 312503827
    0x1406070516021005220e07030219110c0a060809010c020a0302070b09040902120a1a07090311120d09150c230f07230306010b070807050c19090510030201140a05 70
    0x1031070380b07a034000044000c8001078117a41040009030361914540c1c07003603442c03504500742510b20300070340c201b034623048502c0b0b040105152122403020800d0001d80300c1840010420203000c0e580f036801521901040390b031410954039143c01209000d00105000005c503a165002c2d00681e4142111600d094101c1180b054005689a4984005860740b0703810148003480c22004002082081c6010500b0000031825610005901c03400d000c1c1140d001143c02055030361181c510301c00420f040020907040c2141914100d5144500049403a020790002d80700d00c251080c0801010100c030804038203440005420f10000d113020703810002400781c0401000416954055941520054401c5514440c5011740542288811800d11030380c004080820aa00b1410441c0c260301421413903240101c4d0407400e01980340094810480040c104003001018484c01060b028001c0140e640504130b03c00402e40840913000d1038501c5031500002c141c60a00035800102180c0d4140e40741d502e04811440c040000d03801903003010701448414 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 312506321 1250 312505071 312505087
    0xa2001020409020a0c0b06040902130903112407030507020c060a0507120906031401080a030f050408010c0503180f1b0d020a031b0b160f02011103071406070516021005 73
    0x40c1c0024000745150350388070f611714109400c00074080c101c0600102d00c580d1511030800010b840c0d21080d82c04806d0700c1b080000d602e0015040c151600326170ba01c00317031400c0d009a00c2c80d0000745500300440e2400b0101034600c202c103659600415801c0399001d507038440241c1c1c070100c4522071074a00500148005400d514003142800f00c030360b803070300100c0c01034520b00408544410300a01034268588038085030700c10406000c3d105540360101c40360300c8040d20000501040514004040d901d8014411030f40200100c0340200010b400400005041d600113440f945100b50310b130981e0450b0b120740046c0380d401d000203036009410000502c2e601c0300c54980d98042c80c6500140c5428140015950361220180154000c0f000308100004420a010b550075280e0013050402806001213482601013211840c0c1490740040c12406448943c001a03440c2c514112a1507224840003c6007030400000d00c001250b0074440c1822160541c4a00c07509991500581c2081129110052803000c00351408600d611100700841c10000d10b00064 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 312507571 1250 312506321 312506339
    0x403020603090106050301050604020f040b0f19020109050d0806011704020103150605030115050717070602040302061801030f0b010215100f03030f02070b030c0412060e1605150a20010204 82
    0x4115442c4409964824081009050038083e4030f074406030840b0210314080c6a0f84040c51180214020155500350120b030300092001d10904485150b244801c2c004482c0c0d2003d10000c2c0a02a10001281c0e41d008012682d100c0300e0082c80c0c024010071058490081d0540583d84490010350300030001d0b030416885041c0c0503014004400c1d501c02038035041d5501d9a13079604140140082a401045400411408009000104441110305082038501d00303070103035585207603090500190095400c040e6001000043c0c6050b00142c080528a03e224203807006c0c00b01e0303003840c010300301110a6061140e000d03802202074508410354914400d5030102d030341d91451820035203440b10b0b02401045600110003241c8401c03a1009042c3c0c040000000400c0c00500103444c5240c549101e0360f0074002d51091051806000310720718100035603070700310100781e02e0380038203c4880e00d55041c03031821030103114420306029410001c8042201101402114420416500c03400b46421b007604a042400c480121445150356003484045002c680d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 312508821 1250 312507571 312507577
    0x2030a0b090a0317040c0e13170405040f05071b0302010615180f0f09020a050c061906300309080304030309060f0206041106090d0c03140c09070219020604030206 71
    0x1500002c02000d0214503021300f40d440d0002030907402c0440e507000c02000440340100401503901c487c46030300c426203450360781c900c0d907403100c2038000e1140d07201c021124011441d0382c028104441046034240700302e8003150f150304d045a006403580d000041d0502c4844092010700c0c2013070300700740344284000a0081c1d074032102403280480c60100c0e83c3c0010403140d2030506421701d400b0394202908100d803c00d148186003080b040341000c1c0510a003442d0b2500400c004040c18000c006607072004521100360360980c90002c21720654022151496020a840d008010440c813100121240d02245104074141c84581740c0c0310034141401a1440407000c10400481c0469540003c0c800f03071009502c05d80b100400f0074100075024180e004c1c43c2c200282194007074801c00000c200f036a00e035845901c80603100c46170b94076078030408181d43c0c0d104154042c040440e800700000800003201c001c0042c1c1c0c055142a1404d4003404010401c081d0001d898440041e400485481c00e0100002d50864050344000c0003145440d54030383c08200311790 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 312510071 1250 312508821 312508831
    0xb0d0c03060b21060105090406022101080708030c0a08030604020405031b0406090c05030a09060b210d0207290d0c03150b040503030703080c0d09120f0503010b0f0702030a0b 76
    0x2525a103903122982444031400f150b1407400c02c40074448124641503203139101414483d140c46494104045810f1001e03580c1115a466004080c89c200d6000304503060060090a1080e908240300340f03400010700c42004420744100748092000382520340ba41c0e495100d42c0383c01c00f60445900c60743c00c000000d0542d41c2000040c200089400901c204244200704000450301240d04c4840906d0814400390350140d845800c403070b80a044540700251110031418118000e0412400d8160045554132010340200f1025441e01d01940e140b03021140c0140e50260101e0b101c03c4241310308100019988132022030001860740d607034062540c0c004100d0400c8000c407003d00540c2c8a0300d01c3c4801203551118841c03412603048690f8005004075102682c034013032600000c659680314402015040003110340110b49a00d0f1400c003196810320030f600c400c2c00400c0f490305101514210711191030f00403030035400481c89602d02400c180ca0486802e0300c585801d010700d4400c1382c9035a60040004a070305002c1d050f4104001703030040356a28018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 312511321 1250 312510071 312510083
    0x1140c0a231506040f0b041806051b0304082506050105090a06060f030f060f083702040b010e09010f05130e191a161b0b0402040b0d0c03 60
    0x11280003008050038041d202401d4003607004030701109415081090800e41107803050700c000031103c03442c00d0000d0003007508064240c0d0080c1441c0020000e119084900c4280600590701004140c85040d00c466900314150312004c3d100ca0280005804541124007510054070401300508003040a420200d1405c41500b1040300c840e0b03034850040c802810312140050740020760741c07000c019a0703042c0100602018648243d40040544411140e10009101c0c1c0240300104805180004016118000f06803111200c0300c0920040300c40d08001901c1d40401c12b0038160060310303a07595070300488007502408054004203035030b6030601001641c03522043c1c840e5a0340500a02c01b41150a80680c20002001011081e000c1c401c054541003400f4248014804038108880003001c080e24443c9041034a403a0260782806c016100820006800f003099540a070b407007100e400b120660340c2808940364001d0815503443c04690281c90710030304800040050400e07505c8003802c200000c14600b5900680d559400c000034480c0c20845076 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 312512571 1250 312511321 312511343
    0x4090c030903031407020618010605031902011b0c060f050415170606070c0e0a0e120a171612020d060303050403060b0604050d032f0c090604020a050901140c0a 70
    0x103140e070520401c4002c104130101444a07080c0700d0002551180d01500b0542c55140e03020413100c00f080250322a20003810050180c880f40d45507003500b0031266400050aa0102c0c491400c2c10740c04180009020800c540d12103041110710342028002c45142407081c0c50002805400c04c00451248020740b400400d42906035500c03070303200c0b09103600800072181c01351016000e40c8051000310001054000240144c84d00f1000310004c660b240134140c0003030556006005d07494010202240151a424001090202e141d0b44410610040700b4a502d0b4540ca01140c81d4404000d44910841c481c510540241c04003010b0110094204506401000d0458100340d1040b008070390005410010002580254520140c04445070b504061030200403d41743c40b11400c00500b0083e0201d0007682d801f8200b40d000c50901c4030411520718000020351000c0d9070700490f52480780b0a1406000080c001d00d4540211b4840c590b681e40d51500b0121120011b60704600f4441e64005040390500070620444000c0150b41c030303040c0c094059194 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 312513821 1250 312512571 312512573
    0x515040f0302210403020d060605060a09090e0a02010516030c0b1e0f16080705040b070f0b090f070501030b0a0503010507022d0c21010c0206160e032104090c0309 71
    0x480d1111116090641c8210408142c00950f0f845090390300722901038800c10880e00f4507103001401881e071a080a03030321000201e110405503a00041031015540d02d21400c000408141403d0340d9107e00d80000240050020085d98000c6110301c3e0f5100c6a151007030802920040c040d599585881000719400382c0e00c0b00f60440d03020080e08204070310a805c000c004400025a003064034030103208032180c95081c02408420b801041c5003d100740101c60041814107a6191100c20500d480e41c442403980c0d40076140c6d02c50f40804182c045402086043c5000380d032000900c442441c01005401404841524a6002880c1035000509403400c0c000c4a1040d885a4003810301c0d113103101c3d0100d401405c450060400002d0002d181000c140c03000480700d40708071080f601e008003190382e211918201da4183c1c1e10041e5a5003000b0300c0740f88880c2c00041b4070340110078401d1980381107503010360101e60052030f0b03208040e0f00d0342c07054403404000711484010018460706404000d16080d1200d0046c0182ca1040700321070002556404458 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 312515071 1250 312513821 312513823
    0x120206130801051009090506010e07050d0e010606081e06120c090c0d06060207030804060806040e030c012c0a020607140613050706080106080609072c0a090204120f0515040f0302 78
    0x34007078038100c0300801030300303100c7d03121555117480c1401101c030320741e4450000c10982030041080d140e003034641034000d12400440c50b50007806480580705503004034014030081605000e01c6400c0401404071191586919652682085007040d80c100c0031038504d020301d03800380c016074462040c224810306102003019503a19103d441d000407070301207a11100443d042183d051001451200468045442601e824000b42e102c000000c4e0060020381d200340c10354030000500c86030407a010741090078054216541c5100580005030704e118508a101010402e0f40c002c048890f00629059014050700b0f4003500304151401d8030700440500c1e21000703454607404004004003400401c801046440040e00716480c20324000c7d450110003a14000000d801580705144100000ea562480b0348410041c44854500d00041c85000c4041c110251507030780301440c0902051000480d100009008507030403202140036008d15842240c07907445100308510303002c540d54064111100e20b403040700000c56006600844800721200300d203160107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 312516321 1250 312515071 312515101
    0x20304021302120c03270d020f2d01021303050609070602031305010806010c0210110118081e0909040b01050f090402010e0d060e010c0e031b060412020613080105 71
    0x140070141d0041000000300d01c928844182c00510b10000e054a946851400c4180e14400c0c448000c400c007015004600d5013000019280924030f5141c096a1101045a0b1481c0c1c036121580342d510001c5c40e2144100c00140040194207451004420005060504414640700c041c00c2950058845500c04014468187c00c144032400040500d40025890900f811044d495024000d20905052000c00d0380014150f9000e074007211105070b07005100a54071400c800c409030034801c044042d90004d40c40d04640b8188000c0e2041d007191460342211689c0d0602580d801540c00904e91080000140c2d80d0501c616440c603207a00c1c080034003440c0700c3c20300100310798100002d202c00504c0503601280310300071074403c0c840580d0300040600391218050702c04040c140c02c142040009000024050005c5610384001d18080550000c43d601440c1d0003241542c2a901c11a081d480b0030208182d1100c0c0e0204040008100d00200304807112a21840500200d091100b42441c00c0300c0203240b40d00100d1941d4444c810040d07080c07456124 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 312517571 1250 312516321 312516349
    0x21608010501050f090703090b0906090d050403050703080f0c07030c031203150512120403110906150a03050709030510050403080606070302120d151205010c05270f03010c0302030402 80
    0x704031541c580700010786841c1003490380314040d083e01804141d0040c401d40198083c0d541000d0050110b00f401c5c180241d0728802140c40e40c1090090407600c412007407191044504803600400181001800c54039040400d47c40720a079050101c00c00c0000081e2a1000e2141c2c10045001342401032541e0320303604002d0f65000900b01030b2400c25141540502091002116000584002b40c0d16171440810410080f840d080e01e00e0181064100c010500008100000103046100542070303074a07000e16203820081c0300c6500082100c00fa0202c005200004500d40b00b6408943d100c0030354500a15a190b032910340508001000c00044030090b200c0042006050f08407030311a8006900780c1c0c24501d401060385000f921222031100c2c10b10b8a00001410b0003168071140c1114022100c156181510250380310b000481c5148043c034121099420113494400d070718000d000b41e441d903903032030700f40c4503504105861741c42510084d030038110390701c0313261070b5030b0402c49490902c42c0c0ca40800765501c0050b0f807410305004000e00744500c084 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 312518821 1250 312517571 312517573
    0x42703120b010f0f09170a210c030f09030b070503060f010504052b02040606050d0f0c0905090601120e0c010e09040201020307020910030b04111014031603110406021608 74
    0x1a204520366408074440da20f214a510780052901c60168045511000c1d5601a4540120100030f10304159004036500c4040c80c03103458102210803801141c1060148500c8800010440000c00380c1c0c0031078003c803030b250301c1d058092038410300c4c1c00c4d140c0e92907404440098580c0f00001c1c601200700318050404908001000d002400d01c02d05061410002880e11219081540c00c0c821125511112040c02c1488603485a5401441800003645401c4001c189400c04c6440085450800c1d0301d00c0b01d282514821000b8281050781c1c1c0c1c140702070502060020707000000c0d1205040008260000023a0b114034801e0030001030b0802c010701031000940d00014a40500c101105100e289c0c52070278400140e800008490007546c1c141c1d520401070380e855017003c44403000d6903c05003225503218200130800003140100385000d14222520741092001407021120740c180401c45800c0c2081c1040800c1d070b0446601034103440342d40d00d03250205126002d44400089500300c0c3d8040c00142e40704074075550408240100e441e004c0c1000c24 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 312520071 1250 312518821 312518831
    0x206070828170619260d0203031f0e040b0402030c040f060501182108070b01030b04021c0320070f0e100b1602012d0e04050c0a0206060f04270312 64
    0x40e40962240103407061410203140820044210031414003800c0d403201d400c1d01664607000303000386c0c041e450340c0c0201d402c1041e081450942d0024a840c240c03c4009540300c040050303c480d941d50b0b40750a0010307000741c4140d90600c07910a034000c5c5552580200d078243c1c49405408a42c50b460900054032510f90340d1415061055100000d00c40c103146540308900c02c4a0250341414400c0c4582014945849031440103030210035444004020302c170117410351038069842510401081800d0002c1d103480706c0e5002d02c00400158111425101e22009403401641070749104081e500710668803968001418101e92011045841940401003201071040300c900043c90341c029100e141c003059141030381c451070900400074103100c11000400d0200407501160500d42e507552610f0b50503401d40420161050b0b0444607458821f40c10f00001071070000c1140d050355400c02a07070b0020031040e25420100102582d40403005a0095542d00141140d039074483e0544022400c25103014014900c2410003c0c142142c0007007010f801c604003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 312521321 1250 312520071 312520099
    0x309100b010f170408070b0a05190e0c22020d09020f040209092d01230a0605040512150403050a11070b0f07051002270a0302060708281706 61
    0x44248001d46100c3e801c20815038503860503130030a0207034440140681c44000100305441e00e081c0d00a0b8020114401940301144140e01c00300180c44a000b650400d0381c001004000c001c1c281441640708009800c034550301081c100700389050032a04a1949820403d40301c1c0d4a20301942002510b40f058041d00369020b518080c1d41c0070200303003a140d02801c0201c42945800b90701c88200f11030003c04c1c9592241185c0602c241d40c0d220502d22841b04e088180800a2007403500e154080d10344001406c046500d0760721b4441c28103160070b08020383c50003001004001d500903150b164206842e101152403107544251103245c1c659840d4500184071003001290f52800764071580d000d00585410000f42d8006207803078880990340b45070502d403640c205104400403040050011800142807220360074480c50600180280c0e040b5096084104401340310341d0711010b5040b140801030b2401041d10200200312628400040c112140c0760301c400314818000307103406000010380c9103000c0034040500c215280d401000840c0d0454007082d803 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 312522571 1250 312521321 312521327
    0x70b0106050703050c0102030106170907230f040c050a140a020c0f010c0b0103030504090e0c06040302010c08070b0f0a0f020910051b1203010620030703050315060309100b010f 77
    0x180103035014070002090035030405200e40c0803641d5061107080250341700c1d6500da101a00062429108180d80244c0c01c1c0043d01c4000001903003022924001c00081480c200c842400e0000400500440d0f01301420340b0281440792641d00602c0460101a43c590f0354810400900511081c0d000c8000318800200b040440c14182e400904100c02000454004a071325020400584007030901d2a80240050201c42c000020306402002401c01c0324180d036010302c42a070706446a55150541e280855602010a000902c0507512850050361414412500189040b500d620742c1d9000390301c06c480d1400c2c1c182045007007250f00368070780c01401e4198800180a504140840002030301c1145401c4510041141c085000782e0741c1d4091015061200c043d16055500c011085c103005480e680c404d026040200360303110000100c00b1540c1031b054a26040e039801850404109030307400c580651002d0110b500601c4612210400340c0d0701d140c000e602803c0d440d4014010745207203101000958034100061030500017441c0d442041300350 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 312523821 1250 312522571 312522593
    0xc0906030f0d0e1315060807050a090e04170c01020c010f0b06070f110a17010522030f031104080109030306090c0c0f020d061404200a090b0a090c0210060b07 69
    0x2041c02c00c4192550050b0220300300d0011404408803090a00d04418000d840e05e58407803003554210740d15400d040d42c5240c3d050701c5501c100d408076400591260410000754005007034454000d40b14041d0364100315840c1c42c1e00b41054018424181d00c6035800035240f00c0c0c10109119101c041051840180241614040041c00700d0055a60141900001c0b0041800f00485001c605007010802084000d24640b1005000141c000310320b12030b400c561901c0e0205118031015004220b02d00703594400f10411144e42e07034007107800001c031007040b00501d9120417000200c1c0c41140d0241020b403140900003d014102410300609076411079000c8130b0703100d2170a000c1305815544500043c1d94540c0021001424032032620114501c9042800040e080914020b0a03000102e00070350b1890050707004e031810b800078000a0182ca040c1c1000000b421303600c461340080400c0800e205800ca50840d28000301204c034100c0d80c1e1503080301941c441115120041e0030219200100c4034491040d00c0150081052090802c4d51655030b14a246d4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 312525071 1250 312523821 312523843
    0x12090606041b0302160c180f0e0703031209020301110c1e0c061810210203010b070605070c0212061f03080427090506060103050a020304021806030a02120c0906030f 72
    0x264000401c0c0c140d2984d1000c5030705c0255071000c92400c0f190358603c038011801440c0d1280043c45070034007c1f00c66017902a8024401c07040c4501014005003480c6542c140c1e40c40008803089a4283d0b210605070025035020305c582c410700c900c0d00e58240d40d1143d203014024100303e69092001c070351520440306860020340000d004d41c4c002c44140e929555070001684400f00c0032408078800c1c1e9008400c0c0d1b052280c0c0681c070484040c0c0c0340f0070b070011400c0a206180e001c50240c0c002406004000b0704103220710404a401034002c580c018040303080c10301405202d50081071f0366908500c3c88441a504c0401441455400b00820254100318104c10040c050704650b0381c3e80fa148164801d40c039403580d0550301c1c019070758401000ca10201e0941142001031246038034007070703440d41d104543c49808a89400d0000e0018507040c001c603840380790f004005205511510890200c3e44002a0000760144101e2500c0c070010b8841048244c04955031000411504428104000c40541c1c02451309000e9000401603200100001403800510 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 312526321 1250 312525071 312525077
    0x40515031302060f0c0303131211060a051306050a1406100c0b04060204050a060f0e0103110730030902040b010c02030604080313020d0303020703121802090a09060212090606041b 78
    0x350f1141c4004d62403900505d502d00c03056000000a0050a103884041440c4080c13141d0007401d041c3d4840030307050f100206c440740840306640014000130b1965800b503201540c40071082c0101240f51a4980726032080340c90807038030300403950744d5107851450310707041c82c01c0959000c40c0803104140304006414005140a80ca0b040051075043c00d580410704001c2da5030180da0250002a04903001c680e40e0300d000030080c030440242040411408030f0020340652080c000c9021109800d46c0007803800044d95140c00104d605a0103a1640507506a044803100701c600a0345001d2507000d550125000c0420300400c001c640101e4111810711955840000041c1c0303010503001c1e840303074005040301d032680e6401038400210382d1081c1c0c00075400f1000c481c0d448105601540902183c80c0607a94815211000e0302c4007404480040c3c1004109100da482c0c80801071511f03003200d5034841980c2c00081401c0d05159140d80503a0001e8141490002d00d07001001403e80082000a0b1320503c00c0340c0c00d000c2ca409a0100804c0304015003284010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 312527571 1250 312526321 312526327
    0x405010510200705031c1107140d1b0f080106090b010813030905060f1c06050303040b0a031401030503040321080a180b0403110705030c0603060d02011106040804051503130206 77
    0xa40c801e021100c0100000785c203441052000400c0b940b2419041070f031031404030b44400c08824500d000080e07520b0682d00c000d810f02d113560385000c0c200724031014142003c4800c040300c1e000d003100242e19056070710003c2c01011b055011242c09d00254600b03542d85a000604e18902d801c0303904c04143c0e44460001e800004040a040b01d0a059080c1201c032086070342c105c1e5801000010f40b51144580b04130081c5400b10380d280b110502213440b482604150b416510650398560300c203000902c0041090001490421150b0a0000c3c22000b4a040754200b800242c1c001d40301e44d00003040070001e01075040c502c3c520741e0504200d0382d400d0078000c07403003d0410310340075001c0507280380d5030070000044143c02e85030381a08942000c68488a46400e19000b4202c41200090000c0750160300c2c400507540c01c0c0091400f40e003001c010721060461740c1f034400384100850700b09010b074100108807203007a40e142014420719001e90b00400e440c80d0ba80342000140704410502400084082c0d904008000c28120040d9103a109607504a49480e9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 312528821 1250 312527571 312527627
    0x515030a0209070e15280c0c0302040203090718020c0705010f0c060506150706150f030503122a0d0b18040b070302091002011a060304031211160b060405010510 70
    0x5c8100b0100302c0000900d000040d0740384580351a010400c400b03501d10352101c054509013007011201c40e40c0980f0024100c0d002301c1014001031605401079a80001900d04540e1880c4d40c4515860806440408060300240c0c000b8005420040910141c6d02901007800c203114402c1268100501c1d15a2940002d04074550391000700782240d4400350b10b090500808100542c03500280c0c14400010601050001d0450001130710000d08802e0b1030a070076088075008005503040c120341450300404140c00411920000e11044000c001c10048400711002a418088400f501d0b502106041001c444180021178459440030519101000f10b020038558442d5100024568544400300c0550203400b03009400c9900c00c0b030b42c00402030041c1d41548600428101011784852500946090020342c1c41b05481c042d0004103861800c05150325103030040140503544200c01d41c5032000300a69800c49030b41e0440f0480310008900107000749031030b0034010316024020880f145c80410700d413100007804094160340005e24080030000221 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 312530071 1250 312528821 312528829
    0x32517011b21060e06090f0603030901111504050a05070807050a06030207020301090b0c0703021005060f10050d0903030605030d091514040f03080910020a0314160606090515030a0209070e 82
    0x1440d150300d50000344181c13034a904110031541c0c0100c40c210300178134559000a1035500d0303003510faa0040070003130003a5141c02100c400464150b100388030420312900c524144504c00003030380c0c40403500c59030040d409481030088900d085402c101e02640240326507070008805100c650f50b0700000310704907401c0e410010794881e0a440840c0c05041003110280405000c2010403440c3d04d43c681c020b0046621981c240c8244148050004046860a445190b00400740303900342d0000742030101c4011403141642c20000e0a00d05c600348421b0583d41410400c40001e41c55130002c00103420100b103014015040c50411001c92070414901242100c0c4c004200d00810540c002c094440c0d4492170200d40143c00c2400d0315041090f03c90810340000e0b400411001d001c1c00804141c00011403000c2040250162305a45656041c1101a481040b9800c013800f0100000c0c00c3c0b00d00d41001170072500c01c50005040340c400106062503d44030b000411004141994041e4000200c0c0000594030250030030340c000710f14203107501c036000d03603c0c041 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 312531321 1250 312530071 312530117
    0xb19090b07031d01060303020c030f01020711060715020c0c040c080624211006180e04030e090f07090603090c051002070305030c2104120b06032517011b 67
    0x1c2980394a4000081b0034581d010602100c94101501192410b105501180b401c03480780c050043c1401d045d40001040c280b404c0030084c5103903030013015900e8003540101d03480703000c91740090a80b8109070b00c15014a441c1d800d02c0c2c01b030044d60384480c0c201440c0628096010500100314025450080b88039007500c4e4058400079401d032041d00c000c0545400982c0170309046400700030002e8807140b40341c40c10030100280d905e104a9100c00200300c0002c1c0030407264948051442c245801400417801d001c50504900c1d0036480d1a25124400d02000066504909001da0003034081203a5412500825003483c200c4030105001a041d00e0031640191400710722076800240403810100d254000900d1800009190070b1282c000080385001d024aa48d02050480c80369031106816204900c03038418501c290700c800c840854100718006500c074030042c0548001107a01040c811076171309a40400c084070b100e02c4509001c0b40c802000715642032a0140000c1104031403140c40482c1020903501c80c8003c00c0114800300c407110b10443d5130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 312532571 1250 312531321 312531371
    0xc0c0f0a180203010317090a0e090703080d02070b010603050601020a0f0206040b1c0b180f07090312121406151605060a0902191a13030804030b19090b0703 68
    0x2260a000520901d11010354420305c0141c0361044000801d803241c56101c07003100c101e001c008041c2d150301454200340000440300102a400680501000080813030b080d50003d08003015405001a951540c4d494a03000b03100c0103822a404251030039007040156600011610382c1207800901c0702030710381c14500c00030f80b40b84620f406c04000b401000c610961702c0c1010300d202030380d0318107042c0c403d202441c955030a2020700d0305240c226004c810395040204e6070f281d02c140d0116802061514002d16015126240e101f14403070081c0482000980035100c24040000510030561300c4a041400700026042001c0060b00134a01483c0505517a0b5000078200e60b0482c02c48004000654030034266249450600303950801058441c0c0164000d2107544508840000e01c031601e001a01c2c051003442c8040e02030346640c40b58980101c1d00c0c804103020501e0b008004111240041c0000711710403040d0348030b40d01c1d1840e101481039441003024000e040c01d0040d68000590348022260748400e0354500090145c100c52000c648450180304c07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 312533821 1250 312532571 312532589
    0x60d020c190302010b0321040603020a03020c12130e0c070305030c16030206040b13050718090f0510060e100306021305040905070303080709060905191d0405010507050c0c0f0a 77
    0x200d031074201034040d0000304030740104505903000034441060702c5403040078000210070b902130f007003005008190095001d0000b550003442c00500f007803004c080851410780d00720f402d080904000720301301c152625191041c40103022800307180a01c5023804d0080d5281c03030044a000500703210020000407c100604402d035001484c00e1810411426103908001c0c1d19011300781c0d1f0590340d50349004009002017600661a203180f82c1d2101c02400d0007407528000e184c0e40d14100c14825101500c441c1d01d40041100c03070b00b02c00383c81c43c043c1000c2c0c120001c000c4518421962140e20141c0d002640c01c0800c018010001441011260404805607840c4203d41c44110081c15a400036075000d85803090302c2003801400a0328400b070380d00c85d80300c8181c1c0d03403120344050761030816601c50680080d00c0d900382070041d410002c0100e96840c0184c98901e030240e444022100c100d44030b0380385c2c072805c01c0500800c11040c482d0900030203070802254200f01c0e1078401c4040b034468442150f0803259016203480341140d005500d4480e0640020030382c13a4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 312535071 1250 312533821 312533863
    0xa1505070f0c060c03140c04060311030f0714040506040b0d060611060703020304020402070b150906030102031003030e030109060203070c11010507080702041d0f010230060120010504080702120606060d020c 90
    0x2558007d10350007900039000001c1c50000310824030070168086901030010303140045010717501c01c042142c25101c04070040500030024080092151120005000a402d45144450b2500050350850701140c1d401e0f0701902c00c0082e101c0c101e081c1d411004c902c4541002281c42e0142e9650f985001040185c0b094000091911030000200032480381400700c084800b0100311900002c2d601e402007018280d01040d2041900c01c5e07100101000002e0203110140c0c0c0301e11001c0c0000c01d0b480c140b5145d41c8203e0300101c81c61004140b0310765400382040400100d80e1004502400d0460502d1555140e44245024030302c0020300850755007010071240342e007601c0314025000085084403614414428024040c0d0041144001c03442007110190800791141300c800700031342c080003001201c00c0e61001c004590751130390076200f5820810311740c1d25401d60720070a00502c1d1003280905090390b942d00c4039105105040e40b821901c0d0001c0e4120740306010b00c65a80e44100c50394080c005901680703500074881040d0030442041e03011120b80d8004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 312536321 1250 312535071 312535081
    0x1003141f0912030905060c0904111210090905060105090723040618210f0606120b0c0306100e060f130806090f06130c080a1505070f0c060c0314 63
    0x240c001040032845510300c201402080b05040d019609a1100286140c2150000403074620703c0401805040c00010404500303d001e00000c24403030b40c010108140050000d50070001403074502c4c1c4450008105071441000098801e865607505d5650602030f0070701c1034900c440406d40e07482c0f085059001c0c2d120141001c8034402024145108541d20521541000c03401141d070300c4522400d0010f124080f22114051700d502c400c1e00309010504000740303207421a410444040f900001c42d0507441024081d0010f9031350040b003418036060401a28400401c11810302d03a0400400509445840d02c940c40640c80703040c0066000084400100d0500808013103840d203840c085100f100125802168408649000e015a00c594a4413815142c80345403820007603425900070f07804a1440c104107083c001d04640207650061505460740203080c00c20309543d50690780700c500f00054480302c24051251a8024115007030851a005418138003800001c0040e0300030380437a41c0c2c1c40803451118002c0e0051048266117548021a510300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 312537571 1250 312536321 312536383
    0x9030f010609060503010b06030a0209060f0409090314071a061f05040f05010503060607030e030c0904060c020d0206010f06050309012a1403040309151e030204081203100314 76
    0x190b44150402c4500303080c00003820742418440e440200c4c00c040c05103071031030751410500c90281d4403c1d0449a00080d0806c03940000c01d01120241000d0b0241c0d420100b03a500e81c500f07005025003171803144604c030039504005000000341e0600842e4111b141101e07284000b80d8581c00001d04803559249203d001040d5840c3c0c4540c1c10b60700c50001c0007a51007613074104044035110001161140000c40301e0315000070301002014046402080a0b4080440040c1207400505805002c56070031803050304c045031f04c1605da072890040c41e0307014440c001800505200400e015031402052a0040413248540c000744500000400c661680a410145650551001522040495141c0300c0c001c060b801d6a901c0000e02c95000144080c002c2d0310459010319056994040e80b141000141c4440b000032269450922400b5070780710025441c035900b580013221450300d006860b5440c0c0310849090071380c903481142c04103001b0000c10080e61710302510001900c2d00f0501d003624090030301d50603610b841c04100351420303142c24904c414404011 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 312538821 1250 312537571 312537581
    0x1c020f130c020708240411040c120f090c0b070507050a0e091005070507020f03030d1a0f01030e06041e0b0903031806040c090c0507081b0c090c180609030f01 69
    0xd10b6003202c007581d9641c9602038032800000d043c52400c048141c0d174907481010182c0c1c0640c0003030003002402d290a20340c1c0c00003000c032210080c01c400415410342c884400440fa610a9803501c0815a00070b010070413071070fa940241140e19020b810642d004c0402c0c00820700404014500180c0b40260202034450384407203021851520883d18070103030303110b10829081d901040d8065a80140b01c181c407000d00380800e42d8200032416508110345a054442405040c21003c0c080c0284069850803104116500c05038000340000c00c05002c0159050506281d141a003040000442c568000e400802804040c80000c0740001800600d00c0007410b8011030406200c8011008001503008981241641213405007110304544c45d107000322009041548005000c005036022500050003518442c134140e45016515500c040c62a00040001140c480b00302c0c0003aa0022410440f02aa1135021100603e1030710306040d440c091403041a00c4079003415600c250040b5643c40742e030241c4405a10017800d91306030f000d4070751249000384 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 312540071 1250 312538821 312538841
    0xa111306032c06060f030a170a050d1a030d050403020a0b091807030203060a14030307060c12090302070513050f0414070e0702010e1216260403050610090501051c020f13 74
    0x5030305c80900202c1c51030300285a85085910250070348440104040e000300d541c00580505003070060030008004268920320447e26400305800c019076641000b0400e051070003000111100034072404000a00140c1e80758030b005811501d00b19189036407090840089501880b80601011202c104181800304454141d000346205240c02d0f942c4c00c1619944010500320020729200c0380340c140e04100420340204509800100038100341d4286542c14024420500d01200c0800c8019401604090740500140c07400f40c6120720b048400c40014059418905032010075288050802007421158030340d8055495004c1c0075200082c000c9208880c050700d095603029029080303201302c00d040c0c2d0140080c03810200121105a8071048041c02400c4a042c1e45a40d1314818512011511914000155030a01000d401300780104040c0d4841d0020303210a080c000c00c0445c45829680201245e203003401d005000581360882c2d51820311000d0300001902d848240041004d440d20001c0160b00401d041079901e49000d895040b982c0c3c04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 312541321 1250 312540071 312540079
    0x312020a030806060403110d0309030209090a02090c040602030f13080a06050405151b090d0803070306030b01080a050c0402070305121602070b09090708060102240a111306032c0606 79
    0xf42d440d5800c11215100701c0c040102002c20030440384039a81800071580c408140f003030500242c41f0703071a80c00290104404840d003042a40c0802e44c10b004506150400c0d54111490040d42c40c2031a0600f08007075140d0140d100c2d8403850010100740160f06407501000d5400600c0c03c1c1e41079449005441c01c10328080c12007102c0903103441c4211800e83c203044c2028a6464403900d01d07510301419800e0902d986404503401401c8003a84902d0020801012684150066001c1c94190300c000400318554640f001801c40140c4c0603446540000120502080002c140840e01c590308880c0107949903510320302541c15000340c0c0e8441145520580400c60440c450a051170701d0742e4566000c80750790650702c03801054544100f039a0250060520008507010902070005540c1100d01401a1500c0703501715039041e0740106204001300c01c603105c01c50034440e114900e0700c181e5403480a87c04010b4544000304070300e282c68221512403482016513034008649441d880007203e8220240342c030610100a024081c10fa6661407040c0d603c0c40c81 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 312542571 1250 312541321 312541337
    0x1e020607030e0a0209040318081c0e01020a03020c04020d0e100b03070506040303200a05060c1e03060607030f090b120109050106050301051c03020c040507080f0703061d0405070312020a03 82
    0x3541c2d00050301d80c02056005026003416580c60383c046401c9141030100105a4200744004901c4840a111090a0140c105985884100d62840003840d29000f41030307550545d0007541d4001e001c0781c0c5c08208003103281c806407009656280b000074604001c0c003c00342e985107240034002035203024414030341050070701140c2141102e2080f501c8004102280c070071440001c0c0401d40c00c0350500b20280309282424a60302e00072094078a000c5081d1229401c1520486102c082c040d400900c1c01c066500000042c00c418042401b114214600386021034164421007034040c0034041340b858448203003441017250402400d1900000c0f03072950b20304018064105004c1c050703090681c0c2000c00205900c0d11527020340b8121540103000c00046001f41c8940002caa424150075801c6001398600c944242d12030b40a41401421507585a0b00c0d18034169140c120100030242000c020141040c208000d5034841c1d540c0c1095252010b082104c01e9161407030450b02d4480130344e2005044060844008440980101b16282050300949405e22 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 312543821 1250 312542571 312542591
    0xd05060601030501091a0411070c0f090c1e050c0a14070602060a050c1605010b0d0b0103021f0e190807061e0906090603020a0e031501090c051206010f1e02060703 71
    0x11303075110041c1031030111014050301c42c45181503004000300300300c0004100d00d04903054540320b00d1000c0700e8004a038000c0c038011040160180b14444e40c940c44065241c1000d5240c100c0c42c038903002c0501c0c54551300c2004404111222090003d010200706903900200d0712101001340044b035a260000b6200d560058012a070002c0e0200c13030f9500600e8030882002d00a130b17140489416004180417400c0506440c070b50b50b1002051300d42e845100c0c0504405002e201030285641c9503104100c0c01d4200d51945210171000201d60741c0e0740c00e4110002031420a41200d460005a8a828018200c0426944038035840e10802d030002603403a40000e0021a202031000340c07450b07003904900060b207210704c41e07220321400151110010400b4074441e41c023070b00c0c82c240b180c507040300c0c41110240042d14100f01c00b8094010315027900010420881513104811052885051a07070410007414000036503601300504242c1441448240c1e41c88035445940e00c048040345080484488203032050000303645038011100c40c00440c0c50544106 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 312545071 1250 312543821 312543839
    0x140910060806040f060e07320409020a050609130f0608070518070806060f0712020c040b090103110103140703060302090a0501270f02040605070b130c150c020d05060601030501 77
    0x6440780d50004c941003e810080d40d6071030003e101c0e2244a0481e4024a00003203440c01d51030f00318074110041d55403d1400030010400005140d4414200c03148650300d0000d04c8070050301c499043d0011908110b541a0304d680c815004034104503000100502c8141c03419002c815558070fa9803261007a00c3c000781c11a440b080d128010b00a020400384004003604c04445c001440e018400d5500ca030780150090a068207120100b07440007410340001c401152041091020291820303070400c8200264603003100c003441824400004651490410700014003040c42410740000e107a4040d0300030000c201c0301940f40d01220b01d81980300500800c014001203200380400030104142886a0041606a0300615030401480c01b40750380329607040f13040b400c400c055903441e500f540c48100389600c040c1c0020700d000d880700d076910601441c100f0243d4030300a0180c40040502c11041d4007050031100c1748026660806540c082d112010f60003a01d068598490080d840310940300b85804200000c240d40b401001c00f031301c0134400d030f07625180da00d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 312546321 1250 312545071 312545083
    0x15031611060a0504020d150c020105090d0c0f170c03031b122d09030c01060902040e061e040614030d09060807051e041e0b0310060c061409100608 64
    0x8481907611000102c1c0e00d840050740704640044c07008180144000f900c1d590764692500004507140829624040c042c6e00c1602801015480f03481c82c0040c00380d01c2c4c038001000d040f080c140384001d8412910401c0310f4080152001001c1d0309811140005074507102030358045130352544200d494000088016100901d0140c0b03400c11f55164a20101c151682a81c460416100301002d0b00703143c106102c0f2003840050581404860b19024850040242d5662540c1107000e03402d5601e07541c8400c94044c810801041031290284c1c3c110b801a104403650340400c0c0c8000203403401c0a0380c01d0050f5501501c2c164001403140c808944070842c00409500b500c0b0744900400041d035121505200303480c04259006d00050b4140e118000419131016903990f00e40712500c001c580006280c0160f001184e48803070f075042101024401c031103c0d41c0144100354880e80b45141c00e00d5860600d01d007511400701484509844031080100d00d800000109000c0041002940b034012091941c038442880040f003c4e520304280824401e42c00709007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 312547571 1250 312546321 312546347
    0x6090605011e090902030c09100306060306080c0915031c0e1815060f0705060114031501150e0d08030f011403160e071b0317370b150316 60
    0x12103442518000b13090010350b200500000c1050b02c10030001d44230f0b039240e480361031509940780da00240c0c4a04000010301201c2164020708810b1b40501c002e0340d11513960112584e4000840142d0001c20085603001c0703481d084824544048810a103455040714983c404c030f03002280e0303e04685030140c3c000740f002c804580282c251651040031305000700c2030684e42000c400501d40001c001156918041d0715403501c2d8206242a0452803980750481410b400c1483d003000300f2140107016004070031240d450001c151070301c491494074207001c0c03004994418800c0d82d40d0065502c1c1c41c9400445680d500c0c90401e460f115070001c240100f540401181d01c0c40030003420000f40100454190f81000d510142c00c0091084400d200103081c1010090701c010107507074920a00740300d4500a0710a80307440c400000d04045584605500030003100c0b40080174035082c8002440000043c042c480c1d40c090214540c005102c500d800785c52001c80c843c2e002a5007990741071040328502c001354816a80380c034040901c5c0400c03e0080388d0740800d07100 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 312548821 1250 312547571 312547577
    0x6030f222f0604180f0e100b0105090406090207141606030e0c06030403050a0914030d0507060603021f14130e0601200c0109080604020d1401020405031506040c0804030f0c031206090605011e 83
    0xc48002c1c0100036400808d0403501410418107141d114800034050f54100c0d042008a945c0124444003009510708141c030700007450b6406001e6100d1201422481113515101d4401015121690440440300c18080c03c60100f0010b030015030780f0302c1c250030050100d52005004a0015040210010391186048501d00c0c00000c01805810101e407260b00895107500550b20607a255651450004010b03911005202d207603600f1407000b56460803140a010303002980300d1001c0c04041004000320403070000701100980c2510808050101d0507102e22004072110340142080c44e002034030030360302c1c1d0090a10000f120219080246e0322900c0d0544c4640c122030300c883c001c0c5c130000d4000440001250000f28905103402424a102000605081d944c00000746085981121402c40e00d05410500031682024000e0802104903070502010070708007036400804080c50a80e1410820047c1145401018030540d044074803001122024080d90381c58881440050040380303d4140403400c00d04144001300145018040000e06a132 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 312550071 1250 312548821 312548833
    0x90f01140d0c050913061e03050303070f030209030a230f0606093c010e06130f2009010f08070f14070206030f222f0604180f0e 56
    0x500741070251621a0102c0c081c0a4184a24081c50300c40800c1030b803a080380c800780407400500d81000948001403142500003100d441f0a000e1011078000821280c102c0810316102a4101c5180000c070001e009015503140d05024084914050013602d8000302c12090000c4006003c0f0b0350720300b100690b40c0540060034090381d0000380020b4500d103080c12000e98088502d4040c41804603192580085240350600f5400701040c80d07400b03044100c4a450174090150040c2c041c101800c0c1132000014000b0b000c0101201161615010140300007001600004e861590420820300c1c9508444d122601c0341d0018800b00d80040d10070000090801c2c821007001d0301400103602c404804052003102150450381c4c1c6202ca0400090800480c0c0058540f10001c41c031a200750100387c80d031401d01c0a0000810308100400245003a8010280340c08103034009101d28101062100350054982b21414001c41c00300c281c241d0540c04900484d0002d0401e5419014095007805142c04000c00c0c40824a814100d400c001d901c2107a5034011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 312551321 1250 312550071 312550087
    0x10e070510140406020303090106060507031205072a06150f1205120d051005010306060504090b030a02040504030c05010b030109111201110f04050306010906120b1305060a02090f0114 80
    0x14542902040c040d4544240c2c0b454094864507559441a4040d0703005038030001c200050700700c0a204807800303803526290081c034203501a10010444040504070646607591800803515681c0201106d0114070f010006a40d0200e01d40c005921503c801d040040d01da50b8200300399107102c202048119800c0c0d9032401c00004426042004540010f038000d402150b0910400c0180340300120300002234044403003010f401142c00d00c3c0c4400c1c400002000c60388458141750400d2028015541c00c402581c0c00d8030818400000e950070010000b0f881c04024240107900546443c1c140010b244d803048155800600039002480141081c0b02810700700c1c2d9040002500748403100e40003001a140400101c0103d200f4480042401c82041e040849250300c00c0c0318101c40701c3c80006080056003409e000e928010031510784200001860082f9400d642e00302410020540c0c3c40040002d8905c001170410042c0b1180c0107000c5408074540140c401000703501ca968042d20460601c1680e0341c0641c45100c96207140c0142103d40b50410b121 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 312552571 1250 312551321 312551329
    0xc0b0c0408061b090306040f020f121f06090c03050429010611031b0c01030c08011211030a0512040f08010203090d0302162103060803070c0608060f09040b04020909010e0705 76
    0x20603404190424000c01070b640d00385d0b07020007045014500482c40c0c100200e1a510410000c1106221ba0500450200b818030040391408901e58140054002481511800403426a8004c14058001a06403071400800310210f55256102c58844c52107544d003644a40b041304280c10b491046810460042c0c42c0c90001800a40d1040500301851039401040724200f13480d1104058440c8144109900e4070703032001e907a102c260340e0715004840250030030b41000070855052803607048182040440203484401c0c106c040d8038071918200170300440c2a402001380d80f0503003036410345d00610358024464036039000007440300030943c100107100700d0f030092041c2e400521b00c0070ba6103a815030194000c0c035071100d00c2803c05882940401c0e0038103040d5064211040031110001d400f103001408858043d00410115441803025034001440c0f441d40000b40c031b004d4200f0000650b986070001d10700003005204660803800070000d1200701300301800f41c640510700c01c458245580e92220403042c00c80c0e1011030785001540c81130008100d5410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 312553821 1250 312552571 312552601
    0x4050106050f040330030b09100503060114060403080a020c0a06030507020c041509020c031b070b030106050304230f010605040519050a1b0c030e01090302060f0c0f0d0c0b0c040806 79
    0x1100d5580d582c40c1e01458003801c0540301d0b43c81d51321702c08aa1110b04030304040c6011405d041c2d22034500b11145904a0410b40800e0340e510741400340914107541040c40f018a40c2d220b00a4900441d40043d80d80e07a60115280001e40b40d400c2c007041d0500660b501c69020032064064040c062085002d50700030030110008000b008058094031001b510317072003060040814a00304500051400300c44d000001d695440303189160740703d9910030746111201c1d40c020700000d021017040b01c01140e0468110b841d0003500d030f48a9082248606040a40300116000317105401000000701041c030303d4400c00b2282c020000c00342d0356006e11080c0c1d001110000c9061030981c0070490002e4a40e070040d5000010401d0010b04c4a002c0040f0880c1c0f003540642810120b00c40c00c158804266004034900d0021a084ca020420300d403555003ca00b513405100040c140c2081d0100f028100410304216605000480b50200d0f103080c102968003903c00140034406507080c018042c0001d491449050031242150b80000003081141c2d01c454130400842 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 312555071 1250 312553821 312553853
    0x504020109030512040608010e060a050112150e0703150501020d03110c060109050919030e040e010b0307030303021c0204150305090a060509030a08070206130b130605090c04050106050f0403 83
    0x310000000c008200200800074004d0790040f9060b40d21401c06d030000d00421b40580c0414044914502004015290030f10010102d800030b00781484a02502c0100c000502550055051410b40e40d2500040c14100c050019010382b481c1c0d102040b00b01c0004d043d81840d650240185400350348103080c6514a00d110340d10212418080c443c0403401c08007944405428001d081c0c4c04500d0454075041031280041c81801581c0340b007080300103008110259550060b29008429415038803840c0d98041c02540f16100b9007002c41c003440000e081d00e0540f600d0340b4000d8020f400c48c40c01008508400b21100caa500b00368401c036026101d2a1a8151112806481c202c0c05020020084c004a0103040780680010b50280a01401841c1245c082e40e11112a00401004001c004101904640c000414060f0301250340c030b002030304c0540203c0e001d059580d83c050482e64481107090018455403820041003016903001c10782c0d400700754003101c00f80806d90b600d860850b5940150a400e401d520307002c11007000041c0b601c51148060b4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 312556321 1250 312555071 312555077
    0x9010e0111070b12071704030215040f0b16120605090a020d020405151c0b0d11040618090605010b190f020a061109031002160f1703090703032c010305040201 69
    0x20303600c801031620f45400900c107034016404110180301c1010f40201a025420201046a010903d000c0d100207558603400e0400d0701440418401140a010680341241e1003103820810301da0040c01d018442840c0c0d00d951440315000500044820450000c15008800403204010901c130341d240c86544401009600481c1c04510007507080000041c103490352030301d04041a50b0403000b01c2d11100b5820000410011444500d5103461410454070955501c1d40c02c47d001440e00800101807101007103000c04c00400c5c00c2d0b08074000107a4180c01d051541c032020380181042034401c1c0802e00c200d90781c071144001c550051400c01200701040c40c5855a00c644144040320022040c3e10403114000b01a0710303098221084c04c1d550b200d0744540051461a2401c042100b4800c40031905011854464043c0c1040310801c030380c04008040131440806401400400300b04007600001038000541c2d40d05102009070368698691008030f0100b03042c1003043c0c520700084091404c0c0741691070820916031031350384011001814010001c03814 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 312557571 1250 312556321 312556333
    0xb04150b060c280204050f01090f111b0a0803011403150112150b0604090e010c0f0e060c030405040212010501140304050c0f03150103060203071b0503040302060702011b050a150209010e0111 83
    0x56a170303a008190250210b550380300d49550400034070405403013440c0030780c0b01c4403801d01e8010740380b035250403040303039902340c80802d4140710036096240c80c40c242814014007804000020001080c83d62400354680c100350070413001c45400d10343c19101d01040e9002446a03582c0b0045000348640810402d074002c400380000404002080d411f02c500003100d0341c01c1900a10b50481d81c0d84512400034009100b5144c858006041280c901504610300030031010041c0d91185c00f0301000700f07109011190400c155406044018400d5403502d100007582c03d108902441418005441e041c0b48100c60300500c007c1364091500f081c060030700440c040090040d050030348241030b5058400d03100c0b0f03000c0001580070b1141c003840c03094101680d00e09007050001e107071030601406240710303411552070b1100150001040720308482c2c0c1aa000e580328119400103882e841c981124044041041044503000c000000c281060403900c102e04447c101d500c8004e4000c120b0042d4454140072071074004111030030750f01803942450544850700031108 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 312558821 1250 312557571 312557573
    0x402060c03070f0c05031606031a030703291e0612060703092112050606090310020a021002090d0b0a020c0f011a030d08130507030b04150b060c28 64
    0x32440e4030401083d40c1c03c0c8002942d9800f00449101040000c080850040c20980780703491011446c00303921300c03541060507a100f90f481940d20444070303100c0035030b50018141c820395556400d00e541c07a41200c100f2401800014101c290400041011a60064a000203029841c89440d103101500210240c03541303500c481c0c1d82d45842c11001040014921400d41135501041041042c9840c3c40d9884950798980f00f0001c01008161515a008050104c507100304240800c01d5101c0101080c0c1c0351041c622000e4243c0942c0244c1074030307046641c00502141103079600700d50350a0264026035089004099006501116018901010440002034140c00540b2410014505400014054030b041012074480140fa516048000d041c03240c041005034844000f54013503e0500100d810042441a0041007000210959100b44050040402010300a50750044075440d56003068244200c1c103d03071400b40005101d0610300020098180030042c4c8010321090701c020200d81d0f049250200d040b41c40074200311900016038036010 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 312560071 1250 312558821 312558823
    0x50d09061e1b0f0204141b1b03040303091d06130c02010f060909060506060705060112030e10030204080606030d020309040f0b09040c0e070c110f1f02010b101103040303080402060c 79
    0x181c20703103114981c00c2040220f00d1050105413200e0342c46e803026201b07002040203146d080c681c02008000b0303094a4031700c0c0c0c0d4402d0307040f010035846a90844000640300218002c410035402c45203400944141c01650540c40d80301c414100525101100c21942050142a41c1d5104c10f041d9000001c00c44118000800c0c1e00750042d00c01011681d1513071006203e1748d10384d4150000d104061013020380040081e074600e0310f001842d03100c42e96542410300c070385141c1c90038a022107014940720761041a40c0e06c90040a030700c1028222032006019403c0790061042600851012641500d400140c5458400c030b0354004d181010b40c800c082000401448021070299602c5500401035992542c45140c40740c0c0c80f441810b601c042c01c3c1902504a200014086820704c100601c9600100f000326803200c00c1508211000310a42c2c50550215030300d13100d07c8110030545246240404026a010b41181c40350040a8a0400d030b242100ca000b2034a902412042e903c05030030401c804d00202e4454400c05074003e0010703000c5464150419191 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 312561321 1250 312560071 312560117
    0x1110a03021c1a190e04080306060d090f0c2c0c0c0a20220b01050c010e150709030b0f061c050601181a0f131404050d09061e 55
    0x100142001031a640429481c0001000028007440b4241136902030400b2540c5000f00c0001d0700140031a800800040e00a0382c0f69000c590701c0841c0a80148161082da14010442a022610031603034051800004075039800c9140030300041707100c8006241100d54083c09032803c20035000d001f1115000c41000f014002040801050343d807175100704502d9100310500c01c040d000c42e4103090b80b83c5109039014002009003050320901c041e00350400410004103600b1010040c0c2d110710070807042d40101d500313045404420100108420790044104030604105544001d01200c0f0303030300c040c000103000d0344a003004a00b040750000c0390585c4c44200500f01c003621084114410426101030f0701c0880301c3c0d0307200100500150303840c5045500c2c4c00d1602501408081e10405032004c0d201a01c01e9034038003d641a060b01c5006a60b0503074600c114078054a0308004648a481c915030341d070350307040b1001d40f101d1040758010790384a41324801c02c07400c0740c0c0c0343c0d50f840c0010380030505640b44d180c80c428400000c00014429804031a12881c3c20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 312562571 1250 312561321 312561341
    0x306270a0311010507050a050d050702031204050a02091f09090206091f1b02010e0d0615080d0311070519240203010303030f1e09020d0501020f0a020f01110a03021c 72
    0x184042007428074045509464000700690101b0400b80100c0240700d4100341030f643c0c011504000802c059880036001c80c070358011074072a030090001f41340c140000e1000110340200114000d565008031961000c2103a0080000342d085180e43c201d00e00d00822242526502a01300c0c82d1000304501c2c90840c5845c000f90003403c1c0d0001c0041e80b609400b0041d4109030300b0011221081d80300c200e01101075183ea4002821900c01b42d004603000d842e2042c20030003005999404174850f403200741610180d0385d8540040540e90b58404070350101107450300d02c81c1c5d014088000251144a5801802407466056004822400e0220a84102d84028610541075a400d40d92882280c00078014840140c4940c51420300409481100074150320b500d1400403910851414600c90241031044003e0120712400c19101052094030a1000a442544045001400d500300741e0014032009070164201d070715011407042441d00300c601031503000f4002402000754a1a180c02500942000b22058130494580305004185c18203803030301d20340c0d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 312563821 1250 312562571 312562577
    0x60f110a12090b151f0201293a03030203010501021002070b0115021207050a0213020324120102030109201c0906020403050d02061006090e06040e030708070803060418020306270a03 79
    0x307004450250381009005c000b0f0944103940d40c0d418903036010410011400601c8000c1082e27030740d086420014000300d40040c102625146044d54441403c00500075042800303054018050080444034900483c02034440540c0c020030704085a07403820320b0b40e00351a822110b583c025030080d15807080c08000300c8400391299500030006003901c00494030403c0f404124166004807104d01c10300500a46031311408203085080e00101011030030a8404000402940c3c1030748618000b03600000000c98000407a403c5107074510004002d070034019040b506d196a041c00340e0705551088000e4001c01e0b2030280e0458111680190059500500e080d4407902c5442c203114146500c140568000014030503074a50701036030720b0000c001c80e161401080e03091180910116601500442c8144e071940d5010f028958103004a520482d4400c1e03080399602030034541845c680c1c0084a50030b100f18030781412001180d58012001e1b10302ca41c002c02070081642ca10351020700b0304468458101000c610705800d4105d20008102070460315000f44c0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 312565071 1250 312563821 312563831
    0x40f0c0905150d080a210c02150705090d0f020a1212020f0d02070308130b032707120f14030a02100614030a0b04060f110a12090b151f0201 61
    0x654030282c0540c80101e82c021014800c2c50008a00f080b0180ea074003100764904041d040c02c00200944451941d82003a42e09985054103070620150005245d61005101c02005d1001c1c1e91618005c1d9964012420b50395000702004880ca400141d0580f14400c62030320041c002d8080350307104c0e9003e4070a501240c5088a100e00800c941460380f94041160f40d8440c4818030007040000300c41d1000944941151000421900700441c0080d050354295801c0e030090044585415101d2421810404e2101900501d50800480344000b00c080002c0100c3c0e02025100c4014190b03440401d2680c0300b81e600e0300c2a4200303640d40a21045da100c0184400d000510000340c0a41c01018444d140c0c0f5448400ca86c00390f480740008014440541419890208000711156002860359410b07559604119010300714410075103411510300044035882450850280c01000e80d2941d642e0740c24030500080e00c08072008a400607088440490010f441c80102c030440c3e24801e100984150b000e58810745041e59403251540c10000036035120 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 312566321 1250 312565071 312565081
    0x50304230d3b010309050c040e010903140c1902041407031505120601060503220b07030608161511030f040504050f010e0604020d140f0103050105010f0b12040f0c0905 73
    0x19038050349035001c0e08102d00151a000b090034401c0c02c116400b426042c191542c0300401407050030311112004031005401404028105e0070518020090328000710041401498030340c0e40303100d00b031081c2c99070f040284004164002c5212010507003104185e400301e0340a41c5034490320f0480340b86a803103a8080d0640d03440115000d19080840d44d22000340c4d070459030044100317144010714090b00141c880d0440742681446079494072142c13441060848000d00040c822011050584e003040300042d20103104c0c0c0d21941d0b003002010744485007a03880b14521125829010030881d424010141802c01c822241d0100c1e0134020390f24010f501c24503045401c2010440d040400102d001c200b142014040d19901c0040142c8040886d8109a8501d48440c8045c081a000715030200f101d0a510140f54481188002d800030713402d410380340c2000d800c10220070034002103e0035400d0000001c0c0301c4203d0712121081d03807ca00c1c0003908003600d140c1d241012800c0140140e40c10040c0310901400b05000030f088401420031004080f0766071804c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 312567571 1250 312566321 312566357
    0x1d0d02030a1103100908070818090705031b040302011e030f060b030402100e090109150509012c060609060315060301030503071e1509030309120201090507080d050304230d 75
    0x1d402e104d42005052500800003e000f500403260890f034054110f07a2201c4010004960780201301c0340d0380b038202c1d507007409011182c1d4001010714401c1c403082c540740e0004d100102581025004600c80280801d44507001a4803101800c620074034000401c1c43d0000e40008410500800e48401d80d100c641880310001c288800d50514601c00e00d1101480e080400d80103a107100421a02c900510a0380070b1141e442d400c4503c149442011800107290040c04c1c4489541c4030014061b850002506821945100c01e8141100101d980c1c071251280720000c02d85814202d0517024003205500c020102034819a00b19000d60440d642d86018502841c09980215240c02c21454910b0510703519481c07400ca01c2c60443d1545000036070080046100e81810794004c543e000b003516007600681000348004207010f1260b2140c40701340d5030561040c41c54600440445034171550340c8400c5c0c2c3c0c60b11703d02401d100004030104000b40203d152100c0c034070f09003035445031611541e08800c0300485c242884075440800040d80d0f21501c44214907 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 312568821 1250 312567571 312567583
    0x2041d0a0213050613080d1d0a06020705060901020703060606050901020d030e1f0f1e0f09020603060132030403081f141504030b09070b0a1d0d02030a1103 68
    0x104015045241002402e00340052000601c5490b118950009504000d8920580018000c000b840116800155110006410042c0c50640300090020840b0b003414185040031a0000300c83e025009880c01604200620007a0b6000100c1c090561180c424000300040281c8241001009103603170740c1d503d038411403000a04041c05c210202c400c060810028140078800426140c03280d0306040c50701210511901e01c048040c1580c1001c05002d140b81035003096040d4041c1d80c5240152048210070010041043d045d5012649184000b0790881c40500019400d5401403603410b05c00e20301040100c0c103a01c20403020396243c802012040c40c02840100600c0100b6810941490304460480444000c003204550000d801107410310944001000c04280141e082d100d03400844440960042800c0e030f00c0d5141d003007110030900d0030342d030190242c400e0031000101d5070484410f40700e00c0034983c1d07500c00500c51128101192100c0da80182070303100c1210502d85005950401058007140d12800c42018000300502c10141002c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 312570071 1250 312568821 312568831
    0x16080c07080d18140d0501020a02070f0902070804030215040b030103050c040b0f101202040f09061404050708040b0603010209040c170c0a30090503040e071b03051b0102041d 76
    0x410150f908a0111a0100c81e001c161440c000400c04810a030a0000b0b510a580e410040d03c3d82d4400904450071b036901141d900d040d141b2107110b40b4545661071440c1030803403103816001b500c400404d00051006142c03050030700300780300b0600502604098a901e400d003503650003a80111280e90121928006070306145c05050f1240c4401c88000b0041e1071048007042211002c1c900010401c86082d42c500c848103119415100580407000b1090010713a12860f44400070001801451a11007100e13407600ca2900e0203018184c460707921607580303031003584903690740114001004c1c2c05946d05540a1089606030b403102d02c10042d0f411180c2d580d041110700004044040780e01d01500a203071a40c801c110007464039400520714404030125170384554200030948800050100c048103030240c10b03402d04100105101c4000b02400684501400030355030350312001400c0c1c400040e890001d40103814183d4910010a00500280141c20800d1300183c00c00943c5140840c00c907407098002d294001c00c441180d90041c00750505d036036406 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 312571321 1250 312570071 312570077
    0x30605060d030c140106080d0203040e09010b010509240721030c0233040b10080309011b08090918070e04020d06051003060203010e161b03030216080c07080d 69
    0xc0c1c0302038400510000075110083c1c4403110441005901350001d60158004111040603100030103100c8500a407268071610030b10000707143ca60081281c428062043d20b80c5603805840b440d25014003441070000107100040a40e1280074000500090500240e00034411548680d114440351703a051911800399000070b01410041500c0c0c000720f0040141c001034003c20320800051554141440c04440b031510b180c090401020800c0b490051004003c1c00c25141402118048000b02016442d00c401954038026000c081380000d600c003010f910010807085404c06082e0103501031b00e2802410f030b40418228002611607003420840c600c1d40402d540014859980600700c0d00c041e607403580c1001d07000100e00c4400a0009000a5502c1000c03903d0040e4080785803000315440401503480e03680d121a0316000081c11182c5407001000030441513192031040741e16800c0f40306514070000c804696a24110000c3d0401d1240d034010380704119005001c40d0010000c0c0a480c03000d4070050410b1402d100d1b400e030800403680c3c03900c070034 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 312572571 1250 312571321 312571339
    0xc0706090e060904061806090609050c1503040201081009020715050c070f020f031c02030301050913050604060e0c061206040b010306080601031e0803041b0e0907060e030a050708030403060506 84
    0x42d40c1d0f000d03100d5009a00080045001d100d20a80003601c80807485000f40181e00d000c8611007000500d40140142030b0081c0162500c2003032000520a041900d1040100d0480041000500540c020b20030a034000128020810110b42c81d00c11000c100c0c1d02400040d154141c0c00700b5140c007500c500d0700030550303c040e98141850900340d40b0340c0c2d25201d000a00707000902c0303428003540180341518200107034400ea40c0a6072220700190440c42d0065165802070290a014181000016514101c1580c00d070324009d82c400020f001e569600d4803003000070f1070410101290342c0500d900c0c0640781d541c0e10014110880350440d0241d22402c01d041048220750b100c0002c0c60605081070010003001201090300c2e41180d40050000290380c2001d03c10003500e04440000902c1044080244001c3c018407000e8141c2201c2529148d5004a03160004100c941204a44000e840d0780508028440e152162400041a0b040541112851845556124102001034000c10095840450100300344000380c0a0550091000c1e551851 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 312573821 1250 312572571 312572581
    0x12010b0706050c3606030c07060b060304020d151b2001060510050703090302061803100e06130201140d1e0b1302030705160c14040e300c0706090e 64
    0x9070f1842c480380380f6004c0840700018907440000704000c0f2400800d005022681d070780741442d2500070b07541094400341c031207034584440006141490b804480c0116002051840e11421650f10b65006803100c10f2025a00d03a01d440c00248248450920030301c0d00c0c3d2a946841c2520904d20901c0c114140d036248142b00c10341e0511400f00029103500002c54004802e605e0019500c440310704090303560b68003c0c1d1000b03411400016080031001c83c85000010049000c4041d1030044406900c14810340303035101c2000541e600000b0104041980e2201580c00091044c103000701200294500c946440c2c020070000c8040b992901412180400c01c0f81410040c4100310030704120810404011409659a03201444013540e800004a841c0380d00036400c1d145200110142c40908004070b1406040400e104c3c480c1c0d121030400d40d00e100410346420700510480d05014001080f580c0c480400f055035240f81350b80000b040110748002000f0300204200140009010540113090a500c2c10800070541c1107158094139004024500748a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 312575071 1250 312573821 312573847
    0xd03091119080d030603060c0c031d01031d0105010609150206010b03060f040c020a050c0a120209040206091804030f110c04091e05070e010503030c0307060e0312010b0706050c 77
    0x410a001540c2a54400e00c01c0d07020301c825041c0039000302ca454480d039884000d01590641009060341d104003024030401e000b8040c1504e210090841c0103001c20542040010740607000400d0481d01501450702144000e88006c59074003690b03031282480c0c0103075160001400882d4000c03146900a000c2e00b26015544c5503a030b2002512840c040c0203100041c00000301241c4190341e092a5540f4080c4001e00400c42d43d040c1e107001075503947c0400750482e00e50060240490640c9401c0b100f200c02c50315004056454581181d0800009210050080f42c0c06142804200384a44411031a245581c101049210303140c04c060801038500e131030b803101600030040825403042e5550300c0412021f05600c019200400c2440c0146008080c540d10000d074004403610208803401407100019030b07102140c0d800e000848030360b41c880040c90303164800c000059565034820801e1100103041607000786036003c09002a282042c03281d0401c0c2d08a600282d01c1000307421000300312002800030500c90342c1d400080010b8102d140200b452110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 312576321 1250 312575071 312575093
    0x4021e0309011b140a0212030c0703180609050105090612090f19021c24020405011b05070e0c28080a14131506090207051905030343020d0309 62
    0x840300c013000c0401c0729100c050003000400410926032040c035889142c000100344480c4c104400590006041e1445900c10100d90400e0381c0c25103100e5600c110b20582020010340341c03944040e040c83c0c1c02c50030400440320004100303141240118108005031030021014072040e4503121301d905a0114031420f2005000c0160b42c3c40c0c00c40c4807190700643c241c0e1915000d6050a0420000011106d404412803802c2c4104007245a4005c0007695404d881d0700b04141e0b07002c92071f446218102c800003000741d400101706004400b0300480c03103644455020801c5103024400c0400301d131403c28420080c2c058043c0d000c08000300d19001800d20317900400000c2c00300702e0580d0007002c40c244204058100500702542c00042c1d420320100c0c20005c0060075441100b40400303a036425201001f5880804251064002c4090107485268440f85070540c0c641c0100c025030958840342c0300c3c696444004040300d03856642a1071031017038503c0b1a07501010700b400300346034988020040c5075004c0d0510f00080c4405c410145040e65040001e0702411607 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 312577571 1250 312576321 312576347
    0x240307180b160b091011030133140f0d020415050c07030b0604390503090309100c020d030c03030b041e020306010315030f031e0503041104021e0309011b 67
    0x8103100c0c4c860031401350400e0240300249a0f600d040c490117480b103180c82c0f8001d6040790503040e01441d4002c3c1c0b01081213008001d84103010343d544400441c4c04407540c850044610980d11104013545080c0041ca5000d5040c4d0100c0b46203507040b50041402c001c00b0849a1070148101802d0030f00920f40040c2600403a240c44003408028001c0c5000303004140d1a840e16449501c4400c035042e2001c0300d8100c800303240c000940c8201001040c50070015204060148140c098034081e0030820300071030409040c04200404051703002c6c280300070008000701c810050b945808a40c1c040034040e0715541404062408c004042d1407414910900507402c215000d06101d41e000040c20240ca2501001a00d90321101e00403000303041d6001a01c003005042e810701006000d100390603541802d219858862150510b040c5280e4800000d0070760401142e014000100400ca1742d9010a404e40c00c0200014030b00040a55103000e01103400d411030000680c04001c200000b502407160720024503002c0020b20f03180c1c0c0108002032070651b002c05 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 312578821 1250 312577571 312577583
    0x1020c0121090b0103020307050409031b020102102307090605040504020d0e1e0d020105041101050306040617012304020303250503300105060306240307180b16 70
    0x407650070a2140e625003030280c844000910420310903050a001100c02800103901c03900511100140a2030584148512250305450304030940101c2c1100203601034840c002603066014100b9403038000082c5116107440340b10481c00c99010701c8040e198040744610010704149c01d101000310184900c5400400703850031220f0480e0301580c1c0b07407400b00c1a107020b444d281c010300800c1d01c04c03200c0c3c20300805c086c241000c00c0610f50320100d440100e000f403401c03420b0704c0f030945004c1d280712240c0e8140107007940702c3d00007194404809800030410130395500b04070410351444200004640d41d521078100002211410382400341e51400e00710700c41414241c0000361240305120005201000c401d00c135500030311004d4040200030340c002c01529151a41038004024400103420b9450303e10481c844141400c80036100080d0580c1e0000d4005811a034404051042d00c982c4014450320241a00782c0b1407180c4c2207050010b510901c925650743c05400c504e085190b80090a6400081d442c40b001d00464040040342490720a1480c2c21070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 312580071 1250 312578821 312578837
    0x15080f011e0f030f0302060c0304080405060711030a0303061422090302151f08030a0c0602030711010603050c0102071a0304060207020f030a03031d0f0c06030a110304061b050901020c01 81
    0x2259418003088154001d490040d0303000c2e4000140001c440000307000600035001d5503441d0751022604500742c442101d004105d290140000c0c0140d041c041301420050344100038101d922000140043d05e07085003030030224001798440509000389034a05001e4419802c054a0141c1d43d4900c14039000345180c1820740c60543e081d540e0380c0c0c050a05208200082da50030b000c90010340340e802c0c0b1500614020b207084d451030020b2602d4020020b6400c000104a80d0144003d981d541d01c074440780d030f070790b00c020f54005014081003142d0140c49008942080c07144000651182c4c00904040844400190402c00307a6809021148c1040c86180040410346080f240d12683c41b0b6401641c0d01180d20003c1d807030340080d40e0350380e80501c41c0391406400c1640680c45051036042010340390146e0301010214075a54000050001256002048810450b0a0400c00382d42c00405202010421554410460003a50801c490039205c0d1901d40f805245036180c0d03440c0000074000c0720f1409500d03011107440082d640c2e0380144141410000c0407 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 312581321 1250 312580071 312580109
    0x9110924030408030109061502151018020403140c2101090618061b020a20030d020303072c060c010e030a02100b0a06090b0d0e030d0615080f01 63
    0x150311000c42403500c45403016180d0802d402c2c07450030340c0c000b401080c01e450714084010407004408140d01e021031110b80d005088480e9a45854030191703001811300d83c2000c4882d40042007401d9803070b0031024108181c040042e152851418620408203d8150007602600320340d00784295502c42242e504101304480d110100c07280e0311400c0843c01011603a1015000601e424100c01803803040090126446000360010321041d120404840c00050a111800015920584071100043c4102800c0d4554a126401400400c15030724086410001000515401600000100803e140d041108807500b0b499681d1150a070a41c0705403c2204068400c00151080c040480d03c19007080003500440e400d0507002090f01c1e2100202e070400383d940c2501048074204242006a54a05420000000c404443d200d9440320381c214030303020600030198004000b0b01740079a02c88120708140001080100a007840340400003400b86c0ca0b10320300c0c000501100604500308114a0107100c203108802100c01c0c15104407614003070740381901c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 312582571 1250 312581321 312581359
    0x30507060c050a060c112401140303070503070506011d0c0a030b06070c060905040c05090d030c05030f0f091c0b07050a0201060806011d0112170304020402250606091109 74
    0x19801d00a06442c201a0308003207040d40010796007000c0e10600c046400014001a000700d1500c081087c60b80740c03440c05801002111a807046c140464140501230f0f03440c244c1580c58141c11688004410751741540b01800402c50300d0b0f4000011280703c4000300c29100941400081141c1c0e07841141904410961a040006901e603683c0d000c645c005944181ca07081259078842d00a46040040e124852280d49001e02c2640c00c0c40c0500e003120f0000c1c0008000c40c00c0c4084580c0c06903110a80c2100c00e80b880d1005008240c0e61514810092450340d42c41c0e82c080b5180c4c4544410400c1000645019050503c01d0002c468000780e5401c3e132440d00718045003000c036103585507400100d0041202e0340c400c80761441410000a0f04c00d20141008441819900600c2016070302d600e01c0b0400c101e5901d40040850b110307140200c412807142400342d034115200602c050b240401c2d800c1070a0a0451004165400c2045000d03000708000103481428010100c01c00b091000c3c04802104034028002c1200745400740e09030300b00c1440119a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 312583821 1250 312582571 312582583
    0xa020304061e1a030f2503080417071a0a03320411090402010903080a02120703110c04150b0f041a0301060201150b0d0c0c050f0a02010810030507060c05 67
    0xa03525851080d001c0b01c01c440006003005211045111802500b22140c50801181071050300ca0400010265074880c400d55412444090402c00c598001040020000424140c0200010f0101c407403000b080e1070350b10302d9640c2403100036808652142400d489a145105400054800001071810009a0200059140001078829294584980042409091040c992000300074003443c090002480035500403024410b650728181d40103404038022440c1000002e03118001090350101c0c51040c5c409800380f01092401580101c070085010510101500100300410420150311a40444061180401ca60098801d0944602032401100d1001604030b82035610b00e022540101030104000c05082060090040240c00c00e01841c0015400c0c090314500030031801e014801a10b408000c220f00c1e02004e04003140040c00c0c1d141880d41403100c1e418110011981c24800c4045001c009030290074400071901c0014618280101844810000c1d6a41803001c00c0703000481006441c0c05040503032408486042c0540386c49 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 312585071 1250 312583821 312583841
    0x9141509152710020d0b04020708120702070f0609051008071b0f020d0f0b010f050906060702120709050a0e010204080304120c090906140109140406110d06080706020706020f060a02030406 82
    0x4495a0542d80ca043c00781d81c01045031400d91714080000c045018100001d07840340359000f030b141c05002d10040d1034405150113510f07080105401100c03565a41c8405403818a54030781d00000118150010400050408100000c3c0d81802c626140c20a80303000d41d8041d180803000040918081e40300d40d4100d04004c01c1180041100e074008044819001051a100c01c05019006040751204a01400001c10354880e810b2041543c100030441403583c2d031000207210031a00010300590f840540740c104010082c1c014807030b800180c25441d401149500c2c042100c4800c0e1107001242d02400da10402c07082100e08008025901600d1000500e0000c1d0f4205040003514010f840c0c10252010b864281180304000c43c0358400f201c0304c0c03040c0b410f452040c0e90f6244103004454540f510382c00fca1807481c00180c0020030b41c0d030100700080c0c0604615410000710f48810401c9403d9600406802c0d404060b0a00605804110000c01400240b00030200002c40c521a15242c1e0301c00b17450001880d4020012030104600c50300308034805 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 312586321 1250 312585071 312585073
    0x51311120f0c010f0c0c03060b0f09070e03010b03070806060405070201021b010603020a0608060607020d031e03020301050319120509040b04020c030901080709050f09040204091415091527 82
    0x101c0d221860140e16660b181c0070b01404034550281c080f180c207005a090241d0f143d00004254031030340ca56103d03080a000550a041c2d480314400300c044210341e6562000b94061241036481031658400780003403600f12080401c19900c00e0b07009690070080c131040000d040d94454070540b004129501c94103c1a8064090f40d40050480800b04075804c3e9174000540c40075084034002c840300070480790b0b9110180c3c3c02c054182c41168004108000b11405030405c00e1f2a001700a10901e40a04400061054011034926040713801000039000001081035240030080d202c03034184a04032220064a0131b648000d482040c1c03c034200184500811900fa20703554a0b030005a107583d01030030655842d410041041d03101c1c1e02c0119010b0109504d240821846481204188185c801c0036180c0322a6482010401805440080040340d1141d214020f6200107519080103046140400004001d46040050050fa80e03107002400d80780380e503001c003503d01c5108607003180181c1c0042c060340740c0b5840004061118840b100320703080d071a405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 312587571 1250 312586321 312586333
    0x50102040306061503150b070f020315070c020307080319111c03060305010518120702060d0e0102030403020708060f070e060717090f030a020612070c06090f03030e0105131112 77
    0x1404d01d03868603000010440c4d030301000000b109400003180c0b599503006540b000d140500c0300c0d40000c0c800c151024511343c0003c04840c0c6907905944480a800c034106c6c2c1c801e0000e00b1220070081182001c00803140508800b4020b141010701c01065580043c1440d401941004004011a0846403040c4004100d0307280a81c8040180410303410040c026003400d00c4116025880c0c400050b40b210703103856002000300c1c00e401c05841c01c0294400e020601d50032642d400ea80c001010008079808031305502c41e0b10050240c0340f00158483c601070030017034104000f0380c3c000d00300342d0011820000c900c0c0b110030040303500c909a41441070010b2010303404141640135602005140c480418070480510b00104090008800100d03004003007500c0d042d00f03240d1102210030009400c032905001c000f03202080000c00c1c9501880c54548403490510a841c0e51054406422040c0d565462068040c030926a02d40030300502809903800074001414540340402c0c03101d014102c0030341b0700c04410b8806401d0759035900c03e000c008904101110703c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 312588821 1250 312587571 312587579
    0x70209061309050a0b180601231207170a0305040b0a09030206030906101401081602010b1e010305100e16140c160807030803160207051002010b011106060f0d05010204030606 76
    0x25513201030342402e80301c6011071800104841402d92261103006201409401185d103800306101c8050030850140c42054800c9800000940700e580644510000307100041c4021490140c484074140d49003643d9003950380040781c0040100c2d421000321412240980000741d942c4044020444482c142608001c2d40700d00c000061200340d6400203242401b0307008070514000940e990340c080408900f41c00b007100c1d000c00c0002c1d00251013410410000e00c404d80c80e0780000f090344051900041d407250007210840101e48443c681e10461540d05110300b0742c5c0080408200800c86092080c1c0d483c0c0e41d0002441008155505007139110000d100d90000320030039080e500100e850302100325a01d0303296010608055540240100c0c00610010001551000c80b50404e500b07038a0744e1258603580c11a103010080b0715096110b9a00700060321b44079130841d00e112120b60f0303000082c046422400100080507024841d6003e5201d5001d00c40a40d4a09800d000560011281903020030110f242280c00f81c01554000380c24540303407203000a = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 312589928 1107 312588821 312588823
    0x4080d030e0a020d08190c030c3c1103030712080702030c030a031b09030213020702011403072a03020a080f0c07080708070609080307020906130905 65
    0x7981c1c404041e80204075130004a070310031220920002070400c0405402c06140034403403034500d090128001c0c0b42c1c41c010141900200050940e10039803525105a140b4a03140003444001d14804c80d1941000345071031841402603032000d45070071501000c0340440c3e1501100302c0e49900d901850100031100400d100720340c2c1840041550065100802c4860bc021408001a00c0c0100e00e0341d80c089001043c00100c1c1b802c1c0030a01f002c0c0c10074441500b00c2840181e03140003004180302c2002c500142c90307070602e00040728112000180311058903400801d00c410b0b5035000d01000821190049411103000d201c003410b241000c040500500141c220030a500d0000b48000010700c000b040040f80756040c030301c45090a90030017000307134001c0c909580310703807400c000421090040c0c4009216500384000317011719244090740ca900c1340d018000c1c403d4a242002407841da48401000c4c50080c00340303c080110300e85a1901c0c0e = true := by decide +kernel

theorem cover : BRFrame.Cov 312410071 312589928 := by
  have h0 := BRFrame.cov_init 312410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 312410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 312410071 ≤ n) (h2 : n < 312589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
