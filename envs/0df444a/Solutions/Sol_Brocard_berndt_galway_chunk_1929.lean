-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1929
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:11:30.705979+00:00
-- url     : https://prove2.me/submissions/17ddc750-6fbd-4c75-9f6d-6a9ac71a3007

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 346762589 ≤ n < 346942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 346763839 1250 346762589 346762649
    0x2010207030c08150603060405030a0f0e04110c101b0c08070503070602041703180111100509010f1104080607110304030b07020604030905031507030f0f050a090c0816 73
    0x242060b01044020684650000c0c0c01510140c0680d100001a41c91405040d00c80030240c5c0c1c01089544140454403489000341d010b2a03910001c2c2c0352641120102d14001419111040b20121010701c002810903440c00c0148060454403107000418818603410803c0c4001000140792000f08000e503000c598400c100140d03080320f41260b006801c880c0c8031070081c148030009611a100d501d004580d40c03418010421008001e56400c00340610303081094290010064030794089000025849000e107a40040f40c1c4c0c0314a1003254042c80750300b400001c02040102101e0100d42011822030400c01c020301c4204180c1c03100161141d4006242d2601d40d914041c0d00d030303140b403550159400040000c807c42003000b4280d580040e0007403013031703010365540c55102e561002030644804021803441900c103c0200000e003e40c6c083d4011100000750b1880020701c201042c86a80200c1e5019600303102c465840b003640030240b190043c0e540e4003404185000c3e10580c210303118014610314080c40f411402c030340120811003000800040d06 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 346765089 1250 346763839 346763843
    0x306070e0303041a0a02161a0a0314180d0c0b0606070602070c06080f1303020303130507210209070203030c1603050d020406050d0e01050903250c08070f0503030f070206070201020703 80
    0x60040e029003071075116016007020705c6540c01172103030858411070044019103050031103010b5113154807600c072480c140e60020392100f8440014503071100d17920f0b00e1184405c1c03c00d80c41840e480200c1c0740c44041034a849810441c01c0845401000020014100030030b9800701d01c00d82058003180d0310741c0c0d070794458034100020380074040c4c000e0a01d52114100280c3c090704488201e00c50414050340c008550394552182d140c428000d9000342c0183c0c014000100c0d070f19014042c0c2050b16003c0c1c0c04488030030b65100e040d59006c50f5403240b16180303480e45001c01421410b100c000340e0341110a80c0003860944ca400d0301e04006501801d40300400d120071898003d81454091011212119002a019542c1d652182c802400b00ea00590721210a03a151001c0c001000e003041c801c082c001ca411102851400d010202907a40c03586414040810425908601d000003801c0e42c2c3c00c0c0d200414411002c1c042c0b491030714004640a29040c0e01403402a007003000702d01100c140c00404c4803544d6504a0380140c6525460004034a041050303000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 346766339 1250 346765089 346765109
    0x30a030e120a0f020d020a03140a030b0a0602010204090e0604110d03050f0412020f0a29090d05150f04050709020703020f010c050c120f0f07081204150513020306070e030304 76
    0x146242507400f07100386080b40580d800b184c2c2e500c00c007000201d0380c1e5111404003600142c04003005186507210900100300740e540e039150100d03000440d60700040c00700b41d190348001b025079030005007040429028060f000341c0841d980c000c0c1c006803900e600c440c6520040d60007900d1050b01d4400e042ca0805000340252035444200000a81d00c842d2180041e80040036202401c1c2d220b1001030b2035555462900c000303004140c5440c1051504000701d9084004c0c00c2071200c03401074079072080c107102060858032054110842130f4044c10080c002000c0c031098980b1740721400350081c200c1008441c204800b0890024050045603000f1a005076103156604049040030880e1110308074075400d00301006440c0d540b181c05089210075000540d0290100307940c050318103101c0e91403010f492040522881d102400581c0242c480b55008503c014a083c0000e20303a1850000c0c201d40459006240000d8401141902c2c0306d801c2c1e10030a0880e540d406c080240d00042e5641500a14090030880c1040300c446090b2020f0040d10024641c0348d030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 346767589 1250 346766339 346766347
    0x360903270302150304030e010809010b03030c06010f0b16080a0c02180106120e1c260417040506181f0c060c0206190b03070b030f06010201060b0903030a030e12 70
    0x41000400c40e41440168407680040407102100032007034080f00d0140d03500d41ca90104d00e13400300c80103465640c0d0040500381d40c0c0d580e8140105044d01e0034402001c00e0103c00000e00303541c0d81040c0c0c144c1c2c50200550840408184103101c02c1464030240d0080d10305d0260080c45642e1550380a940848064406000003501b1801c0702616110030548484114180c52a40d2118450f94143d850107400f215102c0301103001070b07444101200103481c0c04003030850360b42581c0d01e01005080c041c02030002c00c04c1940d00745684c070510100100400e00c119080844068804503221501d400c1c0340c200001c1c4107000d075680380881ca90340d00810340120b40e15040c40c514101840f0280528299100101424803500c500c81601c0660900e0000141184081403039445071032410302e05496030784c40c031003120018102005171641602c1075100c049600307802a4040e40c0310ba07501d5140b20515180070b50009094500d140d01001080030140301490041e40c003c41034800c0c610711031a000a184203001c040171300d030013518900c000600304002 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 346768839 1250 346767589 346767647
    0x61302130b062503030c0513050603180102030108030a020709090b19090b0702150105040908030f0711060103121106250c0f030302071a0c1c0e01060609360903 70
    0x283d040b00341a029440400000100c0b1005544502c41d03901c0c4100b40c000c17a04c5082c029498090040c42d00f0481810004803400c0c0501402c9089a10030780105e0140c0c0e0010910719641c690400100b00500750a650504c40080e803503850b1b00c0e450401404030950305074a00b81c0b4800d05c1c07d00c2c2c1e020b21161604003001107840c0c00c110001940b1803201c1c01103000c403400400000b18031130405001e05100603a00001c6039156594040358900c3da520081c0150003003000c05010201c240c0030410840340613500541c0c240101aa214001800e0002c21414440d560b411180c1000700e00410b5802d541010440c0841c0400f03120885101101e98141c40726004241c05c4140c3c20b10414194940d01401c0b070b040c40768400c402c00c8074100c0c04851408a088507900650101013012460f05403001d566892a0340010002003403080c0c088000364251b8426411200000c1c14034081040a0720905d0040d4400040c1c0c1007854900049038440d4600c09400f0441c555840c0da10f50028900b007504c41c0c0c40600140500da88684c4003440e001c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 346770089 1250 346768839 346768897
    0x20438040b030405010e0a11130b1e032b080708160f02030d09061a121b0f06071b05040c09050405040f0c090509070614160203030d11040503061302130b06 68
    0x607540290203403d0360314440003408401e00c202143d506004000300c00703040c2603404c1c03a210bd003100c01101d80c0500601c400601c1e40110b0b4288400446220f40c1d20791a2040850740003808140001c18a0080041035014840307200c0342d60804090b499400d24107080c0d01c0340300303441c16071031071044601d44105545010200320511981e0303407045441e070903140c4c074904120074910308111540c604110852203941180a0302901116075040c0c0c5240d101004e82600d4140d0500c0000600b40e8000c620151880c810400010488403001008040501401c48d01008203103030079900180050070030b001d0940602d42e510b020800f401820228540880c0c0d0003045100c0c1d40d1b481d0303c81c000107094150390300300309441044c0c40031400074007841d48003d07041d40a0210600f030010072103075007200440c6403200b640c0501080081c44a10b5059008444007200da42d8031130707907485180000313141c5011402420780d8014241c0c02000c030700607a580e07402c00c3d0701d0042031200454801440d10001e4400d11420602901003000200d40703000c00608 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 346771339 1250 346770089 346770113
    0x1d0402040615020d110a06061202040e0f0a150e010501150905030a03050f090d080f070302071d1602011b0e040b0901050a15020f01020438040b030405010e0a 69
    0x20a031024040300750b503128000081c03000b41c9007650158204500d5144181d10417001d8801e110092012241451020303142c600484600703401084142021b4804841035041c23500901500500f0302e001400c004154000b01c503218070f0340500c000c00115110780c500700c1503140e0760400700c030301c0301100d00802065a48141d01d600540c811500280800d014480004043c43c1c00b00d010611260981c5030140703007140302c010000342944003109655100181000240200700001c5c0504003400000300e81c0c0e0342d9034100342806490044150300007069940d1103016510a002a00000d9801a040500c075240041e40e00c141680506020490400100c03010342250b03040e80d0f80301c02002c1940e141540c0c108a00400c0380244540c20000b4012250064190f200c104100051038200030752042c5184150340000318000d14480c00da9006501c842d40f007021042c5186c0341c030743c5920607802101d900ea0b101c0100b2451034802010041c0214031072424080030100000301449000c0d0407070440c40c4c401e80b042d282d5117807803450a400e0301c2207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 346772589 1250 346771339 346771343
    0x90f031e0d0201050105010801031502070c0b1e090d0209130506070305040b07030903020a021309080f03090106210b04140d0807031b020c0607060b0d0308071b0f0209101d04 76
    0x4244540c030001c280c01841031078140c60060b56200c0f1740e40c0c21520307001c0c55950741038031a0060a500b00550404120341c09100c5011b807111404895541d10710005448800e00791414140040781d0401080d035046d03032802840088242e041c1c0300c5907041c0e5190002c1807400094448094803d02403d130800c090380b0f0749a40254401da124103030600c1d0589400f80700314100c400380039000703016030310600600000d864078106a01c082c046003000803411880c0d40d03480720380c250820481204005404402e0110b5a642030142c8070142c003140620b000b102584122200514410400141082c00150003090034001c00c05550f00310701c034000040716100f41090728000d0010354100d40c0750000a02d00040141698080400c0c2e031400a5680e0007000d8205060b0b08102060348020b20403138000b990360b120505180c848140c81c94400b8040e854900140c60b2024000c0c0c04800030743e4200c02501803604103800090901d04c50070401c42c0d0141d840f031215558850114980500d1030304413510254807180041300b19428040c101c0c1c80b0768 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 346773839 1250 346772589 346772593
    0x3060c070b0703050c0706270c0801050a0b09011a0d050f070305091603060506040e0703030903290a0b040e01180c0b180d030504150e12070308040506090f031e 70
    0x103910010100c0482c1c0d070503117000d40c142d0000c1280d003011603201e801c103d02014201032980016003100740080410210004102c0ea40c2e0400401000908401e01c1410390240e00520140601c8110f600000e1808805014058844900c6110304903030320050001c0d9004814803c10402c00c40c10314400c0754003409800c41c0c401c400079041400040c80340f0004502da54420031a51891b240e880d003140d1321040035140c020001b0786c01990350062505104005c2000708000c0d402a15240c103000c1c1507013010341e041c80a00b641d03100c2840f01a0050010b00c10000c00b1240d101c80030000004031034032140005405403461b403812081540c05c181c100010a48024402a04e1900c5100b003030700b031140c0e00c1d40c2c0d00107a409440040003e07400c4e1540c1d0900c050400c1385602c81e4091083c1f510300d141c29200c6417615402d2035494040341c0040e6051010040c1c60621a02000c0c8000c400e03002844020720390354921034540302d5802000d00400020078101e0090b1a001c1620014840c01020303242c0607100c0b6a0b025160044114101c600c034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 346775089 1250 346773839 346773841
    0xe0a1103010f0b0609130b06030403030c1b120507110904050d0f111507111515041a04020f071406090105070c110f011e09082e050c0903060c070b 64
    0x1102c051240c0710303410314003810190810182c1010488070300c030840c0207040c009455864001c01d90380c4160040d8840c52080d06c000030320b030442c58001442041010604103100c0d21682110004c2203140654601c80300c11480d1095841080f40303054503183c0c0c5000b1040307800c04820005e000411401054444440450750b0340c501500b4400c030803c42c0c1c50348040c071043e50b840d0040c00c280614840620078031607220105040c9584c505601202c803034680303021075813164020344201e000d02901d4610301d0319803100501c00701c4041c000c0124945040d134085c60401015803140703a0000b100841580064169030465801c003401070004945581020f4461401315180b200551a00d0009943d0354058144905102d40066007150490506000d210351440c2420600781804280d915605040720700f0003660210801940d144a0700c00d1070002c41e80d140c981464942c92007000c01c80f40c580c030041c02c10959000d182c40c84900101d038a0f150713001c1e554094031070860307000d415001c4d89c0f08006001c14600002c14840344502c95001107 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 346776339 1250 346775089 346775111
    0x1e0b030d0905040902030f12090415080607030e010b1507050c041b0305060102010906020a0e010f03110a0302181018091514030f01051801060e0c1b010e0a110301 71
    0xd40c11084001404600344203424400c5042c03503400f010005201504550180d5201284645440380007801044035010006501e90b05040c01e0055034494480c0c60210b408807401d10b080c3c80d44808004100b00c04159071034000030081d000940102040c500e000e0042d9108110262080c6c999a0117260141c401740f045080155140c00d09115490301c4400c0000c0480c541118600114040c0c54003900c218110340d00d44110a020071010310041c18040a2034942c0b22494682000141caa10030a40c2c800302031521f0003640c040ba10300c0d05011035007050711031b182c0181d466450200aa42402c0040708240d00000b401d68440032060700260451890303021000d81d814000d03503682e21034041d40c1c0c0e4645140305000101c101000a481120040400108020140d6a00d1a00003481c4ca0031501d0072620307140050036100104070769500c00c3c890380000d000050100b041c14078084101408612551300406a0182825102503048a0030341c030240c40d182900058170f11080c424101850740340903c89a241c829482d100036414 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 346777589 1250 346776339 346776343
    0x3031403040c0612021215010206090d09120314030106022a181317031501091401050306030f0f01020a09060c030c11030a06050c131203050f070804091e0b03 69
    0x2109903440120301e00c0803410703c0c40480c0c1240200e01d400c0a2190280401d4485c44a00380043d803240301904000042040294002441c2c0354028265040c0c40d0000e80381018040e41c03200304002503071044146242c480c01c242c501284c441d01303000c4018060003000300021800603400300b50000240580c40c00c0440f140205c2c824668614001000158002002c034111074110300350916031a405503180d41c84140003e00c58070740c0383c4c0c100703220220460136010000c10002d20350410102948904030078600080c01505002c41c0002608015903410305102c804400958580c1d0100000500850360900740c0f5a85202506058042e4001643c1034002c541d510201080d10303031146142601c000e8141d50380d1000304941c1c1e2140306035103001034800780e010302481c031a44000c900300c0c0c054207000d81e400c0c03581c45598072901d4035840030303454a9801103924a17030311400c4580800d6028055421002842c0080c540da0b2125280c00c0000344100d83c8188103060034010821152010700e500c490124141d10b4050101d0482031007019 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 346778839 1250 346777589 346777591
    0xe03040803030f070905030f0607030f0e060105040207020418050a031b0812330a0909020639101103060d08070204020432011b0f11120703031403 64
    0x550140e0050000400003e01941d4458028040e818080b0f11140c80311b01203810718042d00d812a465a1100050242803545032080d8200d401852204009c82c14000c0710881d144c010600c1060700c1581c0200c0d01005650390741c1d110014000c0c1c0d240384030701c5403111441c1050b1906c0700360b84d00350045082808184041eaa041d00503195141e8045485890451401e20101078030074050300300c1034501030704c5e880c5070401307441c15a262000303d04241d0201d11100480f8100516a81240c0003025901d040140000c0103071a414180c8141c1e181552072250503824a241813055000f0145646d201c2c2c01ca1401c5290000340041a52050b44c81201001e0220070b540c624052035504c0295509c903080a502c0c1621702c0401c041030b014004191000b440581340507034500505940c03c14200c210603140c595405c0c0c10322540820780046141a90a080006144443d90544c0c240d265510502600504070f041d0702e5404c102003944c8464442c07400901c1041d00c104046000d50744c848079800b04a0110300303080c800c00d4051010009403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 346780089 1250 346778839 346778849
    0xf04181a0609090709030804091508150103080a2607030e01090b0c07020301020d0c0906020f010e030703140c15061c08070305130e0406141f03060509100914010e0304 73
    0x145000c2e50700061000341c000044c112030800680385d80200005045c030f001403004110249000c0340c168410890710070801100c2c0c1c099551640001c81803198841c0f10240c150449410403200364840d100f100d07081d688610314003404400140c41d14030700b500c000f03800f0822901400059508001001c1c40e102c0c1c5a00b290f41688024200441010010b955880040c00400c841403001c0c0001d0700f4200c000f1152026140c2e00783c00107020800c0361038107000c01941001001d08a800b108020300401804855041d01c074420010040c042260614032450a10249000c4441032400b11080710070549010213202d0a9050035a0220320410301c0e40d81a240307904d1720110340034100c3d4010580c50702d0703d1321954080e20b00d94026414521095119030b80041c4940341070403c4d901c1940180c00110b800d03144900500010000240404015a50011030141c18100400c140066039407045001485480304a203862a06110b848030162607402d142ca044100541d48080c49485891000240b0090f4140300c01d0356240e005034091 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 346781339 1250 346780089 346780099
    0x40605070606050621060d020405100503150408090607020a0e0901090201030608071a031023041b0c030c0309050a270b011205102402060903030106230f04181a 70
    0x1109017024686600190401740081c41401e213181035a022030b080c3c6100b03c034881400d0303801041c1048581000c2c000c1299600c5c10400e0b8820624240d600d03c04035010380e0302094043c80007c50504115200c0130b00c2d4201801c000b641200442c0362149071140608841902280002e0a0600002d90540f00082002c00e90b0b01d41e400040d02c4d40000d00d07940040d070700000c1034516403a0340070100145070b00d114209298425440c1d880381c83c02c01c00c12003d100503501c81505010b000e0255240d0815819030015040300020303410324191107220403a040c110b501e400d040c0c004503404503400000050025070003d01d804540030b91001c1a000e0222500352008a6640c0c0c000140460182402d01c15a0099688025030054107110505119920350801c0c00e014001ca4246110f60480251645c0c0300ca83c0400c011a030041020004515640c10076100424444410f5900440c101140b90b00b0704094644c1425990030fa1080c80c286a240c0e07680700303081e00724600d1650707500701c0040c035200c0c0310040c103c1c403445000b4480602500c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 346782589 1250 346781339 346781377
    0x9021c061805060a120b1b0315090a0e01110903070e060d1506081203060315060f0103020c03041a071202060112170c0a051b0609330406050706060506 66
    0x2440c2019050081110303510202888001c15071017000a44812094007843d504522843c101803180c50340301c50820031281c0c44509004204185100901c20b005582d400da800460710388880d100c00c00a800b016103511410350030400900c0c003d804c820040c12400d03004800310743c0c10503500d108441c481c00c0c040c3d50b10764014007942c140708045548200380301403c104410000507640c0e954a8010f00f004007800c050f0041200c00000c2c0b00c01f03890100f04c00ca42a02d44080e0900a50501d40001500908107042103814103402240f4401c5598003070050b41d000b0b0404c981207000c2c0100f0529151401e0340025001c0380c000d00d8402c1c0264200d4400100a8141e5040010f1400003003910b0b01c5040c0350030391081e000035034044104080c40c900c100a10001c04014482d100138040403642c41200c0200d4010403209078040c50041c4000406942c441c446640c0f0a9490b0314080c01c0c0500d00b403c41c08010710050040301040100150014201e68000300820050b401800d08014641d00da03000c1103528450161780c0488004124 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 346783839 1250 346782589 346782629
    0x52529041208250203370f27150203030f241008010833090a02060c060901110405060a0305070201060906090e0c0f060301270609021c06 60
    0x8900c02e4010000045a42100b20103040070210f440031a02c0c080010b820120781c03081a0070b0711904002e90100d030108008880c0c0c400c130161544102c0c1c80400c100c100290740c1e0307042c09064081c0e000c141c0c14001080300506e43e18a4540c4d5491090b056101d940010603041d00f00501e880d1006c0241e030b000d044181c0c4070718969120f41c200400142e85045c55a0000c100424811006903102c842540300010140c4a019403589415400b87c00c0c400c00c0e41041c0c0c94840024801c1c0800038818800201405000010329803a4881102d514500210080d000390020800501c3c06200c5a00090316407044400070001c1c0719400303520381c3c9240c1030700030307403140036084002400785400550007a081154031084900c00020400c0d501c1040c001554555400700c0f00c03450f514000c15114240521501d8900c1d0030648000c201c0d20505c2d400310303019100505c81d20281e00b07a80c20402200c1d0b480e241d01c0b0304107205014000d02125403244038240c000e43c854010303505220101010b84407176079010700980c4100c0b0801c00880f00401428 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 346785089 1250 346783839 346783847
    0x308010b090301110c0a0c09021804050a0603020319050601081c03020a03111317030f0313050a05101407180918050a030306031a1003030525290412 65
    0x428040b5855500c411011503440322040107440703103400282c000d184450b6103003485620500700d608100b00850040240045001c408550b41c0c000c00000c1e500001c1d01d91b00c0041010041256820095043c0211141c1000c1e441d0700c050050740040c041d60584555998aa004564480c0199a6010001c0c0740e0303030320038080c00e00075409089034148174140420100b0740c1c2141444541c0c031003000c00e02900b109001c244065004259007082640301c0313400851921400e529042c1d00f0b40001014507950561505a54003007242c140050200c2c0c6a00401325514009140e410002400b041441d442d00011003800054031140710b0b0072407004444400030f40c2d443c220b080c4004000a010b0b00700c048400082d01c0e00c2705000045041004d41c0e84075000b50340000390305055140c0f207045401503240b801204203803003050020784582c9005180480342d040c14002d950300c04036543c4880c51f40d800407600e0005042e00c400d0b4400e2000c4041912b039004420200444a0a000381615000d8a410b403409401070b0901070b042c1e9802c50203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 346786339 1250 346785089 346785097
    0x50105010c1401090606080304180204081c0c05010f200702010c0b0a06050310090303050f04081801210506031c020606121204031a011a070b0604060816030210020303040308010b 78
    0x802c0b00085442c1846031162020765000750303c02102d50f030000800300508105a02009030100041c9070551800b07190040c0700b603907030061018541001c80c8082c4145c5066000301c000d0608507034400000c5c05002407103158003004182100380d8042102004103010101c02c001d0044942e030560584406a00070301580b1800c2005100801180c611550303840c0102e040e5604000074144410340a90100d105442d40c9401011b0b542c0c09401300c04181c0c1800f040c800003034404015504040c14550510201c003500f0001200c0d42c0d0f100c3d564071400b00303101c2000c45c0c24440c003a8200501c00c01e4103800302d40914422480c00d651904040d154080180c201d0004100b282c5410401852640171a4044034001904032042e01d402e540035910403111078640c026105a00001400d2107030060984c850301029001684022004600c9001c4004141d0418500001c415989276400301e00907011140c100c4010307038220303d214a08560740f80400d91144100c5240700c01002e04c0003003202d10456060381c45a0541c0d1824106d800f0360b1304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 346787589 1250 346786339 346786373
    0x270501020f070602090a06020607020d0c032312060f13110f1204050c0a031a0603070f35070b0f0d050a091101090e07050a170406050415050105010c 65
    0x140812114401c540000e0180a089010729401039640c80c041c0f04110b04c05c9103c1e445001950000401c01c0816030300400c404842d42801e04001400c0c80c554502203418241144010600841c0c2d101d60056440a80000e040e50650004071880c40341c440c881085070944040c2a86940300f100120240004040c1c0d400041e00615507003034103801c0c10075200b207250a582182d019105109804020001808000c03c0160a01d680554000d40391070b0850f00c0341590020020801c9030804021004954207440412080d8010545000c00600c1e0030748400590740c02803918040303090000109120400302c521035403440840c2c0492100148502c0c9d00c2c1c00800c00e500c2d00201541300302100d09201c1a400e41713406004080c4500f1700640001a2034005103011003e000940c000c141c10400500401e0080c0c80a15017600d8000a076070034100e44030200814101d40c600d40700c0a01030504800300c0d0a1100304142034110900440c4900c001351041e414070508030007290000d114103030000d00c0190b801d0f00422220746068003d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 346788839 1250 346787589 346787591
    0x904080c1605100507020f040501030602030415020f07080702031c090609050102030c070311060f2209050f0103030806032a2404030b040c0e130501050a090203070b090303040317091003270501 84
    0x810317031f08009000c4032001d910540d0501d800004000421200205500c200b1403005401c5042a41e024801005801800002013030740c0000a101da06554040062401005004546000e1004a004000d08000d07240c4686004132b500104045070643c00442a1030740000040c4c0206201442c0d500d801040e03910308400c00d0742010003000444216109800200011a0038440c482400d45840d0a40c081584082e0300c061030701c51a2a0902420003010711015046a404d032400085030344508001a0800f01501c0d244a0240c40d923485001c0c000d1711a540c00d070014502100c0d0301c50ba1340c1e94603c0d40c154030002d900c0120007070a01000b041c4000389030024111703081405030702050005900e0b80c0000421160a80f000d07814444440e80c0c04c401c12a0902a25071f20866801052203015500da010aa03210150701880c410b4040204940c1041c0d1420001c0d03070015508281c10107000130085800722182d900c108056409181025115080f95010780a0703425817003d100700c03000d00d01d0999004165252159842160320f5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 346790089 1250 346788839 346788859
    0x303070b100f08070f090504030e0d03020c061204050106120803010303181203020c210a0201050c010f02300f06061803060702030a03180210120b0904080c160510050702 74
    0x1070705500381d4041c01010f401024190704291403114941c0650703120446680c108003c00000036070000c015030440d20140c0d121101f000c0d0030701c2c1c16800c104041c0180da4004101081040780041004d60b030301d0180e40554002c0210320340724200c00410110000b00135010000400041002170f2148441d022159010045251850780b03611401d003290400701c00c1580103034800c101c014124503007205000041580c11030b4a02ea20115400d0b0742d5203500080402a05112000c904002141400e4000281810400d9030455036241711080701c03e0780043c501d01c6041c461010101c42440042000301c0c1d02c0c0965001c111480403a6504000c0007100c1d800401ea84641107614078001c5580d45041106d0340c011805034000e903071104402c14000f0100c5d05070f18164245691039000c80005600c41c040e617024100c00714500030011881210410000e091040d2140c0d4004500500304028040201c000d42a850b034454280c40950220784007070020031249015130b50b03004000304034400c80300c0e004000400c130310391003d000c030302032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 346791339 1250 346790089 346790099
    0xf1c02240301030305190e01020d050f0f0d0e060c180d08070b10061d090a0504021c0f11010305100b09010207080f0102030a110a020607050d06170a02120c0303070b10 73
    0xe941003a4411804290003140081e5100c89800078550043e00c00d1900289070104c50b00001d50310100d00e0594020300100090720700e507178004101151201c400c3d8003e0f0b46d0340c841c4558101d0000b8195224101c1d40e0340108000700e01014811011124001c80d0415003803054120701040041c0d840c882e042c2103400e02c5080021b01c000a42446041344030b1302c016001c0d8480e10b403401d40c02901201c3c0218000c030840070076441c00d048598401131440c1d00540614000030f440c1e0384500c0032601c00c600325000c20030030360b0f2102c690f0340801c0004842b04450ba442a007401040004000041d41690b00c00d480e0800c40c0304002300c0a10900030050050103843d24144101c03084250365902d4075080254400c0c0440b4544d4000041041c56044c41c02180c000b441c09014440c03800c00707051030080d110300b000b81c000c030100040001d8001910982d900315801500c2414686498080781400d01c9942c0c0c41081030881c000d16072501c3c55480c810012071050f10820b00680a58600301459582481500c0020041220000d0017a40420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 346792589 1250 346791339 346791409
    0x6070305030a05310c0f06050f0f0702190513020405090601030b01030f0e070f060503010e07030507051b01050402180603250f080304061206060c060209040b0616020f1c02 75
    0x7641c0046419070004044c114103107603c0c216038541102c51200030314903040007200e83c800f040b00d121032021b106880d00c44040251034503091182080180d4004500b121540c0b2042d00d00c200c0700c04480007202c03050740128803c030704041a40214420103070f0044250001501d154000c1c0c201250010b014903001419860026103c011071749030841510340b07948411000d0003000d070641e41d4100030f402c940c20414159894030b8a02c0e007800e503000f40300108054540c000f0920045c003405c182c0d030414084a68441070700b8190261140204070403241a8811000503131911075031020504064001c85e406405408054900e815058903030603002c800c1040794003403030000189800540f401c00f000d4041c0201440d40d49141c0300700144681040d008048030945454400c114aa400907543c00307045038080d07400760710380c0c0224001500a008114070745800c40c0000500d0000501500c6030302e900184221481100c40810f0002d0008010103142409892099901d8203000752910800c405200c1c0a5603a000c909040c200c10614 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 346793839 1250 346792589 346792651
    0x30f02100605332205040e071a070501060e060f040e06060d15020c0c09150f130e0d020601090c030221180f10061409010b131208130506070305030a05 66
    0x10840803080c010004c1400c81c808880c0e4020710044405214040010b400103407030701c0080c03058a01d68203541840784070b0f07030714010107540c0b81d0381c0c00a000f00f003180e03926002c20606c0b0004448844c400c82ca1080c049a4a281034032490001007201e0004120130754620050080c9030051a000ba5150030b208504048007021b540010036112402d44003402000c10060180240c40e0006030050100d818000041d001036141d5440751042080100c91100f80c0c02c60070986800180801d00800d006801540461883d840d00060b095040300c040c60b00400185000d900200c00300e0040304000360440d10710320011844013190a0129070401141609510100f030420040351804c00311032044591504040080380042126100c0c04005080e213040c10303107000c03d850f0006100c1140500407150b48582c00315903110030810900030a0040d00d40b400804c40c1d603044906040300c035904100710461000c40e401c04c0101e1641000400d803002c165150b16400c2c10340d11680d16043c0502401041e8005171207202410800c0101241d085c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 346795089 1250 346793839 346793857
    0x10603150912210c03180c0303080c04060512060a1d04030e060c060f2203090302030120030411030a120c05010e060903270d030f0210060533 62
    0x299103075107141480300c030a0307200c014070280400b10320001140726044441807010030341540d00081d9540e0740c2d20305800a0400794409900d40c8007910801082012200300101628043e403a692150b954071003201c60503110301c2c003c050000d4000e01c400d0068860800c01d1a4000900514200040d602c0303480103580710f2100301020702900c006400340002c0c550400903152402005a444629100900141c0d41e540c081c00340442082008000c0003c000200561008402000c10f039030b992503580c1d40381401050603029000c1079210354070744030b1341a0901700302c3c01ca90b441031248120710b1401c0d40d50700e0722883c8100d0360300f41c90036400d40108100300700001c002c1140710340a8080b5898281442c80b480c2026400c560040061036950341c0044180510010700100744c803100c08100034060000140e102d400e10b046890881e201d60481c0c48100001d01300741d0003c03207501c81c850b00d550032141e001c00d0584110040c0d030120b00c80d95402c800071800300b21030107404006100340020179070518161001c2011440c507240d404030400c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 346796339 1250 346795089 346795091
    0xf020306040302100f0c0504060c0323040620150414030f0d0c02010b06030c070f020901080d020610030b06100302190324030b1f120507051008090a060e01060315 71
    0x2e510000c044622514803c11740a03d01000320941441d00600940301d28050390050000c030502d5001018803e40c40c2c1443c0310340e60081d00d15613003000003044075246c000e405110082611001400500d00c035111000024281041c004c040703043c0315084079504188040e006580b44209040c0d640f00c08401000140f031142005450a43c0d190300b800750020440c0c0384c403d441070841e41402c1079580540d480c441501c0c0c00100c241341c41640c85007640b60481c14001c00d044000d40195820000207940d84003c07941c46540c58198096a030f86565207203e0401202071808001d064080d1540480c2c1942401080c081418102d800c0c01032810349040c1403c800849502d034000000f9403203500c1a216000750003485280719440b2404204c240f402c641e01c50790341c50760050920343c100c81c0a0810f10880c0306041c0b010401041118914549407041d41445500c807461401013a004000c1400c0d814291446020b90f603215031041d00c00340880b0321442d61010081c0c00c4450170340000d59211407000c00807600c3c182d02401d4120b0082c01c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 346797589 1250 346796339 346796353
    0x6020c121228020d080c03040c090e0709150e16050a05030601090e040f05070603060b03010510051e0c060c040302091302220e0f0303070f0807210203070905060f070f0f020306040302 80
    0x340217041c00002060711011070300a02c10b0000143c010041c19080c1c0b4503204001c203e5085102480c1d183c4145540030969243c10001c00c5003200b039510004100b07582c101d10001c0c1d219594404000a10111135001200090080000b100c4e9984181c000d507822080500d040144a91b48500d0360010100555098801e90045071580007005410441c1c14014010350600340300480c5040c0302460207000501c1050b0244e012034426905451240d002c0b42c1d5030040d802d840c1001d00c101d2030103640b5543c10900071340c28944141e1001c03d0b50480c0080c240c60031258010046c20031684c44e0580d02a02c1c00d45414101e8102c0c0c81280740c8040c40510169080c1711271071000000402e0302c4201c0b1142c0c80d00a8807444071940750001c0060208a0740d0000c5904000c00d030034209040551500b2504032400c164244601c0c0701410480740da1040040c2d290025402907440e40d4a001011392a1402c110300c921a05590f50000030301000a1400141c120511420050240c0412407a01d14140c001c642049012101240107801500c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 346798839 1250 346797589 346797613
    0xc0304030f02040b0a0b0c0c031c0e03122803020f07080d09021f02010f0506030316050f0304060c0318060806040b03030904092a030b0411030c0409080406020c12122802 74
    0x7000901c608409c80003405a00900a5410b1a8015a6089004100040c00f80050030749007088604401e40703040364010359a103005102c860708125000745080741d06000340e017007010140c4680240c42001c00600f03101460844036545e640302680c0072038280407220791030b10b0b05000507070f560100d00d00038030240c002071750703080851014003e08480700d490001409a10301020300002d82c030001b0544102c02c4100801d50403040050414618200c03108280c5082d6110014010480c1030703002c4c02c26894244252a19100d036442d002e441c00903175420340140b10000d104440002c809103415008400702020203000e0324038000302c2e080440c0903518135030410389200340f80d0215029844071034441c101d040c0d01202810801c032401d683d101001802c0103080544803482001000c0e04560f004c1c041c801049400070010803024030540340080061300148034030005401111882c0025040410b51302e5041d40c0708002500c0140070584000410ba000494038444200c408404103064180750460080c0c081da10741c000b055144c540d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 346800089 1250 346798839 346798843
    0x3090406050405010f030f0305160c050406090509120f09151b07031203020d0b06120f180a0f06060308031e060f010c02092211030c04020c0304030f02040b0a0b0c 71
    0x20790000e8040d600d8600100701d2a800c0005c4001501e034003a00788000104607050483e01070181450309880c06800e64075042c10031811030522006c40d4003d131020310440c0c0d6108620422074504a440072417039001003404400c440e41c084011f24510003a02140c40c14480d420010440591900d0801d090741ea0000a00c0d0382c103070401c03c00c04602001c01314014000d40781555208403c0d0542a90003500707064000c50655242c0c1c2d841c5d0030403030600c803001d4010f45d2a041e40700e503090342d001e00a079840058400c91502151fa5410303051b1510000003211070041050050a998410840c4110442961165911040480000c00c6d4800440c080c0e507195070242d000a2501d031003144009000f6009501c20481c2000415460360090b50040009404640c203a00942d9443d550190380c0c000d86480c0c454410606907040704104182d0803950440c07509a0032501e2038146441400100c1c03103015402a50780d4010302c010400100842c01421910f0300c003400c040340e00418000418800c554a410184030348001192206c0000c1003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 346801339 1250 346800089 346800101
    0x5281d0603250303080408040905040b1618050613050a03140f16050f1201180308091915020c011a030c041b0e1c050c090709060f0807030914030904 65
    0x90002038042c4041007039280b03828880c1610000703091020402c0020148900030056500801c5455428002860149410640e0090072104c6913031000c20480e41c2c00f47d142c03240d0103100c104e07014007154140840c1824200103c1e0b4014003900b480714980321202240c40d480b503905030b50041d4803c00340072440e030a01003680303400d045180c051550560f02040060b02482d16411b0008200e42050781c021620b268904086421031018040400066003001c007103c6101d0301200119205600a5880030a40e8903080229610303035504520100e04000400d6154000c1085101030101444500c5001840c2440c1007409600f92403021214002010b09070400412505050181781c031000c00c203c4042020805100c03480f1418071420440604200e41e00300201c40c84d40700c95004440055031040c0c0070b420003000b440c09956034848010310384e00504014010485d1103008071030840a99001e0744406803d441742c0441241d066000400b5801010380740c030a40004a034148031140d04821009010710f41c0e80100d20248070650b60 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 346802589 1250 346801339 346801363
    0x5041502030c1207060f05040804050f1c0602090d0c080d0809011811060424020c010203070c060c022701050109050d0533070302030108061005281d0603 67
    0x400c0140140d90303940440c0045000c0034400301c0c50740320304c02800c0c4000109030780c0035182001e51500c800c0c8020b00c9039440280040301c0d01128a00c030601410018440c400d60743c41075801d5a0f515031081900001c0550b009055204006002142c201c0900d45a2101c0415107a0040406030807009035000c4040c1e01401791540100b03507000034405c50b03c11003103101547d0f500350009880c2030301c409127010f81c65a0b4007048600810004d411000003c81c0c41041d06510314051508401510440e1380310300055001106888116800010210403540f5001c01907402154840040341d100c0c005070380107070210240c1c1101c3c41d00c1180c02e110681c5a9030401c0009080e844503500300a01c195050958900040c0d4002010012b0314424142e035502c80c082c0c078680100300c600031003a9491010b1010b080000b940e52544c00b65049030955011908181c0702d262034218855624003519400c0b200d81503040c0303000b03804109030201d54040b00d40c022540c541e80c1c42040c040411415200c000c09500c401c00e00149140030002e0100c0d100e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 346803839 1250 346802589 346802593
    0x28090e010e040f140f030c01060510140d0f020a050304050705062a01020405030d02370b130c33050306150904060906090509071401030e0c030d05041502 67
    0x350600403418003100300103200900030650184003a0400c00d0b0b000c03414040c24040d1048a0b40400e240301415101d03000f03540070361040e40c07a1040008072440c0800d50f40070070440c540c581030152820f0b8001c41450740d1100703da4004a58880303291030a030f00054401004030b540c450f650f66440381400e140403400c00201d5031110380309903000d00c400242041400030544990044c0d41d00d02c038541d41c1a400113030181c05144d120036418007a4400c0c110040741c0115145103100301c0368099007a01c4200c450744020000b0485110b0401d00c8481c4640000070f504020402e402c0401c00a907030140001d6070351810075030701c4aa00289040b0000d00c004aa58900c2480090140c0c00c003001005410001c203070b002001800020721591040c40c400c201c040307003a0760030070445504200161040c0f11064645074844003603c898407030612070310315000010361040408138449050321410b0302200982c0990f0f600440107403030044e9108441c1c0c010007460205170380c2c040000c80704d564900c1d2907841d10b89284c00048072200c4086401c1038195 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 346805089 1250 346803839 346803841
    0x41404051e0a0c14040b0417011104050f0f090a020a0318020d03230301150906030213030303150e01080c190e011503020c030d0501030c140306010504050c28090e 71
    0x50300c440c51100e50b0050244000082d41c070304080b003c8492540ca0fa041c207451080000d03003c1104111040103200340d81d00c11110a1581d00c96501843c01c0700d0360400c504286c200148010301031454101020714007900001e014401130b40c8502c00080034540306640701a052a40042d81d140c0a035014045d28680e840100d00f40102040a0313000704d000b80701c1200c0d006040143c891034149401c2415004000c42d0300e6400b0b203058483d0b0b1916905426403003140207480c045070031050f0001d102c51090003103904002c1500e0104d840d40d440c48d03030150701030100e40f40752044031980c86202050398000005801d0007440c0400007040000503030810322508900c5490b050b01c2d00320998005000c04444240414110340321440944140d02060380c0c114021700860000100d01e02002540d000310990700e800690603a4000e09601160381d9403400c0512642181031626a05500404c0c010015454280c2c4020b81c081c0155540e0340c60108401c00b40c11038042c82c44c5081c02c0c80d24546c520350426130b40c41150a0003030424944401a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 346806339 1250 346805089 346805131
    0x2070806070306050a05091b031305060105420c011b03050609130f120806090702030c0d0804050304030b010609060905030109020f041a03010c020d020f0312010501050708090604140405 81
    0xf2280300d004e524047ca0002c4042240303024040880b504841c05400160b407603080c1490343e01c004000142c0180e810b03225450002c115032821482c010420004110ba507100110712421721002d642d0041c03001c1940170350710020029035240d4400182118143c100000079900f41e092448098034101420620415203400c04105264840701c0d0925041001c641805c0295140c3c0c0c98a108110042c1070010b01c41410030701103041c003030b400003005030040e04d0440340d00c5610760301e041c8100c0c1c2d02c0c001c101c21860700341d024055020000e17015900e629007241c01441500d160503203a413564070f014003017a8422400100003070720170042c07140d0213280344c0d01800702100203022030031762500001d84041442200d10700c603607900c0c0c41c4a14070300060080c401e16040050002e0040204c080c1c0041d48400680c505074000d40900b401440a15402004481e0503070248404100300d40d08040045465400103801222007620812990001d99500e0018100404940d14110288015281404191100034100d8820880e5141a07400c03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 346807589 1250 346806339 346806349
    0x1401030f02010c05070504020d05061329012319020c011e0e0405010603060510020604051c051e04031101020a0302060a0209061b06070306080715031a030303070207080607030605 78
    0x30041d40901e0075044000040c1041400e0294641c46194018800905a054600580c000502c1100b040714404034141d001c2e0a4030080d104403441480c02280c203504010006002e0912a0044003010316000c035549092200034003000c040154402c200ac1c0340030550514246000c44031500303200091004c1e101c0035081000213400d600041c00c15a90b80c05201c0f502c51501442003800400520b402003080c00156500c0001500030101401400d024900001c0d2803064107000080260090743d102000703101d03078030766511402d6210181c40c640d001044001c000c051008002c03008040d220841038031201d130780c40e4610710301802c242801844840c1590400c04185006c82e40200e412540031403024405666044400c0c0029007500c204902000e04495048440d1250540091010310401c41a1000c1180907150510103a03200d030340e48501c03002c0742d08544e910700a00b44a9000302d00d8140185d64920554620b000000381183c108035a5080168000a01000441c03410410306801131590700b03041100700d041c41c011076 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 346808839 1250 346807589 346807613
    0x1204081002162301050105040908070f0201051614060a1e0518010e01021b120403110609090403210e0307080f0c24010e1302010e04090222140103 64
    0x4100d81e40400d0300c4115010500e1030040566009003066081400451000804101140e5000c81c640c6000008036590416200b01c20b6078507041141581414120790342d0b04e0035151a4101281045014400b001052550441e0121a94807520071903428801b0582c040349082c0004010b010242d0411248000c0c0e0700402d14202591030380d620021642d035994151070025030030600c0400702250700e491950300e5440d0044d8042c22003440e07241008a1542c03c0148030070703621016070301904980700d0108001c0000a500e5202c69880c000050501400c0140400005494100407942a8041090013114020403c101034001084807072601080112500310301040c0e80e01c0c00b80300401001c610000039020216100e4805441c8070a203280101d0300c0300809800001d0000105501040200f107903a000410030184440000303204010191000746020541c0e001155000031040100e03800c5a030b925a50700150302d80c0000d0041e00342400c41114030f10441c0c40409030840d4040341458501c0503101006000041c01c008002c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 346810089 1250 346808839 346808863
    0xe09010510050d030908030409020a02010609060806130f02040c0f0305130b220b0112030908070e1b09030604051e060c09220f1e0c0e1e030102070c0503120408 70
    0x200d0081c000078036081e03e0008561b00115241d101c0031078000750140a40e0014441c00000380d000b400744581c1c411540060300c2140c05121032540290000502c101100c0080044e0280190200c40c90040c40d81c010501700c54101e0150380006051009250765036802d409114ac11180100410300c0c1d00b038060311072914440c1d000c1d1107203c1010f429040c400340c804400a80d02070541d00004031011a50751195054200d1300c086d1000c4012440b5000000307001030f07000c6000720454180d008880115601c500d01c009440c4017108803980501d409101d07281040c0c408100d02d52103180b00d5001400c4044241a040502844c402480d484e254051020485445842c0043d0b03007031800190707048140420400a0444a518000c51200d00f640c50000084020015034001072040f0141441c4170a80c0d03d0507090160503100141000000300d2100e0840c040c4078140581140038401a10322040750b24041000081d00303a1b8130813401561040e00c2c081d008c1c00305240500a488080c800941080c1c0f13411b29010311a0b840c0c5e584c0c5034030303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 346811339 1250 346810089 346810099
    0x14190b03070c02031902030d09030309050105090d050a0501050a05130206070b09011d0a0b070512060d06021303080409060603020903150403090509070807090b09010c02040902030a0b0408040e0901051005 89
    0x110307003694010780c81c0000b01c0d6401020b03500b071070410703520700d0f6200418094241e109104022a00140e5070040007803d0549406950f29020507043c40d006541c990b0000c0415034000340c900e2581000f092041c040d01c6400d500c00e130000301c1e0b1340c189580c000c8140d841c046c00f41d402056100520b0401642e03060202ca000c2580084540c4480c1e031515812401096011031a0350300518450180b98961800f06040c2c8466114105544090325040d4040342d103800b40c40001c003107038681c40d00460392502e800c6035076010581c4600d00261800040e001369034000c4400383d100301d56415000c00d0a01030b0240c54060b00c00034040310718003182020b14010000c2c1e036400c085525024920007034008141070522820003800903000c06041d244103801c1c00e43c030003481c5200407200c0d40001000300c20041040030081085601e4464160f6418210b9251502000300034641180c0483e803503c40d812400300040d00d980c10b09441180619140c07a100ea240110809044000802c6900c0c1d9074902410400e1281c030110141d400d4642c03e6503 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 346812589 1250 346811339 346811341
    0x210b15101e03051803070503041a0901090b0309010e011104051804020607020904050a021807120507051e04080a050c0315060a09090204020702180108010605030a0b0412091e14190b03 80
    0x8a580f00c42501300004002400006810011300070000020300803516140381c07a196120b168004540c00340208440180001d40c040000c10a07a28100061604480450000070380b501c07221031002d084070004881102c200d040807070b0803c1a482d000200003d0100c0441c600206480c1c903600151052183c058003d20802d02200881c0a00400300101e45400364060040080780d0020120000b40344800c65180300018196200070b0f80c0c417840750103614005d000f9074881900340300114011900d69131600c0b0505c42c90400904c0000f503414020880e400c1c510740600054814100d2090915050100c1d42103d075128800c20400d10a490325500080812140c0307070080041c181c14180300003006031140410107540030121000d03406410126135500740c1207601c03003402044096503074001c1c580c41c0d03031007120080c0c0400074000c0001c0c040360138020010303603448191600c601074030340755502040292080040740b030340e200030901c00344840b2810403c0c44000c0039044526000c000c00d00101411078407440d01540d0703516070002c4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 346813839 1250 346812589 346812601
    0x8060f0c030709030602030a06030c0b12010b0a05070501060b0304060501081b010c0303021918080c0607020402030406180807031218110118090f0b01030c09210b15101e0305 76
    0x5030407000519881042951f50382004030100028281c240001d5034104682c00f00041c809804004440c9031000251440005a180841403601500481c02c0241400800c02c0101c0028100b1710032100501884499a922810079040c0001282c10580041160b684401900f5213a00a03050528100355424603048048440728030f07045029014003404234141e10215020403c40e280c12100080641c1c0c80b502100d200b05a48100b50fa968008000b000c0b50860402c011500c0035060540040d42d00c07902800000c00e02100c282c00c8110904801002650201808100d2408141d8003040700c01001a0a1105028440b100001080e01a5a030f24000384040b5075080660003590241092034011514941c0a0701240d076185003003c0a49040007400d100246450100c00687d1701910031490032100079a10343c40b6035410b06000740c00500554419500c00d54139800a900054206a4801c2c8218052045149600041c01c02d00c0f1004085100d10390a0010b06013800b001c2055141402052074814074000c03596884d49 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 346815089 1250 346813839 346813847
    0x6010201110a110c0a140f04091a040b010e0105010e0409110603070504050102120406051207030e010c0e09060d0510110f120105180603031903150608070908060f0c0307 74
    0x40d52809052410201c0c1100c0c0d001e401c1180f8803503007060300042d0b074590512035040106100300790003640c00580f0318480f9070085040158846400c64000703080001c07031a1942d180c1c64460b40c4036000d0786580082450400040001ca1081e130303030040802000e1600c241d41803400103865000c0f40040b82c0e0080e542c810825042c0040c1c0c1d8051080100058011652801c041b440108564001d000343c602512030080d0040301404603104540854100d95140d9080540500c5400a80309011307048504154480034004d0a0b420284213505904c250f41c1c8900f15420280c3c000d02110301c03030050001d071103111101850804560041102003442c010400c00144020b42070300044510700904480003201c0201107031701b40301e0700400c000482c16990102c1e201c000201d8003000703006a411048400c907405030018042010a4203c0300d5071510f09901754200803c2103281c0704203420810140b540300b0000035100740240000030340c1112110001e01030410150440d80740c2103440d00001c02d405018076030120b10020000754100c0c41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 346816339 1250 346815089 346815101
    0xb040314131403010b041d011116060b0105130f140906090601050c0a080c070806010e240103090602120403030b0d030806100c0f2103060602060f04080d02130806181506010201 77
    0x10320030082001c02000c071850412070b030518507d03250f28091009210f40e40c81c03819100d80b0700641ca070b000c42c2441a030380c40308007a0400d0b100680c10300609101f0000310f400642208806003a000141842882c6410b540343c058039403001c2001d0007001c00b402070010a8403075060080c1d200d1000c1c00e049540c0d0761400c070003901c0c2c81d450b0b81d800780c4107003000704640c0e566100c0495690102c61030042100d94036603c03030784000704c030b03560a40d6049104190807130001840c101d4850741e86180e080c14180050f41009e13179100c090070b0340d00104062743c0a0402c01d00b0401090b03058816540309203015201a40011110351300544003200141003070303116401c0c00f50082540d5214801c0030300c695900a440e24802e02ca540380c60342000740f03d4040b1040203042c1e250303003881e450311134400c12080316410350040c6178a03280c20058284040300030304141d0390b400c010801800c8010641c0000d140c86070b1181c84050010385400e08407811f050f806800c1d080c985000c80d03610b000c107207000900c800c2007040004015081d92200d400513401444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 346817589 1250 346816339 346816361
    0x11040c020f070518180316050d12020f0418020c030f0706050f040803010303080712021306090f0506030615070b1608061005030a0906060f030b04031413140301 70
    0x41046000465154049042103158084000701d4002580303800401000040d24000100340143e5000010340e06015801c5100140c0514001d80f440c0c151410380c0f8141d950483c12083e100c41c2d20094480110350b0b0b000022005031408030808509001a5485148081c452842864404020400402c40326003041d8110f440e082a030008403640c800038115083c0194100030340554655140c036001410030381000007041c1c0300c0d5a011400c5803450382540d0b0b081e6030010380540100308100000c0c0b8002e40103060f0b440100035465503041c0b00200a8903001c80200449200e81000084088000c400c1016803640d9090340d41040d400c030749910f180c41e500c681004260148003000743c0b05000d40402d12905003c2da50491841401988c0c9100340c5590395014864000083c41900001800801c00075852606036840f007480144251001700b211507551a000b560501c164005462000b00b00080c081010b4110f07843d4400c994601e041e050a025807031074080c6d484d4410b07100e040c041c1522000d01ea6000d560039848940f4180c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 346818839 1250 346817589 346817591
    0x1112040b0d0f090308240f090711070e16090b0f1c090c0905180a02040b030a0c080709061a0405130b220f02091c060227180402100c1104 60
    0x82440c10024071445d001d0f505040300c840440f10440340d4224002514032040c1018040300b004c190010107009000d14010211801c1001d44022403101e0f840a02201c0000d000080e03003a90217083c01d090380f02c05c0c103000115040034000300c01410004446040281d44042c000600d15945901035500303103809210100c008506924a424000c4c002c00a070b4010410641c0c1190004001e00d90340e00314030b003030320034100040d00b101030340a0102a001480c00d0382080d280858003400703680b004559a071b40c940c00e40046822464154001002c01c2c0150031341071042100500315000800b6907840300002d850310074480c0340140c1d8021030504071800d041e460250030005003483c0160050840e0204040040c5c82100c244e120301105a00300014420441100d000350340c0b1181c801442e44031701f40b50a46001074560201c0c141120b10315002e000140c964110100c04140c0c02d00d440c1584c03007100051f8800c00150300c0301c020080c1c1003400400701340005030301e038400509a19202410001c0980c1000e00b010020040610100c990103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 346820089 1250 346818839 346818851
    0x3030c0c100e1f020313150906050a0507120203043804030f0b070e1002030a030501170c090901090804060804110d08092206060909050a0515011809090f02011112040b0d0f 75
    0x5482a03880008008207d6980c007000d56844920803a400c0c071407c500000000c00500858020810400340542131f983d10b401107d01c2d09a48010000240c00058004803200c148911a83c20318900071034842d13220b10350304407580c0c54641155512000160124030140900c01c1c014000f0700c05500070744602c5082480100554082007002c00f000b550b80d8070004010300024100f00c00000c9010320b030750103500800511030241502140c4030382402070203d402410310500d03640704c602900c00700b420a80200050f10b00c0c3d170ba94002c0c40c98a400c1c1010a0b6400c5a205806a40c4d081c09280114620300151400d40c48210f9011200c0c0301d00080d8028448064840108035928002001a4490f041001582240da00fa0824001541c5904820302101c8084513510082c480c28146000c0c0c56101e40282d0700c070703007840a00e5102c2081d04e440e03002085139010b80c012120403084245242c15580c11480f04816960282d005018203902d80f1651a028041c0e480f820700c002c0030108541950340c90540001e0140e5150b80020041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 346821339 1250 346820089 346820099
    0x1308060f011403010b010e0d030e060304080702010207080349020405040f110d0b06070b2409040f0b0c0408062a270604030203030c0c100e1f020313 65
    0x444080c4602d07049610a0101c4600c642410700880d400ca183c1611640720411412061048040d6119021402c209107000e1120b510742d40c02010314040c90242c0c032050b4403994188006894102942c004400b268800d00050b54040c20a40c035416510b24800302040c00340c03500d80702d690015002100c003128134642040034400b0140c0568050012200111001c1c03055014802e103150031201c1140300760004003007c100100d08003605070481070880401901141c03902295441c1c00c149250262049c000b0500030b59221081c190000313460903449001200c880900e824903940c0c6440440c0442c00040c1300701d00f0500000c000e000b66105890003005204107440c0b0383c1c0340a003210f20100d01c070160345444404a41e018140e000a51905031000011000007589800e42d034014144007110b440e203121640480104004801614140068042c81e00c1c0d100c0100307158035003081000250310f000c0918408000142c03480440503038904099a91442d031498102141c890710b204100d0a601c079645000010100c6220005a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 346822589 1250 346821339 346821361
    0x20f030f0c15040f0905060f1f180503031801120c0e031005220203070b0d140c090a0308070c08010903080a1a01090b090f0a090e0c030304030f08130806 67
    0x1501c0320200c0c0d0101d141c800d070041560306402a13000340011070054850520207124a50f000c81d400c842c004010311000c0418000086940340540d0103118040380e041d244c82d41e0150007005044150442032851403116040c0b0740070270342d04d01844507011201003540c50182c800b03901032210900810610b1005000da4580c0c18405003c14500e101140e01900c1a0306421031613075003521895015005505a07404400480042080700d0420358100380d82c18014120300140d480f0b00d8600415036035030312640c041149000c0803c08d00495000421520140c2408c0124540542c1d910b640d40003529800064a6202e0206084c454800c0305560040309982d0700c0c204401c001c2c5904a00d90500c68005281c050028030420b501100410312090480c501140610006210b200701040150a0205000d0001c041c884060000500e60a02c90341c4408152640c4161607034000d43c0500010250400c02d500441c603051450f50350071100c2000b81130151804c0d501180e2480c2c40c1207816404001058105e00316051420003490644d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 346823839 1250 346822589 346822603
    0x9010b01080a0e0d0c050c03150711011e0903030204030b31030c0320010623030319050309030d020403050c01081e2701020409020a08010f0e0a09020f030f 68
    0xd001c241c0c0358000800d007884074080c507000501c5040242c5086120f0200988070840040800c68007405600b41c85507240d141045200703901c42e420000760845080080e0060041410100741410f503034104040005076440c0d660000c480c20365800710014400d1f903a810b00714001d008079000100b0300350520703080c41810301c402d07140008100c41c013010013005940c1d90003009210042c1740100030301143c807449140012a010744104072443c02e040e02401c50245055003038508403038880d00a84c0004e07804450000c1c95101020031820000e009030000c51414154620f0001c0240104404004002c0004001210400244140d9000c044030740410340d180c980700c1c80c203913440760051403585000072040c80010300603451200c40158121006852104640c8410940b00f02220a410100f90a40e010b10000000c2040c00d100070001001d00c004d0040c0c859804040c001c1c08140180c1c07240410b0010300b5020702010b015003101c9508240007400019690355030307101040e1401c0031018030310341c5400b4020055440e0f04c000300f00c10b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 346825089 1250 346823839 346823861
    0x180803040909030314010f1a0c0319020d02070602031e070c15030b0402030402180a0e15040c060207080d0c02040603081c060b031918020904050d03050106020c101805090901 76
    0x2032100001401714045020000d100d8014000002a410081800d0410581d843c11494000c841d181206c0c1c5002e05107107a101c003003081c0001200352103600c1c01c01c2c0e041c000d03111501c8a502c00b070120315142074002966406080d9a429408605118441c2a54a01c02c01c80305050f03404080724000ca07580d103109584605505001001190501d0031004503450030348220b9100c1d40d030080c42c144c0780100c1c2055100c1c3d00b400081500d80b0300da5450110002001080000348241562220b090f501c1d07240c207140440c403400d140d9010000350750045400340810b00300454014540c6416260182c4045018000107001d4a4203030700142c60400d00281905a03140b00007500c0c410020082018030499544000c4c8801310320040701c0e01c42c0500c150040d503610064040e001074104d0300c2d03000103503081d0100d1600021003200c001c2d201100c1c01d602c0922400c075990f03018014540100540d0002e0100c1a411102141d210803600d1840c000300000c610402089824102e00303a8080c050203019030b0ba82e4904420340710300800c264810303 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 346826339 1250 346825089 346825091
    0x509100c091a041d0612011d010f020c1e030d020406030b030d09080c12010905150919030504060f181e0b040b0f1e0a0302040f06080906071808030409090303 69
    0x20000d0106205821103081341e90703103c100724840440d5100c00400c100d02815960340003040c04402010000c090113010414268000158600781c0c00318803903400c6410040c3c0a601641c014000d1009003640070415090306500904102c2071400c083c060541544104104120310b0b46c80400c02240e25a496801480403000c203900304c40159484900a46056596100302039840d400090540e2050418104103440311150400200305090f260742c41f503081c00b04d000c10150b80b0411550812101c00401c000383d95501c03214861404041980da00d0040030f42c800c501510050020108600d09194820910941407400c4c1c1d102d0481000e44070007407500d20f01c24143354a0000c02e12180003040e9045100d048074216945006079614082d060300d0310801c25004644030003000268100c062180020000051060340c041d5a0010b03580c40c02d0031205403504080390440810409a00c0410034074001c001a419001185410a003245603041d01c1c030f82c6a00001504680780b903010104000a403010903400c182c0b6640c2c07190720 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 346827589 1250 346826339 346826369
    0x3060510021c110114090a03081b0301140f1002100507050901020c1203091012110304050c040504060e0a060237080702100203010e0603070801020306060901030509100c09 75
    0x100c01c0b030780c0785012042800146020400b0314802801142d003404000248000410340c441169400351460000b180c0b6011150400c02403041010307071010509038442110116040c151001c504c0741c205038081402992a003120005038010076507210701600c1c107950700007850011446e80090380291a40040c110001043c1d080c0804190040c0c00350007035071804030042c1c3c001c140b0b0883d2402041102b100c800e940ea0224001000140c1c140c1c1c850441d5982c0c5039001c2c1e01c41b05130100502c200700d42290b80c3c2205600340c0303038030500521000030808240041040400c590129980c0c0b15030030100010a40344885000c14030441008070b081180c80d170090110300a074000044da0b412550002d020301c3e98901ba1101645c0c0414a4030b031142c0c90b01501c0c0468010b0103920480d01028824110a801c82c3d2081c1c2100200c0201001008080e20307040000d80c001d4203850000390300310b003800380c0420328134010b03507141e2418140c9a00c00a243d003001003100441128101c0018000540f0704039015000d000725000c1d640407090110 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 346828839 1250 346827589 346827619
    0x907140d0c05070605092a2803060501080a03020f0703170306131b1211270a0f180c0818032101030b1e0c0a020a0c0605030a18080a110a05030a030605 66
    0x1001ca5603a108001d071206202302c40080c8030742103607444050f40100c0e00c080f0000c0440130412a00c6042e01800d1481c000740000c24040c14041e141400c202c885010aa00030001880080c1c0d51000c09260001c620013503540b01d80381d40c00002c080c05640707801d1059440c6003151341c0c51641840a040b040400b000e8450407a001d950540c42d000383c85000c50030a0b41590200076260482c1200e1520244200420104118802c00e0b100000d001d01215441006c030000051310500070110004014020414018001c004040d031440c4d000d07041c60742c0200503a030251000ba42c0e0030103010041c42141c0981c2050011640c68000c80803108940d000700780001ea41c40c01c4c0c5100000c0310301e1201801401e419006603099441d655880c6900c0036181c0c0407500d0401180101140c010000d1419100080a400b4617112a0303241e20341600340008681d07010303140388640e1981c2c4000c1c202007540340049400c192030320718283c03003e80c2c100b00105162001080000740180300000d48955081e90580c070010660740704640c0b60f04843c1901c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 346830089 1250 346828839 346828903
    0x7050a1103030408090607020303070f15050c0a0c110310062d030506041115030f09060a060f0302103c03090503031609150206060907140d0c0507060509 67
    0x2203c00400410b420000b4500c240380100240c2025440141140d144c15400c3e52040030f08211814101d9506102040002d020500c50040961001c4600c00940c241211248000c01032448000094051610000c241030107880c28801d190390101d03070b00c07000d0150a507204441c02090001006003582d040040041c2241225040c1a0008403604030707000702004e4a50f500d40203200d0400c00607050744109000ca01c0743e41140038a016510a0024400d50701e9a403416036000c074200203008183c20300d031910b410028424000c7c2d01c0000019660140e48080c2150007142050707070903102e42505c00340010789103c942c98071803580d111103003042e100c0c07040301001d80c04030700000b90186c0701404001807441d00f050000072500d000110070b40c44808160316007403d40c1991080120f89071800040c4680050300003400300450341c1415550590040c80c10b15004122180344011000c4a00486a0310b0b0f9460b520703085c4c0000c0551042064405503034001104001c1307401d02c02c4d0796036501d5038149580640d00e40003d02800c02c815403 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 346831339 1250 346830089 346830091
    0x110f070608010608060d15050a060501020105091011040b0c0a060f0606080a02030403020a151406120a031209060204060e0f0a080c0112180b040c0b03011a070f0b07050a110303 77
    0x503644480c5120303400e01209961684000f490184c002d07010751596004645022009076546540e0000007420781810a521811303103030107412150641e07041005204004000240d442d840f4030400d00c0004100346488200c000a04c900c1d845400744032030215800c031040c0303004101d004040d8482c00c01003000790310b01c10340841138402503c500004250365100146100c0c0207900150740c094444c0c819a10300c040c0d142e480903882e0b0242d143c229561035440c0e090305019200311600507000003040741c45078029288010780301c1ea00ea60b2001c0080c00c10096464046035440726411101d43ca51b4071031015900c80c0c0d11000020518040c841c191481102c40c01d0203440141819000b800075034002e08064100c02c1242c00c01503030340d041c8940080024503030b034820390f0b040d040c4981e40020146100301f5000d5294101400d000b03003000b035240c11194001d81d082004002045212000115101307210f85c0b06610342c09076003050340300038a9460005e04811110810020440c1d030100c0100f4a40d032003520384c0c620003680d2605081c0d903400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 346832589 1250 346831339 346831349
    0xb030f061e100324050c040503190f080705120403120801090c17062d2106010e07050c03220f050d0f240f0b0103090b15040615110f07 59
    0x20b00c0d00024004100a03244009861080c0f03d10305041039441040c1c041283c0381107843c0b1124581c04103013808249028401840030701c0c2d8180b40b102d0241040d484a613440d400e1008000c0040800046c2c150400c4802e10000c4a102200700c10319460315030780d0815026041d491100e200004410400105040d40c80d8801c80d001c0c000d6583e81e803080355011980e008080340010b00220383c0a02024030500c07030107400391010081000e0a188030440021100c09119030310031204000811a0705800c503c1142c4840081e001d41103030005140d241194480801c262040d01c900404803041d40000100801d8008101b01055444126001d210a80e1580c3e2203c902c4805194094244d1109580d4085008607112200103c4018000c07115061103902008101c000d0001c4be80d005004540c80b501100e40c2d000b40b91040640f180c3c2c007801d090111880ca5502c60f070031080002c090506494080005091a0300c440e84940042c2c080207410004c0b111515201030801d0100c0c0d913000782184508603e208426801007a240e003225 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 346833839 1250 346832589 346832611
    0x30f05070912030c150c0e04050606120f06010504030618030206010b0307090603021b160602191104050a0b10170a0204030309061407171b0706080a02070201030b030f061e 75
    0x3902c565070468507111610000e80700f09507003007a0141c05040501c9070503110741d859224a0030301c969400902c419030f078009140e640700300c6040c4032540301d0729255200164403d480d5101d41041d40c2d505001603a0720300a0b0341025210f185003c3d20500d113289040c20242100d80a0380032200c1603aa55000c81c1414802126420001071075030100f000014041c0d0042c0000d0400c0c00c3d4989610401907030f000e8607001d0820130300d5a20a280603010402c10b601841617101000b41100040703030156040c0c5505022a03030820a80780256513400000f4400b10840e13003c4111080b000f0410102410032241c001c200400c001a448201d10300a00803400210047c401c0300e00301c9906490f48501c06250000a4804070840d180b02500004100f0003140040c0c1d2001c180c024061400e101a0b0b21100310b00020064100c0514408202307034080c11040c80140c1d003114500d5032201102c0d0f03001d40c0e110500e200480150200582154042c860451103403100d800125a030f40c81100300d00070041c5441c072441004404490147c490121034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 346835089 1250 346833839 346833869
    0x304120207030b270106060f11070509070201090b070305010b0702010f17040b070e090618040c030b04061514010c08130503030309100c170c0f0408190c05010e06040905041b06030f050709 82
    0x4580140272001c1054419801d54880a44e1800480c000e00c07011100000140d40d40c4014804103c003e0301e0721034100441d46010001b030341c104014030a15201d0440064140683e0300d80300c48216110700707a0b078000c0c54140c6030805002d003024500030341c031520180c03241e80201e450231030980e0643c180f00c180c1c0b41c0b141100910310610916840425540c19601070000c0c0d9101200340d8012001c00c500035800340c003a80c426140042e21603400c10f0309841c0303012507030400592800051000c800682c0d100c4103191509400c06007481c0d0390a02030414448010703e03940410b81601001c01000003604010840b107142c0c1d003042001b07200f03101040c041241c81c120b141482c11250124017010a44441252002e4258032501d000324526040d01c56400a1030700d010030f030300c402c580ba481c02116020000c0d40f03002c07000141800c0c02c0865041c0c0545000030818013890141c504007555410005061047e1254a5640002c041d0031129420b031719140000c024006910078481c030315041c400814841d41c030804009040b100d4000d810264 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 346836339 1250 346835089 346835117
    0x1f08031810230d0605030a0f0204060501080c19110109031806080402030303070f180e091510120807060e28121d0a080a0303060801050702030304120207030b27010606 73
    0x402d800141e0442c500544d18400480c031030300d041150202c014041c4d0300d0030707010950301d01c100000c0d10982e420440c10440700c002802010000340040d0751446c6042c408440c03183d0900c410882d0944c144600326949136003401c403441c0a02d03800507050101881054040320707045848080a550f041e01c103440094240d40f041000500581c4242d41e840306040080c074203509105445000c01040c007215410004125000d681070081c0d00c9010041c040720311340102221161071502901a1600346900e210355800c0c10001c0100408111804045910b460b90000080006640c2c0002d456914000100049403030400d1082c8621202001c20925880e19480b100f00c0014040405003101c07800400808130700001496440a03030b096562244440c06000404014000400d00d410010150341042c0c0c030800c074a92600d0144004e00383d010041381c0d400780e040b210020245078201c008030300e030041da0380c4007501c1d2551040c02d1000707841c800301007000b4203500f4102c030398551807007911300c01e0880d0b0582c800c40303010811000318808 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 346837589 1250 346836339 346836407
    0xa0608040c0504020f0306041a032a090708010807080c0f101b1101140c0705010507080c070909021509130b030106090504050d0906171f08031810 64
    0x1510078412128040c0a680d24070110707003640c00900340d100d0242000b20403c17070641454801d0703401c0b801c107600c0022003160300c420100e030710742d01c001d50306440f0742007601070740c185001d00700e0014011180301806550036440c03c0c150003083c542c4280520342c03590142c000e001810681c001a01100c400d0000d1115002c94461400c2044c800e51200d0940c0c02d02261805224050364080e400d0101f00740140101c15081f603510000406080229403030500a201c01d001c14100103500145640c19240300303007080c0d40e440e055410090309502a04140e000c0911410102050303400702c503000303d003101d8400c0e9100340040c2c3d284191100385003d8070381c1c00b680250448801d030050201039001b034541030030003800000e001a00c0e8403010084d608200d0781034030f1a82c000304482202c15401200440104001c0ca01034011110402c0005182080580910302441ca1078020115600b0381082c50702c010f00042d01101e03940c2c1003000e20300600d0410941103034070402c01e0025018825000320010001001c2248c40042e20b0310030b1a003030741 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 346838839 1250 346837589 346837591
    0x30115120b0d320601030212030c030d0912090608060d0309080307052401030c0b092b0b010b040b070831151b080a02010e0d030e0c0f0a0608 62
    0x11061525240c0342002501c8041c059103400340642030001151004240e8008007240000810016a840320f6440070103001c04136140e0305695048666010302c0c1e15488070545180504010000507000020310b101007030407207a11980b074603403054150802c00400100b080c2c5200285109200201c0c0c8100300061482c070f449121030b1040c80c03103030401c0800561144405451900950422600c1358061081c00051407000c05414011481d4243c285205604603079454226104038484c40002c4440400d0715506a80d0303190014403014040022848541c403e4000c42c90340f038903c0701d015591101260300110f103075071501c42207170b05070354641403610f2404225540c0c4403426030140812503c0b48120b264292900b401c2d9001c140a044400b01246001d9802e001c000c0c140400e030411404140804181c030f8011a100311001d807018580c02440c29525105599030907805804500c100138800d0003010030440d107098241e40305001850f00e080c01c4440c044140d105212242800b40b0440c0e40c49a83c0c00401c110544c400c1800f9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 346840089 1250 346838839 346838867
    0x804030f020a06110a0815010e013603020907031505010c020406090507021e0f060f060315071d120303040803040c0e010308091c0c1a04051806090c030115 68
    0x101d0b5500c103a03440b00310485801c01c40048910400050b0080060350044d1159003060300403c0000000c0f22042c00601032004410a480c184800068613001e520001e500240700000034150805c149456520034000c0a10300e400100d11407080305011506691003842103c0f00740400c10181500300707042400642c0d0060010108a9200e62502c10114940c1c249010703050107080c641d0020900032590400001340701800c00e00d20012a0312142c00a81807107000289580c0003564422146001d40b103901c0402e007805c3e41c1c50001914101080240481160b004121124201000d402030050500140030010440780d140c403401c03110352082c00410301103102c3e00f0045810500c12203030081c4c01c23a40e0344004a0280000da10665000a002c5840645424030510380341012034044e01884801103160740d4402c4504e047d005100c0d0015002083d10320030782510003218050040202820a42c00194032a0038141d40d04462030b0740260b00100210300c581d183e11342624142d504040c3c1c0d10749048444c19040703a60b90512021 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 346841339 1250 346840089 346840093
    0x30d2009090c091306090506010e10051804060b03040515010807030c030b0603010e06041a0c190c06021c020c0106090507120902030c09010602151b0412021306150f030b010804030f02 80
    0x40d5010f840d4a85c46600010061000c02041c186040c00000d0b0241f007043c0105170044808000280e03080d6031040071141d02403018680c2da440b664010020800800c0b0301c0e041400ea0020010600090283c00103a10301c41c0d4100b119001d8484c0e0701c86602c2501c0f203d032440000c1840360342078420700000350700c242541d40c046006000010b40500c80381c0014680f4400340c03402c0d1180001c81c11800f0f281107115086941c8107003001c10040c030b4064058812202007044034400341c204a40640b031b40003000ac2e030ba0112240d9a034a480d030722004070b004903082c074025405070440385003d41c0780000c0000d8041590040f60300c1a0242c1d1200ba5044203000803403000703043d500d41c08a0f0300d070243d40708880c0103940b042c4615001c0c00c681c0c1c6c01054000e02e41c401102103540c0140c940d075206903600c0740716846849110100d034140e80d00c900100e400b52444d40302181700c21030100c01030044142441d40100310511001c3e1002c00c40360095a07030524105500d00245e0450f44d080782014001801e0100141c046400351341000043e92a84c81 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 346842589 1250 346841339 346841359
    0xc0c010e06121b190f0519050310080331050a060c060e01050106050c010b01020114130309090e010b0306010608040b13020f0d11041a060316020a05030d2009090c09 72
    0x101c04a035100e1600720103220f11240200c401e25511656607120302d10241030492501520740c00981416121f02c420b0410007600100244194242800071802451060200da45541c10712452260080c4481808016a00707549280348070045516140000c40b04041e04070090b05042400440e40b0304040e8074140ca01540b108580001c1c01c0d024455180244001ea5509807a58500842c0600390b03515065603904581c10b00d480002c040e050070303104c96000a6a4480c07139170007012501d41610064019030109080e98640f0a007200d582e4010740141c201c04030200c080c5c4d141a0380750340c0f050f540d004054a0180046078807800141c1c1c2c480301100c8500760300e4001404400803e40314000140040d1088808a4840c540ba04c07864200d810b150085200b201c1d102c44401c0d01c0d505190340807076154000104003840d2400800c5920b404180240708005c009500b10056a83d5081c000b41d80201404184a07a642d601c0c2407448159481c020740000d4071600200181024220303100d201104046401460005900ca01041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 346843839 1250 346842589 346842631
    0x40501050f0f07060203060906030c0a060513030c12030206090d05070303090206090904060906051008030910090e01062606030307110a05041a040c020307080d0504080d0609020c0c010e0612 83
    0x150143c90703001d10440340584d592418005024903588003500e071074044e9000264032812541c41c524404280c40c4c7c540303446038503400304c4544090b0072072140d84061b019071007010000c686250b40d0460b140802d80a90201c40e65500e0380d4001941d83e01c030020700900010341c14410b01c40001d10a402400c84c803400100303140d05204002c0c2c0000c04500e0103030340c1100c100359a5040c9800708652405120780c018900b180c8400141d2900b8407141d201c0c8160604540709410b80340122240300d000f0b00988014021010360000d456071a050007402d03040c0750362510140c1001c0f000b032005c440c0051a0030320348900c5001e000b5505100b0b440d40d03880c60301c01644010740c0e4081340e441d1700400c80c0e4440c0d120780c4103900d40984448043c0f10019042c40704a0308001841c20440d0001c1220402044820b0102c0d0301a075106c4100160f196605d0501451380e00500c0e04a038a16410f0500016442c0c0303094015054044074201600c0c0b4006200005640389614519015040001840780c00d881d04d00d0989910362244c682c5c608046d0000e044 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 346845089 1250 346843839 346843867
    0x304082b080718060201050403020f0c03030f03041e08030f0a0902060904020705011409010b12030307080f04060b10030b1206060108011403010207020402040f0807170709050c0c10050106120908040501050f 90
    0x3e83c00c03080051b035581c1d081000b031542c10884001081600800390038681004404139440b8410085185405040000440c08000310000c5400c0c00c80f280c1d803a03d0640f40d515150a02080e403080e958001c5160960010881c0c910340da208512080b64000c010903c1d041075103040c40701942041600343d03100c3d5030721711020300300701d462418841c452214080001103041d480001c01051001fa0140040b00b98424010007403041c0d04807001580105007000b100754141c1c0c5900e040c80c0a881008074068000b0340001d1400701c0b0540642010300071401c0ac4039462010380035403401720707030320f0b2400c481550009010f580100203108540c0340035542c04401400240c981b240d150045000d9030b01ca07911140000c881c2c0b50081000324424040364002e4416011a481c24403400c0c00e106558504034054010850b60324408182c903c80c1d50002c8500691510060b140240241c15200c00141f0f000d00c036541c00708515070060010400103110ba20050340c0d102c0d2045050601b4030780115403580180c0c0b04294040020001c070281c1c1003131 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 346846339 1250 346845089 346845137
    0x9030c02040e030a03110f0906071e08030610020309030c0603060103061706150109081c0306091508060c2505031c061a0f1801030b040c020304082b0807 67
    0x290b000450390f0b988000c400408407141c840c0090307103610050142c0d103501031500303084403040c0100321303411a129806418080d003501c1800300d00061000010008004110f61400510321407401100d95580c20220800e060362284184000b40380d01d40c00000f5046854900b030800f0f1900140107140014440d0b864560b040500481203c00e00703801d034410010003004100002c00151225000e10704180b00520b40f4800668604a1500d40101920040200d2000728480d6000400030b004516091008001d0102e24040c491964000c0b00e0381070240500241280900d0001c8460f01548480289040e81c02c8182c1403103555441d0340101c600340000c201c9040700a21441035240e90800100780014107903c0c1c0b1000040c00c0015101d484e80d02c13a002c0c40034401003019001540d075402c54603080c05a2005c50000102c00401c0007440250f48286488810b04115a00001034800c0e101c60740212004514110248910f010100182c1910070300c0303101c03012035524030882185030040c89908180c1140d0b03258010303c60307203004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 346847589 1250 346846339 346846361
    0x3081512060f09011e050910020304080903010509010c1d030708030a020610080601060c150608070609050f0603010b0412060b0306040b09160b040501181205030714010c050d09030c0204 81
    0x3001c6000e220511003003080294120100c80000c11440760280c2045040c50303449018003c000d5a2400000c1940c541881031100480d5803102c215034038540f52901000300d03000768401900940c6403000084050005119004d00703002d00d51120114004098070f5a0180843c00942c00c2e007500500e040020081c504001906956245070041c010510b0410031800031102103601c28201c950200c801004540d4103c10301d916201c2d08140e041200154034400748010341040d50240803544650340700091801d0b03104000d14255101101c805c41074904400c01c21070b0f5030000f07000f080001d082c100b10402400385044005140c0504c0380e2004540c1c0c0c081c03040001d0a0031412201650b02103041020418a003105000091580c3c0d29814400012405c09481d180e00b8016070040754148040108a2107483d480b0800e424024a4100c4d0403c903010302d9450071603217a0b0420202200c40c070140c602544061031042c00364030b0785121940d9449052503003103080e5601400800200744e050105242c2590056150303400b030120803072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 346848839 1250 346847589 346847593
    0x9020a090b1824030c07020d122003030c0901030902031f02090a170705011d030f0102091c2105070f200a06080408030a021902070503010b0a1203081512 67
    0x44802041c009120603c05040c00000c4000300c10180303a0750100d0a8941088600709011380b107060780d101046400441c1000902050882c4034070500c2c40390b02030f411000a54200d502c000d0040c920400c000c2d40d9001c00d94140701718901c1404208a254400e62040310900d0005007107490801c0a9500d0385031020a1000b03183c034160b00001d0100c1a4180f044111004019880e1000c1010500c100344a86804480c0200d5040103a19032040c09000c8401908401401000781519844403550801e54009c2d4800f00800c2d01805640c10007003082600c190031201382540046d40c0704c00014403d1024090030103101c1d1031100b40842807216a01041e5059035803040d45105808000c0b583e0740c814240c55045039015011440b50079030360014048143c0c02100c20740c1142c0e0290425850340c40e51400e08003e80282c00c1c2c8003050f240a50342c052500740d40002e607070007280e60644c001c00131418a00280008025140240360314a28103540e000c0019100358070065000c60520000340f81a07802a000031022810741842c0325087d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 346850089 1250 346848839 346848877
    0xb040f0c0b0a02031e070807060f020d0c031b090602100e010908163305062718070308190216120308060306060913060207061107060c0e03030409020a090b 68
    0x3001d5417202d0510005942030001d003081c80995481d07089204240004024a0710340345501c0c0e0840141c3c041da80703011487c1070f05110b0245507000040003000e200035034000e10300742001000f110a014800250075a600c950280140001c00000100503040901d10310b94559650000e49000c40c0b40d0401816840440803030714001452a41031030400083d181507070340c0303010f50064040051421201c0301000d0035019007101181a41c0c0d0f41b8000b4015036908071040f9002c01c5280007050704001e01c0100d06120f1113070081d00e48440405821690b54510300d0307010040ca200e0f0104a500b0501c460b229032000c101001e803040ba882c40c4118216445518841c4e070282001107a140c1c811400c06404c00c6c040355000c00b094004201521303200c03000078514080070703029860882e000ca00410912040c2c0c0c0460701450b800c01002e11015045840d81ca1056001140a035500d41c5002d0029100d1407240701c003825071000060007035003403070705003100a0020f5001c1400d0006000f04848006011380c0c0510280081c040074605400d04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 346851339 1250 346850089 346850107
    0xa090f060906030e070b1905130f0302130504051b030c040624030212010e060114030c0414010e0109051201090605190b060f0a0804060b1206060103180b040f0c0b0a0203 74
    0x141c4c1d001d800f144c5007682014a007800031700600019504000702000c00c44036280010300098980d03110710003500000000407200410f003990700103800411280300342c07001c1c2d0840003800150001c035441558005d0064214040000340e00c80856406c40d11948001d06a03100d20403c04001002c590017503111080300c03045403502540d248102412480c0e6082e60341400c1d0301d0134400010390622913805014408005110402050099120b0045410501c0712080d0207030b92410324007003500031030300a4403030035203070086103202da44c0b95521800140001d08410384680340d070682044100003058440440ca0034040d90707078440340d4000c0366184c000d090054050000d4828000398000a801c160341c0c02c920014002e42c030401116200d42d0810003280e2546069240c00e804130340f03c03454210003403c1071780c14103036100100760718001d0060000b0a00034002c0c2e4091300c0c2001101800085160031504285010b040e440d104800140882d022a141a00141c401d60303240c61710301e4440a0030b081a03044510b0a4005a1000c00d40b188 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 346852589 1250 346851339 346851341
    0x212070c17040e01031e05071d010902040e07031a19140d0503040e091501090209130509030403030c050115060503040606080c090a020901020a06060b0c06010e01050105030c0a090f06090603 83
    0x34007040c0701546441d080220103a0407031010320009003999001d103186500343c00100030b40e17002c15500c40203441002c1d5540314015010340c40142120054541280000390380b650903c00c640c02c80304203025502c1b0569401c1d009038000c06810611880b400c402000034100360f030b1100040d413001421840700500485c10020400ca00e021240d2045000d41411038521001c01c100100b030742c00321140e42ca4035424a9580b17070411410440e80502c800b560b0035021001149081481e009440b040100b500c0003400b05422448e1002525015605416150000c200600109215000400002c1d00a1001040076074401045504250031940b00c41700280c2c01109010801c0300c039001700c900038606000140200c0501030b0000358030701c0c4c0c0505004038040d4006000803459009001c0340440369008802000f907a80e44d68030f10061035019410075809400b642e0300204040c5225503007117068490694600b400c4d5910254131650b140c0c0403110b0303e8240f0415440003d5081c001424800c040e00c82681c84032045071800038007030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 346853839 1250 346852589 346852613
    0x608030c1005040506060d0c0e0a0c0807020114010b0901050f0703030617010225050f120306011202071e02120708010213140d03031a030102032502030a0813060212070c 74
    0x301c00c034249002c1c400450700000c0c0d20703a08040f0444003903150803205d1801005a0034254010005042001e04200980b41d81d68004500b1000c0c613102da40c040d43c2c503203004a0881e131050120b04459030100d40103000b50303042c00014010064040c10928681030858618010036040f082084002903120354040c440c440401d04030024000d0355100a40c10b058000c114140c41284840c14004001c00c3d88021a050000c100600185555600180d603083d09555900d048180d00c100c0384180802c10a09440e26060010f01c04c076050560050070410040d1039002c0707a0f6444512404041c0c8c0c0c419901400d6203c100000c0c801c40005000708000140c0c4d4504c240d100d103803003400c2076000401ca140c8900c4440450703101d25418926050b810700e00040c4d0140c0c18120039022140203005190598404000c0000d81001e116020420041740340500084828214040b60740344070302c0c0000310006041501080e1420000325090b00e101c0e200f50005420000d000d01c24004c01c5c403048030f1f0782000a000c07080640c14410415040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 346855089 1250 346853839 346853863
    0xf07050f1e071109040f0305090f12011a010c080306040207020d021903030e0901060e040b041b0207180b011d03070e04060207020f0f030a021903080307020a050c0103270606090608030c 81
    0x2141d101c4ca041e4440c00301b4001c3d0600064103000c0300251024030307955400301e0103a00f0000200317003c0580344400e01c07039402000113031107a4010074460075100050350700072b0444e121119800552549141e9170030003404041d4100300402c9030483c80f8001070b5001a0782e401000050310001d1194a00014030310b00b80100790301e03046c0f072043d801038a000c00103115003a8000ca0054814605480220340050400c4c0880c00415460800807410407072000c1840c4803070760220b204800caa0b490100c6100074000b109414044801035080c143c041110b403442c2c200c0086102c0f03d07400743c800004041d20003180c1c0e03603441c8034100042100c0c11100c1c2ca0340011600114a03050b088045c603194280c0300c0303040280c0248080380d40c4003004040644940c1e840c2c80d08190000305817a07540059980b001c0b00c0f0b40c503801c200002035030711030001c03000321194058409202001e500c2481001c141c5903a082c0d101c000340316011103020f52864261303c00d5404a07243e110200c0e6411702400f82c40000d00340c0c07200031903540421801c07690900425800d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 346856339 1250 346855089 346855099
    0x20303191e0519081018020c0f0f060f1315091b0e01060c050a0f030206040302070608160807020c0301050c0d06140609061c0e030415080f07050f1e0711 67
    0x80100c42069441005a005180303007088502902c950201021001c41c66200c06c0203502030303031303d20070500d81e035900034105202170703101110300044883c0e51440d118104590341411b10b902010003c3d25603818140241c1d0048008940701c0990001d5032103604050010030b10082540b03807242c14200409c42803c4d84240c4c4480c544d05481d00745800c02d0601c1d48108010b10840c403c01600e036510b102404824406070084545c0800d001031300c00460b260281d140d41e800c0f1400d4000d4002c00e000082c015010707181c21482881042c0700c1c01003206c00d1000c1556402d2003d4040380440c8140c15240785a81c50910404e07001e0784c0880d80064a64070700d1810071068804c42e030003411382018081000c408984410007582d0303503040c044400d9501c0d04c5035003e10380803003010701c1583e181043c1012181c4484540c088000d009444410b002c1a04615802c00c040d07440c9182660442c640007242000240c031244541d014184e8514040321942c1b511140d1000d01c80c200c20307010ba0103200010006a54001c0015883e500311142e10107580b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 346857589 1250 346856339 346856347
    0x5250306140105130603110d090b010e0f070e13140403170c090105040306110c030f03010503120306061b01061e170a0201140c03040905040609120201110412020303191e05 75
    0x3940030344c2c2180611648041c184c84501d046040203422003500c1100070082c100304984d18a60500085d064401c0c0301303540e01c0c0c1a030240441d00214100003100c2c40b0f400c0c141c0302d00110104a00034030180b10800389071048401d581e80d2074401c050880c0c00c01c250045000b5551581d9600080c244035265001c0034002001440c0108030f00c031803d036040400c2c0c1e07045030707048036000443c0d01c03542c11080302d148078070b501c074410030302000801c1405091040d01440c141c6100350110344003044c01c402408240c0c8001e80311250311075014860f02c810341148518949048040e42c0006c100b150340c4d103080307008001c01c2e00300c9968110b01002007408000400d589007807420320b0000041c1040c0c0000d030000b0303003000414943c038042c0a100043c08019454108101d030b0007010315400401c00c43c03505041050042c40020740440341c5d1440207140c03017040d0b1720500034114482000c0d900d851405241c003c8008111108010413a0907000c24003040b0044540f80811100d004d145445100000d4812411050181e89404140051010600c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 346858839 1250 346857589 346857607
    0x2030901090311040e0102160c050306061e041514040b04150510111002040510090b030105040209040f0905030909070203040b07061e0e0102180a030b060405250306140105 75
    0x1010000c112504a0380003d5002503000209014102c882d220350316641c00001c44181082100200d620040d0040300c500d410180c031402015152041583c64540c407040d40c80340380c26500344582d14202442002000000c1c00c160800d0804a00109075004081d8403d001d0003103140c6081c1030007402c0705070404590811161149101c180041c00c06d5010306401103042a140e806118000e50305c0c00d0a001400c02156007041e80c00c90364402941c85402014084e00d0700010300c1640500454065090f9072000b10b038181941c0c20704042c4002500248000c942c000c0d20303000c0800d10155284540c00e2030300d0150010715030700c1c0c540c1c3c0305010031824050700400455004001c00c001b0f00c008502500c030305540c4102c0c00304808c3c0303542c081d4681c46610385484040d46841c2c0714444011400542c0100aa16407a038401c0f4071003a00c403010488250f0451002401d02c20208000441c940b030140d00580d4070001100c6008115100c3c5218510366024448142d00400d42c1c0b2081405000c18a0035020741c2c01c642441c0c0305140207d54 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 346860089 1250 346858839 346858847
    0x60e04020d140f060c07060c080f040204150509040804030b0106090305150a140a0c0e032103100b1902010605060a0e0f010e030a06050105100c0807080d0221090d02030901 75
    0x24026080b240380341141c1540780c074203111400e0381039442e20441d481414a007004214039489024119030079440e025400d0081070140d07171240d2050b0700c000c030b4001d40b50741c2c3e80d002d0001030305400c0c4808000d03100c009004200c9030764002030380b4041c60265510030745450840c40d1800743c40b6810303081070043c0b01030f071a41040010703400a1710540340c28004620125036124803440401600004500d100340800c41c004118070b0805651200b40014200d40d510040c4882d50000d250710340b80c0316141c0d03c206001c00c04150345040c40840040d42c200d8201c0703d5250710941d41c2e401766105034001000c10344022100515000b2855424050100544030440d200e03860b007280f1601c0503000301e02d4000e84600555041203450360030fa0041441043d00500034003600d403c0d03409031604500400c0700b40038007442503642d04800c0503401d03c18191009060f40c411009841c201d100c0e00c42c9000307504882c155011560302009000c1c1241c0071100e1500796000d5208044546007809810b46090082c2c48400b102107600610081d01c2c181c4e48 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 346861339 1250 346860089 346860109
    0xe06060304080705160605030402131109010503040c080d050417010506011d0a0302090c0d1b0203040e0a06050406030f11011e03020717040e0910020324030312040501020d060e0402 79
    0x401001070760340f076801c0d1a001d41440b405140d0820604c40054000865682250040d8840d5100722180403d0351000c00c2c1440840c0c050903130034286000c0c00c8c815022254040e0004580050040c480c04500c42c0c0d550000d00c4c40d00d105407c8002c0000c1020404000f01c540010b01c5000011018009119502d042d000081c400c61541e0104044001880306541244d120200303800061038003c3c106014031b2810221560260380056100444203180c401e0840326401000c01c00600b02ca0181d010b98035042c50220344000110001c1d050003d503035640c000003d15a910352044400031031150340540ca41d4040d074105291601c0c1c0c0d600259040c0600480c80000c0011090649154040c56040040e1603441c1401c2c0351008000340030008545540c0040d0219090350501c0c1d82c40e02c2050805c04a86511a102080700300782c0c0030580b1585980b00314401000003c40d9007460301c1d1890a00a01124105060100f02c0856440c044c0c0c1d0a031400d96000982207446542409400041c1c0420200005181000c1c0c0c0406c0f94080 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 346862589 1250 346861339 346861343
    0xc0307030507030509090c0414030f1528061a1303080a12020403081206030f06041e12080106110102090102071415070b06031006030b1506041802040f0e06060304 71
    0x21001900b9400c160003036040d1954104043d28001311841c0c01000c0100b954020f0043d9510407c0b020359522592500040da01000741c1850041d050403801c2c81001844180c0c041c06410b42001c0d602404040070032106041a4514082c000211301c0626200744c480344107600d9018041821810482c1c0301c0c000d10720f00140022664013900340d56076850b40c0101283c00748030150705c44681c05e000040000074014490702911044010002002640d2100010169541c1040031041d00b1904100002008200c5001070418801820442000d01c41c1566a640d065030b0001d0755884003240b180d60040c0855a401940c0f4030500000c80300841c603107209040040d64a06071740c450048a511540495032007034542080508010307030342c10361302074440d000340c42d122082000441e032260103445003904160040155001e00c1040302e80100080c41d040d2281d021501c041143c2c204403541101c02000001090030035000401920340f44000010307296410071403a1012400740390300000314481c00900b400300d02e0340c50f4002c0360b030042c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 346863839 1250 346862589 346862597
    0x90b0901120e030c1b01050702220209040509030316080106021b0418150f020412111f021501090e121809040c090b04090314070201050409051e0c0c030703 68
    0x1c1d005403408040c061044018000d404041881155000300094058090001c912806900ca4903c80111070f1801a42c3c400382d8014944000300c0d0301d8620b04890200300010f010009490709a080c1c0102e8107959003503a6a80380c540c000001c00ca00c4240401038030000420916282c01a94907005000b5920280b4802c070b00300001c0e506103900b20503901c9901001840e10041024581d0390190300b4030200c0700c449001d0441c141400c02242040c040b003503108603801d0340c0501e2120540301c00f8640f10450701001c520700791600094400c140070712000401c401803503468001e500400d420038202c891360300f40c0101030f8041c0140900340b001c0c00003102008601c0190302d0b400389840f141c0323a50f40d0a05551841032032482c400d4020404c4414003040c801014124001d071488034005014848081092200b15481105e01800007203a4806021030140100c009184c900c0c0145023860a1503120094030003150342c00d07951410b84101040d4a00001d02c07003940000d91014901000c0c504103105005a151030388200c8100400304 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 346865089 1250 346863839 346863857
    0xc061308031512060108010e061006050f0a05160b091902130b06040f0b030601031b08040809040605030f0d08130506060603100b1308010b03010c0921050f150601090b0901 75
    0x2d81c0b1016003890f40781c00760008849803541c1d1044d9290090140c1e0450110354060080018122180c0046407c112049030f600d661174000e1440c9044260741081840c0420000c0803c0391840d07a001e0110b45665950241c95151303420b05000c002ca5141c030380300790b00c4000c1c24111031703800324090707540c1003809500700d84001004201d1800d084005803403841943c0040190607104440070400805140156102e40c03001e8800700400b1004200030707031a5013449403540e0009002c800c001000590b449000c1c209024010344080351307160300c8074000303400c00f002240051482e0384000d50b42245580d010003130301d41048120881d4041c07000341d600e81d82c0d1035150090105e40511000008503010803c60004d001c0100500203c99446207444c0004080e0081544101c0c0500d6081140c6a9214a4180300e4140c100c015038484c600d040e841c1000b080c880007000b091450403802070082d00c801190f0b0620600102944030b10103800400142c0c1040748c07441c0405441e05042200c144814081a071210003200d00c40c040900384103c5c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 346866339 1250 346865089 346865131
    0x21e15011707050904060506010f09080d140c010204140411161101050f190207050603072a060c05030708010b04180e070305011505130c02060103150f050103080c06130803 75
    0x140002c1d40c0d000c00d400444040c100803c3c007420703500c5940641400d0380c803900c910141c82021107000c103090040c06019000300282c021102d01803102c080035011151026820058909900d84c22604154000380c441d0130043d0340701d0320f02c0c40d00748554406048040442810011504450824030300100c0000f00b8030071072000900b52583c05041515a00881c1110055075880d282c1d840720300180c4a00302d21409445810004105031070000107032403044005a4508012500d001d040008204c404031450b45c081e40d04042d0b030000310f0751502412216088903117845075641064a00106140d005a104403c14042400240a28584400384c00c20407880742001080c4400d28503541c5003408030307a9000810320740ca40110b6420001590507a00103e84040300c55410b1004641d02d10010740300c680750144010381140b401400000e40c105020220000200000628507145080b91000c5460130b070419280d0f00341c040b81d612100281001210f074414902d00c1d181c002100156100b01d03050002808005540d42100c5203602 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 346867589 1250 346866339 346866343
    0x90e03090d0812100914150114130311011101061202010e0103021225020105060d0308070c05030a080402040c0c12030209030a05100c0207050a0609180e0d021e150117 73
    0x90b10b45903c0001c40403070504004286550100744140c2200a06159040c103181c41e0344400305114141002c0c4146011001400443d000e00c81c0070b099003080ca10070f1015001c811900071a80000e188244940100413108500142c4005003440540380c1c1681404401e11030440780b1001c0c0307900360341e080c04d0000080300180016000790041c20184010700060004000d101361031040e18503642e440101a012000200e414203d00f40c0c1c90803110180c00210a040c1d103400288251842c9a0210440c504641c0070340003607503030604560000c40c5120002d102482440207600d0280b080000b0903a03c5c0c02c0030081c00c00180c0d240c00740080c1c1007070910300b4558040740e074450944003803109146a680c0041035504031220301c09070500600c1c6481c180c034014400e0a20100ba14208060344000f621076544036590078500d082c000c6003003604658281c00f0555110110722141c03a00400c118550100c00307801802c00c1c80c070600200b0001647e81c40c0580600d134420b00142001000ca40195419150401c811402c2d4840d0900e07014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 346868839 1250 346867589 346867597
    0x2d03090e0a0207021c1106070203120f2808010e040b0f090304050a120c0b040806041401021201060e01030e01060609051c0c030b0f0a05060112020a0e09010f0f090e03090d08 76
    0x80d41040c00c1201c007100241007440358062041c45908240b0150141d1021f0040c00e0144e400b000350144d00403034028090070603820161002c88104031b02d00380b034507a290004450b001460001403004d004840c800030192074110340590701400403140045010700e05900c4600044038094001c0d0400d281c03480205490040600c12240903000142c2840d0380d80c0e5a0300d150880e0548418019110584c1d003241c04200c1c6104002202e0440c0c0540f0014503503520346444070810602008039110056608205001d000900c041c0f088c0e0003445a0b440309031810800310000340a503400d81107042c2c05645044428042c03507800401800560b00260340b00c0480d1745000c20300e0800c840d9403082c0034021503e14100001004500489140700702281003101d4401d4a0310039000040c0e450030303181540803035001d2020030710110003a809407400c04038138980000362002c0340d800304090000c02e07000007246082c11901840b4900740001400c0c01044024020010072900441280c4c80f80a1061494072560803a444078060043c080192 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 346870089 1250 346868839 346868843
    0x91905100b130f050f010540060810150507030203041a0301030309080a1e0f0204110a020f0606060307032004061e020102120604020a0909092d03090e0a0207 69
    0x10300d60b00d441020040c410440d02e4841d5480c18040602d003c50300d41024480740d440690180c45450a10050102101925007402c116100ca111000390104050503a00424046d548500d606074081c45e040500041c4003203001005c0c1113590158071010011752001c1c254003001100035191094a4075031a00c1c1c101d08501c26503228180040c00d060251481c989000000c5040740d119845400c00280d50b4010325840d81c45104000e412040d1440d0410010305e40744480445051003256100b0903624281d0004080710300f448030170044060045900792000b0303010014504901c0c5032000521b51403414800040c0316100082040f4100b58582d1040802038442d4a1586c2c01c2108050145489541b281070040590340200307400380002c0c2416200d001e02c0750040c03007110025848214496101d41e104001d100195008400365003c2044035580000c075000c840c4a0300050300d201e0004184005d130300f14818201505200082ca896951035001900001d80001148080300c002d0310102104d640e481500c5002030081c4200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 346871339 1250 346870089 346870109
    0x60d0501030c050102070e01030308190f05090a0c08030408030d0b0f0a0e07030c050301080604032d0903060b0907170603010b060a0521160c0f0807080c0c09190510 72
    0xc810400340c0100001620b4080e806c64110b00d42e20403100141c05403e103c090081003503a404200d400d6140588002c21880040700802e4604003e07a5403000c45100300c1310503032030790040e41605c0104075000350b444008040e00d0004504040c2000fa0341f98484c13051607038001000d50744401580607501c07101624000ac120040a115040f030b030b41d603020b0813861002c03264940001e142c2035400d10b626004001741c03410f9a03d04402001030b0340d980d0780c00780c4800900c42880c40c80e11004680d0301410111101600740c40c425182d459520062031440c1050680340c10003034044c403500b210310030041c1c055072203002020841c98403014000141c5401e07010134010850342403840d80002d40056180840d542110050003011a0201d0b00c4d510192280120340c0c07134803016943e0741c0600020160074054544911518a80700340202d50300074001903150360310b0003c0d900c84c107001c40387c0c6007001c204240e070380c402804100c0e0828030582e801c07025840d0030061000b00c0d000e006003444c8466074442c003003180080d0454044005d0b10306880c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 346872589 1250 346871339 346871341
    0x60506210402120703230303100b0d0f0203100302030705040b010212130902030c090f0a0b09040c050d0204032108010303121d0f030903010c05190813080409090201030513110f060d05 80
    0xc00b106169040d41c90551044007801b014401940000704980c466040d0100110700c6078140f41c4a03508503031003103191221407910f90054200701d1200384010740c050120040000301d800c5ca1803047c107041c20a1a44000c3c800c514124001900ba600851280b4440651514003580c88051141850424129400c1080004e10100810003059000d60080034002421941030400020000422000500e140628252050203204000003818190080920728140b42801810240351070f9442d81260465070094504039201c00c58070340a202040c1c9880c00383c0c000d0380f4214013b50705540300601040e44140c04407201c555500c1c210385046105080a40f0082c01d03d009403a050114203403015036940060322818442c9d4a00030030f40c2e000314003410450340c0c41c0506230420900a10720620070f07110940010304420020070105c51400003d9070007030081c801b9000881c00060030400c80e0000404881c402000c0d08408000c01862402145e40209142d0181108a500d0800e1144100118401f4042c240c00044182d0800c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 346873839 1250 346872589 346872593
    0x9020102070b2a1615270302010f0228140604031d04180f05070e040c030b060d110d170d091a04080703080c040f03110301060506210402120703 63
    0x1664009620801040040e9007000c2d01c0c40352103108881c03031140c44020b003150401860100c0c2c41c0c0c0c0e0f28a11564208550807210044201d6682803100103009104c1b07200840500840da044640001f000010384020030f044d150410441200e40200669904e034080c108280208201c10b84c1d201c060201c6003103050b1041800c152034090420341d8010031402c14441c0e0320107600c01d00d003420b20031a4010358900071502402c0074181c460806201c40504c0070b40e42c034018000c000c0380d054900c1781c0c0140191320600c0c02c0c122031442c600f03000c040c280c40074192511a8007010b903000e000c2107030710944c280c55800803202002c03502c415203040124400708802030355907107401180c64600e01200c0e81c05003caaa01580c3c114801c85d10301050103611100171140145080341c00d020040100c0c1c8201241075000395140c010760b1800e0345550621030b81c0e444e142e000f25003c01000440890605080c0948030050400750f900718100400d0542d0381c828440a035510030700401040d80020203542d1002000504034840605a8800e640c80c0c2c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 346875089 1250 346873839 346873867
    0x130305070c03330b0a05040b060c06090d0e01020c060a050c071502030703020f0a0206030408031503060406020405040c0e10030b010309080a2a150504030201140f181f09020102070b 79
    0x1156040c100340f07101e4084000b0001d150240c3c0c0d10b1000e0050030080d9242c2803c0c00c020080850920140d0440300601c80d00001090030000d00d80130382ca014005181000006100605c2c030705c1000c44281c1103400100c61060706807104010b803146003c090504a0311400c50b013141c2d0745040b10540c00b640e600c250800361400402d402100821f43c01e0b000746d094443c0c0c0200b410301555031f030038800d000a4100c0001c1000401158a0300c01a540002490341c0a41c030106007100080d01d012001e90b025155240d00160820244c601440307101c0b01000103052604c40c0752180000502c2c0c5000c00c0c2c28040504d80c55400010b082c0e840b83d400b05940c1c680c880003940e140e03070366030200401c18020440704828000000104d00f50600c005110282220703802500300440f000882041005400060012410340d9241c803a061610003428140c11b102d40000080215541752080a1061004424a450442d41c210700c56032083c40c03444c816124168240f01202040000040c030040345082019803100c189204040b60340c118200038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 346876339 1250 346875089 346875143
    0x30213060908240601210c0e090a0c0206070e03010b0a030c09051003081e07141b0d1a040804180222050904060923010b030f0105130305070c03 63
    0x602d003112108292216030354600d98100400700d4a605121000907400d44c8100d500882d5004071000040b20181540c0c1d41321b051321091407040c8040362995030106018180381c40c81d80d500c500009014000802070180103502c542d0050811420845e851140100b5500d00b504025064940a00180b2a20380d82e4200440144034038011510468108400716601219403507050341034a400c02c0700c01d0300c0d2040b40c40b05203580c9005286020034829052159001168a00c4449020348501d100a40700504400c1c012046003004030b2481441850981c5580c4049410703040c0210a032030000e41c000c440d0740c40d1410040390600070766102803060400721a003000c030405680c0182c055502c04009007241006054401c88200300580500da03000829417000030013041c02900807041450040d040e4502031501001c82031720845000c910724650380c0d100c6901d0280b5050800001e880034500e0b100800c074a091440b19200200c03501c49000d4100040440d4490500c580002081d00555221040d94440742c051031080c005940 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 346877589 1250 346876339 346876349
    0x1e050a05090609070e1504060b070c08061029031e01060c0b0a0b01090b13050310050105060f07030332070c03020606010c060f09110a081c0309030302130609 69
    0x41460081a000d910000b01c4600441c2100e002d401c0c0c02d4100b04180300b00030001414040c5d292440e25024106403158428503000d0011369002558420b400e09250411031080d90021446a00450801c600001240f10348020340750070740303007044081890303951307000040c2e1140b0010b11404200000780580121540080c03814201080d0002c0d840360b1743c400d016552201c0407280a00710511940000741803098940c011100c00c0b4050400c00026034489131035111a030005054080204145a07040c4907901d420000c030900200d81401c00c2c801c540c1800080b4401e40603901c259600341c90040b8809003014025007040d094a01611004460600300c403404590260400040e0790708540c2e040d02113180c0f07a01c942c0c00085000d405da0028034560b1206801160f50b90000b000a5803065643c1c03001901d848800d02502d00f2280c0240004c52010448104108941400d0fa01c071050b40d41c030070b0002c8500040701c8000741d102d201c0c841c01e00083c8134206080c145c0203440380c0c0411300c1c4007030079610002c14856005070401041d18 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 346878839 1250 346877589 346877591
    0xf11030d0f0b0909010e06060111010e0a05010e070e0903070f030918020304060e150105100909091202070b160609030309050f060103061b02071401140a080114010816030f1e050a 78
    0x40c031313000b809900301d0b10700310301281035504440f0000d203055010310f008111a44541c8000581502b2007135003c1e043c00003694007140e469443d03056503001800d0401030702018081d0440c0203682814107409499407407050f004000c00c688485407da0b03080c1801094100c1c0103003042c200400d42c40c02c81e214000002e41c400c881c03ca900901c2d0001c510300d41400080c0d0840c0c04280c3e50001d594070f90030f10303007000380c60b6540803143c0c030400505500c040303038442c028068080864401c21444205405e986c81c00307400c00c4480e401000401200784200c1c41c00284034001c0f4560540c001300700140d8880340d4103044000d08801000540103108a080c1d00102caa00010340340c4c100e83c000c40c0100480c502859038002d24010540e828801684080001c0c488034085800c040c1c0300240506000145c40f221003051002608140401c001240001c80100081c4460144800008000746000b40340c0740f42c01c0c0303911005010301840d14420142d40d6128074200c1c407040e030b00810102d0151034140070340781c56500f0a0780180500300c550103074031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 346880089 1250 346878839 346878841
    0x290a0c02032404060b030c040213030b06090906041e1a070e09010b0403060e010209090907170d12021614030405010905100206011509030c18050f01060f11030d0f0b09 73
    0x280c120021030b00b20485a881c2d50030181d01d550b101d090180001c40134a0354035004265001030384c2c3e5a00d10042c1007181e03a606240700038903c3c50816400707040000301014002c115071401c104c40494045030059229601030380000c030001d00c010510f03846030007c800080c20f8803001c0c1d006a641440006000e440780695a41d5050500c0a4605008010303400303218250300381c1024442800061429080b1501d6181030301d00060030700d0502400609078407070955044400784c001450900c00c40a1100b0030006109592008064103e40710800801200700d0a4045848545c0401c0004580c540c20b50164005900039507454400c1e050340b40d6858032a031142c82540c2c04030703400301000221410a00600201d03080f40d5009440d4582c41c2a4480006481c41541041080304035034020001654200d5914080e02c9203c80010801c030200754200704840014113040d040c495082c00412450b030b40b1400b880726102e881c1c43d24940c00d402c62070320103285005204060340c045007030544245035012954001d00c61668100c07940341c5a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 346881339 1250 346880089 346880113
    0x60f1d030d081f060f0c170d0209030f03030402060a0807050c0a052a0306040b040c170606130b030d1202070605010b030a11030c0a1404150c030905100207290a0c0203 73
    0x883d0061160f000404c1c22081d01003a030500801e6100c03000c0740542c800d07076102407108003c5900c0340c2c800c410b00115107034003003400c00c1e0500b4204441559080c0750b0000314036500303003900015418085c494182c01013220311400224824840e034103442c40d140b1780c2400c89454500b54900309444000011741c0c40910011500b03a00c2490f922800882101c11010f4081c01c003a071a25110381c5043c4000030020782c0d2907041c07030304000b60030706403201c1c1000171800440213070519007040c00800c00b041d458031351502c0c8040e05184041c034030342d5404120388038111014140f0100600010b0202006400b4114001d42000e250100000e01000c4010040d07201c1e0300b00301d07030130819840c8142001c103443c003040d1444130858200b8000140c1c8c0d280141c000300540f00c4203407109030a0a954020509942c2c40345054400000c1000402d0001c1507005085000074042c11100400c2d0000380420080d42c3e4401d9100d0800c00d565180e85018055298441030502d01c0c0300222882d40d201e0082ca4054a800103111040b40240b04075015540b13 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 346882589 1250 346881339 346881391
    0x200a0e1305011112040b0615040602102313020328110a0b0d020304081e1e040815040804050a260309100f09210c0e01060f1d030d08 58
    0x680341308207215090701034880d600c1e0405d40190040c103a68000d1076007441c945001d4016009000248a5540142007000b500c0000a082e00d40708401e50503035007103940d000b10840e040340c00d006034491142c0e40003055041050002918040400d003006110101605250300c2c003c03000c211560156015490040f4600643c50034007603401e54520481d03090716014040a01000b45030b03001190003a008800103802c0101c0300c9a07804820000b0801900c4140c00010b2041006c1d01c3c2001c10010316484241d0541064680034109484500390f42c1040d0084e0042e800141c01c001845e030a80d000f0b05005000e01c01c042c0d480710440c3c1f03010b4001c500350504804011f0ba04080e607020000894540910240484022010400060311501307100c1584100384441e24001113401e0480031084104004046c86d0b2135001c054506080c421984160020304861401e41d0050054541010b801d255804251818500d03140e0400441c01c81c023480c0e0044d01c4d074940546034034038102d158031000c042d00448181e400300b03a2041080250070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 346883839 1250 346882589 346882597
    0x2a040b09071704050f1501090f090b1603020c0102040902040e0901052a1b06061305090307080c070906090906270b180a06060305060f04200a0e13050111 67
    0x1c00011080c0148641d00e9241080c4650040e104404070351a501c140d186283c14254000244d0a07150340d05001003042510f0381c000e6034554000d04004110b01a0706440d25000618014210164040314000c482e034010302c298110b800b80c420000085488a4840214a000c0d5210744907500740c26002c500440d181102c18032800d030040d01078001a01c04140608107520410030500c000043c0140d0a0058210818180c10043c2d03480002c0d01c0a0031541c581801082181e1004a02c0700306564908410001541c00000840b041035401c50100c071344813020b007148545400110340100c2d030001c0c1403803000108606150070480556100e60400d02141f08001d031a407001c00f811100600890030541c180074080765032040303981e0300305c9200300d40d10401c01e43c642040c41c9800c80320001102c0040e960740c02002489002d0202c540c001c044078154158a04194540841c00c01c0c481c1030030240030b18030803004503050b1384a800795402020000f45d010040c1c9032594400c8032100c007420341a9050350030000c2d101181c01c9403000300c1e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 346885089 1250 346883839 346883851
    0x10615140304061d01050f0f0c07110d0c080307080a090b0702031902011b050c09090606010c060c02330609070c03030b030a0203030304080418150905092a040b09 71
    0x249003150b4032070303c2d2180904000c0100144100da5024a4001e004080c000e961041c030040b20103032100e0920300c1d00041d81c100020700c01c01483d10184a014000748884d02c3e10000008111140d2800c6806070034080f00d4490243e01a0001d440005646401c200310040a00110162500c623551420f6840300d05a80900c42e045d0001c1d4140c200640b01c504503100400d6100206006240444480103180d03150510007014100079a1160b00c082c1c00c241103458211441e582c0300c0f80c0400540110700709903001070100196948000c10142d121058186800c0c42048024403512000030101201c40170384903034902c9408141416602d40c8405000200d56080640e5840c0c040e8203260340c0c200195440391006c130700038800b0402041d450300400c80381d44050303901000514022030007001e03015641c0b031402c0b040190310550113520440003400c10805440c05881c008082084410311100880c403940da00030302070b0402d14100854503200781c95541c80140c049680c4c5803007a4854044e101003007014510350420901c080c040b181 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 346886339 1250 346885089 346885127
    0x1c09051005030721051302040f02040303020601030b0403120204060503010612090b130219060f020d0801060e1509040504080d0f093503040f020901120b1f0f0305010615 74
    0x1040800d40b00303800241c03905182c5040c0140b003001d60402c9000360740056581c006d400036030b54403200541c41c042c41040c40344d1070b03522030440c50141746580180d20f0320814800944588400340c001400d250040d42400014a10701d07504556440d11000041e04a810030301841c000510350700700055003a511407049414407500a1190105952606945550520000800c0341c000800c81103c40988460f0504440508010388941d041c441c40f2500c000c0c40c118000c0040400c20200c00010443d4580000c1030711010841910a035800c1d0b18540c0200aa03131062421a80d0030a10300303802c0100380012680900080c049501061161b21082a115403d4901c6148040e080c0d05040c42c0e01040c00441d0401250107282c142d486e1642441e07540098403040e08201c0c1c0c25100c0402402c088030840c981a5010b134050504200920050b010b262100c07044840014103030070180c0705520000300d69039442c203000c80c01820141c0c481d5600c1d64881c90468068809032240c0c000c403001e104000302400e8003d01c0010745510007414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 346887589 1250 346886339 346886341
    0x60909151a09030102040f0e2a2a0d03060b04060e061b030d06090501090c0e0f010e0a0306060315050c070303110403020a030b0906061002032a1c0905100503 69
    0x11a410221030210341000703503084104010301058a084c0041d01c002c044245401c081d040c03401e07400c00e05c2403000810040303c0d141d140020480003001d205240303003001d28640d209515001c2c85031851622881c85140707999085078404840c000c540c0d00203621100c419182e5400d000290742d404c0005500d00440c000c00001c0b491150b43e00b60a403d00b00c1c094100000000d1b5130b0100c0110020000341981d0041034142c0c135194480109109294007401814010a07281c501001107000145004258000300c541c981c0c03140802440c03506240e8424803551b51000d40042c031f0250707115a2450598001c2030300d84000c580300c05400d40e9030b6140c1e03500341c4101c6105910081d011442c080d00e1750f40c200c004201c02c20b00303000c41820038440400580c4498409401862140c82c02648506010006a1902130020a0350b8400c0d04d544004042550f13010050781c0541220b10108075003242c2e03100b41004030940e81d101c02001c130302c21800101c80b2184002100d46140c1c400d42c507600041a111000d1080d0140241541008554200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 346888839 1250 346887589 346887599
    0x51f020c0c0f030a0b09100605030a02091504060306050c0711090f0718081b011206030c12050c060309030a1d0a150507021306061205091002031e010f06090915 70
    0x4400380b0765800c000c0c269209200310340c1c0c3e20b00c1c0e01001510403560039400802142c03641c0550303203d507a024081c210002c01c0219543e40c000f44a81600400d030f0f0031b0080206c464090a900d07560400703805103a00c0b440600c06440e0400c1ca11000790030500c0d05860004000c1a200803a081c080c5229005405400c0825034650f6001010354501d80507151040081703100b260b0014240a06000840608a0804108820200c141d0004088203480c1424250140c0f82031401c100042d5964048800c50740d000c5081c015074203c600744030303003804101020903410000002c01c100b6904000b0004020381c0c603180d16400c3c00942c07000040044109264036a40c0c00501d0440188801c3c0c0300000b0b02e24000302130785003007071400300e040c2d020a40d6600605444c0a9098480e4010321446802c201d0a103d07044626404000701c1c501038084a46c3c4e40024002038030340c0d5500001041c04981d20700c0134844000c4c0410115441965542030741031058080e4415500000c81080c0080790151180c051029044088070403180558141 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 346890089 1250 346888839 346888849
    0x40e0610110d20191401060305010603060501050405010626150d0c060807050702010903120e0603090c090c07030e0f0f0a2402030a05030a1e09051f020c0c 68
    0xe00040c00804400744150100c1000b4a01503400c469440400081d0036000e403400c2c1c4088241d03501015040000186410213100083c200407a410410410780700304054103081c0101030541011340704d5420042c010090113076a4006a04840c2c00352410080c5a82c0c0b981e085400907000410030341d0304071407403184044000b2034903c03103170304040040c540c0822040c0d40400146d000000340c20031510500719050400a845d0401031841c3d1080c0c2d2170400500d000c3d032030740c0000e2000041b030200a200c3c2d002303c070040b03070054404d0200081d4040301038541a82ca0400001150b9501e1802e00603e01c504075060009075022128416240c105a05487d41c66000010808200e003821503803014070f801850f4600260341c0c5545610a480041100300c8500c00301041c801c1780c4072080c5400d060341405540c020451280b1461740042143e90080090300e0008505989038078840c00300c000c0c00501c11189003400c0c0020180300002c2001450f40c1d1811101034045070301207001800b640a10030308400c240d041030903071010f10b0400c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 346891339 1250 346890089 346890109
    0x5040201020a0308060f1f030c020d050702010822051c02030a14030721060608090307020a0303050c0c27180705040b030a12020604031202041a1c050921040e06 70
    0x91181c0341a0202c240032600d4200c140303111641d18802000d600000c01e808d031050301014403845c4003900704201103910280c682d204061000b410003151500203401c1c09038640564409a542d4103869440302c0e0300c1d0074956039440c00b0080c1c0001200516150550321030000084800462190321111b01e60301040d0f42110081e000146544140001c03000f0f8926003c07060041040d4480300036a00040340ba003031907030040812034000c0849409910403c88e240241e503c04180c1f000312685440d0003a95000072620b62418112941e90064005490200c2c1700400812000c81507429460090344030043e070b490b10f50103102c21940031b143d005aa004894140518285a04a80b030500b6020f012100060200d503101d2420b400c0701c1c0e40303210058110718188070415a000d000160020410102507045c5401c021001c0000a190030440d40e905a00050841c104124240b07000b600040c0ca000421a600d8209011b90b2a00030018800c010402002841c1011781d48800a64090320500009598503031358502c284400380349 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 346892589 1250 346891339 346891351
    0x9060e01080105060d0f1d0712170717040b031e100302060906040f15080603030a020303060d1505070201060e06180a05070302070507060906020d0509030a0f0212030a0305060f030105040201020a0308 87
    0x2486004d1080e841c0d646c1c0c040c441240c117100303100d0340c40c0841c40c0842c1802d082320358000c40807041d0701c00e032031601003001c00410032083d0095420b80f80d40d0704031514106404c080c072580f00f40d110701008600001ca1186001c0694450088581c15407882c2048514a00e801c0b60116050070850303071049014805802c12102030a01c00300040c0c08946016200c000750302c00c0d01250b600000010144940070200d199001b03001c181c011105400840c1008840e0001a48a0000900d440c1c040c4514440070340512140800e0300d60b43c1a0006d804000900344010004d01130095070244034441104c10300850301604000700c0707013001b8150f04800301c0701c81e0b01e6015646c006000090a0300c2c081540034000040410790a1000310014206503c443d43d0321403804402908148890405209010060059070010784010031080c104540c400401c01d00401c1520014820100c2070242020901c40031a042d8500e9070980e00560140c4401c48100305449104001c06080c0c03003080700c00a0050f000420000c00190088107802e4010b2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 346893839 1250 346892589 346892591
    0x14040203060a11130915050f0d08090105040b030f24060a05031003060c0206090c090402060a05070614161202030709120309150f121104050d0c090e0d09060e01080105060d 75
    0x2142d04100340502413484c1c1110b402181d442160a03805e101d41c220000081109440c0d0b074003e0000200002d83d20700b03110030060094100007a00a0032a0310820407103020300f031656800c41d00c0782880045280c06680880f44180011900b614805602d440c0c041d1030310030113100900c002d251442e440402c503500d0300041c000140c400c1001c4004400509103005010202101d513009168902d00002540d00c0d29601d40a031a000d80e0f5080240030240c0c40f0301040750201c40e400e007001c42e620700f11454142d0090411041c02a4244510018058000310880119405031920b40d00c038140403c070b00508204034031082d147c0d08007241d11040d040105484c204802c0c402180241818039040340d0b02c0c6030340150306090180550004104d40107201d0520341182c452440004011010407039010305c64014921803046000d042d1041010080381c00c1081450150b010291281c203d0510a40300ca000c03a0a64841d00c4180300000305004d41808107040b803042d02c1295884105941d41921079180c641448560fa10503440d0302011 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 346895089 1250 346893839 346893847
    0x903180a0308040303110d080709050609010c060f05090d050c1c0207121a010b0a0c03050306060714030a020c1903030e0d0615030302010f150b0f0403050f0309030114040203060a11 79
    0x229080b1005040258001d13110031442c0c400d03640d507290900d401c0150b1a418031800100b4030101990100c038210540c3c00540b29982d40c1c031410f0005139020011000010f107060308200000b6404441c035004503004205400c121040001c09640030b942502940f04c1241a55004820481c5558440881c0d220303680f5072070055888264898520800d44203407a001640c1d13070244003c900300310f010180c12481c010100b181603942442c0004100402690000d64003504004002c808600e0030740e1050100c0e1100c0d41e010180c002607800825446869411900d007030005401175105410744d50a00c01d00001d82d0080c040781782c0c0511030841d9011f0b2445101d1901d241d8002030b80c0b9010070b0004120f0711408601d400c1d00090118018079501d0000d00f500d00c0c607268a407402c0e0030290340c002e481c08003412802c199001d00f101e0f5a101e0f400a2201d4580e03000d203600180c21032007101c034410102c0c180400206241ca005400034800034039011640b10340c0c02c0040e41d000b0b41503400b00001403201130455101c4810055584542c91178 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 346896339 1250 346895089 346895093
    0x2030c0d170904060323070f060f030e07050a0f03060501090209220207020d0501050f06060c070501030e01020702060f03012309060405090708010e0c090f150105070303020f0f0706050a050903180a03 87
    0x4240c418001c4076081c0840300010544206c4100031060003409178a04d034607142420800001c002440808201c41455110030a0442154090041350060180074203680071583c0d41301c0344808501014401510198035103c004a03e0050314000c481d120341015200d40000d08402ca2082c2c80b02d900242502103c0e9400d016580050707803642500c40660340214000f24a81c10242c0714072803141e10180540d40700c2c807003c002d9841f03010b0000c40c40da400c5640034200002c04a009902080c064410340703800a40c4400d00190010300007006101035070680300500a03415280805000b54096a11140040d0303602c0249600068224601504517951001000707081c1d0f00820781d5400d10381d00f580d21400c0100d0158201e4a00301c05d141c01c040c0d42c07840d8400100b1071082024100850420028005c1400f007a041000c0010704006040c0a5011a00000740d0455075564504102819404542265104660007400c06000c035580340100c1c001c16000d003010300091454041c003009002d00d440e14100045800141003400040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 346897589 1250 346896339 346896353
    0x130204060f080c030c010210111603050a08090c0a03020f060c0f0303011502210f0c030406021f020703020705130b0d14010606020a0309060c111c02030c0d1709040603 73
    0x2004020007442941001d0811014606044800301501d00035800707003d44a0260b03a0008522507040703100540010503c00d8101c14200c0352080f4200300140c90540728446003010750060040039820b540366500e82e0141c517039170b9500d40c86065400d00141d0200850b0421300251900c1c840280d60260000c0c0428a86000008c10504003047d02000e01c68130740001c070040086e08d07900030f0404050308451014140e05807035844a0400444c10480e2810310800c0071501d1414404030608031407000130300d0703411203403244c3c1e0300c41d40203642d40c0303210528151014542d040c4581c844514020356000c030b603243c6c0143c95141c0c184010b2010b0302c0700c0f6210596041742c0782c0e207500300f02d515843e07981e007806d43c0103a41e0030b1424092240160300390303008d5a104000315805100c158010a03806070100003611002d10340030414079001e0034860340c44480d0505c1642d1100d800026000401e0041c1c12a040d01d6109078103940114108034100110303003880d01d9001e04490241080c035070300c08038801c000f0b110554000b031000428036103a80b0703105 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 346898839 1250 346897589 346897601
    0xc0f0d0225060b01030c050f0403080903030c03070f170a20070f0320030f030a080712050f04020907180902070510060303050309010f110d02070f08270306011d130204 73
    0x90703040c50f91004140300c1960700d07004460740004141407041c9000b2503501017050b036200302e02c800742010102154264166030184212040c0c104a1411241c980c2c80508002001d641580001c442c0c1c48490000a0004100c2c1401c0c2d6107484550307103c65a404d01240d102c0003c0040210200260780035904001c11810182c40a84020714007915003903101c61070005c00c8880000400c040c90740700e6403100306c802040d100c001046031440511031070484d0702c680b01c40310f069400e5011070110115060400742001b8021907000411b903c16402140c501480e620381d4041551b0b404150805c0c0885090414070502208030641c000780360040c8114103c614410022840d0411034155400880000c0c00000501c22410b109005242560b030010200b0400001040310702000784c4200310390600c080c0d402103540d00900c01c1d85082c195640b070b003110740150340340c0c1c3c0ca100e030070301104038507103018030503c500c04966a00d81800101d4605071035801f100f400300f90203125404039030024003c1010010b8417014541800503182e9000701c0e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 346900089 1250 346898839 346898843
    0x50a0209010602030d0506120601210206040e0601031a0307120503040e01060e030708030306030c01080a090212010c0f09180207050304180903030b09071d0109091109090c0f0d0225 79
    0x1355880e900c10961110944201414441c0b0595005071024215440414002d0464020846103070f00000c408903034080e0031500c0b01d8080d40c811004540000e484401c00311851141e9800d036020007807443c00164501e2101902406250154070003a02031196100c00c055015490b4002c1c0c044030300f0140d50f040115400d076400d0300000700140c2c15003404fc2e85410300f00700d07039806881c49401550441ca040c2d408669074134881d2116034100100c803000f10304803090340d6000500594010313100920b1240a046035078040c1624203079071000220702c80320440780b02e8400c003903080503540e040da82d101103040f885042c1c9001e034000040039540703070004100c006a100c44448078400c8040e410407000c55a84410304000d0210350b11140140e0160000c2c1042044403644440030309070050700c402e201c0c112903820354012106080640c1080801615040103c001d482c0e0600280c131740341004540c41c1d101540d803401e00c80640d0291284105c8880814004012600c159802810383c1d900300060381400000000c14200a0613848401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 346901339 1250 346900089 346900093
    0x806012a0b010e0103120c0c090f05061c08040b09180906011e0e16050c0709050402031009031440090501060c0803060d061b02070e04020607030804050a0209010602 72
    0x144040140301d03801580104070a0040888075859501ca0103084840b1580e0300d41000f04038402801009004500d050140c80c2414040107030326150042d03100102419141e00748100740030240b280c0c000d4081000800d0f1282c3c425107460506103451007460440c0c000c0b604195010a08621443c20041b40c051800d00c5000020000e0169514102816003c6c013084800402c428100020601c50401da908020750050028030b03c025030b43d13100d40421545800794a0044109001e902d1002072048025000309010703900071002e6921000b00310180d882104c82c15040100441ea022070b00030420f60b9401d025000d1340d90010128140001401d902e1001080102100042808010356044c0c0e20712048443c00090b00910340204540d504001c0058440109500020070324240000041e0050726480588101180c0c000c60900090074902c444182c414000b030081ca0041c0705265000504002c0700c100780e400349402502d000d142a40c5501c086400d240010030a803810311404c0d48400041e140d600c0b100f4000c01013640 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 346902589 1250 346901339 346901417
    0x7120b0f0103091509050604060b011b0209090106030503030702031c0b010212180907110d11030306060f040e01030f1202010510050f030309030d0206010602070803031608061302040e01030605010b12010303080601 93
    0x2805000f103640c4900914100001c2d44833200c00702e403003c010503002c150121400420b0786d54044845000d80070a4200500320b000110a1191141d0004081c0c4650200740c1d080b120180e0707100c03881c0c5c011201d00316491401a03008c8603ca00c61064140001d2140c0c003801c01048818540c51000300d00940c030b0540f500740c0000d035180d03240380c0010f0341403040000074003452400390310450315404850340e2800042d004501c11080015001d0a0400d0744045030020100c0003401030481d81d40342012003000d0b8000c2c0d401d585864200b00003035031151040c0b054900c075500340c42849016034103180c2489800e408011260b60076200820107000d65503000c10003000c541c0c141d940100042d41c180a8020300780002507001e490640d00a2041c040801c00d241c000d440c82c154245441040d6a44d24800900e03510801094024070702d1001401189040c117a0040178160380c0600d40520450343c0c0e400514a0500c681c4800304540e41c8000e0040c00000d1245e58200c0e0000014034011804203d07200220851003049410f03060890f281d09 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 346903839 1250 346902589 346902593
    0x5070207090e0a0201020705120a020319020301051b0d0c030908030a0b0a08280614010602070f12120c030509040e010212060d081b1002030106020607120b0f0103091509050604 77
    0x2c040e01c014006004003901200d030715640043d58400d03150090728460981130041c0380303810a0400002141d00e030001c2c111203611036402c20140400242e0601a40613500781000a440d014040c101604c032040d07950500c515201d1b4214000000b004e03405a1303c020142c4400d1517034042648031002d54005e00d04a13100040303200da0385007040034081040d0300c502c0583d002514480301603111910310241c0c02c540912441c1810480f0b04c2d2900040c074412819039810040d450011072910b40c00100c0340140c03121460301c003220a803507203a13074030480300a0707080202840280d555034503000b0300c95089800032038485d0030010f080c1403c140000c0c09451702c060184045a60205107031814600c02c503c0f1540010041c0c030b59032503210b0140ca41b5045445001254044ca903680082c9900e5401b0421141c000c0c240145411500ca5842d600c00035107a030401d40e0742c0b40024840700d101110b0319035a4031844a2880c801081d84006000350001500a400160707419224000004443d01198005002c0d541020b03103d400940028036041c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 346905089 1250 346903839 346903841
    0x106080a06090513020103151a0c15100506220b0d0b06130e2503021909150f051908010e0a050606030112050a0c171015090b130507020709 61
    0x5584864a00b40c1440d003400203007000c0403c43d441250302840c5c0410700b10400a0301e080c51030381c42c1e0710806848480e41510710140c1c11010151402001c0c190079681d01070382c503448030002603e00746c45c605894a40e1900c02c0080740b030508000c2c5104050030070b900c900e074003044060113841d000c0c941c0450401500003401e6917101d5042d2082d000001c9003150300600f0001401c2072083e1142d828001c4000c070034441004211124072041e510800066400071071907510031090001400f030741100c1d110450400d406040d800302e03903005020242c1594000c010b121260094002c00301d401004032a80141800340030007a603241040c180214a00b0080c0c10380391000c0035450726125216524004081c0d41b280c6103002c051120380d170b9a0f035003140e045500c00007945800c0541380c14407e081000b130503001042c030200c0da0000100c01e0300300080d440701c0f5518034050724070450078046101c050380c40c4146039500800000c042402003128680c8802c03030282d000307010740d00c60388002d900c1d64003140c01c03d88a480160b4070610040000c0079003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 346906339 1250 346905089 346905101
    0x2030408161202010e030a12090f05010c051507090b1303050f191b050d0606061214040b04050c030607050d0f0204120b040212011406090610141e030106080a 69
    0x110392840342007928214803804225603484009040044407000d0004559080200c1603145421101246203482ca2a0340642000f03681c0c4101c400400883c4d41c0040d240d070040d14001300181c0c2010291400c5c6100e9104c00c0381040d001403041c0103100c5013030800301c0c1003140c044c00f402403128014414082d075404d504216141c0342da40c440411041d80302c1950076001280044442c80300940c40b010440302d4042c41d20401000c1d4919070001a000184049004103010040d0442c0045440503150302c3d80003681071002d40709440120300e024a1440890000c580007401400c000d0358010300030815164201134100020b4100101511b245d80025070100d000c501d0f6164a103d440b140300c8000c034085250130f19000c0c00c964110703100e0070f016011265480000d07080d9219117400d0004840748100030031030003040000a064122083c0c8055000307450307140004d02581402000c08841503000e450710000d161071100450b005034812105250892880d0340d510964440400c05940a01500e4035400590f2070002030362012684 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 346907589 1250 346906339 346906363
    0x51c061a03091b03030a05070302010f1e0c02190f020f0d05060a060506130308090109031b030501060e0c04050603090111030f01031104061a090102010e03131a04060206161205010602030408 83
    0xe000f1204009950b400003ca0701304032030508040740c40e0f5135070342801c0e401040d00c924200030450404031540d180e507100b0070300b003109200c1c0030100b0051481c618604a03036450042401d842420800d42e2046c000c10351060304101705501c0144000003000c1d80030085420b1580301d0b44111a00d60110051003408900340c041d541c0a010140ca4041c00d040303c4a80d81e8046200760710010f040100000b03200280c5e41d02c904641c00c0955044000c1d030f2040c000c40c054850070040a1b210541e02940b928001107a18440810f0060094991402c503504003400d0808000311940044e0183c0b40f40d660710080c00c2001c0e070b030702c2c0f01071481591950300c0403010391314504001c16230000c40b81e49503115900d0180c0c00e0040002060b10f0021040309110b10a8480b4040c20040c3d0040011400c40001c5100100d2240c49092040c1c1c0c0e4601a140720341d240c80150300032030b80c0515560040b4014800540c004800081140f040141050325040c4070786006903024064a8816044074002c1e049000141c00020b0217205598041052800c849 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 346908839 1250 346907589 346907623
    0x2403020a0b0a0e04020a11060103051f110f0a020304030c120303050105030a032703020414090d11030a0806040906020d1a19030b07020109170a12050601051c061a0309 73
    0x2a440440041165011241180c400c07070740456500505482910740d0f04c0c00c4840c1d03030112091540c40341080399860f08032404010920700ccd0800c42c1065050b6034041d50b45880114010b0034140041450051096080340350343e01d0441c07005000020116140c901808010154070440390a640d10343d003001016294160171080c00380e0302040d40240002d900150440c8090030042115010341910380c0e60040c3c0545030750019501a0604202c420700740c2800210034000c140d0b18084410310200818140d4a074020810a280c00b500180091707061503000c0d030106540300300c000384002040030b41c60359840c040342c100b2800d0b449142e523112480c568900d54100350542c0d84100b200c2145c1c0d4180c0031810b80601d160039020041c55829854086000a1f0003500003c0296a011514050b034100040500f10710b50408100d2400064004040340000342c441d12500d4003420040e91410700c4d010751102e0a980e004400f0004101c0981e845034006000c0b642059000000002041341513070300c0c10902010342c940780c0000a403410341 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 346910089 1250 346908839 346908847
    0x60c15141e10120f030201020408150a0b0d02031b030c100809010b1e040b0607020d2009010e07081e1501120c0203030112030306080715110606010f122403020a0b 71
    0x601943e82088030341d92010320320140c100d00b8036041340039001e141e00c00c401d24417580c00b01620b199000401580b00302d4110b00100315500c41c210130010032640300840a5010b81025001840b61740220711008841c441c094100c810a54654020529800d0042d503220001004c510511108560a020b9400003801c00c031110311090405131044550f482200484503c181c0e9140c4460b061038903468181c03542c55400624000d55000d25080003d158045000050048640200c003c00703c0c0c5482154641030300e4a034105640a5505c81e40180d880f0300c00a80a42d1150311800c02c001e5144100f6140c0a114010040041e03601120250000d84406c1410300501e0049041c440d84864065000045c0d90440b0020b0050b0040d50060f810103500910460b008108640145400460b41c0500e80040d1944804c281d80ca05205001d0320440e00c0e180c0c002544e509001800300e403502c544441c03140c0740c0000888a07408002038407000d04e550884406c4254103510841440c219804c0081d4606904584020824900c81c1460 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 346911339 1250 346910089 346910099
    0x24090601050a0c1703040605041211071205030c10020d0e0109051b0a0909050a030813020a2c01080f010b09041a040807020d14010b030106060c15141e10 67
    0x141c1e0154050035010050420500024403680445002c01001c8111107503a4900b0503062500c007500d800c0300d007030b544d02d00e1600059003000d204840e400f81c6803903080b018068540c10244140c00b100c1c0410401e41d040c1c803042c000e0b00c00d8103a051141c1c00d42c03407005c09401a0340d070b24036130404015150103042c51281d691502c6000800b00e00e0220340145d15200000d00070404101b000c00040710801d085d0000c5501d1490a000c9408108000a885010501946408646d5559100481340305440d80000a41090b06a42d040203064000000d60020303034081c9040b61070714022800b40031450130090303006002c41d50140c0940001400280705540e84d84d04141e070380307018030310345501c5411101d42000480713103102061100190a12800c04113507001268020b040f1207010045007003580100c03407400440b1207294a440c1e102041807405204a10446400c1c2d1501217107031141d500e43c0b018004070003c10300c010940b140b02e9070030a00000400a481140b0b140321480310400c002c0070904009074000c0402c200c182c0e02007010300c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 346912589 1250 346911339 346911347
    0x6030605180d050906040b25051015141509040c170603030301061710051c0606051903240c02030406030c0503060105040b0c0705100507060e0714011209050624090601 73
    0x15030310007a8078240d5030f0302407840041c40c48d0000e020709200502c03e0800181000b1000c84c0c0e10b04409880b804c00c1c86900d80c408807002001c11240300f0b4800e01d10700842d5110359420110041000b5000000700181000003800101d0141c40c080312605000491550342c041c00300c0c100c2c840c3c10782c110320140d004504540c100980a00500e20203184101d202150b8130005112503410040200681409050030005503400208034020000c0e0280c125802e5040003130101d01ca02784407509a444468105088180718919162200101c44070020070b40c09421454801c00489498001d0140500050380115521031402d00001c048407403065995040002c10424048541c2e80078050f10140d82100202c82e50b24110841d40e14601034203907000d1074000404500c0e1103400e58210010b030403254000c4038213120b1005015a00303520341e141c07409145c3c00e8001300000204503522946681000e100d940000158a00d101d84907a4507200044031010f62015043c100d070744440c006004402c2c1c4500c81600c010515042c641c002030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 346913839 1250 346912589 346912597
    0xf091f081b0705030403080901030f271506121209260f010f0501050a1703070609021302030405010903030b01020d0f0f21061d04030504031506030605180d050906 71
    0x1030500c010840312903049500d42002c0b60304095000b0100c0740d9603070380c81c5010031842d0416419075001c00c0c03030804c0e81015481c2c0e0380201120104507551003410a000c3c104504a038030f81d081d40945000c1d070301002e00c80d401e520303511a5401902c40080700b01141c00303280c54540e001d606e660b10b61000b0810020b108021800c0d076050022011300402c034042886483c1a1216450030f6503d2907050713881d40c00e0a60720084548607900c00c0b416114181c8044a80f203484207580100a1a9201c2c04c0240394400c00102c40401c000707510401b0000d2000b44000d03400280e212202d4242d03003003a2029181655030b02c0856081582510520300e00c000c00b17001416010410880c043d20103803040c42000300344045d10580c0c0b2040c2d48170b080740d0050040d401451440a4680708421801440240910b0490340024642104002c580f10340349442554161f0710f29142504640c2c420041840c010340381031003903454050220005d0039900815209144034400404516203400d405031501200e082c0310001e20804111b542482e8842d9403c031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 346915089 1250 346913839 346913851
    0x3020a0e04020913260d0c030605090a2a050903070303090e0a05010803030610021606170711030a1206030f030e0a0501030605010c0b151c0606060315050112110f091f08 74
    0x11500f80c0c1c880c1d05c518510741c416101d0f0540160301d480304d140385064060348840c05403a0b0640d0882c0e40d554840ca2210f0442c0c41800185c0078880c005c3c0c40102e086030b45010380304610005031505074100f9020398042440c02003540c1044000c541c07600c0c02404072170700411545d0391103082c01000380040d51506082e5501c81c81301904d01800345111040d01c000d1a4000c0048000c51110000103641b00c941d46ea10041881881550310010100800d020983c0395200c2c4650140307201d03001010318a0110018020356031110f10720503c1c1d40303e584688000003c5100011480c0916000381c480064940007107041000b664110b0300510f040c18500302052289076131000c503040d070196001000803c02d480c0c425122901d16040600e442e80154a0001150f09222003a0350390450740c4100b0b001d0054588030307201601513170302e441100d180c030f0441d011041216602c240d03090702d15030051850002c0d00f60460103500e4219400750307007501031014001030410b680742440b90b03120001c03546c5035400080b060764294006145c6000a801 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 346916339 1250 346915089 346915133
    0x6010e0f0c130e07140409090201020f0f07260102040f0602150412030f020d09050129010e09070e0a030c0512010527030408150106170702060c031003020a0e04020913 73
    0x7808080c0111101200b180c000501795440d1030f500c00c079140240944220880c014080c1c2c81100c6a1601b00044a01c042044030340600b2174103050950383d08074000800841d07581648600c45d4405111400e20080016102410358a0146400c059000e460000c90820100340c4103172190070040412035032030070240030110f503203408212032042c010068041c0c001d411411031000c4c035103d0801c04110056110820202041119403a010440480340754000048208640450020341501c491b034508813260030b51141c1c0e01e040040c050340d5101d000c0b42d060045a0000c60313109a0000301803040303142555220304500b030150000c0c407113841c110055444c00f0400030091013510340d00180700d0307501410610960b006403030660200d48040c540003c81d190040401e20800d40401e007501a070152032402c0665040c8251202d80042c002d41d00d5016003501c0742d5000030314800a01c2c0c2d1101b80440186d079050000401810503594011160a007401003040541010700082e01c0c2021704640701001641d5100c0c0c1caa400e41c04180 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 346917589 1250 346916339 346916341
    0x91d0109050903071a10050a06140921100608031c0c03020408060a090c05010302070816140a06050a0c0201150306050c07150e0706020d0203270306010e0f0c130e 71
    0x80c2c20780b039805080340050541002c0703000c902505d0104c4d011141300d240081c152060700b90f60f440900020701388c180501c1c80041c640c140c00580505005000340b88402e40945002161a201800103c442a82c402c61500ca0f400c544c41109540c0114041c800142c0300c1d11001d145041005018030118001400361080499191521280c0d118001c0d419607000b0009003007903410a01d0104810402071a851804a07000040803a021400b94428402d44010589c400e03241c1d03180c00341106d052004c403c5107500c200e03280c4441c4030902c040139109015242d26503104d42d00c080b4460612650701000e550030032170302804580c500003c5003030301c02e00101d08104994100d140081c2544606e042051140b0900c00003403c0c240c01c0b102d8050140c070b5182c2c002078440c154413003a940740300e4850404a8607658107030031340c0300140d000344001030034840015407161041c0c0705a00e42d20740c00c008003408a8140b03413091b80701668211040702000300110600040301e0b480181c4030800b9140044032200214860214024031b081090040 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 346918839 1250 346917589 346917601
    0x406030605090c100f140f031303030c0e0d300c0302150903040506030c040e0c0415080705040b130302030d050903120f030403080a1d10180506060904020d081207091d010905 76
    0x417007201c047c210580b03001039503403800658804140386c40003012000680b50080c0c171459584145080821103000070200c4800500325119890342400c0001810481c0319441c1711052162010b8400c0e0444d6011a02c1d941203181042c100a401c0c0717241460040203c6612208011844202008507415960102c80b6991262914059080c49010703075004403040301c00034014800d910f88018054030031070303c000c8054a10040701c4070080714000410b440e64008104184010300003404000c001d020114000c810101e002c80c2c2c1c0e50002031400c1c001005070b1021079000194a0302c00e04080c0416460000e0140169150461420080240384030051002c2c0c1040b20b484007103442c0001c49d0308980c507e41303506080c2c010000c84c04c1c2c800075103a13103519100c0e030170031403421107a1410b0244a45d601d40c3d441d60810042c0c480c594a00f4280010600020000c903444040120608001410304014100c00c6180d51052103240c604010090491081341d0840d246c0711841c01b0314580540c8a0b6510607041d1489041c02091a840300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 346920089 1250 346918839 346918877
    0x1706060901030308181921120b03010905011109040c051e03040309080307150509191103011d0a0309210f0510060602030306090c04030503030c1303020406030605090c100f 75
    0x1103111042900540080040d8001b09016448481c5e01403940d801c11598030902c0740140d04005010074000c164079141043e441c0c4800e900000040e00090004105440d8550302c0c40c5c21100106100862848041a410454205071156404100c1c180c100280703000e040f0300c0640c0d4100354007901641e60740c100100040070180f144003420024000e000843e51141e00d1898104060558000005512441c010024410000020340b4809151015199510686d2241c07900c510703040160a01640564035004020a03c040a1003404065884e04020340582d00242c0340040100d041540240c0d101a540b440c9610b4a66881e001450400d5011004401c1079085113451400e010403045044100c0740b8140000800c1a0080006c510400c000c480344481c640e10f810a0710f03124045da000c054007940c011f10003d0856890f2000608100510194129515540c0d500140c01c1d501c15070021a102d640b41c0c804c0c09502001040b9200c0c0003c0704881c0e0303200d03500a4190040504030314900720410481c941d40b0308002d441903 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 346921339 1250 346920089 346920121
    0x210705040e100b0f0733021806030c071707021c060b040e101506021c09030611070303050a0605060910110d02060405060a0504170327071706060901030308 68
    0x5044216501d42402c130307103400c1c40c681280701c06403043c0c1c00b0040a019480000c0302d03072030a40b00ca46d80740c45401c4240018000002d410010110070b003218100c1c209840c50b0f80340e0000c0c4d4400d1002905041d034030125480c00c22402034000c446a04076050510625005130382d1501c511050f40b01c403138101c0c1c1c240041410400c002d8404a2612a0058900381001543d05800310310000301803d441d50500c10141030401500c84203a241c8640c400682003c100c4200d000740f01c030030044070a40c56142a02801d5200c1e240e070800c54100ca140000c82840000307580b0101601402450342c80801e0b100b0410509142c02c01040d101e204e00c44841c2e20811a81c16000411030281e117008200040c40012240801440f8002030343d13076142900c054846100c0c80d00050070f1940640038407442a0303803082074040060000400c80b1060782002e481a0480d0040d003c80391181048141ca580e001748002d4000c00d2002d2500784050f8004448581010b00e0b50407140802401c2c0c0c40e0034039007a04481d0f01d4074003618a659480b00e81c40040c42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 346922589 1250 346921339 346921349
    0x103030e0f0d061a0a03050312091203070914010e0f12100203090303061804110409170a09090606030603020102210f04080c010813050c1221210705040e10 68
    0x20200341c80200380103d6510800d240c000003041584160080300c1008644440751200800c280c0c0f0410800a800c80541d039415000612234049070f840100b14034a15510f03820481d00040011070203502000100024011121246401c0c207011400c0300840f40071403401c0c0180140c0a002d070024072800e0b08001410810102e0340c4040400443d02c0b42002ca550325100d5006440b82031041010212408219035180400c0340100d43c442c0f03c043e002115502408040c05d04054141d8013807040e80380e2180394604550052180486655500b005a402c00444000720307081604000101883e0000500050742c002549400b520110305080e00c0b440c2c2421000c1100c0e00c41c4900072504880c000c50001f49003900024154220794007620349001c0350317981546941071a44d100c04054042d0384004020380c59400c0c6460a40c14138418401590b1440340448548240e144810840c1c040c66400040c00f8402c403058080e400c4002d0054184581a90408920091141c05a8004d540b02d44041c2004140801d82020b280e5000708 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 346923839 1250 346922589 346922599
    0xe070e0c12071b051c08010b1606181a0c0f1803100c0503010602060f0c0f0307140c0d020f0f1203070c02030706080a0506030705010504090c0c051c14120103030e0f 72
    0x1000e4030b0107a845609004201a81c0c1160304100217200d806001c43e5816100c014030742e01c0c01c000c1104420b40903803030390313003800d840f02560351900b20190203045066080c124001d025590702456a010340554112009100d00b08201051200104040b9010201e5045859500410998508078000682807046c01e0503110300c200d2604015490b0503410a014604944035902620850790b142c01c680400d000c000c41c0c1100b070000b001c0180c41f22302a985409103812000d0341c9010700c0604402c01180a1035482346c0390b182641d501c804618000140d041080900e40c0304490301401105100c051301564405006402c08583c0d0307000300009500e188940c549010954000b0111407001e661b801000c0e041040c00d030b5804200a00b0200003c0e924100040d040041b1141070351440e290500d40302852000b00058140d41d001c10815216920104000300702042216a1100407000941003403036020341002031101c0201107104c014803d40c034404454191f40350440b034141c02c00f068041038035000a2411002d05640981c80 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 346925089 1250 346923839 346923887
    0x70e06060a17091501080a0302070302040f1e0b04180503031b0c03130e07030e0d1d12030a110a0c0621020d0c1209020307121a07030e070e0c1207 64
    0x143c0000220f002c0c6580400a6030000da980760710009032074190390a000780140c0d100942c00c000500782a03000310400b00e50300700002000c3d45158545d4241d620210356480d4400e403100c0c68684c080c5014407811703540780d18600315001c4100e500ea483c2500d0707000007050101442c1c80341c2550240703218081d0846440e183c0a0054035600c0f03403d42101ea040c40b810380588503010511100283c1c51500034440c034052040c92400074000345025481c102e032803072070740b40c10907400b01e82214820105403940d81040c41c04603640c2d00610344a1440c820300800031604d603800450140c0c00000c072840403513103a40201e01a50528070b0208403d40f00030425804514071000810300030741c4009201500c19485521440507402c4540d42d40ca1203030314030100d00c4140e0740b0104000c0c1d450340083c0d41c20000c92141c1c036090188582700703036841400038105c02141480d0340000c4071820080380d102c06c032a04d410142848142c010f400c100c4051200c42c105400d0b0b01c807003401002d0b0160800031075070000c00c2c8040d0007096400c0e6050b440d801500340c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 346926339 1250 346925089 346925101
    0x1211210f06040606050a0b180a05040c09030b06090c03192304020916141c020408060124170405010b1005040806010f060824060f03010512070e06060a17 67
    0x601c140c100c4040e034806103010300110341c1d4500240c1c0c0900300c902e05c4070114208101d07510500c450740945000141c0c1312544031400612521203004a07446e0250301c2e120301c01d01d2407542c141078907069030042c411480fa101020820141100440659400a03012900002c88244a00080004290702035128141c1080c0509002c076001031b0800c03c0d44920b100b91002c2c5e11680341ca05001c0d0514a04c4070500020030348500141085404d2103000e888801900042a90014083d40204040303a100b50401f0291740c1100c0014089081054000c2410700c41c1000c1d22a194504030800805103200c8224510300a034021002c00c052040075009920ba410b4003c01415401c0340710074010345544d10074468028180100f42c00010300c025080f0440d0216015038484c401c4913602c02c2c0100e041c00302d801200003911000d189030018070f42c8604024091000380b10350300036504d506000c10040c00402c0002c2c442c406030b0140b00b080c006a5002c02e001500803401361855511150442400c0c4e5290010703001ca0b00300001f4400030415 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 346927589 1250 346926339 346926343
    0x40b01030203010b01020604020907030c09030b01080c01091401081b12090c0f0d0507060509010c080a091409270c04050f0a140709061d03100f061211210f 68
    0x81201d108400030007500740c4400c010381c0c6071042241e02030b501081140004140714040d41011050321160302d060b0503c25100e9071048001182038100c1d01c4e19600130f80c0c02e5a40b95803c5035001010305234207800c960300b0741035100000300030304401010320114412100d005506907d048064a0031503142d518a082c0519004100b15030303071000c81c506107100b01a9010b048090341001b82551701c1241d040805803000381d0401e141500d81c5d500803c0b1041c10400020340d0381c0042400c2d44003030604034103140e440038181441c10000091480303a400c412031088404000740f0020101ea000850304000140f509049003d020810860801800c10508c40d086414203003003210702c50250001c54491741d04030000304100444680a00345100040780c50710003003a805102400118000e482064406005600d0186e501d181340b0b0110b81412060710180300c2c40d0b601d403480300c00001c076076000b210041c1080a8190741240555240c2279442109442503034010b400001c804c41440301c82c4441070100e60444403c4840050300d0012182d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 346928839 1250 346927589 346927591
    0x10905010e07060903020f090721150504020f3405160e010e0a090f020a060509031c0f03021303050a080d140f06130912021006050406080304170102070b040b 69
    0x8401402140380101d003d9010f1081001a80c0c0c01520011143c2c4401e000e00c10900b4010740390300c0030300410004050f0110150758131801140300110000c00c00c2c0480280540441515411040c45980184030900c003108040d030039a5861501039101c01e4070800c800c104055400c2c0300a48c0310b04041b00300e4502c5824001d000440c00101040d2001010390680e03a1301d13410048020078090000c2148481001c580c01e07d005030070011203a800740c0c40c1042c00301c096031700007598004142c0c0400b000c501d0100f5840c001c0d00d414882c2401d007040700111030009606d00140180580e0f60b03040d10038289580031841904c0c4440c50341010002d164010229201e5511905006140360000c1c1040c550755400d0040304100c40802c41345c40c1c2d0241e80c210880c2181c984800007003008407900d84880c11542551024040c02140c1d00448003a0321010940241c1030a085104404007500d009130416801b90342000810031840100000311811140d0724152021040700d0b40c1ea0701c03406482402400703007519012000340400e10036040500307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 346930089 1250 346928839 346928861
    0xc0f0512040f0b0711091803070b0a0c03051015020304090e2d072c04030302090a06030b0901060302220f06080105040b0901030813050d0b060f060f030703180501090501 74
    0x8007409030750f401d0709480303034824a24004d2240c0400c200308183d40c20a100001c1d04a81c403160201036400143d107a0034a107801044c0d00f0b41d00c40c0b6007030081c0800d408031032050100003d00c9103070500044ca030100d554011b600a600c1907a80d90700d102004058001d100b84181c2e4042e0041c08024004400800041940c82001d0b81c010340c042d19007a449004205050300d00d0309802c0d41c0e200080c001081c94411030010120000c10150541ca000720140000c030039070500c209101358865240103807210801028031808034440d4000d04241840c0840ca404599540300c80c01d4111070b80c2c2c1c03401580e500d8101c0080d0241c16015462003c1012004001080c0340e82003076456400c0d00c0880d610703000e00740c0c0d980701044240e031001442d09400031b0390070006002040d0300740b0081c4040340800d8680d0084039580d40c0850b1081000c00001d44500500206014451034006180c08052400712540341c181402c2c0c41142000e44405000d40f800d0680d22045503001c0000b503541d00b02c840d40c12400811041001c0e0400502900300d080d40c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 346931339 1250 346930089 346930109
    0x40e0601030b0601170f0403030906020d2c03030114010201150803090310020a050a1d0604180e01020705060c0c0a0c030b25050405010507020f04020301080708150f070c0f051204 78
    0xa040755202e01d2101c00c500d00e4640058645440d260708100c5046d5014105404140d11202000013045140c0000c045560001d40c000850208500100c070312208110308510040442a203008000c0b2400003e41e81960428004001003409080043c0e0040030102156400d4264001001418840120282038520410341c09c0c0c900039900880144202d00c1125039041c0410001d0001182440c85005908008140c1c15020045040030400040540e0410b601500b01c0da0b145080c00480c1f60407601070094000c141400039410b050290756120340f02c40004240d8120410080742d078018150040140b080002d400504c900003468403403c0070540080c00300c7c0c11401c4c081c2d0700107800c0f0784040081d100100d64501c1e0707512241494140001101c41c1da01c01c0c002030f44e0002440b041d80d0031590f80da2008500800e8503030001c10010f0f1400c03220909210903890790b01c07048d442a1003000170100c0407030180780d4442c003186030020100d0b1251900540045420740701400911030840124142c041d1080203000b40c40054103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 346932589 1250 346931339 346931341
    0x40e0c120a061a0a0924021204030f0308100e070305041e0209060d0c0509010f06020f06040206031603020d05070e011403011a0c07171f051302060c010b040e0601030b 73
    0x70740da00a460b0a032080380d502d902244040460802c055003c1c1444a01c0340c60250ba140c0c1c0e640b01200302e1103110f2900040541202c40710184101c0e0100250080c491106101504140c5991101c0148940c0c01d08041e090041c60000102c1c031182100d040390140c0403840c00c040250600c2c04d80100200800c46003140d50101804103030040d0621162003a18040d4003c00042d6284e40d240c1c1405141034041c1c01c01ca076451103101c000300d9a079960a8080d8040e110680080000515003000285400705845c000031203604440c0070f100142e00d901084a500891050400b10080c4140108400a105a140040081d45802c05001066501c11030444208600b66074403582c0c00481e406141c050310003881a031010b203c180d0001c0744840040006441c555810100b540c07030050f0740d00c00e14010310f8207042401000303800800704040c142102c005148140c07540c04404000c50301d4001c140d00c91005800f000030b4440c0c00302003035554145109402c840c10b1200054014081201d164a81036550103080c0412102c40314407070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 346933839 1250 346932589 346932601
    0x90f0102070e0c071e0c0b1c06031127060607170a08010503060604180f02010c020a090507080a0c200c040204081b010314010e13060204030516080f0a080f040e0c12 72
    0x944111715940c0c000c44001606440c20880381969444106801c518150b4540c100219141600c503410040d4000e01e00700c07010f10f40103002c00c42600c150501c0c10a1052000d144102814a0010220303406072058580c60342d9400309041c600712a17140402c87d40c8001c0300015200740001c0c1d122003032904070340007542100c00544410003040280d801301000d004403020711054940100c0c3c06106c04010250040c14541418051600401c0d420250354000003801c644074010310582c00d40c460042079200c00c10341002c11078400401d500501d01414062900d0640410700904240c00d1030074010105120401081107581e16911084c40c0c1e00c1d042a200c1b4401c075403522920541103940203005a0006d042d0b20f02000030140e00b004600c2c8061140500140380b40980c506901c40018800c0c4000d202a500a40013801c0a0140c0c03946102d000d222034200e0440c80c2c20000704ca03280d131040010010245940304250356254007504900301168021580320b40355021240082c0700c00e01c94000024410041d0b240c0c000c07115503680c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 346935089 1250 346933839 346933883
    0x207080d0f0b0a08030703050904090c06110f0115030b07111903020606180f07050c160311240d020906191d060912010e01090303061415090f0102070e0c07 68
    0x500c81c513a00b9800030408040080e10810081190101c0104006503803c05d076191883c0ea030146400003404950083c1c0071020081d810407100105810410090254045142c5541c0f80c261180c803005290215410101e10054015118100f150500b0310455142c0040000c10304000c400c5510180c1c050300903403011130910709100c2c000107148010149030118989404000019070b2600034945010044103000420410030244001480b81456960289055045003408204865030900ca41d12850022040a94001940c0b1407511508141d0802980399510348455001900c82d5400c540d0340b0078130000d4441c000501d00c8205010703281550340c58200d420b01040b41c80720070696243d1907540c802014000c802080c0342500c0da2001d00304100d4000303e4800d42c1c025007182540e821417002c401080d01c403130003408402002566800e4100d4200d030304018071211042c144800b403142c00301e49802400d80201c14010717a402000450000e00451041803414170f09480c60290fa40c10065040360880500300640e0012040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 346936339 1250 346935089 346935109
    0x818130912171b0901020703170415050304150509010908030a150605040605041503090204020705060609070c0b241005190c020f0108040303060b0a090810060303021c030207080d0f0b 80
    0x10005036089203140701c1c10f0580e002903007514114440c403940800000c01c9014801c0d0000c001442e403580b03032410040058848031400000d407082000500c108008a42d6581c00212640000b20b070000e0700ea12052210b07400762440e000f0140402c0d07000011300c0401035441d44050009100080d00c00f401e15214201140c2c688514883c103070018a080c4402c2c0711207004600f856442c0c0d00181000999140242d021030300340d8100d0742c030a4469802c11000c0000900f40304203070301d910152034580f5403580e841c181c1da0850402000b0704016412059468044101d00b01001400038020700100b45400031162540300074a142e1000c840d0f8040300c005c28180140d201c3c007550b42e444000341d004100125003582c3c4801101c1c1c60500034025020103403100300010703841900c40c1c02441e1986042c2d070707102070060a101200b4a40400c640d0a001c019181400070008a540030402000c04d125881050312510075401088010b030046207806130007108001040124400d86521490f02c0000c007c5060080c51003d504004051752 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 346937589 1250 346936339 346936351
    0xe151e041a150a031505010e060a0902160f0807060b0d0305030103080a140c030c070b191b0c121b140103180c030602120a09081813091217 61
    0x26440c034600c10048180401e495110204080010b2403419460002d4501c10340703503105840030740341000003051491690007104e014100c1103c2502280c01d048010034030003c003030310900c0c01d07c550114101900ca011510359034440340d0426201210750540e03042503041c0d03910900040f10001c1c64040010f80c1414002c43e44d9801c25050b071070340c6045030f20b940c03128004c030340c0140b1308101080350120500c030518641d00050320100712250000c40c2c40300c1c4042075040c60200f281d0030a5015450500c400c102d11080e014440e00c1908040c038001480520034a08900440c844405c000c1990120010114080305940f0b443c0041900520400040c007400c2c9190401e40602ea00902c02e034030307965848004140d40203800151140145003243c0351146130741d85500550342482d401c12211a40c0003d10105016401a49103800000c020420006482e1540d9180020300c20040307110304e8840c2c141d803117524036607500403480001d00c0d10140c140540250752500307400303400c0024200c030b02042c0401d56281e82d010300b007011184610 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 346938839 1250 346937589 346937603
    0x17010b06090f030109021206071103160609171210050f010f1110050a0b03250e07090512070810060608012904080607030f020901210e151e04 62
    0x241e2264140003241e0710140c1119015901d40945400586960114400089800c0d01400c41410711110040000d4522020160705520a0203038104040400e4003e208040c1e000c40001451419031401262b01e000712000004510030120300001801e4800314624070411180c42c00f1076849445a00b0440c0c070120b600445c5001414801c5030302d003094090000301c0c504902c000119219452496140000d8440440d44030a55640b51408140c0340d0408104a142d0440d41c0710200120285540c000490f005803445400701e80c02520700494241030198070842c000c5e2101400101105e0001c8943c2c030b0f512301180c480c2031070034030841f960700046224510072001a0740c0035941d09803960b446c0000340603580c1a03c10000c85400c040742081e068202a01009200a10124005d0441440d00b8100a0200ca02011494441a00400c4880c4d2540ea2000c5002c2910705402290000d02401402090040590140135046442002c4c150003003030b0100341440d131080c1c0128003403090444045140d000341d42810766000b0140 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 346940089 1250 346938839 346938847
    0x60b03060909030c03161101090b2508040803130504061a03180303070801060206070305160f020a02030303010605091201090201022107020406120219061b0c03020d0c17010b06 77
    0x41c5031006016400c000c04004907400c100360300b25458150303484107541c03610080856075401c0c100b02c404054255107081c242080c841803442c0500251a51080c103038050b1131404920042980c00d5019409210110b80100005031599202d80440795250b104141c80c50414201d4500041ca518180c0a00410384801c07050070180616a10342c07003106500060001c0b40300440710109508034910800141d0b04c281101d580710141c552402c40080d0034040042c0450b02014109010000040500c8503003000081c594a41845603007501d440c100d00b081010314000707515000001c00014126802009442c10400440e1031142a05100d01968200c440021009016801a0149284909c1c181c00c0c6465100c1c466105070f49441c01ca42d0006040b50340c66004002c4110f003400c0e580055040c07001c880c03290095120781a1401c03034104800a0915136405441e030a200446400d00810054000010402154013034458031102000d480d184544808a010b00d100c43c035410b500d02d186118050082100540019100744d00d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 346941339 1250 346940089 346940101
    0x4020319080d0f020306130c0912020102031b0303060406050316060503130503030f010905130f080a021f020c0d02030a080105010e0f090a0b10090f050d1106070503070b0a060b03 78
    0x44103219055a111409100d030007185601c5018054806101070b03001680d901e840804c229141140b240c00d9820645030002883c090ba8003d8440d00586001804e900c20048107480100d146100e420302c1d0302642c003a01a80d02071040c20010146014040c129010700c00c094440d41850750720f100c03281c034042c40000420f0081209500038402960004c200c52158070000c0b2894903024030b140e20a84040c13407442038140040159a85500c540e035000b090107580d41064800325100c14042c4c4185540141401800041940849000700f0108209121010745d07034101d2101d16040344020f411400c0ca0030824055010741e4840c4070b102004454070381c2c0341900c41050503400d1030011106080c210360749a0300301d24104c2c80008140d1710703000442d01c00c002d0441c010076105440c40605c01042072020f401d40502c01c1620081c0320300c5001d81c030002c0940d042651280761003603280c1020015040041d030395540005000514005201c0c0100091810700c4c000c40021906444e0590400100c418610981e1100d40050000c616 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 346942446 1107 346941339 346941373
    0x507081b0a0e16020c1306050a0501080f0a0209010c060e010218060c0d08060406030b1614040b03010302060a030609020d02130503030915030405070e040f0317040203 73
    0x305103802d03241c80348540040c00c0303802e030b00550f40030900050b0b00c20045400a050b0003400241c00c005044141002040309010741401074892000210b801d50007890340702e0240030203034081000f030780d10121842d0094105100042c100030082c044107004c211203018140c040744640303000598851948460507400c190001030b15009010510084010380000308040710320359454101000266500d800140042446400c01482501c0542c24000c140d920f4211b025900301c046d03100c039020607549210001c0c050041303105040b90b03e10104010310050415001618444216050205903191a1030803002071360810071002c0d111550209102035036604003024030004002c2038000e5840c0240300c8012905145240c861600407403000800300f01040405c106110003003962500d1a81c407410a40b42c1340e503515044c681305500080040d4051400c44490b20421405998010300a03c4140b01c0d90740f500c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 346762589 346942446 := by
  have h0 := BRFrame.cov_init 346762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 346762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 346762589 ≤ n) (h2 : n < 346942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
