-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1373
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:38:33.945303+00:00
-- url     : https://prove2.me/submissions/e3a0b27f-eca0-400f-8668-d6e392e7a00e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 246762589 ≤ n < 246942446 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 246763839 1250 246762589 246762683
    0xf0b190608091203041407120606090e1c14130b0a0f03020712050912071e0503060f070525060b010e031b040c0e042a08040c0308070c03 60
    0xf180d0b041484070004010fa02e151070755120201c03a1584044c25146038054042c0006001d202c102007400401d04c6840302051452402844108483c90200503468980149000c001c08481151007a000b590300c1d4200210400421090902c40e4000c800d17600244101d10100803458071100320140030b0180b80c0b545c42c0307000062000421000c0e8003505000401031880c8075540400b150054014011061000d080c400840001880035460102ca0354448100350095200a0590400141204024107819401002c15051862212807120401004041000004141c0104610300383e02c1c103500328450704254000e482e0103400c01301c00521281110b503003c111060b404070020b00380401d80c0800d400694258070442500038060201400400ca2a002045019130b4894050340d41d501c0f80586d684288051b4a4039940e403031084800a5035005c0301e0f181440700c080c08120009064400034401d41340e0100b022038a50f03806180c04103025040c1c3d04020403412410000c0030030140e192540d40590111210060b0514603e9 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 246765089 1250 246763839 246763843
    0xb060114030a020706020c030307110706030608060c07030302070c0e06090f01060807030506010302040f0e0a0c02011107080c070e011205010f02030606070f26030106020106090209130f0b19060809 86
    0x8650031aa2100910000da05424560b014054090040c60050300c0c10159080b12825584100c0341400415403118458011405c00c01240300940f40a05013000100d0030401d00da943d0b44002410381e000500009012010103101e0f070180d5130903550000710703510410b03114200015081012124180101c1160000071940c1d611004540d04940f11610751840e00d4440c040c045015150041000d03041c55000c100001e030f031100d9803c02c0c074000c0078100c42d0802d4030f042c00454078098800307d121300c008684c10b000c400740600300f03c142200c4081d5880240140d546840d51030351410402594045020703440d40100001d15900401c0f600300d0014490002044104003120a107409c07030006075101500f01e1401c0c085100017652801064040030f029425041d18151010407c007052103000e03003800010100400104041c0707409020f154080c00140310194200300100c808181c00c620390070041c1e0850342d210880c800d1284221313800301121600107040701d4818030900e0b940640d440740030b100745800504a4400a1100600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 246766339 1250 246765089 246765107
    0xf070f171906020a09030c0f03030210140c070f060c05030a0f0606090611030d0203010305010903110120031e010b040f140904260a0329090f181002070b0601 69
    0x5110705020359151161241c00081d000040d0340e20501a0300341003c03010800807094103000300955030340707584120304600d0020701b41070f500d0012003101814603c2205d5070306090021154840088210207840b8011410a80242603c0c210054003e51030702011400280d4400000d512680c0c041a0502c440703505d003e090021540c9a00c075690004042c4001032101c588510700c0c2008030340c6400304490606184009080c00c0741c0c03080c0d004403541da40d964500c030105900300c10200c07803102001d402008016046400e40b4030003015507051040c0100000000707022080348107450f00301711024070790001c040d6841d07482201d00c0d035100380070309280700102c15000651605551404584a94080d0030150755840d15640c04030f14081c840b101000386401050781c1070491441c0c038042c0070701074641e540100b000144181e958000c1c4440302c029a000c03009160b01c401081e1070700c0031210303003280008a00091507626940ca0740c050005441e0010341c180a004400210031300e10b5000760489034007030300034440983c580c0e60054802c2e000c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 246767589 1250 246766339 246766363
    0x140c1018050105090105070c1e0b03010f120201050415080f0901020913020c0a0209070e09060d0f0b0901180305030a0c0905031507020307020d0501020a11010b06040e0402030f070f17 80
    0x881080207101a500c0b030030143c07413140018103055041c071029030f484a0002841350010030000c09a07080c0700b01003600b40403900c4010802080504d04d154100404400301110a0148540c1055080e0460045903c50012a00101156600350b00715001c1c1030300c01007154200390b40380c0c5914007001010904000d01072003103440004004002c2c10038a07039113680d081e01035000381a8401281c000e00c071203180561100204984030b00100d41d0760342070203182c80040204415002c0d0400380145240e191900010724100c51101c00301da00300e950308401303545040b645800f41030000c1c1d4194940b0010f584d52000c154100002d907000304c0001d07030b060014030000c8a0413100c1e403403a40300c2c05615a200c0c104150054010012058121181c1c1c8166441d00354160003207051a51090400c541c1ca80d4000b500100041d402070203115010241070007407140c0c2c000340000588030b0140d03009c0d0721500301009000c0307003c642d020401c00b500803810f0800d45820542c2e400540a444102d8841c010700d00040a0403d106440042a4441880 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 246768839 1250 246767589 246767627
    0x503090316080a0f0c170303071106040c030b06040902040606030f1a0306011a13030f111e130b130603031b02010f05160203070f0801060905131101020a140c10 70
    0x801d071114040340c41c40002c1601d1702c003696a00416206c03040700042c81e040200000442c1d50f410321000c01001c0400b824404101d0345c00c15800c2c04005170181582c44202c075007040b441d25a903100c040000380208000d60b402944146040c4000070b16035016007001e021a849400304010801d00e901503200c05009010071507502d0340290700144507100d0400a4030300403800807800181800302d40f0034000d0403106550070940d00c407440c4902071400c103e104080110070781000e83e0801a010319040302d1904078860780600310b1080a200003600018811a401041d02d00e1000701003000c041c0c90503242c00000e00650005a0000f089000c4210820550071816012280e069483d0340b10100034000844503078109800c010a105040c09500000d6030702045580c000e0140c15020700340302e9152103019400c5075440e0740301075002030400040003020418000030445058111100c0061304171038100403418030310107003001825490700ba407550f40c0c44800007580003540c00c400d90b00c42c950700104881c103881c001c566402d040e13040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 246770089 1250 246768839 246768853
    0xe062110170a08160503190801032f0f01050c011a03280303231008190305070209060406031b0303020d030b0d0201110705060a021501050d0206041a0d09050309031608 73
    0xa01640c09400c41c0c4d402401900c1c10a014101181d00c0b5807281c160220010b45c898005100340305800810f515202290305000950042d003075001d810701d484054007c0d01c154910010028140d0062040750100034440008214501488851190b031900440d40e0600070720540403400d00a04071781440f4131520548d8114815128103a5404801812080e0344050708001140c084030845220b03d0303541070080d40000710050a003804d05041501e0248503040c401000d0b488101c09002090304807007110302c000d4054500d004035170760354004500600002e601c000c003100020b802009900300c00360090016031340f00e83d080e2441c2c15100c5c0800c030150783c80450b40a0f03100913508450307001903004500e0070869010a10030789400f0740c1d40304c00190f181d401403c0d415025030003046104280c00780e8003070128007500044405002098032a004a1414010350007040c1d41c03200d036064100300ca08070724415100d1070101c000080c0300500c4280b400719241e41020b500140217110761080c003001c11107008080403c1c0da940e40c0003007001c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 246771339 1250 246770089 246770107
    0x40c06030209090109150302091512060c0405190e090d020d08060a090902031c12050c0a0f050a090f0b0715050103081801030209031009210e062110170a08 68
    0x10481d884186d185030420010000058480308007452080b080034078001d0042940400b844030f00d00d40c0602c2c180c1544c12020400c40150344250540e020780c0d4040d1040e0300246000c3c0d0203031950b0b2200f44c01100240b181d0740200700301204c001a00320b00d642d00e103600f5140040440038065502c641d05895560b801003031194203221540c2c065000e5070405c2d0000b400c848203200220107400781521585010000503010070780024001078540115604151824509440d291311090000d110342c80b0b1708074640c1041030020381801107900c6541048090b1030f00d0030208143c507968100d5003000345d200e103034121505841c0700c404031002c41c160b1007031504032900100040e1410a01c1810700a400781e10114003414544c3c280b00c0d50346152030410440b000c000c1d00d0800040c2940042c00d015a1017082804031200c003240688a09103590742c0300b0b400e009458011395246441d07159921803031000d03010380f9a1041d500880c0b0700401c078441004030010302c102d800e40d2036811801030503001c00ca911200415000703042c20100700200a8 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 246772589 1250 246771339 246771341
    0xe0d0b06100e1309080d0504230f060c130305030409020310080f120a0302130306060512061521011a0a080c030c0603060a03050a0c14010507030e0f0307080d0305040c06030209090109 80
    0x30913602c07442509290030038803800c0e01e08031101901c040d1004152440040c0011030140400c21000c3c00701d030020070400e07403403010060b030711400200100080039000c0b07010381c0c0b0300109603103480155910609882e110341c2c480d91418000d410440d031078024400700030030000d10b1440205405130b00214480c00f51a19040c4403032901e680354041d280ea001013590810403e8420030306621420084c6200d01d4010a070186440c1c1040607045007004c2005168000800b0301807c0341e540c00205800c0a019549080e4019075401000940715442e180c50034503508181d40c00b0f209c3d140b805d0030310581901c21202d0b00c414a07160740809075200e82011800b80c040d80280c10102c0180b8001b0040d6601000040c00410700c0c81d1030382c1d212400d042d941d0604990b01d4014050030300507162000b0020b01d50036400e203041402c01816880040c40110700c0e00601d07000d850074907200496600c05002034406489500d0444000c41b1031440700400400f01110240d4078031008000c089503180c0f1074000c1b118642d000500c01911642403100b000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 246773839 1250 246772589 246772601
    0x7080403020a0209090f0a050709140c160302030f1207140c0d05090d02150c010c0302031e09010b060a020a0308130b19060e0106080403110c011b02010e0d0b06100e13 73
    0x18415105912805850060402c104c46906106602400341c03184ae0201c204142c4801503207841e0320b44280c408220601141d0000c1d40d04400e50810b81600202031820241e041d8856082c42c81c941110004640000300a4511550b01405032036403034201c218542480900940980c1d202148180c0001e200c0c0406540704a01500414500600140c0188511350000c3c40070000594145150040454a1062500280f1590481c601141011b42c51803800300c2103481c00c84405900c465110085c80301007103c0a40945c0038224010028141c1696082c04480180d40c1d203003140000c0307002540840024412124400c8030015040e480300ba0054641c94400140040380e44548800302d909a94000006482c64086120340c0204200d844464041c14542002002038041510f0750041c1c0d8408078400c2c3d000e991003612b4940304006440c0d0310b1240c2c441403004071009110000800d60140201c40c4410503c419150524060041155500d401d03c5503408152b0310011034100d0b40d98070403d1450f9464961500340c00030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 246775089 1250 246773839 246773851
    0x121002070204110a180f0f0314100509030301090608011e0c050c160f0501020f100b0d020a0e0a0c020a11060307120f0603020307050d0f2a0b030a0507080403020a0209 73
    0x818061110903032038190b5009103000c0c2000508a051103c5c01c0241c41d0401d401400f0701c91a01c003940c604041400c1c40182e0309100c010030844107201d00c02842041840404645040c03007006000b54100707010b640303170340e600f081c00342e5440c0d02d183c5240064039140501c0f41c003044040c209158551202ca05134984020703e007045d001420b010b02044040c003050313410b203c015044450031b080120f980303040c100c030084a010b40d9003106055622120040f421010009800c1c112800c41003404261111014013252004d800c40c0e000940002c9c48500c0407030101d003100881803155000241c10401814040000c83e40c802d0000d070302501a02814072082ca15080c030300c008613400021400c02c08507120f04428140100c9a80e44245030260355581002d00440c0383c28003c075030007010121954011030720b040d10b60f440090070303c0800810b070139460b400e2071030300d00e4540e450300001c2c03040c82d00884480c7c1d54421500b0001e0b88210b50140103030f450000010038880c00387c01c03400d0040d40c040e40105154400341d07003400801c00000e401 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 246776339 1250 246775089 246775091
    0xf1d0405120307050409060b03070203190201110706020c100209060a05090d150912020d050d200f03070306080706050a0318051b0306100b070318082a121002070204 72
    0x40d9100d07012010045004207020b9542d6a42c03985444009800c550403900f056445441c00c005004a02d50f0000546042d12403a000b10b009540c42140181c0c010712007621109110030001c9226418496142e010785030b51007010055960304003c0e800190201c0c401c10f10b1440c3e001c901404040c645501c2140506900040500601070504054072a0b1400e500c03181000944241c40c3c04105040000e602100c0144407032500040000b5140080d020b0240d000d66100d01003102d6a403a8054a40c02d20381d01d0703503144202c803111025690085080030700c0c003c1d0710494640d00424101200050500c20000319501200c1c0103075286800c085540400720b001d030a1040039010311004283e2990b0214005001303081250501403507414401800c4414076080c8403005000200e040310640c000c111a04017074044800280d40351a0291282514402a880e141d141d034024840350702c16491400b0f032242219000c1c1e0700074440c030b000358000b40510b8400c1040b6000907076111741043c0c00c24840209042e0480c0c02038000c0d2880248 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 246777589 1250 246776339 246776353
    0x1e021b06180a061709030c0a2901030f030f080906071409060415110d050d022b020901030c0c120c030507050d020c01030b040213051e0409061506020f0c1504090c030b0a0f1d0405 78
    0x2c402740721002a0819a050f62428140030101034000704101c0784c00d40d00b400c06411601d80340d1180c9403900b90041c4084280102c00c5a00e03c061042601102d8680400400a6032500c0d01e841540c50107800c1058103001146c1c040c4100d046603440018415890700c0326a50b803a2802c00e104c1244030203508611030300c10546100121948450528802205c0803510301000182c403007494900050585a0204480d018411100c01c1500424010381d41021203400ca8282112008154502225688940b47c00501070307001e500c00106245c0d40c049069864401c00340d8060148a0262040100320312030720380c2100c409000f01404100c0ca0509190184070860b60300055901d08a030034001c1802e4415400080350056a00c100001c03c6050745a00c100c06081944001c1000c0012002c0c82c43c1e98440f00c42080e8814002c2000c45901e4588400499020b4440c404080c88081280c0d400070300500718095009105446840020507003451004943c811102c800c0a286020201107215640c3c082014109a81c2d500400e9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 246778839 1250 246777589 246777653
    0x506151e0c010905100c03140a0e1c0306030c0e09100b030717060406050a0b1c0f0c060203120f070518060c0a031e021b06180a061709030c0a 62
    0x3c41a00d01c0b081c0540c0140c4003807154840d081c4126540c500c000030078580360013034510b04680804e0680f0b621401c1410300180181107524290318290211a2158890010006c543c1c0c0740340d4150080c3c0c044034801e0440054482c0c6802080450450442d40d241990303020303103030040d01d103c00c036000078030b0b011009001d841c003081c3c540006101e1008019100314980d8400028032040002070f118156000180000821504e15403400191140e840da00600e048a85844c036610103110341448003a508030391004034003049070340d40d41f4080d48030740240c140440d6600c0e104000031a0300015400e80751140f01c5907a500341c64407442164002c0c1401500344c1c6d0503000b8030180440850041d00700312018110380691284130116160a42d0b514104410890079411500140c114a8585051000d6015081d8048503041d84a22010710522003005101052681c4040b00b400001340282d0042102100d0020f44da2280100d03030798a00e8100d55920070743c521703100254006000c1d0400700c1c4031480a1640f026440c05500700c8102c100c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 246780089 1250 246778839 246778841
    0x312010b0f2a07090e0f010c020606060d0e010207030806180405071802040e0901050612010605090c03060f100807020c1806060a1101290409031709070305030f0d0506151e0c01 77
    0x54000050035507442c0c0c9240f1680314100f10844586c00c040700280010119450000d49918005d8003450040d000840d143c2c1064031143c00c0394400d000c85030000c54480d402e41c100141f860b00190380702800341003c43c42e81d0050520020080b440345800c140108845403034070018230040b5a0400d2242c4401d0b6007800007144105001c16014000d800c0c0070000702e02420300000300b0040c00702030340c00003010780c5c0340c460204095181c1c4800c0a611451541003691251350f0031002c94005007840e240c8039813005030006403600003500b103803819000c4e1003164200c0c0d05200e4403c2c1404481881654041c4101b615440003900c40c0c503103140140990305583c07401c0600d984002d000142035a140f148003c01d50400c516005504c404000701e00d00d08160100c1d014819100b107603c02074a1603042d6039505203141103400c00a44101d00801500c0c0042d9032020443e40d803034500c8080111140c00515102100a0400021410324504501000b103884030325481e0518103000c1e50036440362200c0c500b240e580402010702006c1401d0a007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 246781339 1250 246780089 246780103
    0x103120e130501170601151d09040c0f120314030408190509130218040b0103020c10020d0c0201090317150a0b0a1404060c1704030804080312010b0f2a 66
    0x5100001c62654141a0710070011980524141c0306a48005c00411603002400e05a64541d0707106c2c00d0110040e0b0245550583e04c0d0400c140445d0020106402c1c4410403219050310b80447d0302004805904544500500d95030f1181c206025000502d944c00340160701d04540d00858001c0d2050100343e2a1001d64020303061180e07003038140c3e2404580e0204540304682032103203500a031045181c2d800c6151951800482e030300d582c1d000d03003003c0c000c568661a54200b40d010340c2c101c2d4903041c41c440c102c51404004d6408000130390b0000280402c07050500514403520b5005001d007144186c0e05490b0b50b80302182c20a028000c54800a00349406551001c95586041c1c440c0ca003d040680404007002c1d41d600c02296000e003244405203921000e9150420040200e250301440d0f0380c0c40154084807010001b600080c010400d0300032a01302800d4903800003000515140c00100030500c0206500304516140e80e206501c42a03030081c00c1f0300003c50760080060141c9507007110000b546403000782c500010175402040e5224a8901 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 246782589 1250 246781339 246781369
    0x9030403060b0405010324060e0a0209011b020d15110d0c08130c17010605120102130602061302040c02031605100b031218061603080403090b070b0103120e 68
    0x100140500078051140034206600800b51424402c5504d16980c800d500440c0104d05d04548003084000514581940c01100040c0188030070f036240c40c1810360007980254040103140c1d0100e510400002141503010450140441d001000840750340010303120b05100309021503400524998914101007004172840140005616009000606446401000c0e0080318060038420808500b0360903140013502980255060b0786410304e15100000403e2802c82c00340c101500090b07404810030420341c201c2d280540c0544600804451452034060f6a86030603a250181a04e10400d1800d03c400044007608240d00a04100e5450344122840d111265038400000307954400e0451f241c0e0403030307003071440c4e000c40d42d000e2040c4c84041100038210399810340c480484c061040d02c0000e80302d4642481404400e0307440310181c0c0d0b071000501d070420b0050155482c0c01003d8503000c40e421000f003280d10401007180a41d2805940b440c6510080805c82d0382d08684680c00103c1c0c03121507103001c004050a8811050301e6500524400350 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 246783839 1250 246782589 246782593
    0x60d0b09010b0a170a03141b060f16050a0e01050c010c030e01050c0f16030c020d080c060a0b010c0b0406110c0a020f010f0c1e08040b0a0315080309011805030609 71
    0x718031a8204005003403e90304c0340101c9004204100da9054000c10a01c10640e4141007111390101d0f034480120444c045c4500c02113940f0080782c914000d00b68045000c038454513820444405170303552090040c10080108600f6070006009008840da894024a4660b4840c0b0741414904d04250b0300805503800c0d50081120000003d40f078003112061030f2001d0149030b0300000490802820240c0c3c0342f99040140c000d610041a042e00540c070b80906260054a00c48406600542180100100303070405a281d5030089940303911520444000451031662071182e108010350594410600c1200d41d120003094100240064410555403000018034400c076000a1400036620310241441c801d550040040340c1c07051004083c103020799490341d040c009600440c6100143d900001c00040002d200121660340703000031a0082c01e0302c178000f42c0456070758281d40207001c20407103035513090009a0078030071202c44400c0340f4030420790594018001c0c1d950660181042103080900b4074a06898250350700c4c0083d15086040e00d80b440c0315 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 246785089 1250 246783839 246783851
    0x80c0907020d0c0629040605040b130506040603050316110301090c0302120705040f2304020f0d0501090b040f0b1e07030e0a05010c081e13020105070312090507061112090108060d0b0901 81
    0xa040c80c7c040c81004003c02c95003081001071910100706170313054480c5d900040b43c1e03071a0300180703069480e40d10a001541d045802c8945485c12408880c0800354801401e0b140801d9050004075280f170140180d031b104941c81100041803d1030340d070078054a200c040300c91800b41d009250003c54141c80303034802d6081007012100302181000d8064031100000001da540c0a5190210b002008003684035880b1092140e24242c9002c0e0001013141000c030300500c86920000c0600384d01f07a0134003090003003840000c0c290314001c0c2804030880d250590741007101506510000c040880040015100078001e50000c0c130b2280345402070714400c2c109690360500b11640c01800002103085d2105102c01d01e541c00c45440896800291010864100012101d5141c1c844080007410070500246250405208003240d0545602010090040ca5402e00c0e01d651204205c4c0980c0e80050100c0442c030a4040d00082e24582640c60f149485280803000030044920300d400502c11900a18060501c03000506a140001e1050642d40000508 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 246786339 1250 246785089 246785171
    0x301081c0522180506060318030f03040803010e06010203210702071809060b060a0c080a030209130e1c051206030a15020a090b071e03090801020c07080c0907020d0c06 73
    0xe24580c0c0c83c1168000e5180c4010070806459120449402c2104c51075081800385c811701c0e4441c81c40c428a1a00c0e4011007021052008001c202405181605e0b018011000d0030f942e00c02c012643c030b01030701c0b609070070310000c6c001d602500c210b40041030394100c0c3c0c4c18419281155140c03841180344a020102d1600c0300341d03039030301501c086c80b13403621941010700700884085c0d141000800c801044548404409001c2e400d0014850803881c0c00303a8100c1d03e840001a1061100c4500312003540010a9400030400c01c2c1d02036801180e075445e80884e003c0e080011207440f51814500101000107413810300504407038151140c11181c101152099620321003c0003201c0016942d0f0440844c0181950115444541e801e4010f00030400082c000030b85110520300030001301800503d0f10b04044805000e90740c0584460751000411005620300401c0300300a5034007400440c1c2640180101740000e0b941e00b00c4a100043c2c20800003440030701d204070f01c0300450030300486000c130301550507011052129a6410204001018040d10902 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 246787589 1250 246786339 246786359
    0x816110f0102011e0e01150303030209010806060f04031b080a0f12021f02090a0510051305180103150b06190f110d0c050a14061009020301081c0522 65
    0x40d089082c030082c00300d1610065104255410002d0303940c0490380f202c4007040510025072100701c151000c0c9851407003065803030070064001c1d4041c0030300c09e0019003030b0000a02c050a241e01106c4000c4070304481e2900e41407568075803080010b034200003038400013181080050005010055443c04600500880f40c941c269840c0c60041710800e04900019504807030380d4034200103a090811800d1400d0304402681c3e03501440002038000c100ca401155214080d1407540150641c03100242c5040c0004001c0403da01d078a034004c000b482058083c0481d20030780d020006100044c010141484e1404071003d010443e04040000940107810802000030105c07006414041a942d00c02c420b070500b005582403008002d07000c84541d03611106a002048180301941c42c8040c104402080000041ca40120080d0740740107205440030f803a0b4006503205210b41075110800710314100300d8400c9904884c03620006040d1030381512440400c28401c050710303a050200c03c2c08207004c03c01c05244042001c09418070b851004a052150003030b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 246788839 1250 246787589 246787609
    0x30f09080417060f0c0307020115030c060e01020a11040b06250b010512070e0912030c0a0801080313032301090506072601030221100905010f020304050d0309081611 72
    0x640a600c01003d0014001c081100d1310b4201c00c15168455803030b625a502680500740003142051140d1a01500000780f02d07a91031500b0a0351030603902c4018548403600126954140e00002510f140c102800e0b1b50003600d413035400422050005071085007482c2500f50022101c030305010002142032518490001004615120640504000c42d0495020220040d0256680d200c0303000700c100c20403041c40030079109502002000825600404d109589281002003100703540c000c41d4460000c915076100100d1440c4002c800d4482c0426106284c04078103203140c03224058500013411610411988548101d030b05402030141542c0240160010500c4c4d0806490060098586840b0400c6103918034450401d41407501640f1811a501254240195020420090600c403903842e02d41700103100d150000078070005030340c0114601a002d00000c100340c02380404900280e1000310307030080c901d40105240403007030f41c0a80d00000c0e555010b040258208145500020900d50040c4c1c400c0e07030340c1c0207001460343e05468032800768 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 246790089 1250 246788839 246788879
    0x20301060e07050313020406081006030204150b0f1e040611210a0302090402090301091b080303150d030c0203060702100b1008040b070c02181f05030d0e01030f090804 73
    0x50501c9203031920700144503001c041c080390059180541481d083d59115003240d40a011104151050200c4284104000301110720040303015504064104004804190140c802c641071641c44030728096003070a20000542c0503a84036850040300d400082116240a0045e001600c10742c1c85440103643d8070001e145c6000140d200c100d14940203101400c6c00c410268040d42d0716001a0705001d03886040520016001c0c0c050406d80300d8142d0b00e846803040a01c20182d104090012002480944282d10380200a4581c4030446840f94208240894880a81014201948120300030b20740b031382c20280035500003400c2400640780000180d0105104541145c61751080b000e08031030071180720b02c0941c440400500707043c2c40104040c1c81314100c01c1c0000c0506001e442489005540106148900104d000c2d1039089a03900703449030032680340314120103210b400c8090f103000b090311030041c000d00483c58400411100c0d4000d045059040545070115013074a1110381c0600d0034175034031070080a91154240740360b4407120082c403019 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 246791339 1250 246790089 246790109
    0x9060615160c090905062203051b1f0e010b0d0506060103051308040303080f0601020606010207030212071707140a0b120c09060c011413050312040606051c02030106 72
    0x2401030304548040440e81d00c000030081d00d02107001107080c4103109045030750100001d0790074502d44100b00302d800b096192103129140c1015003055200c1c00350025454000100a01240c801c0000048440400b8070018007010304100319440c148400408424502c0d80c02c0c82480d425495100c030f424038610030300603241b01d1030055920f184600c0e0709444482e07903120040e0003103052544e1a40411845d2100c0f40341341034030f250011a21a41c0382d42e01e28004001c46011a42e1740d111440c800c0100340d47c1d6201240342030040380164010321910b41142c08100b4a0360a01c05680800d1050180001d5a034000c4a10362055107000300140102c03a1421050048542c0c5240495100300340d585010301c0300010240556801e0460280c8990302070f0768100e24038045102c0c10b091303e03501120114000e518031905400280c0c1c0844814480e41d03040e1641d8001d00c0300d82a0703d03280240725410a0203003604c0c030701603405001c1c0e00c1401040007003900c0f0340d40c0c0c000c20720428154100d544010058068102941003d02501c0d0040c9815a0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 246792589 1250 246791339 246791359
    0x507020d0804031407051c051b060702100c020a0512030304120516111c05031903020d02071104060503011802060d060509040c06090b0307090b0a02010b1e0f04021207181805090606 79
    0x780d0280c49d600b0300c00c511061400300b0141e803940c503103841e01030300e5515a01400c200342c1181c0e1842c0103403c0c00c0d0f0b007400032813080d214040081000d0802020702d40e4803615440c025400d50302c41d03640d02032a0f91901034400040041c184403054410f880c51502c00082030260020301005100700082c816110303644030340082c10940142d588000070788000203e50100400240c1610491080d2004501a00c5026803902c0c40e40d0001c9614030502541d01032512408104880401045030f95809040c03d80701c5070b0715004490304482c0aa4005420440c00404441402c1000006d030151240d0009250840964042da012061210248002a0480310200c09803c0e081c010034290703d04800000e2000441780500d042009010511007443c90003500011180d0100610383c1e10090303010b40c1640700b140c40200e031383d43c46030041009110441c1000e2086507441c00c60101d549070180c0c0c9100b402d07180e041c00160400e802400464000070b9980f98505c185148010310200414a8141317100340c0c2d4508080500181e1084040307a0f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 246793839 1250 246792589 246792593
    0x50913050307030f11010f0b040f09170901030603050102030c03010614040305072c090f01290402090d0b1f1403060402212b020d0507020d0804031407051c 68
    0x182d4004991502d001261940b1110003110a010507481121072036007013003000c201a0545410462003070a055404111000c2c46e00f075140e003660303c9140080e001002d0310200b164605041c800500c40c1d1b240604010500e1a80d07659100d003264011030310a8040c08000c00144103003684880a072007c2980004203034102400d41c0c68654131400e240c42403541100c4010074200c000407512883c0014081c2890b10986245070034100345441d480048483d0802e9440c2024100700003a0640440004881c1c50504041c0c4c00c0d803000c2130000030f62040c1410360340800d41610701000208000d40e01842001e1410f0880c030320140d07248410151580e5034101010308299042d103d4107549001684941c06901112400c0c07041c5210300548141c030201c107070642110b019100c2e400e0f1030311035101e50f202105100c102c0f901c80c041f103000c0000c82e00c81040c0050304000580c208140b038050315101c0c013103c2896008003200751401c1c0c2d49588515015007030100400982d00f08407020800ca10301280300498400800b8000ea400010319 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 246795089 1250 246793839 246793843
    0x603010b092101020a0f0807020d020601090e0f0703030c0605060414040b0408040f0b0c070b0f0712030213060309150c0f031a0904050f010501060f1d0114031005091305 74
    0xd142520300500c080b80b0b000c01250942c01818400182401c001c554881413210001c141c6c4811000c80000300380c400000c520b0087c4002200f1001e0801c50703000d001c10f42d00b40489000500016440c0c1c4ca11407041c05504d51100109100c410300542c4203440d0f550020302d641c505402540d400900e41303841a85010b01c0d600c16006c1141c011540a60300c407404801a0707a5900d000d16850055030421302d000c2c00a03090114070040d0703074001405000c60b40c6046641c0f00b44d58100c401c0c0148511000c1c410385080a0180740c4c000381ca050507640b54601c0d103003000340c10520484d1804000c564194042d000207500d4802c440c0612243c2c0c0148440354260400910621420303400c060603880c00803500c4801c055a921740000b40c180c0100d1440124080200104460300b00750801030794801d001c021100c2207529100000503218000e03100c596040d9500c0e1203200542c10002034501d00821511421414810300a1038444802342c4880110722441c415140e0580a500301401c3c4055038a0080c00154190603102001d00440c01c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 246796339 1250 246795089 246795097
    0x201050406032a020a030e03070f05010c080c0625030b0303160c030803070804050714030606010c032708012415120509030304020f0303091e030a14030304020f0603010b 74
    0x80c01e010400c01c030140049200d0080100003070b0340f41041c42496010540c0d010540309102c9020b0f03610b01d5804240e200030140c440035107100b00070350350080c01030401840d400784501a1040e801b4803502400e08590755489802e100003110b52007401801e4100450710380701070f03001100ca00c00d201d103170807c180ca0f950340110b5a640704806180d0035004d0b0500f5179a0400001c071090b440034545c010400ca859040c5404090f2140390140c808941c280140b840200c0c1a50380003110040300440100180580d48864006490a0300c1c9009d060302003003e401014409100c84203240801178031403501c112003c1c0d10744002542112031040c080d500d860703401c002d100b07000f800180f0880151198410044048400208240e54501001c83d5800b0903d041c1800c01034001004400b942c80ba5009540035842c0c03482c910300b0540c0364400c1c02a05c07a0700031031071080900d130b40011003402d1550000c00380441e280d40301103846058002d503d00c1e00e0b1000301e600000801c011414010500c1050400688a036070465041a01c01c24140c01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 246797589 1250 246796339 246796349
    0x5010e07180b0f0708131d0c07030818150417040e01090b1f110c060a0512071b0f0c060504030807080a09030c09020a0e031c03090f0204020a0906140702010504 70
    0x300200d03002c103107042c0701400c82d02c2c80c0d940308170f03000d030390340680b04090110304030343d1146620000c1c1f040500715080380c045200341d10580240185034070f0540c0a075015a0403900c013030f200b60001c0301c9501645916501c2003100d00030200a588801e10285800d10307100c00c10700c000d44903141c44004240410884244c901e143c11741524885a40071860840840c0401d42c0404d21103030140303402c0c84030a480c903129900a98224808882c09081d03851030559841884120311902203a0340010700200100c03d04401c1a40d0b8658104a5a03c0c005503071804407c030000080d11640c1c0705480001c0300300802000c0000d04443d01c3c000304580e0034803508152468a80f0f25207401400000b80c03003410001500001c113840f4600150195138400e64141c03500352160b4041d4000e4100210800c00b15108034500c3d413440c640010709003018207120f10b049440d4031092101703c000e040d19000c101c8001100344131400040c0d840c1d0004e440504002c2e0b0ba0540031a1912500811650b446030713078501c41c41010009000580d80c4a411281922 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 246798839 1250 246797589 246797609
    0x40b1f08190c1d030c0108060402030a0e0708160e1b030c090a0f060206060103140c0f04050d12090605120408030c070501090605100501110307021c060c0305010e0718 73
    0x180e076169900d024458007103620745910b4540316082c580507801111440200781d00340c080b020322020b80c1e0149503a904d26400030317a01040074a0000f4465240c180c00a6600114110b4003140000c907048015282122540240d203491b0440801003849641240c01d520042c00803170002c64040c01d2000d01e181c2440804d103c0301541110000004030340c0b40150701101c1000380c0107001e02204a561b10040c414400c41d5004002c0180140800302e40300358424003560760b101842700711010780ca4803a48100c4841d83c1c010a1120390b104814000041c030359503003000045407580281c13000208c0300aa010300811042444e08038800b88841030182001d42c0c0d0240e480d90b6030241c1e1106100340c1d25100d01440d110316001c2d00360000c1656007000050410028980c203c940a4102801c04000e95030f01d540064900b02d100d40441440c99005001074005880c003c0c40c602c1d02c043c1c544004d0408850b854a44d42d0135140f00c100004c000c25103c0004202c05001c80030407a40c0b10405241c21040003450b883c0d01c00c2c51081c00c0c4500084d803 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 246800089 1250 246798839 246798841
    0x40501030c260a05012301031d010906020c19050a03030209210f0f0705010212030a270215030705030406050402060d02040905061005131208090d11040b1f08 69
    0x110b030199040000b40000d14450510314401c41c18080c84400040360b0326054641404000030344840700d10310300d03c3c08030312202243e48400e030b02d08011401040b5110500c850141c0038809400854003c0c810441014010000944c1d90010700206070b1400003c480300200c5958040000008100041801c081c00c07036041c5405642d40b514540010030b04c03e4408101c03c0c032065201c0201580c01d2002a04106440307100080d01c0d10241d26000c82c1341c45440c2449201c0c003582101d001c4880c048502d00042d681305e81c507010000b03030303a000381c250050400a080104041070b02c03405600700190314000580c10044644143e46503c0d42c5041c280c002e141d0b00024000812940e121b2021404650701c900541d40c4601000004649581d50303403840c01c001d807030184d612500400306683e018000901c14000c41b40bd52661611071080280342c4401d0720b402d20703004a0152500344081c88185016924049000180342c0161a680c0042070224208021250b100041501c203c2c08203c2200c00c2045181d030001c000d58083c02d00d81c0325 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 246801339 1250 246800089 246800111
    0x131d040f02030106050a1e06030c0c0201051b030c0d020709091109060310020a020a03031401060c150204080d032c0706030c03110703090e0703021e03070c1403040515070804050103 79
    0x25000721780086a00c00b103150404a401164030301c454882204080049058654445043d411201e4010f5100e0001d00e502e01140003650261008000a000386000744000c01da0b03091120b800d5030030007080443c10b6000003194035040e1341d0400501c3e000d0544030104000b1440c0c1942c94015580e00b07829000d014134094000512141c0c0c00303200c0e208048014520656844180e510020345410002d407085000c6072030500343c01c644510006183c1d0603507020307849100341008540c64400442d2404940030712aaa000c01c0081480e190a10a65121308100c2d01c002c90300c074039501480d0661301070340c280c0040e02c03080055062401400004004048502d03a04000440054a820480c040e10100d100014000c41c0054400101030340161031004648170f2084130307402503d40301011803d070710420704019a1040e80301ca0700c51041e02464010b5801088600385255a01e0080d42d5201101c519024454035581001c141048982031142200c08032041d00d4500901d030002580d81d842146c003070703402500e04040d030307070489501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 246802589 1250 246801339 246801341
    0x1002160321020f070317160b0901271e05030a0201150905060d0209090106210308160c0215070b0708010509100503071e0b040801050105040c0507020907120f0f02131d040f020301 78
    0x50f522040d080110003c087c9041c1441003800580365010700c2e42ca003c19a40135200c0003808500ca8448c0340140c8801d0264070b0b00c0740001d03800803640c00d10200c4001c03200c1c031000802c104001e0030168280e03000130408070000031800b14540707281c0e44081541400c2a00b00403407a51480d1520161640c1191280c4803a140d00d10458010600750300500c1c1c40b1641c0f0105c0b01160521000303d040120b2281c3d50b45a860390350346040305400e0b40904c03107100100d070700030545c2c3c001854081461000e031a03548074802c0c2061801e49410300318102c00d451003404502503900601460400914141d0700ca8000441502c486140201080c0e940707409224210301a00c0b1000c1030f214029594600c40e00138086004566100d903141c1c103215000348828440e182c884c5240c401802c00c0305025409440e4035540042584e82242c0d10980140c41600c651041d4485482d941c1d0000c8900070303094440d05020515400005849480c02000002462119000301d03000340840300d0002c000d0507407545100d0344a030b4005140540e440c00c40c40824 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 246803839 1250 246802589 246802597
    0x9051c05040504231f0306020a051c020a03050c09031005060301090f1a0112080306042003100e060619050c19030c0204050f0f01051002160321020f070317 68
    0x1607000e420140b120310740a007039048031605003814440022441d1074140301d4200c020b851005c40014810300c000208042000303075000d03098603002824824602070781c4034100386001c1c0f10301204244e2641d012911000155051082c2c030781c40741034031010074a005190b070000795803100d040a8880d4141d446400203440c40d1029001244069400411003843d0702640c0303400c0310f00021003096819800c0c030010000901c0704048082c04400381e00245180d28540b52041803002034a032115007807040790391280e1144401515180254480d01d9102c11a8808a00303004401802000c085c3c0102d2042070144000080c0030001e00f0099130107274050400c10358031004113010070705011042c60089138092080958500345038129036442480361003120100704a41c0c07a045d642c80482c9041c2c038100c203200d0a11005101c2c60400a0a00c007031000d0500448648141c10280310240c03148540049640c03141800703440b00c0100c40d900c02e034a0408041d001805850240242d115516039031444090540b5616179060003407400b040e8125 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 246805089 1250 246803839 246803849
    0xe030f09030f0f0304081501060f1b0c0f1401050f1204020d0f060203011a190e04060e04140f032701110d0804050c030703080d09060608031c0f09051c0504 68
    0x51203e0041840c00e01d600c07a00301e8450114a8004c2c40a440711028000314854140c42d026298018502401070046581e0b42100c1c80c100840140e20314003001050320f000d5914002e0081e0800d0a200b507007004501c02004112030306080c140312040c844020b0180d02d0b10240c03050004200740041007590b60b0f00010700c00005281010b810400140b08440034890030350000c5041e01d40e00070b00d00501d04018081c90340d59104500700c0c9028400b012107003c20841c0b10311010004504010300c00300d0155190302c800000c0f0700b8180c4d4222070b8020f010201d001d002d00240803032204003064002071801c0c0260001004483d001d542810440d09040c0c0b948180e0702e07801210030300c5031040010100c2d1840c0c0c410320405024218107540c25503c0c1c2c410000c081d400d928000441038140d0b0752010a15040c44104004000034125010701110910b49861011030820420400f5095800382d6201c44072034a6089402039044540403c682202603060194810114000245c810001d100701c2500303040f01e12020700210b510740915001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 246806339 1250 246805089 246805093
    0xd02090606071a010602011506120e0c0604060e03160f030803091e1f020418050a0e0d022506050315030f01060f081212040311011e091103010e030f09030f 68
    0xe004500620403e4050585083c1d400801c40c281d0f500c20618a40800c0d0700c105800203411078174618482165420440039119904115180780c052b500003c1d4168001e074100c80c0004008004c3d000c0146010007100303109112860b5a40242c40c180380d03040c90300320864040603040039030002c0801d01c498001c2210201581d06002030140d621001c0d801d00d074907145000300780000445070301c044080c4a0102c4c4219800c54820107403240d5816080450f500150000074200700c0c2e400d9450480d1000c4800a029a400d08584c1c2c1e4060000b07194400e424000686824a00e40d480c1640d091041c00301c01c3d00201165088101c0c00801c00c00d440040e4002450081d2a003588132865090803c0010300c0c6001c810924180d4003403034252941d00c0b200b00c11141881c010768207030346891640c00000c9004a400750500c2c1c0c85a01c0c3e602c0020a441c01c00d006490001b01941104503a02c540c0d5280000c03d1012400c880d80381104100c00901c8194003285540d42e1b00c0c001d84040307a204130340019140341705a4042110081d540c0403403017 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 246807589 1250 246806339 246806363
    0x120c1109040b040303050a0b010e0f0321091504060c020402160c09020a0e01020313030308060a03120f0e030309090f0c0c0109060f0e1501031203240311010203090d0209060607 77
    0x90442d055030001e40342240480d0030031380450b86100041c010681a41410385d1a4000681802d04200c1c5550750240d0480d00750098041000103100c1c441c1c0345400007941402210380e20749080081c0100c06011030300240307880e1000d1100348040e0364011005003244d40c04450150721002440c20b000ad00640b0f0f503c0040007545031a00006134059190003910000c141500c94030340c1100d0241c01a40c0301d200300c00c501204011240014000680100c02c03040d003044001e080c0b44041c58403545c070803800701901740503440895407070303e89201c0c039541c412403880c080c1e4420380196040101c1c0c100810700810010705012004841d00001800040d142820b03103100b500a28000d125401150034050020404107e207014120705200c40c030f0854150018418150001240304d03180309a180d40c54800c01810840c0801040689030072400385085040d032003592500b04030a8030501d0880c5103107008081002c014080d0350540d0030500c20f04030ba950301d04940307451803601a41c000981d5900c150005803703109191008115403c800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 246808839 1250 246807589 246807593
    0x120a05120a02210105040506150904050c0708040f080c040e100c020c10050306090a060303080109021602090103030e0405090c210c0612150d0803191413060f09120c110904 75
    0x80c3d8554101c40080e01c042040d901c0d0142442031300b18179201c18406d03400040100180e14101079012075400b000200c84c40b802e15049a58a034800c2d030144d4090094403540c040280f0105405001000c101e000c00c4404010030808081d0f4107803602d14407009010010b40d10804034690344d00a01010200e4400140034102d2640d1a54018090790025078a82e402001d05c84c000600c900310f1485513a0940f601078448007850723842c0140f88800707584800c845c88150041d4507401001a200d845407213018604c29190307000c0d56458801800206d0707000512188280e40030b100380111076101c2c00b0781d1026404030901c841d2090009440350030710f0050244c50702500580d000401c18000308a401400c0c2c0a40400c51440b400d4003d14410005030403900341014289003401c101141d0541001c031000f00300315a0740340011401d400c448207031300c44141c2c04941c0850460819540081044950711900807074070704d641010041c4000702d0300d8402c0c26442002800040c07040d608206401c0c0083d4140300360180b03400030225183d51820b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 246810089 1250 246808839 246808897
    0x702070e06120a0215191106070206100501050c071d04030212070302060c090409060501090c180b04030803040309090608010204090b0907080a020901090306051503120a05120a02 78
    0x1a1252440889005000c203401e0b14214002001e00d010700401050030905540030054000a030515040b109602002054802080b0304401b4000e01c1c042c0d15071a04030314035108068100b500c000d10040454200408000812151200070001e403a02031a01c02d480d06080194545041d45607041243c9588800c414100d640341c01404942c0325520960a680400c3d02c02c203200d00c214017440c00000d02580003800005c10405821002e48440100100042038003020354440300c2c100c400a0700504d40c1940c4900d004615960000c111a0382c40b0f000c1310b07a40030030318035240c035542c814084c80c00003d00300034001000c01c090600c940c00c43c03006405e000d8070820940f0f9a510089000b03500c24418002c4140c2410342c000301500c0c0c1200500d200c0c003010786800b0031a0303407401d120000039844003d50b141800403524002c0003080441c4a814400c900e002c100c271416018500401d03241ca089940220b001840400c03540305201d6010080ea120082c0c0344402e103074140c856060311800390058603041d85d0303125560102072980c0f01c0c0c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 246811339 1250 246810089 246810103
    0x9030f0606120304030b060d030c0209090703020901080309090a02090301140c071b0b0703030f021c0603060b060304020303160609150f0c02060c0a0c060b060f2812090201170702 78
    0x108031003981c41008581c080030f480b8011440050260009480000d406003040c11700070f000c80e8464505030705403040c9980054403001041d60b012040da44050010f00450401084a0303014000401c01135007803010b0306d400180410720040040c1159a0041520030141e10250800c070782816a01c1030002580c07401e00381003015a0003805050b034000192003725035030170210b06000e5058800f90041c3c5440c101c502c1d01c040d80504a0340c180100e1056080159078443c02c07910441d6908030110300f10100744580395080040542d0707000070015100d24020804e100c01641c0010440303592240340070080c0c10490040c01c05000801c0c01d8813003d020106004160458003000c1c3e40646001c10103402c08005500d49014100c0c1d0799002228060600c00b0100f0500401c5801920311100701d038030400d0040382c001e4040010420300c0e04214403802011101007a0510b0f90000c8044800d08032032035240801402d040890024412110b40e040312004c5075442a401041d64428807003001c84080140981d0414104410001c0d03035400d03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 246812589 1250 246811339 246811351
    0xa030f17010608010e061912060f020c031e04080d030504031803020306010b070809040603030c0515040206040323010e07150c020a0e0601020f010603081c090c0b0f09030f06 76
    0x2950310100466586800e000505075901070b5500300c000c2c1e0a00741609004403024001c80d078017080b401e400c00c40f065004001d01000c0d014281403041e4031012854000d0903101380104611459006110324003400c5800001e440b10030100880e41d07020651002c0c2c000144d4031443d089022680281c0d075100e030103150150005809039201ea0f5400285611850706104407507118080203505420003801009900c03500006402100c0c05036000628000c032040011f01111100c0d441100030840b2061070000b40413040c060b159505203c01d107400b1841c945580081c04910423404004c224554502885503200c004890480e00301075400020040003101000c0e141d50b400e0b01e441410442c8a04107400c001585c8141810144940d01501c6100c00328202414603060300001040c0a0452140c42500741300894240106002180038449003560342040c003a00c003401400f6000d00803505424080c0e0b103000228813408140482d5a04000152910002e5415800c1486944442540343c8219501c01c1050840030803810302890b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 246813839 1250 246812589 246812597
    0x130605010b131410030e0114010807031718010302070c050402070c21020f04020702030f03040f0914013f050c1e130b06130602100b150405150702030a030f 68
    0x1a981c0d91802c003200b0b00f800815400282441441000f64041d402076000341d500c440000c2502031130003043c60b5001500342c0c0402c1c03c40d4410741e4200203000c2c01e0303141c2d03030084905418018541404035404e4044c0c2100c0041d40d504066001030b000d020321541e04442005814018010365541c0340604020150300880d000c1c43c040300300c191010056030301105900280440d0b000d403070080b404052a081000a40201105a130103008a17285010f070124280000d00c050034000d0088a9044c0c140b640e038030106c3d1400784801025081510041c0302030b100f581100104c881201d03c2c141c030020320400c4c54070501c060103e06007400c48006c0d010142049808180981d069205481e410368a1040a0340760b01e40001710b902c0789400203096000c0c0440c03416140c0210b201070724003401403440c00c00c0a80d44100c0c0c0e22940e5200324010b8100c1c171b0400100061600804c0b48400303003110700711144a08042c00210510451060300e1080c101c40c0c186010b44440c0c04103603254150002c00741c2d40c151741c141c20058412650605200001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 246815089 1250 246813839 246813877
    0x1b1505011412061506070204060905010b0c0c04050609061210020414040b030106030f12030902060d0501031e080406030e0c1008011d010e04030806030118050715050301140108130605010b 82
    0x2060000f051445080e0741c08002a50b0100d900c180286035126600030398001c3d40b81e890118903541d150148600034243e00001943e10002c044440781001414840c0511580c1840280503c5595600440380c108104039103030101c1400015400340343c0480003640005181c0041800180000c0c000704400d8211f40650307041c00641e0b000302c04c06080302c1ca680401401200b1103011400881d00724440c150001c041030a00068030412a0000f8920340c01443c5049042d03a01e8000510821000e02c1d103108010252003030034030203d802583c5100f054016800b4004c01c065075003009d484400c0701000000010744014140c00761204420310004c0078240e0034082e40e10352003900c124040ca01608101090304813500c02290031025155030f50100d9906101504141d495921174030707080803861503481517541c0c00e48104010000316191110440c440c18031403400c041401000d1004003c421140d07651074045d000c00b480d2a200950320400c14900c41241d841020302054604000466082d1000c401084403004801e18082a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 246816339 1250 246815089 246815119
    0x3070902030f0106050703020304270e03090d031101150b0408120f09011809020d06061b03050d230f1b19140d09230105071b15050114 59
    0x9034401500e8000c0030b004040300410140d449180580a501d00ca88141c900d0725a41c1d400443e8a240c1c0c0003c0703100041e2144415506615241c4107045121601802640c01c0000040005409041e010405028000c4409047c9410002075028503d056000b106201949440b505040c0f00e07508240030701c4c00648648000d84035401a00c2040c0c079040012503030383e2450710483c0340c01100d01060141c074071181c50044520105001d1254009441300290221002545528200c001091008050840c0c042c0f900c1c1450640d0100384c2c400200d0b000e10401800100e08900a000f50100c0440c00b111060b6403c01000180305001640002c400d00400c40c6141c1e1003054214120b41803524403a50700d41c1a5075000100c040410580654514000d140d4440030103820110031035214000e860341c4000444801d90109004144018800170091040b05403000800003803408201c041c0042c2c500a49020b100e2140b08208420082042c00e010b0b00340010207006e10035542d4800400c1d9101c04840e076071601c41e0100640c10f0403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 246817589 1250 246816339 246816341
    0xe0303160f060b1c03030218150703030b06040b16020f03191101050f04180e011104030506010b0403080406200706090e090a05120d0902150a090b0403030801060f0c20030709 76
    0x21303550250102c01001c0031843c4c1c0c2d064000754400d00c0504010080d1100d095903903500c0c1c10341004d00d80803c5190f1642d404c12132034010203c542903020701d84240c0c0b050100740b20030000355017903a200e00030000540350513044034000585c0c0040c0341941c1560510030f8800303808410790304115410010744245003101519a89000540d1140110001e41c50904001e0104018800e8030300409904c0900c0354100040501d000d4500b41d081d1401004208008000082c0c10020404108825801030512074805420103042da590070ba5a8469413084008011040582d2500010303141c6120070000d465504039190141e032150040c1c40b40b800740c803419224440c46130000e13031032805c04940080d855900c100035080c900425031250402d0b810194840c2c00c0969504803110050700c0e050501a116a190119161900407640d00104031940c540c12241c2074480034841003000030f4108801d10705483c200c0c201a403e58101140c00c455141401001a10b0555140035032032055001c203403e00d410806c150192071071a511400c90350 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 246818839 1250 246817589 246817609
    0x312041806081903110a0503130609030804051513030b0703060b18041104172812030c0c02041401050f121207030908031b070f080d0e0303160f060b 65
    0x1501903048918205055a1541d0306072064500c2400c01d02118000017520340e203004031105c400c507025840001d40ca4080345011840e40000c0085290240743e41f8103503692803800c1d01851203624020700480386c0c11424034844070705541b20a2480c4589007101603503400e10021104017540c444000c07030f01e02400032480c51a08030848051840d580d04800031200118140402800040d504039012002440040360000072542408030318405c000052550310740340da0f01c005940241c0017607803413034a514201c0b07103002403041080e809c0c09400354100082c1c02990744209503a60443c02400030760080c81e000e42171424482181185044c2c2e04140d03013400d2541c54241c240b143c0c812200480b03282960000e2102043c1c2c5840000601c041b600c21303d00f00c1c103100d540e09042490f50b000152103145a41c900540c103040701400b0440e0030001c20800240c003a0a915182403a0b03150720105260302c040180072940c15a25407400c10444000582c05c0d03003003100884060400c03014081c01c03690204d6034241000c1c1d941509191440b108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 246820089 1250 246818839 246818849
    0x5010207170f1903200903060c2d04090903030504050105070518042016050c0d0c05010f0908190b0906040206121305060f0f071403061c020312041806 66
    0x418a0030000c520115110240b4103800001c0680701d1000d00d0140207903254441a4841c0b5405e26038a4400c617408150500384020301848005400344454040f1030060000c1641a00035603600c0740041e041c01c02c07595090b02c01c640202280d1414528828101a852f5105d544998014002007042d0303120080101c0c0e59101e5040440000310700c0c40c0700e10800e4641036022281c1e0032840081601401c00c103a002420581040031400c1d1214842038113201031240034030800401460403518070b203168055680b000e1841c007003030007800c1c104403540b0109090070340210814805801341c2000c4541444119011001450503408100c502424100100311083c1e800074810303000315801807546013450225811481500340050550710901e01610100003c0760051000310300500340c201000d6101e00d040c0010603500c100c06000d85041007064012070032002c00300303401c4d0703500300000301d17010406a107010341e03030000490303000030040e6141c02481000b003072902400e0020b0084400c88000442d0420030405d18004941ca10b1280c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 246821339 1250 246820089 246820117
    0x607110a240207180e07030609080304020102100e0703241d070603060b0703030b010525020f0909120d060b040b0a1806090e0606041d0f090d14030915040501020717 72
    0x70f102c01d130b101d40e6040f500c05172001008941070316949031034200035607981c0402515680d20020502c425968144280e900c0b1140030901445074100c6c106010ba5035020300d1101070304c8411355407500b01c960082d01f0500d2100004003d8244000804600e00d4465450b00000c460200d00ca0743c140080c9484c060f0180f2811510401903103401c2c05c07441e8030b041d000340a0a454181c1001020032101a91100e60710021480741d550341c02c0a2940201c52040c400003089020459103c2e0034144100581217038001076501c20000b0001d180c50b15150b1001e03105000d0000c030740042c0031250000c41d0110300e2a0300003002e01800540390340c03001c5070341c82c04400400c100324043c0a2100018048e0300c051103041c0482040304e820400181c840d0b417400d07544640b8140f0b040b84400104c680e41c400c120078043c8203881d414040d40c03c41a03213005031100110380c810241ca922030211100312f080d00301000041101a080c046040750310010b0601112a19182c60028000d40c8078482c00c42c0c820000d203034072a420350760042c01d41d2105810030b01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 246822589 1250 246821339 246821369
    0x16050a05090103060e01090807030305060102010c0c11010e030f0f010e0c04050f0c030705040914060f030105090322050307030f0b0106080610050c0703051906051302010804020607110a240207 84
    0x480c0320240c20311012070b105ca9034a82c0820b0000402c2000103060b990b010360360004990900c0b5000900b9a080301d8030f03810030041c40841c1c0001040ca140c02c040a0000e00f404d200c5091810400480e060203403031004c88281c1e018008030310755110b406402c0341c6c007100740031380c203403500500c40c1e204000c1102c0c0185c03548094100890001103c0948083c0110380000c1d040c1041410180d035000e842003aa08050303a203101e4916500140500c9080082c0c01c0c240603101200240070b94500ba03c0314568038000c0020003083d007107a9000e402410300c0400c0c0d505000c3c10f03025040d2690181c13a03052420f00090b861030308031003c02002000103a014030806549001d140010a4a0b1040d90703c0d00c4201c450b1b030005110948240180070001001400400841004004100084038054100d0804108450008101078460002c090600005031b03800404039030720950403200541c80d01c0181c10500e410711001003006401182076000411442600080da80010400e5030141c1005015100d00b280ca41280740304000b003c0002d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 246823839 1250 246822589 246822593
    0x180a020705190c150c0f0c18060303080604021602130203070f0c050615180a0e120403020906010311041d06090603010b0102060402220501031103070f0f09110904020c16050a05090103 80
    0x540c1c074008080061408901d058195141c1b0495000701c20b40c01c449a5164900c1040014003201d441c5000c0a0b500e03800300103592845d200500801c1c1e0007040c3c40d11480c1e0018110489440729603c07500e807290040c0a981c6c0d20742d603181c8a8002544103031791580228180820003041d07540300706079614001c2e5000000c0c02d01522a00c0900744454000303030314507900c1210403503040380c641401d0360618450024104082503185101c205581010b1440b040000c0d414010070040c000760301c0303a5680f9504102c00f8600005d03456425040204ca2780116003000031403803003030041c4d203503180c000c034682a028039011200314506403982c0d02094201e035a0501300c1c9015801c507900080c0035280c40e845034081d002150040390683d038a004100c0c42120b2007604115a00c00400814007090b0400b0400072014104400c03642507003600380742c440c021004540c40380e030403101e45606c640c40d20b0021715403d07600c00b240017800964998008120458840ea500007440c4030800d00024002040c0c036001000301c003111006031074681c043c1d0070740d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 246825089 1250 246823839 246823859
    0x150d09060f021207090603022503020a0503160b0c03060d02040b06091203040801060602010e06010b0c01110d090605070f120504110a0303080f0a09030f0e180a020705190c 75
    0x84005890196440c0408000440c660005041140395550310071000e203030050015141001e540c0019040600c103100815040300d0702e180319910b004015902c8807510800f4a800c901e819a2a00014410700000c035810054011401c00c1c00035141c414000084030740d45400d14494140030869207154812440c2030001c0143c181135200d0380c103140c4050145880c00500e440811884960800d42c0100741d800050f0070084001c00b0301c40c242c0031b08280d1000b48400c0540c0c410443d500d440600405901c1140010000e0b4454002d501460707441100e4a5403a0f02c0301d0f401c0000b035000b4001c1c80000e450250819000400c80c80c81460160124001511418030105840007820000d000060040318800c20308001141c0c213035501e0105800030351113561141d80b24174048140a40310100a0400c8003081d040141c1000025049050881d507005c40b807501c4001244104009903039510740480c8010b100c0f205600340918096150000c00c40340b0b0144088510054904040b8170008240740c0b03010700b0500e401c08c0d05006000342 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 246826339 1250 246825089 246825101
    0x110a0302031008010c090305010b040501141017010e180a052a04051f06031a04020d0b090103031124011a0705060f010303030e0c090a05090102070f060b0a05150d 71
    0x45a152600b0b1a43c440703100a00f141d03021019a00824855101001004400d0256580949080e541031140d9450b00c401c881c42d1003d11600180700e0381902c1c008c400914032441010095600f940800c9849507555010340e03d03803407001c2d281070030384100d0360641c0958008001105158940d103e001408031900d140b8152a0410400e4150f00c020169030001c0b4085942d54010b05005016005e5200002070102c0104000c04107241c0c0140145800c1040e100e8400882510300980006c090f54050b0b5608150f0141c0001880d240c0c0d040c5a00400020003c014941d20041002030807003c50101c074242e42041c200e80c203820461082121810308002c00601070780d603000c140700e10304000c2110207a06201d1241d90341400d016045842d4100a00c0100c0100b0034191305010726400307120000007a209095600d00458121500200700d40946500c0f040410007034003095040314421504588a1a003022241c0360000103001c01d4111a07102d4002d048011606180c41100c20706003481444030f451503c010311042d0009804 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 246827589 1250 246826339 246826351
    0x17090307050301050411040b030706090608151c02090a060b07020607020a031208190e03070f210302180f030304060305060d08030903070c080d02070306050c0f0a02030310050103110a030203 83
    0x2428000041e940c0b000d010b4140568414503014940400c104d09100841b00f00c1d0600610a03800743c241046140c0d040382046055880620380300c0a50b607070703d40036620184101e0300c0035500244c90000601100c0e088140c0c1400382031007200c00035410b031550148501500c04a00405e034146108204440041c42d004004010342840642950601542c035140c84500e00c007405440e50109100c1c800700100410b00701044c199044405400b005a0441d0858003941e901850200402d08040c0c41010000e0000030443e1003c07099118020013241c40d40c0d071400a0180d00280026162188944038002044c64982c825a41341d0b180178005600741850b0500487c007810340076051581007501040c4107004201c000c0c3c0114410b15074000110f82c1c40440b403800c00c0844c10564800e22942d0442c000d12041c032903000c03810380216604000089959107807544150114032a20004d00d10715040016810a0074cd00400518030400f40c40d0f440d01c2200756120010b400b654484d00d030901c6040380c200000903525009501854000b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 246828839 1250 246827589 246827593
    0x1b10020421140303010803040914010303090504020d0906020c01020c07050301142d040606060809060f15010e04020703091e050a03080c03130f0f23060918010618090207170903 77
    0xb4105994007410340c0d10a030003204003a04000790a10083c02030307015402c10340d54606042c1a880d851910b00600006180c01003501c1a1740000c5c85405401031070f00260076254000344215516040054041d0007075004203400c0180d40110500058640303011300c510499003240007150903095440e20416a41400e005903184039900f40d14000003255902e40345101c1c8120b1044400281c00341c2420405040300c0002051156030350700010800c03455035489030406400803141008551403500000042c5c1d0300d0864580d00c540c11500c00714074074090640c0b1011090443d081c0300b6140442c0d03010381c800030410118038041d844c1c0020908004000141000004090b60345020003075074100040103010680060140c0d1107081d180c242900c007440411040714603c070041c810f1148081c01e00c1d68215940060391020440740707200c0d00e00440d00303007501c1d0ac0300b04400d00318814040c9450110340e15154098060300a00134030040c26401c4207000b040014651007200c014035005800c12460564550030f00b01c50380c0c4a000c2680e018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 246830089 1250 246828839 246828863
    0xb07030e0a170703080916060e010210051005150403051c0c0221010c05160b13020a080114011202030c2e0e040f020a141602061b10020421 61
    0x45941101440340719001c40b01d10366500c16040c10018000000030f080004a600281010030400b8a01c9a11200700d503964101b140813189030b000140c3c00c0104500109134001e05200030070201b00c44507000700f01036a6080741c400074501d0388012031345035074010f9001c0100258040d00021003620200020001401c4051402400b00d910a9010649030440d5445080e0300280c88880070b0b00b102007c0c0034002001085280080c2010361480100010403480c12000c0d10481000d00410045200101c0840741280c02401c155541a80c83c1c40003402001030503042200d0364600f00010a2118022040301c4030b4540080007070540c0110300d41005240040c000a11160005440101744002080f0170181400b403001d446411544e203500084c4400d45200300e69105031107204100d210000c4d41c00440040b620184406215100c0b201112001407080030200040d5000c1c0c0c0204280c0700712405e8100000100d021403060718500b0400303640100681c0901c0c05035800c81501080d88140e42129036a42d6005640201075090f06 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 246831339 1250 246830089 246830093
    0x120a0603021005120601020118061d0f1b0117061c0203010e01090209090604121101180803060117040b010923040302071703040f050f04090c06030501050112090b07030e0a 75
    0x394651800c0b10710110b0804a000460002c110800c4c41e40400e080c0000e0100104141410303582607a00d0100030a95a03032141c046603100398a118121008a070b1404403001c403040304001640d69030401d64403213286400040094115489120340303120808004100c0f8040da1214000c02900000c44240390000300384030840c240c05660240561840000c4031000000c1107444e0b03005100d140d99006140340290390001c0c09010005848000346083d40c1660300e000c0b00740900e51001d031400341206099802002e00704852400a0080c0000250f0080300c0036241c507010700c001c25a40107040303101103a0240c611074600004001040058110004001c64039107601000652010f05445a000640e41074005074400034083c4a4404015400e42c1e0703000c5503100942c02d1074948161a000940e0070b0090760300030348407605460a01e40b2140c000120807580080750202285e2100801130062409100b542d000600d009074060b8440d004c0e1107a285056004a440c44a84d80c402e041030f80603100e44040741003035200302c542c8500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 246832589 1250 246831339 246831349
    0x8190207020a030b1b04080a030c020a030804030605070f0f120b030a020405090a03030e0f06010302010e010908030a0e090c09030606101e09061206050d12020f07080708120c03120a060302 82
    0x2c0514816950b00ca25400e008030648645d800b09041c00c84461070400c0103002c1c403200002c00c01038040e40f61500e82124200d520224402c07003103030746c40280080b50225002c410003035140c000b603100b8040756943e904c03206203064046500340021800d070b001003403e80b6070103416002c0c1174122005032071780a0308451030440070350701260481e0002c50391041c00c1e4105114500c205581405445003650310789c1c1c020a00084054583c54413000107100086c14080c00791000c812a07406030889000500f900c0050342e84600041c40007500c582040c0d40c102d0702c03556070381000502142466080d511b80001c0503006040316034511080c403e0000006100c0ea040c006250407010515280c0c40341c180c46410302d40c0e90f0078403141c902030000e098410309510f842c00c0d603400c0c00e2080c00b0740e403102c4038459012504141c0707120426a100340186e0508101500c40426809074580209400d040041e17030f10201c441038003c41d02000003581c1c021a145c0104044c0c1c0c101c0b90401c02480121000fa1060740c0d411020300e000000d017403036a9a002034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 246833839 1250 246832589 246832609
    0x30403080a1e0b0906010504060914150307030902090610020d140708040f0305060106080114130e0115060210050c0f0c071d06010e09010501020709090615141f0819020702 75
    0x1071120b03602c480c901d9240b8186406540d4020101f820b0042c285814424050402800d6024144001c41300c1400124199603510805d1948065038680f030b5524140400014081c00307a01400364011004c80c808a140b0303046c4000980d100403100d9001d4400103012a004450b5481e0340c400c0c405a00c0c02c18448080442d8010008100901c04103080224051651a21a080240c140e0212080c403550758010070111500046e2510019070072905030f61402d100c14903200091007039020900e4250b00e00b0700d078140501c05a00c00a41030b5422a02226501c6184165100a070b074821958800c51003424000301200305d407084040c011000410080c3e07040706444502101d030307410100303035a6120b41d004003091100c40d50b009200040c0001c41a9984c40d03903036051130000307556408a8441c00d80340d90f031f950840406100c4a5400054a4182c005100f680141d5880c0d4102e501040e11072214030403040f644020303444c10f40918034403c403980135031a01041a6500240005841e0070024807080700b640802c651401a62604498 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 246835089 1250 246833839 246833891
    0x101b0c0f0909030207090504021503041b230301020c0a06270302060a0612020a0302060a0c0b0a05010503300310031a010906050d050c120c1503040501140c030403080a 73
    0x41242d66420002e00e441103d9200103003051421081c0030258407003240803010f030004441401c5c1e0b20313140e91401c0c1002d5036090744160382c120400100810300c440c01071130703c032000294002c1400003401950201400c0740310740c4420b20b215a20945080f40003900a0300a18548000c0903410800386440e0350b80a0369040c2c1201e421001a000308040003014449071007648092301400300200594002540880e0307000c845800064403a002c04294070001d0f511658000b0a016804076000c1c2c3c481c18145800d0b0041d100038003400384a4014140c00d090401e8035505800c81280c900b0840c4041039507011680c0e0142c0d4400b600300c4082420101000c40400d441000c911501e40070740c58404090340c235003141002240e805401107407007507004500090104000141102d401a4100c490785842a0000e400e207142140e060710071a0450100c03c039040d8183c1e480d8014500c603038040c000a000d29590070f01d0b05280110100e405181400381400460003091081109592091902500042583d031076000c2c4d00d0b81c17050034855 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 246836339 1250 246835089 246835091
    0xc0708070809010323071107050a030302061b070f030c050c270610050d1d060702030406030608010501031e050a050f211e0a0504051c11101b0c0f09 65
    0x110b82c0a075916218501c010600c1c018040d48010880084080150001d0406c3d020030904d0003005618060902c00d01d002880010304c50084c103035403450065103816084400300401c500a0804000204469003120305460b40100d400528007180c0d6000d0343c000701c41c000c00f5602485a1248591942c40340c004041503101c0c00c80024000f03c102a01620104800402e00343c044c20007039094540d240e801030162403241e00317960004a00c040c410b100c040124000c1203201401c074415030050154040d0080300034019202c440e90184410740d2243d000c20f081c0ca000b840010515940c10041840b01c0742d110070382004051141c0103980c007900e195118107241ca40c554080d4007180e00300b22801e00c42c000da41c149183c45088101d4000703091050100c4082e480043e9a040518003140005100183c984248121400b0b008003c1480101034118110340340700781501e000c200c405008801c1c1c100014030b4101e18040c40000544c3c2c0b048814001582c0426458003580422201c8a4800034080b40240040816401512940350 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 246837589 1250 246836339 246836347
    0x1003021e091e06031506120a06090605010e07140a0302090612010303030203070f18030201180306020a020102071106180609030f060f070215010f0506070c0801020c0d030e150f0c07080708 82
    0x2041802d850000d44410711941c489401a41d01d4244010110f52000c4c0c01c54040341c80e8200392860314205001c80364001c0803280790180c444104001503000505941c031900071000296180c181c10fa440362035118469981303c41c00c0c405644224444c2c1c0041080010107040035040103003070880920003400a81040f80800c0e004020440030366805207039015420014a8070310b5901c1755088944501e07072030754040a410010201600c0460750101e0032484015940f06030704640c3c0310212a0000d00030b4101e1581203800501d104000b00c228540b02041d2072030070b1214506007040400200402180e80d014030fa266416001c1d140e80301c061101d050080071b1003031710000903d41c1d56281002d0300a007030401185100c2601c0c8400e80061001c0003035400b04400fa0341e000c0d1603c45d80c0361303d07070704003d40c04140607030240d0602d41c00010244000b120100350705010049503101400006409991240c50300347c01101121048100c030005036003070f4001a0314941148483e0006894a162902c8101203984103000a4510200010b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 246838839 1250 246837589 246837631
    0xf070803390d020d030605062d03010905070f030c0522050a1409101d060105120705190e0d0201030f140106110f010204030f110301060510261003021e09 67
    0x4c404800300b82e409183c10441c0c142800f0008040d40108100d5520462013002a03107102c080c4041c0240f407000d9003100d41c5440350303500c10000b0003034031086030400f00040c212240702003890301034050740030038018603115503040200c0000c81c000580740e8070046e00c80b50740441c0d00001e01510344e00000b8010708103c43c0155003c40300e0009100c0306d00c0018042c0c2e002072440305010013032076a04001407001da06191507200303480c0d19000c0040320a030260400b08081d11621310b090240c0d01e40c220f4010044003064040b055602e1820880076030701154080900c642000340e0340b9a4100541c401e42c005414286c2c81da0002615102e158a0070304143e500360002d2001ca006003132042071844041040c45d0b071581f01d8400941c40e00e030465645c07201112001c00000c00041261401401655003908030901804020b080d080c0c118400c420300805003421001100b0511154020501e0f0001c0d50040d03682c4100301c2402c4c1240094559424003540049150a521050640c5020101d199813030300d49203802440401d40401e40c3c1a009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 246840089 1250 246838839 246838843
    0x1d0603070e0103200418060504020a0c0201030b030f06010b0a0c05060903040302150a020c0603180105190b01020c06040b071b09091202010b18060604080a0803010303020f070803390d02 81
    0x11075240407010110b41c044c0b582c220010001c031015100380c00c8051030303604040030300c12000e031034650082644580041207481000354801b51100f00c0c58001d9806007e002c0540041c1502c07050385010343c0805400103001070113804000303801030030030700a1480c1c8000c96480c543ca4150401400703440100442c0c100080402c25440d1070130000300174412814041746002c601d558044d59a4445285660040001200051902607100303180040071404500034081c42c0392450a18580401c54504000014900040c44425510005490011900c01740070189403d060a882920329006402c0407980160496803500e6041c11854011008200c1d06c030b00421300790b02c40c0c6441c0c0c24040800010004680c50034040c103207143e84950901e101c8c00d248401007809030321000c1c0841d00f40e2046801141e0944604800345c1c0411041d04002c6049900036801e59a512407040c0c01c0a840741014424401b0b507134000d10005103030902141d40c1081002c9102e00d45600c00288a8407112030b00514840c8180c9a01b02c1e8210190302501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 246841339 1250 246840089 246840101
    0x9030c071725060e0105040503011a040e010b0901090203040c051002030307120b0108161209141608060a0c0201090f060e0d0f0903030c080f030c030702010f02191d0603070e0103 78
    0x40c80e081e50b01070090b21036100900d880c0c0c610503003040100e050302c1c035811a40104210741c0a418007400911103550040c1c00842100c0c410150315001d14030f072a0283d0f0071003106210741503001d40003c0095100703901c4d2418141c040c0d000640180d4907400403841c0091156030f121030981c0190b10700e4014644a1800b250f0107455103440402280c840d40c10a0000c10050380c0c00005c1e29031040d40d1100304681215100d1007120040c0d9034513150803903e80b03094000010310407a046e45000c01480c0c04c00b100c0005035865031040018025125002c0c9079804100807070000f04850300310102040c807038400002c1c0440702c3d858000710050b008100765074a0341d5880b44106120800d10603079001c00b8a5040c6200b140c0c0078040b006243d42454800601001251405481003003840000c844070825a01c02c0c2c0d5440b402c24007007020113907000b038800102543c80d21014070b0104116001b503404241652007400360092164805841c0704c1c1603802da00d100d94500c20714003412540d42c10060340c010440d569a04150108400015007103500c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 246842589 1250 246841339 246841363
    0x609060a0c05040f0b071704060309290103030c1a130203150f07030207031b0c0510020105010f0b030411040e011b020703020a03110105070807122d050309030c0717 72
    0x41c2003100b48a40030081a8400444020017441941d44105042c030806080300451082c0c00400c001500040c40f9900d50081c82e6064001c440340502226403190910559040541080d040358100c1c0042002c03a01442801c01401d01400000040f42201c1c0010001c0c001c045a00100c2c100c10b900c00842941410420401184803269039a08a41080c0650400d46080100355000b0143c0001c1d00304c08161140e940b041007070a0031061445487c01f20726001000e03c01074091980520018522110f405105000d100d0484041d084600c0c28141402241e00c1d03c3d0b07100a1056982181041205140d502e8602c10f825085400e00e00018040301c0c0841d0107021680f074000400304640c4180e800f400540d94019078041125445000041d010b5a01c100503603241c00307031020161034164003090000611400c0c1001c41521100750740c40040c020441d144069001000703810300007030303550787c28002135202e4000c00c0210b8101011404490410410000c514609401a0400300d14007d030364440714406601044a541020 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 246843839 1250 246842589 246842597
    0xf0619021201050f0109170f24010302100e09040b040203010b060c030d020a0c0209090d03050c030c0d0504020102010204050a0b070b1e070309020d06061e0b0a050702150c0609060a0c 80
    0x444070058100040c0e2040c040d0b6445180b00101c42c0c0030580c015a02e580c000c00d281c1210b140044013451245481b01d03202000804075019403900200d90b41500442d1709400c111140141c003140c0d00795024414250288080310050102442000c08141d803205c120324401c80c0714a001c4580752070035205050a44500d045000d000344004d0108010011b8007100352120740541d050b005840314190042254a85692000650032400c2c1c042844074903080450461602401da840620003130721246220070301e41c40101d030700c0d500982c400d014191000300d403500095085801440058142519080051903681c1d0561081d0003009000a1013401c04c504846120f91000d11600074070a680b01c00600105c8904005050804040d82c0f41c1c00b5100315590780004407070b4150400c030708004094840501c0c00c03880c0f110140c0004502404000050010b083c841200c80b501d04a03544e0b075091400c154288406030541110800c2c1001e414082c41240e00000c01040e441601d080340140b225007012206a01103d00a051801c02c00c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 246845089 1250 246843839 246843847
    0xd0315060f1110180302190b0a021b0d0e090c0304020105030414011e0e0c030c010210020a03020408030a0503060108151e01020a0501090c1d091c020f0f061902 70
    0x454000c480650410041e003400b072445003101c40d5603401d0140c0940514201407a08292414014038240c2c54442c0d00e01c82e4013210211001c52080010351803603048001c02c07603840080010a000880d4014001c0c40d00b02c801c91031303403100400300085d042000d070307840f040009440003050100301d02e8048496030300001c1030440300c5c0c80c504040c5c000030600e00c00108040c003118540c4070f24038003030780702540300c1c03011194400308000c05901c0020f614405045a410041218130a140c0d5a507002d1401190400362803405800400001521240078006904803884210916600b40b20005a80b6003d00090924030f029558030f9507246409000941003035005000c0c004284800030310402203840e4a8410040310f21550090b0300e0820030030004070701d00765048034005c0c41c07075007040b055070200040e0407103010079a5844170301c580c202c000040c2e0361a04440200c480d890581d00104040c0b070764a1a11448a141f2039030f40c8191901d50803c41148c1d480c03e403107104030800c5980050104034581c00001d00b45034405010311003e501e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 246846339 1250 246845089 246845099
    0x9030c070b09130903090e070315050405090d0e030114090a0507060516320f190f120504030507030b01230d170d091a060306100e0408070b090d0315 65
    0x600800c2c0b00d080d489084e13039a0000c0c014140204c4450380188413a42990121340b13040900280030300000c0c05001e4000680000124040ca0a4001d1384d1148500d80f0080403840b20040f41182c0581ca034040e8560155a94007140c8100c5a480700a2442400403c00a260103405403804a207018142d40c040d008008051041039824080c4420300395043c2d0b013001071020100c03c611800300e6400d01031040089102004681184141800700f0328910007650001540d055101022040e4400095800c1c000e0403503e05000700000500b41c0100041c8221181c0740213030a1940b030741e9620b407502c100e41e041600c448000500400c8110100c0300a51410300d07003448d840c1d0f00d062840d03000c91a011b0311080014a81168071b4140341d900b140365020b40301c030101040b900f8041036203d03003810b41d151140011407050300103401002412905001405034042d400740f100700014240b80c69182c0c00c03c0c1102a0007162420010000c0030003003001e009601d4081d03c981c0c00500440e000c046d07809400c4070300e6113840b0403441d075940c00100b003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 246847589 1250 246846339 246846349
    0x7021809060106030c1b06150f0f050d060b030d050304061109010801150309121d0901350102070c080f0105090c0f1210051902031515090909030c070b09 67
    0x30449402c0c0c180410600c01a00c0244c485040409581c2142e0780b00c0e946e504180031082e041544010380101d031804a142e1940700e00050003940f0b005501064014180c10801400c2c140204401103003d100c00250385403200000a0404080016150020f070003c8203200601c0014410403088405111802c0d01d0080342c400045d00c065814401d401048034884120145035000b5002055038030307400000c0661010407140007800c1c626644001300c060210010382e4a040d42403c002c00f0741610200c000401072410809160350700809800d116500000000c43d01c8101c100c400d0000c0d0144510409420b00040d052101c1c0c5803030080000c1e0801080da05000a1001c03151020450001c9071000b0345203250303e41c0800740440c0003800380c03000d0840720b031007141c82c0e880007800d296110074020540c03020a2113520021001ca117003640001d813945034030b0301c2038004031305047d1a0142075085070590442d2150305244100e000076107201000c4039000d01c2e81c0c000013190840c0600074890351004e4070181a00500349019800410 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 246848839 1250 246847589 246847591
    0x207060e15091b01020f1e070b0418020903030403060603050312130309050415050d0c060818060705090a0506030a06090f0204080c1201020f040b0702030c010f020a03080c0d0c050702180906 83
    0x90849502d2420004844e44240801105c0b8089402180d00100c1640d031035140002c1c800070091003034000c4020200359112a40125000c03500c0e141450f60941640c90301e40750080d03110360764160781880100000000a031003801164019400b03000a15103440c0404c40345407002030024003400b24080300d00c00f0000040e810041910070741d0340c280c9002412404500e48030158014640246a004050b056200104807402c01524140c44288c4d480106507103650003126000044c07a0b002c1c0b016500141c0000d44042d201382c0281c183d5170b2005100c012104e07030300c002194165005480031501c0603111034040c00210303075030300807400600c100f0703601140b902c1c0c5020710b85078580034000070091041600b440b20402c0c0d11003d4040d554400f03840724031143e90315512207a0b40101c0e13003e000101c0c002e00851040b05410b601400402c06201c241d034000d0007640d05296800c0315118401403049030440028010500d030301da400d208604500140ea00c61a5803401d0500401902205a0180c03200c4003981c00d08101c0309840104043e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 246850089 1250 246848839 246848863
    0x40b0303430303051e1528080c01090b07150f110d0b06090a05010302030606090405070f0e010201050c1603090e0106091703090a05011107080109080406120515220207060e1509 77
    0x2040001040d2030019107400a1900c0c4606040c5034100b541102c1a040302030141100d461008a412710500300c00152003407803480c0708001e90300c18280803c1c1c0114091580e00801c040b002e40001030486a203040c0201229038102032035000400104020b414000e0718418a9010354040398483e09148088001804a0799a4050a410035130040081522034a4450a40f182000010420f02071442d101e040103000304000d0322000c0c001460840410b0081d401031045034000d1005941c580e1901c0f403080c16402102c0c000010031410051803410000f40c0208902c41203000e00200d6885c10383c05032800714052807161180300504031641041084030080e0b96641d036214100d41080c20482c0000381c00c80051402c00202c2d502404c080d5003002d004c00100701440005005a62080d103488001c801c4040e41c03402140c108480c440c0201001011114840c9480d074101c4440e9400c00c08440459900c10400c2d2050360846070080b203180303884242e80e48818406118440075800d00e11020f040500c1d100f0301c03882d07480c581c3c865a = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 246851339 1250 246850089 246850111
    0x4030b240d0204090f0f17070309030f0302030d050106090f060224100f080d030507020115050f060705010204080705040c05030c1c020909090f0c040b0303430303051e 73
    0x1d040440d11190407102010b0380003000b03940700b00d119085c000c80190040c031048034040420b0601c914501c007800c0944003400d8059584800241c1140e80e03544402c160703c00c0550640c4070078400810740c05d8090241c207000e02001da40b91302c0c00b1441c140108604c030913950801400d43d0030960170159186407051030415582c10180140f0080e8840d14914031000300c1750341010001310360091021601d8007002511882c0300d08550741c10440381c2d0f51290200e00302c0702d80301c540c94000c0b030800340c04000350300c1d03c01d031042c1c41980000c10162604da0300ea56040e089a2055000107416003298108201e103140c00e00c220040280e540c241f5500d1454400c4482001e80704400395444650244c0001a100d000f20f581a10703101600640300c0c9210b4102030030b801da41c41400e0045e015503442000301c0703400d150a06020703400064001500860800019819200603145030b1086518030115180d1401100700c113869840342c0d10340d4072081d002d420802c241802001c0e07502c000d00510400c0c0c01000d01d61400007008011560000210305 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 246852589 1250 246851339 246851359
    0x30a03140f090a0608010501080606030402100f050d02040e0613020301211b0612050a0c0903030e060d090305030103060c0216050621180610030f140f030f04030b24 72
    0x4010750040c0200b2007180c0d08182c3d90803011500c113400042860686074240c8400d0a143c2e01c2d00e007000124442110025004203200c04507012b0710340500e0360410402c1650600345d04000c9070101c844100d8026601c400d0780e070300b40c0c1e02c00d0082c01d003042044140d041c40350017020b614560424807030803800495401f20b200403540c0300407020180240034200000889180e40c40e01400f03991035400070607038001043e0000b1102e143c00041860700c0054828144100001c0e150a0b03c642e1031500c0c2618a8409000065000801006215000c50302403081103119442034640c1c41c3c4035415814094121101664024155807103040c009c03140303005890b0a0780407103070116481556194030a5124600b1540e0400181c002d15010050180030300c10b03030318900103d242e4081110603950301c1c1450403140111070b100150101e48403500030310200d55504041c0d850b030860101160381150f03a40e01054034550082e07074101e01c0200041424010010300d0140d8030b400860300c00b03524000d400e40055002d94000f81144092290340414 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 246853839 1250 246852589 246852607
    0x40617091e1906021207030c140d02071a04030f0203030907050f0103020d0c02030414030a081803030c0a06020a0e042003090c030307060c02072c06040e010504030c02030606030a0314 80
    0x542669a420320010b00302c030018501d0680040d400140c494218121404001044248248154085222075954251640002c1d034644038865202004c0d008005400b0001031001c2449401d98810340300790f48030980c9191515007002000c5088401209045400800c02d0100c4c000001460780c0680d0011102e140d1b00c0406000160001d00c10b840013100e84a003441e000398130068022014008a801b09a0080311541071401010344138032080300001e141e68010320040f1082307204001030405044010741143c0c5460780400403148bd11403170b5034040b500c843d000034210b11072952000c10042d807040c066a06000a200711643d040110303010f000703418061000440080d8080c0c2d0200110510708401030142d030388d51b0070f5a080547c050424440d64001610803580c00240c0d20607016003401440c503081020700203071380e0030800e2000c404402501069001d51200c1c101074080c1001c1c031405010383c0c840d0b00c44001c00881d40c410b240c14a2001040b180c825000000340d0b1010039000414040c000110708800c1c1c0e6180442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 246855089 1250 246853839 246853843
    0x70f030b01260105090a0309090603081605030c060c1305040b0303030613020904140a23070f020a081210050307080c090a060e0708010f1203051c0906020c03040617091e 74
    0x148034000b00560030b20302440486140850000d9250b8008d40d1281020750b200e5200da0f09480f030350320008006680c10050010a40030810071520042c1c40344091741d29040d003160800c2e1420304d040d10003c200b904001041309010b042c0340382d1035004003425a0180a00078180b00001e0300c0c1d0100804060280211000400319240355034120f0384c0322540100304201c140584904046003800469440d8000d0346080f1004421120701d2100c40114400f40c441c004241d43c0b040001c07221070604218440642c41900031a600092204020300603000042c000013500e4500a444030400030f00da0340c0010b019030025a070a00c20b0a10204141d01400230503201003101d038440034541401040e6030340c04a6011101207040c05402c07075028442c40d0484030442d400c40101030302c0da03600b40e100c0c0d600c802c4001c000c2402000200c3c5c001c03000e02001c1c0035285044400003a00c0300c1c5034407140d081c0d80c4075840154190f04001800e001007030700304202c0f841000a40c4100c48892a0660159540b107080340c220040882c0140d05202240100f = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 246856339 1250 246855089 246855149
    0x602011a09070302070c03350403021f021c050d18122001450209070e0a0303020309131e050c0c01110d320a0209041409070f030b01 58
    0x20094808404900c0b980308d201800003106070260515010b03480001424943d032040c2c80a59800a0001c908402005455002d5aa540070503030198064801d007ca03209201c16040d01d101c40c04e035100c0d981d41d0320102039040c04840038148881d8901c4601d45650010403001007414000440a0034541080c4c0340d01d07d621101e200143c140c0004941c20070804110810a801000300204440311841c0204110380308280d5400610002000c50070900c40046405460f2103003009070424a54108a80c8411414021a000d102140c00c290090f07031001407450100d00b0907503220f070444402c0c903804004c4c0c1c40c9955420a0b22441c0500320740d00081c1c403a00400d40781c912150440e410581d000008111141c04102810266001205034450081c0b034509140b0301240043e80c02240000b0f10500d810100394401001d259062000e0f10100003103a00f8041c605a83e00d0f1031049400c160f001c0300d01c4000741c0c58030031103540c5807000030740000020440c0601c0420001c1c0000e0b0003d415076180b03c0381010700c0c0a440d1500004104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 246857589 1250 246856339 246856343
    0x40c050d0203040c031a07020606013c11030f04030f050f060106030f0b010801080307060c020c031204090609020708070b06041104120302100510140a03080c06010602011a09070302070c03 82
    0x1c8004144020003245050b480101d0348540d110722032114041c104100e1000049840802517040840017822641c4100d4a40e4400b01010b0007100e44a0f400c001c14127107407404040244018107819400050080e08001d0b82003006030729100031442c20b1f140c400400b6041c0141d11004103291030103000034003044018041c034518818200102c81c034a60791500003c1c041c10706d00e4104881c461500c91040415403060100e54181e60100d0020f500e8680d40d603555000402a1004000440c010289200f9141e0b80030b0040e08490340c00980c0c45a151428407a00b01c048551380d9001013002807040141e00c1c006507815003641c1c0d000c2d03002070420109941d028045070203403281c0080000460350025020441001502c1400d82e1140254201d40102080d0f14402003254000e0318a0150588802d000300404034100c2c1401a40711405442226815075030780d200586500b00031440046604a4801070005590922550140d0801c41d007003102e0001c2e0460202d4498040035152800700350700000c200c018400301c68a5440115 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 246858839 1250 246857589 246857591
    0x1b13030615030c0503070f030b060415140109080601150f030b03060c04080d09050a05040f020c0105180607090506030f0619151202072018040f1202030711040c050d 72
    0x7425540811462407250100b114861950300c00418a4140010b051050321404850403035802e08585480c1e030b10800c01020030303501c00c1d11070003111029004180d0380c0000340072111102241e0307103402c00007510b203083d0342d00012029485000104001d1601d046240c40c07242c41410300418204500400702c001d0711030300c1461909885402d0500800e4013980e002032044503546400da6a0301c00c0c0004007294151354501ca8141c2c05980d000041c0010701d00340c2d10a00034078000610040c648aa0032280509440e411900102190516140d05841c0300091001d00d0344124207160031004c0398242800036940d0300000d090030303c903030b000040040c0447c0c031400400c0c00c0644000c080c021003241d076650941e22071159000040000b07011640c2418a2011a00a460559038020180c202102c0143d007144084c20a840f4025031007034003111443c411010102040e03018030301802e601e03141c5888505103144d100c04860b03021403c40d401045808081a210341c50714130a91012680481e10710180d0804540c180a500304183c001 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 246860089 1250 246858839 246858851
    0x60e0304152003090d061a0310020c01050f0c0a05070c08160306150305070311040b060f0909060607030f03090212101506020a030503040b041a180c03061b130306 71
    0x10316040480480b59040c070758894000b180d01800c1540d00e0340540101c44d81c000c0034004620307002030001e80005060300d2003070443c1318039a603000e000240b5119440451040050340000d0348421141c0a00829030f1104980c540344420781072401520480b440307071440100c100000807a00c1010070401034003450080c4100400c451007905180c2000c0f004280c144000c44413a03250030041c1400320a05298041103e412401810026185884500e58454031440c0540c0c041e68034481d0300340305c0d652a00500503400780100e016071900844000d01c007480d0000341403281709000c00e120400000342e100c40030900440b441d190108140304180702240c2c0b032010083d8401050301a8109020118240c8c2c1e00009415030381c0180d00e812541e1f90042640c0710455200c7c003030002042000000c010550303075070001d5003040c81001c10358244852030f540907280c1c1d0400e6450301c03101800235081c0c4116080400020902d007208601800c00d40c240000b80400b29404070800241391440031450b00c001030801e90240d0011a0070000603c50 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 246861339 1250 246860089 246860129
    0x80403080720031609050c0d090f150605061602010201060803030910050f0702071a0f13080c0a081915020d05013b06030a05011a0a05031207060e0304 66
    0x55402c03050030209109004004000303580350000341d01e9040c031029030500c0c0c14a41085030483c0a810010b2014442042c1004150712004591240340c10482c01600240400c82161800c0201c20b03012861310800b00d81032560600c40c954602c400c07200c030301e009542c1d0652540c42d10300c010b03409404154003200300c034080481003218a600115182c4804c03140340500f000740e070359008907444020354165121401648030600600920081780c0c880d8610608a0440d039060944207016403045500c51500100c0700ca0300070386c1c02c20244070100841156020b040702c04004842c1003452113942c030343c6094281d50399091040021003d03c00c0255584915020f40403096688014090369100504001e200300030340c500320051503880c0a10b8003403201d071040c01b0244032003070056000300181c0f070400e80103442d00c0d501d8000e0341c1d0410b0000780c00b4410803a1079035005a0803c28994003c00300034a038100b075440702c0d00a400000001d85180b0000e0100c4621607802a0700042c406d45503940d40340b560195801caa81851304080406030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 246862589 1250 246861339 246861353
    0xa080f370f1203051e090d0302070f0f0303020403060501080309101b0b0f040b07110c01080705191e09030302060c0a030e06070e041a0d0b071e0e030f1f090804030807 73
    0x8420001101c0860019600d5a02141c807010121b03485a0180c000d024a031006501c20b8008220460041052100346445616000c0882c240c001c0c08038046680003a08004100315409940d004080800281d42400d0780d417404509a141c3c1c9a81d003a0801070000c0302c0c00b000c0c18404a00280140d000440c42e269460007104c0840b582005a40503200304203500e001401070351045400c4002011100013030906c0507500c07801034441502c05800e060a0040503c400c7e580d581c8104401d403d0004559269a0303004003002c041c240d801d100405160030000d00314401d1001c00d400080c22070700105e0850032180d8030071481e08114020b2070541003000c01d0340100d400f4030114541c04080c0c0038041c0750484041003d001c0e07014030290000741c4103003141d420201d100d4269021a00001c82d242e441703031440c02e040320080302c0b1801e103000b580760031484800407920210002849080410110281210413802070101d200d1030751450803802c0c021644181200d4a032058101000120340c1680d00070b5912111881c1c8585c0c0c05c0c64006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 246863839 1250 246862589 246862591
    0x714130b0c010506040b1e0a150206060a0b03060a030321021204110a051e18090d17040308130f020307150e0d0209010506090f0a080f370f120305 64
    0x401d190f00700004182c0c14a4a031040b0b08000c0001040c82100b40d40c1e05a505136070314400c0300300310741c0701080c0b040001e0b840103c4900d0300111202d540c05001c3e0f62601500308100e4405036002584518401e00070041035031204a400800d5a8041c1440010040040c00340c0044c490881c22030780d10301d40082014180070030240241409281b1620303001d02054210824401c10611074800d80d50b00401c14000c0307006840d0b4039940c070342038050042c00718180c0c0a0070b1070000c4034803841035a4800311984120030724841c81b82d104610004028400700742c02881d09081d18014070014019241141d0140c4101b075140030001c60198120001340c1c0035081c0c0301c2e26035039020b8601044030030340240c1c000325004c00e44201c990b1402c00550700ca5280e00610300100f907420030050112039041810b00580248201101610b1643c5058a100081c45068010900040c680d0910340c2400781310044401107601519007000c00c071503525206030520b2020402c50314403d410381840c5400442582016003900004507400441c60f600d07030803003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 246865089 1250 246863839 246863857
    0x1503051b041b110d02030c0709180f0b070201060b03060630010303090905090307150c11011121100308070303020409020d1a0303040617100b1903050f0f0714130b 71
    0x164000181182080c6c0c0c0303910034840513074120740201d2000c0c452140e03242e0103002c1818603515600701c1c50403240c1e10003001b100001c2d41942d04405400401c000d1036424000c00002c0c06074012100c1c218109280401c00d103004007080004034104910702c0c4114400c18031881c1003500110311704070f000e550750b034200504401c00500a0100c528140701c000340c1ba0110000841d03038020740c040c50701c003041d1810b100d0343d0000b4141240d8042c10480741c4104114440000d015440070540d200703036232136541d090070000e01c5c4018207030054000c800035520003000b00c0620b90814043c122038000300030503903070082032600310000e00c01c40e000364010500c041607580207500d06511504d0700c85e1410028401ca807805200f0180d40340103a119a4000502c0b020341003209088050318150406640902810b031203031a07140e2114039800807020603110015844c178244034075605005003a0400b070608000381990a0502920300880d4004102c801440644207007409a180128102c4041110f0b410502c0501c030386564034402c10782d001c1d15003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 246866339 1250 246865089 246865093
    0x509011406190e0705161a011a07030819140f0f091207060b09041103060105010201060b040501200f031c05041502030601120c1205161e02070e0103080309011503051b041b11 76
    0x300383c3d011051b481407d00c0e100381030024108030841d90101c507200c50040c8020a07000001d401410740e00810301a0803030103c80343c00c07023b181d03280022841d0b01442006007103c0c0320460400c14045070110102d00842d0001c0000f410a80da50031038100100034240070b0545a0300480c014040206201401c0c01000e03203010118295410b90340c1c0c40c00124243c41013801042d982c0103041004110350b600506003400184010100d1884942c00a40f107107003447e0104020341c4140d040000c0c0740b02015004c050641218008800400c010b08290b100c00a403611203040c888a0a0760000202d1400c0c0c0c0120114040c58020200910042c84040700080099020045010443c0c0c1030a020810040e000d01d0804840002584d8071191100d030168400c02c01e218140110080d8000e44801055504940800074042c1d03018119155032030808034503045c2120081a4103024002c0302c2c14052001074408122010703500000d804017481c1d11101c4000030010304041d403142403404c1c1101816094541c12102d1210494070070701c1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 246867589 1250 246866339 246866341
    0x10e270c0a02010f09021c0507030c090c0207151403060402090915031209090c090604090606050a1b1101030f0f0608100e0607020c100e040509011406190e0705161a 72
    0xc000c1603e114100c000e5104001043c3d00415071f4034242080c19050044044801c0e55540c0c0c0c841a503001a5a00000070b040e495051410086070100324840040c69500341023814110b0f00000185906200410741d0040d800c000082001c65845030140c40b10400c0050403032085e41805404842d481c007001448074042e00841041c0c50b14202d8980070703201060b1000e0440d0615540f10410182681d0003d440a940040140004110f001c1c59200d1100900101d460703076a6549060f04003d003032145013400c82e4281407402d4160300300103004810810401c24007820702145070b2101f0181d01020705040780d2080700c201d28020f000110601c0010340442c400d0440c6200300b1000c00340404480d29481c04507004000b5910007040c041007414800c48606074504c0d58070740385101c9400400000c0a030780042d1080100d5030344420300046500102e0882940140d0201d82a0b000b03140e0054485016500301c2c800c1420103c46200003c2c603040c0542c04580310b440d03100081050071485803074104e0502c1d10003008a580c81302d07188 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 246868839 1250 246867589 246867611
    0xd030c03051503030301120311070303020609060a0504031215050607050105060a0509071403040302030424020106140d0303021c02030f040b090a0b06040b1203040f180b010e270c0a0201 81
    0x60002c24640d04060040c514503800c0010816100786840011400c00070b4420300c00c81d0600c1c042c02150003551084d4054142c80c00d000d111349250440c040c000c881802e1401080c00000380d00300100c807072000006800030030014074940342a41c0050725035000c550004000507000d0100541235000d94070440c02182d8105507584c646080c4040040304072103220100e9203129007043d01d42601c60103580d020f44644101da103000d490f500c010b44810808500d036860440702c5011014031940a014000c00317400c045200c80c0311a41182c000031911240d01c00c0107404e0681c00581000317003203a00e0a0501540e866140300355070b41d05201c1d90b201650b0340c08441c1a40d1308103920b00440ca43c040046000e407402c9401c01942122510b03113604110091203400c2c6541c1d4800312540f0550000d010a002900080040043c400401450415070801010180c00c0400046240c06542d0029a03088041d0081c0100280e4561100c01d40e020010709520100ca40e034003802512078010045000d101a0040c16501e606500912030f901030701e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 246870089 1250 246868839 246868861
    0x110f0304081c2a0c0e01051c0b0c0a17010b0403021806030a060506031009050d0219020d030305070203121609080d080c0309031204061b081e180d030c0305 68
    0xb0b0150380c001a0840040c2503501000d6041020400c0c0304442c114403035046945000071400140d10000c1e01d403028400420091a050403905801c010480c6507030080c40941c1d4440c5e00c011002040750002d4070f404100c021895209032440c5030240c629280c3c10300d00b961103000c46001500302d488120310481d060300c411b0003c401c5444100c3c0c01250050014100c105003a40d484000d8000204103d801d4401c01404000340c032000d000d05040540510054000301c0310266000341000c006402d02801400e110400c4001600e404c4081c040103600752070001a1920ba0810403030951003010420600081807200380101c1c8c44503800c810a6021260710b03900c0009582e0104940c90301000c0400c4408107500800003803034115080c0007164002554010350f403030301c9800f88051070b144c501501c050740e104d682c902c0a102c101600d050009120111b6052980292608800a1041c5103c81c4401c079800788031500443c0411801400c03080290403c0b4041d1003076030b014298000d004242d0030b54094002405e240100c1c0500b624 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 246871339 1250 246870089 246870133
    0x90601050607030207120303020910080411030118060e160303020d081008190606120303090b1305100c030b060706140c03060325270506031605090601110f030408 71
    0x4160003828070341d0300e0508041c03502401e601054041c5602000030b901203541b049602f852030300c85c07a01e0b105854202070610039900085c25146034042d03890320007403221711320b5900b69540320325511010118044540c10452030034400d0080458005900901011040640220300300c5403040159540140d9030fa20581040c0d10080b281c8a090709541001101c0300c94512552008008240070b61401f113465907451000b03171000310b42c075041500003035590583c0320100520314010581106a203210b0303001d144602d84905407107600d207501642d0041e239100c50b1070f16000d000b07401120031100c004220548501c014180a806041c50001242403180c0080002e40040404000d507409400c01400401904c501d03460401f082d005809400d44020b600c8920000790b80341190300c942400409500f220100b200f051801a056900141049100e6001892169003000c80303030121a08540045500200d1903c900d00161101c950100c4040d0480c0280b143c21100c2000000c01442140c3c641e404071071412034848614809110 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 246872589 1250 246871339 246871343
    0x90c061204110103060b0a030b040e030a0e06160506010605070203010b0108091002071b080a050708070b030a230408040f06080408030c030606040801021207030f09020a031e060212090601050607 85
    0x420004075021494002c8024206070b0181400941c141e22003112110f2600038201c080d00007522400756003407500b0180540380c810308d480001103040c90032020b4080c06058144141a000c3c2c00042100d00040042a400000c01c079084026201c003540c652400400c2a03004c000240d0180d800d25881002551241079110b1140d6001005807a41c2950185848081d606c103880c203442c3c000c420b0b203002582101d9505d0600041c103041c00203085003081880c100d81000c5d015030005000c1d07080001e0030000c00a10f40216940700c0000c02000030020f82910300100014101c003200c540340d03100002000104011000200252103507090200c00095498404544042048400030140c11043c00403d591b403900c3c002440c0c010308020b01080c10940c5070800d1501320f8220b90340b03d840f201411824010055098480e01e1083c01c1daa99090003000140c1d00400d1080b11107210040400b541106501182400300406072000c2c1d50100081d0356a000070980c3c00605a410744010324640214000081c041ca8054102d600440d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 246873839 1250 246872589 246872617
    0x21060b0a1106090c060a05130f0905010f0b0901030f110d2f07110d0b0408070b0f010506160c090207140705180a052503052a07110a030f0b090c06 64
    0x21130b00a06020070368200743d0b0302e0f00a11006114146c400b098001840d4090400034000400319072401d4603100640c1c006910540717910380002414400e81001c8011110302800a080200d0300d01d403550040c900074650881e911100860100d0814540300b841d400942e14680080030051030300c108003201c118860340c089940c2070510003c002c200000369082c10b40004c6000003c058010814003a1188018070780c0c04c4a0440b0f12280010383c0508100c0402c8005420040f0340d08414950340c14980425902d10481d03000e810119070782c52611040000b103d1a402c0030784100082551038102c0ca14000c082a490b44140300c00c0307400f440308040b8450800c1d515003803a042004c50050f400d500ea14260000800002c0c003291890203035080501608407200000360000d1495640008551800c86444161220b8941000781d1a1515035841d142d0410450141c0c3c0115800214030284a4507402c00500e10301c07020b61000b00303400c0441c0c2d041c400380484c0e41c8035503100c0d1200c44150b60400741c003881080710381e01c244d040c120100c1c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 246875089 1250 246873839 246873853
    0x60405011407020a1719020604061d030f010209011202280309061503021237020d05060402010906030905030706020a0e0301150f0909110121060b0a110609 68
    0x2584515103000200701d41e80990762410030642c0128518420075000910b2841d0f04600303040113084104108152a40580f8180219865640c000380040c032480c4200000c120180d2400322850b044d00c201801c00d08001402c0300e9940304858a114040e40288440d40e0200c0d4400c3d032001e0425001d40221041c001a02009613881c42c65501251081482d0240001c200b6a60354500000100180700380c6c07520405540b40b002100386541304101c3c01e5048400c4d4504103402100c20441c03184501c4a540b08000c20009600d4000500302103465041401d050000c1e503c04009072003101840300c0800c07102d000394002e0ba40c00c2941900d4141c194180e903015280181640d00401885001c0343c4581d011b00304000c218035003048088138150000e82940e0421040204030499036400b080f5092036161131f140200030005080c4820131300e0352180c0c8406141c0c800004c5c18007028903070403402c10348011070030a040c08800404004094030340b40144400d801c121030000105886100a09008100281c12885081503500900310 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 246876339 1250 246875089 246875099
    0xb0904060903020f030406030501090606030b010807030b01110709020d0e030a1e09090e15070212030f0709051002010501060216030809100302040b0f030421020d0f0507150207060c0306050604 84
    0xa1025800540440c010401a60104d24091004000801d41c5603800b06255050200728801c46030254001020f140c606901d03402641d03001f58603c2e50000c002c0c01d0018020108000507141c16001851514240c0a0000e0116050750154050302c000020a041040b01c01c0c5004685907882c800c08810801082c1255880c0d0a8150013509807460200c0070b26220403800d946801550554500220440b400e810950042d082c3c04001c0d80030a502c082c944c80100300c03403525400311900350b21010f0082c0c1200d9003070000103480207028102c144000d00740507014a10392261542d00030300070f010a0241a0060042e00a00d44040105411400959400c490302516220b16481008940150309601c00d05140c1c090200084070604400036010411040c43c0840e601c1c40c2c2880d03d1041201100b01070440950959160300c41c1541c0000c4010711039042c5d0a21039541484030005480c580540c81005000c51800f8141c0c0706112004c0c1c01910300c0c0e030321605050248062003541a030136030b4200d01442d03411100600007009 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 246877589 1250 246876339 246876341
    0x90103020d140102040b040623090f06070203011b0504090605030a0c140109090c020109020a300f02040c032c030a1206090606020607320c0102210603100b090406 71
    0x111070b10311100014070b03250303413078200c0c10b0140c00681c001070201c0c0c0140d4130b9081800300d04411800d82e1880302031a510782b88201001039031581800e68124001e0002041510464900f54440c0b000758550008155003042c4865000f85550310034001c0ea1500e034245040010345080004012a81c540e200e080c11040b24100b810308a11300c2514100c2e54104600c0c07a400041608180c80b51203401803443d40080355803040c600602416118a5228011060f8840800c82491911b003418005d420004500e00b140c4080605040c605500c240c18081e40c007901c0c1c07240414a96030180c3c000170404041d80c1c002210303105c508404500016400c3c0c180502c54000300080c01d1964440c1c18840d01e00b1141d190f001410580f00c01c242d00840321184c10080c0940d00c00c0090001c0160003002a8030fa051540302e28036100400e0709003803990070560b019414120800400c24a16201c000e4041e511040c0011800084005c040802004507102c1603031858068040c54403114044501800b030300800d600c0c00f41c0710a00340d0301d80350364000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 246878839 1250 246877589 246877613
    0x20a080d05040f15021e0304050a0323030c07060b0301020a020a03110f060c030a0b060720040e030309070303030510050d0b04082503140304031d310b090103020d 71
    0x201d20700030f003880500000d4019102d040308020460001a11180005103a01c160b0f0a42c6c901d02e02c0c8844180200000100c00191503503001c0c0d0701d0701e4a43d8142d40226440d00440680d140d50024210000c8100040b00030498003130001c141c050103052004007a0801890300700e1051105980050b04203a2800300841c1c05010700c04581103804007120000e111394508241044000c0e20702c208583c5002060041d80040d90140004000b011128981b5101d103690359044480d14501c44c91403040401c0c02d203984640d4032580400b949041140940e03540385000d400c0151120f102e40000c5000c2850b020100d80d0350300c1c0401a1209a64011f0140b034014411070300c98501c500f20080040340c00e0007040101c1c0070030f450040e82d0207454001000150688507018640034245500340d450628070160b0074020880803981c080c0e009000f0036122004803400c1c600c42000304803560820782d0a4075111568810000d0b070441e068180d000c4030407000c402000010a05410440c2c02c04003840042d50003039a010b002408039604071211 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 246880089 1250 246878839 246878843
    0x130c020c06070b15210106170601050303220b0406030509060c0c100b120a0506090601060201021206130b04110a03060b0a08010506031f0e04060c14041a090d0819020a080d0504 77
    0x2054221451010303192031700e040c121071895503512180b08201c0c0390407203541c2031500301d10140980310380d605040c04a90349026090301075010146107484c0d0020540720f07e044202a00041c50803e5a0342d80781c3c5005409041300750f4084066220381c000055004107050103a41c1040c10304409007413400c44c00342c03440c00909400050213a000707003514440706074038100304004800c213031045001c4d0005190500101d800d103c8140c0c015403d5900411002c540c100c0b0815030194840720444004690007070043d6003c000b0300c0e003541d000750003038689005882d40e1052807000c0c0081151b2aa401d20125032100e41e108014051030070400301190704400180100c2c50310fa80515802a00421a4104c03280754898900c1136011580c041815254410103110030700040d8001d1651900d11802d149401d1400d035040c00d1036a02c13561140c02c0c20340c8042010052074002c4501100c0040c9002482050003000504150b00103500030344d42000c00c1c440e59500052047c0c00414155145030304124402c0c20420f8000c502000390100800c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 246881339 1250 246880089 246880099
    0x60d0902040b0a090510060206061c0503090a090e010e1f0b180403030603061a09010303050a02031e04091b020a0f0c05030f10051f17010b130c020c06070b15 69
    0x3a20405485801c00b001c0104000607005c102400c0125a4010840654005d002150042c03020450280c0b50700c900511b10203888130160300c1ea18003504209080d40a0700c606554800043d1000003043c1a158101c10b42412514000304a1003007101c1100da641d043e034145428070301422001d0350700c1c103100d079900070541140040e10a030080403d019600354403080c11242140801c0c0e94203010b100b403024500c20b24000360071035001c081c00000c525000039426141440018104030b00001d0160005100307000742d030503030160501e461408818039480591241c00c640143c4183d40e01e03006000e1074058000313010302c0b0101d26540242c040c803010b6855005c888441c039081610b80109014001600e501c0402050410002c200094040070b004d190072542510380c041c2950420545c00d116030160070f070052006004a903101c40800291001341c81059025008290145070f001044203460304414219400c01079481c2d01b191b098560a105170001c01c140c901864001522452022000480740101c5102302181440c000b00 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 246882589 1250 246881339 246881351
    0xa0c0c0f0b07030501050d08090d060b06070605010311090103080a05130e1303030b0301060b1b2e0501060203121801060305060106030204050906040b060a120621030e090402060d090204 81
    0x6030904442088501107840400040802002d643d00d8451280505812a082c0303001c600c054881100602540c00ca82e03106101040d021010800d01e64820300702d007400940107540390006400c2181c014a0244419035046050800d416058a807000d0b00034103032a400400241080b18882044410f0340190b002c108511a44031404101c0507450340321207114a03202e040c1c02c1445050342c034005058401c03802a550107681400340a2040a1048050398104004210340d80056890301c81c03a01c1c030b481601004200e080b481150100350040e411612f039169000c03002c10522042c1da9035072040360340303114030b114042040400f640410041707030544070485c5440081600100d04a030300c03525410f0a01901307a01c07840100307a00050802007810007407074243d0700c10750884d001c0000c0e040c03c2c8080360300c030300c01c1c00050010003400000c1410341c042c3c1d650194016012042081848581e051000b4481c0030b0000307015408182000c100d030003140f605807001d80c400e550181030f0302d0401044081c014040c0407448000c03a40661600 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 246883839 1250 246882589 246882593
    0x130209280e010b0a121b030c05042418120b0a022a010c030902030c040509031603080613051006110106090203041a0906010b220e0403350a0c0c 63
    0x81d0704240a030102c110020307a40e000200003c0c00000c070751038a0300d03460390414400c08002040b641e0050140244ca0901180c03050030300718225000e1096030004616140001c0900d02404500039201c010020107440702d64440d91816100210f03401c10341b240d62514000c4035105e00c0050a0100001c1d00006460405810480300e20545020018030b8022203943c10030402410700c01c5442405019140025820f00b00b207441e04a80101c0d45400510006600843d11200030410b03212080045400b01c0310303150120840c0751020714004211348020f03500315100e082800780c07410355060188906401842000c0d80350b40c1d66480c000c0180e44074440c046110009550301c42000a0911180c001144624441d00386140c0801038070004075540e0394082c20103550340d8171031001070080d0076594088030100c20401e0720716070808001d02e043d00380607810364203e03a00c44940101800100350b00080c80503070883d005240c1080000c0344034410310900c20780c420352078454801c91000c60220f60f0030381c0c0408401200d43c87d000351110382603 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 246885089 1250 246883839 246883859
    0x120316030b1c050607140a05090d02121b0a0b0405010c030804020a090603080301081203071209020d0c060e120c010c031d0613060f0c031409010905120106030213020928 74
    0x4220b05450580021080240c0a0b600150443d002c018200c405030401d008407030010180c0c00350b10f100f02e00074000000d174081556980702c0c80e5401090a48104c0d60140c42c0f0003080e4200070125148640900c8048078007007080101e41d0240d13025900107949074a24002c142d141240e54013006082070760031101420740491081b060b0300515000e1805410a69600e5142c81c5405151594142c5c80010080050080c400c1040d404004100088000c820104000c58107000040c000490300f10003d10310030030818009003403500a01c62120b5120210340c0b40c20305000c40308915450b09882c071200c80c0040d45101918001a003d5056001c00341d40a015441007814000040340d0240d00c07050300d00040784c46a000030456180e000c4a005c059121500c1c12100800c540d41c1c1c0034003d007440b9044902c814002084080d0325174403a0011000030700d80100001448410f07040e0b641e00800c0a408142d000780002c560310310b03003501d90f80200c445404000c0d00f441924081940055505400c001400030025105c2d1070000d481010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 246886339 1250 246885089 246885139
    0x60504060915090515010f0b13080d0903030e01030902030d030905070b03041a1b07020d06141f05010810051009080a050618061b0a0302160602040602120316030b 71
    0x409030b0024454031241407092034001c030581c05003d041550001444103a8036110000d08503000e4402081d22003a00342c02008020b15960807c844078032035440302d6041e00c0d501012510803a8000d4885004e001d503a0001102943c03035040e0069050b80c0300c0242010503034421b901403148a40101c00f5580c500f0f89494150140c1e50081e05c007501c425020000403101c8070858041a6007040346090003d00030311190800e10b899000f12800644a034410384403000a008064010307242c206580e00e8120100d1400103034258a104006000780a801564040400c00d035000b81c00c107134000d03901c5007131402c0340d140b809040150f00114204408100149000005880403042102d12a0329108001901e00c03460f040c0c080903040981c1d0324552115070700c10401c2c4087d0313400c108420410880110222a6a00b8000000394003034420701d0100d01404141c40d00030410b2240c2c0c0d030701070825112039500780d4040c8800012288501c0c0026201d40e1010b00b003d21500507041d000390b0003550b8072074010380320003451440c045002400c030078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 246887589 1250 246886339 246886373
    0x90715050702090903211303030b0d14070603050106030c0e13020c0a03030b0f1e01080a0b0319050606060a0207060e190801020d05010b181c021f0e0a0605070605040609 74
    0x10011070f40146c0550b0b440044d8011440c10700213881d00c2d19040700031007080000c082c000340901d075944c0c1a0040d1502c1e1a804040f005801404c3c0c46032070071011650341c5d80c1d10708038450180000c1ca0032001188071032181c091014102c0c1c03e6a100a10701049004002c240001d64860b401e030b290b4200003500c0503010601c8480c031000e01030b4600080c0f8a00384000d01090300c00d0300e0409446000e00094803070011210041018000600f0710304840c903a41d4a200f11001081c00a040c654140f18090754003a0b00080400e0f03180d0003078030501c280d41c226103500c024020036001c0c8800c0000960000601805001d120300300000c1e000384010705c54a4100e10041240d44088070982019016035000641d440c2904001e0140714014076440c400d80d4030307001004040d01c030013a18842d406882810354807150140340041c24120851681c00400c01039141040c10540f85072105001c00610219000c4031455a0301e190111041080301c0e25031b01d4280c0360000c2584d40da001414002e00449403542d0303400c06480841d000b134605e200166 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 246888839 1250 246887589 246887593
    0x1403180a261c0c05070e0708010b0702030a0b090f010608120906071e080a0314011a18040f0203100b0403022407050d0305070905040203060a170327090601020102030907150507020909 80
    0x4005414480c1c200107580d085008071b80c48603000d0101260b805203d640c11600607060083d140c20442c400681864840c5101910a280c00d40c10f001c441040131944003400d00c402c00080202d5940d40f04199103a0402020112011105210050443c02c10100800a10b80b04440c9d0785040700c0d500010f9407440d800d00d1016220340101103200b10100d901840f60000c0080b0651003003240303600d0180e6162141c40300c40790a5281442c0841d824140c043e08008620581000400a01c81003005044880094100721544a10f02414030000205103000c1301c2250300740ca402500c8556030741c0845000342000c041540d1510100c1400304100390201e241402043d003d014140d40120702c90401d007400510075956900715900c658810020701166980d00a1000f007254200d1046200a5400c0450a805c501865041e149407010b8003210b04602c400c0407d150352503040c100c61490080d128280128200c0c04200e88070441c56101c004103101440b419280d41c140c0590600d807880c50411194007040b003070380c6d080e60301003016 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 246890089 1250 246888839 246888857
    0x606020d03050a0e0a02040b0604120818060309060c031308270a0501050712052b1a0906010309080405030706200c10120204031403180a261c 62
    0x36450b002d10398102500020a10407541d0b011003c0342c0b91440001c009208690700c80c0b44136815107615066400610541a40038040a83c42c100f105c11540301e4507035407201040265000c8141c2c03a00703d050f28040c5540e10001c103543e5540d1a68040d56070303c0038210001034048285881300041c0c4680003010340880d0700821089240d030403141a040098021043d0748030b00f0b8210800d0140780d81c00320603103210325000400f400001c00c002c0f1054030244200c0314140e4910011407a800302c03000d6807000d068085003064400f04140303811200c1c540c16019440f680258041660804110907622940210940c1170140c0680c070714056a400009151404d182e21260215000c2c00c90541140000f514000403245104c0c080d000010885000500509007000d00c40c0500000307401c01860401194182d1b4043c55100d2104c0002d100c132010b07170360740c1d9410149401d902112296004081410b008821108403070f050f2014040d00c0402d040c0e060322902d40c4400040c41c4e4446d100c50a040c0d13601001905401d02c019884481d06c2c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 246891339 1250 246890089 246890113
    0x1f0c0b04081e1812030f071b03050307051501230a051309020306090d02030717070c0303031a01030e0601150e09070309020a0f0e06060a110706020717150f06030f01060602 75
    0x70f800e10406a0601c941c0c2c00c282c440b800e11501008031400c00c4c0200d00c0301c0d030391914246025a04181d10304124140f07140486804000c000c400030091002038003c200f160100b00c012010343c043c407007003400382e8500c40b9010304440c0825003000d421500442c1c40104800c461a44860200e141240c941c140703805101d445844080541c1018000a90400c0c4001c4c007419080e0813070031010b541e910491030f0041a1203440010322350b40179650420340301030320f5009030060841507580c10b00070040d00203100c1d14541812141c540fa000c660007031148c464006808805004260710b402c840015034000c820100c0140084140380c2c912503034500c40038520401c819100000d5005460040c44680b50007a000702080302c91108040c0702d020184044183d00100c210b6051b0303542d002003c3c00700d40c0101507510144962180f0388021503500d0300440e0309000e8600b80340c2c10b000d056802142c2d899442c5103002d260b050b81c1c1142c0307000c56079810042450a6200e00050212040d410710304201b02d0854205502440041c1c2120042c001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 246892589 1250 246891339 246891367
    0xf01050a0902030c03043306060f03020c120f090a1503050c0a020a1e050a0c080f1605040903050c0a1a070f0f0c030327021f0c0b04081e 60
    0x8003404401d00110304510300608011002e10000d4800740a0b04420240048171000a03400d00c1a40c100803900000c2110f00068840c000c0c2030300340a1000410548441030304135130b10a01c2680c83d800c40160082091400641441e00c02d81d1101e02c0090ba0300c403003040751860340d445215103040100345042070283d1601c2c4482c4002d040300c40c0a402005982c82c01c00c008900c1590001c2c451840c070390003e924920440c1d00d00c2e103010b4120034100008250303000f1140c41400307201c4200d101d034046468403010f48140c40746041c8490f44503200082c4107940502c00f044140076a00700703540500b0344144282445458008101880c1f0302c1c01e15454011508180c5400036104801c4041040c00d40058040c01c1c05001c0036003e0f84040d142a48021880003084000c0d8411010326100e5013202c20211b504880081c00001e1140c0c4090750081e24400aa009601e0618801000000032546c28904000b035528018149090fa565003010880504180e0b5411030030b2014201007140c801d00748400d154090141556003000350040c2d2 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 246893839 1250 246892589 246892609
    0x50c10170708070c0b070917010515101d310f0614040e0114160206100317070512040f18270f050607050408060a05090d0f1101050f0105 60
    0x4420410a401440703515600210840d1013070b40d025100610720790701c0d00c000b01c0c0d03801c0c8140c0c88408092601001140342020661001e405495502213070a0000b000405000a080d45041c091000548501660312001110200003880c110010941c0d404042100080002012a5502108400080151142051801c0c419801c0e0342288501c180041d5245c44840110f4180301060140150380390000240001800e41c809849000d401c812106107013810800e074008628480610000b40c401e4402107001d02808904076000c59511009000390031f003581c0010003068100c100110343d00c0c0b18405260f90016880000340010300720411030091624500002c07058903804500c101c115080c07600c0c800130808403002044142c0c46203920b9131032081b258545400401181d5004010b41203000341000d1100c5158000d0051045034004c03c00c03030750f880d11400c0e0b11004854060758480e1680d0311045502c0794003400b0341036501d018030b884d0800c881210f0070b100601d425106c0448600c40c20701e20001c0180090f140c40344900c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 246895089 1250 246893839 246893851
    0xd151409010501030c0b03090a150e0c120303011a12151c0b012709081206030d080106140705060f100602120715020f0a0302030901050115080f04050c1017 68
    0x303102c9549941c030b41d820100301d280a0440c0c1210000001040c3c040100540341d841f990160300d606114a0b41001f10000700b540c414962043c1c000d6140c04881d62401ca068200007500b03103000356107143d10304928400c44480d9206c514403560307410311001148500f5116070b01d104641280585540c0c0d800c2a081203110344071a0094030488011064643c04035459000aa040d18000c81c83d1065209480448104100701d115004005600f03010a0508100102001d005420307000401c040c0c2d19194a0201920b032040203611200007070550300100481480380320301ca1790034085000410301d0415a501e80034101041140e81c038050300c7e0f94100b071105030002c4060382c0d4018200ea2001e84040080b001000c0c045214401014043c20803084007010710244d40e1707045800c0015911591503940150400c0500079410440d90301d44a540303010300004200701c1e100c2030b01024500659440c1110b035a07682003024051005001640e286c0720b01c0c030003015030b40c460b03a85110710034074141c95000c000004e50200041091004040c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 246896339 1250 246895089 246895091
    0x9020d080a2304030f0b07030e01090606080606040b1003020304150207050c0108060306090d0e060909010e010603050f0403090501081e0c1c02040b09060c10090b04110d050c010e0d15140901 83
    0x1000401c0d0340c40701100c0717040d80c40002ea42c0e00d038a0303009086000d8198507907285640d51828000350704002580d4016000c039050201503520b1942d81100304411513601d0200242c0101c840c86000440171301c00e600865105114281c0c40e055402c000340004120307004100b0032503007640040752002c12981c00034412a403101044009017800d00d810707082c4c9502d62a210a646050291150340c3d242607560700790075031301002c1c0c1c083c005400b65a911041010660400c2c421000420b00c1c01000c901c01c0741c400500d41e4891074164449034445880d20004403241341e0028400c116800f800012401c1485149651074011485c214a4503129040c1411506000d000d0b10070345040c46104000170404d200c0c076803081e1600300c40e04032161521403040c0e14000381040d00b13050301160a00e1600045100300280c1c140503a0055000d0342254504640d80028415030709540e003405403681e80461184100c540c418006810001c034060114154102c4907540c40451100e030282c0b038841103884071003e0028010b078905041e030007003810700 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 246897589 1250 246896339 246896347
    0xf071509020a1a16050607080a06051804020d140f0f07080601030206090a030b011e140306012106020c030d05060d3216030212070308030a09020d080a23 67
    0x400190108803610803507080084410f9009a40314010043d1000340550545000384458103141581c0c480300102d6080e400300b0003d002040d10050544140790079100c0252540c49004082031301440751800003081240d2124004c40480000303030360039448480030008203004002e40c84101503000d00f081101015070f25254440b4408000c44400007807082c0c112034041e140c03e0380c0c41c152440032924034003003900054201003121000180c40514040d441c00e038241d0450010710031585440d400c00381d643c8c518107040e074950f100400600090100c81302149180a411400c490102c0050361404145d80291403074505a81010903c1d00b1f07803649600466900820442e24000d4112550303032000d840110194181003100d44201e003c002070000300001020413603040d400c40320001884541031901c055940401ca000b5551310030b07500058100002c1d10011360707500030b044a040d0760750006094000e0120080590303000300080007080100360220001c00c50444180c0c1ea80b20640820740d60881070f1404150303600c044090801c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 246898839 1250 246897589 246897593
    0x170d0e070515160803060d080408070503061303050a0806040e0709090b2a0315090115020f120d02070215040e150a030305070b07020a120c0507050d0f02060f040b0f071509 75
    0x20010f00e1590740c000c03219501ea85980300030072800a0b050400502c51f403400035001c00c903010002002030407913a0480c1151031a1342c0795031540400c4462510002d0200d0302c24032440e0b0940b4018050a07501c0800a0400a04011042070003846c10309203a2020201d1561500580d0074000d421007464be101c80300401404521060885022802c8410b400c448007249001c0013150109411400001c10f07803400800004c17440d40c503a00740840c40d4141c074103182c000d4402c40560111080d0081104042c880904146030f09000d214000c1001a500210049900084c0040000c00d05480d460160028025040c0b010950385043c840e0704c0000b0016007015485100403071820000030341e00400f101c0720075504c1000d140441d06c232000181d10300344000c1d00c0105070b500304610703030b150883d030004c501a03900740a5000c40342810799404c240100201c0744d041c041c007070801304c10a500150400000500c0c070044a0300045160507503c0080c886c040d08030410011081c07900245030414001a1100c210b0402c05d141030400c0503102a03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 246900089 1250 246898839 246898867
    0xa020303040807030e04020a09231e0a17010902030f0a050c011209140c0117130f0c080a06060306050a020a081503011e0c2a170d0e070515 61
    0x50000700701020003e008010184910000c05820802401c25522178074a01c2c0042c0c4640000d0044100d48003d27055007240b40b205241c00040d07110005000b280d0b1031140c2540c2504124540115a5085909400001900041781961007429901c1c003000244980480c41090308021201992240561224081c000400c4021900201e103080900b0903074402411b407030000015000046000e8141402002c1c1030007038140c04280320048400c240c0c0d0303106421800340c5206010904c1a2011a0f80042450a0000041415141108041c002c0710000c01507a690140351385403848000c81141c034191540410001c20006020f4681c110348030b50b9040d4100385039140020062400100310b11680b4402c82c07400e4100c0c3e1820f50004c00800d17941112000c00d0300c10b44a038440642803110314440003460304426207000d030319260f40c0c054041c90300400303503a409115511841d8610300e81d1240c0d1200070708100515030609a5034883d40580110f1300b8084e0440f14030f842d04111411444090000c0b01802c2000007021410003 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 246901339 1250 246900089 246900091
    0x1020f1203010605030a061e0e10031502070c0e04141605220b031b0a0605070201050f0702011403240f0f0607080706060308030f1311091b040b041403030a020303 71
    0x804d00c1c00740e072241d0f103070b28904015140355800302103002d0300c00f18007540c400c4803000c01c4010ba62080c0a2401c0c181c0360350020319207082c3c0c144009020011004004942a0304980007000030742d014009500c0056200c2640c180c481e24240d600b1201c44129480982c0c01d1030040c041000500802a07203420003624200c00300712002c028441c440c01e003501e01c541c0c1100014143e07001c1d099010010301100c00c0c0300285031072800000802030f5a40d1244052103000a40302e0701c40c2d07045824459041c0d44450902c403401141d030303080c0e17004840c00b00c0c1030200d103c8254502010a4002d14451212400d80341303031000012419000d2090344100407401948071114103110f945680034843d2a010f01a5441e039500e00007410410500d000c1c3c0c00700100018200203001003440310020146009002c8101a040c3c0c0e6143d0540c1c0d0000c03080180002032180d400c03d902449185401d48420f17a110782540188041100105031924207940660403840603d000480c051021680c0d89101401c44982030f801186860700c0040060742c1c03804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 246902589 1250 246901339 246901349
    0x40e070302031501080415050c0403030e0d0201090512030702100c0b0a0b09010b0d0204090e07052704170702130615090f0b0306130207030207031716030305061203030f040201020f120301 82
    0x12000002c18200029400c482190003640e010800c03513814405149c01ca680d0041c401613002074207800d00781c20546803101110140340e40c141c6031001b080b4030b004140540c8110a50491080340130500000000d600e410031411002400e503034541c2003081052404100ea06000703452801e9292412202000548a080c40345042da42d0303781d8919140c0c04c540d034540029200759040070030000c0c02d200c0e011000f4500010a10140c0308104e8100c01d07604420303880481c8000300130081c3c07c516800840440d001c2409003104515100840c61031610740300042e00443c8029200741d1280280075501c18080001e90080c0a103010342020900d01051f02500c6c042840460207064054002120000000309000d69610700804d60071030341c041c00c195222481410041e440318007910064900780c02d80c454200020951004842c24080301c0140300c2e44c10012030301c0440007000010085034011030621750226030840c0400145100d804840f18003902d03480c246c800281458807400c003007086503200001c1c0d50800418a402d0740e064030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 246903839 1250 246902589 246902597
    0x1e020717192301060335040302010f0e04050f160509011e0306031506060e0d05100b012f0d0e0108010603050408070c090506090c0c0309090a06050303030c040e070302031501 76
    0x402440e44100c80a401c282c0301014a41c41c0c5600002084040d070381e5082120400d040342088400441c0d28002c02405001c03824050250401043c401580149207140c5054420714161503c010703d20049070403203d0035070303841c1c40d40c400c07a200f049500c801c441040384600c0001e1510034146041080041c0c80642040f120302400c0d0600d0868800991180e400703100158ac01550340214000020070810040406002d2036000454819848a003420118084103c480c3e00400415480c41d01c0703c03845000340503070000345040018071703d8030380d140d0310741e0390700b1484261130110700000003e019000306031410391541d2206003401400700010410783e0b0031010060450f42141404035480d81e440c580200f540c864204010b250113440000030601c44034550005200381400c2d42c0c504215200e90200f45040e010307524109005500410400c081ca040c0000034580200b1400d001144541c0c65a00090a58004031004000e040c00814200002c480301040140c100d11f41e410114514200424a49440d600b61071a250500c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 246905089 1250 246903839 246903863
    0x50405010b1c11130c0513060e0918070b0a0504050a1208220b0a050d0e06040206180103180602030f010902160b040312051503070e10151e02071719 65
    0x40c4c503100304645003008100d400f00a0590b490002a10b1904100101c00800c1d03002079010901ea4080c21264680c50001041200d00f503644ca11a00d0f01c100201e03d03903000c01e000300d2000003200030b00e0001030b10f01c42e000d54448648a0f4145401d00c0601421940300c5130003240041ea02c000841c1909040320728842c01030b4400326584665130450028201c10364407240f609500042d02e030310611f0b40f1074081d16010b242d1010030312000003001161580d5a1054802a43c454420008000c91302e480c41809181100181004500c40002c502c032a5812101d40710b041c2c0d00c850300041042a0703000c095200300d000d4040c2c03c0c005c50070140442c1e14614154a0110001c0608020130041014140510696000100c1300001031240707181c00c14070300c0c44035686035104034040d229803040860243c3c442079803180b160100a030762000301c910b17107004165001c1a0300a048140041d215205403040e038a00421413546280d6002400100d10f00b1503820450701000b180c0040540100078035004000300c1013003014a0300d4010004041c8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 246906339 1250 246905089 246905123
    0xd050304080703030305060a17120c010b06040e150306071407030c08070510050912090f060c0d0306052e0305180106080a0b0a0c021504060204031401050405010b1c 72
    0x2a511850300140301c03511850100000300340c0d158210354031401c4256600c0c0e038520795811006241844428510360385070004c0660b42040c440c5500640703003002d44400003042c0e120400c0003040a650050300400c5004005038100038074075054581c1c03100c40703400c10340007400c0a241280c4020702c0c140d001d0f201010200000207201051510a45820103046e400080032540c4102c10714107140c2c3c51000f0b030710f00d466060405e00000c0d8400c00101c0d140e0724100805c561a03151469150030004105810403055a01150500107103c0c030300c904100c1501044142d4800042032801c10081001e040803030b040c070072000f50070240d202c8818841c400d88201ca0b0f1585d82804a03941e100c4e0042203400c00c0880d40c04003d158079142c00010390290020300c44040074013604d104a100d446100102059408da0100b440260380300c1140e4424100c003800c02d06521030f004203001802c140d01e90303864600c1d403891f01e0281342c080e81d110741c00d0000707029003031040e81400790049880c0300e0700300c0761907031052200d100700314010700800030800040c05c0c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 246907589 1250 246906339 246906343
    0x606080c0105041a040e01060210050a0c05070b0901020d020313031404051f0201060302220501051c021507020402030a0504350912032b050105011205180607080109110306060301050d05 81
    0x6406d902c010640c1c2d66171102002540c642403940611003040c1004045408401d0320300c9040341180c0660b071028030b055240d88503031000b15006444a0002d42d82044840b4a060052000d18062280100103a803070a919040c000c09084a070402d603080b03d00100410442551141d50214400700740722456050245000f100343d00400d040d900c080c0d0490041075035010700c412600c41e400140c040d802e074100043c0c1d0300d5070140321600034682c15128a200703107081d40b000945401e605032040008800503542c5490710550224083c1d8005403500c064494075a010311041100901c95a01c1d480c80750316460f40404600c044d04840140480c400c511801030001c0e840000c0c0c1c41e1440d20103200003a24040781c0da101c000c01c1c4000e1541980390324181d20611a00014004400f840c000c050403224140d50311002c0e11441c841d018010f1001520401c1c010042070b6403000529401d0015a10410b6542c6a500d4903601d000400b4064801051064802813030400c2009481d684500582c0e041d604150f0b6005004652031815074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 246908839 1250 246907589 246907597
    0x4080c161202132307090b0715050c070602070804030b01080c01080609090a1704090c0c0b0c0904061e060224010e09070b0d1a0616060f1b05070606080c0105041a 71
    0x40160781315001600d284c401004841c02105580d507805101c5580d01900c9480b03011380385000706021842c041420304071055030401c5401c05440500c952a0919076a55501240e02080702120a05030129040050021b49254140144100c81c040c00c50900ea41c00001d102c000020506840344103500041500507130700304001042e140d4040300c60401c0d00682040c1041d1900244500b0b003c0710f01b0031148110300c80c8114181000240d1000d480f0059444031407001e00a41c008035159a0403ea840c04001900b64040302d200401d08102c0c2c2c2d000d01c0d182d09008000b410404100298200e404400c10548241c0343d14903000e034112804c6d40e8204860791a00c42030748c0c0c10f01307401c1c1e03005d00c41e131503008205030103170a40750780c0001502c005020342c0819444810052115a0103064a454103420200e145071001c01e2294005200c0c0b070301507010024044202c0c0c030404545072140541075000407408120003040010601c6004050603501008004400710000001c0c420320480c0140101004c402403060001b840840c151 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 246910089 1250 246908839 246908861
    0x402031e090102041503050108060112080f09060f0706050402040c1d06030402040b10170601021c08070324170307020d0219050312030703150803030604020703090e04080c16120213 79
    0x4031617030104545005015180c280544000c2d401010000075402c3d8004406a80f0755901ca030700c41c0e0074040f25014200b559081201c00c260031690412400c0b4041c0203841c002c241d894814500050241450300522007200c0014000703200740704240300c1d41000300b00207c03c1a0b6141c40e00310f480e99130b250344a1010070003800703007501aa0b422181c00e08084540c5d0f1742103020200740305004000076080703540f05001203984202d61046d09001c0d50901c0410b2003010300c5204082e51140350f40c20041450315005800c4000304c0341008404184c1d440005061000b004803140607181a40700d00001e509194881d00007034500e0400c410000d2003450a0380040382c468045c010444c0007000001c3c140c80e11214402034400c01903104507414000203240a080da260065550140019104038030025800c644c2c079002488002e6005810950901681c100001803017040403005910a034801d120741c0da19100c4171102c0341c1c45c0065400a010010405180600115840c495101c41207a01254030042c1c004008010740d009020344d07009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 246911339 1250 246910089 246910109
    0xd1802090c0c0d0c03080105010c051e0c0f18070f0c08030108060f0a09030c021314180c09010308030a23130b0703060302030a020907050c060709030506060402031e09010204 76
    0x41040d07007080a00503084003102c000c2030320002d100b1094100d03030352460030b400100400e18540041c025544144560030304984943c4c200d820300035007100300c4061700d5403000c900b0301d066008481031400c1303003810042040c0d2088169940c000c05011518204a200310003401001042103060a41c2548c0b4801e1a802003503640141a10b83c0c0c9523124906152142c8040f503100005002c600b01040441700c080c4500c1c10400d80503504c0901130304060742044990807200040e00c0507582c40d400c02030b00d4012001141030107a0701b5442c08401310b55550401500341f0386020b0345036210361080401040070402e45800c8a62181d80e00034000340c12440111215410f458403281c81c00c0f40b0a07030908128407543d4100c802030606002c0c40090702c9954410f90304030b06858440c000250036410603480c0500504109080c4e40d00b01045041c840d080002c403d0784549001c20885e00f03003001411741002003050000502c941604444203480551851400c0040c0394150a203a0704850801200b500008a8524086d810340b0090224103403 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 246912589 1250 246911339 246911341
    0x30a0c0915091a1602040902150d0b0a0902040806010b0f0f0f09190f03080306060409110706150f03201306260c011803051507020f0f030d180209 64
    0x1c006140b6a2607000d010300110008001d006180c00e410180c4005032804610500103000d03950901028060380c1400700e0f00300320769005001c0c0e500790f268090300030200ca50300002020748000080144a50481d03002803100392041200744504000415160305490103641825a642e1100b00401401d2044090f840303401080803404682c00f103801001008006001c6800d880f0780301e903c0407402018040d52042c252002c00071181007000811040141d03901002c02030132281816924003405080d507200958100044a0005060042010741d03c2034584a40c4a091032000d2079081c413004107080c40c41d501024110b500c070500340085d240ca034102c8801c0ca035070014110000c0411760101d200702400b520b0084980c103044c04119103000101040e0500115802500140720b9110b00e003006482c18920100941081e5601c18804404508100810b60b1030301000e10a44405160410009050041003000306846410084200240d03040010a4921500c10018005042c0241d00e28403840a000b00c1d800035004034400e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 246913839 1250 246912589 246912629
    0x80702030d050c040504150b0a0c0807020303030108070302101b080f0d0c0f0e0f03030706090c08010905030a090819030809031b01020a021c05030a0b0109170a02031204030503030a0c09 81
    0x40c002d0400c4520941d414040e11f41c41e5118551080c0032800b9801c481c243c03d01103e0070651150207841e02d800e0040a480303140070020307004039055903c26005002c0550185404004608240d40320b140511464030340203420101d030030b040641415a18030003508409012481c2c180307440d03101048130b03603601c000c440412103c080d10801401c1c8501241000d00401c20140300b00c980e50400c01c14011520000801031071800845513500c8004141c81c00b000e4a1020500c170001c14860800d03c030301407030325000b84021b544407018010000d240040b190007142c41c68128030302c005284c179100c8040002e038a50600302090306940740d06100349503004007000035003040e0200360400380030b03503065008103580e00341c0c0e600b510740725115030f400e412085140c21685000954200000f40700c092282c0d105e480001c0051409146555550311403005a06101230030f18141e410030f100150840c43d080100c4408070341011500c0b41090f1031074a8290f120701004141040341511219045802032050b2000d2010380310741d0302119003910b210 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 246915089 1250 246913839 246913861
    0x192405040b070201021e030c070803070504030219030210030f0b030a030c0c09060806180c09010e060a06090846060608060103120c03020a02090a020a1b08030601080702030d05 77
    0x16501500c10701000400304801c903106000711340582081c4020000042c04219200800b03600040010f80e16150610104001034070740c6c4003e600910342581e4886d00c6500b98010030100c0040080280c241f490a50020030050f2190300c3c40851045c8170b400c00003031280078072681e94007616401c4056039242c09248042020103070403c80410715207008503002011280c1740c8480400721003071400346103c558000000906114980000f880c030460606003501c9034484541c0104d808a1000c0e000300c2c1c411036411003084141c0c10800d000c440149003c0c40c1c045146803410300420340301d50761542c1d003090890f103000c0100e1181500010444c9100c19900002503190075a0034020140010050220f6005081c07200010758010009030441c16a50031044403814000c2e10003083c0e030000d05890b008c13020341c000c0041700409a42c4800f01d40d4420380007030030003590750030b402000182458414654441c4000300040800042500b04058a502030000e081c40452030712507542c140d1650251358a00800c036402c1004102034401c0f6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 246916339 1250 246915089 246915091
    0xf240406030f14010e01030b0907150807110a020a09020921030a11010605090105040e011407020304060f02190b040f060f020d060e060102100c090b04031a1008192405 73
    0xa402c408001072000c800e04911000c4081c46514112581c070401400415119a0301507040181c1380101c1e40e010b955600460340241e6035419400201d12140204010f568000107407100391074002001c4c0220245030f9000551001090254a003020fa003c604000103895900014040810f40d0720344030715030a038907400c043c1d40e544a20001000030349100c3d1b04140008050140130705603100140503ca5983c00c0000384001002070003600692903485003c400c40340210410f40320700407c050350185580b1800c00038081c00340d145190710b480466001195503220328030310701c2090050a9001d140c8506a40b40c60070108803a94244001420040c9005a04000a11107a0050140c1003404d0810300c0802c2e59181e072842c00c41c404903501405600024600c000c0c1e2000350784022040d00072418107a58054a4040903101ca03042500122915502034181702501180144402c0e4007007180f8080e882a0380c1091212500c03183c55032851904227607025031540400801a89444031540241c6010041000c0e011100001d420 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 246917589 1250 246916339 246916361
    0x4050c03040218010f050103020f121503060c0901120c03023601080702060403180b07081e0a120c12020d0c080105010e0102210d020301081018020f24040603 69
    0x140044440303c1d400c100c8403928100e524402c3c00c0d201c442c2c5002e0040d00030390312400c040440301c0820007021709140000540e442c081c1c0c5203c80c4041d2800001c40c1031500e0312030080c200042c0300f80180010901d582c0c0c460002c04420314110303c0030805044200c030590190007000c17804900740050700c01c4140242000384011611140307458075811210403480040d61104400c0c2d61480058001c6000140401e008880b030b034400c085030002166202d0b603115880b4038542c10812045954070000289985214003039002143d40742c0c0100090741c54007203031000281c0a465104652480603444a81d10340d52140600702011180091000c250764500c1a00c8009008144621300440820b0b034800000c81d03654130a80d07559514140680042c070000410b800080c10184142e4244501e00c20100039191a0a0290003d075000b06400b400508104514041541c01d50f070710b07090010200f0450824a00150781c6003919200c1c100420b0342c1c1c0b10301c0c10400c204803840103400040c0c0c518100100140c0055919496441801014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 246918839 1250 246917589 246917599
    0xb151e0c030c07060306030b040f020d02031009030207050301050702150712020f1b060106050f0c070302030d0804030807110a1101020c0312130509010302030604030302090607141c030c08011404060504050c030402 93
    0xc0e848010960072541b40d404050103090710381c00050001180040010161400242140c2607080380b0f070300191070200d101d4640710f91142c6854002c030405804100c1e42c4040c000807802800980f802b00c2c2e00079900c0b5101c1007044e030f011621502103404940120740084841060303140070742d50340a030840d641490703900002013070b402c001c0901d5403a0025540400c03610f0503a0116503c05180861020900381d580d04981c070012018018602d00200584c1c0c01c0240d0283ca90407525040b080380b4141c18041c0c20420014960421712444c010002d07015000824120700072035021404110341820240102e00e4140c0c1c5a0000760503104600641e1205c0e074200d009403104021000300c1d007001c142c0310014800c592a00b884000d415034010404100000c0c02074010705010480641441d080a40e581c807140003080c0070a941c0d40c4103400c0718000c040031800c031070350007e003a0410341030520801c0c0321208010040041440b6444c9070269408061202d40d80d650086002000d000b0018451403c02c0020044258020364040f8407413 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 246920089 1250 246918839 246918853
    0x60312090806060904031103040801021204111005030403052104060905010b0312160618060605030d030e0a03140d1113050f010203121302040501091a040b151e0c030c 73
    0x4074200191040c400d90014000c5100364407955001d0320300d40d8602841d41c10030700040c40081102c2a09101500e81d11601d0400c2ca40682468102150822404030051f030003068200031403046260402c0451307030807641c03624015682d070101264503002264505074180d0502800c0c001e200921201e5000f64203618040d0000300700c55200a005c050391003d21510702d070038100090002007250002c0b0700340107611600450001c60000071000d42c0b5000c8400004040707030700da80e0b180740502c01d1781000c001c101d4100d02d4a050811040a49001c0c05552721440030b801020489100f1410301494103c2041e1201481544014041c44615840fa25036540006040744900c3c5682000010360b4900819101107090040e0055450f1800012100f01814801080c00300d482511a00000041c2c9a40c0b04050080600b48800203a8003680c1c05451191a01c2c04900c620550520070b036900c89a0340c44004004502010500380c0ea2010f45840c085604000c03029070340c4904101260b40840c80304044002e01002e10094192400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 246921339 1250 246920089 246920099
    0xb03090d0816090e0405030f0f130e010b0708030403022e1b08010303050d090f031d04050c0313051c0c0b0108010c050d0203040201030b15040f0b0403050a2406031209 73
    0x88150240c40000440c01101002040c200c4e144998125024106032407420289680d1520b165003c99200000e8040020301245400d0101c2c04020140c1150041150b855141c000c03a484240a00351001d081034a000011604150082089402d4154400140a0ba41c460307007981d078801d070000301d200750382040c2800700c0c421418007000d42a920140003a20b41035066405c5880484035030704404625101150740701d60394030100da80d41c10307045070440c0300303542d0008a1240604002c0c580c1030a00b0445010301d04007010302c03240f030000d5425294040890205110003403c0c81c1800c034500400c56010411528480700b16580050344241c80000701c6014100220340742c1d0b0390b40402d81c00c940103131701c500000074001c3c4034400301031000d6001940c005005150218203030245400044400c01c0501c5030050b40b40c400a0200045201403000714024060b5032129414039145403070345512003500e01070080051007103500c19003100040070307201505214250000c00070a40c50389000d00c4c003841503000788000704000c3c000000b1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 246922589 1250 246921339 246921361
    0x31a0108011d04051e0715030902011e02010b060c030307090501021f050403090504020c0c010f030b010203030f0403030617060603011401060f0e030106091103100b130b0c070b03090d08 81
    0x41250402014440300032500c0c0e105504a01028104880b640034651900317024407000894600903800c620058000e440c50400b0105000e0400900360040c10304200c940c501503071300000c0c9440005070440c003804e0340100e00d8000303c0c0104004020710f9407020012131501c18805000001d984288440d4072100300250f101c40040e079441d0310900710546092107002403000200d04c2500007541007803081c100760f00d040b601d030000141031741c200d842c2c540710941c0050302901603584d01c484032030140040340c1010400e814035080002e403644001010380c00c01200c09000300d0f04051103984100c0081c80c01080c0b0000c2100a040b42c25290300c1c003964114402d60a0600c94040c0060a8000714101c81242d102e9003900c4030b2801d010b880000d4940d004d2580b40d5a5008001502403890140749250140322012554038030386185c15118141d6260800c0d0b83d1503000703004680c030310b00076200201c4c1aa545943c0d11a01c1c1c4148034100c902d8003030385802c1461480004414001c00000009090120b442d00d40c0702c052480e550038070344407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 246923839 1250 246922589 246922591
    0x3020c0f0a1208071112030304110f01170606160302030705010c031104030f02010c0507120302060a02040e0118060f03151b050405060f1b06040b01091104090216060903031a0108 78
    0xa03401802c803620b110025204400922074180314090301190302c20500000b54154a485c1c0f0303451b8080d08000304010401c61080c600459080782107401040f64410382c0c6c0020300c1c4110010b0111540b1516030f000c181903688500030349202c0c45804644008280b80d51030b009483c0d0300800f60407a0303158201651103034040c0c000d0254401c0340c0e6a040d580d905291450702e40122840e10924164140a0a14507002c04243e0610040300581003a60f052008188185030003460210000c0a1100d031700d00c10b20061180b00c2e1110300c0207044078241640c007080000782d42248002440a5032209040d8110241d00100b00010903060400b0030484c0304c820414403a12007c242001d400c083c1f180c80c001481003200f44070618042c4090001135403400030b00d07810003142000e50002c2418030310100c1c002d503015008000812100c50401805022424814055100344214a031880c4c0914000c807035030301d500410005c082c1d201782c0780f0101600d5046030041c0101c0816080140003003104c00c0403514801940002600b0f50750296840b0303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 246925089 1250 246923839 246923849
    0xa03090602030424180b03010f090219030510120c050f0d171b030304150e07080604110607080d0b01030e0c0a0e04050a02030a03120b0405040f0f03021903020c0f0a 72
    0x71320a884205510000780c02d880076004014054081d0343c8881480844102c031021b03000944c0800d07525410890085038544103680181d61142c0100700000c41030310a448200844860344c03c01160b40c1e110911644007070030b4250084800c12150442d0b400920241c0d80c58503084590035202040503900500030310000c4001c01901030801040309508503041c8546c0c00c010409004101c400b508020885501c0d030f41103500c2074a0903118240c0b2860349040014030b80c8210b0492030202c80040a419203407068054a441c001480500451080c4100b000603480f003100b100c002581c40641c6643e44c0c505084444020410b540d820360010f0700d06a0740c000604000603103115040002400d55140b1842c20600e80c043c40c00044c0122a1402802c1c40100140c0342080302030605840303601c441d0054888825400c0c00c4514140505110350301708028480410300725101e0084079a003185042c07502c01ca15090607480c02c503652240c00d40419001d06100c06140d40404d2100c0c841c4000c88018003640d44400030001640c5941c013034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 246926339 1250 246925089 246925109
    0x80304030315050f09041b080703050709060e04150507020a021008070f080c160204090206030108061504051b030a091e1506051005180307060815040504051207050109020d050a030906020304 83
    0x406e000c181c90040d00e6040480d14003002c03c85c1900e0b503540a050007444c1e402102e4a901003c414001c81443c0d02604001c1c080810340300305140342544481c000142d10382228854240e1b43d001160304188207001c000c0d00650060302e12285580006070042c89550100c0704003000440d010300c01400c41d403058201500030480c0e0303d00941006002284118544080401280e00a41e140c04242c01130f22010040e60007400e904d400742001c0c0c645010708101110308084020321132483c08042002d0004940500652450070301481a01ea035140d1441a00900031624090702c031184592510f090390707142c4a180008140700f4203a495003040d00024410990f8454042d65910040c3c640c0b0a41c01544500090400c0e9000e441050003861000e2011a00f0002d103900098000f03940c2c4420001c4103107000030314645015050740c0130412071801e0b44540741c0310541c41158000540d000075103501070000075005110a65001814810162120314169030343d10b40d501c1c01200841c6507080000380e014008402e0f5000c540e14548 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 246927589 1250 246926339 246926341
    0x2909010c021f0c090e04061b2307020d0203011d16031106030c1b01020d0e150703110c120a1106090604081309090f03030605041a0f0607080304030315050f09 69
    0x30100003d0400f0003d80010051341d100001100c04904400e14001c44c01a20f0001d076504886000ca0b1a64039071800748002e005a00c45049410450710803641c4e191008103a82c1ca880350070034400180d0b40d1040d00800307075140d0708042d038180000002c03080700c121180000f01221200000c42d00c00e106003911600c400b1b003581d21916401078180c01d00e00000d43c0e1042d030700030b01d0614080e03800d64000440b10034508107100503036010031103402c00a110710030583e90351070b0341d8010000b4031580901ca0601950051a410070540c4074000441071011b0102610800005002902c1500300c803044410500c6d0400481c0200188852024010a620100e01640a000008041d11055440da01c42d4020b40d405403c02421420304010002084c0c4464400c2c0c802140c81a40d9000d4004d48606005069961a4012a1180780740c0040d00c0c51646c20001c61000702101995803980c1d0105200015040340a1500b0180101400008010406034543e004086d90091094800d01d206c2d00ea8050150051000741325030340101c00c82c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 246928839 1250 246927589 246927643
    0xd110a02060a020c030319080c191404080f0a15021314012606010801060e0a060c020a0f0f0e2d15060d2a1b2909010c02 53
    0xc1c0281100407490048801900d8458003007031440d401340b401d1804402001c80380d8400a0b51011300146c001c08600503480c103041024040001003001d82510109000c5c400e070400c0034404c002010348004141150503514088180a0342607203642d000c2404540d001c048900511251348144261070001e4010640322140718108565451407c0b0700651a6050002c9001e445a030750a00c140d141e800540318803070390a0142009800500000c0042e0400006d00c4950b440e00d4200342c032401c00ea103044800714030b0107119030409400841c04000d0160840f00a200c3c0c04c06001c280202038410710340803507051605140143c1e0b074041c010602d14100e0f95030342118108600c0300c1070042050803d0190800380818a102c041c1d0310710070000300194842c1c40d004000030707154401103e604000c0405421440c3c5425094035540362591001001c903205140481007486070b0919440512100c03848880002c05030220303484200c181c0312440174441008403002d818540c2060300a25690b440455540305031518440d410419960382 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 246930089 1250 246928839 246928849
    0x6040e060601080711060a0b010e0d02030c060f0f0301091e140f190603060e010c030e0304052103030403031a040b13020f0d1e110a0503070302030711010e07080d110a02 74
    0x90100404c003d0011a05c0c5000c91042c000640906090310002900e080c5050025005c0311002504603ca520868182d402584020480d09010300c1d0494085a6803140c02c40d95141c13034058100c420351801004170000c180100a90f2007014001849821f44884004401101e4240c0300c448840104108604001c2100d0407141d043c80d58000903d000d8103905104c19050f2501100c0e429802500c0341c0ba2a03080050841c80e0030703c81c19541c00000d18091000050080714140c4c1d0788103900c42d1500a0320864000b418907c40703260765286050740e00081c0c959a003041e05004028142e60800040c100c2085401c018840c0350520881c1c9019101400d034809070104412440000d4010500480c8494004c00c00b1110381041c0d446141c3c059144ca0060380c021100418440084602d04070705101101c80c108440703042540c012043e03c6c0d00041c036250150381c0e0b545502046483e803980d500058082d60818002c0c0481d6240401c445c401da803900c8049840282e00803008507010f00c1c80422a28658000c0f69090f0b0150903c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 246931339 1250 246930089 246930091
    0xf1403090d0801231306030b1513061409040606080a05060907150c030f051903091a0c070f050a0807050f060f0c04030605042a1505090604050118030804080d0806040e06060108 77
    0xe100000035450307600d80340c0321260241161427038900c9070340010448692400c10340b11601c83c000068100250b600707000300c0701218910940c00c9032041342c06034001030810865030400d030080d044000c20b27100808a14640030707131780f514240c450559a0048407000304150b56540104801d02ca21a43d449075041050346050710082164255141000020002c001d00703840409104441440e10341d400094045c858103103842406000c140c0d00c888000d10a003408000c0b64400140c80110350414080c0100d12050f00c6c1c954501594a02c00410400c0003160a20034004041060200ca61003d402e0b07484599921051a000040844401c0d003c104107106c244081125944401d50081c03007560340300090b0713005001c090109140010405840b40010340184900080c2c030428022080844c01c1c01c038200144280001e01034041c1d8000c1c0343c100300300040090700030a5154421001903400c81c005c0c0d680c0e01d443c0e10000e80c03141159040c4401049416000c5030641c10a4130036015007840c4c001c007601003501c07814011246400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 246932589 1250 246931339 246931369
    0x2181003050610031103010507020303040b0910110307080f0402010f030c0905092508060603010905130b070f1403060a060509240909071b030f1403090d080123 70
    0x2a98050100c0000c9080240c54050f403010f21410340c0103450362900050000144a000340030741d040806014207030740c001081d26042a80b19804c40f04603070701e03076034121b281c40e0300d4401d4480490b0502c4e1080c8400b080407002503005601e10ba403a480c1664415084141101c002d613002030000380355000c0380d11410b100340c7c8071040e80e0115250041103039a40e040007404082c41503e5813a44840516030341c0e948600d21407044030400800d8104240f4038034100002940c070740814881e608030170303858000103400c6002203031210b108590f1207000c414103810806001000481114441000b01d0186c1a01c02c0b043c3c850fa10a0324450301c0028914012241007a4080b160358101500c0141c1101c2ca400c0d0940d0980c4589050796070003124941010b4650104a040201481000e054003060240d420b030485406018007807168801c5805040142c185180028203c030454000d42200380002404002d01c80b003d00003264000c10411160390359510741e41c868054041c112a03244400c0c4030840219000c0c84103040c1401420a40d807 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 246933839 1250 246932589 246932611
    0x1c02031b0f0a030b0601024615050916030503071104060803041706060103111204170c0102030109053414040303200106050a032d030203030103031b0218 67
    0x101d01c80301085512496400856009424404000311541d0400c23401034089011081e13080725094240f641401c0c8101d001088082c0089140760070660b0010140201b0300d150310150b0403095607a80315500380105000d48600c086400350414410003140001c1000c000d03660054055450441c0b255109094a040310711034075042510b940c1c00040d1840240003420090400e12450f08a0300c01d0b00c5059428a2401401c403414107240c941c0311040101c4032800d82d588121383d00700a000685941c10542100081c6206d880100140007652100c0c0340011b40195048070710305241400130303458141c20300c0e41c4500c1204140d1101400048580c5001c064080d5130103490100d030500d00d061440001c00e05000794042e40060700807030310b1140c0c5482d81e40c82d03581841e048407000000800105050800066035200584809000d02070b814441d07420041802108580f400c000c0c0000c43c440e1304440c5000b0351290001d1006401180341c04d15119549100c000d0700400c07140c2e00420001d002d25882645080301c00000c2d181100813 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 246935089 1250 246933839 246933859
    0x20d1107030f050d0206010602010c050403060e0708070609050108060a141e060703050415020f060711010e07030c0315020702090106052514120403390b04051c02031b 73
    0xc00e10b8121140b41c242e00903805030030040034800000e480d210707060b0b1046c4210380c54882c904407180d6201c0e0558060360341c450000324202c144d0fa20460f01c1d02107a50800000c030f0081c80c030001445504044000c08071f0300c00b81c0780d0705030a0303a6100400040b444141700384192140362401400c005d103030680503207161840000c8065400d01c8000023207040c40d000fa070800c4010500c000341c280281c807134207450200d080781688003d00c40080c03641e0160351540c4010b08032509220740300e034040020311029004810b11240300000c8516043c0d803800c02946900040c40142c3d10668024612201012580226031100b600a00400001d03403801070101c500d41d200a400c402409106003131303144000136405207e11640d0240306400260800030504d03e041c810a00e88989000300b040004000052010341d0003006145000c280300c101c095025507100c03450340884640000310400c0c3d9408039500e244d81c4007400035203206664520100490303840c4001000c80c403500c081d40c035620560305135842e07000300c0511070320b0020050002c10031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 246936339 1250 246935089 246935093
    0x1b010c06060915080604030e010315050613060f0c031d0a090509100b0301151406040e090f0105060612061003020d0c0905030d0203190807020a080f131401020d110703 73
    0x49500c180c20250042e51110401e01d5650720001c0e21502410076040a40f50900b82030317901800d03000000c00381c00d040c07545a45400281e50f00d802c041c000201005040196074007514108000e50705443e00506d0b001c107100740030380703200c0c2481541d4940b0768981c5602c550700003041030300d070b0728501c0e440c20036104c0d0f840302e2050004110040a401403a000d514640002d050002c82c00c00101e064400c1003c1c0d02d130290307250110500031040c002141200b2110400f103240c0d08050801c0102d070345446130b900400c1e0120303804020b0003114600007400580703501109000b0800e0381c94400801c48a4405e443c0f0107503103103650320f021500525224002248040c07040c00c005241c05666150344040d2020540e42c440892400d580801c5181401d01400f082e29005102030f604d0701c59501e041028407071660010000f0884020000798800c0d0007084180c40c1550010348164a40d0224460350300283d100280305076400609000000e101e20405110f0300000c0d0058003e0601c02e050048221001c16950289149605c100b07000080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 246937589 1250 246936339 246936341
    0x20c0609371104090f02030f0607050f0c030409020c0a030f021f020a02070306150e010f0b0a1b06090b011d0f0109090f120906090e06010e1002010f0e0607021209031b010c06 76
    0x741403842005e0303105200015004040c2400510621491140c005c0ca0401ca8171550110480b5002460113035540e413103086031700c0740300d296015641102001d2840007401d004100c2c00000c0400d0f060b8829902d040c5507000142040b41c80d0a0200c03200184440c1a01c0c81e044161025000351102400030310480d0002c0703940362940340640d00101030300d40c00300c0d192000911100c04041c4240c1c1c050442c924192907402c1ca0400d4a4031188a1924810108207000d660180c0b8891008940000309412520074003904859040c00c0103410020700c101d00805000c052003610074000902150700c03911400716000350301e0380392075880030150202c40003c0b6603005a0301d103e07000141c07403c079980d1540340303031035440325809401c0c0b08c0301428040f4240c12074660011218200100b603a0b00c514440c01400e0155022400090620810f80c050240a6021007e15081080743c3c012050001062449010b540d42114080c4070358204043c0c00b480340308902034054100c811419403000e58500305c18506081890b1000c4403a0850f100d840c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 246938839 1250 246937589 246937601
    0x7020607020f0a151403060a09090c0308030a0c1d0907110a051507090803180409111806031204030c030f021503010e06042009090405010f020c0609371104 68
    0x3c03d8014444c50a000c4c4168000f950220454440540034503500b022000114012082c0c0f189009543c0c45ea2118010000d011180e58011a8800a155103c3c2030152412018080d4425070320005071702031050309502c003005100304c1d540e108007512004e1b440d2500582200e90700c10450032400e0f0f5100712141900020000c202100d94071500244044041c185400020403160040d400840707954410322001c4040000b202484915031412100010480701d20720b4144c81032809207000650102c4115040d250003400f02052500c1a001141900d00c4c0c141403000200c3e80e4060760101804860506000b0310000d01e2841a1520050006100041e0107414480c0e1030041e50098010000c01010101400301c50309060040c0f5064402065400210703d20f9105280805d0103803266192140b01c41c3d1000c07401b880029031144001c01c5242c001550307207071301e8070ad0345603a00c0703500f5030711440c05100d0fa580144020344541d20324240302c40310700d00c62188a0290040306a0501685105441f115916085040c290742c86120345 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 246940089 1250 246938839 246938849
    0x11030d0507110f031b130f02030915010f0b0705010e0d0903050c09070f08150a090605120d020604030f020c1c12031406100507020d2303090607020607020f0a 69
    0x2956607a0341440c005940d0080144914015012003c0014541d0b40100301d07200b0611802c100c5a01900000f00080c0009000fa04200c61580c906803c00314489515001544290640c2c4201d4400000d0380130f007020107150900c6610580d43c42e090040c40400e40c0c010083c03035241d01402c00891140b8102c0341c100d04201c0e0218401010440b0b5600400800005109946101104840e884054a8a180081c0007014050b44407810408583c0004aa18900c002010700400e8080c1c440d610031750712501107000405142c002c070b80c450aa801e0060203100000122106040c030f03d5409029903881d65a020344056080003075207402d43c0030b41400700d1040d80369040900c07500074201911808060403420281f5000d402140d048081505011039001c030140301e1007072950042800c0e280f20380d10403074135082102e1502035441c2c0250702040781a10001171040803910002c0e1807030000700311070740840f09840644d542d224825200d03401880520400c0054500100075000c2540090111500c44c104480000c900c43c0c2e454001d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 246941339 1250 246940089 246940097
    0x2405120a0c120213021c050601050c0d0906110304050d08030c0403150204150f080f1e090303010627030215040902070311060115140c0c0a03060605100305012111030d 73
    0x310b074055103802c0d6000c2005031041c5804616100c410300d05218114400350b445003c1035112000700b0207a910800460b40c1056583c025a0714840342c4400003080c80302c0c10300c20600000c0e400040c901d035030342010046508840340140302c0290441c11380d40c1d0b01c0d41504001c2906000b40d0342484000701284001d41d100d1209030a01c000180c4da54140080e03c103288039400500320400c00c1d509015101079030082d260580140d100420410346035248142c00d0f20a05010108803440c80404091043c8040f00001441c1a2030485c1c480c19009088417002c05204000c0541d40c19050660a4042015003410a8191000081d22135002e28180d00c03030000c48181d0340300d042d040300001c2042a080b0250710302441090f014109000c2c450848542c08a402445801c42d402da507882c07000300040b0b0f20004801001829181800540380440b41aa2400c00e0001001c0078030130540188500316400164a11a02c22507058503480ca4083d10b05500782020049070900c11641245d030710038500c040d1049e5944c05c0050f000381e49031a41e9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 246942446 1107 246941339 246941369
    0x1140403051f110403030306030b010812030703090c03140a02010305090102090f1306050301110c0609060c0a0509040b130204080c06070b060d05240a2405120a0c 71
    0x400d1003c01100000e0010416030180c1000040368020641450b06a0b83e0b81c901980f03c6d106a607055110032020000105180d0080d07109100403801074200b00030701e90b1a5038980c40300109036084001e1680c8880500b008541e17050082c02d0780124601d00960422200402103206240f2600300c641c8108000d070200762400b200380e8001001000c00400034072602d611115040038650050103074140c0c80c0942d800280d1302581c0010340703500410101090f00e2608203201c000303c560760000d40e001640300752241406100c231390341c04000c1c010542401c0340c010ba07650301e000c40c0e07503107000301424040d8028041408035502191151101c00d91048040e1402515410f951803d64140150108038480741c0810300041d510324040d10000070301c506220001084215150602c1000008071110141e04150081c0018440c40c10309e050342e610702459000448010041e2603481140c0031109402c50402c1144003c = true := by decide +kernel

theorem cover : BRFrame.Cov 246762589 246942446 := by
  have h0 := BRFrame.cov_init 246762589
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 246762589 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 246762589 ≤ n) (h2 : n < 246942446) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
