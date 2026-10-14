-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3460
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:43:37.026126+00:00
-- url     : https://prove2.me/submissions/b31e8db0-8224-4b80-bf48-d123d7a2bcb2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 622122302 ≤ n < 622302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 622123552 1250 622122302 622122337
    0x1a0f16060509010b0d0b010e06031518070e150409080409020a020318150403031d10050304020405092d070b071a01090b150a1106071805030d091205150f0919260f 71
    0x144041cce0b00e000440d4120b031000f07400344d80500403700c0816000304a060000c840c003181003042454001454015a484a01e08500100e50207e0951300400607208a0003d00c0305e4114503a8010108020416200244211403908000078000b2034842d0890f070b2800d0106890344001d4204030300104000c3c81611051900040001c81444118505030068640105151004007046010b0410b018121000244000c6240c1c01407034003000c4c1700c1024003170382004002c020141a1203085a00b01814440c21040d1021000c510003030001c00d1400360391240c2e96081d0030207005078194090755403580c03005510001d6503000b446140c43e68a0004038003045542c0c85403000b07685511007404030302000d403880710141d04060310070b40144a01d0340326682d00408090440780c5d820100d181540071403c0a90900030070711072410741c01c4038913400c00400d540844001409004210200d86000c00f00c080c4140010304010001040103182c072403441044200c2ca410425031103200c881c4245810001c5012500d42d42c056075903e1824500b1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 622124802 1250 622123552 622123591
    0x100906110c030c010f090e13030f02030f07020904020d02090403050d061d0703050403050c0d090f0b0a1d0103020426161a0f16060509010b0d0b010e060315 68
    0x5800402200d030030400410a0014510002e40c030341104400c90f5040144844c0500542c0e031141c6102c2000700420110a0020708282101c80398010f441c13441680825001489403200500c0001160480003401014074100f11050b401c201901c0c1c4068801e980c00501d0b00c8801026039201100c082c001c07486500c80940c3d401d05c406004054030711550000f844800350703a83c0e4250315504c2900840e802a15071400161a5490b40360a4483d4000e00c4c0c882d14441c4599490700c0a0b207034021080c00151070b00b1902070348180d13035210004043d910072b0b00c4000b000201900f150700191400c5130002035030a2414140542050346864124580203070302c01d000300101180100517003400342e0a00c10724043c003981c0d000b8401c81c9410441b555640b020141480c1c10045000078440e4030001000d8207030b8003030605811582901903900d0800300094403056404021075440c2200444451a140c43d041003210703803100d01e65044d6843e0110b42c1c0401c00000b000d054050160403500100c4280750118244614141003a0141c103818 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 622126052 1250 622124802 622124807
    0x9090403030f020a032717070303150b0a021002090f010c0201111009021215040807020a030c090504140d2a06021204060e06040201120b01110708100f091101050d0902100906 76
    0x11441b030030000e501c0a11400d4045991922030b0002c0c1d014001038259031303682d149011802480b002106400c05006017101040341842a802420fa055080d821949501c03103800c0264124464200030991110604c2400c0203d940510764503a8214014180400c0c074841c95501b950500b00065052084283e503020072004502d004802182c90b146104000c080b560344a21f0031b00c1c04650040c100cc0d2031404040751031400c40d900d9424000145500914916080785da0f00001c0024140a54049038202c01e440c0030038401e0b80340041d401001c800c107951003000031b0100642e90079001c201082c800018400026413540490381c21b00040245081440500c442d0785080d040c000c0c202c0c0c80031000c021540e0080c105000c091b0f80d21010294018400c0000000d941c115000182c8801100440b0880c40b4002c1d000001000c034800720300352581da0039440050040208009130402118498000188061030702c100c140c1055201c2c5001e4620a440c484000440c401180c0005130102e015880740300c0001c0c16848240a0540e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 622127302 1250 622126052 622126091
    0x6030903030e0d0905011b0816050f1b01050c0316080702030607020102070803010e060f04050906060123071403040f030c0f0605130303050c1603050d02060f0103050309090403030f020a03 82
    0x80d000c50140690f1080c4030801440040103105950420118407141c00c200400f1110b00768070381d80e1002d4010b549081880f85440b401081c0e02040e589801070758600c42c0e00b59000308800c1c401e100d9070b41d124219038010354010345d00d030b0304809860881071005100392220b0741032041280420394020104103032038408501c101031400000030030910469005104001c005404001600d0540701403800003005590f441e008500d4864020400310341c403074182401d0100465010a201b40181000e0383c80211100e40e09010040d80700008400824146042003a0300214030640f004a404802c48001e5a181994030103800c421003805800039100c05442c0d040402003100140e484400418503410003c0c2000841880d0054040d0386100c0a8207202000400b10f0807140c050049458600c0101e11008621780c4904146a0380c181e040344e100c0c0984070742408030b484184102001070403281e01500071031900040700e040c00218280607000b101810f07145c00044c07180c81d0705400030703080f00c0c1c2c0155000030b44410b070070000d002c020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 622128552 1250 622127302 622127321
    0x6200303044b1b0803030c1c15080d050a0c0f05010e030a05180f030a1209050d081e0903061317030a05090c01050a050d0213050409080304150203070c0f0303150603090303 75
    0x7443c000304020303000001c410f50382e01202080004d038452456200901c0b58a040940801d010782c50800c0b61441d6040c20300030742069540e000c003206d400c2c19000f1800d031440c2c8601510300c1c0205441d0055003001601c981103020f4950700c20400407501e0307503540f02424039513000070304024046180030500d01803040d444450003141c141c0c02c0720690b40ca040c0305004241c5880e18a0070160040c42406a65650b90740210003800040102030300e09116034900c1e042c00c000581155034010704014400500c8441100040d080e1070b841c0a0050141c08951a4800f414107c56000ba2080ba4084950007920b1113034103180014611a4901c5480807540e480c02840303c90400e911541c8142c14040c052082000d07465004d4103580074100d81400c0169120040f805080f6065181d500041d8070a0414454404000410340594004d40c8262011001c032444150381100781d010488180d40020300c1e180400010894031900000b003140a4200040c2019929584068000564002c0c8001c00d440351031040030140d00d4480c2604a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 622129802 1250 622128552 622128593
    0x220308071401150909030e0910030b100e062b060209011808120a0c0503040602010e160803191b0c06120603080d110f0406200303044b 59
    0x3d0300c48450400710100d4a034001c3c80384856684600d0810540144c0640b01d8003000282998000d14003551304801100c0342c1e000031102400d003440440d03030060803020410140c9081d840300920960f100c030207020500c1a600d21140e84070190000130807207400041d8120292030b0140c2c0c00565582d1000001420442070010414103240c10070030100000302002c01d1005141103090b084a64030740300c0352811035052a4001c0003030024040060005500c50301580b040c02c0e0a0707052425210801c10102505c0d19a810a110380141c03a0401c00840c0303448401600e442e40c9031034950403ca040714019510041d16001007c2c4101c5070070440040c00c1c0f10340e80d0803c03502e200100e0b00c3c0509000700c07402c50b9035105050040c0700b0020002d039100d1141000c5180b8080a9408021010203d6521582d03100c0c00280034038840b0a40c641815103a01400400c110003004507480380740c12284680310140b10071080c00b52400b40800342d200481ea41403003c200318038464910100170038030680203102030b1100d08110f070001102401d82c0a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 622131052 1250 622129802 622129811
    0x705070302100e07051507060c0203130509040609060e060f01090b0d0f110d0305030105010e011d01181a07060b01020601050d030c05010f02030c18010306050607020402220308071401 80
    0x641d0006954450215400001c19101030b1140d00302c0c944009034101590200180c00840e2030490410054052a40210400c1c0184c405200d0301f039813a841100c0000101115680007071005080c002c04d00d0303410a209550008403040300740c481c41c04440320080381750100e0f00000d060140c1e8081d03540301103014018400702008417503044000918600500c1d08000d201d044041c184c032003400419402011030741c0000d85207030120030340e924004225070f00901480340450303d0f00c0d0480202d54070030b00158210f080380c06040080c01d40e40300c0c010349081c845d45003808100d0341c40610105215003000c80805440f1030442c00e00ba1141c003140340c01c8040d540300c041e0141c110340c050801006140d690090508820b17401d1300303189040c004182031690240034181c080c800e19600000611000040442c000e0038400b0029041c0900003141a00440a440061203025402281400010302510381503000b0045100ca201041c41070042c0c0401700c0108840c1a0720075201c0d0b60000c90b9203000c0c007140d03140c20307856501d44100800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 622132302 1250 622131052 622131067
    0x2d04021c06060e0d06090501200706050c042d030c0611011a03060f0c07080711090603120307030213030c0b07140f06160e0307152a062414090705 64
    0x20036985404d50003911958541c0072410610100394080305201c55580e07040e4402202c1c0c08031800d901c1d4440c6d2421240989004001b501c5490880d0a480958082d0f9600c0841790780b142d14440d4940701015010205000e1129000000507001c030400001864251908508048040981c82c00c4070f61508590b0f1440080040200c000c5d500850724030f0780f080250218800756103550070780d84403074062450001c2001030b0000c1d100c400d000b00c02441106840048452403c00d503070300c80501d034584d80f5104449081724020300215007400d010ba0007401e1480025000d042c501b0307a0701e454012048030281d01142c804c4200254031018442841c02a079180208500100541c03246c0c11100c940e1000001e2074407218100c1030b03801e00280e5100d04075082034440c005049400c0309444252900110180f81b9610300410051460070f007402d4064070040c05051031150a1501a039031a850b600058140311000c07440c000d0200c100c007448100c0d0780403c200a490280c8620703512600080c2480503605000e070608040c88401d103d0780 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 622133552 1250 622132302 622132309
    0x2916020c01020a020d0303151701090b01120309050f010e04090812060d030e063001150e0307050f0415151b1121010204060809011401052d04021c06060e 67
    0x30304c2e17640c1850001441340c815182da0040f203005400c5041c1b100d015200070050454150080103070035000b070107400c00c184da0340c40e00c01d500150300100040110344000d90811841c94400c1c1c4812001c1010305200301c1105004000a044607003d160458100c600410042c0c8551030b6400160741c403107000d4810700411000c9440240c215603113000014440c03a0000b4060004d40d410038070400110704010914441aa44244510400c3da424026480c42c50500c0154a03a070912801c111034003502d01801400d10136081c0018044021070703810150703800c181ca40420a5801911072207a60081c088111141c10300308025100620062a9500c2840615070340008480030961884010f08583c1e070454ac0c558071996140c0152262401462405540794404200001e90350740110f80c2c14403e04014008000300c0480010b0b942010500707005054108501c0843c00c2540c0d0516042000c14400001c1000d03291308c2c0f41c0c030004060b0380c042c05100c1180d540303602c04401060018010320000e03001c281003080d5108540c2010 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 622134802 1250 622133552 622133569
    0x41e030b09030c12090f0a14090f22050c06040e010314060411060702041d1e0304030c120f0203120a0f11030a14120c070b0c09030a2916020c01020a02 66
    0x428507102c000552201c8554036501b6460f984603001d0030340b20105680d02200300c2e4034422a100540030710f01120026201d0286c174031102d442424010400034007892140c1404440280e948011900c52085071071452241d076599020300000c009001c1c80740e44a6040d89003000c080181c2d821100002e50001c0113000c001221454004030f01c55058035440d1b02c0304414000580a01740071030084000d18030b0040e42c03200300d000201c1d020b001141002c0310f42000851001807195644201d20000e4400210b04005001c004074240c1208201401015507404125154000074100130084002c042c05c1c00e00001c0e142e100a0b0000400100d0382103600f00100314500307080c802d40c4c032403183c0c401078000c20005a2000007924009000c2d100c048032490300b264102d290080703403c01540d00580c4103860b100c20900011701e40e00803c1d01242c61208020b8098a04c0300354554503196810341103003807030304080d0900340510001641c4904103031088280d24403803104ca00d0a118041c0c2040802880281190041681e420240c0c644900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 622136052 1250 622134802 622134823
    0x1707080321040302030d09050610080a050c01030c09090f090201140703081501020f100501090605060c0718060905070309060c1409090a061806030c09230903041e030b09030c 76
    0x40000490b620307803030200d06510031441d11804841c0b41004a5090010014800b0f00c22216101503104040e1500030155075509502c4004003507520000c00ca842a502c250460700203140c90f410540039880e16040c4000030b5800004508810a0f9194a0007040d903a1000c0084864006e020f409840c15000d038400801410008120090440b80c0900b54074081c4d00c200300c94840e2050103015500c400031214481c0024260a208603510941401408103552400c0403c40e01003c2c42c40000341111840d0014940d5507000d125030111003d9543e000c009008076040c0140f0344582c4241e900080c140c0c00350300e4404111510030b01118100f003003003071807248241032060840d2002d4000301e455800a68405030524040c00e459001600404007a03010040341c0d0405401140139a8420810012899284c0a914080f00e0074400d0061050b9100b0b0710b0342c0600d141e10750005400c0002181501d14086d2070704441c4041103008003903c100c03a0031404d020414810b00d030b801190000021000340d4074001e01e00c20069a03c001e060b0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 622137302 1250 622136052 622136107
    0x50a020f121b0a0e0a0503120a030f0212072006070f08060a0f03032d0503060f01020a0c18060906080606010f0215040f0614060a09021c050117070803 66
    0x8144098542c01c4100c409070030800003180c0c1d5000b01d031801000003040c480220b0096081e031402060711b1a0101e04030113005c4c0e400c03500c2810801040c4040b0040d1802e940d050300825420480420f440300e0b01465a44503840b951261551030b40c200507040316810719500b03080c1480d001030090007900c03603001d80300715040c02c16480c0503445520340c6030024a405401d41e110211034095044d000041640004542c0c0b041d003000a02503003840a101e40d81408180414020300c00104c0c100001181032030520401800c1c0c01040c41101c031480307006d6a451f47d086006400ca4001650550b50301c0500c1d951130b0141002401150100f0b000c014a80f0725032a940c0c40000c3c0c8a0b0b8188000340c200041400c1c820008442e03036202c00740d2116440e09042c203011000401000003510b6081c1010408641c00040001d110702440019112201c140c0c50036203688001d400c0503140010350b0841d030300b03113110452090246a01a040c40f201d94403d46280c81d250a1030600b0640c04459160010702c8104006414010341e405a42c0045 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 622138552 1250 622137302 622137337
    0x60801090b0103060b0304111c03080408071a010f08100e07050f030f070e0a0501080c130c021908210c070210030e0f0c010e01141e07020d08030604050a020f 69
    0x754010f90140c40240c125818603030001c81084180654444c03202c0f004402550400d40d038081c03800d40002c813a80c5001c000740101d00680d001c240054284001426458040c509000f11100b0700f000c81d9256a10a031301c506507506035008107014810301800840319103180607404002c4030080000054448016120b46881010031020340e0301e4644080c0a19102c40c00c0d5403041e507130303801d40b20542e100e06050251500f6070243e1400d8000700355903034000780901402e030307005001d40a0201c0190700350f000b6210450b108400c41c01001d01d0050f1018285c42c0f0b0300d003418403450a9507110350803460084110516100390503c0b1000c3e01090000070092031702140d290f5601901c1c482404580b5080540c089c0c55400c1c0003800c24411b603a401407050f013001c03030141e41549099803503030481d8503038400441d500003e034000580766a104000b05c01120310b400810303d94003000c8505281c14001070b9000100c0308001c2d4682921011400000c2018500d4540324156200201100031400c20140550062440c02542c1e01c0f0004601e11 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 622139802 1250 622138552 622138571
    0x1b091d0a0506010504030b04060204090f02040303050d110c0a0b061f080a0e030405130219023f0c030307030f0614240c01020c190203032a0a11100906080109 69
    0x5501703d40c0915080300355141d003400c1c42c0c81d20700001d50107403085260041ca0101e04805081c928000c490450f50140e13142410b00400c40e00b040c00810b941c90308a40400020403240f0b00000c0709118074032506005446075106480d040060000046440030b50141502c81c0c00e03101da201d00d4000307014036044040d00800140802007501805c1c558410307a009198010006001002042040d030000c01400b800710b52025206008075400ba640c82c009030b0750301c41c0560301008032610392031082203800d0390243c0c40d44e008420701e10000345d4613a200e51020b407c201183d040042013101440c0c25010f0018003d0607140e0820100b45018211211003600c401142c4c070a43c1c000e0180c0c0c0103507074210720445540500400041d503a59034640545d00075400104a0449400786500c00c11899260308065087c0c0741d0090f000d18a081d0038202c0300ea90100c2c000c64040080d841d640c4a0706404a410003030300c00400d114500350407031000000104a10851405d040000300140000188442540b20312600d04580c00404041b805044 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 622141052 1250 622139802 622139807
    0x80a1a040c03080f0c07091a040b0906121c020a21092d0605040f0911030a0e071517010b030403120b03031e0a032403110111011b091d0a050601 63
    0x91742e140ca01c5d1a00c07500d1400701e030000031640b085a801c1402901081d03020000818407003610144000715030700c001140001070584c00c22104550309014901c0903075020000d08040750450590450138400160300c800c4048003088070007010018041c23584103040700440001c29004141242034001d081816440302005110300c0b04095017455001904401040000d03103604c4020700a40151080c192800c062040008808080b03106482204001d1141685180d83d9401d1a80141c003075001700c41218403c80000084204900d03080e1504c408981e070307a4000c070440c214104402441d0680107105103410070410300000903003201340c03c10101c034100070105803561011700090841c02001d0030120b0541c0c80d40e020305c00e041544401088802c000e03071000c01074108110402c2030841c1024202d0341074860507030410f0002c0740c1d600540004021051503d24501d450440201d42514800c504400782c2c0c9500d444e000b2074450708016600d024204847c107403035140d000d40642041900b809404020002d50780c1011545592 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 622142302 1250 622141052 622141057
    0xc0304150902031c030507031107060b030f10050f010605280905102001020f1e0d020f180922080702040501030302060114040c0903121206080a1a040c03080f 69
    0x150001c050b640700e034500f144002c944c0d43c1c0105540340040c1c540b200240000d4040c0c410a5500c003076080400341041c6295840c40005c10b0103c1c80d050380b511455101181511040081450401c07440102150f03904291058100006068005c032051100c2032014001d0320040d03100c04084000300e0080d00441d0310400c041980c00e8405a001103400507076a084048019400014bc2e149215864000070004106015010700301e024040c0000f4502500300013140d440c44203181c0e945071118504213518030740826052841c0c103d91080902070241c1d117011450141541c1c040c2c2005c01e48003002e8138104a05d1500190012407800c03d0b403034040c07c0f4004680c0311024004d4100a8035a903070f41c094401c001d1540c41c0e08010f903542d1401d114000141c00320000b44245404d0071b0240041003e0180c075a8407410342140e1781c01203280c280d0600b02040010030440350200010358000d10b0020400880a032035519010305081c541c4a01105100102c601c48400f071100081600f44c00000b20ad80052019440d43c00b9805203100302e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 622143552 1250 622142302 622142321
    0x2d0106080705090a0f080a020915012f0106030c210206091909050403180b04080a060203070201020904060e0105010f0e030319020a0c1e080633040504061a090c030415 73
    0x2c0030200b00c0806c60750301c00984510b41900840301545660b4918030303a98007105031004520b000440c1042d03031181c11090301d01016840348260b8000480710501006207801c48542c0ea00a84088a80500800c00342c0009214080883d10005418030a0078058003c21800d01c9404401800b4a14a8020344400d02040c1820005050000014400c0e030400b4203004100c040d80040500e020800a000061060840340440d002c403190800500010b50301515850000d400007048802555002c00c07e440150361948030345405480421049500343d4148000102548403101504080c8860040440b1550381e0001c292040c214007446000b1001070085001c0781002224840140348003111440400c1c514a60021244142005c60712121015510540c0e150313112030a42e04a075004803029224849201c503035000482188a040d4003941a000c0d143c0440c2c200c440c03c590903601603907515001000032060b80065219034008a80c2c082e0a03040a13080482140b00191004001403045060000062115003006011 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 622144802 1250 622143552 622143569
    0xf05091503090601050a060210050717090a051209030705040203040606051804050c150921070f14010201061a0d09020d050c030c0a1203262d0106080705090a 69
    0x5a10050140011507001552800700601403040003107100c1c18401e00302d408030303020795001b001c04642516141e8007e0a0140800702007007101e01c2d0080b880c010800295008040f45001450f240500b070800c18105501002c12403450f6004021200c2d084e54001001c805079a8100d4005a4940b05c40ca8040002d00c0c85512590304200d200d001e007020880583c65030341c400c50051041c1c44044107400104003441c008902080400b850601514496040c000301070b03200c02032000e00380f030300c125100c0390b40500c0d05613194040d09901c3c0f64900f003484490041c010b0401070b07101c00e0000b40060ba0502a0880a07008002c00f8041c1c07039100455100040d840300d408c903001b001c0d009420305010042e5410210345070000403420601a00c1101c0f110708060505000010131112040d9a40c0b4001c44030303503002c0341d409020a11100c001b0000615450070713440b514501fa4001c0141071848030b0b03070700d4001040242c41c100315074804e80d400f40a240100100ca0b04800c2c0283d000c00985060b0b0354462415000944058040d04144030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 622146052 1250 622144802 622144819
    0x91b01090f03060e190c060801050402072a030212010209032b0809030720040c0815270a06030228050105070501140f0a0e030403020f0906031507080a0f0c090302010f0509 75
    0x6e20100036290b50542c1e51640c1c80a8403a0307220001d0100780d2044007002800803005940280c030100041105076800220507a84404d400c1d5607400040c42d01402c0e0808520070b950026800041e85010001c1c0e0321012940300f0340d02101c180904541e0341c408040b10454050003400300c0000d0140e402481200c1400c0c0d40051603982c81c8100304101241c0e07002c905683d500440c50480309a100d940100c0b0304038865803101c80c1451041d034985040c1b000701d8080903400007a00d0b551820020804884195151141c1d01d84c030f0001648074510300400c0318110207100c401003620300e1039842c1000c849034405400150740c4282030103a40e80585103000c2c2d00400c203810007851032a1a850500c410900c5407114a03005215200c4280300b0710100c2d046840d2640b089110080d88002614030b01d4003281090101c2035480580102500c0c412480c0c00130002442d001102c10600003581882000f0100b00d040c1303e2040b00b4142002c040002c892000805494a0450300011341408400400401141e100e00111344480b00080c10440c0b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 622147302 1250 622146052 622146103
    0x3050a030c0302190c0f091a19030c080a02010305010e10050906060d02030f0702010b06040b041517010b0703121406010e0a080709050429150d020405091b01090f03060e 74
    0x20078101040c01034102c0081e1100b0006840c0303215000303554403100b080201c064007181140c01c109c2e0041200342001070548980e1030000c0414449168100144110406860a461144001421524141c014a550500440a0000100003002e54006071102594070203119205c580c0026064060100040c0f441400041040030301002d1010480c080d042c542c00a000c120010302c100300040c0601d00804240c0ea000740300c1003001e80610504260482d91700c0c10200d00d06100d044151000482c05d8010b214404c10010303d000826a00c0410f94803500700407981000b07070031441c039000d603922030010309000d041043d88402d2800a0781c0b51032102c001083c0f00340844440c940d0704c5907000c01601041704d050b1200b0340e9020620214200b01c0ba1034082c05007180103000555a01c5049018441d400d6001c01e58020508441190040e1a10300c12140140340007002003444806807000c0c0c81c0552108181c0c0c50422516940c100100091162442c0030340c1d5003d100812401c1140002d2441c003003e142c0e0611200b480701d140c0e02d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 622148552 1250 622147302 622147313
    0x20a0f0302031806091e1215160507080301091e05092b05040e09030f040e0a0b0d020f040c03181109070201050c0403080906070b04290103050a030c030219 68
    0xf00000d282d0040c95040c100700180c1084114010806a56048880211001100581c8255444191800501c0100c0c550b900d4181a0b14102030091907070402a103000c148444c141c000702d1100007902d1070385000fa18008241d581ca40050006108424059842e40030310740010a030511201e920a05041007049140780035480d4a90321400c42d488a101410618107800760030206074803803190188952582860649411201045c0080041415110b0300040c480d000c840144038009000a14882026071124204401c54804413400303e10210f01c0795011000341b80050315501009582544202c0c2e0000c0c4980d40d50000390003910002032851800c0c0c1c13440c034012041040816040703001040950350b50302c856503a03240c203038202c41054a060aaa039800d100070000a400078006180c588000341c07003141099070b950b440208500c030541d011590002e10a59006210041504401800d112150f001c00c26524503240c0700d0711210080d4019041240002c2d10380b0a00d8001c0040b400d540f41464202c0840e41d0340390804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 622149802 1250 622148552 622148557
    0x310b070609032115050405130b06010507120306060e040b091f1701020d051806010e04020a080d09080f0a02010504030b1005060a0f2309010f140c0a121b060903020a0f030203 76
    0xd40080c01584c1801044c6418107100e11441003114503000001914a07484050486030000d11231810002c0400c058000281e0403104c139a80710f21603843c0490b440c1d060600250018001c00d11a901851401e0301071b400c03a948072214540c0211517800b541c105141c2d40d0203030001f01c41c007542042c592203040722020320070110305500030215951540320800c1107846103004200404141420f0f11800d138030100060103c50b0784404595001403006241420082d41c4000403400c217044c980c60a4089205180c3c10802d00d5028030118441d0b001c0e0030050410311140c3d80c00a00503000ba4003010340074a44d100006001c01e901d04000c02c0c00392000a0100f81c0b5050102c0b0024501490840a140095007000c2d00d0382c40e4010070100e071a442010600130700d040240900045914960803c461030801406c00c58584511281c44024446a0300383c0b009464940c070300d420104510842c0d0f9000324100036440d045468a210900c04400e8640c0d4402e9000c00c941a0b40d0404070b11f421410403001c0c2c600b2011080803810150000300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 622151052 1250 622149802 622149821
    0x8010312030605060403080a0c02040603060b03070602071d0405010f060b07031b030905190509090309031501060504170703060c09140405250c08310b0706090321 71
    0x5000380350030800001202503448500c5107a42001d001d005c18000160b080000d0100b401d0071b440d16000e8402c59070006400c4d00e90541c8240c1c3e03459039500006865082c24064040a00160b000030451a40303498620030220050080390300102440707001080401c4000e4106102d100f40f64401484280e403502041b8200da80200c5c81203012a42502d2611040d851b651404002d8580584913041801d2424040c040034030300f000e041e05005103403410701003282d5407140030080c012500b000045480302c00400c00d251800004580d807180b800902c8004119041d401011541a288020020040000414003083c5018400c1e00028400743c20a030302c0c0d0040941c008007203030843e40e0a81008015600c2c0030300384002c98000f5a1441191141e1280540744ca80c0c05040c03604a40d925403070a41c0021840c0d490300702440e0031010300d1516103400c1d800303074030802d0341840b20404110341c04880301c0002c2403030080182094401c0b264010403054a41c4006030505000d44150100030300300c0d044820b01c011030841442c0c001c00c0d4600 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 622152302 1250 622151052 622151063
    0x70309060f0e03060408030c19050301091103060d14120c010b04060509090a08090613030b070e180a200309161505090609030f150f07260c19080103 65
    0x901804000d1180042510028024001c4e081c291540d03107402e842c6078030051840c1d005030001c101007040c6c0030b4000310001c620101c40c2d5445842e541019204410b40b0060700340702e80208410b200b8450315654008410090381e03440f8085004445440f00d94904008418015100390b441c00b0414940c40b2070103400010115a08440c20000152541c04224504400f52800070482c3d12400d040400030b1501d00082404800080106083c19415440901e280406402c1100d440141c08240440217401514043c40c3d064101c44040070861031101c1c406034590001c121307404564544c04050100c080c0d9820103106020300c2d02007190380c0c0c40c0003c4d100d5580c1c07008498a00b0260310011000448402d02e103000740d031802465645034504601030080080503045401c0166160007005929543c0c0c0000700101407003140189101c58291505440340000d01500510754000d10040130f505005954070344680a4000c02c0244130b149180d25966825161401030024090030800251020420950004a070904803032140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 622153552 1250 622152302 622152317
    0x605151b0601230901080c0f040609020d02070c05090403231e090a06050408030a051e03190e011e05090c0a08010f11091f020c0d0f030e010e130c09090207030906 71
    0x210706001c0207040034884c0035141d400c1f003204100180341035400b030460100c1c014400701c4c4c05a01d0343d0304081240e0205111192241d8002051010852207504410081000304c645464a260940303000e0720300e010021004007040051b80d0729181502050342640d9400526000003a1280e1031040710b4074259002c540428803c4028048c00500b00344607000701c4040d50301c69005142040765601c41507503603030001c0900d10700c1d8401c140d500b51120b00c04580914456084c03c44a41ca00525070300c00c450481e40f0100b1100070b180d0400310b0f01c00d002c0d003040c1060052509150000075681d43c0f00d03062a4203013940140c0071503100f545290009002a4150010300c0d001d81051000c02c05000c021044031000d00c43d540d1400e1700503624160356940707180c03002c0382d2840f409194015a40a18442e400107081c411201c602100e00c81e44401c0b9410501d584800040080c1e80e0a003413101c540001000061000480511881c02143e01c130082c8041d00c0f0300c19464007004007160b01d000c2d91141c42a10b4041d0800e1024058000041d010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 622154802 1250 622153552 622153619
    0x8030f06041a010507050304090c021c030b0a030b06060c0f030c0d0c0b06060705070e01090f0b0d030c06050612030f090f03030406081b0c030a0e040507030605151b0601 74
    0x7a110300148180782c0740750300400c0d5040304010354154211642c1035070180018032001507441200d000703491b042e95555000d80244801802d070780c100b9648a1074040f04043c5014040e01c40c1c0e40354038003520180c0350481c115a20a550b07031000600c2c0c078441c8280a1040b40640c500c010020700c0004040e0100103101c40940f0080380c0340301d20480b441140c2050140240c00e854002c01c1c01400c08000904201d409201945c50041d252141840c0f400020b902c0060a550359050203000c62031a0b100e15a9466022515500d41e045641c800420090b81c03001d02920107130b40c400210700540e03200d60082e480410300d0720540c0d031152941c0c1092400c5800041509020341113841d040e10f441c2c5008000c039425502c0326101e94403103885180f500c6500d042681c2074a809241d04000e081c80c60301d000c001800c0041d0056031410034100841050000381c8001800d000141030412105011540d00c40a1041c91200c610080d40c0d01d070001821000010f0180c0c6d10b159081780a140001316030f400c50108680002c004100d11030416418 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 622156052 1250 622154802 622154809
    0xe030702061204022107092d2a0c0204060905130303050402010c08041e0918060b03190c090c0503060d0609020a0e09010f06090605150a120908030f06 66
    0x46610003035105504200341e19001031150740d040e800c18009070143c0c140341c40359848a041c020321004085060b60014104015182141c00380c58903d4a011b528402030240c4024030500740313012894020007040e01c0341d0507122a10003500c07010700c2002102c51440c003803c41d081001340200b1810441a4050350070b0540100e409240c90150500400d40c500b440c19138403880c0e403170880c018500507100301c1c10085c400440201299032080648090510301d414036841501e841221281d2450f0350740300b10071150a011150100d2007003400b2400d0903e4000c0000b140d05022900004d0400d5020103070b00c20300080e549504001d005840510f0019260100010410500340e06010b4407503000868005500443c074000c400d00164494110341400c52014100e20300c03070740d2120340b5101c0f00c0c101269505030580d55025840d030314401340d025040052026410410600d81807101082c51402c4c1c0780303011140980d002443d094114415007862110302c8181c0010000c0f03a2032890285213030381c0103551f6100340364405401b00e649032a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 622157302 1250 622156052 622156057
    0xa0b1008012912010b0301290316090e01020405040c270e04120309060e0d0905010509150306210c0f010503190e1f090209070807020303011a25060e03 66
    0x5050340006403207000408200b2000248844400d0355501c80015107860744090183c4100d0442e28488d070350300c808000c2486540030741d407155240d21a500c840b07883c0b041c00f400c0c07006030340a07610b00c0341000ca1380c1940454038501920655000b030f500945405040000700c0d9219051241c8420883c3c007070110041c03884d060901c241c0090107000e2503407241c080400e0008000c80c2102051351124103011424811139241c14040302c4514201040d5608800c8406c5590b176030040c0b10402a000900308a030400c0340c4000468502c0d0440310340c694980d400080460190780d20485c0341c812104222103940301c06005070a4a507290507150f024640501c03040d000c1c202056003e482500d119010180d4945680b0891120783d50103004510754140c4680664410085050303907103211007252007941030000c510091188188600b14000410400400c00c0d010300b800102c1d940401120b0444e848a26580410404d0210122492040014001070141213402100305582c8850080b0003042c040ea40c20404014940d981e9a100d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 622158552 1250 622157302 622157351
    0x8030306091006120c2c0a05041a04020d0e03040303120c0c02030a0201080601140d05061201020f0a1116060f0306050f0604230301060b040311030c180403020a0b100801 74
    0x919075810583c481e140c130b94400c83d07034542d16151488500846410017034040c1000f060403000001e400d142c2c080581002d030480070003801c00743c034100496040c98508510782503185498602c6140c0006081e222002c890b00310045102070201070f26600e5940e407402400c1007448040c021085030916001000751800f41070344036003141e0003402800305001c03982c3c01140c0308036000340302c6030500600808400e15070110002410010b4054070b800100d85c18407a0800001e08500c00781304101c0d81c0100003050703030342040005403150120181091282c107c105040c1904010311031070142d0449a010200090700b550049d0005080149a142000341070340300c1042c400d0f01f182e54200c00343c0292080004226010f84040546d21848614581d02148e0010b100003e084d035260350b00210015802190034401d20021004081440c48228020a4078554100118210085800202141d001004e002034203150003404030340c0300e859204800051610b01000c180325038454074012a01d441d86010b0030320b807180c83c43c1450030f482e0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 622159802 1250 622158552 622158557
    0xa09080a0f0909050714071505011203021018170c0a03081f0501021b04021309021c05040c0b0d1e151d0609060102190b0105010e03010b011202210108030306091006 72
    0x7540181551061b0551200000301c2d108415800007689800403072046602030a11125540d640c5005400d0080c9000640301d0b01031a42454092201d40b0070f0294040a021184e0007151801c0c030a4400040c03a050b80105c0421020034018941d411013003650100803248915001c0e07901c00f00b0000791404104c929806409504c0c0903070b0220039101c5018800400b000020b40d00140b01504d001c0c83c0303500701c030407843c00e41d400b1812917030300421216298840c0c080c0344842d02d000c00004100c103141c2601e031ba021081442c840e00d1070941c0c000620950144043e045001c081c0200310350307580c0104003054000c2c02841c60f50115046400074140102d54030f21900c460601c46c9441c408001d034251100000c010704108040e01250542c8a400d00982c00c403c2070508810b1414014411181c0662500740050413642c07243c00c2c1d00f886a403402400c2503251ba000f8200305a084452100162640700102964030180d071700c1e150305a2a47e0700d008c0002044e0100000031846002c0c25100c9440c15210600b41c2d02600c0a1030042001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 622161052 1250 622159802 622159817
    0x406061d0105160219030302060c03090a06050a0f09051c1404091d06013206120403110102070b0105130e0604030c020109091a010215070203120a09080a0f09090507 72
    0xc5601ca040641000006400048030b106110382c0010720462100d641102017411840041041c140c06016141c2d0010f4540b0300d25140d4504031602032f03220254480000c22542d41c07040802c0301c813840b0f5071100c000e50203403000801810095081c010b59600c0700218154400c0341000803d8403140c440d035450403151030500b5040d42450304024100000d0444000407000850320303010301c11a80b0000700003250007020510201900c2c000302a2102a04400c0c800c5880c0c40181e1516407550700b51143d2040300c0310359000082225a54070f40f840e080314000c100d07041355140ca60021075108140b21000042078103c410888010606044500c42c05050350040601c2035a16000b030070001d40030a014010507424a481490130b402099121040b00c0c00300c59500702c8058229240008040495030104060940e80c0381d0800d0011a514001800946c1c903c94029000c140724000804582c1c0c0c0c40c80c1e50071045046034040440742e120600e41c5001024044a8481c240000360701741d0f17000407401000d2003035070302070b0b100d5986480c1b = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 622162302 1250 622161052 622161107
    0x2031e040513022512020705030a0803040303181b1d010806010b03150303040e06030c04090507121401050a05240f0f01021c1e11070521010207030905040606 69
    0xc009401030244954100c04d100e1460f8540300036240d6280d146403044040298142c08400e00038500700300b540142d4080d502036180d41010500306426030340c0c4181d2510340072074850140990b692890185010060000300d02040094207505040d20f8602035039a01d50342040b403244000310380c0040080038032494000e42c001c00018030810040700011a071102030300102681041c41d08000c24a0b541c0940e20842c0450042c40501c0f00c14078082c08140d2003d0804c179010f2143d815252a0203840321f4183c420040d44000b648826004c0000c1c00030000f05000314140200610303c0d02c07c40c858054202140c0c5507501c0c00c03d498003070040300080c1010204040c8040c020303420428600040c0446080302c5a0294158458a2401c900b56140704400610309903c0b5903954604403100e6201c0c503206405d05010000303100540101c10160200081c461080703c604580302965025004039008000c032001c848880c035075000040c20b2003895044801941124400d480811900c0e40d51002110340d00c0da013020415503100d1099400 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 622163552 1250 622162302 622162339
    0x91e0b0403110d08030a15080607020c1210050a020d060614071106090d0c0305010e071a03041a090d0e0a0b1206030705030a05010b0a05030604080708030c0d0c02031e0405 75
    0x6200c180b01a0420303200d84496120b46146410450710702d441c5544030200c062004074140240030003880c1c40e00c0201030074204890040e48a40b154000180604641103c40c079050004103c1c00c0d0032012420004c12903801c05d032142070040c1d0300980c0e00064090600400040c294829241c035003031002e000341c8541c05d00c4851381d910241d0600703071643c803036010b8001d014003949a5035075899070040c1031140704540035084c91441e11500790f502c0c039400c100d06900000c1c001c0041c00721104040303410981000d01903a5950b00c0e40f920002c045100c40c80380790503603425810025aa10001001030014140d0b44503600a00e100c0020880840040d000c1d000507980207201500300007107800485500400e00505844e101d949540102c1d18164000400b0344441c4c1d110000e034486402e00750141c2001d003605130003503d0349240030b0b160b00710300d88140c0400800e908400000124452116404c0e01d46483d602c2800b8405941000c100954036046004103811000d140489900c0c44130b400004c40c0c04541d8060840c255200409491 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 622164802 1250 622163552 622163573
    0x2011e1416140c011e0507020a0b0a0207141309061407020604033009060902090901020d06050907020705120709140108060a05010e060d060e12030f07021906050a0b0d03091e0b0403 79
    0x105046c4801030086c800147d4401490401070070002d6a800d0710340c0740080000349048443d6014401204810304c6480c1c0381c1d15480d4107141030b00190440400d442c0054902030340104040c014640c501c090f05014800005d0340807607600e004070b009a607540c0f0b8080d8104900c1e0060750403280300382d100540c0c441d415030380d1805e04c1c5c200b07800c4540100b00006501a03103401091009500300d807500501e940c00180f00d408034069105200142c41d003900c00460514050310081c1da0f42280c2c0c00382c80c3c0b01d643c88102151001c101003104401030309002e0014081d40d200080c051340c00000078082e004e001e01403600000c0c1c102d9014810b080c1202d0181400603101d0301c80d4014080c0300c80c0c44101c2680c4060b1161351040c4004020030100d14900a1010000e41da80b070012041c0744029030180071078045400881549102030f415078401d04000c1e0b0003182c006076944460340c1d400001c2041d41c0c0c8254100e80203400007000c0c50303089003400301295120f002000081c0005842100c50998601511071005414032080c070109510040c07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 622166052 1250 622164802 622164857
    0x70e040506010219030504060f05040e0606071e0b01090f090f0b060102010f15030201021903051c180f060c03060b16050f0604141902011e1416140c01 66
    0x65030b03002e600401078a0095800131000340c02280700014100480c0394840038000002c0028980706040c2820400382e01800701001c0d0400b4801c22004c1000b5090203801034800314000d42c00140c039880640c3d103188c490417501092007412682850301000d4607012445000303032602c00390700181007010030b00113031b03511000c015010f420241107640c0d40c0e041c000e03049147e101e4a07003a03007410001b403204149548002450110701503018503001e010110380500094000707064911130790580800c1d00444000d081010003c10034200202030300300d950303000c40047c0164540c40021b1700703000e030344188192600414143e0940340c0903c44c2c1101c107501081140c0c0108580080c02131030501c01d8099411a0007800001ca03d40442900c0598005206503d5002000c07010016400610415600c01c1e82c0500c06400280490141000c41d01d69902c10394404500c15110301c08885407485410001500c40d100100141500b0075541011503550300700c04072141e1100400601080c60740e605946095400c0f0072001c04140c80f00d902003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 622167302 1250 622166052 622166057
    0x40b03060d060e0d1106060301020a020304061b080313150510170f0106032f010f030c090f0b0c0708032b0e030d091b0f060518060415020d08070e04050601 68
    0x340340407401074043c0410000d0a945039110100c2d503040541c0c01b07013007500c00f51450b44268410010307800030720340100030754049546d9410326002030081806824081414090003c1c50144008204041044100c0192401500414810742c1600c5110030b0401129010344060100164a080800c100100c1d4507004000e982d00c5130544001040e000c49503425944150811a1103c00e191400c214101d44c00d00800c1e005002c4e00d11701e6140115140018021b069039040b10420075031a0004221002d0141903440c0c000c0c41c1400710402c0700c594580d400e041c03541002c0c1d0122024000c1781c3c0002104a800070903114103d680412182090000940e0b94003940c03900c010189801c3e072165034800c080030041c00070340f291864034a030128058007a85840d026000f450f244d0380c12900140780090182d00b14503042c913403d4506600700f41d0745d0703280604240a0390314110200503511400001e40401c4801e842010160802001c0c0c0840b07a4080d030b2100181da51400845007200040e481007840d0341d1510b410340195410607010b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 622168552 1250 622167302 622167311
    0x10b0309210f1c050705070210030b0a0e04022103040501090902070c0522050c090901170a120e0a0f2c22020301020a17060d020d0b070504150305091002040b03060d06 73
    0x1110780d44142c2c0c4c01117580c00c000c110701058031420b40c202035102e0b00b900c070707010b1400b040aa5013090019100c4400c0f4043e403440c8100e610002021034903a2007000c807480c1d234850840000400c40000175503499105000c0e184c0000d03101030001a54030024003e442103a43d0003d801c0801504110600000f101f100d032580b11172031195007460322a00e40e1441158018459043e2040c1c1c2c03a002c95092026125060b0321204500b016403e1400c0062404252581844c0e8840c51700c403038025060108480032a1085915644a005044002550500004030f80100c5881840401c0d070305204007481d0040904c0c01161005400141c00012414000c043c0c030301440c0003504184e411070f550240c02107400ca07044034044501103101e24a00e004400011440320307502c010121005e894800d00341d40420304851000c40c00501c04110840410103080c0036009440107049100300300c508148c2e1100c0010068042520205201d008024880c2c984c44900e00846007601c851f88805071a589a15041c484044607541c4162420350341c8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 622169802 1250 622168552 622168597
    0x1b08030f0904050c130803071703040b0703050411040608060604150e0a1e050703021315050906090301060b07030c0c0501031a01050a020705060c1b0612040f08040806010b0309210f 79
    0x240442c171000d09210720003180c50b002c0c0d034640042c0c4046200e641c014110000d008001c0003a0000c9000ea900010b10f140105003502c4038903141403485a60f0703841a48c03180c1405c202040748a800520706210700c208841c2400346250030360800400d02501d00600440c8088a0001904000c960b00900112002d008540401a03d24030001088480988800c0006030700003800200702001882c8040107407200c9104040d8200c0c023204068030901c81d420005010f045c004c105170ba010f907001c0d488400107100504e00c9a50f14041d80c58002c2c113111169200f10ba403e4060040403803154403911401120440c100744c8038030100c144a00648690f040300b00f0050440c0300d05500440d0585a527005403da41c1d15420051581640d02c8441c0440c107682c885c056405124144604141030740e1030046140c0040d00b0020302c0c03d606d071050404c000781e445203070028200c0c1c1c0300361000024040d814074000c600c210400350689030b000f9828400380e02002040340172101d58402c1800843ca8550829000307000c072501805541144200307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 622171052 1250 622169802 622169827
    0x102070510090e0a021b010b0303041202030f0f030a020d09081207051603031d1e06070203030f070c060809030a090605030a0204051203070b01061106040b1803071b08030f0904050c 79
    0x281240c04c0c0240a4003c80d50780b03156251503401c0098031300507200030321034042d040011965030300032807081d0441c121310805850103544040c01550340c84010802030300d0000182c02416581c03588174610000040c0b180d13a0f11600401d00c2a0103d0f419103082e0b0010300710182d03c0c003520b4841d5821002041c1c0f0603000385074907222034411040300c50004510079201c80d050101d0019800d41c1c3d12000496a902038500c0800700698205808440d904201d02159196181c0c41940042803540c003811290410031100019200c0c28040e0398040d101c211191583e0b080322640e0703a400099203d0045110000214606881c103001c003070f01540c00341d03502c48200000182026500c1c0000386a48000310b0540c000c1d9000090400c09000094004502501d210304041c000600d000101541e1203400030000307060400404081800c44c1d0394142d0340a8071042070300c2180d441d02c0ca182030039005100a10a0406100d080c0440041c040e080803040c0d80305161103000700c0307007000105401c0c04003405004298040340241084032001050 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 622172302 1250 622171052 622171079
    0x3150a050d0b07091d060d0302072111100503130204150308030a0b04060f1203030b091602060105150a03091a0108060a0e070536070309051b010207051009 68
    0x10300482c0c000c10542040c00e400340480c410b40e00071310039035048402c8400ca80c002140c2d0860300100281c3c0d0031608038103a0305080f828010160400d900007106841c0340c441c6440060383c0c5005090141d801d2034102d44108040082d6091001e0354640499030078000216040201c414a10040d800079001141010203410004202d10160300300b00e030b004001005101504082d1711031600341c00b10a5804000c030504000ca4051100241c1c828042c0704500181039008041c400d80001da182000504000b205003400b210b01c143c0105801650801071203214000980c42ca80303900000540b5408411461502140035001c070050201510141c400c40140380501c400103040440301030090a0010160555091001d4030070306441c8907038480c40d4180c1c0418028041d40d5290048a000103051005503e8549000c818018554079980d0f0000c01200c6c03090100041d0a8258002d078221512030415580c54800e000e02200007400302c100d601d40140d002013003d02c280c2c01c00355004401c01c0d0b140d003403490b121966041c6903100807 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 622173552 1250 622172302 622172329
    0x90a0218090703090317011d091c0306090b03010c050f0a05122d09030a030e0a020d031d01030608070302090603031308010911010f21020405181f0b03150a05 69
    0x20395103000840a1541c000c41d01884441b40c101808015450924180c11070b00455882c0c605030b00525000c608024810000703e5070304004c21840310700e51041104050010580d92040844080c1444600b4440d0301c1d0601c02c070f08410401b07450311800c01d28a40c441c81c4480c4c120400302c00c1801410082250f080c1c40340600c0c14401c03030388034680b1400e05100e003660411925404d40a84079003e0010148106058080309131150101d6920700051401450f000c91450551000006504044034192580c01d15034040c0641c1c840b0701c07070b50105852000500004400311501442031080b1a040707100203000514012041c250000f0000342182c0c100f0031143d158140840b4254009003250395100d42070b008100c0c11840c240c0c03648109083c4841700012001000d003001e410003810301c800915054443e80c2201c83c3e42e050b50301900001d07041202c860308007548480101c01c140d80e0f9411882c48030070300030400e91320a0500b0080e00c03850b45d03c050558403190032402208400a843c95881388010101140685960a030340141 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 622174802 1250 622173552 622173557
    0x10906020d091106040b190314070305070305090a021c020102120f040302030c011b0f050712030e03061503070e0403140712030506040615050c0f070602160e06090a02180907 76
    0x656000b07141515610120565540c014801840100010419070054030010b104190a400b407820802e0400c88c024040b40e0555a50320070140306019001380c0c561711880c0714505a0700c00b00040d80710020140d540e01e00c901d000a500c240500e141d1103061308800342c88a440e52040c0112641004480c1c0304482e0f581000d50800c0112034041000c10644c60100909868080c00f3f0038001c8400b0680000700c0b502c1c410319200a011600c01c00c0c105802c100041062100618072007010344070003185494000c22070b841018065100b4441c2d00b011031030888070210001031850004006013005481e111851a50318070040080d0188240c902200c00090032a10080600d1442404058411000031102800711034002c0d0440d40141d1410b541800301d4426000b40010a400c113003002521030a14622403442c00c080e90705e06d0750481c040e00100146403030300001c20014410f5010001d0200c80e8650846022220301110f031280d02c04050703000f1500f52021b80e4003c20f0441410b0810b10b0208600c0808078001c40d40a0b07414400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 622176052 1250 622174802 622174811
    0x5010b1605010f052404060b03010e0403020a02060a09050306010e07081f1206020918041e08090a080105060a0801050c030105060714070f050a05060702060d0203060d0c080706141306030e010906020d 87
    0x19007024901c900005c101046404101003800d00c040340c1514001409410041d07a4080d000c01c017454001c101920150398014a115034500700c041c002442c0d4074041c411940648514070020450100138200d60340314610b01d0703840e48590340d1032003800d003a421540f4415803031080c00703030b440072400b281d801d4200320100d80501c001603aa41c6280086c04603440c80c0c203d040818058100c14480010a680ba850016101c1c01c032005180340154205400948201c40b05641d015000f290000b91740310041d01700e140303c2c0400f12240325007141c0d240c06060136189d00f111202907141e02000180b00314507103140540540b0b8010301c903100812034007840b40c2d03203481c080c0d8105da0b2180040c45001c2149141c440d0460b8060102950350906145141d40880c000b40a96018000c91035000300000790f441c0c540c0070021603055009001d07042410b0796100181d8681529000794000034006a038031a40401e0b80307034110781e0780700c610550440f1030919001c1c080307004003141039140643d9501ca01105011603541c3c0080d120744c8002000004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 622177302 1250 622176052 622176091
    0xe150a060f050a080a030c1b0807030b06240d0b0d06050f0f190c0c02030a0b160c0f06090f02190603180201081302370626100902160203070905010b1605010f05 70
    0x20331400001d10711449038000d82090b003404281d0060b07001c0c00c00243c0c0c04003a00c49145241403006011030554094100b111181e03980b05010003034000314041c0d04080b1640240d91128000c04408002c22a02140104030206007405440324a90140180300f400e4607203409074010940c0000d00300805172105036181101c0c042444617402410003141600196800c1002220933640d892260000f4101005090182d0f500046418080404c140c584404da0042001401c131a425000d07403681e074014050b5200081c40c10207403090440b4a04010192603805850b20101036840c94821100444001001c0341c210005402c0742c1ea015104c40c06d0407284100030607070151400b41d401141c5020713142d44c4c2e01240820902c00e4610403950768051002d02c0709500809103081c0f555a2100640040905070b100181641c0300051401250307540b4880c035802d0500c01c9080d1b0340304d1a034640840c001c5d01c41c28001c0c0154510100600c0c0040090a104040031520920001c550b103142c0c10040b1046560446100038580c202e2031014 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 622178552 1250 622177302 622177313
    0xa0c0b040b0f25031508030f03040506060d020a090f0f050721060e130809090a09030305100f060507030215010e090d1b02040e150a060f050a080a030c1b080703 70
    0x1d94003d100c4201079000140d03012000410000c02c1c03a15405065903011031070581c460320000803014010708801c032592019a2414000c841d4800c541c00d48050042002080d120310b0a840501c00c0c0c00d0300100600503e50808186500801d050355203040515510b1940f080100c504d070055500c129038503212540104030b01ea01010b41c0e00c0c98072540d403892030716000d414440d11341028109034001100b42406920580d003440d000b80c1a11921310941c0c0e00030a4030041050132102070300892100c5100c0e6800384103e032901203800b100c1903038901804055000f508010300c401441100584119800b91045aa03601144011400110000e8014544402c1144200111403600304548010501940740c11101c00e16512030205494071342d408002d01c22030f281c0050490300f00c0104403000c116191038540f50b8a90030115118401011f89d48075442d0a01040710000070203290030401d2500329440b0001820001c5426602150030380c0a001d0215040c04007030420907a40001454510080c26000004010341821030401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 622179802 1250 622178552 622178581
    0x4020d1d0c03191e061e0f0207020108070e0a03140705032b0509041b0804260913020c100209031504020f040f02091c02040c0203040302090c0a0c0b040b 67
    0x406000f580402d030040d042102581041000c0c0340c1081100d00f6200300d28500b0b850f18119075502400d41030811042c8240c05115561101d6440c1001c0020081e0302c01d03c03600b071000d81c014000046e0200d5610400500341c140100d000300e2100d0310040101c0340068580c0c0d20407030b84466007614400a40c0c44100f040c000e5050401c5603120b1394840d02241c5241501029801d0000703030141c40c020f003c002e070101d0340c0320b0180c5a68109801c005024800b1002149281d980103146043c200d41c161540c441d2040c9066420105003649242c4084019070f0030303c1c041c00d250502006409000300d410200f0750070480c5007012007042c0311a014001c1c1c50100543d40f071035030408151512010803400c4040c21000b1041c800140d8803030006800c81c0300c0941d004162900c0684540d002802a00c11580e00001c0c00500c2090030b00b110003c1a20b0030780300703c1e410002c000058100300e941c1d001c0e41c000250056101c1003c201c0c11481c1e64060301081c030982c80d0600c100306256540c4164908141d40859903400c1c1c9409000024840090 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 622181052 1250 622179802 622179823
    0x3070f02190b010905011e06030b01050d05040506040209060123160203070b0304060501050a050a0522110a122028090305060a0b01020c0f04090812180703030c1104020d1d 75
    0x41c02407000d0304408031f00d0844480c3c1c86540245580c86d504c040c07140c0d00581c03e8551101812804203e50f14040c1009a107400302180c2c00c910403a04080014102d602a901480a00d9800380080d00e00400c3c1c240002d449621026940850030781c948031810050340c0130001c54020b041c0c55022651241001e1a140b000d50700180c0000b8803402c1880010300c00c030340301c0020b02021101c00301c905a5555420702528465507072600400030805007040046817a00003c0700040440030040d964090740d500d5000010000c90300d000404c0e0030360241c6032400c0000c2c5030081020307003082d4489281c0c41e9900c400000d9040c1d80d0b8a0302c0c0b00602c0c00309171007003810014000f0610030a0340c04901113109000010700000000c0d08d40d02d6854000d4803420081c206820b05440b56805000d1095226804035a038130001b04c00c201c044413049515110210742140082d00d4208080f80100803642d0544800c14191010756030410305044e00e8017000d0308181d0030310210310000000d0040b0852041c2d02e140a0061004000c1c03d2400e0000c842c9 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 622182302 1250 622181052 622181069
    0x5010203091f09111c170418020403020f0f211c0302030f061504080312100f0b0304062003160e010207061202030603070519050102060f0c03070f02190b01090501 71
    0x1643c20b010034000d0015081c0d0080071142c40c40d0510020456001131260140c0c0079001d5041d13401da03090000581c0000b04180c54841c1c1c980c03c1c040c60f006075201e00f60b200b2030200941142c9203681e041c0c56401c1c400102d03215a50001d01c0449010341200a00025080910442c8090750102140c001c110101782c0400700e500f07140c3d2401754030790f180555070606410300c0901440d00070203140c140752603801c201c0c1042d00d002e0450742040d00e666503800e004006041c9400d07030f21030f1032160b4501400504c0710700c6003141c142240d800462590960b9900d40b101c0009241000d42030642440741880800001c041b840150300c148420004000900b400c40c00081c1903104200485056620443e0107000d003641000d481050341c4440c0e9070241c0e8a944000c00319081520030740c045500004103403d1a80603084042d0241d0a40d03d007039081790f0560340c603400c95103120641507500106481c01000880e038210b2251075511220581801140c03400303500c410384001078000d03240d01903401445200061102070039601032075004103a07d1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 622183552 1250 622182302 622182311
    0x1d07050d0f020d0f1b1d19060303030911030f100903051b030309010f020a0909020d0f0c05030f0702010506090403081e01080a05010b0f0a1203090909151b0e010311040305010203091f 80
    0x80760812040f491b100310b103100308003d9000105540e1018110700311030079901e034003403283c5035403490040d000e030900260854403d03024642b42c6129040000381c0385400910708000781f42082528400c03e00411001209804000c0100413007607200214517041c69080044070019541c0745001800700703085880c4090000401d5004010546259074030000b400705030343e0021401651b070144000034000a0400e40400340800b070600f06154075a98001e00503522a0480410350300c541c2d5582c400c22400c0b41e604564807940518031344040f07000f1030301c2480d240b940a526406180c10703542c4250400800a403090307120504641c011108002001428000d001d2104000c0e2a61030200540d003002881601083c0240f0250f090242094403d040c460352441000341300c100410423521030182086826001c1c8407002010090520381c02004420301400894540b02c041d84d6140e200d07225100044000d419844422400703028140310200101c2d02c00c0c40110301440c00b8400800d102c2d8405d0a9081381d43c50030480091405190 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 622184802 1250 622183552 622183559
    0x609010b010914030106030b070f0f05030105032d0a0b0907050901080a08071a0910050609060d02040f0f14060306060d03090b131701050a1d07050d0f020d0f1b 70
    0x1c0990083d642c0c000d560018201200001c07038014080d0303501c0178040811090a101601e81c0014580480002c103036030ba241e88250041301600d003407000384070307154255002c41d00c007421038005d00d50b9030300000d0341d1030080c5481400d501d0300162a01901c103d00b501c03d40429410301249140800603c00105800d640f1500c0395803401c20110346444202c4006040300500241e10003c20001014011981030103a03510302c031a0038100740c50b990341c480081240420b5840c150100d85c07545030400b0001d1250000405103824142c403075080c44003909046415800e03551302c0d07402c44070360b8610a00402034042e10344c00124000e450860201403520304058070403030013000a09070403400710380d0191440b4142d4050341d0181d45d03213103a100c00d0918101c03101e0f80550f41040c0302c11751080c000541900030902a100d0300d0030034080020b40744800000350403c2221100c0303d601c0007a04200e14105209044925400b03800120645406034010501034450346508590b00031618103607104002401117500d000942038030f06842201e04 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 622186052 1250 622184802 622184807
    0x30f0905040b061204060b03070b040f06110c21030d241a091906020610080129040603140a0b0903160f050a052d010219050a090b04060c050609010b01 66
    0x6209a0280113040400050700b4400705070443d44442d440074040712402542c4030081c2040b6001401540c02c0752030342c1c441c006600340c841c18044815004040140c9000c0000b0340800c500b4003428039021611040914a4001c0d280040c005480707003d5680501103124105200c01980140d00e080d090090586880002d000c0e040b0b6103c90401945c0b41030306000c2da01d110a03c00a80d08180d054030302e011728080c1503030219407183d0110b40d0901442124103440502c07610356610509070307100411108141031412289135640c10b030008070704000d00f002810000d0b84688945650070395040d009130742d0702d0300d41c82001101c040100c0070a1565001021744055402c1c9600b9440707008504400c4030010700000111651181849418065072a070380b58480222520410302c030055402c80340c08921816844045244110b854030018004c44e0322000d25070800d506045003141e000c2d1200d8001c64940d40800000040210f019505000244098034213910385035804003d0340380c11450b0100040c40c040c0c060341082041455642c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 622187302 1250 622186052 622186057
    0x6330804030518100c0b06010f020606060d0e01020a020703020907080403080604050c0903100b0a051203040603180f1a0c120f13061409070506030f0a02030402060405030a030f0905040b06 82
    0x141d25150180c0c0c0d0304503041e14008024520340d006a0b1003040e207403500985507000713507800c10305a10613240201c20369287c00064607404070030030701000581c00c0700c0c6c00a11a40340060040501203172154000034086180300320242240c000761503042c007603400190240306500e0900c3d5011303440102458071241c24905135800506129018140c80d02603134555011840c50b8068005032240758001404440604c0f420002600140185e0041c260240c0081000481c4da07040125a000000c1118070096217400d2400340e0480040803407803100b4240801026500700003030702c00040c00592030701079840100074081014840701e0301240074001c82c15549041140c1c00c010220500315a602404a5208820503030314198104c5c0e1800d08000b00601007072a103005050150302450185000b02207010407a822162035005200480c030007500c948224015500c00112031100380e4000b542c1c003a102130141070409941d02d000c00d1601c2040c110440c00b0611900034031416980c03100c01c0b0002000c04813014003031204854041a51032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 622188552 1250 622187302 622187311
    0x309051c02120f0f0f070b070804020a090e1906091b0801110c0a11060d0230070c060b010c020a031101120204150c02121603060f06030b070e0a09063308 67
    0x4004150041c41c2d000400582c0c1b43c45410074a640e9407490142c800605d6103070708032001c900c104440040800c500d0400d2055034041fa60980040c80221509200b0400a174a422021100d039901d5080071000942c0d010b004084002074104902001801c004119082d115919003014242d44280030407032391104005002003d9640000380a015130100d4070225082c0d1088002081081b800002d110f0110000424696080c0641e40400d42442440032120402104103540d80b000041d9402140008620103a010140e00101414070389114040d580c01314200c1c4203541c0c415105108051074882c01c95030001114050300a07042da0440c03800341040c9e0b903010103007210050f18040103110400b140c03c5441c0d407803098880c407005108551303c40041c0c0b00040c204103480c5c08215807003410803400700c1030a00303035000d0041943d43c41000310640e81e0300c281e03044a84c1001008000e5208010f8180000c0784800c0340b2030380005d0b20b0078002c1c80c2c6403e203030b925041644200340c2203800c10882c040d11400913599400708016420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 622189802 1250 622188552 622188577
    0x81b040903030605030607020a17040e0c0309010f1b081503060c0c0705121c0309050a082206180b0301030c150c050f06150f0a050609010309051c02120f 67
    0x40891a06045004207a0f0360030454241c800e440c00e00140940004034607045a114599005892510580d0842180940e10601094030818004101c100c41c8050166500460300c1d0000200040b6008281040e0303015001410310300d0309441c0d20030a50790760205e01039038001160200000111b050202182d6102d8004010921004002c5030501c0d00003024003100c001001c006020314280c0212400d460340340d01d6030703194210000e401d0701c0071040d40c1c500901500c1f0911b5085000f030411101507032604640e6501155040c0d82c039801c02c45950140c43d410f0704004010f42029500c0d850003450000c2001e100380c02c0c90f080300340c1000041c00104001020462050199810100e901040b02c0704010159090740300740d0002400c901905100c07040c0d4001c00242548100c58000080003240e09000c28003605180c1d911a440d00311595500902c424140400240f941d20418540020200601c6d2142401c00344030103981d0100c21090411450580d43c1080812460320380d140000c0e14003128088a13503181d10030013000911 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 622191052 1250 622189802 622189811
    0x2517010221070e030703120206090d0c02041a09040c0f05040e0601140102030c0601090e0c01030614040c12060801020c1002090a0e04260a11010204150c0f0501110a09081b04 76
    0x10028031440341800f00300c00250440f80403640300c0c6040181444e82040d10b1006204803400901103c0001035940d00000d19511290b102c01d545409100203065003582c00490010300c0c96241195440b200e228502c1540101002c284640c03c0044e18420354034a6888644a2800d02c074403c0f456030804120325044503079815180c1d8010801400603815030064400d10310050051000009145a998002030b02801c0542d041c0c9201c0e10304000150100e130b0b00b074058500704c0d40c2c9542c841e620340d04160b03200d6180031440d420700d40c40e401c40d00e007120010785007940c100c404940d4001c00c2c00078540d84208044144106030290941c144400783c000700d007000c4c00611480140580090104051210311442d40429040f80e41c0d849420344015040344c0410351051f606c40c00055119a40040b9401042c401d82e0305651910504140328000c9010456541504a10a84280b8403158007100014403d200e0180c87c1400da001494a0b11305021340a01045065441360b44a0f03003104016144490a00c5040d01c128942102c0c0040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 622192302 1250 622191052 622191061
    0x1050114133201050a0e0106030f110c0708060f09060c0717070c060f030903090501050901033201140d170d060611100b060405122517010221 62
    0xc09442c48084440007004500c0e680c5035284802c0306855216284819110310690303030b0340c080c40004455885002d07440d502d40c100500c5090f210342c002190070b031841d601c0454070750340300380140c070280d0b014564500040e03000388410001c1c01e00904c0241d6200c400c01c0c60004042ca00340d103010b44c0ba120b0007003c050040744005010410080c440003424108a030314628652280f00c180342113143c0306914090725001c50404241d924840303119001d4400e24651658400705200d00e05001982d00d50000110b00d410f15841d0308800c5400c01c40f01c070440f000000e81d01e0324501580542803078510b0108041e0032800150a1851a041054035503038204030036141d0009010010205451000c0524060028a080340d6401e00c24002062035102c1d680c0042d41140c4019903040c0802540781c001107407480c10750b440e04804248070410061074003510000703403014090241c9610728200079140a40c140002c40c140002170910006100080e08101c211803900000402140b07480505e40855000351440030215034580c2e2140c0006 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 622193552 1250 622192302 622192339
    0xd050306031f02070c2c100317040504061e0b0f0910111606021f02040806010909200f04200f07050c15040306051e04060207020f010201050114 63
    0x1040014128481c1c0c01d1205500703040006540304500560741750003502030200b812901c2039210301d40a40501440860890000b154000c0d440004102012042d682c031000404540da42d074900304142c0e00940000e50ba43d0508c41003004584858100c1c820300c050842c1c1107140c4109690341c21041d154021080b0380c480c00361400700756061040461031500720b500c01038101c050f0b0f504424821040880780d020340320420b00c2d103e8060b241d41030910803000181d03c82e05400060645142000340c1c10300404001510b816110310b03556290403000e90100500e6580d4a80c0c00040c047c0d0801300301d0a910200c0540b941c0c102c45a80000c600040622416118a030341e40495094103000d810598596150300003400d40f02c16080c0d15406a0382c100380801c0e5203074056203a914801c0e24000e8000c500c03008803039070039508050550722080010800144040f500040d609040030b044800395007528490b80c80362002582da500390b48144072800c403150020030b0640e0b042074014055010007442040c0d00000030381d141140c030401c92166 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 622194802 1250 622193552 622193563
    0x303051c06120303111c05191407080603011109010305060a15020a0b01050f06031b370215070309021302120402100c0503160516090f1a030d05030603 66
    0x12102501e1408400140e00c9480305100b14070180282c5041001d0201c03402900194440e040c200c0d420922103502090300e100069020540003803024030400656410090120203c400241c0101c407003603241803c0181c0c0303d40c01030300f1a910810a80c02404128039080742071311035009401009041c540ca40c0c0001d0b080c5c1d120501440b0090001d4040c40702c4030302c10352002030744071b90f00c000341a140108410000f2559081103140150030701c001602e40351865682c04030b00c00c10f08207115040071070640d040000b04030000c1c264481c60f1000c2183c02581d4076001070b4400544c081114100c0000645d00300f113000c40300600d580842940c1c00f40042c05c000c95140300034400a1100303141c80401d03011062000c511a5981600b81187e244502d10030b4401c2140340b54403100995101e1050b4800074815407040015801c010510060210468031900031284220085000c032010381c903142e009030b00702d1780d5141245d81d22003000c0c0c06014011880c04c90390ba44084800030209446500050350300003840800004120a074904011 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 622196052 1250 622194802 622194847
    0x40b07030b1f050c06151207030c0905100b0c0309040e010c0207061b0510050603070509160c0c09050403030515040902150703140a0e101d0d02210c04061a04030305 72
    0x1070320b0486c9003250042c4018001245068000c42d840034400c0c100d4030340050007005494001d00400b000c51301d07054200000d044d0007080c0d2840300151103030005940380310802030300820703c5500c007458681c282441404203c40380703c21108143d80c10001d0510410b600421038109031002e0f80b0f03100300d50b8040303100000c20090090000030460302c61610b1980b1603041031b61289014150460544a54594480070001a42400d4503050386c803111034400041050302880440c61f545110301c0d82544030f581c0d40ca4000c000c8890841d030a03030103c2c1c0c842c8204100d40c1d100c0350b610110200200c03410841128150007160020603a94bd10100314000059a0024540108411000001206041986c2d4401080d00030109044d04aa0721f004081101004505500605581d04168131441000a99460b071000f005401103942c4000e03a0001000404842c0d06c0b4010009413110910082c000d00c10300c94143c00b4407086482d030361701c45030a0038140c03c40c50100040f030321700b2135040303a405140075500d4949803103100c001c0c0b840084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 622197302 1250 622196052 622196077
    0x120a0915050a0513211b0317090715081003020406030605060a080712020616060612030f02030306012a0b07050c06010e0103050c0d0309080a060603060e0d0504060f03090605090105040b07030b1f05 86
    0xc14107010141d010042d403421803c00841040540c032760203520755560110380200000080c00822140700e1a1182c540a5400f03103003000c80c425240c3c3e4a4001c10200c403020303041541c005840c0c0040281c0da0a0280070003001702034032001402c0b06490000000c44803010410b000344228030000b91181d41d525189e4814a450707030484000c0001e559195040304040b00a800110082035a6000e9420103038000b01c148c80c0300b03420684900c5035130109090341840d0081406003401c807200512004e140401c214440c640d00c510925141c49a81d04150350b0810b1400c0c00584c00a0038248103203005200017030b00462032031500e05c0c05039074003820305029103810348252001d900598420701c5052503601c1803143e0354202078100c0c0c0c002c500410442105101072178841d8204000140401c1042004100040c030820b2919103140d41c502d00029038821075913810094031020f03a0700f010542c0d1148144000e00910020769030704081c880c1020000f520b00a03020491020104090000800341ca51a040b152070190044500c62203125 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 622198552 1250 622197302 622197347
    0x105162a0605090303040b0c0301030b011401050c16050a0911040e090703140d0813050a02220905010b010311120402150f0a03050129120a0915050a051321 68
    0x3150311a56030303041210300740c90b450307c09004108807604910849050381d411031441c40103607003403002d50040400000d41c81070400804010350070300100d0034800030f9080300600c50700c240102d280c041041a9040c0542099004924040c01c124081a050003124200e48080851320040c0da220501d40d42404000d603c041c1c8540b082c086544000034020994003c0c40d4a251184002034036420f842c58603410311400010059882001c105000d4500132528080161038421110564040c403211042036407810300707045405a4569080315007030b41e00340c02540c1801441d0000c0d1824240658585060300b01d0260005c1d00030034510502007801642e90b0110350302034030340c561400c0c7d0301c1c442441c0c010005c003002d108401c0e40e0040e1909458507007400c0c1c041c0e1401c2901c11402d030b504009044144221503400030384035661b540ea0701d6044100081c03002c2d1220311407482003c5c000456207000070080c4240d810040581002d242c80c45583e10005000c204040e0baa941601700940b480300c80203806680c0743c0007051800c0491442c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 622199802 1250 622198552 622198561
    0xa0f0608071d01090506010f030509010605040c1107080303190b0a090203010b1b0303191a0a06020609070504050c041401090302090a09061103060609120316060e0105162a0605 77
    0x682054510342e1031001c0240c903030380c0340084c4045681c01e036581070000310301c3e00d40300320160720a402107a0400c00b11400014821350740c400117000c5901c50310900c0042003180000e6500210309000c003100a21840001d5840c41c41c0c0180c8603e4a6585140310b103000590365400d000880d15180b481c203010f02010b1200b1036495031142ca640c041074000d0401441c0b45440741c40c00070b070768510210075240585039032806481849030601d11300014204500c03180350302c0c05540c8602049641d40824003801054582c0141550741896840d103420f001c00c541006001d42e00b850305001d4920041c00841d0105e806a00507071713001c0400300c001201c90b6840e650001e9406155035040c4000c0c904940e0000017818494541001591420030700042d05d4001124020703404001030043d00564200821008454081034080ea45810300000000d5038206561400f903591651356444a80940404d1103540d41101c04d8109080720006101002040c8903c055042d40e8200c0341103290f00344250821400c821a01e50000043c841480c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 622201052 1250 622199802 622199819
    0x4051f060e1008160302060a050d0e010f140a0603030c02060d180302010f0b0108010311040b0a0b0315100503092a150306010e0d081206011101021603140c03030a0f060807 75
    0x8607000f03004142c010034490148908658901e90110fa074040c20003801c051200a0545054200b1482081c20343e40310103098400c41000c1c4102482c8465480300002c40c41c010002640040c10020011080249000000e0011035000766a400c4103d50444a00e56921034805a480240c0010800446c0725404070b054681099010b4000c8000440750301d0040041000003001101d01c00020310015003060100d0780c241d000f9080513080790005030006800b0780d207410340d140d0740380e4280c0d03104840940344600901c0000205250080c220110125145821801c0d07081c080b00a0340c43e00e85524401d0f500024a41040b0420820451030340d100c508000d00f0280c01d2015005010341940c011a816030004066a20409a5190010b000d080350f5401440e22418008811882c45003a0f0014002c07030b0600c009000c0455944a09000904116036516002d607160702031450060840d902c000821000120140642241c0d0b80002090326031015121001248030740e0201e201c44010004e03604442c00d02c0c000e1761808180200c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 622202302 1250 622201052 622201081
    0x6060f2205100806090939060715050a0506060a111903030f050a0507020a0803040c03021f0210021c0b0d0804080f0606030114150415060207050f040504051f060e 71
    0x10015680404c10b0b40d110300446440d20103d11440c054482c108031418150100740100c2c1f41c2d03040c88500b80d8000b2822500016045822071101203a0b0003156004c0300941d40d500d0b0158542100c0300c01c1060020303081010001c0c14901824214000300a50384001c0c201020003045010b003507030030780001c035035203d45a03003401006041400c0740e603000e40341050040381c4028203a10642d4440d040c036034090031422426a5400f070072540003501c02d980245d903044000c40903a44411b44405241056200210740e0011309d003000c1e090007082c001d81d01c0b019205002490110746e242209901070841d05c0070000380300d02c0d440002416454402401b0300340d070002086c0442c140400140e1080c1c0c2d141c12004507246544d6460406007691492400d12000341d44a1700861450f0310902030944e0108001000491941400c1100c4900700060350310040c0107900202c0c08102c14100070358030340d0240700140c170180494074064440680e211051007240701c098840302c41c0000b03070220580c4404042c2a5040c180982800c05480740c4a064 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 622203552 1250 622202302 622202311
    0x1170405010b30070506030705070c05060406201605120708011107140c0d03050d020c01090804060906090e070804031106010f050a1e1406070c0306090b06060f22051008 74
    0x684400c03900403c010300290140071200e0003003855140da5518402290301d5001040c00316007116101c180800c0300c0d0f5034074000c5c1006c0c000304d0b03176813640c0c509010140110004110080c1e14040d0008440361000940c0000050180c81083e12901d400c09021b1b40c40381d01e4041e855000c0038082d440c100f0130a007a2041c3c00000d0211030b002e0085075180101c615003040d105e50302940c01551000451801e600000d00400241c03071500400900141004c1010001c2400c0d100c903d0801c480181e800101031205680000e1194094481807a001c079200d130428802c0c5d81030940103030041d800e2180c2d4a00081c10984590500e0044007902e20a0300e5195030f6503a8805003c4129001d01407140e103035403a011600c225062a4141482c084104503521180f030305141c1802140d102c44801e420003404c0202401055805001c58015440703100002080155800c00b1140418050700c081d216010030041d19107032045810603904c40580034650007110810981000586000941c8400d4000c43d911880e100c0298102c104240709 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 622204802 1250 622203552 622203619
    0xf07090603140d0c020d0f02030f01090c0f050d060b150414030138030f0f0318010c050319170f0403021c0215131a01090c03090201170405010b 63
    0x611095009180c0310140341c80c1d0f40b000640d0010304a0003502c2d100c3c04000c141c0c1d024a503500c0001e500b580100b03080406200114070319030344070018841080340150081c002080c1000038500c035507003040006110741e0452000036010580f205c40320842c50b51b0340180b0b001080a0356002c00c0d952542e660311080501480e0400c1d074840d520b031040810300c0a0f04400c1455501484004804a010154614181d505007034010703690148152800c1d4040424200044a584803902c001991200d41544810140c42081c2101c903041040d2105864001134001040d00c148251100c0901018446400700311444102d8011b0074442c41d405200780684540d030080180e018a00917800d662004030030103604482208080e03500340040e0700409450700000c41c4078403d590405100c100b000111401034403036000da0203085103400c1c021169540100203282c41442180200c954600b804d100c3c0c0001e940003e4480c40c80c0f10444044031005c1c50000301088001c0d4032007501800001c21880e24900f000441103c80044000031044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 622206052 1250 622204802 622204823
    0x415060306080d050405130e011505091005010903030f030e0d080f0a0921020f0d02010b210309040203040f0605010801050a0e01090803060f0a0e010b03102310020f07090603 76
    0x4401c07202095032070000c0c2c10b84e01c581d0314040c42c0c04c090103110004441341c001e805035a440e0748941440280610901c4031541006d0003c00c504007810890040e202402c0501d143c90f500c0810030490742c0200e801800c032501410111800d151080c025400341c503003130310b0011881c0038980ca04030b40305421800d11406540341c1542003103540d4880410104a0f056a04060701c0704e8074542401c03500c4c246160f0380c40c1c1540c80b1441a01c3c04a4402c1c0103181c501000d0400700b00140c0d441d071510b80328505054040c0b0315010202c8481d540360f8001d100d00551684544148240206d030000300040a0180041d11517400b00e0384070400b00050b41e581d04016000700781c182c0d1118407a0781861070742c81707003104140900803526030814541071442d01c81b41308000c0241d60f00c0300d40e44c0c0c1100030f116001603080d0340b00324158020303e0340255080d03903440d11044240d59500c079034126013511038107142c1144146010340140f0700c6501041d035040c8215445040140d28286403104100c005100b01c800200b84500a504003602b00c0b4400c024000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 622207302 1250 622206052 622206059
    0xf03031008030c120a020c060f031b12070c1415070f0201060b042c0a05010305010b01091419270b09060607031407320105070c021e0415060306 63
    0x1c1c1c980c820b008284075036901850f0f00c0d000007254003004010702d118031b0040355451074009002c10321603041b142128126820100401100621856800f050700c4507582110340b42c02c0541c24000488000980180e0411a04280c208204a45840380081e61020881101e01000c07002001b2480444d0031140d82e13000401507804c10060360b00500803031060361452404141882c0c18101c018004e08a84501940c04040f0030f10074884510b00701e000c20307010320000480401c596040d42091070030749440180d19410400c12050402a4404e210b551201c003150803510701406806041907040c200c919900320303041c5000c540c4140402d841d44036040310002d81c11600c00303002c08503108082100d400381c02c95501d50462410454200028030468041030681c3c4200d041381e04040198840062030b00c03024440d0601c859039101050141500758241d207580303501320b40003880340345000080106003480c0b50100038042c0e03100c82c1d0004181c0d268150303601048000540104a1403c54488200401240c2e00c80c03100428a02070011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 622208552 1250 622207302 622207319
    0xb0f070f17070302010e0715080c0d090302060108280b090c03060a06031e080f0c030c060106050a0305090601050f0607021c230309030c0609010309020406032117071107080f030310 79
    0x80c03048440c0b003032341820142d00c0301e04140c40b4840c00500310200d01404000310b01e0549114401c001510340a80d00901c107130341c180700c1054640150241000401c0b0240c800400400036030100510300700390311444444003038a4a00440d4908402d403c2039681c940110020800c0c0009103038070500c203c80c0100785a4414040e8501410308280708103002500d0031004000c2e01010084400040918044140440e86400e034500d40360707400d0810a03001000007e0001482c40800c96050081d03e4000030200080c10283d4905000107407405105e0501d14020f10700440c032a400c0d9039644110030301c003c6603400501da0040c6903103442d0000000c82e20750050140c40359508807086a07000030580b02d14501c003900400d1178804800411485070019202c0300c1c1095200c01c03222005859070b024246c01140300f801020381d1b14952840004103484034104400400600d0818078940120301d015003174106803c1c0c00c01d550400301e00c02240d8102103060f08600d50074841c41c8102658488004025485000141140d0203919280c8090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 622209802 1250 622208552 622208563
    0x12041101140918100b0301060915051306081513090308090f06153f0d05071e0f030503040c09050915180118020f01090b0f070f17070302010e 62
    0x1a8116004042202d100003400d003407a50044e0024001c00d11aa030f40f50010a041e40c0242c11040002d0882d1104010321610300c510031104140300c1c104a400d0032000204c00c28508a5445443d0401018030003042202c10101090103d8071f80203080d107070580214015100151400c40012800215440000b0383c4c80003000c58260244480740c405000c503034a030208512040d000824855901c06003030010b03401c400b0400038620545500a250340d00c041c0c46503074078007020700d110181c9541c1642c00c03451526200c5036001707045910781580641c802d48081614800390852044105000340400754807202c0109264200001d14443e500c90354010481a44909500040e40c4098584000540c001d14241004004508041b80c1c0729920307200c020018000c035035500e400c1d02c0e4091540c03441c0030880c040c0c1c9015804c04610900d0700b42020700386032640a10b4180c484480f8410f40d98540340541000c2500c50401400c00005500590403400c01c000c3d4100d6074000c458580c1c0200c004401543c6403000300d50814001290 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 622211052 1250 622209802 622209817
    0x2011a04051603110d0e150a0218060c01090b0405100b030a02060f18150c06100f030f08040803030f0105031504051e070810060609060302190e04021204110114 70
    0x5085510b41e884071400e5001d0040d034108024203400034030004040f000359208a025010509000303084011040c4c84213642c102000c1c000040c0c0310b00402c9642049500c0d41e91440c261b03601559245e5031a015202103a0040580d0791004028600c0740c1c0512081c450002840480280400000c201c4081c17541c080564594010000035080601403040025007014071016003600c0082c6651100c1d118050030000704070014405060f1140040441d078403400d20301c1000301e20740c407a150850305460282012510101240e41c1d12009102c4800d40005004100040041e50b00809651044948038101403004207280e40d800d01900e03001c1e118500b00d540240042302d540c4e900658124018250100150810b11980d11a201c2030881ea8441c034400005c55500c104040c081030116603800007446814450002c0103240a079208004050040c009041c40c0080040c41e100095124189189217840c100c020802a005a0201844c00300b01c0d45c00304800e00c480c0b102d010400c1e4000360b96600d048040c0c0c0c089119180500722 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 622212302 1250 622211052 622211071
    0x100212010902031e42150d050f04120305190506030c060403060b030705010c03020601051306240f2604030e0607030210110a02060a0b060d060602011a0405 68
    0x400401201c05203900964110206221016000d1126100c001c22101c007907801541e0301a400311030801c40e40c003902ca421202c42100340051101d0904554004412289000ca07512540414000e4800d03103040d881100c2090346040001c0c001ca1030302041040103902c003100e0940e44000907844a00000b48a441007030700c20141641a1041200c483c90070000401008144940610034000b41004aa8805003d0720003148154800b043d001011003d00d420400305500c05070600c60454210000030350089451410b40c0c005641d084400d0a00600079009440e460303000e409a4190009a0142003c41ea880b0171010502522908409000e9400442d191001180304128181032103441c1049001c2c42c03849076810900914040214035a000005680c950000130210007503408800940016209406014200b003084210f607418031a9003440651035013401002400d10030f50314459840740d955a801507680311100702d0020018a5210384010b4024064032001c1781c845a12442c85240303901e014020716100d9074114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 622213552 1250 622212302 622212337
    0x606031502032401030b06120133050304050a12230408031602120105190c0c02010e060c120a09060201051b1b01020d02120114030604210504031b05031002 68
    0x240c107882100c03012011507042580750159840c2582d81c5101800c5150744c234001407085e9514265041d1888614000c144407039004080a03480c2035100c52890810350001400c050f41d0742d030344918010f41880100003009003407043c03031803040701d5655018144185da003144c42d03e04a0504112035154000d8002c91042d9103e0385e1003080a8081c402d86103203a00700305480500490384250540c01030720300b9103400321034940e0160300780e002d140c0c0d49018500070001c2c0074003e82084402c402c1d6a4000900170206459554051080082c864009032010003c1106e80c1e114144941c0d2200e0344900024640d01441c0f040303200541c20000030460400204102d00b0342085140410741c03400c002c1c03a40009030203030707030050000d0b0359503081c008510215001c0c0010110703002d0645c0d51089030b40c1003401100301440910b407182c0c000e40c4600304220010325248001c0260203002a8400010305014104a40038402c81e080100442d030010f506d48034000c041503d0b01c0c01d40b101141510341c00c03901403015004a0042511111240190 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 622214802 1250 622213552 622213591
    0x907030608060610090e090c1e0f0103111303080a02010b041a010311040b07050102091e012307140109030f140301030b220b040c06030e07150e0d060603150203 70
    0xb0750580313080c10101c0d0038644900e03903581202e03102d0300c034040315000300c2508555140c15040c90201e180e0304015140c19030314030307442107004042075055105441c524141540c0d5082c0000a0a1138826240740e030b407145108148060702c928060540d0703001290094059802c2903815400340c9028001d81c407030313040b540b0301304115980000011805011400c060080602c4204004260f02c0c2c10303032005004150150001699400403c0c0c1808a450000220746400d01c0c00000d00d01081e070b0340194020802032000300c504403c0d408001654446102d00311005203120102000300310f0032030064002503011400703074a400c2030810140c2c4007901c90030306c2c6400040c01500c0400c010700005440c1940d403a0402034080750081a1150811040d284600303286055076642d01040800040220001090002d4580c5140c00e004484c02e14a10301d540b2900c2c2d000303402d405c1c1c1046040e03d920f01c0c4140340398034200400034081c14204000e4209040102064002a079228080310200c0d00301400b14001c5a0040808001c0c11700403400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 622216052 1250 622214802 622214809
    0x16090803071b0906121b0e040f0b0c04050d0f052a090a1e0c0311030a1d0f030a140f03010b070b01122a080706050a09120c0b03040f0503030a0b09070306080606 70
    0x700458103180035164440c0c0407ca02d084494060300c1140b10f003540c0d1840e0031950800c4804044001c040500d9500200400d010940f15001150500d44d0b01c241011004205403502906280c0d44000e0410f0307480b0103002c1c2402e0341c100441c42c00300e41c1c94150303034580c101d031a0242c0d8202501e003140c4115002140c40e40d0a03d02d228042d40c001604280185070002d801d07814022090f5142c0d005a451a44103034a50f9184030703800750074032003108001c500740f4020182040861015030322806840306100c2808250000688004000821030f208407800456030340e541d41e120035442150b46c00040b000e441c40b007456400803418501c01041c44c000c01390005061400d00c0d1000307860114280c0c1c40c00c100904e950700350b240021001c800700711880103050b0989909849029002006010003416800034919181180003840414400413864003560a02d01160341c0d00d50752801c14103079030311454400030a41c1c8030002c10800101115402922000c404480304813054440301c5081702510818000d40a10717070480340104d0074515 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 622217302 1250 622216052 622216073
    0x60a26030a121514010809010b040501090c030e010e1c050f0301080f06070f0c150b03060a05160516081e04030501060311300c04020c160506040e16090803071b090612 73
    0x203100d40c008190443c514010405a610370b92041d240c031502c1e42200300801d9014014900003c40c482d000700010700061030b01d42c1d80d42c03040c151040c2178030000c84850748000c0d2081080369584c40d40e580b1450b0b62542d445041541c0c3d250b54079083c40f01070003281c0200f44000c4c0b0070400001096a20b035501d00205501c0d07115000f4244900200c2c4c0c80341507581410351116141030100031702c102241c2d50005620f15118800341400c0400d0303e10201003000821558548d01c1c110306007100781c15002018a0349819181d80391202d11103205c0301d47c4d03440c55400326000040010541201c0d068074407644120700e017120007006200c1051a181c4250312810800075800f82c9240010f8940c141152490382210340c64183e2074085030490f804443c0060040e04400c84a03480c1c0c0d54103440c0203008007400e44505140500c3e01215140c0ca10014161a42a000560f0a06196403203408840b000d401e40300c0c1925503810852400c011075008080304001004c0e085040000e200c1640c0c81400202c0700d981d49520030a050690703aa803a04d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 622218552 1250 622217302 622217311
    0x1080709110f03070e120a0f12050915180d05010606180303020c09090c120312070c02010503040b0c070206120f090d020307021306150207031a060a26030a1215140108 73
    0x40c0702281d2501b84104100840c4000f140604e007440300900381070401c00d4449010200c05014004100070704003003500c030052090807400b980344200c0d450741031580d50a8103489444130300b65840081c1880e03100c1409410b50100040f5251620794048804004c25100800040c611002e005608545c480141a080800d201360f032120485044c1c880818600000607030100790ba0304240b40a81c0003207000001101c00701c042079000000c0c0c0c02c020180c2d0f011540024568440184010001c240751404940002c0d0024141c071035039680108038a8907080d00051000714101e0490300e404200c02004007043d520100403030325804411071a40510f2900b41c15030248145900c49011712602d907035480301d0000d1240b40800740300c8100709440d4040d2040500d10b05210301030401c02c50810301015194000d00ca1247d17a16100842214043c2c0182c200c1c0b00303045590050941d410400611160000080c1030000039408840000d040981304010440c00c0320007046d02401c82a0340c00350700280794440340c00c4130040d8014002d10360710 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 622219802 1250 622218552 622218559
    0x40c0509180d03020a081e0c0c0a02040f0b031c080a1107081305010207140303091512070f1101090503090103050c0c07180513030f0e0d02040501080709110f03070e 72
    0x62071194100a00d03103141c1000c41d40c0040d40c0800d40c0c2c61541e03445454180c01c0141002041710b280c070013002e07200d4000c00103008651461800515844489010300035880c0a9030018810040070038041118409090441141442400380704010403900c02103285404040c81b0702c0d5100e440b07980e05d00c01d22a00030300040c402d010642400780320f0000051500b034000c1c440c1481518040860500d860006071074070301c4580004412281541c030000040d140002078803100134080703e81d002580c200d4501e0403542d01c5080840c40c0b00100303090400401c2078102609515070301c07080c0c0d9110310680d503110740301c9d0032038861440080040e0004c010043d2103601c6038000c81d401c9007005101c0d80c03521242410340f52816003158800c3c480302d59104400354840544d8414282d00084500c81c0084409255400034500b08840fa900c0c0300348516120410f000d03071150001c4c1c1402c650b020300104800e51f100c1e07a550f80c0c0c5411602c9500307102800e00300440d05807400c210a0312450f00d03105075004e06503150101c05407034500128894940 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 622221052 1250 622219802 622219831
    0x2a0102070e04150b0618060901030906051515090a03140c090108012c10051005060d0614010e030703080703022b14031909050f070605030708010806040c0509 69
    0x108a890500e060b40228890422070320b8110403034441c4400d44542d0b181440c403a001c248040f90710648241141c400c01842107640d155901d201c540141c00902c01940007504c0c00789030104100d1405924107a080640d001120710203a0755111100d02c507128130071200110381241d110441000000c00d0b02e9400800a10000141c40c421540c80011400b06d0382c09900c200c8160707440303640e52288240f44410680d8111424600d0585c840214040d103503583c011400f0740c01c045961040013454140078003108602400c1c006084a6403581070700e5400c006001d8500840012404110344400c5943c001c403860384910360041c0c041c0c50304034510344503a0354a030403180e410380541c05240000b61a0650101020300b09200f000b0062021180281000304030844950000398008420010f00c5a00d041e960302e90f150781c02c12601c011414051901d010303401c010600701c0c121290b01c58010b01203800d0390410040c0d1310504041c2d13038404403a80d845003134545e18003054030090520941c0640038081e9060480d1034542c081004155401c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 622222302 1250 622221052 622221059
    0x60a0903020d260406140a0c080306040905190213091a0c07080313030f09030506130c0302060a0e12030f0306010c0f05150a23070c0302100203010e0a06082a010207 72
    0x52099050206003120220f00050038003000c2e41000c1e10000e010101107400d82400881c0d60060245502c0300d102405100000c000500784d80d40d56040f08803030ba540308050781c1c0e10341f908404030768404c0441c190803846454181e00341a100340003449400030300d6030080c0307542c4004d0b07100c0f120300e030004140074007456124402040b00c0000304060800540c041c0110001e14009605c4500340105140700b0340e0744042c00c20042507000c0000c40c4000aa10350461881c1c8241c98400070300381340c00140c400140d03000a40042002c100d160000d0740006260400100607145641c031060080302e40c944074410f61140d25440f810a0002c50740340d500c140102c100061080c01170b0100b02200d81c450624007465140d14043c2d01030000204400c158890051020490074100d4803454801c80f00040030b0703044002040c400402120340354000602d4030820407902d1ba130b0f01c550000c641d01d5842c0c000c00d07080d014048459085040c1094000a18000c00113401d50000c21900c4190140b0a0380c101c41c40100300f003403010306045104031000071 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 622223552 1250 622222302 622222343
    0x51f030e03161505090604030c0605072c03010b0a03120e0612040c1703130e1e0f010f0f0501050d0f061d0f0105030705030715050d091b05060a0903020d 67
    0x304215409001c0d800c0c002c000400520f415698000d103010186e401c040103010000e500304982141e00ca0b1300c580049000d90b242e0a040320030300005001d852500c4003911b00d5038a490000511074601410513070080c810014100140403503c056480014a010f190078050f07020340380b0400104090080050030180307130074030713003100c007400304078140c070182c4000012440c2002003d109079500c450b0300c1c0001c03003d141400e10000720504148107900c20010540d0131400000c50f4003890802e00a4640c0c0b1001c890007031420308040d141008a024007489000c00700c0b220f03000c25104601380070101100d505030344a9103085002000ca4020b07110014855080a440b44800b1074079104507000000b10f80d41204440c0449d150201d1100420603040e80b0490080d04161410305c05034902280b200c041d038800a55032180c003407038948100e419120b05818480c403a03103000000c80c00c1196605000310050b0b6425032102d000b030384030010031100c3d1189211810102e004850100010305004194004850050049030145801c0c0e4280 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 622224802 1250 622223552 622223587
    0x120f03020d0e0d0e040e0d08130b040b04050d05270102070302062d040602030a0530072d11010e0109030819021e03060f031e07051f030e03 61
    0x340398040d00050395841945500c80758070060349401720340900c07441c2403c110498403070300030320a0b420800c10702600080c500740c5403d02040c0c00d258400303800300c800d14060421b22805c400c00ea40441c0c0300c0c000c03034151100c02489041030341c0100003d100201c151030a0000f10801d001021001c007070560140c0c18002000d6034030341c009412035a83c03000c5180d441010241c0d03003025142c1084542020130205020070301000c0d034000305581445403181070a80d0341c0c2002c07445045a96044130310403944103107030740300f008880f4004c0c0c2c1203c1d008081c191a04001c00c00118064045c60321030495038801802c0d40c0b07000c0311101d0300c40c4040403048015031000240e5881c440b40301e5420b41d0104e060640102e481042031214501548c04000340d11801500210304201240003e850035118134640d103039000d030020020800903903900c86400c12030b000040c2103c640c05080000041000c0322191100803501500c1c40000d49810320b054100001075803540c542e041404403d0043e0014031003804044520700c024080115400b100006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 622226052 1250 622224802 622224821
    0x30f3f0f0b03010b0a0e010e07170405101a0d031b17070524010b0702150c0c0301150305120a03061a130506040b030402220f0603060606050304120f03020d 68
    0x140407420080c0390090500f902c07440c804030750280710107000801c03071148000c0c101030640d2510404007605484591048802e0340c50075805030250140d40043c00200000095074600b41400c907541480910414610359a82e11120a503194004880513031040c0001e206031403c01c4480e000c030705005103808007615441c610700507415481202c56400034480707040c0039040040c405990030360122100580c51001e0704204a040604c1003113112040032039848219990b0100c884a000070601e0295101d10119001c15a500a020b6072180213500c0c000c0c4e4401e090151b8072001c825690810000c142e16250040f10700d030140c7c0200106000c0641c0c40201181c00c8440180103407031641c1e50100240c60f6920022500811003041d0b00c036a1241004100400443c10700d0000c2e240e016804940e02d41400d44642200da004400d0744501580403460941d4121101c00140c2c0310900f40d9025500c00c0043d991a0031081e101e62005031400380c1b500d10101400c0f0b041c907101c0c400c804600089032401609250259680300300380c2d55080b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 622227302 1250 622226052 622226081
    0x61b060b1c03080f10030c140102100f090201110111040308031012030203040305070f06080c070c0801110d0e0307170d0b090a0504050124050f060f0d09030f3f 70
    0x10500030804c2030a03440c40c0d0481d64400f41c0c2012030b407443d9503002d08101144901e0900c2e100c07404121034107a009103d03840c1502a102c40600101d035844030000000e000d80c41d422070204000042c881c4442105104191341c20755800c4807680343c207003544c5070001c55400042c48055849443c50010a082215400070825035106e0b400a684547c19480c01c90f040c0016500501d140005549080080542c0810301d81e0300001158071041d9101d12a04051682e42180c2c0c001c018151709103181c1503c03401c014030040a14101d802c4041040610160b880e43e2030780b00304032028002b100340900c0c5000d482c031110700400248103d000001149035060300400d209200072249030740013550790010081803120038019070402028008008121005600c1001c1d0362409501510380074103a02e865022017070701c0301d40c1118902400500003a445000c25401e100142440d032f0004c40c00104941400188103001d42100d4180c0255a6094000303840c07443c90212180c000d02540300d200c80c1031032007600300c1c1910603c0340941003e41207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 622228552 1250 622227302 622227317
    0xd0e0106150f0e030d0e0d1a01182313060c030c17040c1a0f0301030f06140c12040f140601140609010c11150f09010306061b060b1c03 59
    0x4030700107403201080c029030030300f44010480402c9140c2c0d07020030074134020f00315070401b412001084004110300c1224250000c000d071002241d0182c80d05140c580850488803d0580c41541000c0d040c03070881942c06c0100b141e44080c14500c079401c1210380003423407103600c43c003080c0c4400442442a200c010507905080c0c00703e0040303030b40c40038802c45071a8021004e02080030101402e07019070505607a8280e03545101d2141d540d860b0200307800c0700c081040e4102111424151104422386a58481c1044c1c0000c41c6002c03000c81e2194a401000050300c42c042c80c140e03100c2e200602049007440451410711040400050003120385a040caa801c0000a02080e00b014489250000800981d810710225044500e040d0510034459072080c0402d68840e030f0320200c094403e590000403040f10399640d01c00701d840072080c03084120403102c0100e0306002c0030440303a02038811b08109980500907140d0b1003a094400340840c040710200b0b8407400449101040c000d40000400403c007810300070340708032002610900c4240001080b000151781 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 622229802 1250 622228552 622228589
    0x4270905030f130e011404050a1b12061707060302070602040b0a0806090108070506181c081801080c070219051e21030910170f010521120d0e0106 64
    0x451000f0040c0101075076140d038550500c4a2103400b2555005030500c15901c81001071160520303904001825483d203003005003d800003a134040c1121031b0081e0140030040c9000c8001070b80f001c900c80220103031076002c3d0123404c250b810003a00310041d6110b0345080d03032030320703020000043d103100ae000080000c1c4074075550f034401504200d81000203100040c3d10104d542da111070340911080d03842000310303000200155070241020003580c01043c5881008600f054000c103606c200041441192070081403618a800140111540f510f001034601402c00e45007141c141030140721500060500202d110206000d090304c07007010550b99000180d100d008231800520500c1c40d03940140c0f09060845002034800d44451081140d105440c003110b54034050440340e28440e114094403401c859004880314050140c07115a1b003040e07880c100150b82d601120a206030b03030140090200c00d2803414212001c54403c036a001000d403030201c85144251041e60005621042019030302c008800c941002449948010018000e12190201e030703 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 622231052 1250 622229802 622229827
    0xa02030105030f06062d0303030406090b0115120f1d07080c0d02060910120e151608040b18011d06060105030108030a030504170706061a04270905030f 66
    0x1000b072450110f0350b100c0d8041c4625980c0d6451038421030b881012080c001c03244251000c1d018840340302c0b079440e05030100005110900000c5e0f042101c141e0b026003214001640c0c0e074075051402c1d031102e81c80080002c12030141c3d0349104016811070b0064103ea5400821628500143d04600c180c144c00035610951045900700011031050103250710748403046441303003c0503075a40c0100e090b5100e0003a00340d10401d04031030b01c111001c0c050b1805102981004004100700700f21a03c0c4180d0380c0c2c20f601d190b8065042d030140003512060b80728030402c051803032641c0c6803056500c6a41c0d4103409104041c040071128580d00d4680c010002c001d110741004000805648001440300009940c24003201074551f80c1003100c1040107002c4480700204881d02007109103400500e41d503450425140361421800a522240c00010300001030100c640c0040d001d44040752070304603228500055880c094401c620922000e00110244a1180d078140032106101080e590b00210b00c00d030320303031b030300c01d4110741c0f18245c00c20b162400032a09650606 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 622232302 1250 622231052 622231063
    0x424020d0c2f04110f031f081f0605060a120b041b020303180a0503071704030f0b0609010608220206220f0510050706050402010e0913050c091506130e0a0203010503 72
    0x1030926044c94030300300c1401e20307500ca90303c0020b000d183c10103c003c0e001181110b42c14183c4005040742c030140c0f503a02030042c4c801d000f085100c20f80c6050f1103051000110b150724040c02200d0103440581c503194041948080032502521a01c48403075401580c2c0c6e101101130503194140d00343d82c00c1c11540030395034a141841d6800003140ca090039400c01548840303500c0d8002100002220402c81d0000045100540c0d54000f640062003103402c000e14101090340c2801c10400341c7c1c021980905012520002d041e80c840200702c82c1507108a03211240101c041c0c4400c02e960784034696030040e09001401491601070310718148801c00101042005a28050078001c112100c11081001d000e030208603140e01680785c000c0c4008000d0f0080440280c17820b07035200c002c101168010f59032140200b0b40a00756121034a814201c1c09a0028001416202c6006900003003082d817a10481c0180b0900c0585240f01d10a030490040c00b40a4010f81e0302c999500862140c04115201141d030803030301c40d110307010003d0790b40c0d81402c1c04e15044c40c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 622233552 1250 622232302 622232321
    0xb090703090c05103501030209090709110702030d0e130e030906030c1e27040e0d020718020f0a1b0f0609170309120a030f0504080424020d0c2f04 64
    0x880c0021031700d050800c00c0c481581140c1d011658450603031620115181444040d40c4801001480d0041148041200801802c03556000b141a1703582c04140744000d40e41e80c00c6140d0f85950000d42105208007140a41c0d00041020342ca2600301c03401e0120000105000ba4810303514094105000310304a804000c0031615005030400780b841040c140030003030780f400c1046a11030301c0a1300080b40740c541441c81521998803100007603849030200c0e00880c08000f006900c1d40c1c0b03540102e01d200040020038000c01c81084c000c80d07550708845207002d0310300040c0781c000300c500a200c2c0c0041d1001c003600b0811381020800c10580c0790b010741d001e1840020000010711b054203c52004120192031900280104055004007003079040010146d56003a50383e07081c0440048008040642280b070740c040c942010308c41444040c002800c152401d011400c29601e555040180b480c0060384c1e03860b4010307801160014081840741c0210840144111081c2156a10103040850144d4165400382c8003000500c1e42d0214900d42406515403c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 622234802 1250 622233552 622233617
    0x2130e19080304110409081c05010605040303050904050709230f010c02010f030506030c0a06020f070b160f060609020f09010e06040f0302090c070606060801090f0b090703090c0510 79
    0x40c4440e40e0345407101e0000510140079040c0442002040d070715540c03c145d01c0c2c0b0754017100d05a95070718004996082c1e038810081d0320340c0203407a20002013941d80c026000c65041e2a015218241041c030030404010162000400050030002d04000020300c09031404100040714141b4031400e14440c1500b02072204800d00c0d0107400d410020552620030141c1d802c1680d843c013040c0d4078a0301084030f643c0e004c0070a140640003d581e54005403110400100f26501003401180c01135000250703038180c4d5945404800c00e002e0019a14401c252000103000000c02c45131000c2c410510528003c9101c5654440017022030b001a0682100301c1d000164041d40b540e8842a6595a400205c0e055810142480d074191202142800003d029002da00b02040c10310189900b999181680080c0501c400341d00c85d4001000401e007032080828482c100842d200703a0302418000d18051200142202d40303659a00304040300609074800043d5810b0211420100301505c410700650034038003090312101508422070809150115144c80f54412 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 622236052 1250 622234802 622234843
    0x4062c0c010f1e03090803100501020705061e1303020d0804090b041a01030902042a08091f050c0d0c05180307081b0a0f06020d110d0903060f0902130e 66
    0x80ca03a0051420a8090f405411440d07070012480b5094008100e00303140034000513404800c0118091f0019a0001642c00a03801d442081b81d41d00c0600150740154203401e40780c1d850845800f05100a1140a40120041c2d290314a29150f03403500414050400700105540c81100010300784030703521a50040c0f05c03101c01c0a0f20104600d6161040d802410700680c054a4109500c44d21294255543d64008a10074464680d5240c85102c86248404021100c0c91040c004a01c0800004107100b030040ba410703c03840c407540c01d04500000e030b00340360000602c0001c2005c42010403e01089031a054540b250381c13020703285925002d80e54000b200a07040100142400d00b4402d40c17020400b444018800704803180d291919007480800804921f0001d0107020258009100450a0301e40c0056a039600203099071801e201611501e280003404101b06465811a1025002041194404000040455000e4220000c034880001a4802190f000170300010441c2d560f164001e4807410200762000c000d01c484691400c61110188 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 622237302 1250 622236052 622236077
    0x150b03060d02360930041e030b1b0a0e011413050f0d0f0605131b15081e0c0f040b0d06060807090b07021c0b0702070f080a02060304062c0c01 62
    0x1e100704802c1c0812070070001d00c1c00c041c40c0703448104c411b442c0a0b2641c0da05944210b00c5903142d50f060840c0030b200c1992001c1854020a000e4030f000715028100c0c20240400901c0d11058450a540003003461500364100305100000742c92140c000c10213801d402007030a402002c07192a040400481c8170014500900c640c40d01034190001031404107a05807001d80c01400030403940c0d0780d10500c42c0b500103801c0000e007180004440124200348800800d02c20b90304450080b503452030164000301c51080045640400b00b01451070000204600e05c0a501c1d40110307004485840c10403072243c0140250400c1e8000000079801080390001300704140901c10250541d40b0700b0140c01c0c0703001d07000185030060394405e005040340005015025915217111054404040305640c003043c031000e00d40841e40030811250000140200b8902240034500002c2c2c880464004000a0203440225002c010007a0700142c81110031507580e003505010344003259142c81c0841103400802035000340500815003808882d40603141000246e05944 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 622238552 1250 622237302 622237333
    0x90312070f05040e2710050f060a120f062f1908090309040204330207140316080307290103060e010e0a0c0801150b03060d023609 57
    0xa0f012200c03c1184504035854502d020144502c00000841c14198203459040200800144038958410800c17003c100945d070300b85000c0001082910071a5119803500000c000761400b401d40c0030145405881808a4164183c0d03a49040b6000c90740a01100040da503410f624007681c210010003203907540e61180d03143c5001c0c200e0384a803821600010740305003c206000704001c500100b0585440c141d020b04110343ea20340b61002e0700800c403a180001c031110300c4c5412080c54503480303103011200c4446554004110160901c60701002090704003c4541d0144111407803080c0c809170042880e4011720f0514041c1d80c1d5016181070a00580c0e161f8040c2c262200340e407003500500d144807440c800c4d04580e08000000340c03200c2c5075900c440c05800d403022070700e403580b0881e15044140180c94003d9011900c03408020440810302505c00042d4400320b101e8840310400c14000640749040650b20124140c1c401841b040c0c3e520704003001d4000f04c100c4010381100d46500390044605e4001490740803034101510000a0074200d400f551403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 622239802 1250 622238552 622238557
    0x112d070512030706110c030a02061815010e0a0b0307031112030a080c301504060e0103020d1703010603090302100b060d11041203020a1a06150901050909090312070f05 73
    0x24a690303640c0b1000c14030b034131004042e140c5012080d0242c980d40c0b408140001d59403201a01c10160707030b003001c030b10bc4190600300140c1c200038a10b8284d800d2a444e880d01600400c0043c000300042d0b20103854418680640e50305010040180d40700c0c0381056141c0a184042c404528849403407001c15078000c11041c10960341205e5001d921200748003000c0c1e51600070034242c0c011414400840c042510458881041801c1440100c80c881e204081c52010329140300d00c1004241d40044c0300e250750840c6030100500150501628803000355028a40d0000d003c580002000000d510907400a40083e83d2880c002d001c01d5410b00c405581080131140c00d11505450300c00052440c49034400c20a45a9541e1401c1800b4034a081d007501d0081c400c0070040c509010440c10042d40b00c6181010440b03180c440510b5048400040800c4c960088002401b4540d0520030004c6205443e4840200b139810b00c0424803881015a484801c190b200700d0701c00000e56103c1c01c1100c091400201302601000178444440c810080095100c0305 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 622241052 1250 622239802 622239817
    0x302070c1401120c0e030f2e020405121e0a03080c0313061506110f06010501120e03040f090b040b030c190b0705031213020d03112d07051203 62
    0x4014410348900740060343c410a81c40341100302941000c8026901a0b00b0013545060154140c041d68070044001101d141c4480030811031804919183c0c0085090118101c0329403401c0000e2600145410f07214400600c81c41d4030f60320b200000c1c1c0d01c03a0f00e0b10001c01260860407100b0000643c020000030820b0707070f00604801c500510740300d43d9440110001b07101594010803030840c240c02c90010440d40c81c0326601070403004d040d8007400001c43d8018040d21210280041d80715182180d10029100f01d9007004011200d0b04040d40d1811680c03600c40004502500c8148010001000c0d880801c0340c0040c54031550313400361070681d40d40a00c030f5841c1000195580d1004142010b111100b01c50803800c0c41407000c07a0480c0c209040e00105e020b44804150301c410000000002c0178201078960110b600e43c1c1c6d43c142c500300d80c4640040020340062241310302400103070103000a0070650f01001c05407031510410700701181d00c800444609612018601849041d401c07420310489001d030070141c035080c01e00301c220b070101e40e541d1143c0700e03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 622242302 1250 622241052 622241069
    0x140a05040b060d0603142b0503060a0305030d15050f01090608330406050d050a02041a130902010f0c020a0302060a170c07030206010f0e150102030d060608010311010302070c 76
    0x1021201d03a03644000803500c00341c109840400c4599100e003404107468018051400844c0b007a070281005416401c42c1e40000d010707480300d185541c2142c0003011180c82c1c0028282d00d806c5208403002100081d010710113044200d40c82d200001c2d5019640c494994060707090b521050150008124503982e82c0d034415401019140b0500b0300c60b00503103825803035450004103c60b20074080c1551004410b000d481d2440118a1500304a4080c40b85548400c01c101026204910040559110504050040c1040e40101078200c0e540403040f000e20009402045103030109500e50000c050340d613540d074011580c100c8400f07082242070349000c0b0806065513020888880c141d0101a10414010038201c066600c160b400000703180304110290158144100108429004254200c000d40107910010a241d00d89560440880e4441c2415480e152242c404e08070020700c1418215045000c00c10900040da08280140d00c0102003d81c1c0e40c545562550170410007406042030b04a0402d401004a43c010606080301c0005450408 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 622243552 1250 622242302 622242311
    0xd0804020a150503043e0616030f030608010b010f1206050a0e01080d080402181e130b0a0612150f1805100908041202030f1b0307140a0504 61
    0x140006080525158421102d0070201d00d98804815840f2018600443c03103000b0580c0c101940007580081c03911415005c080721141c40144580e440303002c6900361b6840c08050300d280e141024910f600b28201d9090b80003070300451061020222240d40c50b104810003010b0110003003080300e24a1000030b0540d02412419410413000c951301000d00d244039440790b80140001041e107000b103659818500a610b0007489030b040180900c0601d9141135000355041d510850b40244048690b181c1c0c80c40212400202500c45d0310200401120527400c1c04c6c151102901900341451074156120b010300d813034040b10030001c1c8008909820124200f10000f4048482503110345d005900f144003413207015070203004005810503840c1480c10b15131715a4140109412085d10540030b85d040e20343c1204038145842c1902c988007001081101c0c100400c002d42200340b0500d5481d41d2004040d1490603441c11090741c075103a0051400c00e040e41c043c440c00800c52030208889001000402d81e401c0c040310080001510352025403007624040e9844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 622244802 1250 622243552 622243561
    0x60610050a031d0d0f03050c2a070e180703020d020103110d05010f0501030614011707140c060601090e040302030d0209010309050d270e010302040b150406020f070608090d08 76
    0xa50880980c0980b0b60390f04401043d010400c6a43e41c80c030b2000b42d4000b06600b07030b8000c60361512a0003901d00c20200781c0304e0180b4000300d0300d040d00c1c130100c0c94003000511707a603101014800703102d014080c8500625401c0174031003e42c14941c00e000300c8581c465194040603803181d181000140c90f0500c51819840c1c090a00080300c21040c4481d58281c1700c0c2c0c18958580f64501070010a1ba05038115003201034643c02e0f80c0c1001400c1d01c2d0240300303142000da2107a09003c5003400c817001440c0340010030075960080407031409400300504e24007000d5068000041c4003501c1d070040720400c6040d5901000d1003000340f000c0c3c00c811075507003882e441c040e40300d10582218120040e00014010416402500032405050340002111006503001800801c000c400c1c28201e8103040f81e0603507081c1c2c003e8030b20341c40406642c0d140180c43d2290b407840d82040003c044083c240307034120341c0d44030117108044802e20140c001095150041c1124088400300c40d4208002c580000c824000e00b0710a0101410000400d1000080d05c0e040002d030b136884 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 622246052 1250 622244802 622244807
    0x6190e060403050a08010617040f020402090a0b090906270a0914011b080610110703170a0e09042114031614040e0609041a0126060610050a 61
    0x1a85564008034440e180510040540c0031004204c0080c00d42d54242940e600c5180840da04280303c2c10070418a061180450b01144000c40c40d0300020748020f2005240194030004216851003540c080311045801040340c04190419900050344170b10708540d240d40185658280d034815484048400494100100c0001c0b1a1241c9a00a031050344c3c1014064070b0002c581490940602001002e00c0c1021394400707500c007100c0d801004a240103910042000007001003000045829900c20360b4000c4d1240300e034442c0003011507005424601c0890510681a544203056038000c0c099004807410310703025211601c20400490107140c0c0c0c2c83c1c0000507001000c034101d00c490404a07416040c4903507251001e1000410700402d04039985960a007071101e6102c4d606000051441d08110f4011440b03009060180e0100061961900700c20f0351b6072061040141041c510031183c078071949203209801c50180c03604c01c2508460b41840030440a80e0b01304003240100400d00c5c001010a098400011010040c80004200784500a0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 622247302 1250 622246052 622246061
    0x40605030408040f0e0618091c170112031d0603040b2d06030106080a1703130602130609350c090f06190e0c0a0c14070e06120619 57
    0x3644044450130301c0c2c0f52440400d101200f9500d4500c41c40b6500c005a008100070b0a00c41d10620080340903101c03103005034203901100c2440100040420040500c005140e003900d9228034040c18a01484501c110020326010340b03404154503a005080240002e0164141c1c2e407801125409a40048080700c26101c41e00303109a520105542045071b0800303000c24040541e00c8441c190320800d011402400701030341c1c5001c900e8450208044c0030700500c000304030041c907419612000b15005202c0304000d4070f0100e0b05464080c201c1e00316000c000240000100b0420415601c0b41000000d003200e01c2504107410110583d6810340719a80c0b074810300740301c813001c65004000c205120240c100c0001620a00c4d080c0f03002d0814502030501101c030b1034400d2040d5500c10440c1448d010392001034480c8000c0b03200203611401d9103080b85400c2244900208400a244d00001031121011808012901001045424145240050344100c01449940600040760040781204000078042d90404480c040480d060140b410601002c1d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 622248552 1250 622247302 622247309
    0xa1101020d050a0605060909041b030c06080108010b0603090d0f090515070618120c020d080f03090607031806020d060f24020703020a170f0709020405040b120304060503040804 77
    0x552001c034040e0808440c41d046244194800340c0200401511760007000301c2ca028030036020740c10540d028002000203072107038141d54401c00000e9007101c5240c2d0380c1e902c4843c41c204a40000c0005100d50300108070101c802d0081c403c46107400c980792400d614220ba09240c0c0c552031110030008001c0000c4501b44594002c00c900c001604003c1c056090f060b40a0516003070326030000e482102c003286400c0519410040c10f4020500305540080302c084815000e400031507140b04500d02c1030341c2c40441b24130341d0b000007125800184025030000340f01c15141c0c90300c041180c0c00d1120051901c818107007842086c06100041800811110380d121000507240c000000c40d03c0002c0100d50011010029030311400b00b141e83c0d540c18038820074201804411100520201c0c2282c0341c406510000b5040102000700b484002c4d940c061480441d0310100440d0194122650041c0ca0b045180e44600000c590008007401035040c41d000f0b0001d0102c040e19085815201100c803240d881c41284603002c20080c0c040080303020452840d040350000e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 622249802 1250 622248552 622248587
    0x9060f02030106180e0709050904031413031406060a090c11070902071b080a0602090d020d03030605030c03120306010806060c01231317030606090a080a03080c040f09020a 75
    0x7690384581c0c014003010303c401022841c410310200c00107041403a90115038440c4580350783c1c0d015154a07001c1030184800014108400b400000000c02030308104d004050320b0084510407000407024030758209180310742c41c14140d0004940081e0204407068464404c2031013218061500002c1c01404010f040754490407100001d009809004000590030f482030300030780b520718007890000070304603091041c40d10304090a100300011500200e102c1000300b0429405401e071004050800c040000043e40000c032214a03250044010940d40c03902888a41010040c85600150550040110ad960b0010032100f070b00000300900d041000281c001000c5850f050260303000540c4107070091003200c0a0840d0441504001150001d1080030800000c0d07500c882c0f01d240c0c02d0f00170f41110030843d1210004503850400c1d800203051a40000b010019150b0365210784408000400040c03000d0607408407145801007101c40d01600400d48410705200a0050b480c00124210440e4030007140180d0701e07108000180c3e00c031b00982000f00d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 622251052 1250 622249802 622249807
    0x1090b0d111504032108040c0302040c0c0f05070e01080a0201080103230f010506041109010e0d11030708030315060306090c03040312021b0c0102030a05160c0f120605151309060f02 79
    0x40002002243c5c148012580c190210030004250844020404036005018886010702c100058145980f0130402900c4a03d00101c02d203419880b000a68134034408221015404420308208403014007092501600b03004015002c940c4440d00020507109040c00003802414561400c10003551607181c090103408500419250400351600e426402040c0071034401c1d001c0d60600720320348021000f070b20071074400740c20507140d80f4520001d41003441101141008200d0f07a2068800c2030343e00c00d80e0104203010091804800869807803410f03d80134a11052040c0d40940110014000d008007076407210b05d5207500410341101036172240d0b15401c048400004602181007800e20002d4115640c210071404960000404011038002c1a00c030001203940344582110507000540500c640040c05d8450301041d4103a5000300304c0c0c0d02889807100781070f100540d410781c48062080110040781003081400d000d0164003002c00f0440c00442041c20010501411091410b044000e80e20540b02c4d0401880da40588650080c410f000c64 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 622252302 1250 622251052 622251059
    0x150b180609092e261e030a030f05010308040302060a18060f0f0f050f0c0313080d081e0109050c0d090305090307090b0607110a030605071701090b0d111504 68
    0x100100f0a10445000d4106400050707458400d4000400e81140c0610103041d002d03000c1850315224104040718200510b0080710f114207104850780340608512150b18000d1a0b40e20752400000d000c492800345d0f19003180c1c2c10300b001040400c80c5002518112501075840e25034864491000b180d103a1406000c3c00310035050580d000c074500f0b9000c010241c0e082c2654550107003c164a050545052080c0103818000400410a20b840100200090031b41c80e01d2040c112401c0c54501e001e04201e00301942c011180c00e40c070203035140b50100d40c0412a0b64100f000340001f0b0f894040f150020401e00401405514030340c80d01c41c40881c03114a103600850346003119641c000c201c1000b041c50014466445003112a200c0c0c4a9001301013041d80c114400c00f091100c005012078540041581d4012559038112a907590201c0c00100000c04210140a210700c00c0c0c032540d54024004540c0c0c40d074500c0b82801a00400303212440d101250f100758441d418100b481d81e030000307284045590404009112848030705041240c0420104000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 622253552 1250 622252302 622252321
    0x3050f070b0a09110108060906040b01020709140906130506070c02060d02070f11190e0720240601050d0b03120d05190c02060106110304050a1701150b18060909 70
    0x80120f103110791036080d542030201c801115240400c2e80d03169809031907200403c12500d070940c48904035030810300550754160b503039210441c100d46c11051211511121002045072510041c40342c507610809003485c0d1500c1d00c44c80d46440f65601001050f00c000d110039003c0c04415580e41c20140d404002d560030040d5910030350741c54a002d90300080101242c140c08406074201c0c0700e1410300c1c0f20b00741c0446030b81a0310200d6071402804c1110800301902e10024458403400d22900400ca114a01d0001c40102d0f004004210340ac0c0c403400041449100402a8040c44a0506c00140c0e4840200c855290065001044000000000034100618400440c5c110350001031070000f41c1800b40c04c5284a282c428000440b01a2490244420b84100c070002c40016000a401400014010150034510306201e034100c2e824283c80b400401d03c01c00040d04901c000300702d410040307016810309004800a5818040f9104840e91030030b08001a03500a41d1144d0001212122032120151910010740d0701014004044442a09000c04071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 622254802 1250 622253552 622253561
    0x12022a030c060f01080a0b04110901080a1502040e0115020f010f0b04060b0910051b0a0b040209100506161407030804050307080105010e0a0f0e06010602030a12110703050f070b0a 78
    0x48000c5400b0741800110300d0281c103040d081c102c861460203400c000c01255541c00712094020812038400c0c003c10b043d09050b80394541c0c5580030705100c000030039695210341498001340d00d4009101417114010801407040a054004903411a0300c0426869192030700c8800690a250110604e400380350f20b04080d00e120070b07001750043d041c00c02c0281d80c00c0200c90b803980380b01a01d5216440c441500038141c504801c1ea401e00c01e00003030503200c0e5099503001c00810b18100243c2000385140090f51582d40b402c2c2444150320748003c40c07940200c2001c80c1c14402c85e2600c0003282c814001e520352003485ca0462f0760001700b444050358003080103042c0d28043d2140a03840f8940386d001a0490301070b2501902c034591004c250210140b05070307410b03511510381f500019681c141004014141d500c2c00001d146459041130218000c08012107070103080d0b00d402071501d40c040c1040041200c005c001c01e0001c19800c2c42500341c2080005801c480b00b5680602e0500d0f550901480040f103a03108403071000701114038513401c11841c000190300 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 622256052 1250 622254802 622254817
    0xc03090b0d0606021b06070f0f02191a071a0408040e0726040201020601030206030c07060f1a0d0b0103060b0406210b0a0606052a0a0c06030506060304110f03010605060a030218030d12022a03 83
    0x11030000c002c0080740033099a0040c1d050040024001a800c483c3c03407800f14440a90151080700c000d03152684900b00b0310700081e410740303c90000c18052000c0c00c0b801e001c1d81820580d8440b42d40038030368240c50240c0000707540700c006200290142d04000081000e2070a05412a11915003000c000d201d4030300152628001040a041e104000d82d030191418030303140c501040d03403030312058000e0525040ca07421a01c0e802c000340b105850b101e5200d0380d5103e002070062000d0342161903244d50130f8a01c601c12141d60900500c1003400618503010340385803840c03d1002c0c81d0070406580c440c10500b02082440ca0903401e0020340311480308000031072071184600c40801c01210420300415601d013603a00b170002d84c40344803e20041340020b0714000e08000000301443d0407030078089883c40c848a8020008038401c0d0740ca41c0410103a6100c03141000000c1c0e00013404008012600b4140064003030700303400800e02100180c000400e00c90341c040712a00c5e04d03600018040300d18040c030003403009562002c803004080000c10f001c1a96580e408100c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 622257302 1250 622256052 622256069
    0xc26090606090f0a0209041d0d082a0c071a07200a05040c090b341a09120a09091401080304060c03090b0d0606021b06070f0f0219 57
    0x80014007a402d0221403540500b8007000000041d07100d001082010350048900d071900184d0760050240c043c148120a1000602c90b04050003030800c07501070042842200900c00f1400d410601101600308610740c8a00b0014400000340a031281e80200e1003c0c14404590b1150450740c1404a0804c40d1091100050040520800c5c0c41f107a14404070040f000c060564485480d480924041c0412840c18a40c0250140f00114034251948517102c11611580d82c200149090040300800140d1002840d41c481c4485480f00000340b001801d001513440010b07042508032000105500c0b0004204500c000b00040328090452a40c00390311123080450041000c0c1d1188641d0400c181004000c2d00707076800407440c1d581a5003616001d14641810031106407421028001c04070204581c2590015030f40508030003414034090245d5010034850304d001e200034501240306110342d00000c508803001105640d000c1c1140c503c2ca1f030080c5480f00d030342c2890904a0401d000801c010b5044012985000c0c24962189841d8090711401d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 622258552 1250 622257302 622257313
    0x14060108130209070509030102120a150509040b180a06020c0627060604020c0727063303142509080a0b0c090a0e160e130c2609 56
    0x1419103261044101c0002c1d420140075030205040030f1040703008041b203032070242c005440c2610016402800c64030885091880680d2589860949912410550f009000c2245c1c22201c4d400d103512064103509010342502d00b0034105c210045143c05d0144900d40000f600308034119219095501e82e640c4800b02181c01c8100c00940c2021004c81104036010311010400d000000d00751365942c0d90900000358040e990400d003030702c07035039100240030001c07136101c007509400e041c02810654140a10f00d100740c4115812141210a28220021f01c441ea0b010000015640f102d45c10500c50003e10003d4000300078400e00380b01c070b09201508029051011144a03c140d0b08081251144452030601c00c4076a88141e02400c03400760050102c90020a50030010a9003107558112614508009400004c0100316554413003007203050b640d0100844c04550050480d0901c40d5400c0c085c0700780d844440012100a009414400c071940c2c1d549280d0a803a21520024144001d80d15900500c01d07682c0060300c10741e031411528a00a44a035 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 622259802 1250 622258552 622258561
    0xe0708060615120f0408090d03110f06060d060921110705011b032003130608010e010f0b0a0e120c03240105010c210504180b0f15090414060108 63
    0x101011a0441e4021400440040d104d0303040001d000b18004e03106551011007409028515507505603281e201d03610036162140e4110034070300c1140c180910240d05900780d80080c800c10513280ca40356481003829510040000d1909458034000940800918410941840c456a03003d5003a400440300002104001c003101e400ea6921001103451150340312840c2c110f110008030490000b4040c15003c525088000c10401c021085682c450f4a103820440e548100484044010840e41d50003090340e502401550404100940c1008448442c001c540d108100c20307040c000414807461841840700b08101c0c00014202c516095098120550703603941155920b2203801840d00316120086c451103080c0c2e00c50310303030001103116a180ca401500d00280141c1d0658080046010f90702c0e00c900241e80c45a44038a16850b03654a450415100180c16030044808101261a000c84080c107541c486403541c40c071600840b01c070100310008150154440c020785010a411500304007d40000c0340c0b4010b40300d031180e407080e44c44100c0c6070f88 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 622261052 1250 622259802 622259839
    0xd0902010e0a060912060e030c06272a1201061d010f03080c1c0206042120011d0a1a01152a030201060e01060908061501030e07080606 59
    0x1050303c210804a07010b030300200103500e200f018030401180156000641c220000440038150f030700c212001090341e0007807802c0100a0700000c058100c242031851b0741c0c640300c1c1b0494001e81c0e99220149030250201c04181901c02c0da070101c4c091001082e40010309801800417250b42464040c01e203e0050b4509e2100c086230905064210001c0e160484062001301056149540c0f1543c070075a2100c0b0030406280156008044081201e0b0b110000c49802c6500900c400e00e01402d218007510700761f009462008101c180326002803540400801c41d1000c1032040460070080480c60980100b06184c0c00102c3c5090b04444c0c1218420b02240300c214050007030b030b038483d815240c00d056441c454000740102904481c0152900c6030003441100032034256001155042440701c1d884030880740340b2a0030f01080300187e440b40e2041c0301044e62422450700402c941e0410018071801d0001071900c0b094020a1030701550380b001102281030f0310903084070302c00303c00710b03029190101d489a1030240c44803070882d07503076001e0119110380020116 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 622262302 1250 622261052 622261069
    0x8102102030f0d0e120102042111060a080403030e0f3415230d021804021903150f03030f0206130803241e270f04030909020d0902010e 59
    0x8103143d070b9800300b004c000790421207603600c0c4004c03031500d079903080c003001c10f544098180c6218814407e540f079141130129460a0440c140c59084414042c00040c0b04e03240d0519004001c6a41103540f60401054140d80c00301f074039180001c5101c03210b0882c400c403c200d0301c0b10022480e40000c2d5401401480407072407110120400f004915100340f610b180d0050003c80c2d1028424014003401c50f415481e0f00798280c91400c1601001e401118220f1603082c0e00107000c04551000c19050f0902d410180c40c05d40c03d140080d40c100741071070075103240c000605454003490840c0c0c0210224180280c0503644152100c87d80380d0a0047c030408034080c98601510580e03011a00321041c420194cc5100d40c420344c1d0915659903007260b00c802c25105002c003084100b2440314044140d580f05085201444c0741250841519802020001e0090500c2c1201070001e8601034030340c205001c10401103600c0100c18104200680b00ca14080b40c1c0961554056030111744081504400507600c1d03000209018000d9032819060030220f8104981c15 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 622263552 1250 622262302 622262323
    0x20a020106090507021507111f051506030c09010e031b120304050d08091f030b04140907030b0403140a08070908011a09150301090f0204060b12060108102102030f 71
    0x1070744410252003051541d00034003035102a6238a0007845450300e0760200713031402003850786812040402110040d040b642034030031309521407a031000d01c21a03403240340f020403078070f20001d411058590000035070406164011402480c0c000350113412191540300d0b21220700d40064031880c010b485032214100e0070b00b40c86000020340341510030003811206603421545e02c1c1d4103181c3c0300ca002d441d04030100c507200c860540c0010280102041c1e0589003c2405101c2600308412a201420100792803c3e0307803001c3c0a10001d0000d0703d801a654424226203041c0c4030f0703080555a009803d80b240041d410002154840d1b96803103d101e50048419490300e20080340c80e030341715600740d41d42c10808540e41a0b4224000c0e486141003182e0711740000801064030000c00c03600d80440c1c00d40b284d070300054541209411000303045041a1103920b00030507403640042c0c184901098100344400002d84070341e04003c00c85020651034010000d00e10000c0003810b51a5400d0176101100c4010207049030b1050b40709000301c80745648090303008100276032078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 622264802 1250 622263552 622263557
    0x10606050a052d070302010e160308092b0c0905070804080901210207050c10020f03190e0619020c1c03081e0702070305010b010e0f0918010609020a020106090507 71
    0x1018040050002d0920f0700a05160909200c1d030000d840c801c025100414105010703070f00105000b4003044040307103410300f401d8450900080010707040010803903004c141c55600b40c04072100c0c144403030841c1420924004042c0140051240074101004004c1c11100042c100c0e03605800500003030342c07203032001d907444402190040c03d80007007000b009c101c1e0b611a41c40101d007960b40758185040059281c41400490b0410f140480d4190b112415070205407611802001c3c180c682c902c01040c0b505141000d407603d07400341c0d0895450701501c1881c03d5201500408000c6200302019151580f40d1002205420b04010b0380c0000801500402c11010718504052059038880e5000c10303c8981d003806031343d40481e10040b0040602d80c1035022100015401c410380e0343e6260003038040360700410415046041040c2100d03c01242c1505000c000c030742c2c4c60300d01e883d582000100801d04450905669480503010070716090300d0803008604d9468164040348003112503002d0806504940d0080001c0342d121a505000c440007039a26201 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 622266052 1250 622264802 622264807
    0x90f020906121c030b0a12200d110108060103090c05150c060106020609060a05010e0106080414011e0b0d170c0319122306060a020a150905010606050a05 67
    0x160501100954100340090078070312110012101c0c40c1c1c1460b100303d040d80c0d80000403400516400340c0c940500c034900e04003150340d02086450710391038007448015103600034404000d084150400441c00300b41090784110142a5a85202181c0740003ea504c840303410b418081011200414100d521034810b80300840d0b84950400300e55800c1000300241600c91a60411000c1400c1100c00d02c0014140103080c020400758004010320306150105a00f4040000e00540c2440e1400b40104034009440214604492480c14107582540f03e504120300019446850040190b0030700c00d00c07403844180d0b2280e1201c8a0300540f4100801031180781003118240b403404029107582c42c148008000d64400310001c0c035805015130f080343e1408482860841c00600c0e030081c440041003500140c0f4040c0c983d18096103524a04000a01c00c1010103240141e889000282c6060b006000100e080792009008004500400384c011401003e41454180c10201801c5040d41c110303940d5003810000a025801042501c40080d02911941d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 622267302 1250 622266052 622266083
    0x10f060c0f031b080c010603020325031101111506030105072c01110d0801030204110403020120121210080d0212090f0405040803071106060d06050a020d151401020109 73
    0x120f400d24581205282183c0004882000030428001080a2901d54001180803441c6004050908240901090004d810328480c1d003030609000010701c040d80d80c06088003560700240e1004071185000d03101407800074843e40c1101c050b010050941144907620480090200b42e4880c18225182c010100c5005289050011408418000300001488150041c540100c2e0301c481020454a450410402c04002c00c10010050040d8180303400303000501402c6140040c030f002c0ca140d0009180c0c078101b00da1002680d0000c41402030040007408009000114003003119281c0b4049800c009580c04113448550300000701e1600021003940124a0950050780e5401a0024000c0c00e01c4010150748080003480e44000d40c8009104565154400c0700d0042e40601803180c0c45c0e02d00864041c01100c03900d42c403400c183d40400d0404c4500e03666030303420740d140c80d601100129980d10760700200d42c01382c0926a5101034807420444903034104425024110200c03000d0801c0354240500d0702005a00700e078840f00c80544080001100f40 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 622268552 1250 622267302 622267307
    0x120f06260f0f1e100204120302010606301b092606011502101b1b050d031d0f0a0b01090b01120216061d010f02040e040204090201021c0305010f060c0f03 67
    0x1400c4110368107541c2c044c420640140c080303074040d422200c1c0c550f400040040502d0750920890020f0022030030140e880c900703080800b418046c0d07040b1800c1081c505000c03103600c0403903481d00911011002a8014560070031181c001600503801ca0040702441402c25100c400c00c603540001da401c01c2d43c030340300203850306909084400702c0000a8000000a42c4200364062060002c54810440105c903400c2c584a040400f403000144540d03109030003c1e243c03071003001040002c5040030851182c840b886080020380144090444001c0724124001011140614514140c04078804100c03512014410601a40d0a0780c0f070f194524211280c1104250002d940c8602d40b41880949034020310304641d0010149042e180e10b40c0c1d8440076100045007080c001c03299420315444840c424018625841c894072002d42c2424107055007010313562401807000c0d1140751194811420b5900910481040c410401c030604294808103078081e015000030700c2002035103450356500150700b070312404840c0e000d140c0c013a1503034032002d1454804 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 622269802 1250 622268552 622268593
    0x30c04050f032a130218210a05030307170f07080a1e0c030f06050f190b030a0504020a0e0f16050f0703020a0b0604020901120f06260f0f 60
    0x3056018861595200a500c80005a10203901e044076a0b0a06200c01c003003e11101d000c031005620041170041c400564000c110425605400c882603690007050345660a1045407054000c0d03c1f20803501a0322400810f10001000071440b5180d00c0c0c441c825020820403900c1c02a500485906000c0403490020038002440b403041c8035005841414041810032040000500300100a100c082c040d40c0d684035028040d54050083c001e01130300c0301d0803c00c9450325010110b130321000c0214581d0320560041c0d80c030b443d1414084000f50060a00407054540721f140a212800040405982c00e912a0402010004807002c80212162054056070205c46441d01c90204480901c085078a0301018840c4c20311030740e4080c15442000c0d200c01c500940c0200f541d50501e04025154040c040d0605000e940104203002e01d59800c2120b4201045c070300a0002046a512003001c030081c5003c1c1c2140114155860130300b072803034420210140d4070840380781c10b881e0342d0240d01c000b940c3ea4402103d0489041d03001201071340d602c11b880d40e04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 622271052 1250 622269802 622269829
    0xe010803040312120c020a02030d1103040501050d0e03030108100e03030709060e0a1e05040509011b0c060f0612120309020f06181519020a030219020301092015030c0405 74
    0x203244c050380c40841192810360340705d00e500c1001648020f41440552600700021454440b047c01d200d1414000304034155241e04c1140601411b004c03000032036401e240550341c0101c80610b40c001c11380341c0300d50312005407540b607242030310401d070a250030446d0100606c1d0020040340c0c0560682c0e21503403811441c01e0000da8030580c44502c00380d0300907800b05c00015540c8002c1c0c0801007840b0640941941c09040c02c0c100021240042d21031141c581c034041e050307800111805031910f40b0044504091002200070310300800640000446510b40c01d007403400004065541a124121443c81344002041c0003440150840c11112100e501940c015192604200241450002091210a0980130600a110352408035800581c0e030030014132181c1c000545004060101c0c3c01c01000e1807184d1001d0144c012050301e00a69918001080e229501c01b4210140700315902507220104840e80300443c1c00002d5080c0366804020b541d000e1100d40900c1710710f840803848207820130807a803241c07031031f000840e007810b0800702030156001401c030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 622272302 1250 622271052 622271057
    0x3030902010e09040b011706130f021201020c0a03030c170c090d0f08190c05030f03070e040e0d02010608010204030b0c0912250b03090d0f0e0a0b12010e010803040312 73
    0x2089020741c0d1500b075200c501c101c0c05000d641781a549003580e001580c0303803100b24060b2150404400c0c0050140c6000c42e10600c180c110304110184105400091840c900d000c0c180d40c143d40c400100215815030200300d101345580641c404103c21030100c01c1c140c4039404100080000c814602d80028a150f03860301c0513100406000d80050003420b203695985424030b507820003d681402010031f2180585800d08040c0040c20071519180320706525950f1190350324000d222040c0c183d18804000030740010311512106502203c020028440040c60300500d580700c10b60024003000550034040c0c0400c1c95503050003101c088070b0340a0801d40180d83d608102d16030980240c0030060380300c255032443e4505c81c40e0401680329110030041c0a000c0e03500c40e55403020228150f0b0713071000c0c00c2e440d42401000340e81c0202090b0f03820b501b003140c1420011050700aa00321428821000010762281c00444003192038054800507011b0b03211002d8052185036207440c404010f08000340f0520032640d20030801800010f00900444041d8074250 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 622273552 1250 622272302 622272317
    0x8040308160e0604080606090a06030209040b0c0d0c2622080904091406070f0f231605100b0a0b1623060a050408031f03020603040b25020a0303090201 66
    0xa43c142e12540c00f2105960060b002d000300c80c60026039081d005121408200240b42ca0340e03000c903e1038080100068201403d480c0080d9180d42164102c511040c1d145204001c200681d01c130240c6814440e0840c00400f01504544440380c0f0803000c010350158440030451291505a0006020f00051f0b20404840c1100241300e14813003034495000e40351401d8401c08402200c044842c2209140101c01008842001082c0e4455115190000c00308044040e113441c0c806210701046c0c0610403007001000219079034120024640e43d1031140c48610191651256094039440300900c4101020b54000c0c4420b103038018a460310811480440500815080541e070f001e4900e010b16030340b48d9029405a4070340384030020590707030700aa0810134244099039002c0320403141005030f070900e5116003d0600004161402c655a100aa0001c044450424500070b40d4020800ca6891509241c0040c0052003038030265030810000340108204140702d045021802d01c1d40e40100354114441c1c60440280c65104016070500c00d24 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 622274802 1250 622273552 622273577
    0x30e150403050d0f0f02060103081629060319110402071b120303060506031e0606040308030412080112200604051306030512040f090e0102121f060804030816 69
    0x40c445a00d80000307513183e020600c0e070f4540340581110601c0490707100b1900300d0001800025021004d455106103c10004140b810072484c0c51032403811140036260706001030740c0310300d40c4140341000d40700e01c00c82c0d0980c01c0c2d07061a5000d8402d151031401d01800105032180200c400b40590034998054210b1070700a8540000413246c000c2900110000e5412440405070660003003002d141e0940601c038005c100c00d4031220714501c1c000b04c13903440c443c041410600c1e03003c01003008250b440d9611000e807405981c0140b55280d0380d041c589041e40c02c100c104102100400c022400005044100d2091064003940143d00c04100c0c00749460201d40b940d0240600590042040c40049241e0700d5108907004000c0244034005802402c5040c2545002c0030040e002e18080020082800204c2180030701c1002c80e0750181001c206200c100040b20b0190061114852011441208000145400707501180c0201c0602c0b029640d040e885440854103050308480103000b2403010302c00b04480711000c0d41c4030781d4424200e01d40454944c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 622276052 1250 622274802 622274813
    0x609030605220c0320011d0a090c110f010209090414012315040204050f060d061a0403152307090b0408100608070302031903030b0607080a030506040504030e150403 72
    0xb03011040d10000d5880c4424401c02c03503545444e80305d0348032170a02034090094000008200141403a4400c504d9402c400c4040800c1d00d40c00100400303032802c10400d00549401610040c440e0342c00f81110b00b80c40c0314400f409205c401040c8229803140e080608900c0c400c1c3d56a440e2814480c015000d40348096503501ca4000740149004155080d1000101000009082c60303030b0408100e0f035404030f541d4411481004200040e50300e130b8040156521050b140c140d00d43c0c0c204964900281031603440f0280114014950071814504c81000b0416a8461144850a01026004003040f200c51419014120410090300004503698202e0580d11110501d8400320468a0f5800e889160700181d100e144c59a1020204101c0f81819014082c00b5000341c030000d0089505e1500025035031440b41c004071a4100d60b00c60540c0905200ba08a01076180020306420f43e01d108500c1c01007116400300c103c13203001924110210707410389403900405005a41540d03c040340061040104600400b0140c2d02011015040000000113075 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 622277302 1250 622276052 622276111
    0xd0f08040807061706220c030b040e0706140a0507140109020409060b0f091e07020703120c0b0f09070b0c0109020a150e0a03080f0d0204030803040b0415060609030605 73
    0x8069581c202c4a0b54610307551041e040406006244071b4441540c02e04501850481100d11184101c5404118003c00311010340c02040b241210541282c100900c140c5220300010b0403108850301c942d50128100c0c0c0981c1c100005018490398103000500800020b0007080304000820110034104000042d0b0040507030014003202c0c440c2604458054030f03a40000220b1130b1008908107480803d4031040c1891401e11401510317441c07620020f071032a083c040049100740e80700b0000b0001440e40620b400b00454881f0101070903943c604c41c0c0440d10500c03101c1c0042c12340101411228052007440004000300340c01d0465400d241e40154110110b69907035028900b000d81c1e00c1150003c0100a50f1445020944c20910020207007000303200d401d8096034942800700002404001140e080f2200c18500325154524000680064402d40e030014100c450b0100c144006d00852006150180784250f0340207011000da20842c100395401e912a120104415400400214100780c05c41980820023003081a224203640f40030741c0001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 622278552 1250 622277302 622277309
    0x70f020a080114040615060806041812020303040b0601050a0c0b04020f060d0b0a050105070203030a2303010305030d05090f030d090f0506240402070c05102309041107020d0f08040807 80
    0x300940743c1407106100d014858444c1401c655901d01d110070703042c84006800904090071040c0601e81c0ca070144100304003030a0640d101e9551041c14800780d0031610348000e5880d00103070340030b50781103c41e1004540507601031000c95000210544070f4000000107911221400e0700700030026a0000700c5940356083d44d55920009011070a04090300042c034150000030b0245500c00b171342015052001c20840440560b80000c280c507607642d42480c08121041c140140c50110744109501c20303001c01d40c0800007104201d030100103081d610b02c1c1b6100c01c1015560345800107a40314034a860000c08d541041216800742a40e83e00154605030080079220f1280006503500d5242c101d0490780b01c5220040198601301c020384512030684841000c450640c1403800d01c0d200d40e954000381d4030403d4490990000380d03003622400b40000080440c800c0b41c0710b800008606039170800d41d60042050034865850150200c500d0748416081c1e4078102c0d009040c480444032150345895a040400c001a141800e00b8480083c041c0403c00012001c1d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 622279802 1250 622278552 622278581
    0x100807050319050711070e041a0a0204120602280801060e0a0b040b030915060603010e060f04060e1906030819140307020d0318030e10030b030a14060c0c03070f020a0801 74
    0x3d040a414281c06e103400d5400071492040d00406000109007507144110074040d420b049844036443e0000408000e01c215481100d01320b0380c442038401884015805090504034119408201e0944045d040e9003440a070282d04010420304401800268403c00c02410140e101411070b812a035241e00b0060107540080d440240006000020007144000511220a403241d40b2903070031003642000400620203003c140180140e82e916000010040e80d80c8441d102607901005e4010041c0b2911070006110144c02215908081c40801c40c0e840c090560074401c050840e038008440c0d84c103000044020000d010410303040f0504100340d4481940c050890fa0008500400e21500281504105604050240ea51402c0811440b500710101440401c0c5c000600c0c002c0d41404440402039400140000e40c01001401682d40d014815440a081000f004070781ea48403903451641151026070380c10a401d21144220241c0e500150800e00403040080c90070540c00b0a40c5c1d200904041103640c94011450840e01c84c6402b1010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 622281052 1250 622279802 622279817
    0x5040606050126042405040c08160e06030f030c0c010e0d11010e01030204260f030a0906080403022a040b01080105060901051305040504080c07051008070503190507 72
    0x4022051058800406081c00e003800c100552000150a40c2502903015900300c00000004041200c0100c072808142d104c81d0f2620394005403c0c400c2401041e04480482e042c00f00e600000c40c25400005048102c5450310355000c170301c0c4e82441c0c00500100800340c0351a41504ca1454282000b040030b0000e490003e0344840244442d41800c40014000c0407841500c9002d2240070440710041001d0f62007090802a003803d0907010307903100c000120001d10580c5e021001007091441008a00302c101d80c820b003207034403420080b241160030905030b440e160320400b00c0900116000e400c041000c1d60041c481540d0042c040d0040d904040106aa8040d04091030320056039000c6400c0020745243c9041d1148280104c000e10340501c5640c1044040b501c0c82c4900c141403418400b0200b5881f0748606207581e000301504001d4014040703401c0c03515000b807080c1c108203003060040c001c6100108403400c100981c0301186d801b0303a9400e243d03a01d13002d605035901e90000c0c204100541a40b44020407001180c0141c0b40607140c2e0381e8131075a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 622282302 1250 622281052 622281061
    0x1a0702030a031808030c03191107030905122808040906030b181f0906020a080f010b090a030609080903160501120b03100b0109030c0e0f0109050402090a0203062205 72
    0x282156800310460803103c40b81900900844c2580781030ba94001000c034603495894540c1d0514035002c2030010b10720329909090001501c04101c11070080c1c02e44901c00d031944144151210300b0007000e5000c10101c5122070740311081c200311009150958a00c507040340084016403c1d82c0781c80d81c682c2c0350f001b0b401669074039840e10f0042041010300186550700c0003c0752207440140340e00354801c0da106e44128090184c03000110358180350b10b9031198441640c5541c07080701190303500d50184019283d010101d0f03221500311000e000014034200400d00300d40e804040105400b0b065803c2d03a0b2281e00814442c0b10955040c0b01c02c0c84528055101006056a0110060000313032a007481c00000400001041411180841c10004114000d0f01c0004011907254084100441e100c0719180048815004551001d401c4000c0c81c800095003500341d04200780160a00c003034200c0c003030380c072404560103a0fa01518000c0d00440313003400040b1105000d501941d0040b4004081090072400007a02001d5400c1c0c60070056001e039038850612 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 622283552 1250 622282302 622282307
    0x190906020306010834110102040f050a0f03050a03180504020a080a110a020c1002240a14152206180608060402030303041b050a120303111c091a0702030a 67
    0x181e0200501c005040091021704401c55011194904001503c00f03a50382c209000e409280c074041e540710054021502d403a80c0341c440f2020180c503445414005d407c11000030500c2c410312040601626000801407900c2c403004d503012110080c907a4030751004801501d07030210f1151344030f000514003040c40d5a00d07941e05040040c0018115024208440b0040c07404101c48400c95802140401c0c18a00c1204c40030411403512400341e05003143e02c030640318404403101400b102701a108102a018001d510701c2040074403241c50419508120543e01c7d40c13080001c1041d10250f0b86000695102110604007490881c0e4440c0c4003c442a500309802007146044030641441d41c40c48180314240051100c030000b01181d00302500460380328440900083e000d01c2c01060501102c0c1002e00c008002403030007410718130409070b545841e090010a0b10004400080c100041445c0c09100079041c0c995041000b17010840e2045240720090040c100400c040355035a50128006907004001d0004520035880350700a1a6078207840741c0300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 622284802 1250 622283552 622283567
    0x90c060406111e0706050309010b0603160206060102120d09020310020d02041d10050603040f120801171203271006030221060402010f17040507090c030203060607060519090602030601 80
    0x3c02030140c2c02c1071181401c0040000e0610480c1d6032814415a03031744403101054050440484066000040001484400c07113040881650b9120b40b0b9080e80c0315901d4000c01242c6815860f04004550103003072000100140e550740c8200e0002c0d100800b100c0d812824480d141c0241c0c2c1001401c075020546c0800c08100c1000d1400c0200f400a4a8091713990b401d00c0c3c62444024520583e0003080e004500210001d81000700403240058100d410070319014064a003008014840034090042418004690340c2094030340700005074083c0388104d816025425035035898107210164106010024030100003050384801c0d21001e002c41c1c100b140c18540c01007540760660042c482522078220b05811284008000402e00450114045030001d40c24a00b01b0381441c0054002c40340350b242c2804960240803030750180070402000049a100f1502c403044140030070103800000790f0480c08122005a0005010019040011004d07842162b000c514a1082e1120400f182941002c0350000740c0e003114260b500006102c0c50f503801586 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 622286052 1250 622284802 622284823
    0x201020c0c01032f1e04140301020c0d1202070804080c1207080c0d06061502060906060a0302060912030408030c0102120114061e0d110405190e0f090c06040611 70
    0x80520400c1581003d600880550544c02c4038245001040b42c4030440880c41141c0c03050408407002c10728003600e07041946203075020f0300c1001c44044c00520010081d00b410300a03940c00c1c6422201520041c0d203079042c2580e803030303400d035001940c03c690070002c04000409410150024010b00001004410648014042c118040c60401c0032580c0c0045d000300b18450300040d290600403815035034918424a20303d0008050842600940d400f058541c10b80314a03039034001405480f0700f94503402c0700d051b0f03141c20080c021281d80178040a07410000800c100d01030750505143c6032102301c0003c0200c038070307280e500c001050964000c084001c0e50307079400091489541c020113885034050203541190340c10503003c5100242c498803c1e0041030b9815094555146000c00a0f03c055515465100c441881040006c0030300b5034040d072044c01072030310a41c152041c004d254100094114140d80b1002440c10701912a00c01000c450000149020138034450a000c102d02510b400d800f0300018070315502e600d0800b940202440342130a40b0f444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 622287302 1250 622286052 622286057
    0x31a030a0f0b0721020918011508160509060f250b1f060e0f04020412061a010c1b0308280e010906051305121609140609180d0201020c0c01 61
    0x401040f59941655084542c10f0440c4010303510400100402c0d04084840c11b01f0384a01400d9000044c05c5201c00b60304022000ca03075481540356505e1a4801074202042410140000c10034040c282c2d240c20000010b00032012042c03c80340c18a604049036100781510f00f07450785c400d03151400b000030070420700c0d440050700140500c458003451213041e03010000300c0c1040d10407802040507003d20301e005a214110310030a64800a032081d5921500c45801000d00102c2180c1225440c1c0307044000c2901c0c5030154015107240c08145c1d900d40f1500680d889000c41c01880f07507415941410000300000c00911a1402040401600c0c2e90460742c800e0b01b6000c08101d0f109107402d100c02c2c00782c162031011040c2c0c0e0143c0003105481da03070305206071078142c411180b610700d1303c042e0000307078110340d2420302030440a00002e2072201c0d81f5481d10b02c201515840d4000a003d0307070718040c0c240e051001c4900c0422507502d080303450540d10001401c1c00c4d1001d0030807204150306c1c080310880080701503540022004540070041c401e0751800f10742030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 622288552 1250 622287302 622287317
    0x6080d03060602060f0604020c060a0c02071403060406050916030f03030b01031503030f110109080d050c040609090c0c050303070807020705061c0e030405061305032b031a030a0f0b07 80
    0xc1c3d1a50300085c003001c206580c140018440b40d4680d4141c5038440c40010455005281c009281c0b0014000d80060074058070420400003500c8811202d500000d02c0042c000e44425112655010080c1078007904884180c005c1000c00405402c40c02980d00c001c8d0300620180d0f02105590501400322049440382d0f0f410142086007803400000d070340c54058126981f51502c107105540300038003202c541c04503102d218455401c0500010603c40c121029101130f42c1a8681007000e03465030003000f152403040d441a4004039013050020480e11b4490360240707824085c42c0c20090b11121441e0360300f034216401102d4100c003164822060210312581040b0b00341c090507007540c640c0d20b02607084549116040700306c44448001034448080d060555028810b039001040b014024603101e40c04000324803081000c1e405428000c1c401d501506210031030203588060095140151240c27101800c120480240c2400c0040d4030202d5003804100d4119201081a00c1c40c031801040c90421482c0e2030b00d40f1092500002d0140410007204 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 622289802 1250 622288552 622288559
    0xf0f05070e0f0105130602060103020a15080a0905030433020c0d02040506030f1f0e06010b09010507230706450506030c1b070312050d09050303010906080d0306 70
    0x11030750080c003140c00c0b1070381d07440ca00050700125072a20419402089104500b9000107540340c00140f0507044e01e10131203405019985850031905005150320001c130004040001081e054840c035400b072100c3c18010300035649031548070b90900800001c3c0c0f0791081036071020300c0115000c0c9291441d48000c21a800d03c058540201001c00040080c0c2c00d401d00640b00c2c9960707401047d038036542000800c003907008031020ba6100400745582011a07010080001101034181945032107003103008034910741651050200380f42088003402c011255500898412a1035007140060456000d420040444140c03001c0001052814203080300140354001e00300172190304010f42c0040318039884005109003d5810040c2c1c001c0d14103014001d50300d80303540c450b40c000ea0304100d000040c481a40e107810000d203d500e00341e070110402035000b85c40340e640d80e203520f120280c284900b81950052441c8203500031324290f05402030104010549859640c199031080c3d10104031150360b00000c0041c80340030701208118003102c1c02c042010502c2e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 622291052 1250 622289802 622289807
    0x90109032a06050d1d06270d03230402061204060f0e03040503070605041206020309030f0706091217010605090a030c0e090613150507050c0a0c0611010614060904140702010f0f0507 79
    0x20044e0641f15003180910425860641e0102c94640d034030f0300e02080355044400284080d0080c1008003901e4000e00428004001c005003003107000b0300a40d4090030760f901e008800d072100009081c0140003240c10a880f4500000070350a03d005503e041d901d00005166a50310340001c0502d03000d1030340d0040d0103002d82440b040002c6600941442655070f0414000342e900d40e0348141440c158812a0a5150303403110215587c01448400e5000040c0c5912400725a002c460440b01c040d61f2004044000345110810100140300c6c0134410b07009001d5490015040d0602c0640342d0303840340d0701e600564000c50f501c807007000200221709004001c0340b604040d103603a03000e04e984441c1d00e80c1d52811440d002d404003681d41b14808148c04a200d0422514041034a00c00d448080c1080e2030400c824103014451600010440362185031040d00601c00d003400c50f00b1300920001d144400c0c0d000e1000d55084040829840341d528540070031001e5640c2d1189105225590001a024906c0c3c01818100ca050700c000ca17520a1400b000c00c0171068 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 622292302 1250 622291052 622291063
    0x801091220030f09180c1804050105090a0b031903112b0302070302030708032404050709090509070f1e061d040209120712050111090109032a06050d1d 66
    0x100461401951140f980d0007042d84170342020090b51303142100008002a1102e408043c14032140d4240c440c1840880c2e1600f040282d41083c0140f0b980704024070302044140045501c5204c0c603400240550700008801d101104503501804000d40c00300301c42c8030907800b40c4c02e028409c0a144031903031030340f03070b4a1804a9441071541030b010211a5081c1540042c551042c0741c02001a550340d41d6024011b00e540e4036241d0358000300403405100504082441500003d03d9184c40e00800348141040e030b41c0c0074222131500d640038002c3c9c0703030281008244d401061004602c0b50b804640c880d014040030100901e41c0f5103128540940f103022a031010081144040f204680352182c44c00170b2b00005000c4a015885508600000307503030321203040b6030440b40c0c82046000544440502104900749000b00e00802c0106c8501c1030480b11031061045c0180002c1e9620307003c3c0002010102e03290584114070441011503084103940c054280c04640201e004180c000c907052801480764040c1060841c0400c041289507080d20708004d6462 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 622293552 1250 622292302 622292317
    0x2d0403030804031701060e030d03061a0f0f030f01050a1401140f0d1508070f1a0f0c1603020a080a2102010e06011d0f0907030b040c080109122003 64
    0xc80504042420f00d0b21071110388180e60a086010306165075980702c040d1180d02200040d90003400b51f400900c501d607000348901002c4800e10b000071a841a15401c9884540e032003d6141904000107100c540080d0b190302c00651b01c14442d05001c0c1010b0750400c07003040000c407500d0307200e9503101322410062466a40c0c03054414507520301030141d107502d45180618030443c0d80100c540035103000703180203c0090030b203607a814010101d400c1c82055590302074035884007001d012614000c00383c01d0032030151081c0744c950b00351000b07014041042c0c1050b801c000c1c00305921340c00d10380c0b090342c44101e28600742030501c250b2070210140c2d00202503400043c000c903070759581e560b4142c5503a0015a044c6031150010300c9410f50007034111186018091f02612101c2d0384802d1100351120380c0f5000c03075821143c80c030002168208001c1c40c1e035000b007002d00024904d45207503960703801484100800894501d03020300000242c0d08001d016020a40d84644d1111051500b8894020807540c607000d001d201480401c440e0f84561079001c0210307100c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 622294802 1250 622293552 622293557
    0x3040b0402043903090227090d090e040f0b01080607020d11060f040203071203110c0d1a060d080a0806011106130b06031e0a15020a0e090a140108032d040303 69
    0x83c4440c8050a030014844100c000e0b401030050340e903000c0c0318101e203604401100840140c0282a860b080032896035408185c0000c000f090030200144205401025190390282c850981145092010303658161102002c1c1d01c5001c05500280034400d00580511071503103d0f50543c509688031004804549a80d0803024240b91088003010b0089000c0d52030900041d00505488250ba424440c0706190050103800311841000142c05004560071a0707143c8a1070b1210810380141c00c00000c04040401d1289800018001c01e6015800d070011324000b5000300060082e1100b107883c5ca0710185881000900001400071354502d0b1600084104071a0245a0f4a010442074010303208461581c1e40c10046460b0480841c1c2171008900030201191200c040001e002d0f030694130034143c20304900e030044100307001d078012580b081010504244680c202130414015640e440310b00c40310085201229103059459503502a04151100d03040064001c5102c240700f002003150003500c100c5000100c03a4000744487d14010350100508 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 622296052 1250 622294802 622294901
    0x1103040219030b07020705150c0322080a030c0b150306180f15071205040519050a0213060504140c040b07080c060f1e0601020703032303040b040204 65
    0x41c0d04054140c0307000956800100f01d2602c0c145880040e40e955000e1254074800c2150204060002590005980c41e40411800960600d00c05007400580d205d044000a4100d200074040002c42e1441000340c0300025000341c48462040c06030f41416100000000c100d2030071003159840d030b041242c40000d440c6500078039603190301d0306c41c802100000f400c0000c1c1e07181085052080800146109500b00782250083c40f4a8030303002e20010500903114103071003040f900600b283e044800c140d892a01d14001010b049407080d016070f60f04014640c002241510300f40d502203840d44c1d81d40c0007406641014800c05010354014101d09420b450702006590540c032a601802014090100e501d070304203c00c48007924250032000c01505d0f8149040e0491030030410003100c0b90300d101c5042c440c00b120705e00c02c1d1011203030245c401a0b000e400344c0d0b4103540382070326010b06405000c5040340c0d14204425840e00c1c0c0300042c40c0128807817004030f401030400e401000f0a580641001003440100001e007807400ca81c43e140243c0540b14019500b11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 622297302 1250 622296052 622296079
    0xf0e0421050904020f040602010501080604033e0f060703060b0304020f0a030206030117010b061921060e06030d140706051902030f0a050f0c1c020d060f03050f0111030402 75
    0x540c1401107041e00c940040c000300e4a0604c05c018540900b00b074520940c02004540e90350401d10703503035601c25100540415950b4101c0b041120031103210348081c00310f03c014500f40f00c04d206207207003055440003020456504104501744030b401040c052190040e50741d1406202280c2002142030062001800c000d11030100f501c0d11b40f41a8a5541c2d070500215002880c6036120b40e51845000120401c4207840001c41d403a020f00c00e45c60741384c80c505031038400104207022100d00320049001c1d500321059500301100328118206104a8402d030740220005049040c0c03840c80c1900701030b0245440c00315400800780612420100c41c40840000d8815580f205130402c401103000d17161108500702448403005a040514000801c0181149051410fa40100e250070010040d40d52801e080e5270b1211800c0c1d90642003100300700140301c40384161908100707004080b10310040c913041c0002c0901003140c10544c0031a00042c1058010001d102c001d100380861220b244009201c61031403110f08402d00c0c44000e00007881741e9800321703109 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 622298552 1250 622297302 622297307
    0x100b030a090c030507030b0109090804150e030d110f0d080705030705040e270a05031e040905180610060e2215050a050103060b0f1b060a060f0e0421 65
    0x12111250400e50541d000b9440e400c00d90b0b00c405090005891141d1601e0000882900314404d001c0356503009540141814103151120311502c4140310b010341080b030040d600000c0d07994240404e00b500416610351482c000003802c2d0203428950440c05100c0c441e00f0100e000012143c10105041d030000161500039680da841402c2962203000b580c0101d60403018400801c5104c5144003070f407550b42c590082c6a070445900c42c441d5079644660100c1c00a025400502407242d40c1402d01f2403820010324032100c814101034865040e00200e038070403200354000340500101406403100c00e021142e0004554507440c0310340350508101174144081d021a00d8069078441c450b008540024509090746c10f001007c09001ca050310380c2040000070040d000e030a104912626000881e5802440b0f448202c44a102000d030610f4480c0c144180c0617003001c1c14014070442e4601e44040107070000d108040c4070b080c10f0003000892a00301041198600d120740c0011501980724420302c030100d61940794011003003488100082e00022840380c00c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 622299802 1250 622298552 622298561
    0x20a08010c0504090b030c010c24110307030b0109080a0305160b2401050a02060a15170a050c04050f130303021603032304032c10030b0102070608100b030a 68
    0x544055181c0444400c8203540300008008a8074040d109120000c0480201a00c4402d540c42c1203002c265a1080c00c030000317100024014400651921601c02e02101d144640d00ba60076006921800c2c0400100708819140c040c030486ca940d6000b031a10344425418510b006540380420603000d000d211011030841c40c1c01c240200140c45075a80402c0702003840c242144c01910a564901c103000e203c00030540d9890301544031780c055a0030100182e0083c0680e45801c5155002010310710079030105a6024000031a00c01c031101d1112054940940090122140501b48030303041c41c0006946d64852820441030055003105070065580000320498a0ba81e901601d280c160000c3c400d041e0781200031002001c0c1e6009150309544200303201d06d1035550f85030301004004410a11031104440050114a0301c860301569412802c800c0030940f0740e03440307000203200300000000343d6510543c2c1500c40025240c00300c00e035895234188008001010f550400c40b016050841c114071052031304c0d018680f605640400050961982e5802 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 622301052 1250 622299802 622299809
    0x8030f040f06020a020109020f04022a030c01110d0509061015021c0e01080c0903120a03060e01091a0f010807180b0316170106021005040201210204060e011107030609020a 75
    0x10115070b101d813860070180c00307804040c0c4181c0c829100e01011145508090003150805107840c0700151900b02a40c6000e510502020f0300c80020744820b010300889840d0910680d010400c0c00d810703141d140c2c0c0f034241404056810081c0b11403610380022b028843e4000d0308010748003d0b90303454150a0540580080200c0c5400d002ca540f81004515a140340ca044540220b01ea000006003a030301e00b0501d59030481c2d000000e01c42d5041c00d581580c0103d442c000710700310070700180414074202d180c0031403030582c3c6681d03811054100380c0281203602e681c0d005001d01d020162440d01d2803500706859244002c003a84001030442c01d4000c1000050013504c0515901d01000009080d02a141c0558440c1d120b040c040f1580341c50b5880e091100c004200f1904100b5001c11032203550307034100c0e5201d500800381181c0c4945610003400740500100d05005501900126a6400b00710300d80807444000001170700c0d1071504c3c1c030003000c01038034002e05070600001c6002c59261200102c5d8600a81e600004040348039445d07172012a20310100c550 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 622302158 1106 622301052 622301063
    0x403050702060c1203070e03010902010e060313051b03010e06010315110903011b0f030b0a030b09070b0a0302030105040606090e0403081b0d0902090a0908030f040f 72
    0x50040c18080d201511041c282590005441e03e800c00c0b0320081c0c10080008401c00629903800340c03068940d5103046000f4014030318680c001070440c00e000700707440c0e000c4e8200100007402183d0590304081215800400c48007030307500102c032903552522602c141a209500303003002c0000000d8000360b80c6068a402c1141d0000d810850328001004103855120303c0100350302030007250495502031050440e0001e0183d0300030340c0480c9444008100b074014403598400c0c9480c00c0d050052584501e01c03040305996024000d0615a1203610f2010703d020110b03071107400580c10015030440000c0d810340140d4105c0304203440030706c400d9484480941d03072741c030300390040700aaa0940c1c00007901082c030814403ea0402d40c1c40c00c00c059541c1c0d0241035a4519484105100001ea48a2007101d0850805400301c90b4850141d91b8100418103145d500d0398042c1c0f001410400d1480c06110200d001d0095282c01d4419456001 = true := by decide +kernel

theorem cover : BRFrame.Cov 622122302 622302158 := by
  have h0 := BRFrame.cov_init 622122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 622122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 622122302 ≤ n) (h2 : n < 622302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
