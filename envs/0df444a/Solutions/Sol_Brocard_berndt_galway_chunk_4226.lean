-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4226
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:55:54.223724+00:00
-- url     : https://prove2.me/submissions/2194d380-fc33-41e4-9553-fb2f46577411

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 759892086 ≤ n < 760071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 759893336 1250 759892086 759892121
    0x60f0b040e18011a1c05070b0708091009170d0210110d0e0309040b04150306050709080601120c081b012316020307060c080d0c0c02060a09080106060201 67
    0x70041c01010310301c8160014440a000c0200d466070348a040d00311103003a192074614440780c442100061901d61082c03101c45101c26848030004000d551801d840d42d03610301400d88003502c0400c00c0700512440f030742542c200078406000400945440d610141071030000344106484280091038080701c0c2c3d60003040144104403da001840301820248202028048000c0085d01003a01403001c0300e14400749001d50701041d4044005540d0781e080380c0d0213000680d00700c941030768061818254448114a0190304440480360002000610b50b01c4070b580495903004540c0c0302e205984100000454052205c0352103203401d5201e07a08000115613035a10454a07041d41407100b099411450940701d0195010309840c0390701c84c049a030a50482030551488416682001510850710543c002c0780c0c4085003000c2200e00c019054600301008a24159a6035221501c10a514480e10035240c1c0d6a60368100d014096401d00300d54018800c030745070450340f03000902d07900d0170b4803400620750300300000020120300611413954a0050381999 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 759894586 1250 759893336 759893339
    0x80609070b0c24180d1e050903011d0c01020f060c03040309080307060204080105061c26131502030f030c16021003020909011a0d0207080c0109080d051e060d03020c040e10060f0b04 79
    0x72102140501d4500c6c418030034100001d405036642031098111209051b240004400e000703990462414060316030490641d842420000010540000d84650240e041900d04c0e58a50340c9150881309108241d000041c144400308010041244c240c01420640b00c80500070822959580f0030000c1104000030b4407441c0d02401c500e80b001181d205c460b2480c40e00c10052030194103880300d062410b51603010a2034001e400180803014440080d002c10460288480da1004509020300c3e40a80030381e5102c0076201022503c8009a496a401105000d1249090700142104455076000384090065401b411450744078908080c0089103c480304030b028507265101c0f6451609021844645000940c411003058417460010b0100602e4081e09008030702c1c4483c810861a80c580c0d20155409041e035101801c00c40f841d0300d00301a003000b03038007030382e44010791203401189c0a80b03002d442820b084c0e080c104004442500141440c40184001d03000060402105444e01001c100b482c0d42c07052000d03270204207400b80c00b4401404100 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 759895836 1250 759894586 759894617
    0x7080c0703030506011e170a0c080106180302030d0c2f0d0807140304030c060207060f030f180c1a120f04020118080703060501080609070b0c24180d 65
    0xe1a80810103042020b41e4031a24100d011070034100c50341b5500040e61071048075040301c4440a8098205410039030034030121500c1c07440600650f0b0305015241c204031840c0e07462400030541c001194005c64001d81070790512a95051b0003090f003160b5170001d50b03818005194541d414010b02c044034001803d07100241c0305004403a000c200150f103a4503010358040700c2c10310042d0003041e070181240c00503c0301c3c18004d40d9a0361461400c0340b0314010540c030500564100c2202002210b400840007100000b01e4640021850701040001009010703060503842c2c3d00c03485585403820807400c500d240b010743e01207241400307504855030f49204052151a03002c106851131280070408030050401c00c1a009441410304112900343ca03d5102c1000a0551101000340d0180c4001c00511110344207203409001d03c2d4001d000c091400c4086a5613400c3d50b4400c0040a15001503c40541d180034070040c0b41c00482c03a901c00b4600c0368203602c0780391141c074203460840c41300c148201060403903503001130307206050400d548504444c2c130805407 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 759897086 1250 759895836 759895841
    0xf150307050405281a03070f05011407050316060605030a15020c1912030506121906060b040f05030d03090201120b0117040f03020d2c1912050607080c070303 69
    0xe01c0c0703101150070700a400b0700011340707100c0300210b11880c4040041c41d9400380a4001403044d2820005001c3e400c07116080c800394040c00d4910069034003c0c20000701da841d00c080301c1242c920940c41d014100d8000807403071000c414580e202c000341c494098801480346a4071541055126800050001d10380c10980003606031800d11a0060503445a16006482c1040301c60440010301c00300e68a81100c0c0340d20101340c2c103490750b0f402d840b0b02d40d041a010360305040704030030b6683d074035680f409010f0444030f00f89075102160040125903000316015041200e00d0765143ca5079000812008031050050034840c0c052096010803040c86485451742035501652205100341018440600a1000300d443c241004040070702d0a110128019075a800b9611038002c182d533101e000c2c1402400c110004102c00304000f000382804904040401d118002480d5540103801800c0440d000030765611030f030300b6025800081104000488510500d03651040358021000e8032000c0c2d4842008994a41301218440c039510804d10891002c80e00c81d5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 759898336 1250 759897086 759897091
    0x10504060f06140702040219080a11030106030b030f010c0e040e1506060a1101090c0e10151107031a07020d0c1e02030a150b100201022106060d0507080f150307050405 73
    0x306a800c2c41e00c104c58011400340d0b8403040c201d001c800d00d1000f1a0780e0750303a4050032007a44801e19107410401c804450600e018203109c10b10400e01007646659000c1c1055409010171290310009900802070f0811121004e0a120011140240308500d020005e80402c840410002125540422071200c075a9802040058a03000340c2c842e60200b000d040c9422003044824810710000500401e8506040c5107042c140034850344004000d00400c8075001003c215030a400b62040303071218003904210038191010340700c1c1e0745010700d6644080c0c900a0405243d0001c032036400070140c0240c0c0290b081d2030840c21840d00540d14031340c05500c0203005007030818401c2c20900440c0110804140700405880c03210704242ca40001203030700742c0c246600141c1da480e11003e407071030a60b61a01c0001054002541042c00d401d0520994a24803039000601844090010380c03e0780e2100200e50503003084000070002402d103807800625855040320920100105c0c0000720304410401045000c007110014010071b00f45050006110180001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 759899586 1250 759898336 759898367
    0xe0403110f01060608011a090f130e011a120609031c0f020d0c0912080301030f022b110117160306120b06040f06031a060117010909020108010504060f06 67
    0x1d101c401e42100c1c03401c2c010440284050366883e441941000001418100000da40c60b1200108110655060b02c032059030800e07002c0704aa01040f00e001c220f0120b0064442500c88180c607500c0e01406113044032000c01c0802d00d07840d06841040285921f00340040d9201c805441c6000c0030781c400d12103080708410380f400103800720351042d00205092686482031000e90b001359040314034060711122001c00081d40319a102c4020b040c030400403c40404141c440840b280700600000d03001c8903035210b406055489402c4030100d003148185900c081c2d0460b41d022344404410101d01203401c01d4403002c0b2062258418001c01c51a662504401d050645403058000e55142548000c0014944c590800056502080703803801082c40c000d8070200c0c4d19181010800003124010030740504001d1410382d00340023069221605681c4a1f0000001040d030f51500c81c0180d03000c61502503007407451441d802c0080f480354070a402ca0305101c0c0c0f00781c0344c5d9007183e40c031941000140e800d00d0003070110780302502c401080340501ca0001c039070302000d8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 759900836 1250 759899586 759899593
    0x5281e032a06020606040e1618090f0305031005060414060310050604060210051014060a020304030f060e060f071b1703070302120901020403030518120601230a0e040311 74
    0x6055104101c0032101d5070250001d6041a820000399042c2401104011002ca1024001843c1941e104140c84c100324051503031000189a0711300c00500e8540d119410407900469219030801d40b84c85c3c020041d03441200c0000300e42c40303e15000207081c1805020b6506850424185041c91400c040501011b900f00900310801d880380c0880004071a1100da00501c0980040d174090056501480522402d985000e040e608501d29002010030030306580d5030b1503280a440032601345a0307940c5a6401280340d40542d401c080c0119030340014080030009076911402c0e80c410824295501541d8a0be1400c07804a41140c0c0c20000c100b41d50707000000142c041c1801c45860344902568660000428902d038030325041202c190380401d600245010003240d0010081b940218038100039407801b401c540d0020091b00610b4550140300345104400310f01503072100740c492920b400000440700d0542e51489800c1317030529038408031300d04603094049099a03420b20040c2070080d03c14500302c0e601030f41c545a40850310301c050001c907400c043c00f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 759902086 1250 759900836 759900893
    0x3021203042f0411090a050d0503031605040b0309070f0b03040f120309050118030311190302030709091a010f180e04020f0306090d121a0405090705281e03 68
    0x583d188110803407403042100c416103a80024082c00321283c50742d04a1381c4a03495111007640040d0001045a40c4062104a0f1102901c0e4460054030103000359000600d4110000c010807122034800036032101100e05568115101695a039a800f1103840142c5010f0726441221813503401280e9071a21901103200c180c540080d00c6a02c685035942107850511422071601c18000c6050107140e0f141c09407114820340c210f00545010520f003030100d04413910300c030950709164011000034001c6018a15150051203224401d02c040c09c1030040d2510304d07048481010340030409045658442da40f1800708080c070141f0103045158441e05140c1503c440c1400104201c5c4e02005e5190002e9240d00c0520206001d0340d020710041c00d040c20210000303080c0c4281003e4460b0740c0e618080b01c541d0b0003018502c41c3c0003168000d880015403903c44089031410f00040d5042646c004103142103014440388040c590300d2082e40340c60564014151510000203581d8840d029544040050090510100b10303e20741d40205000c1042105001e00d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 759903336 1250 759902086 759902089
    0x140d050a1e110706031a010306150f02070510030905100e03040905131b0e090a020105120603071715090f1c030204210201031a1513031e03021203042f 66
    0xb025900210002a00c400010f800f2409401b4811080300c02400e040c0075a44c200756008240f012005103a27402c00690f007050000d4103000340000c0010f0039015101d10100d041e19400900509205002102d9602c034000141541c903259206001c0c06078030500103180780c01e203400c1241014000181a0003512a6000030b050001010340041b294424055040301403070743d26240307104001103c010002c00c0540c01102c182d1340180c3c0d000041301c0c4240740e040b21440c000d483d0980860314120341c6810080076049106480c0074100000a11003070002011108100c0540d5036031980f5807a03203805240040c071640404090a403184081c6802c980000c6e1600d001401c01d41c2e0780c04141100703024020484411036407031440000b0355a0500490305041420542c02003000151004144051072140003101580300200f00e404802280002243c011134000d5041c451045601d510048201c05200c07045000d407003800341c3e62500084410903284515009500c150071116468040d0030141c50f1140c840201c1c00da445000e02c6e06 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 759904586 1250 759903336 759903343
    0xa0b01151e0e0319020a0509090102090301050702030316020a020d0602160606060804060f290102100911030c0d03020c100e03150105090901020723010612140d050a1e11 74
    0x805100303640e0381508200100c24107003440300124520a121341000600005611021b4140003101c03c161039003401a95110820740c02401042200c0f941942003400380103000383c1c000701850040201c1580500c5012880c0002ea98841d14420700a410411207281080802c071a980603181081c40307020024203001b45c0380d80b440b00f1100071360401c0012504800070f00081c4100d83c0b2540c0c0c0380029040040120f18880101d0420050118000101e00b0643c8040c0c61441e03442885402d07015034440c4000e0016840074541944030f500d840d064103000344240117543e222450809034081090b50582c02401d9a00c2c80e0720280060030000007040418422107441d1420181c904015008001000d070142c0c0145505001c10484203007406000c1c4001030380140610000310386c200e4200500a91140c80001d00710070180c6056000d4002588100c00064400005500340b00e4024802e818030043e000a4130055948072005440300d02451400360000340c24020b80c004c083c10500c808800000003170401d801c0d203c40301c2508514 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 759905836 1250 759904586 759904637
    0x30604050f010501060e0d11030c04060801021804020f160f0b0f09070504020913091e0305190c120c020a030605070905010905271b030403080f090a0b0115 68
    0x440e0362088140c48201c00003885843d015106900c2d08100755200038001a155070f0740e070320020b0310622016140038415071302009071200404018000784076155035031a0260007074100d24051721454005041c28000d0745010302c202c81c5c079000f108004908008801209001c40f80040508540d034803914903000d004110342c0e50689100703110060300c10317545107000614035041c4803080d03100d980a203005000700c3ca10fa5582a074072101e05055918001149042c17800e00e03504180e03060040c4502d10550a65070401c0c07551100040c000011002089290301e02c00c1401140e0400e9013050241014a0354517516813120301c16400c0080715800140005801516915144215441030700c4c50341c0441d061103001c00072940c12407080401404101ca65200443c040f03403411451415801000400c01142400540001240d484100d030010300e0b42134a43d1240b0700707441d0103000c0800990f840d5070203051490000d0900e01000519503c1981d10405410300c50b40b0300074885072210280c4080368103021b5081c45d007407900d40e5100c5c1d0002 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 759907086 1250 759905836 759905843
    0x60607080c19060c020d0c0b0c090301180326040b06040903020309040e010506181009020306031009152703050319050c070204050f0106140d060e0f041101030b01022802030604 77
    0x1d081c0001c0c0b4001c2c0c50f20300906c00742d80900c046010104013044001d894158030041e0107a18a035a83c8500e80045d005140040c0710b0104140085840d0f0241079000f030324009007140b0292000c40031051030b01204852881100e000301210141c2000441500f0705030015103100d8440d0048030308200e40b00300050180c1d0900485152240c3d03441b01001481d2404614030018444001c118145030700300310403041c4110700b460080c01072098001020a0031620200100481101d080d00b0400c480d10a62801c1d0b12001031517500e0414090800c9002113680b44404a100c10091030785035109142003455a0681d03498000901610203a0750340c901c4202150707094058648a002c96800e1035690b4912441080300711407010f0410590070001000500181d03800c4038490303184c0c5040030641504c0d0503103890241c1c00b4204640007203120582a00070701148401c900401800b4500c519450a4040300300c000440443c3c5910407040d0050b070010780b403550750303180400007201000302c007111032070101c00140c01107803500105a4044 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 759908336 1250 759907086 759907091
    0x306150e190b0f130e0c0603010320011d0d140a050a1e051f09080c100f0219030216061b09051804031d0a1202011403060607080c1906 59
    0x36840d01d4081c402d90809420440308200c00d002c040c40403039007100030020103840155450707411225000080128003500c0d40700a008695030340c0c50385044190012400e2100c01d03000b808400403501c941c001d42e4282c00503c2c007040449001c9018038100207014007008816640f803094921a850302e000b080c010903100e5030044000302040c0f0031900e4698017400600300d0846801c880104010001080031aa10700c0241c11302c88182d4404c0303004003542d4010035040d20002c041020000e000000e1000c04107040c0b800424130081000003d440036130000580c49011906000c2e236000045192102c0c0c0240e02609100801c803000f004480740c0c070340e11350080307030114542c841e8070003041200c040503541d00076a074070090041500e180254030008441c001c81084080c10050606c4109002000313100c0030100c2100c001c080043c0018000d0340d0350b180008000ca100d04059000820b040041011907a03c0300c100c0b07000c3d000240121b071170000a034542c13070515000003248017024000e2100000b0001001e446210b103481c09107500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 759909586 1250 759908336 759908371
    0x1519060306020f040f1e060819061d0708070e040c0c06020d0203100906080a03110f0601060f0906080603030304031407050a1b06020c03060708090109140f070b03100306150e 76
    0x72501e041b58014400710900854545480d14240c0d101c00c110350160030801b0b01c41d01c0b00c09408000342c42008a950180e444c000c00041c1010046004101c101c061029102c016140e410080f1000c900c215400c0740800e00106039810f031420690300c103002c0b2003203910307007804c00d100c603641ca142c10b0368040c0d00307000042600031007806191340340c4007007000061862090800c2802e1070b205109840d525501000fa003884054806000e4101d420320404101801903c2034846540c0c480d840504400c42a400f9000010142c4d20040342c010300800c2c14034040c40cae0040040d400c50351103960440e2241459950010381e0081401440d0014504008500e09030384118103011161700044010120000298000b004650150708804c80e940ca000c11010f40115141c60255115902d500c05a405881940e20040c90919481485203c6880215020505450034415180d26654030381c24540940000d60707250400c0085600e0810015007d984010480b081c1210b03290002da50300c03107900e40101c108445c0d5100a0629440 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 759910836 1250 759909586 759909599
    0x30b010311040e0d0e09060a0306141602030c0619020c0d0504060f090e0711031306180f08060a0906140103080909010821160203120a030e1519060306020f04 69
    0x2801141c3e028032004080c885580400140078000d144d8000d401035210b100491280d0326000700080246400900500911034448403400032070720101c90030210079003208050f89240f8404811207040d13440460007040c194694146080d251030010040e42d04882e4204191a10b1800c2030000710f04991468039115100ca14010000e001030007031040e0082008505030051041141d64002240c01c884289000081450807140c0f140c5140300d10706450403981e4180c400080e1041e44461039030340503034421821034001941d072610034a80d402607000c0c455694011000084a50b8850743c06407100343c0c00fa40001c50640a420985041d0714000c0c2c00a44294a0005a4041c0c0d4100481460b0041103520010214030318003800d5400b5036100c003082c05180880c00030b0120110106100101003642d0001e007500d2503e600d80c8020b403265402204141d0200b8280301c1e400c00802e03400f0507141c50b180d94200954105917907500121800035908107000003e20354442c0c011011484a2015140c0200800549940e031805d010 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 759912086 1250 759910836 759910841
    0x20703030207052403060325090b040203040302120f120f18060105060a0c020111070e0f0f0105030a110d0b0103050313081903080723030403090914160504030b01031104 74
    0x1040740340228480c1c150790250491681000031340c030407009100d5449440d807000090408000d030b008402990386c2528000003e002c414401002ca400e0003008004410240c81440306038082101c002d030158006940400368a0604002054903c45081d03005140462045c030740c0c0c41280040d280e0a00c0e060640d01004031501c400329003040d0003103000c4010b0040e0341c0b6101c0050603d2040d17092000820004040d0541164002c50b42002c8112280040d140c034140c1341d450b4003405007812121050b1038450b9201180389510182401070507220054064400d4525988540140f491859100c1703801100401c120f0000c6454416228065440340c8041c0d42c0d030b4110b42410110060003600b2501041e08034a001c0c84c15500d400b28100d0281c0c0d8136060442c80d0b645e40c000700b520800c900c00146041001d100d140c402d2035511990085110350710a80300c04440603180e141d20030072a0003503028005c1111a0a004c50142c5003030190050b00e200180c90f10a10f0b26840e5176413a400e100083e80101c0742c020b0700c000400c0c030615090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 759913336 1250 759912086 759912089
    0x90f090b1302031513020d02030a090215120112080c0d0f03050a1109040f1e14011d04150605060a09030501050108061603111902100501091802040b060910020703030207 74
    0x40c1c01d50039401d0000010f0803c0d40c0d06400303540310325040701210602e10301c190169035642280d0700c421500c078600700c3c91442c003625180c24203c1c482c0303c1000c4085502403422055451031411015041466801c10b03200042c045110031007a20000300c113101c00c0150b030200708400700508413a42c0d80d1502c1c0d85a03c00c0b0207020b03900083d21200c2c025041558142d00240c2840c203454041604840c049001c4450484050083c04031070b51045c0c58603907001c004188400c9640150810041108243d052682e07101c14054414148144d9000780c695400041400310b02210312510964a0101e40040c1b210350300c0d00000d071168040c40f00f500115002c940d040052207800c0c4542c50042441d0700291000b45800b540d03203154004291000001c0c103640e00101e0540795407907016204c1c1401c4015592150403c600720103561018600c00c400800c0382841c0000c280c410660007101303c0807078641d0103410341d00102d5003000003406400c0d03185500302c401400403045590b82c01d078401c6198100e40d00035003402821810003e04004c4107 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 759914586 1250 759913336 759913369
    0x1b210f0905042021131209060801121502181302180123070c0311030c0a0b1806070b190c050702090601200106080f07050604060c03090f090b 62
    0x6100340d242c201c100d07400e41c0003040751540c8201503894035a0b010b5444c4d081021940100000204000c001094814180a81040c0d02407000300180c061840700c119100d403242d0084800281c19600100907594507100350030030051080d20f0000903250504070510403600a000c4c0011b500d00e00401c0b04400d8100004844c11910081350207501d441d45c011070070700322166000501410072503000c02010109524040415107104005001d990301e01e86420320182c814001e000603070310310300001c0000380a031800080071861100d000c0c1c00001d1709450080341c404143c00414000c400580d4600300d044642d0359085c000c00c5124861701d1051540e0401400009908607401c2000c40d856103030540070a900e0f42c0290559464582c110344200d1a5501c000048880300c1044599209072114030900d4001c0c1001900545c066509503012607401c1c903c1c0710441c039034034445403084035003100041100f170103400e100700d902c1c0180c40d01a04024055503500e40781110f0380b41d469070010550659656240c1e01d5072508410101c4001007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 759915836 1250 759914586 759914591
    0x201140d1514040902060921060a0c2a030302030a11190f0c0c030f0204020c01090b040201030b0f060714120c0303040c061d010c0510060e190204061b210f090504 71
    0x4c1d95804074071b00b80306410155200d0f503007401c026142c08214280021050300b1850a0782c60728106140b1200c00b0b00b00404075140802c605940845e0100300d4108102c842c544070500020024421781c0f0b0030340080d4009800d54919540310300100800220510040a90401d10606081d24201c050b000400c00b00055004108111241c402c3e140403489800601e400e403900421114417100c07580c4002130003842024810700c02542800000003c2c0f00b840400f4503c214002c1c3c0702444081e2100e8100040c22107a00c0683d50b012106004140201e14030403502501c0116a1040f990039216507580d40041d030f044400360700a15800041040108140081e6100050640742030007c628401081030f08102c001d40101139041001c81ca095074140318080100550010380040100404c5881d0040b6900428080b02c090303200307a00b07041404012025501c00c6404840c2c865641e50b03d11101c40c030001c031003010700d0075040e55020b400242c9071010346507100b4480d9a820841d11185495540c040000c0d160314541e40c84036101d9807 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 759917086 1250 759915836 759915851
    0x9080d030203010f170c0a0311040b04511503020414100e06030115200a140c0310050601030c020f1b0105040b0a0903031206030c030201140d151404 65
    0x32100303480041550700c1d0a00d1044220703005e01c040c520704169600d8541c0e000c1c5940310008140146101040d843c0728040d2024400d4040440c280019500744480c407101000f09420000381c00c12201c9416803203001c4403120800e40300c0c80004842103110294141c501281d4800740108070001a80c2c8110228a0290078254103003460030910005c00e03021100440d00501c103242e41c460001c0c4c410740362840244001850b0717580785d507107030551101c44800305802c01001c1200c81902d000380003818020f007000610300d000200f1042049a443c01c440308100a00400c42d0310070703190309180c0d0355400c0c022000500c1c041c1400107203501d04440010b0550b00d194043e00c0554004016460024401081382032900004002e104202c80d850401207809214552040c01640004038003105403542c0180c4e1002101d00a030b9483c0e10360740ea130550400c12101c1c6440020070400c0c01d60030400065004129800200300c12103086e6007000a0080f0705810745080c081304d01480030500000748203181041182031010103059400300000c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 759918336 1250 759917086 759917099
    0x14010e0103030801091a040606180503010212181903030c08070804020a09180611030402010221030f0a09140c1c0c0b2208012a050306010f12090309080d03020301 71
    0x1483c0c10701500c3c2d401a1241c0106030b0f442c070440080d0340c0d103031006070081040650326a8002c00c10880d01c843d803014024003c0001825180500070707101314103d0180301d848242c403034485024551403c916003041301d003c0e48070003c10505100301c010b110325010351070215203001d140c68000d0000b44010240c400780f005450a100c0561201200d540039614a911f0004880c140001400480031866200401e41d50802c0c05c0e001c0da81807040d010310302941c800e80860700101d5192440c1d925042c02e00880c3c2060344001c3c000a008a000511503940143d0040e50006450754103032106120684c86400b2140c4075446808142880d04008080700c2006c44400c03c1403074240c0541d5581c081c088254450798000410108140c500c80b5511080d0701c0c0e04201d04070301000c025985480881c080e1082d003d10420b1200c00381e440c2c0c000e41584801c0c1d003500c0b03607140d5541441d568a910055468610700c00c0d44008201d54850480c280b43c01c1d41c030941803101d001e911290590707454204080d02c0c00e81154421001c150041c00104510b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 759919586 1250 759918336 759918347
    0x6030f0406051e1911070302210304080d0b0402092e050a09290703020d080a180204020a0306090c0512060409020307032301022a1b060d090503040914010e010303 71
    0x11a62280c88161000000383c40000501134082c4100700c59172002480c0c608054000401c04101104e46950f048070020b0592842e609000c11600034101e0074041100c2000005554000020301c40001e000604014403240446c800300b001c03540c8880361079488120749c001e11010500c12001441d041c40c181e03203042c1069400400107141480743e0f120900102d001e10004904c4400d031501c01c15501c40403640c60342c04504000b90766009981140010480d0740c400b02d142c12115009a000e0796200d1600600c030313160300f5824000290f1142454108066559030042072050890040702d840941e62394416403141000a4604c0316a80060441445a4a0203c5c84001a100440c440c401c0b2908240300030400b44100e80c981ca60319542d19a06101c0e94030019848600854041c4140607410891041b40140c4201b03901d11a60340c96076011004003107a90803620441da1802a00424240d604c00101151442d901d5403510700d180c0081e0088183d207a151042d10642825801169004007505030010300e1039455900c010b001c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 759920836 1250 759919586 759919591
    0x120a0926190201021603022a01140d090c03050f0c040501050f040507170f01030c0e2a04050603010b300708070c02030f0c10020f1b0f06030f0406051e 66
    0x49a221540684818003c4d41910814180d20603c2504e041c0035240c002c0d19140e995143e0303040e40d08403003480c041c4000340c04441584000103840b040651610392500e00901c0e003192030441000b5032142401c100080d925480840118441c900030700c00b056900000500f84440c4001c56401140380000401440c0e54041c3c06514000303081d0b60025868942c6d14088450703c40ca02041c0c54840c1b101030601c058065500c1c07109040340e0050903190041a250004000e070003805650380c484041d81000d404080382c1c0c04c01c4c100c3c21480407000c092480c0a50b40d2004c100160400d91040c02e00c02404a811004030045409441030404421003078451640e0a80010000580241400081090400010301e041d030040442c814650303002001c5902e010800643c06554480018406000b0200604240d81d20303800029400f600039a654041c0c08141c50105140c0c002c11141003c099004103d00010340d8140c43c0c0b0001140106501d8001e0070780392a0604050056a0707000d054902140b181c40320841000710104240394 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 759922086 1250 759920836 759920857
    0xa20030a080c0c06130504110f030a0506060c01240b160b04020105070c08010906112704150e090c0a0510030b0a0803030a09020f1503071103120a0926 66
    0x782c407104280b008070300d00000b040c40c03950854000180d420307100388100450000c41c0c6045406101d401481c00314144030f401040c000e590300030360900200e14020fa0540244c3e030302c0301001d80600c0c2406911005070313003500c40b0b125440042c005d6001160f61507582d6404040058085000424581182031245821802003400003512820300e00303020400310b81c40345003156a07440e04000010f2940380c031040c000b4003c3c19440411074040b072604030008140118103054a852040301000300701c0741c145080014900b2242c08081c0355000c0d6640c0301c10103008100c07a610340702030200c08110703a0315840d041c105c5a00c0d2001c140119407240118900821150792015041c06a4444914000c51001c44d10300100c1c40700b44043e00005c0c1d1500012042020740941039021302c807442d000700d0302519400d51070070034030901286141c101085020108001070806024244400345e07004441d040701d00d8000c1e83c80c0c000b11200300555000014503100d903c15030501502541e581d40c050f2a0300c807100182070300202c040341c2c01e101e2900140b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 759923336 1250 759922086 759922103
    0x13080f040e1503032506020d06090f060b09040e010e01180302190519060213062601050a260f0d200a0615090204030605040506010f08030f090a15020a20030a 69
    0xf41c000100c0300d80705591240d02406c290b4441c400d00e200d50018100600074135131a140303043c0414402c41d60900a107401ca80381c10b40d00d42d01c1c044d45e501c00c1c000034103801055002eaa640f11992a844400244190504007a101041940000d00c501c3c0c024200354071901210302c40c4141243c00310215001040180301502d804002130791500307140c50020041d008881103900150000c0c80e0029081e40c21041652441d00c0400010020130746003400c06c41c8545085c01010340145808500380500e0410340c08043c0c900c0350389410345081418440e8028079020449421700215008800c8600b03501c1e400c2100f401c4140e036100305c816103186480c018590384406210014003102e440e00060f00c0e400d00c2d0b006005024202103042555959224101a0080c00041c0c134103d602d485001e0002480e04040c40c0c80006130b5280d4400703180740030900891240301ea006600019072000404c100000d051100c042a95042c14142d005404107200ca0705040900c16001c91840d40300781d07a5146601c3d0940c0d4042400030722241d008840 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 759924586 1250 759923336 759923377
    0x803040c0f054504060f0b040603050307020904030c0b0108100507090602060f06130c020a1415010b13120308150316091509050709080105060604031a13080f040e150303 74
    0xc0c0c3d803980541c0c038540c10401204400d11041c02080d4021603400403030b800051201d0010803007440111081303880094080d030010300550f00103151904503a60818024903100700b05940b9511030120041003a4000015030b0301c804401e8556020500809502c1880c5040c442e0145190040107034507001e004041d540355054580008489585002c4d40c54084650f0150411101a0303014002e90765400c031007010741300285400408868100f0018001c900582083c00c000003d900e040c0b0b010040d5045095058012070080c5000b00d8008001c2e1007a52081d03020380e40d2841ca5060031580039600a021050850103500300848032102425840004e8003102c0941c2000201980e0180005000c0d41c0c0d5a080000c1c1981071106220b40c081e4803014880c151072004008205c0b6403101c44c00c0015038402da2000610603400407091b8920a8190100a42e2140100d45403a4107031425595900c0c0e075a011081c0241c20700000300c0c00b44286012030040560050b8181050100c4404100000359a4000c00c011201d8000d4213806 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 759925836 1250 759924586 759924679
    0x6061409040915180506250c05010f0207060603020906040908160201030b03010e0d090e0f0a090317010b0408100b33070c032f011b0803040c0f05 64
    0x1100f0210860441000040d0910801620383d50450700e095441c0d1040902144844c0004c080046903901441054801001050001e03501402c1e113401c10703601950b84502252000c10503000801041e40f161b0300008145043d441000741e00e10029003024005d52800801e103000840d62000c80d803000d08241801d9a1308540c03440124090140d012072503802d54200340c0750180d007003000182420040b60780d07220514803944540c10260210021035246140c0c400050215900a44552284c00c500e4000d1501242e818110038000b444064203a00004820340c0c00202008502000c1c404030040c0c074402d1005200c104e42010000300b002c2190001480e2000703000b40c01010b51400b00b08202c0e8100c4252000c00e8644100e41081c04507003007144030543d404001c01d401998520107581c1000641c020b0740324000500d108040044034002891054003681c041c0041454000c1000040958850752061180c413810030b06142c44409440100c0d17004600489481403172001c4a031501b03108074001210600020100501c070340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 759927086 1250 759925836 759925853
    0x21050307080a032711210102030714190e01142b0b0603010306270302011527150902040f03060c0504050607060b1f020d0207050f060703140c070605040306060614090409 74
    0x108290444111b420200c91115010f4019501c180c0140e143c40c83c11170000c460342c80311031040200c1904030b800f40314100d9800ea0701500159480b1801071500701a518206005400950310580c0d82098440344080c01d070031044507410110122040301301c0e007480341424540100711580410f00000700204d0f01c509001c0500354a0110008071042c602880215140c0309080181c020303d40c084500803003c4102401180404c2d14022009050400c1c01d4000c0f240e543c100060303001030201070b000c00d2840c00c154200040c02292800503001825020146034600352461510504917070b20021008240300081c4020083ca07540c12341610140c6400c894086903020b288800034490140e0f0441c9480d01480424150400c0d40d40007400400c040001d07000ca0f0700e11610382c0c003002502c0d410180030540c8000204010000240300f440803d2288418194442c24468080348c40e40c144400d5400ca60001100860100148001405400002c24550030412403c22071800305030301c5480b44584031405241c841c0d074003004024625 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 759928336 1250 759927086 759927109
    0x30f0b0c0f040b2817130201120b0a03170903070f0e04080703210b090f0105060f09030a021c0519110402030705070f15230121050307080a032711 64
    0x1140c40c4c181680c5400b400313003945840f05414006001004005401c0b0712000c0c00a403980c0c1d8058480f200104401c800800c09040c5c4008000c0e0040c02004d800400100184110000c0d540c54414003500c3c0c0100c1011700d4030700907503903220381d6410340003440800070b031010700c40210b800a4000750040d82d140d03018241590003094907503080d200e96941024005940c1000d030301c100141c1d00100c41c2c001d102e0711003800030701000f2420300405034003400800c9070b04a0b05c0c3d1440d004005000f4041d0984049018030740002d100305031064000300d410004041e6850800034144a0150000d25881e0b09480600311912000e00300d4005025050140c0c0c3d000010610f000c0c042c506607823007541d2140d20350b250300c501c514040c20540711018424500a05064081103a246803080d9502c0d00700e074280c2340a01c180e20b000315000023040c0d00e00c2121002d008c081383d020003081c8180000d00d46e00c1c0c000c1c18040c0d51103415000003411180c80c0394000c6c1e10440203050b00c2940da8015000700100795003002d261111003190200280020303082 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 759929586 1250 759928336 759928387
    0x212120c0a1115060f0301091a150d0605041103060f040303020304030e03031303020a050604060e3001090c060908030a140c1005150a030503030a05040f080301030f0b0c0f040b 77
    0x243c1111030040d041005125100d540c040d2401c801c104961001e25080c3c03070181500803c0c4c516159188800c248110062541c88040d8403a6142d0700ea0080d804201d114015100942c3c000d034548080109204d18240c0c02c82d18504c0c250014091868040580603030844003500080c00c06400001080c00c1c5481249000c10b00100201a00d03500c8550448090991410303110880c080c02204100081e586800b00a4504031090b503140d1802e900000c40801c00000c40580c40c60000d0164100b0581c041c2c8444280c400d08070595130000a021645801e10300d0b1500700d25800034040200c084001d1080381c0010013500d0b4101403c1c20444400804000499854081d10703808030030500c1120000391800d00c490300071501610900340c4c642d080380080c00c00d0104491240c003014050358002c001090308181c030756205640c424013803696014240b02c81e9513031000c3d540c000e034010755400c1000200e01050140c0024265040b8000080300c516198180d00315241d180240e10400000c020040341c210b4144504848c4159038108 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 759930836 1250 759929586 759929593
    0x30409091b08150f06060714030409091a0109050121060b030d03061706013204050a06030302190506130201020319051e091c030309020a14010212120c0a11 68
    0x44a02059954505103ca41c1109044103800305003001400c00c005400f61401405503072600c403a07a101c0649076510324821300c2d8140700401002403d28404e100e0f01001c1c600c14090022444894a001c24070b140068200d25800c0349894010002c031841c0440088141e56601c965800240c40743c00d100004024800110390036003e03a444a280c0396525a002c82c00b80c8035090503800c580d16410740c448c1da543d4000d0292000e4898400d1070601c0b02c46245000701d4084030300d00303060050f4146400214055a03001e1b42c002e0010b6132120310600c2010b4050210481e0f119000d400d20244a00c103480c0d90790398800142c0009007a0540d1154101564401d104484003805c04d83c210444003d1450001088d95015201c080050080045440250500441194a030310741c002c0401420080c0380002224904500c4011805d140c0d0710382d503540040c0c41c1c141000000b001c41041110099205000182c03c0c4a10488800d035065010042e5142c0c08074500c00c1c07035030021208040c081e121aa000783c16101700003880d920041a20 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 759932086 1250 759930836 759930839
    0x80c07060f0516030603080702151621020a030915090302061206030c011b030509040204180e06010f05030712020111060f19060b09090a0615030f0b0909030409091b 72
    0x6200d4209a0083e031400498410880150750201c046624602009011600802c40800586132907102d040c40b0700040e4103014600f4001d202003480e1581d24000440d821110b040d612040718950300c2c00f0756039004c1d690011f050741e4802590011700d048942c1c000c0b4080c403102e60400140b058400d0303420802441d400f50450346d98120341412800044800c0380c08500ca841291240362495226038004010640182c4040301c444509540942c1c8580040004d15040796007800b0003d018803055030001100102084000341242a0300c80c0c0e00d003810f505800ca8007010740396000c20040c1d500d00044030b204503500a207040ca1030301864401240c2024070040c004801344a8038082c8400946440c10880c0a01240c0a4020780c01c48001c0381042940c65a10074030041e41c000344003e4000c0c6c00c10500142e40301d801048001081c0d5114403000500100015040002942c0c90340440d292040c180324100c10110215001c01c07451608903180ea64a21807030282206050700d807680d038020403201c19800403900282007020508107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 759933336 1250 759932086 759932111
    0xa0332190318061d03030702060304080c0a0b01061707180b030a060b03091501120f110f04020c07050f0301090c300b0405150f0c09030f161d0610080c0706 68
    0x100803120410380c0c10b0300304d40321103111071070004111759035954080d01e80350540e925600e41008030b0300140550703041c82c060305950b0400a40c070035100601030100b03900d51810401e510515040d4101c00103026600303210503090a1710302d1080c1c0d50000d5007116400321080c0c0d030300e80d6100740c0e100180c40964055420840080705002e141100031400c0c00c150303819245c0c2c041c200d0381c1c4c4141d440407052000501810a000141e1204007203142c2c0703c00e000403d0006030070196500b140d00082002c0340d2003004c00121a802c04203003400145007107034407000321100c03c4000740440390716500c0d45229407045100b40707449014600a60380300300446c0c10010708841c1000d110341100e5892420020018401110111014000d070205107200d8044440e43e980254042c07045a0060740da0501c2c800355681c44040f8040c1c0c0b40c4607040100806803010403510790101d5500d0f4142a00915141d030b44a00544c0b491610401c0146c4203042000c25100c05c110b40b40c5e0305c181403400c0606a154800c04401034404c50001405e60b074200301201450 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 759934586 1250 759933336 759933347
    0xb0a08030912011413080c0607050901031103160e1513090b180103020f1203031003030e09150108060a0e1303110307021f02010b0a033219031806 64
    0x1d20402d40d401c88501030303016a0507080b5010041407940041044000c00c0300619415440842c451043c500149032401c0303c0f4405250100460740d0a000600025294410f96031501928490030140540c00d4210300b00114800d00000d40181d4150800031643e40755078066880c04800c50054460155003070b0303112036109031685481e0045c05440c400c1424894140001c0c18905680780c45a501002c101242d030b401e503420041403030748004a6941c00160102c001591310030a00055000d81c210300c2d0107941d52455403501600003001c02140a228003420400c00c4501f49600d20054080002481c10724040e55504d0002015a20b558104012508030401048901d41205a500444901940324080301110b80c3d01d40c00d81d00e03c580c410003900407449003120352000c00000c0c1001c56030195070001051a80503c80840e4412025030710640d1283d000c500790300d969000c08244207030350b08035012a00c2a0f03524407649041c2e6400c0b1810540040341102207650090602c6104041e80e800042c82c90340805503075426000b0030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 759935836 1250 759934586 759934597
    0xa080738040b101d060307180b1003021306081e0702030a0e030d021915020a02100b0901210507031502090a0e0108070314011b0f02060f07080c07060b0a0803 69
    0xd010403450003040340e45450030410301c21070f0035021300c1c1c0000a180f550051440c20000e0003060b05481203000100e5603070150704000d410111041d000003641e0f01a0008c100000f54003628034424075204009425045422415070303415510b85040c10001500c40c2995901c80c200b050b088020158511401c1c03040c0c241c0d000c00200807841d01170b612814400c105004152f2107036885401c840c05030740041c0d605145a0103485200c940303280203c41c000d8044510403281410380c1d2203c800d100060b0082402d00044020500c9071203000030090342c08000f11341c10031000b9510000c455000d2030908590300d4541c0f00708070017048190041d503844036403101041569940d88000c0d401c60940070b4031516141401188008a04501728100c0d40900010b0403420f00c0c2d504d0b4401d0391450040c442e41d855498651307050034070100801c04104c04140c0d0303aa802d42d1b00c030905002420f08001604611168043c0814441c4585d070100740660841c0700740056036600c01b03262800c0c0300100000c030760041e00080561030002c2e50742e201002030107 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 759937086 1250 759935836 759935843
    0x1020d060f0f0e15130b120705030304090f090c06090e15060307120209040f050613020c03120c0c12040302280e07170c040f08060f07050a05160b04140a08073804 71
    0x40b8000050000c6036108c00080c056560564000d000402903410b50b9001015200c404820000e00c4040c15180c446410086400c80008152411402c000c21014004083c0d444400c40c071541c6003041c0304070001400341c440a00170078108128459030603014281e6074101d45071814024410840591229040d4002e000b00b190605d00ca007104000b40c0c0f809000754001c880c00f0264034009146010b50020303030019050780c00b503d002ea08046c1804041d00814040181c46040802500308a442c0d0b4034502c100a0b88944041d05860400710b81c240c1c40040300c0e02d0203030743e07002d607a8080390118187c0e0b50940111645050403581280504e00c56091101c4185046c00801c241e07618024051b06c09925441100e42d2440181d41034646980510002842c00f84144094560304c1450b00d411450310000392207820001f20851800e4a5500c2d550081c4410000c102503600e0200c60183d019244191840d21503010b140034050300904068100d461004420700400215000100740032400b41440380705101e41c80c1d5550003100c044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 759938336 1250 759937086 759937099
    0x411061909080a030503011e0b0a020303060f0f030606101b032307020d0318091407180f05040902040f021c0e01091e0312050901020d060f0f0e15130b 66
    0x4690b1503004a54407141e01e402d5140c8514503403030410790717411016610641d401f2080b0300744800304c0c400d60711400900c4003e900e5401952a81080303010021114500c204441c400c50b01c030344420328240c4010036070310381c0319000b16580c01400da828802642e80d1510800031a00c04041d40c1414810160081960700c076000f039042041200c51103840c1807908038403410340c010790f12800307401118000a2150b040700d201110b50341910851a561003050806a0784040590780340102c050040044030b40d4400314071178407142c000b4002c01d007080c0381c45402e1600041c18001e9074003603919006140e00750f443d00e403c440c0325072046003001c5640e0a00001c4825403840c040d041c0f03140840c244030026441900500803071072603680007031180101e0646038402d40034004141d601101400703400300103c09110418803999200701c0c070550000d80d030350140d908014201c7d0804d411038640e1900400c0140705143e0500080420b0ba42c2029200c107003a01e5400c0400240001c14082a5011100d48075801040380c49170841e810000d01035980 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 759939586 1250 759938336 759938339
    0x609060e0612030712110d0c0308090a03090512070e0a05010314010b1005030603210306030721081c020f040302040c03021206190308120108060f0115080411061909 72
    0x104650990b003010784000c036a00503c04e04001c1040d00e64140000c00d814142000300526840405003000502588035000c10200ea401f007080c0b54005080c00d5005514401410b4110301aa5000e4907984440c000e050144844041100d1502810040c04016001c00181e0400b245484070104c0054a002d00045031403c4403503110203202c0354140956040400000e01f000c01c0b0955004049540f60001031140f0b0b031604c146401030100c0c3c070b030b170108240d030b8100f481e21103e40d079142640c1458946403603a0311070280c40d006401102c041043c0ca640d40041c1c02ea02c400300566a611032800070440007080c000c0d800595200143d6000201150300c002c00c12a4406da42c02d11440c40c2c00c41c01a8101d0040001d00058282001300280f03940c501050007103600b03a0b10514401420391241c440d5070140e0040d1801e1051035420100500c0080d0080001076072104c0c81c00c1200c0c102c0c0d0b041c80851442e02e00e0409400040c4000c089c007150801185076210900c100000e48080e8441c1c20481424141c181440d2400000c5904000d0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 759940836 1250 759939586 759939589
    0x90307060203100510050f030118021204050a030f0e01140f0712020705010f0c0b070806120d1d03061e070201060909080d050f3916050c03070f21060609060e06 70
    0x166100d0040c9440b9090460307290000d48070800c0e141000900c802030340cc01c541e152320803a504425001d140644014401c0713113518680500707003181c04040074050042c000380450b0140c0e8415001424200400000f03034840300402d449040b1805200c10007011030f80000f0388070104070303400211001198400da9a042c01c01c0e80742801036500122410000c0e108848640c000b50701e041c09805103940050300035102c0300c24004203201c11402d04035140c1e010400070302088141c0712220440074484400007803ca000d07140a04001004488079941e0b01030b104044120309001030010380c001c0d0303c600b0050821200c01c0c480300c111440d01c105c0341e9200c0341d44410901c1c90f040c00f017250510f40ca40c0c11445205035802c03165480c9800050314803083c500401014288200b0010107501d02900009440b900b09590341d9458840024a403907420214040c01c214040c0d404001704104084800c043c40d0101c60004440da180c0303025500075600003160991014084506280000600c00c015920120403541440c8c40000951240720 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 759942086 1250 759940836 759940847
    0x7020d142107080a0e120106090914030f030f0a200a0f0e060301051309051921120f150312030c050702060405011b0b010e2d01030605090307060203100510 68
    0x10400f4045078002e1200c201c015024950f040441d02d401050f084281d40b00c0c1c4505030a4440c3c1c2d400214081d0b44501c503400c1041408150080380f000510055802c203405102d2000690200a200c01092800c11020502d400c07a02d500108c034111200d810381d44d5000300840e122900e58070440d081c20020f02a08402c0319140d2240b202011900e0004010354a1030740391100308604410b1104081041a030344500220000e2010007204035500a0400307444681d007164146a40500d4000d41e50380061b4809100d039000036030744640d542c180c03505a500002030016a100951000b440103035001c000300c100101c0040705000840f20700b121a120103aa0034031110b08280400c031079900629000a410503410311040c000c0358000c00140c030128480d070b00e40500900154681031200007080c1c0c00101c01901345028401d040522380c000c80d20043da4a000560000c2e000c400a01203030742e051001402040c0e0710008112401d0043c81100d4120760400710035916401c0412902c2d08104807440b40c503200b02c9a984400800301d0040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 759943336 1250 759942086 759942097
    0x801030b0603032a030c0313090c02030c10020315040c020a0210090302010c0b09030f0a0e1003090308061003020c01140906010e010602060c0c03071236090207020d1421 74
    0x68080700760781001c0507008684c041900c404503c0d0741c0414400128041010405085209080b00b0741244643c94041d1050440704030004060440d0820451380d0024800001c20701c2124010001c0180d60740e480d80707005805d000c1814082c5034494200342024801c0380d0b0000303061480138021299003000c0141000150781c03140e001d1000031b0100743c1c1900c07010040b1700c00c5024564041d0011040d24646000706100c1043d650001007131101050601003840d1983c02c2400305090561140e08081201e08901d8030080c04408005104620945003002e0954a0034440d8041e1000e0301c103854000d02c8070040151014684d00c008032503c403128883d6000004904050350b10090480304960068242c0f0740b0b030048800c5e42c90303104841200c01d03031008002c000005805118130420a07105581c800c1180181d48001c010700003040d0f0840d2100e903d119141048954204600c2001c50300b41000c016521038051001c00c44140503048007900240661040b81c41c03001e40400c01d80400a0003008000c0040b0000c03074802e0755401903 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 759944586 1250 759943336 759943357
    0x1021e1b0906030a060e01091205040911040b18130c0c02180c16050109082a121c0902060d05010305060a0504030e040c02160906051e131e0207030801030b060303 71
    0x24101c135034040380b0568002402c5401d42c2e400850140030701e440b21104480c0f104c3d44c980c0050b00c001b8081103509203a104000e0700d165004000e80c90645000c00d000901d000303140d0507049205000d0403d0019907919494982e502a0100302400813001111000d840d40c0c0111030107900603800386100740302403048281c0c03035403150b060b01c0e0485003080c080d4440000c8442c002401240d5941d81c0c0c902010112704014060542c140d02c034021009642601c2c5900c0d07905414030220307010310b03034401d07509403a0102036001540d252105ea41ca1a00d880080407000d107001e050150000780d086400003400c0c8883c00c050f6004241070b0f074024012526280c489640000442c3c03811a0040c0006404201c10391440c5442d40101ea032280091040307501c0c541c1c0804400110007056800914a942e0740d0310b0410440c2040c3d1141003031010704020001c2002d8030900815100207110160440b1300c0d0b51507100b03444c1210318601c61101030082c054119101c040907d005083c1000038013003a151060b03404001405450300200300e4602403070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 759945836 1250 759944586 759944593
    0x5030c0406050f0c0f030310060e01080103120306170c010f0c1a0a060302041e061d0c0a05070507030803040302060f061e0411161703070f0e01021e1b090603 69
    0xc0c046044400303821410750f094950310104403803032032407000300300d100c0d0380c11040d8024581d01e0820100c0001620301c60713801201170100c41c820007a00c580e04811598112900031800204405a145c000c8008203030603049070a41c00c0d4045040290984000758080c2d041c5000e0321008034911040700d054500c1c540300c201c0200050048421403c40350031b01b002041d00003c3e0090045482134a90303000600340d500c0d14140110602c140f040c44016400d0718001d400c0100291021442080e102403881e01c42c0c085c0c02401d2404207040041d0004902d4403034002ca4034141d400c1010740b00032b1a120b00d41081d07550310565090300188106030110300d4a041c1e00d140035024131030041800c034183c91040c901240c100d91041203030340c2c80781e03803086040e0b8001c0e004030080540011814003820b20b04650700e809201140508840c00c01020107104010316142c11002c000a4000c5509004168041c443d00403850003d600040c10035030049540d00103081000000d1030701c001c0105030400000c0046a10511024180c1210166803503803 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 759947086 1250 759945836 759945839
    0x1505090a03080c0c13090209150d0303051807032423092104060210020309060615090612270709150b0c070503150105030d052d1905030c04 61
    0x30b4190000b00340c862941801d4a410444110000700c0303e144100c00f402e070254642c080e03c41149040c0303650540c0100811926429481c03400040362100d940b40360010141503460713001c2000c10305843d00c89101030b50080b007120545034072072501c03a51041d590301c851004050303e00e1440014074114040d40c03c100e240c8181002e0407020102c04030780d241c200070f0a001e80078014251400c0c4050200300440c0d0003042c0300207c0c80c2d40c1c1d07488e112000f0302d010704810300404181d2050060002c9008041182a0000d0044401c40840180703508901c20f40c8c89013101d01c55111400198810394030003003500540c42041d4603220070031281c51035017900c2109180d44a10690b01e4200b00c6062000c40b6856000c408003004258161034120f0b114a0002d0a613030003503505e180d03241d0142e4004c104919040000d003141d0b020b000441c0d0307582e515001c0407070380c0d6030107a00f29941440b0000c54001c0c0c004142e0340d2858980000072003560160b402e13009401c411940000d801c549045030f00c0c032908900500038022070b03000b03200d070049991409 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 759948336 1250 759947086 759947093
    0x41d060406020a0909063c0609080c030c1305040c12060b010e03060f040308100302031006090b01140706180b04030c260405060702061207090915080a0b04020a0f0b03011505090a03 79
    0x46640042c411107106100d07e892449407010f4100c0c0541000d0b210f04c4009030030b20058500d03189224034410711a51003003091002c00e03268201810215290180c020850392281e01e407001d0b480c0e90541000c200d4118082c3d0b500248003164011084101d0b00780c0300c2c1624009046c0505440d41011a5000312070560039000c140064410882603131300c03d00f1059001c140507103030340c0003908001e4600b80700c3d5070481d1145418060706030144601c0d01141c100342004003c105880c1c082d0509400362141c00b5282a0740c2e40d081030348803020f0038840d40007a90702c941010740c180f40614002d440d02c0070004054805007013002030080088180074002d076240c8000202e0904261500080290940c0001003c07038100ca018050b20b4012440398406502840325611550421824510120126101640c2c841110080364004001d18240407881d0100c65411003c002125901c0340082041d95489078040c0c03400c104c03002000240750820202450688104041da80101114803404440d0f0f40104000b2652102c5044d0703080001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 759949586 1250 759948336 759948389
    0x3050a0209041707060618150b03060402041703030a050f0618090a02030a1a0c180402131a07021c0c0e07180b0406030e010614041d060406020a090906 66
    0x1610911400e0003100700c01c0f804510f00c2e040254221005915800144074001c1c0710303484d080100c40c207000200010b00940c48081050451442144488040040880c0d402c3e00d0ba0f03012103018011261010780c3c42002d480340d196999000302c0b24031820701d140402203880c04004081c2130380110001010540c0d07000145c843d0406154020345107641c3d504c43d0642c1c000060320140005140c0d0f6005811000c0c83c4100f00c01281540d0000511a2040310803c002038503c090800710300c145815425100103840720f8020031110b01f200e1040e085528407001c0010707081002d960140042143d82d10980d5819600d82c601840c0d01942c00252400070f102685114051226811981403258000d0b094078003400002c141e2151203a4841795900254101000000c003032002039018001e404400d003c010007080780c14900490442d00c0189182490f22590b1107030381041680d98080100c50310009118252803150420b80b9045000b50701c54101d04000c1a10f9100c00110030b28944144130803940085450204c1c454030444c003102 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 759950836 1250 759949586 759949591
    0x1320403051c210e060f1b0405010221070203010609020a0311030103020f01111c090302090705280504030b0f06120307031d1809160801021305040209040603051603150603050a0209 79
    0x6296510001e005403004e04029040c0900700710715520300b090514102040446528994414100d00c082004011503640001c26000c882185001c40501c007501e51000c0741e0601c038490000c0d50640c20300e0400b0a120303200354003c02111009440c00c0003441c0c11803094800c3c0e8013003440080d520840d980f02e11882c0d54060f4910462104c4d4280c01e5070540030603548900801c04030140b4020015240440500860508405c1203811400f60300b4036905141a800c512810540071104400b402502943c00c615828050307000e9601139984004003017110301e050510f08001d943d08941071841340d007100d00203075a51140401222000c07a095507605020a0740c114400380c0700d40030321002c26046208031810908580f03100020b10b00900202d00070b00441e050710600d14007904416001604964410085581d11044490200e0120303801668007586070034000000a004000d03507407000c0c00c00d00481035800c104104248500b8141c0784138440c508284425031422004940050000400307a500c4040030001528100710350783e5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 759952086 1250 759950836 759950897
    0x20d110f1e03040b0f07021302070f0f02060903120310060e0307030b060a18090615050f010e06040306060b191404120c030c090e071d010501320403051c 67
    0xb443d103030740e91400000a5100d101165412440800c6600c210b10b0061100a101e5a41610541c104003a1341c0382c800007070070750200017003041c81600044000c54036040706035401c40000074103458a0360403000e22982c0302e0380101c03a1103e0148400c4004190359016120880c1400400340013411518250b81e40c2901d4514040d001d240d0149030024002110003005421110520710290040707044031071843e10400b17940b00b0301c0c015240c80c02c000b502400242c490b00c42c4104a80310910f4038208688001c2c0c041341042c0b00350f800280559040c4400895402440d00051605031400c2a6051105081c0c0c0c0d000c170b9010320118012001074a042000708182d00c000c07128a410304e800f41c200285030343d40d0307540c0b543e40500c001d900000d00d440c1c440d401c15440c0c11052000d0780040c02078404804201018099032903040741e05018035414098038440c070814040da01d414861f82c80b65040c202100301c0719074003400c0b45290014407040b1440d201d1041058801003441e02130140721402911048001c60422040c5c805c40c0910b0307901c49 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 759953336 1250 759952086 759952093
    0x20312091006170c0f061611030d080f0a06150507061416090b040803070f0302160303202b0c08030f090706171303140a020d110f1e 58
    0x4596401e042c0b0510005001d05030181490f221200b07900b50510100c0c900d654410080310039041500d4032440200d035182c1c805038519484481c50f034908844203000003110b45406104440200b4800d60b0040e003180d015024014620f51a9914003010106071640d6000703800c401c0a040c020905070318024009084c1c40c5100b10008503038a05007500c200340b2401e00703c0d5100300c03100da000e05003100c0b6508101d8240203454914081803505040c080c4144e541e1150070b40081684200c0d602920a0601c00d210300e031980c002c0d600085d105c007562400c00410b944141000045480003051002c07160300c0380083d82c0c8034403001628101403103201c903561540c801000108550309010080c81240005000c0305c0003035100d00d00100000e041030030618980c9140040301d411910030711025104007801c400b4544002540b0000000301004490f00f42d03d030840d01d500441200c00a0890041030502d61281c0102d45800c00d91900c1e40e85146000c680050140d81d4445101c00c45041c0d0003600585600e00641202c6222402901048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 759954586 1250 759953336 759953353
    0x40e0402010c020d120806060702030a08071a0408040302010e0d0209132d150207020d060908090a0b0910020d05122203021c090b090f0a0302040e010b010207080d02031209 75
    0x401c448004c081c00440d000c1c0100d10b00500302580094a80390070034801c0e1005400c00d00303181c4c00300340d442c490f0401c003a10201c0003182d84030411000c0e08102c01551580035407903a03030341400e140607001504240000c03800b140420071500114240060300309403182c0c00030324100321500d6a500d1490f1100419030140c9195070f1503114060205142141c2520000c0074038500c42402c4064200001d50952140300c1030240303801040180b016a0720403442200c01c9402039000108a4580e2412004901c911041550405070249c000146103400c800507041585082d10304081c1e03521802002c0743c4500380214082c2c046082070080300d403040700644005074048011200c40304401d0008448403000b44a414048005030302240e85610180030203c0981943c40c0c00f820b0000b0200e041911081c102e0092906142c010f103c4c0070708891865030307040b80100055401810030047c82c0315802440d030107044c841c0e0505000d4455250300181c011000103030201d2441060740a5030070f000d19680d400040c1000541a0b007650300c582207e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 759955836 1250 759954586 759954589
    0x301060c0f1b080f210d020c0601090f1a0306071206031b1707050d2019050301060f0e04080307020a05030a1806050a12020a02010626120f040e0402010c02 68
    0x9451640030ba01c020030644249000c50580c075000203041c4010080c0c0040c60f101d50468401c03241e080c80007480706000c83d26071805900c6180280584804400240725400002441c00096032100d054003500340e20038444501c0030304c825103810a175151001d4056001130300007000144200044030300c24007098004a4865030f252540103d10380340d242c009040c5041004100010301802d0400c64907800507902804a0f14a000000388000607503280c0940205a241e03802c00301c00d415a2201402d8004c0101140d460640900000218024a0250500030b602e001d002040c100030629190085903001501400103a03038a99484c5529000070303001100f9403042400c000e00090701130003d8040346081ea621000145041a8420b1310110603500400502c070303040114181081c0c1c09400c415902420302c43c05a034522001e00220300600c803540c05105009401d450b1a210754046c0d283c1d00348100d003480308a4040004202081d5514401c82e40241c601400410003044075100c1000d185030302a005040540c0c0390741e900d40 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 759957086 1250 759955836 759955853
    0x307031127040204091d06330d080c0a0516291c0f0f05070210111905040510050301121103010b040203090a0605070f12150b040602062a0301060c0f 65
    0x18813949101c01600ba0543c40403408100196004003d000e035182d842070110707144803c5141403d5500f4445040322602c007004d480b4990f27600d045c903511004141e07990000030788540d12503820840c1102c55000d17882691605c01c0444964805661008903200904141803030f207030303c81038190b110300e0710b40050504c012044c443d00c0c401080441d05911a003c5034001401c02514200c0c0c1035111601d0180b46428240507074150b002a40c41700d5403010160001d503c0e603c1b1440c4070441e004460680316408660400c0750091380e441030180003195030a0b6052455115446020703110390209008000151085102910100d940308005204095000d400000d1580c00c0d240401e082e82c2c400c0b2070b6416140e010500e800100042403040a030711407005e182040199000e020300410405003540c4100c0c10b10b03120b04008810350700c041d8162005001c550325441d900c40e40c551000c0d4480c142200c4840c00c5051004414080d0b0307110710319a4180ba04103a103801d103541c2c02c210b001d4900510060054440c510701d10321900000700e400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 759958336 1250 759957086 759957101
    0x70f0506010e1005040213060810030c060c030809061302011d041119020f0c060717030106170f0114060705031e180111030438030703112704020409 65
    0x8100e848810f20340a000b80c2c14200c11641320600075441044400aa48130040d10700068880900e040501a01c0c0c0070450112861280c00c050142d00c1019400590181c008086d0a8858800c0c1c640a1082c2c1d2506291501c8000c105c444010014080d0850001981306070a00c0b0b900800c41c0070228010284280401c040320100031003007092040000e60118590f00d83d00d141a9040180c0c4020400c0464100c40c598880da500c00100e80907d101054250810041042c00900300c14482c40b004d0b2250381d94440108030321290140c042c440030080700414950b051704110301c1e058600b20000704100000640c2803201c04e41c09503c003940c49000501a101c20608101101c050786c42804000e90f03110202252101e941601d00d54a5905004040f10301c0d02c26490040142c8003140c2c50107100414040006c0c164030a00034101446000c44004610310081c00310507040070f0360003802c9581e400c00107581844007101aa00c516040010502c43d01c0102c03050300781060030039010850340680007508055031850340c1010388006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 759959586 1250 759958336 759958349
    0x2031b090111030c0601030201120b01021e07030f050318030a110126161202040f03231f051302010c150e031b06070804021509030c100e011106011a070f050601 70
    0x44010810f56078860581202b24040f100c0402c0800c0c407810004c2c1d80c0722800c07440036480401003044200c90310300501040d4015074102000b00c50110080ca0000d031281d010000403031080d205510714641d80e0a0001d2001708040d407110808040a101c2001516244001c60740741d000c440b071140c1c40c442d00c0200c800b10b0324018480811050035408400c64042c01c82c40c00402d503200401d105006c00c110390a0342e6032004045980201e1120b843d50110042e5a1100e840e4100150b06480744440380c40101d12040e42d8a142070034450780070009516043e0980c00c16030041c1d0800390000395203880180c08a410b00340e6100700d17400388520004200000003200307801c507041900500000b890710b0603069107000003403010986c0b06d12a460b041040c0d141030360005071b880011000c400c0300941c002c1600c04640c2c0701007013207000c1a42d00070046400c09001c0e01d0001c240d00d07050401d030750002c0c00c00380c550042e81c3c1c00003905a069401c1c114183c040c1702e601030003048054100d5038040e1402101c0100c8540403400500450780070b07040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 759960836 1250 759959586 759959593
    0x106090b090f043b0a020f040207060504030c060b04020403080a03020a1701080729120a021c05090c04110a0c030e040507170709081f0b040c030203160302031b090111030c 75
    0x10748104a640740c40403050310302d800d40c4001d14541e1390400840d80c0c0104513412268000990b02d1500828000d02460400070441d0345403501340010b00d43c000c501c00c0038442c45140c00344041d144100c18001039004611004290070320038418210b0b0903019802404c91b5111929003285001000354a003c00802d0aa1002880c3c2d00000414001c1c1d01022068152903070342400c180005600c4400d84503454407032400c0030002c3c0920f0f0404540004056012a61412460602d0305421904455600c1c01044190f9008026114120310210b60781400c1c05054182e90903000650305100136010180c40455080c0d00440c10400c1110301944a90f40714843c450090b041d42e618070002001c00e41c42c8441628015050b042480070030241001200000900300010800d05030030314158000c0d00300c0c901c0281c102ca0b002d032640181088090070320103906901562046042c20303080d2965901148080d0101c1c070099a48c3d0b854000303a50040781c1c42981d844000c1c024864180341440100008840d000e003960425600180542c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 759962086 1250 759960836 759960881
    0x230604110f150406140c030c0d03180b01031209120c08060108070305070b0a0e03100b04060b0c19050a020a150e090c12040201120207060501031a0106090b090f04 71
    0x101425820603084060342c0c1c07604140c1070b859484615000342d100309820040101d03400e54013040d1000075038001004480880e0b846031024000540c54807141c250900000703181284030344003c183c10f1208140141c0001d800280f50f425034031640000c4203404181c074244001c9402c001402801072001c2200306003c1e000c1c1c81000e60815000318109041a0f01000301e650200c00c09001090010503140304480001348035076550600d803071055480140b02c100c290341c5401041031000c421035090700490f5640d002100c04011140e125140d072901c3d0b01540c100c5552551080040d020b42d6010301841e6498035008108861440070190700080c8d074244240c01c01c0e020400f011486170b4105800036100b0540b0b1504030303004495441c0c564840c2e11103000d00c0c46103400309020900401c080d64091b40c60450312000610b01590340741624101a8060705080c841241c0f0181c401444018000c0350101d0316058685036a9442c7d2054a06500300010750011116550f01020096036040b2a944510480602d1140e00a5000301e11 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 759963336 1250 759962086 759962089
    0x30f0605010f0203030a0c0309021309030207081b09130615060924030b010908030301230a03050a081e1b0c010c021c0f0b070e13090203070323060411 66
    0x9819551000e814030861140b02e0840980210540e5800050f40c14000b415050002040b0040c085480d4040d400454000d254030044020760400080ca80c02a001c5912283c0d03076582803503807050282a002d81200130b20f01460058945030351503940014882c4082d0068045a8445104540921070081c1503030385403810070809903400c214000000c020b5402044000480c1051030301c01c08402600c500c1c200b640d40d0b0202c000c26802805144081d0400c0700440351039684503460350003603c00a125803000003042c400c0329070700340c07030300300410004c1c0c0c2c0d8488003030420010a6034074001980c0203840d600c0c070b04400341700d0444207501e503210242c0a900c03012400584400c000440060520741e03150701550420182103490000b68645070001c0032002038503105552a40c80a00700b0503004480350000070326808081c8140300c55681d01498404090740212101c010035401c591001003182c100c00070007501900107000030000700301c6500042c41046d2464035540e4035440217060a40c10448119811254039100b4510300006 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 759964586 1250 759963336 759963341
    0x20702100504030f1e0b04080c010e1c1425030e0d050c2202030907140904030206060105030c040b0c07030c05040b030304052b121d0f0d02150703030f 66
    0x10308450305215142c10f0464607920b1081550403000740c0040105c2c00895104d080c0071108242007900040349a0181c1403d141c100401e038050b5801070f20640c00c1c014008144040130400c2180403501c1001d040107a80d001d00e055403c0100100c00c40740d4075400f40013210201c01c214100c034207000340e2001800c031110150315001d800c0d038060304000b03030146640240b0000000c000060341c0c84045400c840d1400840422800404003040c005032103451180003006100d90184006050b0007611300c103011103100580e641091104900b03046030064010ba000340c020070000e501800045420020701d079a00c07494542c8501030740c0c080ba4800401c0c45020307070045e8801c0083c0296010260f000c0e100481c0e040c000385403181c001a640c0d002d140102131203409002102103800106881c11845a20300013002c4032020311500300f50540c061403555100120340214252a041c05500c41c801c00b035203400822691302d6403500801d0003004000c1031412604000307101c1c4001c1d49848554040c114461113641c0c0403550a0341f000c4003800b03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 759965836 1250 759964586 759964609
    0x60b030a1e110702090c0906180a080d09031b0b070b06240d0f0e060c190306050a0e040201170a090c170a0803090309091603050609010e011512060603020702 69
    0x1c01e4900000d6007000c419403000c9816080d0100c03042c000c2911044801d552521907039401551281000404800450264061000c0c807181221001e000c182c0da200115220b2100f13940440014172046018000242000c04d030a152091600c00d054805440d10300d05803180e8004401074441032030b41410040740d8500640d80c10200c072050117245045544d00d000a4409026a01140c1691500c43d00904e190801c81e504c41e99540c00c404e8210780c0642801a0180d01c0c984c0903145090440140b014a090076078041d0064004840d4080d060400091500ca9505c110503001b5004030704120f40381a0b00c0040c4a440074809010b41040f0100003020201442c08024480c0300768024004900b0b10a02095210004104000c1c5150807590141d600e58031110020b0840c03103a1850568014000811312007103c460042e180c441d51042c6d2800c01c04c607100d807010001200c1003441130801c204000030041c06000340d004510305007810141001c0203001407106c9081c080d11295080040002d5001c6023040c1076181805d00d111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 759967086 1250 759965836 759965891
    0x70f060f0e1518010b03010f0203071202040f030f0312091b06020105011412190b0f01050d020d02011421040c0b0a080c0703090302060a120510180e01060b030a 70
    0x40c1c5008000420b15000001042d03007040410f500b03001e8100c0c003c01e401999900e90003d000300b1040080d07480c018002d4200340c56080006082080c030180348001d07842240c0a50f4a00d001d40480540340d0740d00c0749000e045010b01102000702c4e40c0b4200d16495420b028202900f845080d11195001d80c002664201c042d0507440a001c581c10034004000e00e101e030038000110342c0f10a80f180c0030352000701c000c2240340c40c0d522011400d203210341d00710400a0040ca10540c60094512a500d40c0090343e0320000c10803044151240a584442c008400a0040d03004410a00d40341c042d001e0325a0030040240c6054088041c00849070130703081500810002004003405e9514080c0c501c4690786800c007400c84500815045000740070024006001400005150045880d00300540c3c1c000c0c52a035494003c3c0600610080ba80c012040318107007030001150b41074403200354080544265580504103140c582c4d02d698081c00c2090942c07000b555a07844c002c01c5003400540258404d031182000400d501d0301700c042c11120103c1154000 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 759968336 1250 759967086 759967093
    0xf0402090904110102030c030a1701050a0b0306220609020d0e01020c120309120d1b05040b07080d0e070608041a01030209011203030f0609090b0c070209060d030203070f060f0e 77
    0x849496941c03102540d00b058000050380080700700103005030b203940300c0c07030182030043e100114003555699800100807181c8a0b0607081c5d8030301c07a42e03980d085c170001080380d00074620091401c1c8000745140c2080008002d801390800e0034003012034602c0e5810000c03034050740c2100c000c1540004102c2d2218426011310107481d028031008502e424258000d5580b40c03010340f001c50400350400808168000b504021500c0d20390800c6680c5544e0741d11a001b02c1c8010000003002d40c55006000d03449000440c000c009072000c031030b040340030395103058501c0c0c0d2001c420b0741c480203403081c0d5035585e080040d4110340c0402056000d05059252a4118180303410301000010448800d6070b0090300304801400141c0b01c81000c02c1c1100e038810341d505120302c401d2900394090000c5002d031030f4540e07141010014010304a500282c1c0424000d0b01e091646489048603000b451117509070103504032110301d0204100b401c101036110b04c2e5600070301c162810300c92107580e81803c03211b44d540d0960304140c070b5480c3d0140405a501c11181c2500503003008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 759969586 1250 759968336 759968347
    0x1806020d02070b100b040e090a02190302011115010b0d0e01090501201306050a0c02030d351f0f24030504030e10030b03030d0501030b0f1e150d0b060f0402 68
    0x10240f1b40328500503030501d510880c010640c071250800451503243e9004054162800c440c0042545c002a584026030008004e804014065040480d08410043d21405035001582c2080501c25155206203180d8041c2d1750354614400000c80c0a100300322565114500104111041044c655440d0340414113510110354100b04c0c000c010f490410b41401164003a080048d00e61400d2081915a80180003001c0d401d4025122200c808a500c4502c4036110828800e020110b0113544044548a0249491180e070361101c4c240841c0d074500c0c0010411420743c1e00904031440c07040d11031120309203451a541c000c40c004006040a003003411000d95100c0c81c101c00c1031904011030701d0142c41c01003126041510590181c4801042801042e03c2908040d0b41e500b4050102d030b40c1c4c1d14034001c070080203000c24841a5900000c220104103041000c10b03080d07008421545040c14102410203071071003400304c05000b0129641011558050a8980000741514107001c0c05891515149c41c001740f28082c82245041441749204016 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 759970836 1250 759969586 759969599
    0x40504111206041d011a01180807030209060a0308040603021306030209030a02090a021314040c0f050a081012050d02010f0b010c060e0309030a120f1b061806020d02070b10 75
    0x286a580080111800301d0103002084044c0003808080484543c1035080c9001940c03144161540607030302c1502a83c0d5040207650703c2c0400c0440300d0f51801003140942140d034040000d450041340c1540c10103001010448001c1d5290f603400200d52013503020300301298000c1a1007411518201c488001850941820341c607100c0280c0c0020380b20303c8645e02c0240303e00f604a0115190303030a25419078408419035043c410f045078442c0040d040300590420203c0c4901d003800b50050078544035020a442100b856140c1600b811090003040d1440b20004003203840c42e1301100c03400154101b0006a90603150301960103002440390030b1000030b007940d08048100d0141d07420b000c26002a640d100c000759103050340054002403c02c8148240c02c1c04e5200d40d41410f0350600c07681000005010b42550340c00030801054403024505d80d20502c1c2541c40c44201c651482c100000c01c07280c080400d09503082401c3d40c010010341c403080700e8080d5460001301e82000c802a84c1c1c3d80e9000c210081082400c542c0704d904040342c2c501400090f8138040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 759972086 1250 759970836 759970867
    0x1609080a03080609092505040e03040e070f020102070f0f2618190603060509090609031606091515050609030a1b0e0a02092b0308070903020909010204050411 69
    0x83c4894000e05441001890b0601c0c14030030309103c6140400c40d0344841801c98001c0520410178098180320301d1807d0400c0720070440020481c0c089681e1210701d400180e4a42074142c81441c046045d12041d95000c00c42400004c4a62a000b40e4481c8200a400380310354050401000e41d14a01007060310400180c64070381046880901900d02c81c00b0b25000c07800c26880f041d008240e50400076501190420604180400c205405410200c107880d800c3e500f6900c0c0b5070b590240541c0d038400560300241c490f001000301c1c6100803140c16883c201c00740034040c04201092640c1e6000341074641e10341c40079006d43c3c0d5078842818051060080707100411044400364201640c00d40025142d18080c2001001141c000c0c01c8074080b4030070000380b0750003803108903107141300c5240c020004030280d40034000c800c0c4511210301c821107800444010f0641d50b14440507130301c42142d05954081d0742c0100041c0012040c8406d00c800007005030f035440000744c800c0c2c05d1600050f071030b02e00d41810f0000b50341c0d8000300c8424040052141400e60b04001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 759973336 1250 759972086 759972091
    0x3021c033b030d021b0402070b0a050414070e0406050c090618090a0608030405131b0c05070501090b0304060903110a1a0702030f0304120521091513031112031609080a0308 75
    0x1080c1c2084070703601740b0001400130303c01c095004014080f42401c02000c94000d0b4001d40c440c034051000e0040b09a0b6161501d603e58800e4014030511403090170200340455503582c425540425001611071421104d40000350340c3d60410402081041c0041214210500740a040c1325044045020107004071070818240347c0e10b90040340207840c0540d20010307070803114200a0308040340c024291002d81042c0c00d040c05000b06400c00500d010758591040c14000941c1c0d520642001c412203031b18100b410f0568680d56181c802501d401c140960411002d003840c01c02d0100c0903c4a88400c1c2e100b2a00b6030180181c401c0d070120421001401441590004e202c13154103140c1e6070040320f83c015440004200b4010b456403080c1e58034010220074401a9000c4000440c64500720354580740600062002c55480020a65a0044c0f8207000c8400100f00d5400080940c0001d000c0c0515480c2007003030700c00327550352070741c4d141c9505200b5002142c2c00da0741c0960b0780c1e0003a901b07150051311420160803080c1c06086030325456100504000d202 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 759974586 1250 759973336 759973363
    0xc05090f030a0c0b03010f060503240d051002120a09170a0c050604080a110708100b060d0504061b03050c16080c1203060a0f03021c033b030d02 63
    0x480c8520440da0103100300c0040d40e9004212240413600c8054800e0035030024060907090541c400408109180034000b5284110309001c048030154115284140001003050341c4950400c0762406000000303041800b44101d84d10f00034200607103901c0b00c0ea202191860015000e00003942c0342640b42c002041c0a900c07005190800f01c0102580d600c0c0010301202d2a507000c00000e0128041e100c28801082011402480e400341643e41e4155016080d658240d10340d0030a20544119611441c0203120ba002550000100180000d0509040c028504c03c48000c1c0d034801c64040710310700e9960258440750b102d10509641c029140346402c101515004c544e200c010701c200013810000006850400c010002e040044808040300401500e210241c1c00c2484115900240d42c4c46120705041d8401080540500d4600400c40b500141010701005801131000030b240b030701540a80802141801980c0410003010000442c5041821071400501e04101201100720385008094425080042080c880030750004418580504 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 759975836 1250 759974586 759974599
    0xa030c05070f080109060506030607020d0f051b0c0130090c0b0a030c020d0f0c0b070e150423030c040b1f08010e01050103091203020d020d0218010e040c0509 69
    0x5040c1485480d1968540c04420441e07080c0d4004a011a4103400601c51148603107010b00890700d507a0100f51721a031040b140e100050340708038892030800e442450558031146890402c680f804896448180162503e11600c8905034811801da11007564040f03120034490421940400740c20f203484082080310300403404058919078030380c0c62703010038400d4168461000340700340c0d8416591003e00c4100a0b016202c080f480c0b401500810700101c45150141d580e02000030a9076460800c1c00ca1540e07550b407007881001c1c00d403604205c4201120300260b02e030030400c078030f1001408100701c1d1500c0c50030000d00c10b007141c040e0300c46600d43e08061000b900d544000508a0b140c06d01113401140815803100852030103103500205020890301451401d04031a041240315042c0c500300042040f20381e80700c000540641e010442d008100c0d0159544030007a042c86503002d403e00b0800d0b01405032814580c070104201741d801c82e4510048190007100840101e40e04858852001c003000c5d502406050000100a04540200c0840600440 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 759977086 1250 759975836 759975857
    0x2210609071e12060e0a051b0a0e04180206031e060d03091403210406031103060d0b13170c01150f0603020906070c0603090b1515090103022704060e090a03 68
    0x3c540e008070340944030710302076030165160038010040604400c2d2554005820081007000c0195800c1044441d01821904d5150200702c9030021b020007400c450302e01200f0725078012140d80059a1f0742005500420210301101c0c0046100c40000c900b07a071000e041a849241c8450340a00042c0e0052b840c0c4003160080c2c84841d07a486845004a81041c0b40f0140e568050030703203560303a0010090b0b10806030065900580d010003d91065101000c4248010346499511083e40c41043c40050482d00030039074400a241380c12249100c00384d41d00750040c882d880911550110114004100640910801d24042c1807400d1282260b8980907100d4400781060007074a0800d0380000d654251512048112120329038408140e05045944a1000b4020902c40b002110a25240c070040361a001c080c0900e480c402d08002c120108104c502c002c01c000692004410606044d0244400c1607600e10140c40360360500b42020500540926000400080b1801d980041807502c02400c00d03c0812140010448501e80e8103082c41d00600 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 759978336 1250 759977086 759977117
    0x16030303020a11060a020a170f010e0403050c030705010504021f0f0e120322060c050c060717030a0507080106020a05100c0306030b16030b1e0d0602210609071e 70
    0x410014100303440d0f07840340340144088082c10740e001b00b02c01003ca9451124404d0b11104a44060788140c8400c880c40701502d00600c030700c1213800300e000d400c10710a0030b00900d402a8409a9030440c0c000100554090350340707108020541c02c104000380c00c250000300c021520302074000806401d10900261600802c840d410070540c0780c3d1500456200788458402c00c982e222802c00414180c03030031041001b03c0310b043e10404d0000e800d500506180d45000e0348507024007104d8918a0500c400380e0001c40c001c1e100700c1600d035286040e101f403400096014800c2d00b800400e042c074220300301500080c030691208c4110351142414001042012605031010401c684010a0b80f503618401180603003015040900041500d005000c004c0c0c1c0a0300710103644900684040c01140075100c100113280001d2014000400c054624582480c607203108600581d51051000600703040f01c1d1a4886081403401c10b2480100940c4814040d19240040c521507000845e403801d05403c905406440710403920401c1410180500c41444011a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 759979586 1250 759978336 759978347
    0x30c0703030e0f16031101021603030f03020f070f111e121e06010f080d05040e0a0e030c0703110a1a0310150c030e01020a0201020606060904060f0b030702060916030303020a 76
    0x1d10030300f1011240c10210040b202c1d801940144401c907a9500400c44583c41743d4000700d8070040b60a41406910b0000e869620240c44030451280112304169003000403450115070900a42032041c0140100300f0040058501030100203d030080707440c451804481c00352200c0c98440c040100e03442c429582c00c28421582c1864600d009a040c510217035a20030b200d6a208102e0001803031328100c440c2400110f41c0310340d40c5d040c4242c50f0b20412402000040e8100014016419944011034000104840001d101c101034140d460554100241003020b54000c002d0800c244491180c60320741049046a04001385450b101f882500614903034500b0b850f03028080001404100741c3c8118900500c025000000c8101300d080006141c0707150000200c01103018607401070300c40d5100154030b282c0141d040e0020092038983d6410494540c0208c2d117815806a2902004624040d0308440c117001080c0e58051030751a42406600607043c201c0040815505911000c1c4056501c00b04081010450307800d41070061fa1380b0031039042100c8 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 759980836 1250 759979586 759979603
    0x1204090f020d091415040210030507020f0a081911280b0a0915140a050a29240304030309060212130203010609020a050f0a0903050709060e06010302030c0703030e 71
    0x1882803070321000c80f0500c610041c5031042040440706035486044440a01c41030300030141d0340650070a44901035a00100d0023540121340101050040b10300004100311401d00d403544000c0300321440c0b64082690701941d0403902c8520b103405614100f00e06922806418941d40d4400c200c00340c0d0f0035114a090103030002d40340e1551340c0c03040d6030000742038016031510b80f5845010707052411041b111120800c00001c0340c0440d920405e07040b034080443d014229211174445034051316010b031420791180e944100900c1c044114201c054584410a41071844400402d020407460003841c624038079044a4004240c1d008144001c00c40303a029506003000250140c0ba800e10030001d014000d20712982000032828407000b00d9201d00003100c12403003103000b800855100c100c0102603010300b07038206010407401e02015680d600b4410140000d04e646240002032565030f0b40380c2c0c030700e0300302c169105020300c41c3c0d42c060a02003011071920035130b480351080c2401d61850425100c0d1004038800c8403805000c05503150100c0d1203602060082d0003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 759982086 1250 759980836 759980857
    0xc090605072619120905030702120f100b12150c070303090206030408030402150a09050f060708030c0307030c05040e0721050c0a090f051f18060f0f021204090f02 71
    0xe480e802e020710070710000c0c1c3c9110380c0400031801d50b5070441d5420649008805079154080702840c02e01c1c8065003030103c60320318407692810380c1c011101c0c4105c88900403c0740301d030b071054000340108140c0d4046050100d1400603030003040142e04001550290501d2500034180c0083d10660615038603a00d82c1000c900030040800300a60224002003400240a5461301850240d40210f0300f4143e21016001b400c2254800e000ca55030125540c282c04010743d03d44841e000520002c003034082d51410606503204041c56104585550f980e640200903c99100d506110b1030031075404500f4294901410300800c0452a0001061102048070300d51068001b0611800030001d0003070314400501c1103040640d0701020507002500000d00080021600041c0361280c0b120b0740003103c1d4080c1244c3d80c500d0701c00081300e90139500300c8500c00501002c68551041160702880307400c000d1003144d44000300a0306240006000c011507108520465104480a291500e4040c1c22101211990040008d1416118220300041c0c003c581040 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 759983336 1250 759982086 759982163
    0x30b100515130b12043f0201090606150210050106020c1e090a060603150311040b01020307051b041a0a050402161a0f0f15060703090519090c09060507 66
    0xb42013011203e200d860041c1d10402c40a5201240080f002c8a01101c424a0406802c0e600d40e002c01c5803504548500003000e150320022846a0f030307a4554405442d1564010b00c0c040d01c148000c0d102c80d9074180301241525481400c14401545000d0b0029914030301000f20a2181c3c8400c40c810103043d070580101c240040000e40001c0e40c1e441c0c0800040e00600e00b0388109404203081860803203216004414032401d43e5800701407031070420040400e0000034140c01c8580b50661008009034404240308010b50704200c3c0000c001040d8600560301400309403491321a40c140015101141c4165a07600c1c0003040c4241c075010340300161120212000c44c3c04a600020000d030515214049040340c00c40490710441c4034002161110110303442e6040111030747c40c0704840c00e140141c5042900c0dc0c0720328241d00240143ca000c0d240020300262a4000a003e0016019600840c028152000c00000c50980143c00440345182441e818503403400c05c0240c907521440300010004c0d541c10146c80d040344601c1c002d14a010300b82e07003c0c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 759984586 1250 759983336 759983347
    0x7060c11011a12070e0c0706060b0309100b09060f010e01050d0e0615180a09080702090702010e0106051002030909091015030c08061510110303070207030b100515130b 73
    0x2c80800749a265420b9000701d8560798608100350f000207030641120032002030380f642a0344469541c886600f00e807200310764a64076010002560b84041c3c001d1801118045c0160654517403000d440422515203240e0303c1e009003105000c0013800d5031116800741e000c030820b00b890228400d0302001200c4604c03e401e00301c5046850a05942c102000000d040c620400c0c4090507200e20700c44010800c151480c40c2c1850640b00c901c0304000074102061500050038092080000606140403503001500c8400111050f0006030f54607203c07211255024002c050040000361008041d2a000b080d000303481c1c0c860498000c1c0102456800301702990401c21500a01140341002000742091903801035003a07451a102c01d40c1e0340401910080b402d801c0100703000e40540c0703038500404011581c0c0c4007400061180e1054580610443d0386107055a1401070006511401541d4042c2c8580360a504d0310f003104e000e020706030124107007022034188502d44840d00e001c2800d43ca007000f502c1d1241c0140c6c1d2206144603180d00903503061040400c1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 759985836 1250 759984586 759984611
    0xf060609120d020f0f010218010c0c0302090a051f08030301091104080f0a050708010c0504050d02030c04050f06031209090601030513080406051b0d0c11030703020409050d0207051507060c1101 84
    0x180c5414400504c0196110030403001c400303d090b03000b00c80c200d02c00440030b60008419580102c6e05101d02d1845800b682c8a02e568a400255901c98116580422184c6410401c0705028103001d080201c0c6030078108a01d2920300307221103039a0701d0205003c0c030300384a0754400900c07030010110010b4400902d6000112801c40e01006480e42e01c40c0c80d58007084820707100700c1d83d0205803d20180240a9850520380d00d05080500d00070800440500c000c0702683c0600866106a1003500c45020b00da01c03e0400541714180c0e800c02c601854030788031003862521042d0200340100d5140e40d45520610307400160034030707010605031944c60707004018411030f0f180140006800140010041e4008019002c0701c415408985464109840455100c1c032070140b5884c0040d1100244000080c280f9221550903d0094100c8207020303106e9000c5400c489001c442600c0d1039201605168141d58108451009400d0542d1043c00a21048002e41d18500a40d04018111600e031078201c96001e210710316102241e0108402480803a10081 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 759987086 1250 759985836 759985843
    0x1703070516140c101403070903142d0619111206190501050714030c010204170613030c062316110304120308090c04020f0408150f060609120d02 63
    0x100401c2c6902030502c80d211185807040d188140118203440f03021503c1c100020800c1c0590005000300180074034000044007080ca0b00c0d00d0390034001034540003050380784070311034900b00c0400c0c0103098000f42f00030030451403040070400b10b400b40d0000680111011a0001140c580740034145100c80c41c1010440031070b0b401f500d409500a0389014100076200b404400e171500700212090915070168030301059040100c4000149140a6024005400c0d001d1b40c1c140019011054203aa00c203901c9080d480301c58140304010300c10284481c03600264544001c2d84944074070350300505201c89400001e00001d607511150146507040c4054840c007400c4085040e551864990840801ca10400945600091809009040c0b00a000088a003070300e010035908656420140d4003102d500d00b00512070020b5001d60b42031100e003900c80d0300140c03540313070100c030499500c9074105034059180c0080d400d4030310280d545400511a060088090841d00440180c0f42c0c9692141c101d004200d031030fa00c901343c0580074459002041c0000e940032 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 759988336 1250 759987086 759987113
    0x3130e1312081005040603021f031409070501030e0c09071218140d02060417070309050a1d0a02070f1202032b0b1806010309050f0a0503030f131703070516 68
    0x1a409500b8080d02d45080c001106c245010080d04075002c1301707058544422180e0340690701e5015140c0450550b030580e0981c0d407100810b0398010641d038003038007084c0301035a01030090f80b5100341090001c04504020400103051504040c00c45410300941485010500780351780c000030002d05a50000c03083c1c00c2424a0b210303402a0651801940c240a0083c41218041c40411010f0149420654001501d024140b540c074040d440482d0482c14402c01400c002810b803510802c21005000c0c400c0e01512002c0424050080d648000702842c03d800e00c1005a400003c50301e410914415030449003610361100c12001c20fa2461040c03a005182c1c5007010020110303460f400d4564680d803943c9141040c0184070b104004d220030f0314001c06c89039144034050400a42103512941c0b281d0901030048080320902c881c890328a5007800041c82c01075405402c00002c002601e44060300c1c0640280c0c403003102413107050b1603440d040300700c41e86003400b4505004001302144056104009480040c2c4001074142d1019215207000181d00a01 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 759989586 1250 759988336 759988351
    0x408040f0b0d0c0206070f081512010e0c0a060504180f1b030c0c02011d030304120818010c0503030406050a06151d040b060301031113020406020c1203130e131208 71
    0x30603c02810142c4042070441c010441901c0c1d0000070a4034403825503e0040003007003014101d06000e031f008003550307a1003181c4550b4052a0300024440100b4581c031800e11a200d0b00481c05044015000c00a81da030000032101220a180c081002400266110002420b0070344005182e241c14030b18809540e12001c6440d22440a13980c034204440090710300141c44c00e032140040640440e038a5034600204102003401c00b038850b01c00a0603a86444e480d0000300c0e04981401d6130a89001b200800e000d4689039101e644410709900c00d0810034403080e040d0342c0d62580d91000600c020a81c1381c964010440210741e540151014002c00080c0202c044070b02c0000920f44211000900080d0740d8000e0b400c015400d2a03c15103096032400b41140c0e145a007107440346c2420502c10b40c1c0042c0c201d6042d040e4016000d91300d06c0030380040c01c00e41d8081c052421200c810000c806d01040302904140d0010024030919181c5001c82d0800c03220408625802d0355101e4502c0b030701e105100c10b40031b0310144001e10040bca090344030340344500c5284e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 759990836 1250 759989586 759989591
    0x204060515030a0c08090c060702060f040b0409201801020705031e0124150c0f0b0105030c030d050a0e0102070e01080f0601080a02090c0f0d06060206191a090408040f0b0d 75
    0x100c5220450303520106030740170015900700c6107c66110381090401040328a0014000c03034034150304501c00c1c9010382d011368490030a010700810244004e221902034849803240340f814103000c54074a461150607512503c0c2165026028202102a90b40d009215100c0100b0b001000d0340e610714403000002910003600800b0000e41c3d441c0400f8440300b81ea02d8813204900600c0c81d11000c3c13200b801c240c0729102180000840c5018403a0100c1c4500006040085c0c2010683c42501c402185514003c240351800131080605403094004801c1c00096561100949407403407036518001d03800c40341038070050341007121541001803400c02440020408500c002070310001e1020600c101d8039160b994030303007860715010102002580222030a02042d000c2070100040c0c402e035004a4002464010302070710b000210303059a845540540c02a0081050300300181400210b01e403e0140d040c000601c00540388080c0090007a2224030417118217010800340107059003600c2c003030402406460f404940303c040130b03260794204100301c002260 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 759992086 1250 759990836 759990851
    0x230a0b040e030d0e0f0a02010513090c0c0b0906041109152808030403320a0c030213020c0a1e0b0f1b040311040921120609020a080a090204060515030a 66
    0x40041c170b980305454a07201506600c511640111100d5028100d0007005e5202c407100812001c08611845441c444152200c0c1c3c10b8501510741040c04a20042000416400007070800000c03c60442c1c00c421078000403140b0407015038420300071480c40385000e080346811281c01402d048003000e40c40701c480413a010b45011221900d070342c0c40c0c1146e984d10503404010b024140c54004110048440144020050995a50382e8071040402a5043c541241040141c48907000520100158140321456588250b02040c0941c03800b500c558041750341d8029048010106000010004803690186541c0094181d20100b00d8405060a2034600740c03680d4103807101c0310612040100c0d030307028080d4142103404507075004400a40c4034032100c0804c002080072007416252041e8851071414020b6120314504d41145150f1074240150346001c035000708031000c0e038202c00a1580b042100d10344c49a0480021644030010b69800308200e05180701141c00350600360300c07075500401c91000940010384444040d43c825140041f0420155 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 759993336 1250 759992086 759992111
    0x90206250606050d150507020a021302030f090d0906050c031210080d0f0c1b0b03010b040e100506090913050312150a05010f0507050f0f0601050a0603230a0b040e030d 73
    0x1301056240107142c0c12641d00a8000c541c119000341ea44035417940103480b00c464072500868071000e5201d91010249a00201b00003072050b11000b082d402c212098028000402d8460003d04100307000e0041005221000c41c01d40c0c28070f5410811913460321240b910142e03003400c01418a02e8540418060400c241c044c009400310024032405801501c1c000943d50281c900c0306070f407100c2000e0003650580071400d0b03038082d6010480d241d8040c0214020025403400540c2c2e10300d0048201e041c158060500c0910746000c0b07204200c00c1c1c1e121003e642e215032080308c07215a152540c414500c00000200c2d00140035010115180400d00c00d440c4220344035104207009003031000748603030400c91442e03900d0013010b020402d0700a0b2540310074403480c0500031440c816000c07922403a914070910780c68103580c80d00050855000900510150801c3e850f008003e000c03a080c01e2100c941e0811815450b8544800c041000d82c0e40c20300003c00c00384c840e0f0030485924201510030080b0136442071045403698448800c2424030740c203103074035201c00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 759994586 1250 759993336 759993349
    0xa020607020a1a0a0e12090315060d03030b1914010807230c0a050f0d0908030307210f02070308040c1e0506090f09070c0303060609150309020625060605 67
    0x107a42d005240c0010320030803000e03040d400b590241080c0340c12961664003910508040246c6044442042005a181c08030903080514000201140c0d92507000d2090510980340c0b150400740614951605000c203001080340082101034030b0700450710011408400c070000c1c65642c041c51003400e060003a41c9100c410b0f55102d40a88402e80c90000600038a0882c08000320314080920107007003500071140c16a00d20b40d6498403980e10304076401200744842c2c0c011110214065401c5050080200400d0021f54103520b00031001500c84240b6010191024010480b810705a941580c0b0040000003102d03011034580382d01d810014010b035400c407011034103600119004507001028001b4549007000008214039010300301403c0c803845070000005607800444850092100c4d0b075514200c948140ca41e0780e5449400c001609000341964840e41c06032007070244c50301003800406800721101a058049082c0490700440c40e20119034180304030303403004002d104a008144145002901102102c41c05100c05002d16511881048403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 759995836 1250 759994586 759994603
    0x210050309192123030108011a030a110a030c0311132007020f0a08100b01080f060d15110705100507021e190b0f071e110f0102040b0a02060702 63
    0x500c1c5500c0d420b401c1c00111903c0c3c9180c100b0b41618000d140e55941401d803460500801e10800703404400803005200c0300d2404d10800241d0212500390b03c00e2400e1742c0e40469203030b031101c11002c2c08004000c07507e800713a6110643c840d00103540c44100d440790380b540c81c100200075401401c959031044400c070800ca0300510250042da0010310104060044031050b50341c402c031a075032040c0d504a800c00800c80b11000c09a44150701800200f0403100a002d042c0000d180d21801c441c0800d404a050004000a0212248482da0001e80c40501510295886207107400c1c02400c000c00c0c402401040c0e820300780d1650045000c2d134081c101d414030542c1100e04130201c0240400554604440140040e8000d000030030700a1034900340c1545084400c02540c00360310000e1682c030a19200500265101454003041c041d08444d90f02609500c01e00c40d00d440c0c0c1c246503180d40005140e81d0011140300c00c0001080500b007552006011b500c170076501050085642c1d03940c407141c21100e0342124030040050f0240c400081d103080e001040c42d54 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 759997086 1250 759995836 759995843
    0x2d0c01140f01090f0b1002070302090a021204021c0c032a0b1e0c0601091d0d08070302030a240906330c1a0108060108010603050c06070f021005030919 66
    0x800c1d6070070804150024074040d0071040c8496120880ea001035280c2000028031585a58050280241140144000080c0240049448500c1004101c3c0110180ca180c0794019904030342d141d01000281d010100300e401d04803c081c2030404064400020020302003643c0c0c401c08070780110704c505540c0c1c444e240000030060b03203e06890058104482020703200803614448510010b050031608280c0e42c90b46c980e2401c00e00b40c01c40450700b5519140b26110b00c081d50a41100820008000e0076a240d540038014001700c005813000301403503000b00100308451403d03000403004011400b02c00c00034400042d03882d071505070700d441101d141d1440c0c4880450b04000c587e4042c1d0508900d21031000a03c0091651100d0b1103804026030b0041040501c08240083c0c0d0080290031446040c0d81c00030740035410900c0c0303542002d0041e4407504040e0701d802420000204041150300c0c0c580c508030703151030b213450803401e0003900f205000c00300a501c12100039010702a10703000800355024208038070880e2856850035494011f200300503003000c2d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 759998336 1250 759997086 759997111
    0xc091509120206041a13050d0201020307200315010504050a140c0a02071a180303030610031a091f0602060c070204090501140109020c100c090b2d0c0114 67
    0x5004021501007880030041c40a040289050fa0312000c8016007100f50046200c05103001808001c803111166005000c1c0c4070807250090480b4441d40080c1da24440d403407001740003c03030b041d03084403040c6603035a4600c00007480903064400c03145000c0a084031400090007038521942c5030101040d0035481512805182004000094a064540003004038164002008000c110321407208007181c00e48030350300e150000f5100c03a19055103505900341d02c00b81030100b09200a00a03401442007050f65500c10a40340387d115102d040004642d00e1005d0b114400c51159a5900c0e0044031803414448020822952201030741031024203402c00707030707140d03e0202e0b00c0d223005407039020010400b800000054030f01507010440f1180b2840002541d07410b458002c002d521070992103401c0b181d50210781076070b035504141b0005401a10007002040500002400541002402c3c001c280c1d41500101324140c1007111200b0021405040030569852402c01a4014642c0d03032040c82c0d448515400c080c0ea1034031b00781458042500800402882 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 759999586 1250 759998336 759998339
    0x31c1503081c02131d040804150201020705010207051e03040b0301030b06010c0507060e12150408071e0f06060e3d170706021902090411040e010c091509 67
    0x180100c1da00480118120300b0a4042d2110128000d440240907550701e840706080d00324541302010014030540060b121440c4081c10402002407108000c0b03605450082d50031401288a41c04107e00901410074020250740c070024616042c4180007803038040d400401680d0002c1a40503030030329502e0340610301c6000c040c40b0382400180009035025454a501503818540706910803020348425240038911f40c020000304000d01c000d20954201070ba40801089502030007014048030210b20300d2003125005001030301c01000411070b40108205001c400c0c00c01d846800103840829800d042c1703440003004620040303a0443c030701078000034000c50555032584500d20308141e903180422a030b414010820881400310701c16210442c40e010010a1a0880740d01030484c0b4820300645443d41054285042c05c0e68000f142958072101074007443c03020304c1e000c1810040d81592004002d407070f0762501417181d403084002d45611a00300307039104260282c1540040c1a27000c1503960075070100c0d502e1000003231411040344114000b40c0c0c00c120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 760000836 1250 759999586 759999593
    0x405030601051c113c01020a0c1203031b03020307092715121a010905090a14100c0329060904020c1011030a0c021c0f0c05010e031c1503 60
    0x81c0131541d000040d00070416030076010250181110305900b1010307030305480b501c041d010300182403c100700c00d0030a00040111044a451b0740303028100c54420103101000d884483c004141c4a80c000c40302c09001c9054005005c0150f01008d0040d4008a6125000840c0c0d00d00c0000d401ca43c800d0503290700980340484415400740540080003404140c201c2c82407003c412400040d00040c1d004428206a001c0d00e404a102c072181056014202d10603405000b5460411051046821000c200c1c2600e4640c80004080c00030064115982030941c3c44001076126440c1c010981074054164021402c003001c2943c1000303030301001801c85e407440001e07103111f250401c0c0300384502c070402e090640c0107112044003102150745100c1d07204130b4003043d11207100031082c408401100380300e8003003a68002c0c121000114000390004805e902c040c0340d8545180715000d810000c8200040d084a03000303592403849a600700c030092194440420600341d50360301802d21580302c0f00d07518001001c40c5105102d4104d0382c5031915100f110341e91442c5c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 760002086 1250 760000836 760000853
    0xc0f03070c080301090c030612022206051012050702010c09060c0804091d060a0b0d060b01110709021b1204090c092705070203130509090a15020405030601051c 70
    0x801a4061162003881107000c5000320018500800c0400004218109481c0c0018240c8141e60300110303070b48800890180040e520205400b0518140000382c20241c8040315024002e8401c2d0f522040c7c01090070140341e606954070442e0b003030600c6400101032280b5110ac0030102d00b00c5983c596020009040b031801408103510668003592807900810006050030f440342d800404980b80d800304072800103c10000ca039020702080c413070345a00070700040c02042040c0c2c548005c18000d41c0340d00300040100d551114500e646038040c40072408814404800c5941c0c040d10b40360b220000390301c0000c156099410420480c4d176100740014040101c0d494134030859007030034a801d1504001c1c201d50311100c414885040004114500040e0a0502020030505418000e00f101110310b4100e07003010700042d0864104000500c80c5110f81034044013220426146032401d5516244c100f414240d1540005001c40d444440921401e90315401a10070f84030202e0580c0c2e21071340d0307810420181000385088004412041004071001c59540f0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 760003336 1250 760002086 760002091
    0x120302090643050a170c03030c0a02070806070801030b04060204030b0702010b130e0c0d11030609070f0b0412111f0e040b06030613020d020d0c020619020405151612080f0a050c0f03 79
    0x88174181400031030305005085800c01c640301008208085244e040c42681048444010015100a0071203800c08080081030000140409403100c80c06c0c0b40440c04010355581140c005540003c034410150a0542c402400f80c19010251403103441032040d485642d03001d03446190403480e07500000302000003804050002e5907441c0702c411344094281c0180701c41a80c409000b0b0903c5020030344090f20b540c0303050040d4508080416000b01010500174407090028405d4031404200440e00040c2910b07544201d1400030383c03039114448aa0110741f610390058500341da0810000b04441600722001e12405002d074080c00b030039010855001c0e51124400380c6088030040e0950042403ca0605d00015203400c1d81411034000b40e84800b1003600050f8006000c1107c1d08945100a60810a0b590003d42c5810b19040000360703180382403413410401d07580024000c044120700c0306200c51290350001d0707070540e00c082000000e00714460840300000306007100302c0001c003000c0c17080c03007031074403c00f44e49424a0520303201d04238801c2641c000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 760004586 1250 760003336 760003373
    0x3030b1201090b070f0503010b0702010c060b0622050d0b070f02011104060801090510060509010e220c080f04050a030c0503120103060522120302090643050a 69
    0xe61600c2444440a0080d003141e18014007808505003061400108440341c8203004408114040c00103102c583c001c441114003640c7c0900c1c1204500c8128140035000b0040309580e00c0d071000780065400480f80c02d07002650304160710644410210740c2d45500740701032100411001803041c0804000901307954010f0400e0301045a6620000840d40c1196076411429485500000007140c2548010000440b0341c0c000c0d070750f1040051400304a45468240c01070128000e0460407414400242255241c0c4d0b02e640050070b400104100d94007030080702e01c0a280000b07000000101c0001008000080d682c1000110158003030b0340d01600030000c2c090507403402c441150032008116414041002221311005c52400303c580a580107007800681820b11624032503410032070484240410344c1015001010805480781014140e129060140c1d60380442d00c00102c0c18400c3c42c3c1d84040d083c0030611909880f0400e44130728062086c42d616520380362043d551400092603440d010081550380070b6000d00c40000c900001e2907148854 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 760005836 1250 760004586 760004599
    0x1403060f0a021c0e150106021c031d01181a01030b0402060f0706051f270c020f0f0c03060105150a0f030b03010207050c03120a02060a05042d03141603030b 68
    0x2080d0b9209040c3c40484e40e80c032000d94000d00103034003030940403548031703004110a000401000d51949155001a0f5000ca0710000340360351800d90380710310001a071007003007501d000400070403e0115401c0c1c02c00c10038820701019a01041c03c02102400c002e801110790f03050b20b402c519400c00c0c2d84e50707036400c1098075406a8440e02c40c550041c01000c000618a0103104d0264148084100c0140d885c0c50200060320301c1c41e442441c1074405a41c3d21408500c0e036001d446090441d509001c200d00c9500311003070f45416046408140d070b52281e140e00008100b80416007240644c012400e035500c1c1d0366200100001800b00e102c0141307081e07104003c041034050042e0003c4c9054a020b040108140c1d052200080c2280c00c05c88064610790407040700c12602d460180040300348241e000f80900c2c1440c141c100006d50340c010082242c080c00e56200042400d0143c4114504605440461030252211100700082105510740c4012000708445100180c50b2000c08010b8550582c841c2c103c010160500f0f4808401408040c48130940024 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 760007086 1250 760005836 760005877
    0x709120618060513021002030415050c01090f0803010303080f100e0907030b15040605181807080706030209010f0e01080c070f061109090c12010b071401151403060f0a02 74
    0x1200d43c043c09100e4a0361004c040504101c600601c040d642143e1121821500f04210a00090028440c80208043c06142068503001c001d03000034014403140c42c025144110803117a884c10001080000d5050f20b00c44d50b04c41d801a1070740310016501703035801d03500d407000c11420320010b0001c0310750205000c0d44a0441c0c0c2c02c0302c2090b40d5a480d01ca920781421b44007480d841503030101100b00303420107000781130042c081030751003076841c500080380021002e60190002c0e00d80c0d21792914490b4140c0e0704001400150000760244d80c640703a55800d000c1c0017903200d01c501a01040840c14014566801a0350090720320b00c060f141d0a2040c0d458201b24a41c5900004084954909192888010800034810005031080000301180d45010480405c40000c5000f001b09c400c11000700011020790700f614409904498248000c04c0e11591503282485001c00840c0480f202d66180c01448014400005901c10456121442860b104c250000906403155422200440340d000c2c0307a4041002c0105170f078004c103400f0801304040c01c03002 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 760008336 1250 760007086 760007093
    0x3070c0f15032a23070c050f030a1a06040b01021903050a02010f0e070f170c0108041518110406140f03160e06090c041815050a031a0709120618 63
    0x382e008100c1000a03040e44103080042d80030b4202e026154913445201410824640c0e500c101104090050314082c0b000040f501d81c26032400c001064070316500c51a40f228102e9000321510804004035966441141000110b40359940082006581c0b84406019130460114a48041e982c5501144c3e002d01199641c48581295201510980c203d0742c102e440a00566450122100c000d00071075044500410a40c0c100301c4400c410005a283c48a50203003004050b5596900f0704e00c14040395001002d00807030034002401d01a000210414000a01c5600010f40005026052204030b0303c442c003620070841c00f180c40c5140d0600c8c00340300031490880002c04032201c80e6034410303210396000000d9004603090000d10061001c146456018141d1160005096904042c6000828003a15010004001c403041e42c0700461601c003031111140e038002d0100a400000c42d141d0b6880c100480c40300811403079641e001e40d0300100b4500d0f40b1656100084802c0203141c00b24a00540d00c0c0e44000704444114804041d043c1c8803d107000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 760009586 1250 760008336 760008401
    0x9030503041b150519020607231e090a080318210a0515160c020d02120d09140a060c14151023090109090f06020c03070c0f1503 56
    0x1c00f15aa43c2c2c940310404190350034a14103085105100b55042201007020080d400b4840b03050302226003040e15004031201d00591810b00c80c803c107400006d10010070001400f800300000300100d820549060007411b0f0348114160701c0b4000e002800001001a41c900303006450003e0105003036003403081801640c18440200da0b403070451039200c00c6400d40c101d1502e0b02038000445074160b40c004103a075841d503c40300c40b942c002072000c0300305500240705006d41952030701503403a02c100303c48112100c00102d40b0043c0c035441c0041c0c1413070428440c0448042c1209225125402d202d202e42044800c0b6441d8070f1880542c41e40c600504500e443c0451100382300e45000c3d245551003e406541c015002c1c0c180307607520f140c00c00042c03c108440c00700e813078a15004000d2001010f0b4561880030350440d401a1800648d030b0010b4074018820f5031030248040c1440740045020707200c01c1130100041c020184941d4032403a40360741d43c1c002001001201c4c4140c021880901810800d0a070203902b25120100c1c2a0301d00e600c0c181142c1007680c82 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 760010836 1250 760009586 760009619
    0x2e0c090816030b0f0c0706050c1308070f0609030503030a02031f06030b0a051801060503060111010908030109060515030c1b0a1202011d03030606071b03060207060b0409030503041b 79
    0x10008007040410602102c0480a40c105118081c3d59195140014010109108004c030042c0044c4e038800010f144103080ba01540c8104c25140c03220300c4100e40e00c80c64640e89603101c1c01080c01c544000e400000740c50380a50075030341c100d079801701c0030714119510324031443d0094000400c01052820016074200c02e580d00e14511001030300d8035450014140b100801400f420003000d40002d401411003801c400540c0380c0e802c03440d0b4111039040c90f203140d0f2640d400004a8a80c065809000c6c0e5545c24910303990100850710380654160381c1d00c1c01c010800035580d00204002203d0310580d10059080401c0451f045c00355400007030039064010300300040c00c480d803111409d1030b0240c0c1600aa65140302c0e203030183e03041a828000c1c440504111103118100034a040c003a5616840041c0903d40311307520008105003002101c9210800c0340c548200702040d420f64030b0500388013940c090001182d00600c0c02078211058645440352017401c0350550341e010305650340c503a21407a8901d40240b80c1c085990341d001e00010802e034480101907 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 760012086 1250 760010836 760010863
    0x70c08010207050106171c0203090d0c08120a0c03080703062102030d030204050307060e031005090a03110d090e060f0a08010207051b0904080a03060b0414032e0c0908 73
    0x580e00c00b02414207908451041d00710820a90006116030340703540380090b09281a20320620260b042003080c034010381c030b5841103407c2c141d08100f1020090f410f100f0305900714002c0300c28110640790646000c003201d100c64803589070a0408124280100d0020034465542f0301d510440e00d0400240c0c5030f4031290038840c2d4580301502c5a410445421044e401c40c20103002c031020582e030038201503050074200720003e600c80089004103030421440d440c480c0044d40d401c11079403500d4192000f0402840c2001c0c404203841c2c6c1031519060f0040382e52191800c0301e241c6d0001e0700d0750010381c042da14100d00a00b840c408201008000d081e95a00c00401d188031119603969640310b01c0100000000143d584507940782072800d040b582c5045c840100303402d03088000e540d2902400164442c1c0e01008040e81c1f0b0000940a0f0000d15241c0c214010801000c540030078441c04001c0e0300c010b4040c04070119000c0c0d48050800d0800326100300118a4001d64040900310b034a4041c3c2c01041141146040c9500d10fa9162003900d031600300b255402e05d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 760013336 1250 760012086 760012091
    0x10303020706210204032d110f04180b04020a06231c0c0e0f03030f3405031c052a070512031501050a1b1106071b06030b0a1208070c0801 60
    0x3541c002c107410032003034000c075414800300003001c109846000c100c00646108c140a2980350002140942e1190b1200581c0b4400c0c1203819000f00082c00c0c0294290300846040b4020240200f000c1a400d0007038030682e4944100b425a0030901000c0d01c61941071f9041000d0744c401088212038407a5508009011300c40e42c0c032140382d5400c06c100007148100080042d60500c218001d4100700841c60625416a086925a1241c00f13130b4500505d0742040426003c0d11280741000107140341408800800c5400301c0240088404a060102015a251001030403500c00f6601100c070002c07201e00c1d400e84815081c61141c1901160321025040a1310380d101d25080c14024108030f00d07508000420010f0240076070a600c10b103400d0a00e00036041038620600504000c10755502d501100c428002c0100c200084a600203c0c1e00c10302a04440c1c540c0030340d1900441380c2c290107000d803c0d400781460010a01510a04c9003d02e1283c0060032554250b140c05040110800000760503602e40004022550106441c04580c400418421000 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 760014586 1250 760013336 760013363
    0x20a121202120a08011a04050d06050a05070509030c010c0602040b0409051b0c0a14161202031506030706031e0513060b01031104230909010b031501030302070621020403 74
    0x3420b10203101c0348240c0440092041c000710720b500c0209981903501481841e05c0340122404030340c409005590019a01000b44031170300d0200641508881c1c040da009080034049520b500c0000d48050017071044a07034259200b1160703d10385600ca02e00640c0d0150045c1c0c001490036454603c10841e55000d034020b010342c3c0e0784903814025a041501303c40221100c0001d46103043c82d603031406142d00d90892003000792a8040403c015203000f08148456540c0101c0315034401c600d560b030b0f10b1209602614910069100380101c64401880103003075087c00d0301c0307508010b025106903810443c060b0001c00c504484d04038201120725007960803010794411207000e04088014400303010f106140a60940d8a003440f80383c1050709144101c0740404858043c0c0e01511000c07078a904030300202084404c0303900307500702d25a54010350110500105c02d4040d448141c1c0b0440c198103503000002c500340d000d41d07000e4080c4001001688024001c026a5119540b5040450020310200c0c14807402c4071071810580e0401e80094611181c2101c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 760015836 1250 760014586 760014623
    0x80307030515120c0f06030108150403050f030709031a06060d0c03022713020f03010306020a120c030501080f0c0d1211030d0510050910090b13091b1e060c020a12 71
    0x344120102206c44070300e55810240c00589825043c2c00e5080d100c0482d0020804040c082c2007601c900802200c0300c0c94583c640f40074000d260703000ea488141d95410f070b0000c8181800a5840c1c81d54400e05024104500c1c1448042509000303010b0340340340c0010194280102c230381c2c0c00c481c60707059030f50202c0d429400500d0700c00c1d60081001c030101c00c02c1000f034220300c104040007100106506490449800800046e11804282e0050301c0d0720f15058503800c011b52614081c400840d805500c518183c40c5410300b04c84003000d40c4c44031607942d02120b4604552150301035032004000b42c14101200781e08041c610f0000740e40d0b00000c107803d1a50308040c00a980c0c89494000b0001c00316500038400c0000c1004460f000c00c9404d10307142c08000042c05014249001e5151950000141c9512220b400040c81d107500c104084001800d00704180c0c600e1011100205124050001d408070303c40405808200088424120745484c05c60152480043c220040b42c211061050000c1c1226080710380040c1e581c010600702c0700d0038104c9007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 760017086 1250 760015836 760015849
    0xe030903010e2806060b0a0305041203060302180a060b1801020115210311031c060905190905070512010213050303130306021e160519080307030515120c 67
    0x20b202600760341c00785501e1200491904005000b124403038804400000b15810404040c0582e900400c14000e40011048100c95041e4801c0f031050380241d501508180d00f811f0700300e0685425100c083c0d4451250f25a00c021b01c256420069049100b5800000b003407071346c510204025400c40c80c0b04075400084a1000c2c01e0a50302802822407140c070350310600d001a801c2081d181208000706911445040380308100703008050041d02c0c0c0e011005203c00840c0d0b141c80c10024070003560016400c03040c140d28204840098107140c1070141d1070183c031154555038101d1825640440040101040513a0984160000007401e911000300d040822450600096600c080c01100181c11680591001340640c1c41005501c030510100314500007078941c0498090780ea0758020407440c950182e107001c214001000004d03000d004d610400c8202c0c128170300c03400585e0101d100c10200300020407101c0d0310250200c1010000110000c0c4254080b681c0001d010000b0b443d80200365012074200f000c0c511001c000d035400241684c4003481c204 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 760018336 1250 760017086 760017101
    0x20f07050f16050906180a150b1308161a070f0c0302040e0c010219050c0619120c0c0b070309140105011809080702041107050f0606420903010e03090301 67
    0x584907204c05041c840c0201c0c0d61142000e24540c91a0b80c80e1000c034030515425041b5000442e0990651803405440c0c44946000b0b510040e862401c1030030b0407100092134903010a00980203200700032420000c5142081071a40d4038030a1450111800d010400540000d0003c410740c0b02541c02024850800e508602c1840221081c0302544030960317000e00c03811220350380e0004041c41d4040c40500c1d03800030301000d0310700b0714507041200e10525807050020590340105070a0038030101c0f806801e69241e0b1000f0403103c6000b000c54036801e07401000540628401303c046462000f11035044001031800141c0150181c0710302980302008213852007d42d44502c0100164150404011441000c540b41045080000d569a0b02c152040031002801551075034010784555021500b620155500700c4142c68141c144010b6594840504580e102c1c03091803184d0501000d1014403c018948200c00000c2602050300d182d00b007a04030080800e00482403404000d022890348003030040680d0175907444015134a0b00340c0e110405080d1000c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 760019586 1250 760018336 760018339
    0x103110118140303040e0a0509010b0d0f020402072d050111040b0d1805100c171618080a030503091b0a06030b03030f03041109091b04020f07050f1605 66
    0x148051a40301c216400140840b02c1c0210318840480c1a180403c1c210b000301d41c0240441c03042507017000608000342c2c200c0c91043c2d5803c002000494010b10030009503030150040070380010720070401080182495801016654000c130703804c51001503410200112925960710b120001d403452140b0504016007401803a000d511030341c0071701c0e00f442d003024003100c2d260003020701031400103072940b140c001c9207130f21075207581e04103030304481030300d410b64400b00c4140007400e0001403050001d4034019012080030840310540b40101034002c40e450218440314000c070740310040782070307a00283c0288810014202e8800c00920394014466100c0c3c0c0d0b260f103000701c1c03441e00b001c5040707084107140360000ba0002c00350356806500900f600c085d402e00144490005d004203255000c2d1800c0c0c1d01641304c0c00024070041c04141a40800100c80031110510665103002110303458520203100c3c00690508070104a4592404d074016003900603003420800e050620303d4aa292600094040c0340d1810f0300601000d24005015031200e4025040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 760020836 1250 760019586 760019597
    0x106050a0c0305070602040b1b0d02010b060a0c170415110613020d0303021e0301170f0316110901060908070602070b03061314160e0a08210409021201031101 69
    0x4200c0300074080d440c0300c400042c100300000908a0411206a065502901d0303a42d56413038a9907070b003a02824034005112003104440c490941c021680d40d00c14013804d00c007401c0152045007000020f400c03c3d248000305400441e044038a2040d045032000705040079200030310020b800c034000141c445102406c0c2c05414610326030305800403000c012045810400840d400d5034181e4409803442c070f06040c1140280140c02c0b1a0000310364201c1c000d100c100094000e94180c0d000e0000d88424000c0311054240d03030b106440107414103600b06200c0f2006158410003030405e070b60f004441816410240100088408100f60030010102c0d403451024002200200318003009402d0b40e00040c5a078505003a600074203070100402180c42a20043c01e06080c2d400e40b60072400c003190070303551003100b5810099189415041034074424000114003030512240b0b442c2c441001012a031451000d05a1000b00c05441001d140d8080750070b51061004010008500145200030036100e41c0c0c501840806505501e842c400454800724503504101 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 760022086 1250 760020836 760020847
    0x10b090a02030a0e07030215030c0c010207030507060b040207030e1002010f1b080108062505071b030227060f0409020d05011b0c08030a0b130c08040b0f010308070f06020d09050c0306010605 83
    0x2c036010303020b408c2021030440702070301c81d9202d41c0b0402051082c1001ca02c515400812070f0030405400101601c8400d00c80c55007030083c0e1120300309100480c0a103600140000e03080095540c41c50401e21035400722000c4920001c07460500d0101c01d9002e49900304051511180808100f42419a10172070041c05050214060800c0e400c0031103480c002d01c04054040b41041c0000b400075000a4040c8d001c84201e1980004000303800c038041000c20320006094807051f801803040707100941c20712007140c0e0307410102500c8034103c1c013198a9010900800d801c42c10901500b19582e10160005170380c5411451440c1d9201e0000401e902811031450006c01900707a10600502c5003106104001402c0314050f00d41c00300f90f180c0e000806150090004008207a81111314000034680030b410304065500c608054400d40c000d40d4402d029071103440009161010074800030b001400c050020b82c0005107034041c50100d06006503805410419104402401c462081c0030440d9030381c3c050308821005007400e000f00c03801880c06050650410 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 760023336 1250 760022086 760022089
    0x1080705030c0a1701120b070e0109030f020409170705070801050c070b07090b1308011b0c030c03090e0117010506010f1d04110a2109030f0c05010b090a02030a0e070302 74
    0x501015001c80c0b8030400108031a00000d01c215000190703070610300c0e400070f0656951202021004c10300382050b00e16112681c002080c0178050f604000c0011011382d190b48525140d505d648620004411089134410303111002d00700456501020440c0c0500660b141039511089890698034056056000340e0850341040100540b211000c0c05840740550000075a180640e5592411152114250002800d48001080042d00c1c2c00148111b50309951450000f000302114184510489a4001031310380006480c0001180000b441030759200b101c0c80c8030b0b0801c03407aa0750b1981e02d00304001500340c2100c0444851400500d0780040c0c24059990024420f007813450a15100300070042c00403071401d8413481d044400b0910134089407141c0e400501c001030402c81160702e64018840060000c910052a559081c0d004c4419501d601c0c42da20a50b9505641915900d000e4804140255520f0100c5001030311306d55a1200060130607103c11008500ca03910b18017006076203140440e114821030300300300380482c420391002c482800107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 760024586 1250 760023336 760023347
    0x90102040e1012022e08060f060f0301171e010212010603050615090f06041d0105091909060207060504030e04201b010e3c0d1202220e06010807 63
    0xc4c0c0c05032a204809000b5040c0342074088035110080001220b410910800250320005450080c0d00881d64410500250010000c50340242d40e031001540004000401c20344503044c550407040c6414200b92880b599102c2d814007800c800043e40070030540d400040c1074181400d82200c0c10301410076420200f0241c1001070114010090b8240401ca0011000407001c5003691405c41c44602002c008084a5590b030f00c80200d46018070a00ea07900510070040e000108440c070b0701c242c44600c02c02c410484903500c880b000303070071801403c4001c105440300c940c204040400310f0820301525101d030b8003d8035000d134512840424802204e4048040541c2c095140080f0748002500404513628401c441c40d20130350040101c41481d00506200000800038490460340341c18039003000e0051000708090810304c1503202c22a11440c04d905003140e0361410a42c000d00c07d038610060103000c00103103001c801280141046d0f41c5001d012400d01c1400204501c420522108002d13242e40c5500d15a4840b1003803800f900a81002d4001a00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 760025836 1250 760024586 760024619
    0x20a0e010f031503050c0406060e0904030804030c061103060108010b0915030a0f021209120a0905210607020109060b0a1409090a0204140610030e120f040e090102040e10 74
    0x100078001c03540460180c42038000e144500c0e041489030142650328904195114118074030035009500b002c00000d0b40300e005019180c080c01c0041d0280c0c203990384580d807c13504080001d20441c00d1100003091400450024440c14151440c2d00743c00560302d041c0b82c00050920007059002d0040c40208011255003a01e81c9910000c012440c0400d0746d40300d44580301d54602030040000c03015103a5201040c1c64005501102000d40125042000d0780d41d90740b502995404140705402d00c40c0c02042c081039003000b141c248604040b2100c0c03078503101c0d040038002001c17000e424820f0903030b66840141c1d103070036143c0300380942072107a90000c074001c81e02c1e000b400380b0342250640754441d41584107100d241044006440000184044e0302c109a00620800c040d25103503403890740507402500c3e554020903031201e102e800203020b031054503149280c2c1c4004103211b40300041c0b0840316900000c842030030a101880001800c0c0352210000d8000c803100000941c4460804482c00010003004040c01e007051009230b0f00704034548860402c1031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 760027086 1250 760025836 760025839
    0x40206180301090f0803060a0617010302130902090a060f0b070519030507061509241a090d080c0d080f0406090327080c060c030d0203060d0b010306050f0a020a0e 71
    0x14008080103001900410710000f01030451042030000c6030400c0502401540b01e00802c4500450684d11010203c03940029586070080101001006001629201000d41e544444512011620040542c00b05403017600660701c1c0030706140c443c0010310042e03010030b0340f000103440000b00041c20b00901e9114a591440204040d000d010011030f071017400d1500c82c400710346015030040300601c00d140424444240c0904a0f1042c004250b203006855021005021903100c0748044580315444010304210100d1911114940321504903401001030399440c0d02c036400d0080d40c1602400807541c540034500a01400c0c040d0605038102004440000c005889114440503074105400142c002400207a500d01507601311080c0c030701907071241880b51514034003007039100121302a03807444000c1d5140b6074a1141805014011042c080f000d40e0010322022b00c0a03c0c595000d50342c00003005002e230a0305007131501d440c0741d10300082c0c1064407032a45030342c00c00c4008140c2c0310190390003121402d81103140207090540101030000014859 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 760028336 1250 760027086 760027117
    0x2010c140a0b0103030504060f320d060b030a14040b070809070b03090c0a0b0c0705130906180b070801050a0e100e07110c060301030206160314030f0109050f040206 72
    0x400030041040341c0111194490050849035840c1d060141050f040703841400c0025050561005109104841d228400d800080001850780344e403c44503141500c0f042508a4048024411140ca040941c000d03900188648000181c1d00e0811705040d40541c1c0e2094240d64291200f01e0501c8009464442c803640d010120b0320340502c0645072100d645081c08d22541c45004000400320501c81c901101003800b0607004411151440c0b0a5aa508a003005000e44245001950080340042159042c8094110000025a0800200003030300396070700f1080341d80d88a40085041560042c50003000480c581d03003500030f40f40e03042c00159980340200080c0c4d101014020902c400e00c0700d4000c507110f4919040418041d01c1d1407080b4407114905202d004048900c1014400c54621a12000c440641050707401c0302d040e40c3e000780507140383c4903a44000340302480c03107080704808001214210421740041003020710f006200800c00070a80c1e5160103c0c0300c0540344003800c2c8040202049060000583d0b800e42160130704002d24140 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 760029586 1250 760028336 760028363
    0x1203030f110702061c050a0c1b03050a05070218041208090a110111030c010911190e0604020f07050102040b071203180327030503040915150e06071506030b06040902010c 74
    0x140701c2e15400f1208903410745040805102c003006c2c83d50018072303055240380d0701d90b2780320401031800300c02c1c8400c4500c0190116904220010140b44514014012180050000010782c004140c1400115000f00c600351800e44211086d0001582d020100e603400c4000313080142240e0300c898031456408107448101da414000188600003024500f8030955003544c00b044003c22a14203030341403040c54200d0000c4424030400c14147c0d8803400302d0450f140315041d40c40703c280b81201c581d108401d001c02540f00826440c02c0400c14400e640003c5e03c00d0004001410340150741d103480e00e515281000e000702c410000d482c02d05041c428006c00040302140701d48045909890685002405003610400501d03000382c0170404056003c50220910100000500131900e001e6000c00001c0c4a02e07200c00c09103100d5004d540c0102500310b064200580c8601e1420308081802040c192401e111036496000601c01d6401043c42562108001c0080c0007c03810802c1e440441901d00344510492640028000050104010a00180100f0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 760030836 1250 760029586 760029607
    0xe070612181209030b060a0303080c160c0b0403020a050109030302032d0d051608090d0f05040918030908061e040507030204020c2506050316020f071203030f11070206 73
    0x2601c00080e40c0018001644501000c0020710400d4580400c0d5408100900418810b00304070181c3d404880d05591000c0c3c5640392480030b00100d601159200c10f0b8031154011680c0071a41900000d0028080240403e550764178500c140940b02c03080750700c12414000c035850b0800100b40c021086544055408205258180c1c080d241104050007a00c0ea050784040046410300d0a410103a0100c0d0249000000711003126941c0b00b41110409030864000049420101180301c006019182c1c1c80302c04a640d0408071300340707078480050f001214000b50301d5410749840020490140750b04948081d0107404410041c1c00c40c0d10b0255000380e665441621541d41d94003603d00001e0601c0802d000f040c010b1507001700300355640c4085034900c0d81d07641c0320110741d805a14080c1c240700085840a44d1801e04031020760300c907113065680340c3c2010101a6107601c1d28806500607c168407000240a03c07030600946521642404681c0c0142001011910102a031590407480d1608065034a244402662201036040f99115900c0c0c40050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 760032086 1250 760030836 760030871
    0xd0c0909020d061118030a02060a1220120a110a051303050a111806012a0f0302010608011a0f0603040f0f081e130e070c020604080f010e070612 63
    0x2002914051515081c0f400740d40c0204c004144004001c1507100d003102c0c010302015165142800c0c02540f091040056030142da01511045840c50321149002a0315500d444440301d003240065440c01c40c2040009000c01c0c48412a0780c5540c005115840800c0495110303080001d01c1e01c81d851044040c80b201080300c5408503020341d40c03040699440000d450080d00c0320310f440b120301d0b540710751900d2103940514001321001c0060301c00244103c10503500d881560030080030344810b00a4172070502e0308500c40380c0d401c0f401040c00311060a001c0d038480d0f03000180d082d2070205017600b1a15042519500070320000071000440d550952401400c0c5421121903035262500c0c9006006402030700c400134034001303041842e1800d0004140c05010b01c1c050600b1100880c11800e6100c08040c40340c646110305003150700d0428880f8001401c0400d6000000f42840b98a00c0c2031500000d4140d08264400c1e5041d500c40090f41c0a00f407400e0141485001c000d500038100c860070610007a01c0c1a021501c04200c0d1030b6a03500b00f116820703269 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 760033336 1250 760032086 760032109
    0x40302041a030d0e0a0f0905060a051f08040206190806030d14040b131203020f0c0901031a0a0f1517030403200105160f0605070536090f150d0c090902 66
    0x4054101b0344545c0c0342c10000141130100e80b070f240b0403080a10002164105500c01c41750700440c074003840b6038500c81440265007416006c1c2040c3d0f0001828022041404580e03601071081d1002c644501d142440c00f20704040c40d12005040100070845080014456001e00c00306550660352084011a1216590301d03801004840c00e03800200f0030000164141e05142c1c010425244071900c035800d40b40c07104080818021641801e1000501c1043c24210503a0070703012009a4540056003028082a01442641c07100b0a03070741c0500346a0703141c40300c001040002045008140d10900c425402460805195490700c400da401d030700082c0d010401c10508031740c43d44c0c1e2041e81100d2441d40c8070488842c040104c0c1c00c2002c6d2541071000c0c102c035014580404a80494054025a0b1140c004c0307032000c1000c4802d404c1105201140c45048020f640c154001c000078907a42e40307088600c1100000820205460141419aa1001d601c2070b8a8090040b02c0d01d2500420101500a030694070702120100d0029580d2012a00b0018a0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 760034586 1250 760033336 760033349
    0xb18040209121204032109180e0102041409060f18070c150f0e010e100b0a0f09050f0f060102030703141b0102090a140a060c03090806010b040302041a030d0e0a 70
    0x60000d070680c4183c0100c058800d50b4000c1c1c00c816610071008040060f00f5498500400c0800d529032800c102c2811803460546480358045004240303240325000310340c00c0ea007282c0c10681b411744148a1510050500284103039202108440a40c00c101c1600c0105451543c0920811940c410060008103428010701d1105450380d400071254054040c0251200e00414131503550352032141c10584401d10213401401303a6594804c4040142503018540e00c0c00b4802041041011500308542000c00560301080d603085100800c0316000118003450807400c0384011104c010000340501d62104c003884171a99000090300c069a03414240a000c40351903494060840c0291807140d44018060005ca2180728419005030106080561301900d4441e240c080d00c0780601ea80050290700880140f50400a1034459002101121301a0500c80381c00b50b242c4282c0740c20003c00341c00460096000160400450801e446403e001805900141d043d2001c039400098988009401c0d52042100c0d8840c03025007555180c0b9184c0c000c280 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 760035836 1250 760034586 760034593
    0x160c020a0e0a09060b040e0c130f15080708190b0a09060203270a08190e03030a05040e10031509060e030c070807060206010f0b0c07230a0b1804020912 66
    0x2800d841010107410f003102c0c12110f0505003500c284840c1020b0280010746058000641901841c01040c03040207402c0031030940c1d600f40c59600040c3d440030644102503502020f110300b0700c501d0341000d40240c541459503010110592089946030303d044075258200c0b0410b5032040c415a803035200e0900420141010303100c040c2c032151000061005910002d00d294260070010781154040c1210340da105622480401c0006d440107030300b001700108003400c20495141d040441c0c00c240908400c19000319103503411004102001c0340c40000d007400f2030000c0c0031050340e1016080d0001c840036401c540d910030010550707200640800780c580740d0050420203142c100c0d0555400f0482101d840301d400b4071040b65110454410440d4034020480301245952011503994180c07900e28408070000d510309080020268030589140d0301600030114045400780070316407051b082c0001094014105036180e41017254200140e40185410350f400c0103400020f149074141004003a204880040c1c07186180c10110380c0c45803810000c040b080c00f = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 760037086 1250 760035836 760035841
    0x70e01090212060109231206040308040b01050f0109030b0424021308010203161112070606060305130c1a0c100e190c12021306170c0108160c020a0e 65
    0x203050380c05442814504055180551520320064640110501440d141003401d10030400052803e800403500343c03a0007402a04040303141e04215401e101c42034a0880001c1d2001e0140000c0c4400aa401030141004440000d0072410342c000290032843c00d0710000300320164802c005024400c3c28101c0d4172610450400c41081c0390f80c6412036034001e500124a6403200c04c0311400c04200f0f0001403080d24441d29244202460004600100b40c07903041281498000511800c41d2441c0c8040501000d8844584901d40106185040c1207024081d04d900a1101407032151400494000c101803441010407120400707102d41c1e140c800c3c503102c060940300742c0c42116214492140328580c4040181e100407005280e00041e181e04901007101c1a4407900c5000002c1c0c40c00c05502c0d02400a03100f8941501c024620043c4541500c00110000000703484640e031054607110400804840200014003031600344031001d01c1c00e07180c2c80c5010000200d0054201c00c8450810070382900e03000071522001e10803000fa03c4440050b22043c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 760038336 1250 760037086 760037099
    0x50906280c02010b03100203040b0f190f05100501261807030b22050c01050927070905060f1603170c1c0501050d1103191109100b0a03020903070e01 65
    0x90132000c119030300038880c21000c407003000b100e48280ca00075079022082204d662105041c1c4804d03000d000d00301e440c42036519006d40311003c0d994480c50115000c4144003241c1450500114608001160b001605010550190390300000f001c0500207842c0550091440407511004002800103c2603110103081d4801c0d0302010080c0003054400360f06c030700c042007501c000310184c107942d1344c82e030301c1151500400b2640100305000c85c0758003880150004c110701400c03485014482c103c0d0032031100e440e14140445d040010040c00600780d4084010300290000752060342ca800f4110005015078494030b00c0c0d544103509014902000c061240080ca24241d00343d000e0035640d400c0c504640c9580754801519900401c0420204602074401d0380220740c1251002030040e061a00b56846441188004602499050040c114148965034081c2484d158190168075508505088141400a00f19010f00741d08400000e00e0010001007001c03100310750711081546005a140c0382101d0100e41382404680005c138942c605c40c400400c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 760039586 1250 760038336 760038341
    0x30f0237030605010f0b0f0307051204060507030e010219080618070504060201050610050405061309050702030702030c090114060c0721060c030c0f0c050a0602040605090112050906280c0201 83
    0x1c0d41d019207801c000690365454401c107000003a00c5481401c5906000a00001c3c1100b800303035900020702d080092402e03114104a440c1800304a41c101d56599852090000859061255401c0b00c3d100030004c52600b10071400482c40103030241107403001c0162138800141e0325140c010002240600710411036a040c101f221000d440d54100b40903c1300150b21380000a206450850300d02d4001e1244c2e612828603240c2840c09000072070348554003075601d00f414040005082e40285c030a8500ca0b00850340a1900c1c0e0005104250502c0400c06807948036200d0703080144000601d443c1c61040d03584040310401c8c1e540321800c0300e150400d546a804145910801028008011039069042119920400003080080140c00054046401404034200099079013a402c4010750b00520400c1160f45c050011184082c5940e66103c1c01e99000f500300400140340030034012010358001c82d415400e200d68003024020ba04e444110280c0c3d443c001861100861101c10b5200388040c2e0311642c08a038003000c0700050000c0144a00040d01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 760040836 1250 760039586 760039589
    0x18020c1006061407080a050f09120d12063005030301061e0206040b01090e03040506211015030f1d0f0d020d02120c010b1c0516030f0237 60
    0x81160301c3c240314010f0100070308446001d40d00c940e0b2941000d0385c444045031942c011041940740c80f002003050050603550100b1201c0701c1c0000c40e0040c04551184240103081d40080d0b182c0a603124144142400322100c03180c521168950288405540390000400b01411008821009020303400000700102c2d107540c2c4484c034001d4403020700029184411110308101c0c0c0d21481203602904600611006101406c2d641d00305a812144034070860342450745600c000340030b41d485103e040300d8115001c0080101a110401d410b0f6014010307949055171030780740c41c40041041240407041e01c20581d0b200c05e04101829507602c27101420103140349890002400c07400076503030341160000c06411803040c09040ca00c820b100190080007101664041d050121a40f044140c03d0340010300c0642c4103540b221549441034503105070b000200081442c801c610328150b41401410064250080980c1025408091020030110011060301b0b0f64181c43c119000e90051080010700c00200895414407a0141c08030074074408490740180 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 760042086 1250 760040836 760040849
    0xa091505070803151c0b0f04020a1512050c0c07151b0b150639010e0a03030f0507050901081005060309010b091501140d0609180b0a0501030201080118020c1006 70
    0x300d21005d44202152140543c41c0000c044a90000001e0140014424000d42180c809003100000303e803103011440c6514060312500000a80401052071104468081c0581250740344021528021424050540310b01e41b50003084600d50b45820600c600b00d104020246040954410038400b9088ad071500b1400004161206440342c10241d06408061800300110307103141846d51f160000c1c2c200d071401c0c44980fa42000090114420203000750820303a800c01e0040c0b03440500709a0140c01e404042e0f01c1c0240854041030080502d2700c2c03030441040003254100d402c5480e444400d003410007090783d8081d0111848416600711a03001600401440946081504012007219040314074203000d6503003090175441825680462030020340c0f042041d240c0b181404c0010404030f1010440861000d850750884c2d002d503403196002c070f60000d9680b07070054188180303540300c6034102d402404207000355495600000c120600600480391a00c61100d024100c20a031a0f04480c0e04203415030640705140a40300380700000304002d2080e40b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 760043336 1250 760042086 760042099
    0x7110306060a050f04200c01090b0f0103110609030f0a20120604030e032104061229030106030c0f05100c05060a0b0103091a0a0b01050a09150507080315 67
    0x741d00c62512500020944a002d08081c0e840082581040701030442e0100041404c00681114080c04108100070070343c00f444034001140407800d501c3d2080a02900800c1e41001180c201d0050000038000f08101e18100720403280d0702d45603044d82000a04000602c01c100c1c403903101e01002c407402c00001510641180ca4000003840020901c3c0c020b114958031070494400d1150000c100090010f0300a4020f44117141c0064110760003c42c503c25003681c0e03041450901c0c0400f002c0071804000c03213584401c08440c560b032107c10038006e007400e00c1903c01c490b034604146118000000f000c41000750300e09510800040d03820050981001da80c3d40c0011101c418039005880c010b42c2199401442c81780a0811094220340c000e000303280d43d40e21620641d000300700d00100382d8105500c40782d030170002c100307500002c40f841c040042e6116100c1c140b035a420b108070b4501c603044c40d051081c148a802040b6801c0340f0008221454a0510880212035003000c48292189000c004c045c02008414413504545100d03803101e5020041e0b400 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 760044586 1250 760043336 760043341
    0x93c080106170303162319030b0f011101153507030b0a020f0a0201050a0630050304091503030908010203130212010e03030c070606050a082a040207110306 68
    0x80d440400709011411002c1d41c420404204044081189001e9812039481c040307030b4030034003040c10140340120503800c114196004900ba01c20a052549440c4c031500031401c0c100001c100c1200440c00c600c2d4002a42418406c140074014031006003904151038151b0070800c81a0300a444442c0f420405000c904200201030000c031210b880e01d10000d1024100c12030030700040406900e15030f954030382003000901c0302c46601e409008001d084c10107a00a8481d01c41103400101c1c4a1503c50b0340c44080b50166840542c0302000002820404c031944c00c0548004201c0c0c501c041c680c20312a0900380d1841c13049910401440f4074200500c1c1d450042c802c1e072801600e200765500051a0b036159945402d0340410742c0c0111400800d4580c090046c54044001001448403600114500131903500060035030304100e400d200e0050001965408010383d80c0300303040c00341108541d00300c203203403d00c07464941d07501003141c0c603560240700300040900742c1c2c81040c048072100d84014810355882845260078044038900c4242e0071f006e803042402 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 760045836 1250 760044586 760044599
    0x8160e0108071203020118030504050103050f06090105100e120303070816020627100f0b03010e0c0907020f0f101116080f0f04030b15010f093c080106 66
    0x5a65048400300c0004201050508070390075207480804804500303665a44002101c0300c00382440d0304641602a403201c3c3d4441e49058009011780d10000c00802d403d0042004000c1c2c540d560803030050641d0001d0701c5050440304241c1c02610a41c0d403040000354007810041000c81141c03c000021482043c0551f035019554440c03040c89480b2001c0d600241001d0381007840082d084107241d5601c5645e030000031141d140c0760028102c0203400c0036800000c0510032070f214401d42603407001d98011300c01c00300020390080107540702e0807001580f2150000710b075074400d403a0310b004111802c0c401c21101d107003002c2800984a00c2031864461a58804400261000541c14078458209807400c0340207803028020100e03c0500724035141c7d50385240d0b960155044034119201030001c1c1422025800150002e944a0f041101c510f0629a842c1c203a00c404c00b080309410131610001206031654444006002c42d11040d55504001035482e811055540e6407403480e000403918003500e840117908408400080b41c2ca00f100030001d0f140c4404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 760047086 1250 760045836 760045859
    0x403050604050f0d0e01050a2c040b1801030602031005030f0105040201120c0f2d0509041404020d0b0a090f030e2e0509041b090626011715010816 64
    0x14044d10100e00e400b00e485001394041c4005025114041c0342411034851030205c8004004000840500c800702c0b81001d1170701c20300b002d20411f20314100884a40340d0982c451003c14140040502004101d00e0700407011900000d00c0c0e081c0304000e40300c01000d0b04c40381480000c510303000300012075041c1c0c0094240310b0101241078951041c6100307054a0b42d502491000b041c3c106413128840c2c085078a91682101d0071580e0402c80855001c2568009580d940b0394840c0a0000c0000740c4102d01003031802c0c40000401c4c40016035a410341071845a9202410b034011340c1d01c02c0341c203200400001c04094041c03000b240d181400c041d40250030907070602c03040f101d5030303101d002242a42202e186001c0c480c2d82603030311841030250001d0050003c1d081000000f480800c4204c0d070440040000304269102501144d81c0f01e17824015560086105040711041501c2486002c01143c0c170700e1403426043c81500310402000f84c2c0c0010a620034021180c0840c074119a161840d44d48400c020b5603041400c0190211207a41140440d848010b44c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 760048336 1250 760047086 760047103
    0x111070c12030c0311070e132f130e010c080f0a0603051b190305300f07020d200406061806030e0312040614160f20030403050604050f 59
    0x15910350f055410030765400d07118064a207000810502c0380340d90004035072884072074152003074048280303840d02c41075140b40c800d80384a850041d80b00307042c0c00055140e5079010300c0010030010074011102e8020069074184400002d0568070032080455003085180e40c0c00f140c0000c5428026294030038031108994030340c1c0042084410328000101180c01180a0a00d000000c01d019850800d004211112381081801014050961a40104d9090700182050310144850041c1c2907401c91301480c400a031144a1245203010b403181c100c0002910401160742408c0d52215011140c6059000700c50b80030243c80f24a80c1da5040c011580352030f00c0f490400002098607442013056a540c14100415407862504011041c2c0140000615030203052100f8003500c1d443e0011151294010345c0078070303800900d074041100e08126441d40140362940c0196903400e00758803607502c40c0184010f040203142c03800c200103032940f840b080c03088a56000c044a02c40840c0c04400d001c40411745c00d004600c01c100316100203100040d00ca880c1d0b1441e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 760049586 1250 760048336 760048343
    0x2010c20070603050a020c06040605041b030c1203030b12150a0603020603010b0307031b051908061806041d0c030c010c0206030a02031f06170105030f030d1d0111070c12 74
    0x8500c1c10440203000340c2141e500114580005030a000c038904c0c24a1820000302c4081d21801c1e2100c0c140400d0004181c00b803490340e680e114501c10f6860960700c824070408031500c200700d030401913004a8400e061017070b8003001c0d01d2907001700004007116180303200315928810383c1a000555a16140410041c1c0254824442200d9010b0907540c1160301e0f15401e62100e800081203001031607182c440d03948501c0c6204806032901070550b20b416440d00c01140e10890540e070f01030014410703c50440c0c1030040d9643d8298600880f40000055241c095803180d0110b0080e0020911034900190030320760510f00d40a010403000c1820a09404452214a6a000448044e9101403002c2e410101c200089040742450390000c681c40681600000003105504440c03c544113000c0c2d001c080001c144106480468101d40c454078010b1a0880082174000011307089140c80340300389002c0304011507550581c003c2d8014650011596050040c00070070600402000003041607210a200311080c0090700c101290381e164014020225582 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 760050836 1250 760049586 760049593
    0x100c02030d050405010f2d08010335031e0c070605060402130e040602090a0b18011809180215041a07051027110429061b01050702010c20 60
    0x100c2c00550341c2c640240c1c0d4151000e1f184a0700c003400b20000019020b02240b85585440481d132660914050050002c0c610b29070000d000c4c1d01c03103491002104250f40b0800e09190342c940d507945402c0f84040c9888030721000585809554000c02640311803543c050001940103010600181c0d0b1607030704000492040411a41808070a420b0901c100b215030b00410754440c0c81072400515190b100f900103050340075a035020a0344050001204031080b8514480c269500c5820701f00203042c00b0b52030700040f4101c0300900030300b00b0b01d664a800303030341030407154800445c1050f801500d03010900441e4024900b482c1e12034080c02c00003441030514503051030a034030f04650b1110381040182c09401e03204d444080203090705000c914403003140d80c460341c4201125076031506280c070312032480c42e55504800820b08c006e03100d0640d013503144d5107003001c54501100c80300750b0008006a02110030380c3c0e803000c2030f592404445c544800e11264035847d20040015031740c0c05601000c000409603d9291010b020f201e03440c0050804001c18424582 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 760052086 1250 760050836 760050857
    0x10020c060f0c0f011104150206070c060b01020a0b0c030405060c0a08011809050f06041704030f1203240e0a020f12310c080a02060301030f0204020702100c02030d05040501 75
    0x180c2810140c00c0d00310b5603009444103c01169802400d456106000140096000404100404100105440f0411140007034051880c1908014080611300e8401a00c016110155408582c2c4240201a036107a403001c80d041150500001c082c036250001c43d0121064411003010611007007000098a100c034119948401c6540c0c201400c0710701c0078401c2d0081c0258142c880c044800082c1c8148110805280c40f18014012071500f41040c030740f180c080180780d249c1c85ca0200028404035050f04484407449030000702c180304000003820114001c0c00700c0076482e80200280c00e0303071032910031040700b561044440c4203180c1002501c1e0111400203d1144000050b6014800c21000c052100c00d660400c2d449003100700ca1a02940c000040701c01c0c5c4002100035866a220740084090800001111b2803000d061200003c1185488640c0414114441800050300c1c22030003002e41c004540e125012120702c294007a08076292003540e0039003c4d0a0200030f40003240b0034092011030102c26441113040d41e080b90016581c045042 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 760053336 1250 760052086 760052107
    0x3020405090a0c090f240f0e0103090813030b0907062109050703020411041a070803010303180b071104050f0603071418090715020601080303071b02100e10020c06 71
    0x1001c43d5400d2405200c0c00040000e4000c1140846000074103010301c1103071110b00c0c3c0c9a6a80014070114143c1d906000c506100d20490340d50200101a0704002070a0024005540e400c110000b401421110080c60900c071502204001c03040c00710754020304546040f10a2036440344800d03901401000e08031f0b291b454184088603810345042e0004045140540c05440d411754698001c6810354500f410201a000000a0308100081c0384082042da2982c40e1641581484019620804240b1040c800601041000c00310350211070b0710b0000c0d0380010061405a10b43e100c400f40b81000c40150099080f0340710f9460040021b4650382401d01d0648900c0c4c000300030b44103441c14a0710200c3d0002d45946001e401010350080c02c90300e01e01c9101e0482c0558010001080c425107080400290f1031414a08a011500b00b04010080d09000005403a0416058100302010300f10032a42003400148d0030402940c406000d106254109421100200030000251041c143c40440c181c07081c2da841c10001041a0411010407000c5a803 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 760054586 1250 760053336 760053341
    0x10605130b01120c0c0515100e0624040909030905100516140a05030d05150a06120c0c0203010c0f12020403030503040f0203241603051302010c11060d0203100603020405090a 76
    0xd204c000d050000c0014441d44031103180c80c21203400440300c0c0f0b603504203100d100310100320848010700c013081e980004c41c58054040b485031048400c50000d419003407030548510021050523500a801d03401400c01a003005814024140407180c450719000f02c1019454000b01c40c8124203c40245006250a4145180540e01c2e1000400d10401030012070203140344550010b4030034001403121110380b01c4046010304281c20140c8403403440c02512481960000410840070b50000c46c00f81c64556110b00003c6e180550400c00d131844107481000039410351a1511403031a01d50003107405103d80d0016513546051102049540040b48903900000c0c012480034400103000512020300101c0861000e000d6951041c058001d070100d41801e120ba040c11403682404010306400030704401003c0500074030301800170382040c0407003d024407410040641040480c28101003032100c500e1101020386000b80200d030344c0e00e0020208000941080d12402c0342561390b010001203d500c64000e0343c2c02d03650024030074142074a4542c600e100 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 760055836 1250 760054586 760054601
    0x40c020c090921120601020d1d06040f180506010e0307030615030209100602010b04050103020f0f010c0803191d0c060706060305060123011e1d03030c010605130b0112 73
    0x103651080601030090b90108a0030922a181502e11480e142ca0400444c54900d07a001041c03241158400f1802c1038907158000180c14503014028240040e0407552008a10a8460703034003c111000d0f00e245001034020007103403141c00190984a4200034a4403041e004462081ca9008000da1660180d082840441c1c3c1c00e6115075402019482c212460a43e00d80c04070300700312400c55034081852120a0100f00964082c02402d03e0014200e404008a60460f4001110400e004c0740c0070f0300600c09440560300c3c40c1d00a45114038810b170030034032103a101d00e82910b4480071008034000780b5914500b001c40b811f8440161440700c07491003a815010b801e03030200b40342c280010f42d0000c075000c1e5951500c034940040490010321078140a40301403804060070440c0081811124401240c0d50741c10000308411500ca0302030412030584100c0028940010304a01e105e91602ea14840c11104d05e40c180800a450286800154800c0e0100c54050318061004040c0170a41012644d054a0507808604070b41345040c0104c17401c1d8401d11 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 760057086 1250 760055836 760055851
    0x1b1005090d0606060305040201120908030c03070512090d1106010b0f16080a05090906060a08070e03030702040e03090405010b040803040605130e07030e10020412020609220204060e040c020c09 84
    0x40860320a8840c0300c02e41d9016030013600440c0d030340c60074082075590040a05460240030b04040c0001d011585d81c02c84544070042c0244041c41c8040003003201c051241c7d0031030700f0b10000307000c25410701c0c2001d0454135111f01d11070480e00003180d6254509855901c0204005040380c41c4120141c1c1440d40c01241c10720580d11500007000700c201c06400600c002488813015090030710b5159200e41d00c40710740400b80040320101034803e40c440e100c10300c990760350f69900c600c40e968841010710703154284a1007000130074958007404800070351082c104403140d500c3e548008040c00360200f0440d418440742c1d03605c600c900b000d4850390098110304c1c2c03c00c003c14800240648010700b036002074551124011036484a809804010507104000001d8580b0007240388e6901c1000744100c00e8101d03000452802d4500400c1401800104000070f001d00400b203420102540c514841c0202e00c0204200c842c1c8481050f085074000b98410b0242d400810341d4112442d02034141846a4458103016400030841c034101e4400f04a518900209401c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 760058336 1250 760057086 760057099
    0x5041806090201050f0c0607021b090a0b061e07021309170a120501090203040507050919091403070318091e02180a080705031203040819050702041d1b100509 69
    0x28104050b5500420301ca40307000f401f824036030815420003800c000000003a045039100c03000c00c2101f15541e92812980002c8412000a002520b610110744580181c020302042c424030850840c0060801100621017170303200312214002c0151100c105070861f200204042d050100b00c4500000705500b140c000c180300f008030700381100c1504405e150501603031000d030400000243c0210500042080800420b0040c00040703642101c0e900d400492641d600301c3c4607064000070f42d141e0015809000f0007981510780941c0300819a9a0351120341030150400a620302c90203860321514000040440083c0700382100d004c407030181d01488440b000409400381d001100104419244042c03161425035070340301707000d0080c51002c0203800110b20f004209400c1c6110340c07121000a00c0200208000999250101c0301484100e0404152400d081c2e0717401c030f829008003140203400030320708200c055513030101181001e0030a0322041101e800110742c0c0e0a40f00007021140c01c5a411161840f0980300960103000074001c0e400000c5c040307 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 760059586 1250 760058336 760058347
    0x170103050c09040303090f0606080d031b050d0f0515090c040302010e01030906020c010e06160e090703020f040b12011412060403030515150c012004030b070c29010504180609020105 79
    0x107d0b00c1c980d03d40c1c80e0844a095a501c01000132240600c0400818861403c04000030b04141d00c004000788081f4034200100700740012070820061196104001ca0340f02030500304994541988040644510408494401e030001c500217090078981e2001c40701a00d074103950b00f601c031016200041d800341c07094400450310141c0034050b540b03041c04248075161a41603014001e00060402298041c0320076814058102040380414490ba81d68a80310070442d0400603e20300180e036900f0440716444035000716004442c0f415070001e4481e000c0960a0303582e90580341000f51203840c4501040c2044021856840082c4081e0003140c0042d0120b0301039804a40d0002c0c2d603d501280c19042070340001d1414080402c99a0040c5002c2410340c0580c0c1d00344a04049035124804200305102880328100c001e0088d0f10006080d296610001081a440307411305407803003588000750b02d4603415101d80414040142c4100e0446102c0030100000c1c2c0c5281ca4000c80c05070301c840030f00b10500707030300b05846400240c10442016814000100030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 760060836 1250 760059586 760059593
    0xa0c020904050c011d01020a0f0c0308030106020106090f02071a1807060c0b0a060e0103060c05090604030311060f010515090312030f070f3f0f0b01170103050c0904030309 75
    0x82091141d44103002500820007450009420041d242d540404503545020074110140d80000388032540607001494280d1000341440c00c001d0041c800d0b0001090304c9804000001d00ea40c05400c458107440b44c4078400d11900c030400e0b02010490042c150040e00d103000d143c0100080c241781460098110340d450340da007444c11ba0000305541c03900c000c80c2d0103103000801d0010118144171403500403d800400c40b240520400f881c1c1a030342000c0c4103042c00040c0c010b90b03031030354042c00c21402401107805a0380d0240c01c07a46c907135950f8100a000a01580002d90050240b40300203404006d03001d00c51410b80390f004000c0e45151006a00e0060346402841400e6091b20461344075010040015024510a98080654881510307000c08014101c0c609642010144841c124400062641d07001d00d140008104880c0301300d111807441d2045041079200d80c0078150003450003013450174091881c0c01c0b9510030308082e2910050b212001207070303c62a034002d2001401e180c02c41d14550006161100d50990030600a00d001300b10000140c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 760062086 1250 760060836 760060849
    0x50a06050118050a0b0102150c0403050d09050111060f0c0a0210060e06150705030a12150303020d021b210a15020a030f0207030e2101060e07180303050a03020a0c02 72
    0x1c015008440c0e64182d040c80940307190042e075502c0100e213103041c0460400c540001c6d40c0c507031685820521244198000a168071403003070035140110f0b0018121403900308105000f034078200e043c1c01924000344144003c103000381070001c1d0302d600500070304080c0c031103c0d56041c3c0c0020050700080c070118218080e1070702000c3c0b490306030b002d91f01c0503101f00c08400009050140c200180d042480c101540198000d202e02c1021403c0807060303c40d42c046034202001840640c10306034000749801c00300500c14070755000c808400d16600150981e60110207400300ca85525240a10381100c010410740e039503128201c119204050b095001147c541c06035502e0440d03240e13150310340d9003011402a1008070700d400c40d804110598000c2e4075002d082d04c0c1c945180401c41c80c6c02d40d642c400805100c8a0142140590340c0440103051244408075104592484140204002a140d1080c0c40100f030061b6400303400601c61118850a8078071080302da004496064692518080b070b01402900a0340050414000340601038041c180582c840e403 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 760063336 1250 760062086 760062089
    0x90703081209150903040905060a080a030c030e0307050303191709030a0e220914030d09060b0a0b0307111c022512140c120f2406060304050a060501 65
    0xc1d04900900d2511820140c5007007111003c0071141ca2142d0b0600c08011008070072207003950f1109074003180301d5a440003c106000c44580c4100c2480c0301c0c07203180000b4140d00003800310080c0c1c1700e5911000c000280744101740d6148418081e10780c0c560020050042c0b80618002000350b8400c42c0c0c10071841942a418205051040c111030794442500005080c0c03400d04d900c28040c00c070901003201d152400384a1400d03400344899250898000e011399030b0014406101c030f1280380b510800c100e0000c0725036031a110880b880c090588039030100c9400f42001070034256071410345904000c1e1010311680ca410750740c804404851864599030020183e001d00201c90f4500240008130707080030001a00104210b9001920924841c1482c6114120b80400000188200d00c2c9018030b001e1003d404c4800c0d5020120404031841c24190340d030b070016a10104442204045000208500c88249240c81c10307148441002c04910340382400e0508030038100d11812001881030f04d0101e010b9170b00240208100d07050303642d00c0d95416040b20004e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 760064586 1250 760063336 760063357
    0x130506040615021c0201020a2c190e0a020306060f28030e06101406090a0e010909050708150a0c0c0f080405031612030c081615180201140309070308 65
    0x496800c980030600403001a8688060344000c40c9404008103000b40340006003844409031141c41c50270750000d07500c110115041d0040041c1130b038070110035403221a4980d4107a8461411019100070009104e0f044a10a8902c00c80c00034098519161a2500340100d81c0e0111495100c403945c1101c034180000c002210003004040d068500050410290300c40d0b924000c1c0013801c0c00103c41c0380d440184484c40300305920740c0202d9020384240e03071104001c200254580501ea0401c03000c06a91000008150030290850050396003d041501c4c0c2e041e444038911a2505646100010000140e0012860b000136035408243c0c00142e9140000040050b5581d0902410051905480740301000c18240800c1c034003803100d142c8441058a00e0203001d45003103401051364000300406018412143c82c00e600b8407081c3e804540040180401ca59101d403018600b01090010982030014180d28111100010b101c0864101d040f980d0140c4880c103514061045601e07450b0b01c014011119809182400070004d10404041c00840a2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 760065836 1250 760064586 760064593
    0x30c0213050a150909020d1712040503040608010815162a05071d0f070302090a091401050609031f0b0d031709150c03090a02090702010917040513050604061502 70
    0x141501c52548055044c0c03c60320005150034407603c01a0317aa480c1c0d00120b035900c0610364062081d402880c45940c000c1c0b0400e011892044000c00081010100080c4251034041d210b1480d56621001c182e59507601c40a070841148500c3c0c1d001c162010080001082204118034102c0308141c00d01d944010181e007500307000c0d101080040e500c002002000d01c000b60240000360006000003a40c00d00c0001c9144001d810761440c82d044a000c00c0c183d40c8039030106c40384860090403045605039110f120300010041d10098a00c214000703400403540c0d02e8540121107180303800500400c003851070540d8034140d540f441420b10110301d5803001040d01d1926400d0000e0003590007602d880e225001000f00710203011030300401540b80c603045419505041088a81d0050700440c1c1085a181caa0b43d5180d041c070314204145070081c0d400f94920003000215581500b01c90b444500c10f1390b0b40c3c500c2c1c200351400354805e4000da01816501204a84445902c5041e551005a211000420115403a03a4800c0404e00100d035154201c0e00581 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 760067086 1250 760065836 760065851
    0x1303020a091b050a050a231c0608010507050702040209131e0b0402030f070c080408060f0723030a021606020f041a04030c14030114010608070207050303070f030c0213050a 75
    0x42c41d03502098040140b410010716011803150010150b00c102611141403000f03111442009040c00602582049000762000e0f0340c0b440d24030700b605041244020000492400e0402c0401d0600041c003440d80124a661191b90510401e9801c01010f0f4014410164201c000c60544501005260180e0600703038011100c400e51206650401405641c912001c0c00c1c0038034010014402c482226116035940640e031440d0130000c015003407070100d003c1e104d40d03440002e15218010902548583d6184464080c49075034036031781400801181c0c040303003000018492078440c49080c0300254186413640c00030a0800c00044034100c5d0603005590300c80c200d811944030282141e2000c01e0030b100568903258a4030ba0005d250080c103041c05d03d140d42d07500840a440c0a01040d80d0114a1081425142500908c1c0b40d082d0b41001d94015617183e0100074582e2200711061790040c0b0801000080d44d09003c0212080c240d08800d104520081c240c90603201e003400b0f03100807600005070f00404554020720f40700d281e0041038079450204401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 760068336 1250 760067086 760067111
    0x1404060204170a02090a0e0f0a1506080a170a05040815040b330d0602030a050f0a09030e0609060c06010303032306030c040e03090307030b01031b08121303020a09 71
    0x1c82c0c1100c202c00e20341d4407600401000d43d42e98509240d2021100c1004901c1c403134103446031401c00c6182405460113108901106c010080c1c5c00f21140d205500c110010088580d4402c0102c2c1c2e0380c43e0711315010b0705588022030b045941c207001d00010583c60f025410a1440c250b40d4103c1103240550301c5c6000545032002c80c5c1400708001c01e800850390801d00745055440d140300c18120b54104a42d46940000c4001404031116485403650f05070042c030340c2d8000f042152285042c8040101a00089840040490302a130020340c54440c1880b40380b29130b0b0703055592001ca0b840141d041c800150700c90041150f128005220902c12108100000c50107144a03a501107485150501e600d85205100221050440795401c104031454030300180d5500d81c180200c401051040b0b0700441d1905600c54600c0640e010302401c8404014000451030032412a440340195a145050302d0303402e005402c8140c041c9c403c258111404041d480311903140604a25034245034503e50140e0349500141c0c1410656110031602601d450621461 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 760069586 1250 760068336 760068359
    0x30a18080307030f03090c090e030c10050c0a0804080c01060305070806011a1c0b13090312090c03080d1b0305011e15050d020c01020a020109050706020c130c031404060204 75
    0x51202000441c200002c80e5006012440407480c0002050790351810707001071084d031150100051005440401c0107540614685440368000c201c00d040c02e00c2030b5100003a64800902c500c611814140f42042d080100c0200c086402140143c0140d409103c2400000d04146007841410b005501c87c800400c0102d03e40071b002410301c00305900815141c0e0440d8407143c2500c600c9011641121643e1900c41009500380300d458000f4140d0b42c0c10300740c2162051790f6000c0208c08a600982e0785c0c41c0070307444040350700d100709070b2502c180c5030303c024014403440405500b0000100640040c1c00389840140c070101754803400200b05010466000c1c0c4145c0000d032640d004112201002e481c1400c1d10b4680400f00c100541400d21004c076040d401c2d00310008000c00015110710001d5203505a820520300725000355601c4501c820000e010784010748041e03440f405410f600090791400007400440e18140a88141240d0015410400040140300000424541c5801c1449030880c010543e00d84103500c0b640c40140c0791810007420514 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 760070836 1250 760069586 760069589
    0x1201e0109020a06232508090301060905090a02010c050a08030f1e040b060f040902040f020d0e031305100e0301150303110d0516030c170306130606052703030a18 71
    0x117100c01c0d41401d8403002141e103141050f8090a028150b036421605008180c02c110703559040e55040c0f900c9403480c1c20402010020500700e0750850080c016640c451404008580040d60700d0307407030383c0d06c4002c2600065004841c007014080c022000c1e070302c00740801c0d114135107158000c58590540041201c1000038901801000940300c1036170400b500d1440ca0190364440c0c0c40c1c00050081d52041e40d410013450410b40d00d03900801c4031f82e5030107001448103120110603040a5017003845c2840ca014105918881360801c00010340e030b0340c6901c054118107503600e01409e00c00c0c41a000c003010401c00144507580e0855860900505080000562201044030b02e10300b0300514901d0121004a0a40c00c50a400e070201c0c0d030301105035040945641038011151080f46000c0c0c0d40d0343d000a5000b0240d2050240c642d8190710100055031103260182c0e0441014140940f151049403020302840c40464001c1c000c3c02d01c00da0380741344040d902c5866854a1484180707601e0001c1d113140c010515190001d14503c08240490810440071030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 760071942 1106 760070836 760070849
    0x182013020406030234110a09060303080411030d090302060f0c0106121205130e090c060313020102160806010608280218010801030201201e0109020a 65
    0x402a4019016408500c2d0f03034507082000004c2101503801001c0041c5a8149500100e543e50000750030421000c40d40040384020080703408d200d2840303801c010754020b4860038a80c3c07406160145890b8002c04121703000760001505d04408907044812032081d668111a0f45403241e04c25010700c2a02d000f2040044001c2d030a0000001d650020407082000e40f50040d489902a003070903203002e90b024400c00e08180301e01d0400c82800c222240704a220030350004100c03026a418004207200141c07843d0402c0d2010b6246520601c40d441c00c6680404c04142d001e2550b594200c52a8070300f09407141c88900521030a0b0030b110200d000100c1000c0310312080d0b40711007200d00e05041c40006810400c802500031220140710400c600380310071059801108401d0499505a41e0204103c11120482d591610b003650400348621421140303581d50b005c1030300c51003110b000781c000000d21000c45004110308040c2e0342c1d0222 = true := by decide +kernel

theorem cover : BRFrame.Cov 759892086 760071942 := by
  have h0 := BRFrame.cov_init 759892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 759892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 759892086 ≤ n) (h2 : n < 760071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
