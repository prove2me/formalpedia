-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2531
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:58:55.594202+00:00
-- url     : https://prove2.me/submissions/cc81fd4c-e3c9-415d-8766-2dd46d1b6e45

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 455035971 ≤ n < 455215827 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 455037221 1250 455035971 455035993
    0xd0605010f0c0c0e0a0e030c010b010206090604030804030f030e0102070c06080a2c0f191a01140f030f24060a05010c150912050703020d0504120813030605010f08 71
    0x3a80444440000c1c0b00e81e1a80c1001e00050079100995600041450b2010981b01e500321803280c2907030845400c3d110281c0d03540512070380a41c1e041041c650009110000341c842800c10351001440d40300010006024404458040301140d0b11a6100d85040942c0400071920750069142c02c8202800b180701d160001762032000860480d6283c0e1007090482030044900380103072840d6500050182e41ca80e084401c260180d070440b110410410704c1a41181c01000b1009001410f00c0c0c9000e6910100b0300b148001c65400c440c0042c80200700200850003441c4045400c644510840000070f40341000c441d140c81c1f00f6025141907802200a107209140720302e004582c00d4191a07071800300f031101610707040c402c00d400910456070042c041150304030381d421481c80c150800304a1010b40d440710410a0b03100d103001000644009010010305506001400509880f8034281e1702d03181c6080d0701c0b51580414032501821640e4009191051506c1c100301d42e600640d0f00540c240825a13681043d01c01051651003100740f2405030341c007401 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 455038471 1250 455037221 455037227
    0xc120b060922080403020910060314040206181203040f06030506040b01080402010804060e0a0803091504050d05090303041a07051605060a050f1b0d03320c0f0d0605010f 74
    0x14410b508486480c2034100300341c210010382d07109512094454103000c200100150316544580d5108182c1c9480d0356034000c1c54203d0040854481c141c00060150f840d2003400f0041e940e010803a0201d00c1d0003030b80d01c6c404c01f081900040521400d211400803a10000400040b5069411585000c481154404114135900d50040c0300a980b1141805400521020005001580990300141c3c0107401040c0000d96146031800d03052406000d1042030321a880c003c03040040040081043d0420402c1a03c6221407504060391140d90300d07280842c13000c060100c04580300c600c5032000c000340d8000f0700400e40894506205001c25070703860f5104207400d6030a4000c280c083d60300c1c114556107000407036001920351ba25007040780b0821204d6400024000b035070a001080030000e040d410380d407050801406407010b49508080580046c0454030451011424580e0314042d0107180301c0d0116802c1d561449050b840302e45565502081241c52141141140c1403034004611743c813100006138440001c1c0d8100b030302e61131f009003001e81d825 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 455039721 1250 455038471 455038489
    0x10903020904080f0d021248070516080d080f06090403031b093002060c1e0309130204080616030605040914010c0c050d1b0c120b06 58
    0x40e4001c040d60010400058440c0020f03c040b040e038620083c1018403901c1d0400030b80c2c0c8280c83c9141002502410300200d0071000d203c01c440c204106003c003480502c40c40c54841d1102424103074846160b4400c2050440d00c04000440b084298040e040d500c0c00b42c43d8034146020708031140a082020303c0380c60040034042c0d01820009004220a0020081c44e545040c20000036240c018003c404240d1180c2c0d06040313a0040383d0b2a4164041686c60364852941000c890000824003a04030388040d0b1504020ac000400b481200102c03000d0301500c06a5580c408090300601e0084005054224552100c6254444807004800340c0f0026004544108646828a440c041130380198058440c0c1c80d0044400310f08141c00c0c110743d031205001981400708600b80d40b9000641101c1c0602016070381c114000752200f810710820300c20340b90350307a0f00b43c2808102c411705a2950b6a54248210b05141801035403d8100802500800001c0c4003d51081091260b43d13180d030a500c0f40090542d1084542c0c02d400804200300d0f04e001426 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 455040971 1250 455039721 455039723
    0x50609040f0605090a080d0b0f06043206040b030103110a14060a0c0c061107080607140706020904060b070203010c020601030308070c1407080304080f071d0a1b0e010e010903 76
    0x6108440c01c45929450010030000d049114103210b507441c0d03907002030503840260241c11060b09002806086007014008044aa02c140a100d07d81c1000140900303004110b44150b282c0e14035116910010076071014031600e0302500201d07640900003203400509549008025816244501c1c1802c0b040b011f120280311040003030340151180d181b100710b2150303618104103000c2e2040000c40e00e0040245900c544605a40041507040840090489202c40042101c100068001001404002c01291a211200806000c1c4a0070614a1081c00090040500c101a01550070101000380100480e03540e400d1031f0080341d400158200d02a5090840300e004a90007c0380b22412660191603e040a55482c4001c03166004c2c1c00008855140c2916801d07000074404104200c0070341180f04c011680d503401d01203c0bc0c40c0600707242540c0c2c050703403207070308148010500340882030740c030745403104588160340c4903880ca2002810354003c82a6042e4100070907031201552201100307002c84401e03290f00c0c406a048000450700000075003c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 455042221 1250 455040971 455040983
    0x601031a0c030703020c010f05010303020c0f090c09040b15180901080316030e0105130b0a090f0b09130b040f1b09030819020a0c03080c060a0b180a11040f030605060904 74
    0x80c1c3e01c40d01070f4004104205540c0000241c40c050311100108644080c3c00a40050b884403200c0740d004c0c00c0c0700e242201401c0040302d08030418501402110400d100710b0340f0150003603840e26444401078449416028031110381c0c0b200b050300c0d003507000400390001d08180321080c031844000c07000003042c05020040ba02c40d241e00180c80c801c075183e26101030358921410f40035541040000c015406400200152820141c1280c15007550340e244224001000b00c41142c10602c0c2400c00c40c03c040001d1000d440407a003440c482920400080d20200b94958010994241050307005410060401003543c015407011060041c01e1110480740e500d101c208071091520340c000104001800c0003610140703802c0781106007810322a0700c11201d0f240300584e44e00c03a0171020342d4002c0310220000325150020070401d00959501c020304590070000441028001032080440940c856049070000010501c911410781107a4000c40114010950343c41da41c1860782c05000e55403000343e0320700e45000e0100b9060f03c0d00c0c2070158040d90b0400 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 455043471 1250 455042221 455042227
    0xc02060721090f0b0f0a051032120303090f0102040e01150306180b01270b07020604031202030d29062206090501030f0b21100504030c05061303141b0106080601031a0c 73
    0x11008100420196200d009c04000c41d43d90751034295208403d0382445403590000d1034682c00c0c101a10791804030340c805c0c10b082c0da03401400180200001a00003904640000c0340004450140240036802002d4235007201c440b1815044e40d1079442003003600204210413007a83c80c09120b04041d04c0189403050f2400714010341c07640c00d503400c008038400358002d047c0b06030000744030f85d250035600d607100560480380d002030101503040442c0c003e44448051042844c0c0104072407800d0300040750300f880d60160348950645644102c0003c00c003845681d50041c109000c030740002e00e2541d900ca840e0040a00b03040198429140040d0908000c0b240d002064002c42c0c04409020701a0f08460130010034112540704441e00d8402503106003241d0003168141030103028040c1d8000e440340300d00c200031410301e282003600041284243c101003407801e00009034415100720ba82c18607403400170b40b69146130620410ba420b81500968403076080c03800c08198103501003400c0d4101c1e84a1001c040b1018441500c02e002618122945154101c1c01c0c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 455044721 1250 455043471 455043509
    0xf0e0102070b041a090a03050d1d03060601030903050c1203011521090314030408120601082511100f18111003021b010c02060721090f0b0f0a0510 64
    0x150300307618140c12404c180c1505010f0008089822009664415155548000b003407044407900444c003030110a060404410300c00c00410b0129944400c0601702c1410035035107045074800c0c544160152140a800601503540b00721886a0000d0250401e00401901401d004000b50105018010180b0036025243c480140a10382030300d03001c000c04419a054003800700600070b01307407103000381801548071301d104e03150791611445510403507034040800a01071818002c11200b4008041d040000740a2481902e48108600607407114040b106181c071038980324042d102320903411484e442e154101442d100b807450300400544805a68450110603400000340910603081d0104d041c9081c4825100c1d01c0398140e00b00985084150304404051910182c540185a5902e42c0c040b0714080d414415140c00030701034984100000c42d6503d0410600256803540c0c2055a43c41070100104000584010741d500c5d040840b030115803500c0e40f01640c3d4108125036040740c040c9440009201883d8501002013a04e0201075440f00003806 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 455045971 1250 455044721 455044739
    0xc03110c061902040314101406030c040e07090207080c0d020c09160e1e010e0303030c04051c080f0309070618061107090c02100f02040509040f06090807030f0e0102070b04 75
    0x403540b10b400100d81c08002c080003054400311410302280e58078004110b02080c1c01558012514250341603c58450074200340109994005500400e929048800003404481d112042d407400450b9801012228008a200c3c1c0905c60b40201414005444005680030030000c850101d07221707115001d080c0da0102c011008503408014601d4600c005004600b4050b02c102d01840000700340c1c01545040c1c04412500160354415540c0c803203a048170a14041d401142581402d0040741c2482c0101d00031107004040410841ca600c2c0300a03102c0640d5039400010640d9912364038411103940303503c03c8a0419503449507610000710544114507150b41d036002074012405090402030100d41042ea01046140b8911410310082000c10784bc1c410141601c2803a00140014045a8540e0003074501844121020318418401000f03d5120b60300040e600c00d5001880409064062034248010b1840c11f070080c09c90400410b9203001c260300599030070310440150f190743e00c940c10315500481c1e50f4402070141a00041091104101940b4 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 455047221 1250 455045971 455046001
    0x110612010e220b0915070503070e030a0803010303090806010f030b04060c021f0c020712020307050105030619090f061e0905090f0a06050f011706070e0f03060a0c03110c06 75
    0x6a001403120b00ea245010304038880c0360b996016288685481c0c01c1c000d50450402c026081c0c0104140c03c620149407010018007507000080c011401c2c0900c203c1080c1580d0703018451100d003a6405000070f40c0325616802c008203a0a081e003c0c0d000c8520400e03001044880c1d81d50300740300071640d22000f0956503070380710b07610140504003080c010025442010b200207001060315031802444900a13000080c00700303061070024a0000c1a500c903034860a1544100805601e01040c6d40013522400c1c01c1855517500c130032000c5450020300c01180b0400200e9030302d021800161542040520307814140007481001c2d02c0b105604880880d9403242001907540c01d2080200f10001c0d088654416210825200c4c10030300b00d5101810308240c01d5048606130354031020450340040d012405405004503001500400008441c8240c0c0c50302c0192080742801700c040180900c5940d49240070910100150544e10300381000300350320019200b49021400400d0510081c0c001c400d1054050381d0000030315200030602d07501d035110740c0c0c00181 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 455048471 1250 455047221 455047231
    0x50f01091a010e0105271303020d11101116050a0b070807051c1b0305060306090a030507060b36070e030705060309010219020a03110a17030a0f0e0109110612010e 71
    0x146040d0010111906c90100c4038420a0300c0115410f010449150003409d1802c005810018040044420f41d5103134000982c2900c0000d0a610016003804540c0404000380035a90036103001c0c3d003142041404201d00440c07410f821902ca400b803104981c4031300361f0645070031500719500e41c009070050010459001090290b01042202c034080003900480d83c1c540781c4810102c02446102003a03c6100340500350504000190748028228040e1030700c0308041e50006c02d948544c0c00043c00c0e040c2c585802070382c00c0d521860300c0c40c01d4001c944000511921482d0b40e010000c0807184005040780002400194030034010410060381c0c030750080c081e00200b8101010044960400360092a90799800c1c0081c2c92080031007052031100154a07001050014001c0c0303001040904401e03a8010607410400e000300c00102d24000d15009001010007050b213907680d041030503000b04040c0303510070611410255090b0a240c0194044000c250003419284298000c0d8014482a8131a401a1481102d03880b80108089134020004031703004 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 455049721 1250 455048471 455048509
    0x509010e1207141c1e1a010e1f0b0f070507031b0f060c020d020409081210060f0201090b010311011101060b0307031a2407050f01091a010e0105 63
    0x4140c0c844400c2e24200240e000440c01c06a46a802003151400c0110b4501300c03a09401c0c3c81003541030654070440009185440900070f0160041e040c0200440c0290f024040c10b05005044065a50340800400c854010740b980b0031103144501d4400d041c180110b40810944048942076444c011401000c00c04540c0102000e482c50b01680c880440020711404203104103070745004100c0e03401c6080482040311000140c0c0700c44280300c1d0f101341c244010780f0f0b4201c3d03403e201c940460b40062014490700f000d01c4130b441500ba06141e90b903642001c00c1103030b1110119403415a40176a40c1c40143c10925030b4184d08880c100c05000e41020743d404010000035a544050301840782042c50320b61005002510258290b80c281c1d0021080c6440100070801050360502c12010300c0341d040d0710011403402807071b004502d40484201030101044110300c00203080b424180704840f00f059020f0201c031580d01105060600800c000c14040700c114031920049a0480b5041d04441e042c0c4020000c023031960303440c00c001c00040112a695100b00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 455050971 1250 455049721 455049739
    0x909020f060c030c0f0307020a08030703300c031a0a0e1f05100815060f0714030f04030308040b0105150a0c02030106090e0606151804020d1b020709060f05010509010e 73
    0x40d1130014841444004045401141c4403503d40c4100240b002c150741000b0500d500600c4803c0100e6840f608203d000d03100f00306107000103144030b45070281080c001c3d40e8a01c5c4050034859840e1499505500403441040c1807041c803e14902072004020300c1040c11720458014142600c040344640c44922072000d030f1342d600d4145600d2110b036540c0c04a282c4098040c40c04003c14450000c02c00106100f4080c3d4540d404c044444c0f51402084501d8a00035008048020f84021050001000c1205041088130800c0302403680d01c0d502c0d541e891900a150f2a0708440c101d0711095404000201c81c00d01d51490310240d904101c01a0515011180c200d4101103501c106030307407541d01c411000075010340300c1c8901c103001d425000c090440e5203820418842e02c004030f0b110b00c0310141010002c029010100e681a09100d01080320050b81c5c404013803080c0ca0280080000708c40031551400110403e031303070f000900c810841c4c814000510845685030540d4681c40b0319071240e580450307400c0102c030328998400e000e8219204802001940c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 455052221 1250 455050971 455050987
    0x10080a180b0108060105062506090213021b010e07062319200c01031e140403020d09150804060f0501090e070819060513060e0312010909020f060c03 65
    0x6003044200058460707141c820018440d080c01408101d0140609440840c03034240d4440b02a4402202124194104002000d0480070089160002148282c00400035100000190b41c0f10000f58001002101746040102c18400700e400706001d845103110102001d409800d207048403e0768060b0100d14180c6441ca0b140704191a0902500702074032204580c003202031003111f00c43c1d00107803060801000200061581100c0b02c1e02e0f1400000707030344031414000c2ca40452004100790795040f44618003500e20600d40d003849001e401c0300f040400d03440c1c4514000d9080720150241c07418103a5650101e40200103a0011503032055001d58010000030750800d21504000543d424107040704002c8400031b820540080c0d0300c4513004040c0b01c0c1c0030085d410182082001030118100105c1c0020240f03000440010b00c174a499030005040251009544100150466000e101c54030b10f003160b05480f42c0c012280700c406104a00000b1070002d231284075085c102a40a0206170240c00102c0c1048a1b0790410f41c1d0400c880d01c82006500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 455053471 1250 455052221 455052251
    0x2481c1e0b0604050f0610050a020717010203040c0501090e0c090f0907021b01050a080f090f0f0d0311040e04030c080912030744070b0f15010e10080a 66
    0x18003040d015907540d01c050b050410820040c0c650240a04041d80c89550034000303117a8942503c800e9144150500c0b9a0750a55148181e041c80000d40c087e41080c00d00e40c40d0070702c0c42481900110300c1144581e807102e6482d911540159101c052a01500440a0320140002c03800c081d1a8001c1031a110020148001d1041030000522002011280c5c0780041e000361400e89100c0007040c18030107142e80709092203424964403101c0203041110040c00106490b0303030b04001c144441c0043c0101503400e407044d010f40c3d0b0f200d001c003042030341c0d124010391070500000e02e081829112044482c0940d0207540118410710165112610102c8000c4090407045d10400307000c1080ca0650750316502601e07a030381c1210000d152141c01e0340c1400c03c2c07100d526104660030781e180f582280490002c4008000892156070151203040407440207810b40300d000d0018010180f00842d803e0203c01d03034000004e51f104121620124078070184440044950510540c015504400d540850f441540d01840301c203548101c008500082d1100108001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 455054721 1250 455053471 455053523
    0x306180f050318041a1509270901060608070807200106031703060108132f0f041a01140705071517060604030308040302481c 55
    0x4803000d0b0b0001422503281281d070741e4a42c00c158030403942001140c442030045808122071084a40c407641c0f840308140040e10070a8195842e0303000c060700007405026001400d0100b00244803802059201800000d039241005000d03907016500680d4401d203d03915170301c809a8450201904041c14491f2886d407210301150240c0740b2840643c1907500102d41ca03480c60900c04e00342d04e4000681c2131601800c100b00261a40c000e0305090b00411881c004500425060401808444400298003502d009440d12062703110110352800300054012207940c1c6c1c4540c841c00420007110038840802005481b0340d40b540e15258068042c11850804000b08245021500d5a03142e0074601c25410014620704803000e411951a03104a02c403c04924103503003484c19041403030004290380031710b210003010440600002000c1620902c2211741071940210005500e0f80620f400642d20b40506104c000d030b600340392080d003001c44c842d505205541d010141c03122008524645036818401c2034060142d40030300c2c1d100c2000c2ca18600410b14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 455055971 1250 455054721 455054723
    0x30a02070303120b041e0f0b0d11061603020703110603090705090a0209031c030b030f06010b0f0405030a030e03011112010b160f0311100e0c0d022b0b0115090306180f 73
    0x1040e2006c1c0b502c130807900c017181d8844218034415403500303140400d2510b404d41e62540e00341d001296825500f84460001e1000c0c4500c0550824a940340c0104404040e0002103c0301601e114081d00c00c0e01100040511546010840d00340b41d8a42c00958208410700b8150b00040c0c011880c01d4005d80352848600205e171400c5502c5004008001d1085800c0036004e0349403003a83c4c0000c1d02140540a1360500880f042c2d6900e01c103000b296421500002d11440c0b11100780c04550040c0310240035140074500c18200034084040e54a982c0d070180d401c00b8800c2e8011144203040f21701c400036011100906900340304e6200d0258000701296040100d0410102001c80c0c0310704018a20a882a0b880d0001a000d0705000b034180b2429000d0003002c9414100c000414403c04502210455001d55001c1e03213100d50340c00001c0c0303003400d240400c0344c40000d08801101103480100e400d4050a014154400d1240d80e2140043c807510310300c00b103540000d414001d0a200003802508400b40c06040d20701145904401c40e103c4110b85103034004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 455057221 1250 455055971 455056001
    0x40f0204110c1e101817040905010801020901080c0a09061b210f0216030602031f06120605030f03030c0a230c060702120f0d0f0906060512030a02070303120b04 70
    0xd84a500c52010001004294140f290038059440070174210b051000046030010304815140c443c07010021507940130358009001d10b8406100551b500d00c1254001d600c004052030010b9115800620301d0f400b0901260300c00302c04c0f5940c69000070316200c411142180c01000e02006103010304d0b108808150b102ca00c43c0100d1200000038240c400c18940080c1c07000c458001c0c04019900701380102c40c8094148000d20040f00d0b0042070144c1d90343d464540c2d40700800085400380e010143c02071404255030f035000900d4011003404100421032552110b0805503a40710404e05070245d41d208000058a52400304042c2c030f030300192820712145281300100f050b4012105061500095070001c221203030fa40804000061f04444ac0d400901010a02030301000e50038840c003106105041c0d070016500c40381c85015440748100000444040128000b02d2802c08050f0800c0e202d5203200d50720710f800c030100c001c00200440b1000b00140e0010840b80349166815908201c0706000d540c0c1c0b041d0364052510352600c444c00349500326803440f0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 455058471 1250 455057221 455057263
    0xc0e04061d07020f0601141306060807140702064e010e0f16170f010317040b0307030515090a05071d0102070b030c1e071505040f0204110c 61
    0x4075901c1c159500500c54011503010f001e581c1444800440c119055441a1002c907407204000808607203681e420b511501c4459142ca01e00043c040d901c403e18034007e500d156101c41c2c2000608030307000080c0c010f8810182d441601003050f078064041c80c445980c17401540541d03845000031740d900310391085000e034200240c0030341980d4441c071140c583c40d4000a024091050709400075003403d05001c0098100180320003c1410564a0310080c14020340c2d9098801894281120079450b101c210151500002e00c4200e56032010101c2c003004400b0600309441c25114099000c504550342c0d0b00381103001c0d050261038405c5156008148245a450305200c040c499003100da40841c0600b4403400080c0300030784101a450842507000c41c10300b00c50b030303000c10704804851581d851142c03070741c071200f00600c4544120482510254508800354005a22840140402a015020740d14030000829400030aa07502180c0003041503000d00700000c010b00c1d10fa8441d80045040060311424000161149442d000001c0444000c0041d09 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 455059721 1250 455058471 455058509
    0x1060603050f0103030e010c0201021e0106150503040f0303150e04060b01020708070f12051203070c0614011a0705010e06181b0303030c1602150a08150f01030c0e0406 73
    0x1030040c81d070440c0c91100302e000c071903155031001807440d5020700f1054104842081c00030150784c802c100c510303554240c2a04005c480e45d5103140c081d008014134402c03e40114420552848043e0040d01030701d1290b50031000e00f20070303018542c2d41180103020122400e14150410700d00807441c40c0c0c909000c2032185201c2e410016100d2901e0001914211b0340368052403c03a070000005110210f031011844084a00c100e803101c1c1540c1181c43c00c207040c440e219000003081c0c540441000325540e441401c0c91040c070f005240c00c102d1000c00859902006d1030901804800044c1120098000f0712144000c103052406a0000900914075004a500349031060310740104407100802044200316040c04101e46000c1004c01846c03410700d00d039001c00d46034000204584d2416101056035484032500480600045600030700c1154881e1107158041000d0300119481c0002500c5a0000303006c09500b486100f004110041900e9000d466110044015000c1075600c00100072000056015584035401030b00060104402009020441 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 455060971 1250 455059721 455059727
    0x90b0c0702011209120f0c05060403020a0c0b04050d02100507050a08031609050f01051308060703090b091b100c02060d0203060f0118060815030f070807060201020903150a06080708010606 82
    0x30188488195904d4101840e0004103001110280240760b41002d206030090703040d05a9201000d00000b42850060004000400d60b0100300808643d1180c074504441307a8079074020b10300c80d0007035001e03040c0c00a84041200000d46088500d42003465190300e411460310844e030f52442d00741401c028007100d8001011081c44005450948100715140d80c51601451072440e02c3c0006051501040c40c0794188000040d070396102c880301c556000040d10441044a1490400504c01001408405002d0b03c0c00c08032000494802c0c84042011040311350881840c4c40414580c800b001381c41780c5074403040750600074113050302401611000080c118001000000684904c0d00909101ca2400d01c40c040c24104120045582d40e010344901d41352094903070f24a01039565036a10446070004803040803140ea4144174000c4490229a0000388110903502400207503220240e0381c55043c0d0070303406503a2160354150400a20b200c00d4640c8001c1c459441008200c003c144640d40c0e0681c2c1341089080c0d0041e8803c5e9456003800d000c1c65030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 455062221 1250 455060971 455060987
    0x705010c030504050c0d150e030c03180306060d0201021c051c200a080f04080d020706020d0c092d0504090503250f0201030902190609050108010f03032001090b0c070201 74
    0x3050303d41d035113610019500e40b4500107000d100400c0c10f594622032208c41e41020026103c3c001d00c00c4080701d5031034503580e803d03d000824070b00b407142c800d224250015500c3c0c104101d00d064a00d45c1a00180003400011184100c1081c0c4051504100b00b01031021280307040c426203111074112106540024421000300d84c1d0301108a01a12940a0030f10410000e0242076120104943c042c00d001948412a1604e00e4401d04602c22844011440d0340086448030901c005603009010305040304d1400c000032741e510302055511104900c118032070241c3c4400c0b27000c0784030000000041101075001481c9103150b201c0001030104d0b8640101034590340d0001c02e0007041d40c444450496601c1c282d241c6020136194440d42c0b05000031014450003410140c07610300301c170215103440512060405010396642056502d9140041c09002d46101301400507240c4000045c0440003c51440f0035250160b40da181d045604141c406401c082020503072312103642e544001c80124181a070760350702130f40c20440400d5a6440d180001400d001d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 455063471 1250 455062221 455062243
    0x6080430080906090a020d050106030605012403060b09060d0b060a05190e060a030c0516050c010e040b0a0e0603070f060e091f031b0f030b0a14070c03140705010c03050405 75
    0xd03005801344102c0a9002070310000c542c0e0b04556074068620185040c034090300d42640b005022500b031071b0001c5200c5c06600d0440c906032441e84011a00e00703c00c8407040701603030b51521030303951190b00400003844a801c3c22001844864129440404c120300400c0101c1c80e150300031844440018400301c1e601c07c030461702c1036590700540d2441c40c203188c5020562001071114800d045c41c0e003040c0355681c01400015070080c0b081c3d0b840c0d42c1000362641c18184072810f105468548806186000505083c07081c030343c610f0244100c46265001401c1d00913050b050511022015801400050340340c4600c40c0000b40b100c0c00c112414005d01201e6603510444100c641c10311991000140040701c1d4065420b15103031142e0108a8904103c0303800c18501d6007954454052440031240d99009940007080710200030007800022084a4001c10a9120404c24a038203411104440c60040e1100000104181141c0c40400c0c428102c18204460203d420741c0391140303a5a500d401c458000c0c0364400880d4841080005210701031204103140 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 455064721 1250 455063471 455063473
    0x15010311011b030207050402030a0e06090c0f0102120d0209010e060a090f051503070327060e0d0804120521040506060a0608150613030c063501060804300809 69
    0x2d00c8265800f80d02d64259001d42030085502000246945d90720f038000e5120f02c5e840d801900c61604041d08680d0301c1381046002d5a00520301020380b1541035100049071041c60321504c1d01d450174013407410661400307907000214060412030602c0d200c0c01d20342d0b0786200600075281c1303646400c1d00e258500300060042c0d9070240c0c007407803188109405018080a01d00e08803640002c246c60009412201240440c0144003419600c020b0036103580710700000c22103c0d91011080410b85000c4481a0360001000c0364441411100101480c002d0350031049003034010009002c01000c81e12541e1000700750103001001c50034003220140c80550001007400518201224124058035042c0340a01d1a0300d0600c260b005800b01701d41c0e5890003500c0004032060305420440010b0080d5501450718283d40d991140300800b030034429070340092054180742c05020303502000c120b1443c1c2e01a041d20090860f03840c2107002d903105400180151040b11100c4080707854a9248000c2a0b1248170b107552440995000900041c4900f100412040d01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 455065971 1250 455064721 455064767
    0x3050f04050a1719020f04050a15091409070302030a0201050319020d291e010e040c0807020609030405130b06090409030519023d060b0405100503060f0f031501031101 73
    0x581c640300520030b1001004d44022603952178200004004ac801a0000e01c204000c507840850301c4062500320200d0100500b101621944841c000307207894cc07005100095165000e81070180055001c3c401070344c0d00c0420b01c4c9407503143c1e500750a03040041c0d0740212006103400395100107481d0a84050352200c01000609950700c03e41003528404105540801100d0994210122641180301e1b0305c074003810003030400050024400352445400c042d065520030317200b00003d0300482000540e005400000d840456800038002e200311602c2092032001403800249058008a08004401c80c5450f076002c0e8100b6030b8800e641d001c0d5101889070031141c56000e80018042103420a15401540007200710700301c1c40c0d951a80301e03042086101e842c807612588401e44000844e45060920028141c202d0001034801c403541a07a040140314205082141c15200840740b0950042d68880c900d28142004400c40ca44a08041c003214840440300302d90340c80d6542d007640300b00c810004051103002696440940041180c0301c018030001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 455067221 1250 455065971 455065973
    0xf0608030901090512010b1206060f06070308040303112506060f030c050618030f01050f07050715051915050f0d05060103030c030504031e02120c010c03050f04050a1719 74
    0x200030f45100c0c2c64450201c3d0240c403040c18100794004d00080c0c0b8001c00d0102c05813840d10f0010749442e400c0751464461203140e0302032a01410500c0840746001d0f410343d00c064560340d460750240c0051100900450047c4810300c500f0400a61050203210000c8503a0201e501c44041440d0200541e1903e4101c204d440314041010800142c60b0720b000ca095840c103c8180c0d46450201e804090046400c054003a407500c0348402040d09280f040d40401d01611681d0030001456641030001d843c00d02c103913a4001c054a003441d10242c12204243c8c45a0780044005110400c242c2c9250f001d08141ca46800c8480381c040010101003216103041c20701d502001a059642c194402283d880e81501e80c0414480a028000944200400c0510131b100300c8014551180300c80c0e9081c4242180f81a5150780040c04900400420314006500d50b0001244400c1c840141d64550544030340e03560403200d54011617452011604140f1010600741e13101c214002c003401c0d000303a03042285189001224030f020302c1d10029410f26106261880 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 455068471 1250 455067221 455067227
    0x6170a0e0c01050705011413150c0c11180a1a0301150b03040311030f04180b03210d0219021005010303090608130c0306020a0f08190c11100f0608030901 67
    0x481d00e14003d00304140c94606030704205015021a07450035032040e2030f80c42044030107880d126500030514022070800c07010746980d80d00c070300440d6086e0b8051400b1540e5600c1c01c60000740b6202d08410a07000140050b40340d070f2070000400c81c00740800e99600442513290700f4103918404072044000151802140203000740394864400240c000c105010708810500000001000e1500072100950350540000440351788008150240c0e9094225000701c031520f03003651560a200d16128040d500408400034041e10740e80340c810000c50007402014402640b400350520108031030301b08a1000e00350b21071406101a0780ca19a24000038200444492590007a624190040c0080f0707a100415005032186820100d801d40c4070303882e460005458820340180702d90340d0040c0c04010087d8503009440c0d545109d44603803030240e844c4801941e00c10400c0b1994040400b01c1500741c9000340d440d0308226405a014101450303a0031011b00fa03a42482072400945659580b82e41d80040d601850348101030007011044040c1d801d00303122000007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 455069721 1250 455068471 455068483
    0x1302040905340b1e0d0f06060c0b071b0f140f0715050306010905060304050d140c06040f02060c060103081210050f010c0201021f0504060f090302033106170a0e 70
    0x40100c200012451201c1a200c480103150701c01e11200440f6242c0740c405d201107018000c029101c5410b181004c5001404074080d40002c131100307510004002c0c2d10b6460140454905086104a40d000030702c00341401c001c43c0d14180605855805103400100c000d8000e007a09241c00d0b0000382c0200c182d07000c10400c010341e00c0316950715040c030b503114a0314903541d4a80c0380040f84c440324140c126a0340300c20000140410020002003a0210030425101c40500500c131002480c1140503403840d80c50f041d0456000100000c5035140d0782115144001c011500301b480c007080365807400030300343c01c11581704070009010141c5c2d14038800340691003195203111190b42e43c02d00000c0342c2071150304860b803414041180b00e181c0441e0300074040f00e4003000f041100301541c1031100e00401c0191a0030340382503605074503007102c194101c842d60082c150309a4054001b18500400054040c5114101c41c80c68400000c0070411600301e0702002c000140144225601c001d0340c028103015404603046d01410f01020140b034800011501c041c04030741 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 455070971 1250 455069721 455069729
    0x3060a1a030f061f1107051e04020f070609140105060405070c03050702010c05030d0204180203010302030a170f03280509071203021c02011d03090a0509130204090534 73
    0x50b00900d44400d0040b41d01a80c0710800003607a82042a00001c285a000f9042c3c01e544000c0c400325a001c65071002480f521810888a82519821070941134469040580082003444680e034070031032819490f52100d0084412040d0200e4000310030f0480d40c0001002402620740003d01124100590704000b5405080601400c030700a0a2220101c0ca070b07800c1d6030085034100405a00241034980e41e18012100c41c0095105010300103070350740c0503010201161500c1c800d5034162a4050001c14104933181c907942e032103040808248900190420203a0340b94192039000d14000c0715402c8240e50845684a68662a05401c01760000e5080c030f403030200408200700055038001c0700c4c5095400d03a111580b030b0400700c2c10101d6025801a46111201e00b0821045e8154031240d080c8022007561041032100c20350715522485900780042d0b216400400510051400310f03d201d1300310042030b11074542c0c0a0968041380c180c400164003560380d1f4119144400f00402880c0010a502c0c200c405a2220420500c103141a00b410310b000d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 455072221 1250 455070971 455070991
    0x180402030d091d13020406090b030f030403080901080405030f0409021201140d030f020a05070e040318080c060a0e040c03050f011401080a0b04062615010605190207090e0303060a1a03 80
    0x40401c032804c00308401c01c00902e402500a04c502502c505002004e40000202c81d8001d118020000d464100c0200582d400d607a030000d00e4a2800c0e600c44011501204050000d03540b9002c100f001010b40e00c1c03d140104014090b810025847e00c1e40d11000c002d500105238407014018028051411803951560119204582d150401426101c40e02d9412860020044401440c0e842407030400315010035440c428a2041d0b2090752002d40c01c0d030b04248180c1c0031062901c03a1080e65480400031504500c0c00030090304a03080d00345890031504007444005029250500089800702c2c0c0e5900a00c0300749e0400514030b0380034100c98402c9104d40050000000c10310440140744403001540c131020040f40b6540c40d00f10600408070b455070158039281c8a054060003103010a105244d0384a10381141d68000040d22085040754480c0d20f070542407130070715168540048522400e11046021b00400031880d8105c52107030200c101100d000440c0c903450700c5410300c0030b1061160000f80c1d03201040c5c90307501d00c20084a4116648501c40507 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 455073471 1250 455072221 455072279
    0xc01090b07110411090a0305150703020909010e090109120e0f01110304030f0f05010c0f030f09030e040509100203101703043b04112701060f020c180402030d09 70
    0x1c1c3d1619031350052044c419400710082c0b0002050110004150602c81d01e1210519601c3d2181c0c0b6091301240300c2c0c0001c2075004140f03100100603590305806003e900030100c0700080340078003260303961a050340311640c41040400d9055000c050107040414004840070800c0c0bc04503030010303866604656034040d903c4020302040044440308200105001c82481c61380c0d00400038440058907407070190510040b6403000300045e2500304102c00700503407800b920080e0fa0700742d12450a644440010301018090090119034035210b06c0c851000c2e4558a4802144185000c28240c80340a007016080f400711041c882c0d10150740c2d44240300502078481e1421004107601c40300c401245070003002599a00c031002c02101d459204107503500c1080107020700c2a816511552044031011201c403200011180030301c2c1070407900307540181d01c03100600217503019010b65214003d060040317800d580a10b80001f100d0b1341404001001c02100f003805c4c0021400c08110000c0c00500d82d0502d04e041504210030001c0446003108040c19425501c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 455074721 1250 455073471 455073491
    0x201060e0619080d05031e0f0105060a0e0a0b030a0e071503090302150f190c0f0e011403160806030d0e010311041707030c0b0901080f15120c01090b071104 68
    0x862080014126802600d1308000f0035100034000da00102da03d40c903201811064040b400182c800d0b0144282203800c0d05070050f0b421f04051180715008407091005007d01880710240b25034802ca285402800002d520390b982c0e14080303c0c004155500c2e040110003581c0308403801d012900780b03101c07160980c0401e0310b0000b4548a09003400c900d004c103c1842d50303035506500024041007110790484c0d1881000c00680e90010305030010020012108001c0c00c01c000100142e80d1444014031440303e40403000c205141c0107000600d03260244240d41c0c01501d45980d0710910400107114140c0010308076030301c403904402a08080a811001418400320900f1940c109540c0f800b43e042240c1c0c280c01078170040d1110800d1b000101200503445980d0700f1007400b05581500c1e62107400a5018285c0040350041d88040e500c260b50ad485c1d0445805007890054500d0001c500a2840051143c807181d000032719003641c1c800284205040e40e8009440982140c02004001c2c20030420440861048501e10074030b064142d41c00110706100f = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 455075971 1250 455074721 455074759
    0x4060620030f1605010b01110a031107050a0909051e06010e090102040911070302250308030a060b070813150c14010603061a040605040b090601050a0507050102130e070201060e06 78
    0x105060642d09100c041000b0000e000c1d0403415030700700d41c130840081108840321801900e8011240c48050342c583d108585110000b0710600010300740c18601c2c8112859541c50700c2c00036003615050740145000341d60390849281070007002c210380c1c02030050660702c10042c4a0040b60440d00e842c4140540309800712401d002c00c04014003503040f180148405081042440c4142011201d1544030340e80c181c0052082c000d086654032804950a200c5050b201c1d01c000e11030749142d6400c07a00c1c0c0c00007071811912980d5507400092900f1100d00506103a4400e030350951b074a05140708650031000c80c039005110781030904c2d0000c00c605e907000341e24402c01540042100304843c0001206038090491a00014034060920042604c04c1d103408001451901044030244000350b01c134014003040314100036a0a43c04961280403401950148004040c080385500d411403030040242c44507400c1e68040c4400390500300c0940c0041001e031100180440d0401c0e09403000740203140ca4030f0500d01ea0810007900035803158003c000c00c800c012003 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 455077221 1250 455075971 455075977
    0xf070f0e04111c0510180b06040609081002040608041e1208010f0e0615032a03010e010806060307032901090213050a060f030203071b0b0402040b0406062003 69
    0x8105001844070009045200d8001d00c1504626003419030010140403881c0c050148100f00321440135500e2498050507801d02007404e0030280b001b0341d03140d04d1422251078120041c4060a050f031640d20041d86000340d500d160080d001c0074000c071241305010612242ea884004981c2068000604010380c019402013152248a20940104000c80355002c8019250b0003041d220b040b1440e0f6641000f0595480da50320b080c03800c0c112001540201c1d400c000103140c4051501442e04940c0801c160010092085100144850820308010250b07102100400440350761090060150603040b0180c1800e08000e0046942d811560200801104509000f2451540d01c0c000002d02c201d01d02a039400d0740d50f5501649002903114980101c081d60302010041403e0038107800b0001202c520f5592a10130000c0800110003e400c00381965041000c01c400089013032207100c0d40c0102640c00345c1400705440c1058410042143c60f0420070754000e80c10804100102a007000f001001920b4048a40c001450107140d6907040d84 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 455078471 1250 455077221 455077247
    0x608060609060d050919023618060c070f150e0d030f2f1612020c010206072102090f04020c07060e0a0f09021612030906050604050f070f 60
    0x100303811041900942040f401a0780445c140c8031304011301c9040104540024002135040003030641c00c00c2450b020009003401c103140c0c0d003201d048851152190616002ca00303544141031601030402441402d007090102c550080881403002d4036100c1c40d0360f10408502c00901025103604044540c0e07040c94112900000442c90380082901c0d40c81851303543c003070010003003101900c0c840c515107040817031643d0444001039000c0018980100d0390307100641c4111001c4d44112800806a00044c03040b50000307519800306400040c0a8000c0c0c9100841c070000240340000003003040e020845492014400904103a01309104002102c9015a41d5519034000c500c540b00e20541e00d035006480001c100c0a43d403004650031060754842e03039174049000760318010802000702038040c81c030404265610810115906038000d1030015550b05840e0301c0c11f4596143c0c500c01180b00001c52000c00e849403503100c01c00ca5548242c40e80500d0896082200b801d10752443c4a00040060240d01444500780503022080d014a20b02c40c800d07 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 455079721 1250 455078471 455078479
    0xb070e130e120d0e0c0301020306010503041203090f150b100e0402070309050d0b011802091c050c090702030406020d0c0c0302041d03030112030806040b180711070e1005060a02070608060609 83
    0x3e06600a44031000b03025042c126085805504001d01880c41e060003128042e00d0140e5509082d82c45503251800f01800b40c568100070316588100501c009010303030908200f181c0c0070740700702a9448407200105080c2d403422211944500b9580760444122070b04800540c0c41c424040da00180c6852540c50140d4150a1540005500c030304103e07100310400c100320840e14141c812091103001103054503510001640190a01c896000b1045141a0386e010484000140402c2c029011a90390441034000305203082819980403005070070014081c001d075601080584109092403514040c131070056114507000b202c8500000344034644a0404080c401c03a040ca039950102503000959a9950b911440030b04000000c500890206030410300080c6140780500c1084981c5001a00305a00c0300065030035859400c10081c605000e002d000c0c1c0301c07145201010042080a824901d500b4401803c21a0100d209036030347e170b88828414041002a1500d06502180d62001c030f41803400e2044c03554940c2d40001c0c4d80c078000c0700300c60b90308 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 455080971 1250 455079721 455079727
    0x82404050112050c01081005090406090614060103050c0903030f03090f0d110d09050d060506012f21161a07050306010329130b090f040b070e130e12 65
    0x1d810041d210891006103d901102d5291074198015a1004021a940d41098120301000c22490404166103a8005c1c8901c000040c86002e83d564101110b0161014860000a103020003110f56018800d0b2504411a01205802d20184400095881c403c50301e051500a50120100b03100000820205410046100598413543c2480074010440120f4041418962046400b00c0d105079014000b140f080e00d00103840a21407d41e581c448001611000c1e1443c1c2c1003103005011800e50755003070841e00c0321100c140c6817040340880300c00a049180064960101f80e481803070291289524960b0011a500d600d0b10038a200d0140d14681407601002000d240d64407042500d02c001c0220607644040258401d079030989041085070240d0031501084841e20343c1d03802016015491040042c60015000244042c44001c003181041c007100120700e0031031080da45401186000c070140410480d98011450303005840b8604a040103402500280c83d0740f80d03000318418000d9440224074001c03a01440703820203c144000006036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 455082221 1250 455080971 455080979
    0x709120f050f150a0b040501060507061a0405090f10020306090708041703180f01090c050402072a06021e060f0a02130b030a060609030812061801031110030c0824040501 74
    0x30781c0701040b44c890080c10b01d010803e492034501441418142c50b484c1c3e4481741025103955403500204445010381340c4400340302144a10a41d01d6002d00c61103148407401402c00303100f40a10451910000c00310391114203005208001841d160f641c1d80690100c42407500300304580b101d0514042c190440c02a60450b1000041003201541c0035600000303007501245d00302caa586a09040d042c0c201c9241c00341c010700c0c480008404201c546000d0b005443d005000b100c0504030500001d400110110320400d0100d250b0003034074000c210154060004200c94082042c005010320745807450a500c84c4d400404030307039070803100102007081c060950b8151004c0c20440112142c0003034403088844410382040362200e04240c100075000c03820b184900043c0701140d60208401d4204650401d0304a40c000d0300621040d08070168018440105071071000290085001b1455400032002e00420700100c040c10019042c14981420310b004071490b4031590340c9138050400401e0310502640c0c044111f036200481c0c0042507009041000110f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 455083471 1250 455082221 455082253
    0x1b0a1101020a0c1403030f0403030506010e04140912130909060b1908060604270203190803043e040b0406030503040906080d1e050706020d02030603060709120f050f 72
    0x140d142801000394413a020040c0036020354900c403c403502d908140700100803400003400b03600880e40242e4141000c8034100074545c085000c5840c23028003800da8070035007018071646030000d011f80345035092000d07961440c14080c140c030420161024032070000f0051d504c01034003061100c194040c1801540051101010314002600702d0038100d000e0240358001c2c00340201003a140e01d4648104444025101c2050302400f8684064442c45074041d982a17801d801044501c2d140700051018071484248a4070341c1a071282000e082080d2801e82242c0b4070302c035403144043c25407800b00007000102400c0001a50100741c419a07000803d0141c9140c0c0f480b541c000341001c00220412001001610584940080030010240d0f00c00040b541c405a400e011004107034405981d040d90030751180360304c4081002d400c0192a0010030340d6800100e070301000c00586d1965011083c012186010720049811258529207441100c0c240f4600894809a1801c0140b0440c40c01440100b005018800c04101d24021400d55440d8414901c1203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 455084721 1250 455083471 455083487
    0x601230316051306141b16050307030c09050402010e0310020d0f09110909012004090c0f0503191d16060c030507081c2903061b0a1101020a 61
    0x40400160620074900089218105490411801107001c820030762420800381ea50003080c001111703400004100140001e03d000c40003406910240c4000c000d1101c52002d26800116140c0003284070360000c3e00b04101207800e03000d0010a48101400c00605501c0cbc034801030b00c2d0f004000c0c00300f88d0140510008040c8070302c412340c0504001d2a08050074409400501e8044d02290341c25040101031440032003402010341040d01c0d91660100d55070f0300005400465440740111070700d40c120091008540014140b01e450814000d40c0b032100c005003030084100710218000f5025010080601101c2a6000e802d0760600c29150005000a111004001c00054200c518240c40f24000d00e00c0f50141310180c10f001401c0c80c425094100c0540c0c0594400741840d03034039a18151789500c00e0201c16101c040866041071440072922401d20842c0c010040c07050026000140100d50719000b142c070300e00c01d4101c041048008090b12000c140d2283d240c400050b920110b065099911744079080d04a0f100e0361011901c56280d980040b20 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 455085971 1250 455084721 455084731
    0x3011829031902100507080c0312060a0e070e04150509040b1008070e0c03060a05210105010b040f030807020105191809020a0e011d101706010507050a0b06012303 71
    0x9490060001e0000036a503050800402900b00b61a02d0100c113445106078003601405100d5120b003880e08c0c0000311300c0d80c03a64200420700c40d4031040c0c1c03405001c041d24180100c90018401200039002e24038040f80d024050540030000c0c0c9024035104c043c110140c20b0215895005803000804803a4103003041d04054400f401e0440b0000b14050440e0004268844005464170881d40e148103010a07075540c0090f80319484d040945010b030030688000010409517940708040100b0011122a17080fa040916116400c3d180c041c1e05c94900e00400f0032040c005010310000b0303401500c0d00540b18030f55400041c40101c0d040e02c0781c12015540a4001044d9050312a4400204980b490201c0424940703540c40751508401ca10542c0c8010000c00d1200f180c1101d0342d40540c60070800d4802410032030031030442e1a40070030b16000d500c46110b4002000d44403400034885262606540042084c6400c5013060303c0c541d1400c1c2d0b20b1400240c05014050414009807450b031041e0301d40b1100038189802c01850740384502c5440202d401c1940c0c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 455087221 1250 455085971 455085973
    0x11011a0406090b030d030207110402030a0b040c05090102073507030302010f050c0313050106090e010209010305160e0118091e1b05042907030503041707080301182903 73
    0x1c0040c20200902035040759000040180806030035040e03003a4000e5000030400c1301e102404950a003041d5807184041d500c55000105e0205155500000b04000c4515461311842408000d020601559900207810015140020091a2035000321080880031004500e1030140346100c2d003464400b44a0085041402c62344650000c0c0034041480d2304141c1540c0048407075150049050001480d540366051a84040301d024100020345c1c19101c0f081c42d170540f40414407401c00ba0390000380c0d01d260b5580c0b6105055101c4405284060400824980100030300d85940c0320074100440c0701000d0b891498002c40c00390040c10030b980e0402044404420750641e080b460424020841c0c0b40000c3c0b02e0040c194540606020030095491926090804c130110303000903059060f0b9480d200990071007204080041000b440e41c20b02980700c0039205e00c0c180c03509540d200110b44045607007141c184401c00005101900780c906407060703801508030318070311a035151008011519146144940c8000f0380c5034060f1035181c0501c5034940a070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 455088471 1250 455087221 455087231
    0x50c030c07240c0506060d14010509010b01170603030d15171c02030333060d36022106040c030b090f101a06070b09010612030c0201080711011a04 64
    0x1102a656000b40900c040c0160700400c00080251400b1209521407034403840340c818600c5e4148d41c215003142c170216180281e6a40d140f08280d220740c0c01c84643c05c4c8080c80901141e00b00e140172030100b030b2a400307a403813400380843e199061044410321420428000d0400d4081311403c420440048a07541e1190400c281c0c0c0303000702c8850241c1018804421070780305000480ea08491018208404a40d0b00c2880c9007540e000c103002021095282d483d00c00904d00b2121500c40403491109020041811000350314046075203050740300301e552142808100103001a6012280e50314024094024501c1000d40c1110120260103030b00b0030003041050443c030b0312040e603000e00021000c5595000d0703219a0380b800b1070210b411940c486610003100490980008040700540340d1014011261100072481640212038210744220740e035010030401c01024410394004014680c806520a8040c1e180a403035600b1007140a8100f1200d400040d000500520394501401180c3c00200403200b41c040115288814100415120ba4140 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 455089721 1250 455088471 455088539
    0xe0c042d09210806131d01060302030f070f0b03040f021203031905010b0d090614010303050a1b0803130614070309140303060916120204140103200a050c030c07 70
    0x2000420a1002c1d03aa20b4600ca180c44030010020308820814255005039250b40d501c0c0707038501d102d50380718060401c4140007003100d074214810142410340c1141c004200d940002003c101000705258030310100c0d08100040703070f56034689003000d4081c0e1301c5002e070194008400b12042c001d0488000000c52144203040360100580b040f80b44200241c803800c0c0b04071448080241b11081aa620344c0d031059154620490001442c00c80000320700000302c070245e009a01141020880c2e8400c1074112590341c180c2005281072040044031075841d04000d0202074044c603140031036000407408010043e440b908031100b05c010010100d241880c40203025041c4880d0440e019107184020222069000050b03a0041da0010156019a610701403240d02480c003240d080c00401c41d1260511088000d244000c1000d01441380960401c05140400902520004480f220850f2044128021103031400f1080c1c0d0010305d0f03945000d9503a0701050075454614000c1c40e201c2100e600610750f00140040700200a40c2c4c402d4030f140903c803a81288 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 455090971 1250 455089721 455089763
    0xd120f0903020c04020c0114040305120108060c18060d24050109210f0b0c030103031416030f02120414031c05030403030b01091509090f0e0c042d09 65
    0xc400000700981d020b800740b2956490103401070402207046000000b07142c1611071101c03076545419241075000c00d1001a0754858828100f44203409042c2503030007840c181c108000e43d80018400c0303482c91034603401d25083c289201c0d91441d04903640c4204101c0c0034000c2040c2580403103441303901540340c1035002024040004455016411000480b6032480410303905101c0c01d05141c504c6040000d040322800300a034006800144070718202030080304c0250401c1e40700e43c1546005808281c1e2103aa5101c0d41c042031081ea030014008039002c07241c06138140780040e080560b40174181d10b449131806a98101400c0420045808180b20030216100c0808404481c840c0000e007045a4000180c0d840030000aa42000003802080c000d0700034903a0840185480d0101030742e100b003043c540c00449003540002134489032040240f010fa500075180e00002c800810802d41c9210032099a8404070043c2c002c2c060342c1c403040b62044011006e07a144841222040080550082051581c0001d01070b001c030072034124050b00d00301244400d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 455092221 1250 455090971 455090981
    0x80d0b040b0d1a090109021806010206010509040b060d031101020408010902040b0103020a200312130605090c1e0301060302100504081203040b01030b18030d06030c0e0702070b0a09080d120f 83
    0x1801c421a44080f80e01c081501c8860003000340007503229900c99500500523181c1406126800c0b0b079818440c0f042c2e090900c00207051000603842184202e140300c052001080c0540001a0000802c03203c114044207985404c4c0c550312807110f50708481d54404200014089019003180030f00620840f02089061b65600c010b504a00446071031500040c42c80d02c0d060324010003860851441140c2c682186e0809070000314910349507008590350100c103010f041312002040b2260081940044245001d4821039007440081800a5003428903820754025058140b030890301c0030740c040c20246402601c4407100712413125001e005a40705100340c0c1c0181c86008000340c00080840b066901407a03200d00000f5442c0d28503199900e1524001d08841c02403418000303009401141000100310480d2400c0c0080b440c02d04d18100560616440d0f07004011441e00d807010008016030104e400d400381c620904031291102c0c46008100c81801e8542c1040340140301da0680c00c0f640c280c02459217501d170070085405119038080c00112809541c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 455093471 1250 455092221 455092223
    0x1305060c0a0f0518100c020405090a032a0c06030501150c051009060f0614130b0303040303080c0c0109230f2d0604120225120807080d0b040b0d 63
    0x1c2c098a00c07001041d115078000c1c1054206031110744102d654800001e116408403034140b4010500e10380c030f6001142030a0003040da0289441c00503050072001078034003600401c010034074003002c0900c00e000103040c50161a41100491f8010041410035a252040500103060a00818025008549806040030300c120b01c0c1d080d550b0350003c0904a41070107022907d02800405038226000c030740355030305400c50701c00d81d02c501c100500c8200d265038a034000880a018255022108000c1036605146481e403190700c1c000226401c4903414076020f0314a54800356509940d00800001210550030a2804e000f4051101641007042c0711883c8209880a503071240950b40d2100000502d4441d00030350380080014101364003051171401160804030b8540c400600c0c450030504201c1e0119185841c45042c0080c030b0758100420003032038654031311740003403c00f1200040540050511500079a1300351140100c007002501c01c203480d102c03503000400d9902e45210300340c81009002807084171405289800c48180300c920786020307000851 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 455094721 1250 455093471 455093477
    0x809010801080610031b051003060f090b0a0e0405010605100302030601090501080103120806060408071805060901050a151206030b090c0411040608100803040305031c0c050901031806051305060c0a 86
    0x1017461640d80b8030f034a0b036651054000b406140c000c0000c86494a4204903400b680303966000407480e04162241e0345034009504085080352070408070030302a4841032000b5041d034075a8034080340555030303034a0000e0140c805900080c0e04034600c2200700c403282c2d030950050f6000309000d0f01c941c000c039a111001111050400d12010707101581010200c070110380903035425900b00402401c0140781c02c0d02e400500d490001c00d40e03c044042000c01d810242240700da4802e40d030b0000380c221343d0402503500d172400240e00d5510901900e122042d035040c185c100140a80c0c041004210300360403d119903a039a0500000e413020849221403203000340c10008000d45414070032494110240b182c80c6080500b0000101c42c0b103000281801302c0c035481503501141400d81040a000110b1140000b155980d008251002c0d10240d420500d4040504040d442c16606400c942a80e484200a1800041000800c3e04440100e40348130744c041c000900d00810301c2060741d03071950940d104078050130444820380c84043d402170342441014410800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 455095971 1250 455094721 455094751
    0xb042409020703080c031005060f0c0f0a030905010503072705031e032704020d020415110705010302090120031806120f0402030a060e1605010e030c190801060308090108010806 77
    0x5174a08501c050b5402480012142516a4407080070896540c443c9040c008100c0c0c000c2144107540b84100154001e40c207418001d409000200c2c0c0c3d0103040322410707015a50600c4404000079502c580714500103e0b5000301201000c0c0d102c0355582c0c0718640c8000740d004031400707406000c4102c0c145180214840e08032002c03840c011898011001003100d5411b2510300c81c0508400081000003459582c1d00140174000764005005030b542e89010035140d40c2200c5085513509100480303c01ca078402c1c2010948104444c001e0030301590b00c0c095440100d40c0c29256002844070248040e003080c820203000000b030030640783c0c004194005909918100403643c0a01181050307001c120300005001403802510031504944050121034050b60075a840e030342139411100303005c3e034154424001201540f000d1030081008080a003000f0071502c0c0182d0100342c958103038442540c003d0101c40107042c40d061800305840c00908551000b0040682c603803521508030703031110b4080360000c1c54a100101c1d003d1004a800d6002d41e00344405481 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 455097221 1250 455095971 455095981
    0xc070b0a1107060e06091608280807050f0706052a150108010c09060f050306040c2003130b0f0316020709110a080a0c050901120b04240902070308 64
    0x30242624500d581d1114805000b403500103149401900303040300886020300094034002e130310301740b406003005031032400050704501c100502d960214090f0744028180f0003d040b0070f002c4004030b0240601401c00104000c034000364900c18800e006c5403200800c225075042d00c0c0950340d0751808039107a0203840c11a03140c5c0c10780020042da0050032003640e08200c1503c1003d80d81ca070b0054240301c200c258026407010009035142e8102c8000c4592142d00b4101031b0550741410111000840c0004105020040c80f042c003440c6c1c1c1c1c3c2983d480c55406a0b1080b40c050110765103440b0b018000f100499169041042041d100b040000300100d00d612180040e144120028903a10341903a80341d0042044503541521100f041d40151080030690004a00680d651201c591050a41d2600d4400c40200050402088030000900d0000581805c070f82c414125503a4001c24640b116150700076240034001450400d0141da1f0182c5020a0704410710721503148020821528001e00302aa55221484000d910070000c0c000c00081900e80054 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 455098471 1250 455097221 455097241
    0x1032a200d0507020d0816060615091e05090a0608060108030a05030601051e040b04060e0427020a091409160e010302010c0807051b13090803010911131d0c070b 70
    0x100d0343d5400142102d0301030b0002c1d2516034241c3e01030b1100000080d40c12542d1420710034a03018542c02041c03801d00d1102070032802c1100806003046806480c0021501d2130130203500c4000e443c1c134540a440d000f4101d01c40f90402519000003000c043c071502c5028088c240000134103890100a861600f0102d80302c051640d60703035000458056100c50170608000c0400788402000001c4800680f003d071a1180015a80b04c1c00d004014000002c150344c0c69110324100400324100c0110a032540c040c2c2403507001c0300c01010204c0d00c0001c0c803001480c0c1000d45101e00e020010300310043c00d00856070262115a050b40c048584850b00b40c18810700c1405220302e000b228400400c0194881c1c0c500b50146401000c00314104501c541d00d2a00749003100008008001d180f0b080411340d440d0000c1103010300c100c409010800c1005580c0d5610141c041403044010443e80e0718601c224241ca0034013158280c00c1981c82c4400099103660241b883d1050044040e210040c000f40060f90144102045402107a040021300107a562241014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 455099721 1250 455098471 455098477
    0x30603030711010c0501020a080a05061e090a020c01050a05010609060203040303141b19060b03070e0406021614030a080f060d061509290d031205040201032a200d05 72
    0x450704002d0744184c0b20703010030b4080c80503041c807242c2e40c1d9400c5100d0401c800d044083d9100174107094070070700000310003443d00620243d00001c0c0c120241c4440b602641c1d40b100720b400074003980e0702d070304515403c020800602e0303402d95100c00e050316a941c5031503040940f41c0d4000ca0b038038000c5000080200d0380b0b41e00ca203a00180c105010340103a80e4400460010110040000c0e03007011003810340203100208000000301041035034065240c05480950040446c1490a80714100e00e280150028010b183d0010350060b0380704043c00703681000c0ba0400d00001241450800c41550fa42c01010207100140d01c0c0b81c08118807824281681d40642002401010655003503201c040003081d4a60403001e000d541078a00140c1805240110590818840309020400c90344c41c8813550b415172080d2141c3d102d00c900142e20f40011750086d40704904001011800219950350b031005074020040101c551200c000c924098190040e2080d41c000c5020026581c0c0c40c8407403c50803200441c5050381109105e15401150004942610a90107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 455100971 1250 455099721 455099753
    0x406030506061b010c022803080402130528020a080627070c1514041502040b030109091103070821160804080d080c0f0a030b03011416050306030307 65
    0x20b4540340109140b00b441448500907041c150994454620032002c83d014030400c1150582010022005941601c50100c0080390710001828054590045800d41d240e6042e000c04800035601c0400203800e12014041e417070911440321554030410600c0001c6011014000d0f00c02c80c202940ba450310310344030300081003140c40541402c92055181d0041c240010400c104109015000ca6214080c4030f441900f481c910031120380c022030703041a051001c6d081e0311403000b6a02c1548236400000800b01042500031060107445150b210b11a885c10100011520300c000368064135095100d02104210400c0e0142030603100c00181c841c46041d50010240095030500740340c41c4241c145031000c1407a1400780c011214086004441109984240b401301e400c0c8072070802008082c05822413410400740e240352692803101c0d0b504c50782a1000d22403001007802d001c030502941100d0021a8014000c0c80b4a811696504102d08411a040000000080e00001c629030082086a00840003d80690721300801c54403a416030f0501410 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 455102221 1250 455100971 455100979
    0xe09071703030f090a0203160609080307050304050103020a110a0c050a05030c030d0e04270b07230904020f180f060a14210405030c06010e281503051608030a050406030506 75
    0x755050050341c1c20300810f9090000e02442098083c09c089000f402d40c19a60444140c641c800c0044030f0119400205850807604246001b5075158981c80d0216200c003980c1303110708060700c036101851003007006200d100025240d0580349174101075030b00c908150b92031030300344042505900310500c1c80744078500c6003907401a181da015202180305101204010804d640704905c80820340029800c48080000c84058150800e10a02d050000e00c00c50818281d21800032007103d90005100092429407521903805465081010511054950580350b000d031850a8500c107415200b02d803e02c4800c070301840e000094440c0c000c40c6a81d00e1000c0540090000c249030312025200070001c151354034101300315150820851103503120307030007854a40039482c82107498000103800507108031002204214410446801b00044100d00e07501c6c1c9515102d14001c240d009069080413034901805c0c000c000f2051240c0007807041c802d0185001507241403541d440038162a40580306902000800821040000500c80d400c1aa08114024 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 455103471 1250 455102221 455102233
    0x402060418020d05090607081815070513080105070e0f18041202210a0c21090f05030304060c0807170706060501030e0f06071101060f0e09071703030f09 67
    0x2151864042280c508064041d5000121640450400d0240b1900102107034000c0181b420445006403610030000c020400104c4010801120300b4000c210303510760391300020544921030400d45002481a232221445070a9034201e9000018841c00500c02d040c1300d00c100e03079180c5900c0c00c160420422100d81590742140d00100340050403540281c1c2402c21400f40f4419083c581d542c581039000603080851003244031140000c1104032002d000703401012220a94a0380c13403d9211110245032145451008040d200180d065810351000441c0d040411401600c01e0022003926144d950b0082503541d208130b010305000213889040340e0700083c00f000050302940340b0a10111038090107292200c51550045402070340e205440352410021560548a00f1650341c21000c00340c4030101151240c85d540d148058070403030401015a0020444c400c7c00e50264014100510089007004e40d503c91541c624041a0b070302e403038507008040c40001d4001229505411760001d04000c0d5041da610310003141c1c3c0c1d180000f06134000c240502 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 455104721 1250 455103471 455103479
    0x1003151d0102040e0103031d100309060e070e0a111804022113110907021b190905010e010819020f0a09090506040c0501030b0102151008070e010503060c040e0f04020604 74
    0x28000341002c0c04c00c8003000d118a43c503604009100d04070700d074a03807800105510032010031510b450f1480c4440700c03280c1c02c0110f100c5820b890040c5c0103094000c0510410300038840c020070358800c01d804c06809100310010900c007a00e581007030a4200e103d000c809182401c0300421580f61030910f40c0250560303101c1c8800d00c05940901102e07940e800a81142c1502c4040d82002c8440301b0040350b844d60702086031064030809481c2c5801c10020799500122401060007252000300704c42e542e0f42e4000141040c0c081e0741541440296105071000c0070300303000e004100e80d1712290000030402450000348443d0303005820551002d030700150f4007481440c075541c1100640040012501280c1001c4a0007032541e010f00c524010005440c0070308000c15540c62075001981050308001e1680c000340ea00240041180610301010003094030358458641e103101840c0c2c4000021300a0080000e140480c030b9030740c281200c1055060760000c2d41c644402404030301c82ca0145110803568580400d0a00481605081e071103403024001519040e11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 455105971 1250 455104721 455104723
    0xb04031b151d061803130f18020702010e0103050a020417060603060a1e05071404080c0a05060f0f0c0a021804030e060a08010312090b0d020403031701050f010503091c171003151d 78
    0x101c2e0050880c0c01001e1f0800c01c85074006002c4041d0003c610ba80450030304010f540000e00c01c001d0500340364100340c2c454000c69800720180d0b04803070007041a2140c80a0f8802041c071400d8854804594440c8203000300000210112514020902c1030b00c42001e007171942a205440d03880003440042c050008014140042c0c0c0c0c000545100107001404000c002041c403000e502c82001166841030308524024032080c81900e003203481c50001d46026404000303040c1d440d0a8504003052900d42c0c0842c3c082e41c0403501541c1c80c403030b48a80a11140c029030207a501c0400094104081c42580d200f070b140307903000083c1240010804542900754a249104107071030302c6480341741e8a0022460641083d5075940e2130a500003420810140c000c0510131980000f02480c402035031500d00000c025410700c1080905215000001401442d0b003031203680720704040d0ba41144810003c4001c01884d0507000f13454003401141284c0841c0211549403c0328040b0307640700210f403058489940e040f1003d81400c5001150554a588102d200100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 455107221 1250 455105971 455106007
    0x211b031209030801050310061a09120607110601120b0708040203010e0a1401062907170c030a0f0503040507050418020612090601150c0b04031b151d061803 68
    0x4000c3d69000e28a504050815041c2800c0b403100203815850124200300100c460350043d801d05041111490303c0307000d00f10100f0280c40c0030011001072400b4103400c014149801144003172904040c101202d01c3c40e031700c905042c607040c0c8401c0ea01404085e0a04c0000316210301c20841194014805400070940075540c0c2c9140746007444241e0704840d01c0e406151988691002441150014210040b4281c0c1a0032920812012851a05400000c1e1a40060113400340a0b68200120400503100592580c6110a180d06a00e94008110318400508002d91070140e03e880381c026a4012604400a0318a45144c01d013080010700c07000c0400d02c60030180d11149005a80da140280880d0f4100002882142c0703001d22201e13041050581002c210398542e0f40608580c0e41d03005850000c40d980c0020181125112401c09903200c001d854aa001a641030000010400409211400d6117100700801071025180c24081060a42c440010005c0380b50b01140000c1c11022541500c41d464a417802c0540703180c40b090720b000c0e8020903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 455108471 1250 455107221 455107223
    0x30409110c1009020f0f090406020d0209030d02030702010905041a0909210301030506130302060f0c0405150d0c08090c1c02210d0c24110313211b031209 67
    0x3680c3c1e50f180f5403d50070840c80381d126850007220300c0c00a175194840062240007014101030429035010520f00003585076a8120303000c44a00604582e600c060ba07da0007541c1c0d40c4072001c200d0005420800014407420701d070043c80541c03100110704031502e1581c42c0c1445104800288441003610500d2181d4058880d0f03815180000c120700d82c013190b0349604506004e8034102020344031000c41c07c400e05050011a43c041003103034000e803116520790041d444c0e030b0340e12058600460300300d031703512510380541d040904000c180100720018840e4000e00807400e50200c19900c1440071a040c641d2600602100b80c01481c000341010305400800002c040c1603000b5030003046040d103001e02d00380e452201120310444031410400c00c0901b04a0f06107032404083c1500d0352410700140c058020100d41700070280b0400e58902c090307040040c0558880544507100e141c8442e0700581c2c03510222043d543c6a048034111481400341000e0031883c4542e540b600c041c100042201030f03174000401302040d4104502c51680c0ca20782103403409102115 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 455109721 1250 455108471 455108503
    0x140a17100905100b09060d23160e010e010e13050405152809031b030302040f08070b0a0804021903111f091503090c0b13080609030409110c 61
    0x1050074407111104556000e00080180000c0601c2000303405000022038030094420381d6007544541c08014410045c00766101c044140c440304c4424400002c20007141d207071081c2c4440346030100404007180141c032a4071084480c00d0005101081c01070055000d100c140a481801804944580d60b488407128121441942e00b10380607000000d44403002008544034581040043c0c403400703190b54000800344104400c110318140003030b440328503c00a050094006071803070a10b00202600d0040b00c0e1a000b00250f0180c007541d900554044004601c0b414005005004c2c0c0c3c0042100b0f500d000120301d4284d5243c0c50085c01260b001d800004441600e411407002e450046204600307080d440d03500d500030020210243c014181e00301c00c0c0c06194080e440d510040e601c044030b07406d00b407000090340b0300ea000714064501404003070111208684006080e4841200074490221048154242d680e120041c50fa00d0781020b0f184082e45501c02d200500065005038000d400e0141198140e500e0000000d201d541015540f800030005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 455110971 1250 455109721 455109751
    0xb0f01180b0c070806071404030609031403040b0604060609030b01030602030901021603020c0901090912110c03030406110706090602030d0c0917030d0608030a02030406031e1b0201060e07140a17 85
    0x2c0203404103c4a03400000c41c3c1800011040201000704650081e4070000e0b0200c0c2cbc80d207444005060180b04254425051a000181c1d02e260038240440800320585c0d01500032442c07c0000030708030344280c2a480039203070703c80c0070b8407007991868460401075040036152208a541c20020b5000e0241303e03510208400344a500581860303c0751100b00400940c05a0041405a0405a50800040032084542e4414655090040c017001c0786550302031404205030105900743c40b00150216919070018100040e1450482c100d40c505515103008441170308051040a001d070b0b0040c040700380d00c013440d60050980e484d0b140c07400d1810701783e8900c0111030f6034441d04c510114030781001802c940356082d24007411002d0000075000b5071500440b880000c0d41c0380f02d0b900c640300405a9500260107002c00c0100c4503c610201528140071040007040d48000011901d60408050340c40c020000a0300b040f00c0700002d01c5002680c07100151858010301510007076206101400c104100b141a01304000c02c0c004025000300e682c4001e07444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 455112221 1250 455110971 455110979
    0x150906030c020105270705060d060f0b0c060112050a051f15030206093105011805070207140324091e0618070e04051b040b0f01180b0c07 60
    0x4201d5244040640c1164100403c01c01074000710a1072074000804403c04980301400784032100e04040c11900240c1d440900003802400c40c000c1d13a0400c20aa41d03040268600c4142d071601003540900c41d01802110036001400104010803081042c140d60501442c2a5441c191069a96a050840000e0460451100a01e041c02c900a09204054030030880c050528845811074002841368010245650701c03962000ca0080c440134a030384030310b0090080d1034400807030a01294502c2e0f0060442405a05002c204009505030064220b0260b240070f1040303a0040c100c184c0c00d00e80c42c02ea00306e003032584c4207030584a65825060402d2404440d20030710300d00c814608035582010001641040e000200e0369024130500a651400100c010884035003041c120000d104922a104441c50f081c000380d940101c2d00b40e44003a00708824084080f40d161301d904000785041040a852804100850342d03600e9100b50032001d0f040364140035501501c81c010001d000c8800c10034410390b0710180c140c101d41c0a00d501042503003100d80208 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 455113471 1250 455112221 455112227
    0xc060c1308030c0616020a060e060a0506090c0702010c060b03030c0a05120a270308070501060501180b0711061b03070c080106050303070602130302130e0d08150613150906 75
    0x210260181c40055898616070942603135a511010701035010b0501c00034151800d06008101c040c0a080c0c1c402800d1081d240c00d00d80c070b9512400200c2d04014450b007000c00040107450a00801ca01c642d1034001090309041c07041d001159281030808080381c5081d5144042403c65400300051311031200820020994041030303182490502600341d4035000300180c18080591507540241c00c056040302d80b200c1861810640c100c40b40000c800951022301503000005003002800419003114056650a0b01d0b00340b820f8800c02d02c4115110070a1150b11300b10380302840510b00180705292803000d85c0c2402403503242070440054121040746440c525060160707200080c5e880810280a54000007409154004c2000d5880e01020944034410480c000b8441030340090841c200c0855441654061600a032008a81c5614100e140c4000e22598003010a01d22842d980f40c00d24622505059204880b590711982c20040d40c030061000c03542102080400c0e101d040800480c0d00f0380c022800d0028560103641d01d0035402d14040c005 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 455114721 1250 455113471 455113507
    0x1e25080903070b180f1c052802010905060304030e040606050c010f020703090e0414070612140709060c14031809130f0f23030d060602031c110c060c 65
    0x80c4a0f0010700000c9003071030281000107551201507452891001056000443c0380e001d4485140b2804812619007090110000f040214030040030030300081010401148501c51216143c02400507040c83d80500403824014007450700030f07100b81400c8101b400300c0800501594001d0704400000340022401c50b080c50424047d0190b03240c44000f04628004641d00d00604804950240850607a06c40c0c000c94200a00103041602074081b9409680003240c80d00c0c40100001c15031140310342200d050040307400c0746c10115401203000750b11540b902440d69103000c80030b4480038240702c02a6010010300303211100120051000f001c502140003021803100e4441170170041d039070314080e000d0046002d410310f221000460780c1c010001c065810480001b40c54099140400020600c210301e49041c40b40040c2e580d0340418008040c100d280030300807041c40001d85a0703c080b40d0342c3c050350f10b8400f12190340b5101c650108100d03901400c031303041c00044401d01d0000b250540718600f100170780388032840d4030001890906881d1442c2030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 455115971 1250 455114721 455114729
    0xf0c1212110705060403111002031f060f091a040902040e041403031006080a0f0c080403110309060f090102070b040e0109060b04080d1107080a1a0703021e2508090307 73
    0x7401d042010544860355a6180100001c0c1403111694620b05500010007110354075810440e0150340ea0314002000c1d1050400d4010030420046100001041c454014031a0180fa41c1c92540c50104c002d00e0300390806030381100711941440c002d404000108694000e800148045c1612065846103030501d80703410001d9540c4d01d826448180c205000f40700740241c201f00c000085032030900d0502444c0e120601003000070290807462080c03040c5070250381c1e044190032a6110303102d5402500c03158040c140e100800780d140d20456100a500c0700040000c81d00c440d0b0030001420041d0b4040c412607000e141c030b84030490b00d1035106810112250704080c00401c6a420036014000c040e00c6540e00c2241424a407200e007907a94411803200307406000941d510000f801c00d040100c0340060815100312100e40d049410000c04030800800400b9401110300c0005070b0150182c0200c03101e501d2a002c0c1000c0e2004070390218002a001000054008000707407801c8bc1c1500600c080815030300d4054010700746c6d00c54030041018035080003070340 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 455117221 1250 455115971 455116001
    0x11010f1d1203010b030712050f04050f0102090f151312060e0a02010e01120b0a12030305060a08060103150e060703020c010c0801030b0604091103030d0903090819030f0c1212 76
    0x30805084074000c0003900e044403006843c01d5229103507050b080d00c1c608015417082419034034240c10800071a204030308960007940204280c3c1c201c800405030580c244e1049601c4030b50090b24140c560b240506004200b0130040d03051000041c100228148000000384641c1c0c00b010131451006a9281403240c640f00b442c21404c0c1d83c40c014038000c5103580c006000c80c030172001d1042c18414a4511040d900c0000c1e0030900c5585801060b55000036128271035166840544441940003c1ca0032001a49504204900105a84107100103060aa10b5991410081310381500c4181c030064442e11200c0d21440c0030060706004a00d10348025881c3c480c1400c0c11030859020021410400a1100041005c03524200f02907410900a4402042e504060b0070441220b0f040910401d07010b01c00050381c1b9841000942c41604194407035501c1c00003099940001903618283c5070242019600b10741c02000000380902108003150010b4141125409400e4860425045952040d0300c042040c007000540907007854170a0303482c1400450 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 455118471 1250 455117221 455117233
    0x50708010506150307080f041a010927020a03120c0b0c1c14070525110a0501050c03030601120e0d020d1e0e0607030c1e170f16020111010f1d 62
    0x150001b00141c6020b4040144114801c0100d0244020001c2808182205400301c0c1840d580d60203e410042504005480e0305001d002c07070080b4120071158030300d940d46400600074050300b0300b151285041644400010030600c54980c1618000131a1840c0035841040312483d95a1100d40a1030b0740304004828040f495902c40c901b139041d5900c80c2181121680044e413038604075440c0c46000300d0391449480c11040303000c0d1412a441031007080141d09000c130b07840c403801503510a08280d6240c0c01941c4501420b03407416000d400a03c005032055205a9180d40c2035891100082140062001a5400e215412a8020058004601003103110f80c000c80144801b00e0504400c190041070100000c142c032013036210640c4994400034844040c941b00d2030030211000c1c0c1000c181400c0441da10a61000300d14040c5040780c3c00940c1010703828078161880156034046001c030003564584460300d840e00c0f241c03040c285012410711a00c0701400350b001a0903c242c2d8110340318281c00148420110307566071048403e9188030502c030780c071007 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 455119721 1250 455118471 455118481
    0x905031f0b010e1f111b040f09080d0e0c0d0308100f0f051e03030a0c14060f150103110d0605010e0d080417010204031b090c0305090c0607050a0507080105061503 71
    0x18203444a41c082c013030f1a42c0c40740700000c80c00450300c1d10910f03c0002038511030700300c690a0f0742508032a160b2482004032403c0042c220728002403415a08800000f500060f41481800e000314100d812183c01158500c0a441805081ca800500c040c1c2520038141d001403c1d2400f040055115641070202810300c103010001114a811501000c680e41802000d010701c08690101c107105100c00c0040c5500341000702a01c5c1c9178401141d00924195201c001540e40340303101410180c89070390101e0004c0c01850240c01c8840140d490354001d030b00b4a09555083c5e8100355076640058034000040000c0c0030712913442d51011400784d181000040010202502e00b51084031180c1001000441d03000854040303c01c80e0b9004000b40c1040804540240503a1348040c03e0100300b0070810300e0540c01c850f41941990201a001c02c00c50007080e0044041310310031981d800865118507a154080d152480140c40c07540d10400c12150044881e5a50324184405070740541c031139030b440e04188101440c05003000000700302000f000782d00311b24007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 455120971 1250 455119721 455119729
    0x302120a050f060d020607050a0807020a0b0a020d0c0312110d140f0402010f0207031a040c08063d080303161d0409031413080105010f0b0711010905031f0b010e 70
    0x4040c3c40b591103124040c010204640740c14042e0344440b6040801d48080c0d113068140207500d648802030403442100d50b40f0020503050140410390f503260100d6030081010507825034050320820312108003502844940b101c004d41d42e903020f005020300d98160a40c1c00d9160350918041d02c094514110280d4121a4030340200306409248844040e031158091030462b00100061000341e00301515074001074610b001c2c0d030444d981204103121040703000d903114060b0072210540c0d450302d454a0b150180c66000108034400034030181c1030f004650b100124404809809a29100c103c0b0303200521900b50301050741e80c0c05c040204900351004441d84000f41d02d080c10046044000b06645201642000d002c0034815035a0f22800000e043c8656001c039a07228228094564804407080c8010b91004c00b4420407400e9800c1800100381a0007604159044810004015090007a0b03075862460040d0309145040c1003241c00180011295801c01030010403d91000300b104440340c096207120141c9201050943c14040c440c3c2c440c11141d12 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 455122221 1250 455120971 455121001
    0x9150b040f14150604180c0e0d0f0f0c0b0c0a0b01050d33050c0c07081c05090411120103060b010c1e05010b0405011715010f12110a03030302120a05 65
    0x2906440308540844120004d140c1d07005540000404440d1035a441002010507801460280b80130380315541d0802d600c3c03080001c60700130414000c04424154016400180c0c145500001d402d00c550b04282081f42c5505c14405503401c01c00c0720b60325580c850b6890b4010721803d80905409001c0075a03401040fa4090381710b00303420f40d100010007441200021241d20121882c0c842c4403a00c00c0c0f18034003d20460078000c0c415072850300301d440118454043c0c0203000031064400140718494091416200034842440c00317040c0d900e504020040741c0c0241d192082d880e400340c7c8500042c40c24a1404400381c04550541c1000d04c22110710110240c14049400c208602140b450700e031010680c1c0d00504030300341c030035800c1c505a4050b208204a180e04141007800100e000c2480604244009071400212540d40c0200300341e844030003000f0301c1565204130040f5410f0251003074100082a10900610008a40100d1100031840c0c610f0a548141c0c0000d43c0801c0003104142041ea21a8100495904c240440e090401c44103031824 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 455123471 1250 455122221 455122231
    0x5192c030f0f0d02130909051506010807030b010e030d0201290105070803153a0f0201030e070b0c0606010e01020c03070b0d0b04060801051b04060e09060409150b040f14 74
    0xc000315079054504055012243e580812814a07840d4540e030302030080280104490448a038040c441040e00e0527800d8480c100c0c41030710141d6505030540c0f10142d013a40200802040c1c1030401c14018800105601c042040e0604c8400035400007071051056180c1c142c09021510b04a01c0b07206c0308000740b04407603a02c6020b44410541101d2515aa600c542400e0b82c00714804050b07440d040940c822040c40090302c4144185070011100e22911780001010b00c0b494112002042c008006600c00710b41500035501c00d5120040602101045417016a100c44218002d038001c4101c802059104004020803540d0003190600e07803080030300017040d46400144c0041d4903038000340180c44400a003c202402c92030001c2c1c10405c0c0104015004000c110f403116a814081c000c00c82c1e81441407100900c1101051203150116401c84005a8540750036841c030104000d10b0f290060409540282c030b9517220400300b4000c0c1444035183c45100c134001181c41044080c082680c0145548010151510710f4102c21142d5201d4959442 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 455124721 1250 455123471 455123497
    0x1060b2814040510030e060717060102010c0903080f04050d05010f18150c05190503090d0806131a040609140a0e03040605090409081c0506150d05192c030f 68
    0x144d6414101240141015004086030b403060030309020b402c81d0020a00c1068810750305d140c5035070f5500c0a0041e4241c2c0d51410501c400244c560404001249058026166142500741d000b40340c81c0d81da800080790380d00307008410346203a556480301d050010329500c40c0c1501c18840c4400c0d01c0c2600440c1d00d61500320003000c00d8110040b5101e0702c01c42c000502c07540460f0882318801a5040c100001000028181d40080f1106a103a02c03500410120240c012103440b40b09800003020007510110848001e000352058107124680712101900e100345030750f102d004250181c0118800081c0c1c2030a582c0c94640c03421005020754a041e45055034400d003c000110407101507031034500f4080d42e170b100700c07501140080541e054090031000303012030100146441500108101802400140050b484403820002c1020b031600101c8400c6600704040d542040f0036800040d0702c04a01c45d0000c0720441c7d0b20780d000341aa1071507009584140c2d018035525070000514140017110390303407400c0114107000014100031090300c54070702e0820803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 455125971 1250 455124721 455124739
    0xf080a0905030d0c0308010e0c160305070b160f0c020105041e0518180111030604111b0d020f0106030c060e06041a090f01080402010c02040e01060b28140405 69
    0x10040c003800c000801004040c0458103035a20102000f0125203050004900040441d00005094460350030060701a007100102d06261510b031044801030b80e1000c540c2101030210a202c200046100f007001e841c0708121055034105502e0800034000d11002411480c0300030300041902e4003001d030b64480280c07015a8203003c42c50f0500368025200215001c0e440d80326030340c040000d50f445400d584551000e2030103094803680128000000c09401801c0e41e42487c1e283d540780c4d605000060b501e1510350800341000f038070244800d1500150103000d02d006003040a200c0600c2d48500e0119032210340c1045650784000c20038008100c1c19080d5512640510090321402c801c102a40c94011416a10007048800030603480c12aa000200031001500058011145d4a84200380100d901d400a500900c0d806105907070582d60034a036601d181c1d080000505a0f0748a030340c102d65940201007107500341d6030000d1038042c4a1044030b5580d5440107084002342c0008500c98000c01502c922b2003200a2065010740302903078070890344100 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 455127221 1250 455125971 455125987
    0x15040c02031b03091002060c0708130b2d09030601090f140103050705030606090c03270d09090e0a030f0c03020c1c02041116030e12120c0115030f08 65
    0x21031801440d140045410141c2d9042c204101e00200900d14894269400c4a00da52204c80c181c0c1c941d03c1c100c4201003010410084140060342810040500e001401d01c0070b44c0701da86400e503d101e90f802503103d002c000102c410351040709a0520301e40b001a03001d4510640d02e000c4000000c030b912500e0620842c01d040341c685e0250040301041f5081600320507100100440340b580e507400c11640c1c404603885014042c2c029907021071141e00b0280482c610030744c00308213a0340c075549660410700146011054044600c04030890088101320381809810f00500c070541d1446041380c140040d941c01c4038543c116590303040e0b0046040300700180d0411041c40c2616028144500082013504060341040300600300c5c83e901000c3c1c040300e030b016408006003820309640207841c1001807100b0300c40d00719586d1107000e149004241907100c074a80000e1054003020703841500a0806201004c1504074240b40c034600410b110700140001c110b105050301d092045501d0800f03070503010303245c040c0f1f036441d034101d00460520702500341580000d0a41c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 455128471 1250 455127221 455127223
    0xa120501090f0b012d1202011806050901030e010b150a031b05030109230105060c0f0733050a1407020915012006270f011d0615040c02 59
    0x1a501d411500380015400246455003000320700340100e600300c03418000c4003400641c07080b12200d070560100750160171160400001c00c0e80c007001c40310100d04022402d1079034948040c20351011002002d903a00c0300340d29841d84000150036101c0c07010079030003d0b0b031428408055560302c001c03001c0200400c180401d030307840c0d2102d0000c0340500102040c800003142980d0400c1c1e10b03c1e070310000950499080240401030307201c0002401501d100d8800542c4030403200340c030060100d8900315005040d204c0918003240e00241b2002c00840c2400b840380d11544600d1001010f1031000c1c2d160604281200d1076810341c100c006105504041c03c103004204d211f4042114001c6a1005108084102c80d040307500240742160a141080008241c0c1807100c916500180d10700c407018101c41d504107813000d00716008001a01c2581c0d07903002541c622491200005c0c0c1c5141c030307442c00e0f183c09010a100c401c17426610f00c00049440403644800c0400c7c0c00c65064411115440711007006038400e80b84488010402d0221404070b13461094000803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 455129721 1250 455128471 455128481
    0x109081f110f1602010305010b12010b09010302070f0609050c06130b07083a061d0406090f080306031605031020040603020912070518040611070807150203060a120501 73
    0x10295940c00000c1c3c280c0d515801e10303a1081d86901c00d030380622170341c4c0c2c07119546203040c081d1f500f90000c84d0b001100140026907404014254034030041c50b00505100c00d940762074550500c0706500340e41159503800d1a0050040a00810300f14601c1035131128a03207100d00170aa100034110f0f209500c220040800d04a0401c002e4004490f80398141c03c40d004c59600c1c0b00c000c2d42c546000310000007a4042d440075012074101200740151002c0741c901c9070750200d200d400340060801c841e10061046800607901c90b4850000759991800c00d43c214040e50505480c0e01d001003c1c145800d51461508651440c003402c10015541c0c00500c41454a0b2144000b140100d111807030003410350079440180321a0300c008100440c000d030f81503000e030164040032030300e000c696580050595100c08150165680000480d0714080d9a040c2c60060290000e1081c80300040c60108810040310a420882040310720010000d0800107003c000708000c500001840011843c500300800090a1403030070748a140c203800038420640d014400d0070742c06 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 455130971 1250 455129721 455129737
    0x39031e1509050c0309070f08030405210a03080403020d090e0c070611040602030c1e070608090705090a0911101b05150a0903020f010b0f0d020f0d110109081f11 70
    0x1d01c41801d00325419002c3d0b41040318910725902c695040080c26890100381f440460305060040c1d45400d0818082c800c4890482408900484102035440d00c1c92204100714158103020b40d07601e0005e41030a01d0000c1c1071200c175502aa04100b4028824041004c08020564000d040080d01c00d60750007040c907140014003003881ca454980311000c280040c0951f000300007401184824000e881d04c14000f400c401c0014210b900b000a003640c4000020f001c000e01480003150007034141380032944299554000907091410448040c0340c0641c403a42003204101410905400d0007208a032403041c0c0b441da01e90000d107101140c1c0400004421030408000610205000911114140710981209031500300e1403000070303100b06001200103119145240942000c10f204006441d80010b0000e10b19000140070403501040d502000d82e40a980c0801c966540c0d6152400f200c0349c1445005190200c1c0f004d50005010b44440e58041c04507034010707407071030305402c010f501058218080d2010009800242c0c801e001c502e500800700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 455132221 1250 455130971 455130989
    0x40b030c040f06051305040503030601080702071806061407031715041d060708100b13050d030e030d0908030306040504031704050708010615021b030139031e15 70
    0x40d14002280b5a040f0b002903030000e036031343c08403a810b0050000845e10103c030060f100307400030310104089600c03908485c0d42205003803048503455601ca0440b0100c1d00032044180702069a41d01c010401503030448590340c0c4413100a2609401d000c61134034090025aa51041d10003103140b400d0019040b40c107400c04000c100980580104015806015900140c100b0406600118440c0d038002651700b901c504451ba108000d00b0340039441281c035080302c0b401d03a03400856a1640380342c00c040001c22651500002c002c9038034000d030b8801c200007140a086c1410044032089080802001003001c1c001410008102c9400c150207403400111a621741c24202e074514401d224164030565083e080c00140440060b412040c0c0c3c0884000b003000305d60700c1e04007002d0a0702e0260540003603000002811030031030300e1810181039402c02800115000384401d41d41408141005407801c0c0c40301c00d90b26401c14414000341c40707402c0d00c2c400d03050402015101e41400030900b483c000e200500350b9162804500c9060320319104200800401c8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 455133471 1250 455132221 455132231
    0x40b0d0902030f030c0d0804080d05090606150f0f130f0b03040c0e040c05011d03010e0109060f0903091211100503040b1e0a020a0306031a040308070804050c040b030c04 74
    0x101280500341035041030b4803a100711015030044040c04400c44d40e11202010085c9030740e8928800649080c00001d00544007c0d4042c440244000c41e0b40c00f40070b05c90400780c2c01810750351500700c00700240c0350f140700c5100180d00000d2291118803070700501116403158505854940342d03508614207a5203010182c0003240c4036158020005030781c55512019500841c81090b21002c0c007500d4030000c030901201240c016200c1c01d010f10003000300d540070300780610301244140c1803404498617901c080380c00c0d114078402850aaa554001110500400780b144443c3e203002c1050500c81d041d840d40300104204024042c00c40400345444150082041c201710020020720094880c00c601e08a4a8014103903800c100c03020340f10349007500005510303001c110310781c5601c4600004c2a001191035901d5154000e402160104060550340c15004c4081081030820006100341c408848a00c0d141a20700181000c81c0a00700109000000d424000002ca01141c0030360780000a43d000500c0301314020004e1701c0c000501d0301d507a401074640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 455134721 1250 455133471 455133487
    0xb0d0f090512031e04080904020a0309120216060216090c090801050406020409050604090f060b0d08030c04090b090714070624030b07020c030714180c0405010318020d03030b010302040b 81
    0x16501c1004c5910052241409140c61118400012100103060b5501049140d13503928241d03000d408406584e141c009078004c95a610341906083c0ccc030703403150f000da804501303200200b0700100000405030080b403024060f00019440c4102c0a00080e00652000513207035081c4180c480d01c5910764900800c100c030001c8c40942000d05098000394000c2c0250b10310f02c0d04141c0011030764103160041c1d002855015002c800306416076100c42d00100540d03100075510243c1030003540041495070014500609818200700d5459251004031403c9a0341142c10a02400c480410040c001e43c010391000301004446035550355460007440c012004121031010032203501002d124514460100034039010981b48030306000d51740c0307441e8a44240d07920f180451317079203500d0703444114107204000582004010114001d8a894100c01d031020340c0c4445280c0c116134201d00c14802140c02c2000d580d06000381040d0720708408000f00d076009150003140050002440240515444504000c01c50340f181c1d0458004021064035240c80e1800 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 455135971 1250 455134721 455134753
    0x10f02340b09030c1c030c05070503030a080f070e030307082104060c030c020118020d050c0612090c01090b042105010204090b012606131404121205010b0d0f0905 71
    0xc101029030080c0300760300080c1c404d400c08220444408201c1001c0036441940f59400701c03818292054103c4075406010b034001600d40b810409019490103548079682580b4151100850f0020000c003e041049807001c3c03000c8440c0c03404011201c00c180c1114145546080c1c850700b51030758a030484014a280c9200c03504100a001841c0d11003a80001c090b40d05002000300d0f460124240d45c580c2c0c0c0c2640100c00c21942c2c080040c03604050021010344a04240ca009850a10000c0c48940140080c020903800d20820854042e1040c000e0314903e00d000d007802080c4030f00700400d00c109030045000300b030303907202154120059800030220008181c952180083d943c9540301d00c0588080d0500001c0140415802400c54028103c810302446c4800019501003003035548580070400780540d84181c00d11825540c100486540702ea107041e46209074001c003810100300182d800020a800022140c22602514080051102c3c410100881d0320300c0ca40c85d04007240600e01d031240314000b000103400040c0203124102c0c0200e0b603001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 455137221 1250 455135971 455135977
    0xa02031c021005010531110c120301080c04090f05070609080f0c06073513170d08150a03111504150507080702060309100b010f02340b 59
    0x4510307426148512040038a48003500d0003805507640c00203003c5440b04064500b806a1034110001b4641450220403003003000044900b810141c1071205400112964071501c10007100601e01c000201041c80e41d03140c0401c00b62036002c40141c42d4803a50715070140405000c051040d0841c1290040280c511060390740001a190a02501c01d41210f030180b07129081401401280740b940490700a01820718042c05540c0300209604651644150b02c10710714001c0c1c004000f0320008107070301c0400364041070b0b40c2e4804010603041600242e101103060000c040304091302050105825000e158a4102404907072140751400b104000c11f25288d5410424046c000028416001c22a0b8100386041e03c0c41c0019091881024416110314010492408030705003200c4d803824030400041c10800d0080440e24105042c6500081565100b5102c0a440d9030002040c4108480745200301808941d09090202001c20050310294454030b10700d461805c00c1c0b6013421b024525012110071183d01002d1140c4041c1801d0715540c8144007a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 455138471 1250 455137221 455137273
    0x30c0606011d030a0807060e0709020909161b02150f0d0b0d0302061b16050c040621170c06040f0311010c1b030e0901080c040b151b0a0203 61
    0x7038805400503865050040450b074119902070041e0007914800d40380d140e035a5008290442d030042d92903d180203064000e000b94409010480c4c17015903201c20b40c0042003040356000e4060805000c600390301c11902d5800c5008a4054a000b0301504060001400042c6c0d0019074810946600300c0001840c0c90101003080060081c807102e448104100e5220310b092000d0415807072030080243e804480451811840e100500448045840d4864034180108011038491031900c0c2e022606540301001e100102d142c01d0242c400904240810650881c81030801e09014881e0441e005e07040510400720350044005950417261800780c1e02003120024101454840c2daa41d41d051019030001c1c41c60103610368122018060880c50103080d40e50903081100c01e549661a04840c10170450030701400c04440019502c40101c0309000b4030514026160391207048007840107441921210381d100f50700c0d0310b440108030394800d0266001c08002c50f4000516058880610f4a04448018060f5241c86051590400400701c002503800c1d003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 455139721 1250 455138471 455138477
    0xc180d0602030a0225030512100f0f03030f2a050a020a0b040e07051920060a0609110408070b030613050f041a04031e090b040b040501090e0411130b03030c060601 71
    0x113120000900320540310031030780200000e4081007a46900c6101080d2590882c426100c03400659540d251800e01404080d400002f41c1e100e0418100b040c140c000b43d200300107440e141084580c0356240300a114a0502c4034001c001404851880c0c40c003440001c10044580f1030b405020744c00169140c038000c8000b60030602c00ca65031203a0b40c100280d603062190094940c031140322a00c42041c6100c2210682d41c1e0555407a0205450255401f01890b007a002c0201a000d0030320603c00044082c107210114064a840c135080c0014000100007c0142c0800001c009003199444c0900302e440740c03100c0c800111102a15120602407a04140503c1219600c6000083c0500c2c0304207030410340441824a2403401c1d02046030003501040c0c40c00d9401020141d0030007800c00c6440e031840c000d1607071900c2c2c4c4d08507111504070340c2050510210100c1e041c0082d581010b5420042c00300718007844001c0c5420360b0b40c0140c0216520f105030142201400211840741c15400458111800070113494480815412540d80c80000316001400 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 455140971 1250 455139721 455139757
    0xf1603110315010e06120303100305070602030f3408091c0b06010c0302011e050603060906010f090b21150f15090402130c08010602010c02060c180d0602030a02 70
    0x140303140000c2e11070070b0216407403240d036032a030700c0d048002c2d00030f2100a2000b904407480c1003458081050a20003544074581818604500609600b8000d107800c0440d04031100755881000307250000719801c0280c40541c200302020010014100ba111001c60094036100a0384c00c0070310903c2c600304603154001e480c211201740c07103400b82d0f500111070707845401042c031401914a0b4004804140f41e0f500c10b400070000213010b0700021808611a035011410700c1c0051020160480c0c0c1c0d20700f4081c0c64542402081e03007045604008002c03650400e101404440c1c2c2c00d00c24501f81c41c0ea42e807580303101a2119112100892680b00010b0030300003c9500490b2502d004e4211244480a20000142046075521200e40148078018046c1403040e6030302c041c0440040003038000c0e41d114502d403407400f4640b05680500d852807400c50740c0b49401d951508001a0030748079940390200a6400c8a020400d41e00480400ea8054000c2030003201c00d8406c145001c201c0c1c0500740382019003190300000030442e0000c2150012b1400740c10001d01e48207 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 455142221 1250 455140971 455141003
    0xd02191203120f0b1302031005090112020406050603160f1202070c0e1608011203051309021210050d1e06150501020c03030903120c1009060b04060501020105070816020f1603 76
    0x40f0f40903100c4c1185d0000304203a100c018501c01d54043c59010404203c03022000e030702c803800503220307880c242c0c01558081200e0120804504190007210020002595841e00307508011081c00c0401e484c8030b940340b003000510340102c1d41d880c0c8035090420002261402c21136079a135850504510f4002c05000f203040312130700200459244074400c0509001c1088641d15581c603a42044254129446010015810804140022040f410100d0580b8005006500e001030340c89030100210700702500014040816150141c40410081d10742c079811120450744403081c008641844001c10f80340c41c1c0d0421010741002e24200c030360400c1c14140603885043d96026002c1b0b1340c0640136103041640c1d86c0b1440b103001e0b4254114107128452120719001901e0100c8100c02581c181710b00300741f078100807035500340c805854950700c0d61980d08080c181031150501400c0c0a1009221900e8102d80151081501501c40c5900030245108424442d02c00d21440c001d0004440c103845040e00840740384001e21070345010646171030804110a103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 455143471 1250 455142221 455142251
    0xc090f011b0521070203120d06050402130609051206070e1c0b060a090c05040905060d0203060901050a051006050313320136030315030b0f0106030b0d0219120312 71
    0x30702c604d80d0042c011b01004c5410070550b400b0390480c00b0055801c0713485001c04241303030380c69002a0243d49845410705c03400034600000242072040c9a4000340c002da07444080c50341d4106000c10129404181c50a20941c00150000400c0404804018070208042c400007480c08000b1700c001894010b65080b1180000d241c2c490300a0307801c9a1a241e144000310788104000c11554a031500f03c1a484000184900c2407001240c0100b410300004440141140e50748000b080000b0901e4450142c100b0a00d11220980500b0940301038440d220252000300004100c7c101d6004101c6a001d400075446032030760040120341654039840020f0020240110700e25428003450b80703000c81801041024400b00c50603010550b603000c0401c040f40d0702c94220160b0800d92205402c2c04110025420000114814101f4011515043d811010350003070681014040504001b100d882590b07851410100b0700b50112111000003540c10004029460290b00010b00a4503095070320040c513030000c0350f07001c8000e4450001d100c0203d0a01c095 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 455144721 1250 455143471 455143477
    0xe01030e070918020307030b250503040308040606031b080c03030316050c03210103030f0804030206060103020d0f0c050703020f0a0c061215090614090c090f011b0521 73
    0x510003a9000c14010080c404841e00800000b048000e110821480350340c021a007400362a40058400701c410000f44010203a0262010014945c848a8054140050b000c010aa4400540040c4c10401c0d428007007410301c030251388130030000c5500c840004440b041901c1c018100c043c0502c950450380c090080c1e001801d0801004032403164802440c00c0b0308007e4142800c5d203068001d81c400d420709100030b0001811070703180311034900c00c9030810800100031503245260044c91040222801f004000100c01404000381d00003913080c0d00b1407024200561182078101c0300e1001031800150481d6682d040186181645402100404205002c1d44c02c0e98811862040e007035654451805d0020040d0b20551400c22006109c1c0076a0b090342075501c40007040c0c0300409041500c0588003500700702e030050b030b4030581003080c548440303c2d240a84809480100c03145c540313411655214010907180601501c00761684103140e81c03180c100340c5446408170981c20303503003001d0f0f007015a80e55908401d9040411814407650b40e025210300e040e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 455145971 1250 455144721 455144741
    0x120c020607034b02030103030c020a15020c09130602030103080405090c0703170c160c05090a0606080105130b03060f040c0617063105040b0109020304020604060513090614010e0103 79
    0x60192411801507010b0b220b00d40340c3c0b41050015070300c1420000c20603000860003913000e07a4800b0520880ca00410070300c18555406807928094400e420611507401042c0300e540d0b640c048410035a03a942c2c1029a00442081000c024002d80c030000003c410021810050800e4400039980c0f4500d0f0381e190140f002c2c03030344600b8501a0100d0394603424040100a00c404103a40b02080180b11420704110304c0c21002031709040b8104070784905d0b01c100180920300b0b00100c0d03542e005148200c240701d001d00e0408003500e1759806001e154081c050703c0c03da80d201c2d4081c540244200c42d10140c100e41a07032400110004861071709460031109849101c00000e030441c891940044038954001c01e00700d00341c483c00e04000490343d036200d1141c0c01200d060b13180c06100c0040b182c100482c1406400200f132500d030604d0107802d500130580040420306e00c140144800340e03e882c0256001d580e0b03142070203655454441d0114101c94000d0f408513640c035051480220340035150030180b80d04000280c0304c490614119000540c10b8500d2002 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 455147221 1250 455145971 455146031
    0x31a030a050304140a0f030321050114010e0301060e09100c050703090b130801020f07030e10020705130f020406030f05060f0f0f04062c10080607050a120c02060703 72
    0x5001d401ca070713640c1107070007608018220402d040ea2521550b035122400d038001c0e00403481c800000702e100120508400301d6040604000c12103036041c4140700b90458180b07101f00d41048482d0140303c1040d20254460000f0f0942c0202050103441c0100d0b0040c0c1d50801100d42d401540d00b4140020541805501942c14090313044d00c2d0809441e0130b02080c1002c5401414440080316980400002c1303e4000b03200501d160030003100c405540d46260f0402421201c810841c5034010350942607032000180d80401c004080d1241129840d1303485620780d400f4005800000b0110301914800100080c0d15509680010a500c10b05c0c101403010356550300402c070b4825000403082d41c202071501030300300091a02c4900609002d000901c002042a02c41000c84030b1413480008011030120440071081d070340164840b502d6842032400b15842d000c1d50038850859142d00c80580300c00d051000c00316110046902031040c0b01042108510100000c0d003400d8002907440e0350a5500e200401d01c0e0040b030008020f03907a04250441120301c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 455148471 1250 455147221 455147227
    0x916081506040c03020712030227150307050729150d081309021b07080307051203100e070309110a0f0308090102010908030915130f0b0709050301060303031a030a0503 73
    0x81840054070f0b00004400c10160f082001c071307000981d00d1249800c410415900140c8034800380e00041e1f101b40300500c51600714a1a0341c00304101e071392800e10303005484285004258403510307050010741305c1b8000d50340300428504ca4030090b0110368841c1ca9503d00c2d41c000066000b410ba8580007512107000b13000b502c2c26070704201f0107140000450159002000745214401040c81e0b0242c5d1000202c0c100c1e00040390768034182c2024980758022401c100f10910140c003a00018500d41099580c4c0c0d917907074800020380c1e03410f20900800011000d500f42d00d0800010501e101d140c0c965031800010080061000700421103100b134031000c4054031820a002d0070802d8550b5451600046401c544409000b03030485101c01d4115901c3d0800b002c00210300001950150100000400c00707415044d840d444400401410b0043e90304811444102058081e84483c14050300417010020759224807004450340140da030009030301582408400810960b140d40f06040c000a90600403400d04021000c00d912645000f80142c00e80d8418 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 455149721 1250 455148471 455148481
    0xe061518040b060f0111010e0609010f0b06040e0c070c092a0f0c2d2006030a090f020303211302090106110c040f020c061806220b09160815 61
    0x24850140b44d490505007207501c94207002c00142035900d64070200020742c200c0c0d0140b121084013409000c00d540d180070310601c100881c8102144490013180310b950400c840103004210442c0b115002c907010319420010004a070b40c2c84203296400b400300e0352000c3c0c1445548582007215200c40e85000e0b6103110556461108224416004170b60000c0c40d507100340c40d1141480c92804d01403502075034007142821140d10111140d41c1c1070506101d0080c08021901c00c2d00f8001542d290380b9910340d01100c0d40420980e20004010b02c442c24050f000c0664280300a402d8480050740c071078030080300c404408039200702034a404c0003a60741c10600e60201040d540000d400c00340d00001803100c0d030701883c00e00030640c042500712486039244100240230344002e14580c1540c5640041c8030f41d0b0320700040c00015808840110710052402d401d4525994030800108dc0c03241401c03e0303c3c14142c6507520780496031881030300643c81d141c40d428800541d9031500d411614080c8011085400080e0070a004030b41c00e08841072142440d01301e561b43c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 455150971 1250 455149721 455149729
    0xe040501051513091d070b12010306091a2403070e13051903090906050102030a20010f0f050601081609120201051b010608060a110304060c030e061518040b06 69
    0x70f2940e16000068183e07011415481c1072040c82c00c01c002c0004980e0441ca00b210720281080142d8200748585c100400c64030800f01d4801c00d0340c80c110780d448440060110110304148403444271035000752080720701c2071090140603400c1030300e2a94804003104103140582c1440c02010340c0c0301d403240304101c051801440080c0c9080555244048814051819244002e807000344030480c25510600032004524880020b00072401e080c40303040050a030a000844c03800641e444081e1444110607215110303811520001e43d03941c8400c0d0002424094440d20074001d410014882c1e038054071080319424000b03608000015a0843d1070141000702e60000c3c0c4810840c035041610b1100360001456059051000070080e0740b50b0140a038098145030030001340005411410441076a042c900e010301941a07207820080180d42c440340c40341c21250025405030700014030600092095000d040301502d5403415014607820000054500d01d0015000002113030442014800030644060b0160140c80141190022200151184c10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 455152221 1250 455150971 455150977
    0x403020c01030218091b0f0c010b010801050f0405092104030510060e160c02100e0f06090a090f0b030a1a10030c030803190e0f06090601080607201506010e0405010515 73
    0x7010012802640e1b00d0f01550b5030040940000c48107000450035a02c00080c40741d039455407000d180018981d45043d000138010341800f04885d102e555288082200c94030200101482640140c0d00f00c0c5d64841900e10f1011150000c0c801034609014070780740320074488000d11640064851110400a440e1112098a540240b040301082c05000b001d03d40d41026036940c4204d101c1c0b0361815030f075080100000e8810310001d03002c0e002d0360b240a42400c0c009130a0b541d030342c1050b01d0203640001c41c00242016080c14450040d00040c000e031901401a1810b000a000c580301c400415060070060203a155180c074420005022414440500860b9560800b480001d420340e0065400007041c04d00098903840300100c10f0100c0f02f1540d4184a6a80807400c86081e814090014680c4031000c540504000d600d044c1059842e032400401d040d04101c1080c0c00200c00480580e11000d200290500b04c8145014006000104440944005020840c0116140f910345014021503040c2d07500507202d0300090f40d94180f005d4540d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 455153471 1250 455152221 455152231
    0x1c02010605061206031009021f0314132a0e06040212011e0b0f0409051003061a04050105030a0201020a020f0103200703030c020a0309060c0c17060403020c0103021809 73
    0x95200d0a0000d03966581902034441c1040c4070b10303216502e0030705208062510360600c00c2010020b090030418001741c0d0b1606209800e11078001c81e0942c40d800b038580c04030000d0400400d00c5074115110801e01140314580404c00c1c446a20580840c01c03c0c0c1240d8881038102d01c200c003045420036004d04014440480040d150907000500a0409410702c40c11819140004400f60030152a5000d038521030703803441503d1021240149400f15046140905800d0100403d10481c040c0d400c40c42c2e141c001103000745404d00030040c01940c00007800c000c1240341016440b00070001c0a13819210380c1c10080080386a140200d20486c4261381600140040000c81e0f0a1040306980486000c0c103042d0343c1c0701c410090200c010801542090403d01d519504c90281c580581210750b02e0007030303208650041c0c1c1c0104c006600034015506480e007906109904413070a03e07020400140e02e070404003040c4000381c0300400452000032407e0040d0300c01c3d0252100b1600382001101240903450384250046014034004c12541410303419030745c04c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 455154721 1250 455153471 455153473
    0xb09071e050703110a030f180f031e020d120206010b0a0f0e0a050d0311060f0405121c0c0305061f0203090f061204030503010e1605070803060d02030714040f0c021c02 73
    0x703818000031301c6082501c4d803241607000c81c51907043c41d6030403079200c42d40c0111034010b1800c01a0140c00c1509443c01011140001491081c0c1c900c100040620020f55159200d079008290060508413441c281010b803038008482400340c8200c0c0b001240510484c01602d08940e40f075580c0003070440300c000d022030340813807003d0050360030501e2a080030403140c0355039901c080402d00a0300c1c2c903144044610030071403074807030028004540141010140700010f400030ac1c1403000c0d00c21404003d5101c11000c0c01c44080c444000d44800701c0180740455aa54294240d000b1038800e80048803010f440c0e0b40f40b2070a0131040b00c00c00301070341c005800030002d0f0030041c41c0c401003640000c14043c14240c01c00001051040700703800e0507101640412000300c01000803002c00c080165202034001910104000c07501c0025007640544400246500808800074070140c450005958503190010101c900c0b02c4d43d200c2c000e02d509400000400d024600341301c0c070000c6e05003845c0103004180000381e00920303030400001c1c00c01c0e402e00c4040b0020011 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 455155971 1250 455154721 455154737
    0x10507022103280504051003140a09020f150d18020907020c0907020309060a0c08160308070f0215040b070215010f06030b01080601170a06180b09071e050703 69
    0xa410392030340c0e0035503460a0700029907668543c1c010200e4228528034004102e214000c544801880d0b12005036000c859060314518035501114909a001d40000d0f250303c80000010070070440c0340640e40c1c0045081c0b9000f03551b820001001d5030103010f03502c48190302c0f5902c40c0390308120089059005510202a498662070040348100942d030000b40c000205403003441c0107901030f1032031450300e250051b803180d08000140011403500c00c054001c28041d0258071105030920541c0302103d0140a0700c24110340e80c801917403580c104114440d207406024000304ae10700344001844003035401c0c0781d5400000c80002d600c1a00f400d9041c107507902d41c7d4030340c0d001400402e60f000314012455070a0360b80520070400341c060541da01410450300d00b84100141142c0c200b2005904100c02d02c0d00f404a00c0e6003007102c4440b46160042610810780d01c190710080170f0001a400505003102001e14401c400c0c24a03802400c1e854000c42e240440f5880f6044111040c1c5400901c0c100c182d60550300e41d0860600402c02094500c2c402c2c03c00c894 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 455157221 1250 455155971 455155999
    0xb0a15050903120909010e1b030c0c0d02010606020610031a060d02060d0903080708010303081611030a030501030c09140106050a031407050a0201050106050328150b070b010603050f040201050702 85
    0xc03d1582c464100180c082c00071492110034034100783c40c0390140031841d1641c1040c0c135041414030100900d0b20182c2050038400408220b80c0c5a0740422210f0318806001141c6d0032214040c8024020004c6114245c010302401c0d01040040e5050000d05003101d4009018511650300a1101400c902003c1c00441c0d02512014156005807120805803900c50002c4900140b0582c813420050021480200000c0810164100602c0000d8100d27407150340080c041c0202c80011a8084c0040d03680d00d8140528094a102c08a01d881101e40c0c15000340c3e0580c0d2181042041d01130351884410705032880d0045a0008981394801440f0035031003107000d0302d02500c1c1450f000c105c0ca035100a59400311102540c40000203030300080c290185d50b409028050040c07140d803506614506c0e01c0c064004220707142100c601b0300c4000c4034050f14060011500700c00055a01003030180a416a500c0004940354080c240c1140c0102140000061450017445181d20950300b00780200c40d599950340c01110301764040a170483c1d100541001550f = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 455158471 1250 455157221 455157223
    0xf0c090203091b190b1312021e030a0804180b0433050406090507021608211306030219020c01050a08060402071403130801110f0a021002030405070512010b0a15050903 73
    0x1100404140c80007590706c0c000c04650142000344e64000c0583d05d01403503031900068a0720203c50000f8010140707056481d4280c1c034000380c20055803000143c054200807502207011003072244404044c12440b907040081381080410301003034035154ad0140740380a04001f00751401e049040d03c0480441c1140002e0403080e600c91b00010216034440d0004072216540c0d0081002c015010012841c80c10b06140f584420035140580c0d4035540e08078040142400d0645000307000c900b005490583d5420034540c04201d5180c0c0d01c0d420000c009421401181d11902c000b01e01c4000c0803400454108040001a503035980b40c0007041509460200001d464150016130800020300070414096041c150380c0443d0b00034558555003c080e07941994001d0b00002c103035901d031481c00351814800c2c1c4200d80c00421442c14680e250742c102c02090341080d080708454104107000004010030030034042100402e80c2e90485010744c0c0da003004240e243c2201c80002c2890b8000380ca9880910500c01320000d10382002281d07181480c42d14034818086 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 455159721 1250 455158471 455158519
    0x306010b180109181a01110d05090d0b0a0c0e09040308070e120d03090b100b0304020d0f050607050403021807020d0c1106070f020906060a020d1b0b01030f0c090203091b 74
    0x50355049039a450890a1a400605c81041020302403030514100400900c215880b940006644003e001c80082d50414640742c0c030400c00040e41d000306c401c10583c94004c1800c0d0240002d0214000011080142401e5034038040d0b100300d024640541d00d000c81503840b0102650b403001d12402072540081840034240040d9000c0007040601030756036a000c41d44440c1c41c901917140d550051310306071085c15150020300442c402d2b08252507006804803075040c5020404d041119071340c0c14000c400303020741c090740e410411382541000042049038400d5600207079107564800032b03240e40c8205840d0040160484240700c001c0911409070606020700a2451008182c141000500c540e40005000c440b0607040b0941c0100703501d045900b2a40c08041034a100d450640d80c44c6c0000c0d03d900c0c00091100c00d00602c0310b00d21008410030789000520580c042c9000c14103586130300705416088080c1d2003c0764207418414010a4503104e0b4000d40e809180c0f50700040c028440a4027101e28101d905c81400f64210f030f0401d4507004001000030030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 455160971 1250 455159721 455159759
    0x1f0809122107030605030c060d060515071203020304031d03011103150103060f03081b0c0604030b041203061811270a060806011b1e0309050a050306010b180109 70
    0x1c1166580c255215110640140580c0906180034800c00c62a28046540c2c480c0c100c003245d000b0b95a00401c0546402808036401c01e58008504646044c4004480802032907050f00940d61680a03104c0076404074143c2c131044400a0025403140e10040c0101c29680140310b0742c0390b00a00202d01e00c2002d5144000707a41045078203200d07460307800d0075900c1c041d60584600401350a0000444090508540303500609114016109502d012800200b41c1b808506000710340320003400070840c980e81c41e07503401c14410603001510141d9981200d80d03d4000e045000703106000895500e2082c040740c0049180320203005041011020b000803c042245903014001c0202034005081410030107413080703079541c0602c01c031480305410140502002d1000e0000c603030b13000000d5048441444142900800aa00e484101c0f001c440b541201203021b801803041c03c0640046c0b58805a60040e6004a0032035503a00400d0b68441080c412943c04060412041086409089450030740903018104400031035642d0826250070720306262 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 455162221 1250 455160971 455160997
    0x70f0807050a0203012a0305090d05030402060409051e06030a0f02010e180c0d061e140103020904141b040b12040f150c030c030c0f0804061d0a020f1f080912 69
    0x40c8900034200c00421b03c889a00c640307402c00c10392400b44201d5556100b0903051500340400400020308556811782102c01810400703809104034103141208021900d4080d040d000e1102e4584002009428000b60600c1c4041c0c0100341400740e08000e400646144421489580d000f0f01980c2e416860310f18500d200c40d01415040c9212955450075108110403142d0b0b5801c1212030100310020010078206245d1a002130311224140c6034198009040140d0007881081141a0031500f800a48030340140407020051140030580604140c1c0c4218038603090191042d4014600e1866050001e050042c0203030445a83c040e200b80381848440040e0788908039101c10178529042150746440420941580c140203c1498a0382c80c01c0c2071040d59408807000d0701707158000c11000c040202003400074003480525080039040c4861882d01040c0d01c4244c00700c103501d83c2505a001c3e8015411000d003030b00141404451341142072014200034001380b0b5040004c9504201c050b16207180c61003000e041f60401c210742c400901b40c01a140b8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 455163471 1250 455162221 455162261
    0x1b03050c0d0e1c03090201081b0418020a11030307020d1b020a080303090c09100e040510050a0605042405060a0203270f2e030e100509070902070f0807050a020301 71
    0x20155000034075481e2120f000b054104048400181d8121090325000032006181d41c010043c015680c40f05805598880e004100d00007135015924940d5500600082419aa0381c50004030702a42242d542e00c1b00340c6400300180d0046502569003485101c0c1d01d40c0c0850b0b0b10306003802004031500000d89582403078001c3c0c000c0f50400802e01c40654070400c00428240c10664860b181840c06884814810110307100714900e641c03103800001c00b001814001c10014050026042223142130041c4604014101409007901a9182640005400b80107070a2070319140f80807242c001c0c20b40c0c00d15051000036000405010194402801801c0c80e180a0445400100c0120680c904280350b5560802507030318000c1c21241e0242c50a5100203031800201840b03501417001182c0707010300d1411507802c01c400a014154440c0c80f0b034000d1480800e0428441c3e0400307401480648111603a1607228403801c4103e201c0c80d20b000f0010300f8890b60003000610800d01500865000d4401d0b01d882e404590082800e6a100488000c1020002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 455164721 1250 455163471 455163493
    0x20702150909090f07060f170106020607090f0e010504110f043f030e211006150c030f09030f05011e11071e05070b03010f091b03050c0d0e 61
    0x307042e0060b4000d0032500100740b80e00304208040d80b141080c1c0a60030401004038102c440c09401581c010254038000b44140c0c159695440009454200687d040800600d2040c0001008481c1007812000d6401d50804107016919102c200002048140d40e11604c03060f0601090001e01e40010291004003547c18210390108040c14407110b024801080790307a494035501041c02e160524001c074440310b207585800c1445110403034100140d0101c603480c0c01d486482e08070240129070101d011a00d00b000291042d13050001039103811811000030600007440001071103040121002c0392242c1046ea40c1c02140703046c6000c02e991240c0740c820903001c0381c0005072043c0e0f44503441d1345203020540ca0000c525070380b400303c100503001703000303e1040c514802c00c0700140140020380a002c1000b110003070700f0b904d05a48042101d89a5584400504481e002480303505214154404005005a424010340d412460703007214440c40483c88031016401440d015143c2240c0f104140118100416180300b00070940c4200c200410031100c41d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 455165971 1250 455164721 455164729
    0x30a060602010b1509040e0102040b0412021219030815060316021501050d0b0a1107050d0908160e25020a1b030b010b0c0f01090b0f280f0207021509 65
    0x40e501d0950103540b0603180c104e48140c0450030748036000b004a80c003054901e02c1c8040180a070050713030010161544009070000e004015400400502071003500c01948800d0a641490344070201940b007030203c020000d5035440028880c40b0040c4c2d100d61a0700e4900c2c00d902c011000314407190411182d26000c18000004a034201d0b404011034668080d400140354007640c100320104034000840d800080200c01948046403503041150481c04e0b54800c900c01d1941c50701c640c3d06040d03a442d001070141c0d2010503c5200c020949c9800483c0c1c8261801581380c0300d101d11032511617141035184004003005144100885a6280002d5804920048417550741c000e0001c151076050196a00000b001d86842c03100c10044104000754410140e5411900605406511141d050210758200b0800351600c40c1d0070351a04440504022003d810640034003141c882040144d52080e9140541c001c03921409401d20001180c0c40209220341c0c2c1003046844d607844800760401c6640e60118102c10415882c0315031203c00400c07a01902e0130 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 455167221 1250 455165971 455165981
    0x307020634050f0606030c010c0c0909030507022d010c030e030a060c030c050301080a060b180f070e040c09150509030f030904110403120507080702090a20121303020a0503030a06060201 81
    0x403c80f000b8280604028000944c3c44e4001c50041d41803000c000e4415090080d1218508000c240341c4c401404015664540186182c1c0000400c82c85808901c210720004540702c81c940c5030401881001c1c06401f144980151254200000c00720308004020002803907684042c401500164810700d004648d0000004010302620780d03581a5804000e0144010026070b840001c0211020b030700200300041d4050307003001040e400c00300008080c204044840601c00c01c40424030b4558840c1c64a607461202d0b980c2000d0400040e40e0703034a10707020300041c1e410800f48407180c1440710038030040896050092070059007001103820f100500c06810865080801c3c4e0751501d0178036000349a1000c020011403490b103070542d1340d5802058240039003c0c003000780c0850f0040411130303501c0444900640003004080c042c40d0075412007003d0001426030700240100103020700c40d600440d0081d11a19100c19000da071460342d804c401c0c42e2042500c1d00741581107114600c2980e001c00d400f84021809000d030b03588003042c02030903c1c0d00642590 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 455168471 1250 455167221 455167243
    0x30f1602121b010305150f151902070609050a052107080f01022104050d03020a200303060a0b040b0403080d0f0c0801081c1d011403151908030702063405 67
    0x51b21228051964501c4652240a0340899005901c2c03030b01110405850f02862131140094209203402586040d00021018100e9051b5541c41e0405c6840f2802d00980700d02c54800d490700201e114410182002c0602d64141903444584100c0d89602e555400903481d000942034000001e1b5400545103d040b03c40c03240b408203510b459032000109041c03958506681d400003100320010164089246034580d807003181c40070b241d42d601d0765228806210304126940c807a80261a640d00c900b09156002911252803000d4034215511801c12038142851511005641d034808080b0b484195070390011139200e9042c2e44a81105a0f105541b4140c4560400111920302203a05018a03280801d4038a1426007543c825810010300102e8a90302020218413801603038082910880e64a9081002c41000028554401411010b4504485590441f200d17422011070320311550144a680c2d41040004401609001008214443c051001c110001d103d80043e240490001c01c0e2082c0d103200908403400c28041e040290010b12 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 455169721 1250 455168471 455168491
    0x902090c0a0503070f18090c0215150f01030b1305180f210912030307020c060711040506011403010909030e0603070c1b09060b04030c08030f1602121b010305 69
    0xc500d448050150f01008100004020380700051540c1c0030f1241c80900c206801d250031942d4000e4030350940340c001d8004103c0d04c000611a6655034000d00c050b07030240ea402405041100804106101d09100040c0c10058085050688076095064603031248036140000c154900c0c000034503401c21a800c03ca80c02c940e5006100c2c1544000020440c020000c039084040c0b0a041503400c10b048001c805032000380c0100c40404e940f2107503107048840c039514044011889841d8035800d0b0303407098441500f001032a000e00d1401070403000b210b024144003420aa407086e83c21074030504203240c0302d001d645c407550b544e5072090f00489145921207140344209074104031034a600740c1d0101d5425003035203081100100300455a03c0060a44920a0b070f42a2007070748444100700290111080a01c00701d526a071103110198003600c801c64800c113100000180d8100080b06640242c1606a1032910707000c0802140c0a40d83c8000c1c1050ba845840701c062202d1640c420864502c8260503041e0880c11910448000340460780c000f4251410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 455170971 1250 455169721 455169727
    0x30609050f0d0801051c0609050c150406090e091c050408010c0309081207110a0c0f05010201090506011a1c0f0e0606030a140c180f09070506030112030e040f0902090c 73
    0x10703c2d0808072040c107560040d01c0000c1440902d1024010f8800301020181c05607207080c44080c140f1801098240b405802591001002c03200b004c42a14148120b100b510002158540184103801c4035098280d040040c003070840e03950308a40700c3c0200d95181103203403030b1001c40e0000030b017040070007401c0c00b909009826904003042280d0140c5c8034000103108108100d140c0303c40300000036041c28001d140c00b00f61000460210b5600503c0c1d071401c0ca4903461903000324038a110100b20b0014556105000724a407007584440549a164a802c5a0f00030740c00507012420004078090003440c20120b04009044d5503142c04034800b20b10a00250420003c4a116214418081d0000c1d810407202c0d0320f0024082d401c503075001070120020b00d03080d0400390600001840c1640e001c90f01c0740c2078107508143c0102290150840400a429546034142c0b403507581d10480c42011307000740042c4010032440c01c10128501605000381800d141c46038414000500f1070f00102e00380301b826961181a2002c4d81890000b50f0307841881d100d0082e20b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 455172221 1250 455170971 455170993
    0x801020301032d1b08060609130b100909080301090b0103060609060e060c0102180316080d0e01020a15050a11040f03140a060e0d0813020f2107030609050f 68
    0x402422056070700c044070900210032110780f070300c8500ca54440a421001d5945450002c400149a25000d0710580000e4460310340419035501c1c103a0449030007600d5080000010070b140d039407060103d00f4024a55240821602000214954140039811900344601d00c10341d580e60600b070039041195544120141014602502400741940180303000d02070303503043c0c28280c40c11880c1000082c0e0521803004a40c0040d40003082128202d04144964211038000300c0544007012040c0000f440402c0d0588622825580100ea4014599002d05c1f10203500c400180705a51400d45076495506070303440011110801c80b0f80d91000c00a00b4085441690b010030080c0700728a150070302c3c005256a0201c0c0500019080f4007480c0c00f8403130007180401c042c001c500d034403041c02d00441c9003100b2416102c80e0b80e80040b2010540280003c0c2105019040c14941c91341e008181e0750b405000b038014809102000040003400c0c2800842006440030100718400040d032007580013003210641450541d0400e8040640805103a1003100816 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 455173471 1250 455172221 455172233
    0xf12010501200a060e0f031c06061e080a18030c030909020f2203020307060c0201080a020f0d0e16030807050d2c06070b0106030f2f070f050d0513080102030103 70
    0x50468100c0b0000c10b100c1c45d2100030a00b08605007148146a20000600303070540c992859400c508504441401c000365580d4020580703440250705650890741c1c00e80c160b41003000b40110603140e00725100e24000241d01c12034546840421601e07100580c0444d04000e01141010f500c22034000c040d04101d4015410a9000d0100035114081e6081c840580003100b254440da105825094000868000f0b00311030b4075a9031920040d00ca007a80c20011790004500c003001804036030060080710a2a070a0750940c40c50203e04040a80013041d6283c0800068024520314800c83c10400580c00d000d9801041e10301e54900131484c05500d800349404004040c442400c03110700c00084e00e101c40010041240750410591780e44100025054420b200004000c00040c0c070000c2141c50381030b0b10180c40c860788840c0400c00e909101400034949941c0d241d01d1407d030780000451140040d06040504401c510407200c0f03000d01e049030368402d802c0500103000703c800148085024038140d61801030600040020000851455055480e20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 455174721 1250 455173471 455173483
    0x91a0a0918030804020d0b01061e090b030a180219090e0f0607080901150e0a15050915060909040b1f1206020703021c110c010201050f04060b01050f1201050120 70
    0x601400f042c0740004003591241e0f03890381107440d03201c0202c1242c0d40e1101c1c00070b0081d541d6107468030511540101c0b10030843c0d010304e81e09015207600d9480c560440d5104910318003e0041c0b030040e0310316030441da6400b80040c1c0b1a24040d400c00e800b80c2c01c180c1303805420840004210340484a07801c4a40c5c0c0013401940c1501030100d40b8a4011a06181000d10341e90b503881c520b405486014550808010207101c0001c4607201d00006501980000c0002e1080c44545900b0650000c41802010703800386518005c587c242480c04625030740040c001c1c103450300f8018200c0000e4030401c4110340c1a15404a09410003040f62134002184082103221a400501c02e0f0501c0c0800007008500070000303064a0340001c21005050003040703024807a2503030442c42c246003c50410004d0084480000c895040e10807104004015030041c01994481c0b00840c6458003039a850703865000c0074200d0800101e043c070904003c910302154685004001c1c01c1d003040e400e0240c44d4504400140081410f000104c02090400001c4d42019004188 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 455175971 1250 455174721 455174723
    0x9010e0604091b030f02100804120503090c1201050406050f0103050309040b0a090e0f010c0e030c060d1509020310210b06150408062505040306090507091a0a0918 71
    0x161400c22407421090840e0f0050312102c101c861007600004010303541265002c114420784005890401c213a105850801040e90014600f19007803094030202d0344220090340d40040d801c400c44100c1c03055140410040104828000c40a944070010402405824082d06400c424141841155980f554803116101d0140e10200c2e071166445841080031561041022000b41c880070004102034070545480b282d81d5003a00d043c0100c5542403040d001401070140003900244c85014010b0410402d00e1703000c00a090b03102302c4c44009003a07680d00c41500314885400300c0c00f000d0300c01004016540d003011140c0131850a490740c071500242c0300c1c41500b003040b00c0d00321000c814030603070091a088060321102c0c001000c0018020301e408540101141c001441240000c5580c0108500d40c402d48107041c914a6418001000c100e0010100d4410041080040d130030b50301030455140140300382e82c5003e80b83e0407801c090b2800d0752500718440103232881c0d40a852401d21f2031200100589001000104900781002c10800c002d620 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 455177221 1250 455175971 455175979
    0x1b0a0b0c03040e06121911090702010f05060102011815020408070f17032b0b060a02160e0601020604030c08160606061d0a0b28050406021608120901030b032a09010e06 73
    0x211b480304101c0125800c02003c1c0000781044c48514081200034004c04030030494105660405000c624194010700c1070040e000d1990a204442c200031740c07191005910900713850054160300b000005000c1000f8003c0001030f107081d040d05140540b9050169203070024001d81c0c513440390800c10203401c405019010182c5075089000f446807040d0044250356000f000b82e00b2440703800850004550104680c0840d000e400340c0900901c1e007a11a0729001c134102c0a08040b18400d015030b10403400320f0042802000140c2c0340714400e41c90107280c40c1031011007031000f51500c03100f01d800c01e0319140c041c802250041074080c01c06a0114081e08001055400102c0506007445049a45540001c905044441c40910301c0003c1c00021101d50868004a100a10541c01485140f00601885450300009640d01001208840e10305004129001002d68001c8440d88243c0c0b900303043c540c4e120380c0d1003903544090003400400240161031010f40214444a10b1004800664152044803444014841e02c51f1f8205d21075080320f404d413 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 455178471 1250 455177221 455177263
    0x224030105120a020415050103060e04110603221101030e06060d200603040c03050f030f0f1b0a0b04061a0102030f1602060301030c031505091b0a0b0c03040e0612 71
    0x840aa4104952883c0c080d400a0070250000044000401e200c0201c6030280e0741042040c1d40c4000500c0b0300c20301a81c00a1408901c411000e0030b07403906101541c3c008404422904c03400e20401c404880f40c50000600700c80510728000300c40ad441d0b03090b1240008607a01d06010b000386141c01d03400074030f4401100c240208410a5410106643c000800d40c8002c403500c058007003036883c101130074042d040d801d40384001c51b03442c4682943e1061070480030043c3c40701070359140c14050812000010301c1e0741c50341100c0402e0f00c01c50000d608002a40b10200f00a02c50640a05c1d6048410300302428150242d94044030050f01c528001b004403950303039034000210b4914801580e507413a20f524140302020100c800030707880694407005c048004020700681c4200700c81124030131041800040804906401625003c5443e0105504060107001104440350412031807040024041c1c0744181e11346400c5045c0c0c0e081a022132009620100381800380c03551650f11035401890480c3c4009003000c1c180380c0903583c1c202e001442c0c45035010750 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 455179721 1250 455178471 455178499
    0x60601110f01020a050403110604062a15090210140906030c0d05010f0e0717010905091005090c03070f08030f0a030e123c0a0c050601030c030224030105 67
    0x38070444034100284002503590f0041d50f4401806034100b4042940d400350f841d03042020501d0700c0d4040f501100c1c0c5c1511600c40e283d40020280d01c581007840d10700d40c015a41008407800050403030081c0510141f98004c0040e0068140c01030202884041c5540000e11280704209103012940c001580e041d00030841e6440d54075500c0d0342c2c407195140104440402554140300c00400c240440c14620015541d000809087c680d94032501120710030320300004506c580106000620402c1c909030020341e406244001225a51030f40302009130104d440480300d2420681002042020515003804030200800e403805501d03410504005c0c4140d1640f0034540c450b803094400080b96640907009412441c020b41000c070a6600404c540c0c400d002040d40044440c0100c40c1d104048040e42c14071100c149100c00d000000351006082a5030340596440c0c1c00410400c1c1448ad4010900c000240c040100f40e02030f500c28400900842c0ca5441032025071081d85074910300e0543c615000030120b10002054a044a5040f102c0725180401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 455180971 1250 455179721 455179723
    0x11040b0109080d051b01060e04020d050c090705090406090504380c040f05040516260a0b010813080a20030d05071209020319020a0f060201050a11040806060111 70
    0x703a07000342881e00500500862842d080005400403079003888141d1001c0315440481400c0b11020b028111121001c20081001b40c20800c1164003410300c581c0840310740100600010b00c809200b1280b850020360009010303001420907004407801001d80d80400e1101c1d0909644032101d001140700d280c034400c42e98824006d0206000c01000280102032040b989130b80c2440a00e01c4855403103405054582d030f101400c00142d50514ac801c2610070340030585000c401440340c29003103800c00c0c0e041c009050b400c6080140b105484c14a0034480c0e00442200000240703a0010f44000f40c800000100300080101c0c58840701c0b804202d114003249c6061034070b4689400d58141c0100c80200b034090303041491140e0b100c00300e602c041c508011f5002038095007490f250071024405030f200b8201910307000e4600940507004040c106540c40c26020151500e00d2008108440700c83e102c010384c40000580e0760180005070b4480e0207224110f0594072800509161102425141c1420031302c07100d580c0e40000d8040d504000b91405031120b440301c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 455182221 1250 455180971 455180987
    0x2060a02030a1506030b0906090606120c040504020a0e030610030b010308070c0b0f030f15060d0f020d090503040609090203011409070212210a0e060f0405010b131d0a11040b01 77
    0x14050b100e45a51311840000d00030030066060b10300580003400420014601940c01c10301c6003000400075454500d05072000c4035001e030064030907214030400f400b01003000d44d241c0c00541503d400a0b500d8203030480004081528114002e40080030107003040300b0901c041480b8641650559070050f241660341d0440f4038045488441d2940460080c0c90007051003140c082c00c620045004003002005070b007107a1241c420b03800291089842c000e03030200d010002c080c1c1c00580d940202d000c10a9241c00141000c01d102446000c0d11607000d0101c485410001c0c007071210b5500105458007815403000d00b1400d540c1081d0341103100c4c0c0c00301040d09105842c12000528014801c001800c0e040c1c1325000005d40720380110382e0314181900c40c0d0200604c110702403000101da030010391051061405181c80185a551201d04552450010242c0142c90355502d8403240b61003a02e80710701490b45915850070008400c22108895000c00c0d8502100c0c1c04d081e0049a803400c08202520b910a6005c3e40441d0009020002c03180113030340c107070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 455183471 1250 455182221 455182241
    0xa0e060123090d0b0105030606100e04090f0206040905010e090316020d0203030d1103070f03020c070e1e04080a0305330d0c0f08010509070f140a0801021314030a020102060a02030a 79
    0x880f0140040803c071141043c03034101c5000382e044a480d40c484600f00022804903258880029080d503003504403a00e000d8000e00c02c428000c0d0000c9131140b40680114140340d0294101c86100c5072294010000043d400035440c0d440003450020310b042081070b001d440c03400f22040340080d20517601110303240c0c15941d040c8100d45219444200403c6844103001020801d6041102d030f00002c100d640e89103650304c9004e4001c0380c0d0006904030141c41d406007440d10016003050040d1808500c0725540b020400e1001206210a00840c0200c00301516001800002001d80c0c000074100c81c14002045078501081da407400d01e13041c44007004001605405400c6001c00c170304981424000e880e100b016071000811401885540381035550729402409a6921500515580d2103a403203075000342c006041c02044040c1411a0221070284010000c0d80c804e48e070780c1007450a80c0c0010b4000c5c2c0000f4841c00e41000340c2e080021010b0780180c030a41c083d0061480a4001035110311005002d0710700550000009005046180d000720317160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 455184721 1250 455183471 455183479
    0x301051306050702120714030c0d05070c12031725050304060506091014010c21080604060810050606070206072904110d02030f1b0a0e06012309 63
    0x52425104110001180a80036501e251815000c03c140901c041400135441c1580c16074245071141b19940c1e0f4000720f8105041d903c0c0d0707000c00d100301c0d4002882841152181c100715610103859a100c1d04082100c06002c0e4031200118940300e43c00310000c0d03001a2014162001404c0d107068569072146810042d80e048421130214003042c40001002c00e400c1406540500d000789000c0010303545a00c01c0c0b00142805650066076400a048100442040d074071503140c0c200d0341850005030280b0b1690315002944003d0300260303c1c0390340100c0c0320705006034040b140c280e1245c0c00300d409000c0186405c002d40d4031356100e41c0200d0075580d120800603806464584c01c441c6c980fa409084c0f0380d514072650800074001e101031301c2007405299100b155031400c51820034100e4042c80d0010a0740f1504602034080005a000c0c403c0700b00d8050060881c0c4840086050100d4030b8180001c295034004146490f041004500454020501150240e002e00c526a64004450213900000f980c0a800c030a440444000071802000c040c1540 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 455185971 1250 455184721 455184731
    0x1e1b03040b0a020c03010911060703121119030507050a030b010e090114010801080a03020c090717040503090312180918011a010f030902010e090c070b010308030f010515070602030a0b0301 82
    0x1c8100001410307038908076425030792200b664008040c280d030708400003d0007040c000b0003681c1691900070001d04604c0d109082640c1d485070071190710b40584110360202c005452000c01d881a0215441e01041d48001483c641001a031410042c041d0950045011110400d40c1d1800c0c900404e9005100039030031410300601d60700d52581d466070202501484490f003240003903010700000030380c1c1030005240f541455240e005000c08c00c004000307008083d0b800600701e004101e0100d003089499190869090300681c05080555032320722071401071502d450200e00e00c1c81181c5000b00700d00c045000d9481506049004115aa4180768981e0003500d1607241040031030b02541c0d460800c02084030300380c84503100c00031702081e01c80d09281e5403259810743c200c0e00d901601034003040020280e00c485107840d10302d0303a40c42403282d00f07060f040c5a0382d40c4900c00c2c012803d0300110307413a82c03000040c041c6160801c401e860040100701c419000c80031200b000b03042c0038040d0002c000d2200f0b40200100e060a040d941005110060150003000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 455187221 1250 455185971 455185979
    0x618050604150e07060504030b07031b020106050a1e030204020703140d06031a070f0e01022503020a080109050a060e07090908190912020105070602130f03050705061e1b0304 76
    0x348030b010001884420301e0003c52044002011801c1c204603004c686409080c1880d6841c0d0702c40041d00281000c00f0180e985640c156410350b48884201031004550000402609181c14485100f0083d0000b1082d41d0241094040045500c0034070410359905403000b5803946081d01e010307120f00881c00f03402850044049441e00c00c2c2c400a91011007268028092400740c001c44000020002009071129800140030a03410001c1034040c040d51814401c040c030450708860140c42c48610f480711401d90500a03040308100c208250720300020703000b014210000080044410b140c1c0c0300d42c2e807200e00c05001411680c03078200918014070140002c000801040e4004c0c04156140d20b00503605030f10072000411080d04082030511071a10a50b142030541d1040c0240400510954006548035040080100c079156000c0280072501111000900020241c189207864a2410740c608507092280940045000c1d45080c0b110380e1645210160f149041b0000b40c18166458200310f03000c0f05079a0071000111918800060002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 455188471 1250 455187221 455187233
    0xf11092b0b090307030e0117070f0e0303030a1d01020c03070f06090c0b04030b0a06032303040902120601120e0303040b09010209090108160603110708030c25021503130618050604 78
    0x246403190303035070002c1c6e405c4100055402d001c202c00d0b0320300340681c180001403d240c00307011900ca03c050300b8200801c1321440d0100003443c5500458a80b1101030311090500c01e44071409860043c8030080600135410441410203103a501d00607920003a1142629466010070701601d0f91241d8400c1e50041e03003150250340c960111383c000381e202d1311003210050020400640440090721070344003900d80c403a00440405840100e00c0ea1401c524066006180c0020080081c100140e40300070100b818488880d40601e1400c1780024103002c50f44803400700c0440c180010603800410103c00c481d84160b00072405001910b65290160082c09051a200c1e00090b43c1d00c00400d21341400102212448031200c0c404c146c040e12803000310305580d5817003001c014000c81445448001a60000910351120420121a06000712500c40d48c032800345890f09051b4400700000d914056090032008040580c2c9004c00f031514500300115092800380c000800039209a58400046054640c07880c0c11a901c41d030030100b01c90003810242448 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 455189721 1250 455188471 455188477
    0x2e14041224020909040308190608010606180308120c0702040f05061c08030c09030a0c0e09010f0627150611150106020a060b0f09010303030f11092b0b0903 68
    0xc0401e60880c11440303032107420107008441070400d01034404a0540c880d95026034040304080c0000300740d41039105403205442481c1c403841000301108000801e2071841c01401a01d00d403000c040500031101d0501042c00403404a40c110b405609416803c844c0c15658103000d80c5240c010fa0760029401800c002c0601000c103010b80000d800792800b210800004195080c40b40e0328540d420200400e0740f141030000410402011014249041000d42a04c2c4034181030399904504041d070381c12240851198100b805800c000074030034903403804000c1804020783c030300348a1009002040c03210700400a0409174074801c2c0c080c1030394018101c6100107007030504489850751005001c814400500f00100c1c42800303d000710450011040904031041600035013a95041511003001500b01002d0541d040300c0d40820400107070701c0b03102100e40210f0280c2da0004840c0c528080f60b50603070704030000d0501648014460145242d8030300740c0c0051040500350171500140140d44101528020303014014080f06007440402614200200003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 455190971 1250 455189721 455189753
    0x8060d0b1e01081e031c020d0605030a030504030b0f0103020d0b1906061d03030703140f070f0b06091509160e030a030e01082811070501090c052e140412 67
    0x480035484e8001850340c0c9000c0c0d2608200e229081412000e645500c0798010030010003105c0c000b00c3d4803502c481c00300340f8284407601c0c210b00040c0006010014044540907542c3c2280c03100820102c0b55145270000340c150729103c18042e01a4190304c0114403060300d002464142c0c006c800805005d19956110041d00c0b4010038400c04078000000b00035003803a40707030100880f010305a040d01c4070180462112804107880e0021240c02c031b034003003003041280045000c50380410340040c8502030000c018600501070080196024101c0c00684413940020381541c1e07200e0f030600741c0c4005c41007200b80c125200b20200303c41c1c842c641c4071a5034040c02101c2405083c19400254107520503000e803601502030304c81440b0403562807180310450000034102c40340d40c0080581ca800c2110703c4181a01c0c00c0d42400700d6501e44a0864802c124200c50310b07a042201007049081010044185920b4440400012013005002890303440702589004204001149510101d001d08019100a443e000442900d44030f258600380c040d0303201840c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 455192221 1250 455190971 455191003
    0x606061b0703110a0b072102030d0203010b0a0e09040314030a0204170a02040e06090316080723060a02181002070e04121202031e0405011d100b0108060d0b1e0108 71
    0x240881c00c00e00030001c5410156101c0200030201c5550f03403402080740b41130107c200460000304001d170035046031400030b1806080c0f42030041ea40c502c00701102038104a02d140f0b01e1401504c981c070801020907007000407440081e030400386081e0baa980e598941c100a10698002516043c144a605028140002440704409100390780030403110014100c1540c1d1014111440160790388100300403451464945001041c4610403d262814101a507980d103900031322605070045681c041994600488a00300441c6400694228007149401c45488580340b0b01e120a625183c0620751680009c242d8520030004c40f80101006100150300d410700740340c4510304801100354400001c0b1345441444940000c0e00c2128024518060031502110705d4024911310598020000e44885d581c41950401c10030041140356146107110020b00340e1803a00004000444000c40311145c1001f400208115030b58480038081c4bd086074100400881695800d00741c1c1d16800001d10b119440720b4503403000000c04540020780d403030540718041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 455193471 1250 455192221 455192239
    0x118030515090a0b040f15020f0a031508030409020f070501050702060f2409040501060b0a090e0f10210203120c0105070e0306180f0f0d0f03020c0606061b070311 71
    0x201c0c007241e94464008000c0d107400191000b26002404051103000031b94415804103040e80c0700b00c01c0c00400c0360000c54000a4000000030407a061540c18415402c80b580d000000001d01401c00601d15564007540c050798003403590001d00700240848010540f565154000000c0c0050300d01414001c2d00c036042501c8a691078208100070414211200c106144482c010840080d0910800b2041180c403090286c01914595a00c3c50040380245004004000046454480c0089a450440e0f00c0540580007010441c402d60754400780300744164400942070840c4c2e1030b51011010300490002074602c00080d401c00030360500c659081c4039030103c40c090203000b102c0da01400030089130751201e60031780304518402c12299160f040721300020540040c203062000d4072300c60581220924401c0041a40c0386c900d203000d6110440d8404240001840d61010a041c0c4800e80c9150540c00e040c600207690343c0d036807006071207039200d290702113101c070301d0003c2030212510403260b8001120380c02c540d0b034240f01904102c40700b16140129a15 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 455194721 1250 455193471 455193481
    0x20a02030111040e0a0b100807171f090519111303060609060905060f0909010b0a0308030907120f0b06010507021c03030501090c0c06090201140f0c070504090b04110118030515 77
    0x51180c8011b41d136006e00202d0695400ba20220303002c05004000c0c60501c10308880302d180d0004a00380d102d2040c0c88203c2c554881c6c1164800825105004ea482400406e040c00104800510890f1044100c001e07000710100d48031120b181c41d0565070240040460032139204a9000050040d03940000e000c40d420180100060303611120000b050340d00450b15a60003c01c1160300040d41c0c01e20b4522254000d1025000152803424030000800d01c0700701d54400d50b4001004401d11940190510120b40185403010809980482c243d403140b641640014000e0070f400c02080000300f01d64007803012144440e0b2300030114100142c61242a0440000065041d40000d250500105811b10148074000c6c0108040e107411600b00034683d11200079020350724040b4100710a055160000c011644042c00d1045460036010340c46002c6844600d2501400384d00c140d01c11405d24100c60040340c9840050b0303410a0300035036404501400e41c00182c4041c403101d003d80c0381c040c4440c40300009101022034001d844080c650400c0a5546039 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 455195971 1250 455194721 455194741
    0x60406051c0b0406060b0708210108060c070602090406061805011d040e010204030b0f16020a0804030809120708161707151101050421110303010b0a020a02030111040e 73
    0x11207540c0e078a80181e40d0842004900b4032a403442c0c1c814414034000c100c0c1501d070304c0e80c0050b80c0c10a20088400c0b503000301d003400c1e10304190001010380006101e100000c940c50107102581e14103025220b01d001c140c0005002c0140700094048581500002d0002d20959540b5913004090480e29a541416881e030004041095841540d40081107000f96612098031120403040000034820441c01207225942003000200013092005405e1050b0300400b0403042c0b41c64052040c0c000e054604149208540002d102c0d040014902e2045d14107aa8004110544800d0f510020a460071040c00c400c0c0160300c5158000240c0c404000b88070025222200c040d416810b03928404103211f241000c5804583e074100400c00d02c00c816040940307100542c018a48400c3c101d81846d0018210780040d038003510207140407554080703803154032144051003280301c0c40c1400c8908014003107a0b843c0d00040c002c0481079800040d58400851081000d030340b40d00e8009001700003000d0380161541c80c40d406445556000101c0800180305050 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 455197221 1250 455195971 455195989
    0x20c0a0b0a0507090b0a030c09030b0a0b15071e0519121808030a0305090a081306080105030c0102070510020a06050109200a05030609101502060105090c04030c03020909011b030506040605 82
    0x445c4840a00b42080e0301c2c820382c09003041d01541d008202c150480040404c070214001c901038415040300003100c894020034803690610300001c0c0854844200649000200c2032449030000340703025036003000514054074005080c001000000410b901d039285064050146004003003164a41030b0710b074900c000303400c0c01c00c01400c030000b0700c240c0d40c45400034012803101c03901a8201c960300998a000340e0300003100340d580d41d000c10740046031150414900c100003440002c1d0080e2881c0e000d80422401030203148a4800000d5071103603d070003030500482103101450880380c02080104201d6902210511036981c4803844c031001420000d0000c90f10f0700784070300700c0d002680004040301c0000138a940e526141d0b60710007043c421f82c042c025048544100d542140050845011030300006881483d601602442d4940010041060400f801310160b4640c00c01c020000101c210b29004205c0e941558103500542d281380304c0d1401010910740300c14001c0700380035903a14000d60580c0514402d91040b40e0810a8580780d1042c050110 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 455198471 1250 455197221 455197229
    0x6050603040f210306092d0b06090d1a0c03040305430203011406060711040b0402030103140f1b0f0d06060602070609080111070206030a020c0a0b0a050709 68
    0x40800120303021a01200c5280c403018055403400100083c2c9003008212981d6072000b64002980c0d44000307104202c0b41e400340d0f2080c0581d0950742d00c0b41c1059070010f9690422184504114150384415400b413680b5890191510118014030303107552150181802841c0060100c8000440e034000400242072980c05415a801140c05079a080d0134840340c0e0940340c040c211340890104d440c103554014210300d9039124004000c50804120001c449041c98818903003034405079440011603107000001c000b029122a0240c403200798101208042103180200030500410820002d15080b900000000c01071090090245c03049004240407650010a40380c0d410f81c0f12244a02041e0144072420280785992900060b00360340300500402800040b8000e507200011181e047e07000c0300160308815401c005407504401c00c04000c0c44684020700030013070005900002d51142c410f000348684008000f09861191a9041d40d000410440848925070180e007481d5482801c11217a02408600707040000d072419200d0700c1d19100315 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 455199721 1250 455198471 455198479
    0x20a120f090503090120120c011802060d0b010e09090105041a0906060135090706092405120c180f030d0f0210020f0d14040803060d1e03080603060106030605 69
    0x12103213000044421070b011b00048005000d4001000d0341c1741e03500b8032a06032078008030f0820f42c1d42c072207200c2041030035520140440c2d81c0896004909001580f12581100e01c5140b5590300040c2e4030780104016521007000e03500184e081440702c810401030354415441280264020940c1c615804500b24a450b84410219507032201e070b4000b8030219035254010340d0041c030b02000190200050300c0c64043c0704401d038220a11110352000000c801c1c411400400d100c507001900c12858514005401c0c903400c40c481141d120101018072a4140d1006400d80c462400c0c0c070001c110402e8202c21508000a9200715508500f800d0460030300032030190000b505c2c0ca003401c40007892001c0e0180c18413480e0364106a5030810a1010b983c10f45c010b02910f200101000e10060400092203402d803901c4c0c4028107418021502d12220b9072200f42c080b6400d07c00402d00c180c003a25400441240d080010fa1154074003201c0081e10701da00540740e98161080e003000c042d000f0004600c145030550854429a036110030490640c0c0c0079104031500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 455200971 1250 455199721 455199727
    0x60304030929070c0e01060c05071a07050709020403060f0501050d0209190c02061b0a050d051b0304050a1a0114010c080405090c0c160501080a0e0709020a120f090503 73
    0x11040300d09842c0c040899500001646105060120750140c2c03120104071140c0c81c00a209000b1101c0a00019025003241c1c6030034903421703406940300ca64440c07280c01000760350041e01c3c070b4006030903003008122a080c99002d401c1c0d42510740d699580034069040780c0402c03038440b41002001c103112081c03440b40034100c410080201d9012090b54080c4140c00c3d0000d41042c840b00f40505054090460034001c142e86082a0b034000d02d01032905000c3c55484158100300142031102c2041820301c807075440310a540c09813500040015058540f01054080d2103200d0a030503215020210410003802404601c0c041542e01034100b0956100d5491850140784400340107000500b4548820160654428002c2e0604540720f0f0f10340e02d240c2030b19200090f48100e0f0440740c851321035000084800a0840501c40c0d400c02040f100c1c482c11b0503a0510700043c02d5a04002c0182220a03551607008800300c504001c0080240702c1c16108540c0c91209460080c03a110700745421202d0582482442081e86803d0302c1000780701900301000d541 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 455202221 1250 455200971 455200979
    0x906030f0b1f12050c180414040314041a09010e030c100c0212150103030f020a050601060c031718121801030b0307090f0507031803080c0309011401081006050603040309 74
    0x2e0390490840840081203000c10705456820100d10849004403150030701c6a0301c2d031003200304013900729030800c11141c00f460400e010394882d903c0804549801c6941400c000c80d10500002c5121007034041c5a0100301c509101503216642c1d002c21f0401401000420383e2841e401c4404002495540c0da021015943c001c41d03002007101040d4442d01d080482d0300d1008100c08448083e8400c1140b40c291451009800990000300400815410a04076921402c00b0300141191103690b84560b80c58400510825007405440e450b8501003602c26002c0300c4d00e135203040b003141420782442048114446502c0d4401c111500c103d008001c1e01100070303c1559139011400c00760060a050407001100035021114403641c041c4100840403502007581d00401c01c4007030302e4040c00100c51510300030040c1a200082069400042c990030f0040c0800d52002401c0c0c0c1c03206158810590301e8644e00b80b01c900500440c0c90048030f81070100c001003541d000201c0da0184001e03203c403040c03003001d40358006c0204922064030002c0100e02c40100400c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 455203471 1250 455202221 455202259
    0x4050706030222081c0c0827030609010e0601170c061b07080c130e1504030e180603070b16141203041b06030c02100209031204060906030f0b 62
    0x21803d07030701c24190b00415510a5680102c5030b070a03040040c65811a440300c030350340b40b25001c04400c0300119241c10226910951542c89a606c1503007100c0c140c0c0d103004140b070300d004003520031500c01a06004e01107804a10b0462030050007400505013079000da020761400095011048005501400b0081002d845400c43d200100100e5900841b0b00c48910340141c0f47c00710420740140404001000b01c50003501c08141c11100b080201d00440700c04c014840c1c50001d58a406440c0001c0354004414104103149044d1128101640d40c2c40c0c00303100c15907115100c2c8405134804816403030790138010b10082e0105d41d04603840b040d540340c42c0c1c080e04814038007880c1010060b00200d4155104441c800c8422416100800d034000002145540704660a03100c0b0301d042066290040c5580c0e01450042c8058030b003c110260309190003d440340719444480401035000700d1081b00c1c5076400e11a01100c2a0b800356400c1d80c40e582c0f04000b402c03010181c070403200420314100c089000307240315005448124000500c01000311400e08105 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 455204721 1250 455203471 455203477
    0x2030f0c0f04091a010602070f08031603080415060909030810150546020a080906180405090c03070f060c06020a020316051e01060b04050d02130510050a0509040507060302 75
    0x94804c0c4c040c10030b940300002d80140c0b19a021301425806002c1081c18100e0f030305060b403410743c4002c01c035070f200300880c24100c100070840c0a4801c4e45807030211105d80f941e080024081602c0501001124540710380020041160b034010110b0324407944a030b050710b81d5044040103100e010b900c1062507200010380e102803124411030080040c9100c8010314842500d0b140030a40c03640c8000340c5142c940d00c2043c00d665a000c680c000341ca03545e2103090300c0200a01042a40e403000c060150440c03241c024200840c4498444070f0110141c0100c0c400500b0400542c0384c40e050040d6507101e15803200c0e000c4d0003568004640c07103442030050710607969141c80320301800c3c40e55076074080254400c920340c1c401c41c0814030100b110704802480340381030540178038028403403050880c80084001940200f0419a60b02d03046040001401c403005503000c03200102d82d8082e851100e4000304e0010740140304000e0352546498200a100000100c070881590340550b444000592035a05000c4184e0f41524060b056070704c46c0408106143c440d40007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 455205971 1250 455204721 455204723
    0x3030309140304090501030b060607050c15040b0d0c0306170601030f02010e030a030e010810050307140402090316080106050d230f070b03220f08030615030a0902030f0c0f0409 77
    0x200705500400814182141c000340c1001c144141c03203030010424003445800241d0081000c4031014504030250341d680380e5903500350601d07600500000c0002c440468508040d90000d01c1d00f03000d16071f070316030740c07101e40343c0041903020364500219180410100340d80008031244615045080c00405da26401d68841d86c085040c50b0030101e04001102c1443d01c0940c40a0154000152080d11440940001040094208a4000c07c40c1c00c0108101c00308000c03e0307400103010421075141c40203030308507000c044004c900a441070505041c2c2503c68001c80e8102e01030610075080858500100030410340e07885000b0440c5100004502804030080a291040100914683d030141914000200c600c4020940c100d2070900003070750306c420014a000704c2000422400500b00d040500740c00326928071844600d07660f01c454406403500c054000c05000c400506142ca4041440d003051090745045512450171012190241c810171300228000d0085541a9503001000a41c40708100720003444a030440c42980705020040001c0c1030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 455207221 1250 455205971 455205983
    0x40803060a09020a0c06110a0e13060807150f0e0918011d0102070308100302090c1c020f2203020901120302012c06090c0d1101210507120204030203060103030309 71
    0x180001e0a002c4610042c4241c03c01510340c0b000300c800320f06089045801004044104070000c10100c01790b1980100c3c400700c03075a000c442010039412001c04840c020501d50b0480d91007845000710104c0d50194100a49410180c1039031512420202480c08641e02504403c001e9000358220021407c0d80003944500142d07854840d000003031185190000141c0b400c800400c25469942c0010300c0320506612109240d48440e010200c41d414502d5980401d042d20001040000c1031003000c01c03442c6080008c4614000c50320043c407020354880d09507011081c91070380114004502003900382c20580303078820b04600707540440c4e0b002030105e00141c0c0b0303101c40030700c446a2625048046541e500080b0172941d03a072128040c03085070b5600102d8203080550402a14028001d4491501d80c1d0103010800401d980b4138108031015580003030489241080c00b40140c411030504001e1804411442c21100d00c6240c041d0300c0b031441466070365140425207000c85030f810124401c9000c060f4040c1c0002d4010b002081c000c0c1c20000031540704030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 455208471 1250 455207221 455207239
    0x9090403020f0a0602030a0b060c0d030c0c0f0507061214060f0a051302070b061e0d020d0b1612060f1208130320010e010f11070f03030801051e0904080306 68
    0x6007050f414590280d4003240c0c801da0202c14402d00c103803580b04800c48030006550341840d100410803001c0d80e4848951003482010348032002240302c24071440d4451907a9907c110004602026881c0c42a00c0381e00f640038010020f00100901c0406208c14082e07882c0e0040b80a0b121210350b100c100502c1150700390088503a410250300000000c8940ba81900401d1100540c040180c0310403039403402c0040001c020f00719521888580f002d14600d00c070004085c80346440100e52006c42841f85101040e003501307030b801b406800119008101b040c1c00d85250b0a801c5141c50381d9840c01220082019850201ca410340114040403401040502c203810060b01c06640c018052000e860402981000404441ca070342d0304100d50881022081c60044116003003d00385d441d07402d0030080c5645400500081070328240a043c8820091302c0003d459a060302480214040d06a0101021000341c490602030308012080c4601070160101d0041c0349804010000c0815510000402d2502103440c2c40d100c002c02e03500060b0030150301c00030403 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 455209721 1250 455208471 455208493
    0x108060f03032101050a050603060a06120b0a120b090f2125050c041a0904020a2103020c0a061710050315190e0304050d05010207060507090e010b0f0909040302 70
    0x41102c6440c000750f03e01403a640c144420b0020104003580210300525003401030025641c0d4602040003619042c2c9800391042171181408405001c0d04480d49403c407180140c00318480402e0428510342c0c5000740e4850302592103129085a9070011000700445da034010302d0002c0302000c103940c030601c016500000c2440c00d200d98444100659a9403130901c07284c0300c0e100c00550007080303000d2004890318a0100c50800000080407201e044c1003400c80c266070300c0b625100c8000750456990480c4840a0912082403640c44030404403000090142244142c0141c0701c1c03440c0d00f1402d41b030200341e2501070f101c4a41d075010808083c1070000b1a4003030003601031010b14070085c801080940303040000402e105008034441500b42003021501400c0b001c0480c0400322617040c040e011400150000495080b114107a0700c01c2c8002401d400c0c1240207001b0700000814090610301808522a80b1289140a0351140d03a000c58540c0d85c0e44141c003281d0700c40c00c0442d440542c803d11039000540f41207c40580c4c4507001e40150307400c1c5441c1c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 455210971 1250 455209721 455209747
    0xd030e03120106052a0a06020702040e0a0311010b09090309011b0f032309010c12030902041a0a06050a0813030c05100f0e0a0201090e04140706080603010f020301050108060f0303 78
    0x740c00c0740e000504045506041800708800030792040d11400c1c4444007005502d80025124042558050103d48d00011240c086481d030f80d00c004084c1c046041540e81c1c0a07541d281c014000c07017131303d500c0c848658280b030005012481c10103080ba0240e545c4600031458101d00c6001919002c20b002200b903410303072600100c2c6001c120000e01e000300291003513640c081d114042c550307801e02095544414480240043c0324060117030740c0012200d01c0302c0e90000c1c10740c8000700006404501515440300004c0d0485e0802c0352506409940d06990400c801c03040b0780d002d1040340c903100101c406018403c2c3d03943c0041e074100007040c4a03020b19451060660b003c0e00d0300d0b840014a588070300d4070f040e20141000c2001541c0d40300c40f0301820028130270300baa504135500c0070b0700c3d62807c0c540000f001c20b01e85028192000b1000d00100c0d08002c0750303601c00c804440814040d282050fa8441000e441490102c0b075150180d400c01c01c4100c0c1c0740106108a0741a80e205031521b41d841e0b1540e105104280480c0300d0220380602c8100b015002c5401 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 455212221 1250 455210971 455211007
    0x4030f06050403020d110309011d130204171f0e210c01050108160608060d020a08060411091e131e11030a0b011a040902040b0d0e0703050d030e03 64
    0x801024045442d041a207002403030500d503480c12404000d941c149040c0d4581d80403045a81d00030003460300300640e0b08441600c100b038200302005243e118040584450781101c66801400c11628640003080c038058400084503201c800d00080d01c0b079005800340b28814049450307880b241e8000c5a08040f5a002c50780100c01000001c07001c3c000c0c110000b40031605200d8203400f401100c1c09000b00001401100310310316401e84d00d51078980512801c0c000100001855a160301010a41858004100222107a0780c1c1442c26110b0005403006d13190079807040110016802e11103c5035010303402d40508040391850202d18a060510701910042b00e0910307100607800800e04150000741c0242250000100200540c64440f40340e0b01d5641c1c1050081d049290040f0116000c0078000f41102ca0700e4041a001d03038000c915500c4184030716000410114808a000300f1207030807020160640e03480b920030401540b0740001800342c0d00e00c02403100401c298807465000180a11a400c0b8804007132542c01101d040200012800203400 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 455213471 1250 455212221 455212223
    0x10c080403051617010608122101030f260412030314010e070e030606060702010e030a1403120a09020d0206130506190e06044a07090801022d04030f 65
    0xb42e943d48041c4003a04840050510b401c40b0a4000c1218a150814031910f641e182139080510400c041241c007244501e11180014410f95100c8403416176847c1c0c40d01040d81084c100c403e0300c10303052003c0c0c2d22034480c0261421045081c0c1c442410303810503192503110301c003c2021240403410540c680000c82d00d0718022080303443c0a000f030603040303080078076050f480200240b1344070400320311aa0202040c41043e4441c001140c419640a1a100741d8100074100440c2c606609400c004001801000d0170b18001c14010000d480701e00e0f90f80042845946a00b468a02504c2d821200658402c0e551001d00340103192010040516105003594003007255524000075025400a00380002300998071040d510800b680043c902c0030030f0384100c940d030b81810b09010103454041c3c1003541060f00300005c2105c104601c048416071a0031210f10072900ca08000700d00c041c03070000070008c1c0c0e40c0e41c0108408002c0803411003018000d0320046a600c000000310b10214074000d0035071001c52210340c2d40c4501c080001101041a0764040c8481d6 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 455214721 1250 455213471 455213503
    0x60f050a0b090c0405060d0510030f05030702100806032508070815060405040c0e040201020c0a14090a06060f05031306060b1c05010b030a0c0e0a06090f0b18010c08040305 75
    0x4818000e005407001c2c0140310240c04a0104018415a5540300030f0b030380200a0044006503698800c5020303e02c203480342d0006040000114103a41c07c1001c0000201031940c420384200c44070103540c04041d0780116040c1c0324076a1540000c450b000300c900e11000c6402c001042e03100007604440d5181c54080c10402c0d940c0041c107040e0400040e82988020901c403250b0840010f4404000900e400c0c1c84051905909015800320070508a000c43d05581c402c00021464090040450600b20b13624894800784558400300c481c01544175030000388040c2003504c6140200c0e11282c8402040c041c3e17680301200c499000614610f43c100c84200e41c40c02045241c410500604804041c1a544110138404401a8841410390071740031400c2c880107100f4014200d007602e42141c0740078000b00b0011441c074002e071035042000e41c40700e0704560040c200244460f40101210b045170902030001150545070130a900b0280325181c0850755401d051150695654800d03041d010903179015002c400d08144e281c0c0d40d8607041100b8443e03401d100b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 455215827 1106 455214721 455214731
    0xf03030a110102040b131404090c05010c080c030c010501050901080f07091a030a2003070f06050a020a080f0403060c081006080c0c060a0c110601120f060f050a 70
    0xd4803508910640b5482e04007605c0800700300921541040e42d045603c17203015030419204089c502900400c1c80035001c1d003001d0042d2003c070030708482107418038001c000c000034209092010b049503840da0740001c91194034050401c040d400c810f07008480e980d082400743c008000000103800007154819440400c0c031921070217654007613921340011036030180129504181080a42020302d23001c0c000e0742c041c110360080a5401c1c155035182600400000750025101801001c0c0175101500004407544102d8000c402281d540c0100307030b04010024200c0103c0818284100080c2e4040c3c1d104002882c60051198070f845141507984c81294880c41041c814030b24023003078000f11628100c4410b0740f2040c00301d4a9a051180d94000205500c070840c3d00003030301d02c2c095042d4100e4081201412652407030300402500270552605200c02134404000c4908641c0c0e004050000301050082500c508140d10700011 = true := by decide +kernel

theorem cover : BRFrame.Cov 455035971 455215827 := by
  have h0 := BRFrame.cov_init 455035971
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 455035971 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 455035971 ≤ n) (h2 : n < 455215827) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
