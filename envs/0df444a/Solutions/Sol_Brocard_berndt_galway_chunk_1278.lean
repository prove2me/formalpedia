-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1278
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:08:07.154625+00:00
-- url     : https://prove2.me/submissions/7315e56e-8d8f-4ef4-b9ee-8ceb5506503b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 229676258 ≤ n < 229856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 229677508 1250 229676258 229676261
    0x1d0907030e1c0503060301050a020c0d11030d020a05090405070801150c0623040c0807030807110a1e18020703021510030f0b09010c02010b0a050d020609040501090903140922 76
    0x18000024107140d5040c01d2100080c00c030384c8204c44541c040d41c03c0c180803a0350400b180c4222442c441841002e040e00d081058821201c1100480e00350a0520041c40600004441480140b24040c1e894507525900c1c49a142480150b85005110100b0300c40804010484014180030300107603104d00b446c00f04074142c045c4c6068401052481032001c145107501d00c0c003181031200307684854011030149030f8a4560540c5da54015a84042038000104dd010301070003203074000303003c1c0c00c20720303d0400780146010800741e1075010b0290002d0f40c010044000c40600d0004101c520b60740302c01c00f00c0c0300410100651501c1005d4070007964400540f0003002648024200180c0300101ca8410038019543c0507624600180403410b11400315041681c00e0034444d4a07061010b40400c1c0144107800020720050540180246804100b1414140d4841c0c241e03084881004108034a07601d40c0b064902a00d900300f03000560400d2400e006054510040d10f4205012003005000c00e83d9440d009409910b50304000c2896945446144020 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 229678758 1250 229677508 229677523
    0x60f060f120702030a02101e05070e04050a1a06040b04170f241609031101020304031a0915011a0724090b0703020a0503180a051c1d0907030e 62
    0x2081c01030410107118400c1d074003000074031500105a00729060345040304000c6048503000140c5911000e12611035010078003698101982c02040341c1003c4c5070800d0880007080603100103c4003088890364540107001c00c402c4511403820741800c1030b5906410a42016904106882140100038098195440444140c1410001c490304840b040c411b540d6903511041000c100442d0400a03d90710003e2000081c0e443c0200704491241e00540d40e540c461040c1c03464549400c808004540c00707045000400010010130000700005802207840320030b00180d4a865241d071781c100804941c04020142178800100b201001300c288917100054006110b83c0e8500b814079224128203030f403040f1035420301d0095980e031881107800da2107140c0036402440d12544555035080120201e20901c00020702040c401d2000c1012100d285042400800580c811100e804d10207840d15464012404c4036007440d01c00001c01072804030340c0260f080700781c064195101d022070562100000c0c07005400403c00420541d88864150b00084100f0054 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 229680008 1250 229678758 229678777
    0xc0d0806100f020a021e130609050a02071109091603030207030b0a151404020706090501020d140610030504020a09050c04080106141e0d0b07020307030216050108280c03060302040e06060f060f 84
    0x344100d1691f041d02e40075001512503071560524110000f240716440e4004c45450643c0440c1944030030010300100001040701412074600c034440c0000d401006c0007002070030f5004d10300030b400400800380f071442c041c020681c0c02000031005505222400c540401c000400c801501c400b02080411002c000021400a00420303d001e0003040c100000d150500006500030903980c44204070900031030b040300c140c0b9200c00c003040c0c0e2402e401101087c00003101030310a0b8800364005200920103840a95500a207005540041d1807441e0301110000c1c0400048800b40300b164000c2286106c05200007a1030400102d0b6402c4211900807641070b10b0005030200c2e41d8180d0307031502007540010303060201d045c00d0320000d5407500a003070101d0143c400c6a001b0340e88e20030002c0901c02101c03016510700400e80d0760f2043d06d25085101800091014070101c1c5413601c20080c80c098140506150303540007440070318500420065071a500c0d580550303a0020018440a9201e0b031060890100d0292070031540e40032003d059459500c03a18600 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 229681258 1250 229680008 229680019
    0x70611030a06082118030718020301060801060f0203040b090316090f06051c020402280806270604020a260f16020a02010309080c0d0806100f020a021e 66
    0x70022100d1240e070020302070383e201c48104e55036042c0404207071020044001c8892890001441620600b55142d61903c0a81a018066840d420342e2542c2085c0031148515041c1041034000c40140a8240d1024849004041c01e1034003003419521060b001c3d48030311490048100c11b8a0008564049850402038141202d420036003d14101e540d40d03480400614002041000d80d6040546c00102407800082524003074000d082180400c1989900b040000e40c00b40f62654041808140959058840c07600c10004910564607044d20500d064000c0084d0004541c1c14488010b40c00988903014101e1045500d51040c0e0989006a4650281031305480d00c1002c0e03201a400700202c6c8030602c41e081c0d6210703001d900528503407600c9007803a01d4610000c08034181c07201d1030b0340059100c644501d000d0341c4250480581180508851803400c0700510301c01c1d003042031040c12140072886a00c18403a181c24100c0f41c040c070381c0301d1034038210340d0b9000820402901d401c00500040e01c1644ca03201002d50022829200012200c0010300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 229682508 1250 229681258 229681261
    0x621040b0103050d09081e0a0b1e070507030c03030b01021006030501021c06030803191401080f10050601020a0311030c01021204030e0604030c031e0507060e0909011104030807061103 80
    0x400c444140c800740400c582078001c0741c110390b85040c041c403941d205581200b80905010030114028140d19005040800320900c42e5042541c00318442080180c001c840e4800401c1d000100580d5000207100b024040c0e50401c00100240c00120761701420040e40d0a0381450701103080e014010040b8074103903130301c2c0c14200520300c2c00e00004200710055004080d05210b890804901002001ca508101c404a10020b08404003c000054540c41000705407209864107600c0001d040180600c41035003450709070014601580301c4954950b115101b007051200284203100107000c1c0c3e03c2c110000039201d0021110003028003944001d641c540030824800d41c0c020156500003103481d407000c0100410844020b80b41030700032031080106080e26080080849055031780210b0344114a07491070745d42c4088401c80d031011200d8038459549940c0058801c5c040000280b0181c1e60b00340010302c1d400300300800880702921f911600c2e0325202c040f018155800e01554100ca4000b00802e0b20b500039414804041c010f0650074802d030800020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 229683758 1250 229682508 229682513
    0x109030c090e101d1c0503040b09031e090102010f1e020c1c031b0306030b070c0201050c062802090a03020103020c030d09030810140a05060a03090605040803090624062104 75
    0x2038111341002d00119449140d10300d681c0410011001020030000740b007040041c02003036240145a400c42084d600f124606040900a8809000d281841c9000c1043c009500011076034240190191040c0341c64040000c01c12208404034181680c1d01c0c252020394001c40c040050716014000c007003212103034465000c0000c4109000800401900040b88050280100c1c1c4d4020380d44680314450940341d01c5500500d1703544a0b01c0060711031400380725040b1b041000410108a4008050000900400840c86d414003945405200d20060b02c05000d0085c10341841030042c0240c0d9a2001d820408407502801c00503920f1030480c40442c29849034085a80d0700d603003001094020150300200d442d104040c0c98401003641071f00c50b50310400c420b0540765400d03440540017809128a1038420b0084c07684d24454100020101106d0707403824203603001103c1c2514480b00100801030103100500c903440c0d00c401340800c100003484921600004d00c0310048285802084042103815000603440c14410500341100c00c110a0781c82e292 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 229685008 1250 229683758 229683791
    0x1214040f02010801060206100e04020607020d1407050d170a0504080303070905090705030105240d06060201090c0f030302060117031b0123070f05071502070305180109030c090e10 78
    0x4800302e0005400c08000643c961022482074024084d08145020051074203008503050340000d802603900c035900300710301b400603920a032030500b0042c455003100c1d60f010210306400341000c06c1a40071900401118170b28500045408401521108401c002141c40d03044003a412a0315005a40010383c06100000a002041d0303005030350641180d07001c46060b40f40f0b03174829404803894082841a240c100444001c10308a2229120402c0503810550b40118201000000301c1d03820303504164030240c0543d54803001175080c0b00010343c560015007102c4541c903050301e18664009540e010140300700c0b14a441c0c000d800b801c81c00d406200b2119088424058003004a404904e41d5000380281c0405401c00038130020307810801460715001170710070690754076040440350403480d00799076075801058201c640303a841003100c160300d4880d44003420803035000350341c2d0b50b4071171840200d54403840e80803d21003418440107800410000312800324135400e4800c002408100d401d502401a850040b4a04070107600e1401d0603c80400408603 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 229686258 1250 229685008 229685033
    0x60513090c11210301120201030905250b03070801060c060204091109090603060c190302070c0e0f010b040e01060f110709051f030b06010c020a0803030f01090c020f0c01121404 77
    0x10079074040c0d0014480882d076040e03c42c1c082240b44101400100a140f81c1e2120350f50140b40103040114042c02c079951601c3c02c0440d004c1060740080900040d000950350b50b030103920050600860501e02d141403180018140300c105100c2c820410000000d0b6204015081d0103880091048400500142c0c1d0070503050512900070a080030301030790911000521034980001c0281c01072106c51203281c0362101345484101034501c8030301030100741030b001c00429001880520440c0c000f400d00d014a00b40c1070500744102414650180c0c0541e089400030700040c000a059428058119940f6060803008900d0708030f0140c414501c91010100a406141e000103070700c2c04541c001510030403030949458040a40e03600007001680b0140400342007500c0c8540094581c4d400b03031030268903841c0010038000300303150740703d05a501d1907108035030001c202080040104608400c0340502c038064005800503010034000c0b9420b0541d01c445181b4140e04010041c00d0000b082146688500401d50714031129801a15250900c00f446546 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 229687508 1250 229686258 229686287
    0x4050307050304140f031c0302031503070b0304020411042d1e03050f030c070b130b0408030c070e0c07020d03210b1503060d0b0402010e090405150c0c07060513090c 72
    0x140300c45d1000007498081032180d8040d04100b4581e400c05a000c004600075040140314a40070f1070b1000c261020b5950402a01d4018461903e80c179607603181500c10300042d1030464070180d2003440d0510052016440654846004070040001c6841003c420141c68980e941160300145801c1a8240b402d00e6000800b03e2130001d49005404981c00d0004001000d03070380707105048009130305400080c000e0200360f00000080010501c840d00e010701d150703100d20f043c1c1080d82c4658401c621690001504d40c1140340d0501000c0e0082c003940c00080040e140050008441d480b40d102e000f0321039644143d0300300400d805045403040c0c1340301c1240b180b03840c3c1c1c0040c0d580c0f1004150410845d485015909400d042080803042264400e94024107030848a01080c0d8410040700c40240080b418400d94002c465010f85990714100c4c0319602810041c4551100c2c1c000c0c8560360711001d40310750103412080005c44c41c400f000142c0725045135014a000b03036a0b96010003542002c2c00c1c01c0d802070075181d4104010310441d01e42c0a002c0100054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 229688758 1250 229687508 229687519
    0x4060f0c0c02090612070603110f031303031103060108130c030c08161e12030e06120118050106050a05091c050307210f080606071a09010e0111030f0405030705030414 73
    0x3c485134104039088481c850103581c03c3d0300c80e03030060080078400c3d00055503200048580a003040118584071165800407541110340080c11045c110a05500d4064401d00c240c54104051030b60801e5400240b0811000b400300000078600030301e041c20440c2c1034029000458020340000c102e1070319000003075101c0c0107454004190002c014030102d601c01c031240040100a900076102079015207401183d03e08204031140c203034140b000d0b0980c12040c0351a280010184801c144048071002e6040204880ca4107641782110301003149000018050380d600802100d60350f044e41e0825548409107000003c0785551039a04200181c141c805c40c0b4400c000c0000060600d1502c59000042c09402e103d034805001e0304a0361904000800000c0c0b1a401c0d14001d100058001030081e000302c1ca06038041e1185e11100d1a13a0504000d090f030010104219090203115030403924506500030312001e588003481c55031502002c1c205409004141c4007240c01c000c42003040b5207140c0e501009403030b00c450f690010300803440b000303c1545004a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 229690008 1250 229688758 229688761
    0x9140d0302040f0e0612030c0a140609060f06040906090503091f02030a030c030612050a0203010501080109200102010902090a050709050f031f061d01080d08010b0a0804060f0c0c0209 80
    0x2103000340241c1d01950003140c6240041d5240c4018400111806003245800040c40599064280340620040022813159070007092501d0051803c4103403603114099502c0d5940062040c029000780103e00560040c00007c00c0301b0790b941b143d4001a0080c04000360013480b26103491490301c2009404030181600400880f09842032a01042d42014541104084540103030801c0001c10655802980200c01003c5076203000204c09031620601003008810040684160b8031801400085103024019070303025005100c0203000d90100d550b2a125559074003625542080c6d44084003e40d03591003540249102c9400903d81c1d05182070038806e01000300415520240010207103000802e50307050440041184840c0507000380302080b03414111150015003540c160000d6a00d404000403010404441229244e00c510b4100059500d08a051860110440ca500003400511001000b441680506545210501c2d0a00400698a91828100418200300848241c40c90550317050303503d9a1106500c81494806d40303520559 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 229691258 1250 229690008 229690033
    0x50406030c03061a0d03020604020415060203041202180f040b150d0f32010e070602030f0a0302070f11030d031401050d030c060608150703020a0f03021b010914 70
    0x1a608a40005812546505402c10005446510410440e0f000d01000e810341204040081d1600e401c00e42c080c0c005074456030034402945050321600091705010104690320b580f401c44080e46a01541c400d8851124060103480e080d901c441c04804c0c5001c1c4000a01c901501d00404481e0060005680968180f90f40b240020b00e140b0380d2488117404440002c0100a01c09565518401d03520050402140c04074403603001d034002800175001c41704440c0b4450519074204070540c00b04030700712015406040c00d1a40800c40401040341c01000311031100071070b0b03481c2130364600c5010700c180c1c080d00c59501c004145d0f4512410050901000d0100100004011800d4645141f1840400c50130b072032482c4103030041d0005006c01003205103020403080880620a040201015016459900071120558001c8d109034200c2a100781a14800b840d00725404080707420118240b052114000703144a00d0142c600f014590300049070140c6080d0118080b41e4069100005e06c40c2103000c0c90080119030300040d10905a10a800b01c1c00207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 229692508 1250 229691258 229691261
    0x20f19030801050409050f01050a0e010b0114030c0307020f10020703030606180b0d14130506060d0f080f19090f05150d1a030f010501141e040e0102091003150504 71
    0x525540556810740d050342043c003048001c2c410410201c07110321405650b4401e003002801814418005064001078070410b03030b0121400d4443c510350a604029040d2207090b1451078a5041c2c0c1e400a5410000e5916650740b003c06910b01691510028440d109402490b50786040c1600180b4006119540500885503140c2c030642c2c8002821943d8200c0003072196051010380b10301ca0180c04400c03101400442d040400031100884000305994001488041c181100300b071040c100f00080e08010f041d50187d807103030002d031039000c1c80c0320000340300505061001613403115403c0302d5000c0d52044281c0c0070f107407040c81031420070140c4030300210301c590900c1c1a030b035000001300d0346070040c0e010051030f20901c120703071030150b503008130100038040074030281028203001c5000021750714100910010110302000000d040d5042260800f02520010b150703e22075415645800050a00b0443c21b17102d80c001a600800c41002340c0034060f0280c05504603168005140800a40c0c1d15941600314091010b00010760b0b52000e51960706200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 229693758 1250 229692508 229692553
    0x12020a14010806040905010f060b1306050a05030c1602130e1b03030405040209180c18030c010e01030504030e1f2a0209041e060609050f01080c01050a02010204090c020f 74
    0x501168842d80010110f081541007100c0070351248000282000c43c00010b1412103103141c00001d050703000800c21000389501200c0d514082c1c04142800c0b414509181c0e002021484001d0105141e8440400d505a0181c140d803070498055074001c140210350707525000d110b0300511402c00d11190512030416500709440d1b00d503403503250420f07025003e1071500b030501d8240000b951284500e982c00c03070950381c0a19000d40c0d480e483d03940554403007218207950318203989404000440ec50b06461080e04451108610350b038100020070519042030034086803035540c074241a14400603c0c1a6243c01010f61103808581c10032542c5d560718241c1e269100d810070040d000341c070024482400c40d11525413505850200001d403800e00c00e6581c1c0907109850403092801c0446a0540940300c01404031101504c0350014010002180034565202002030103642203503140050381580d42c0b07008801c3d2418030100103070440d0311610030b404503005010f0405007803112840780d0800a603503e605100d03040807806100b4003402c1c0b50020040d0301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 229695008 1250 229693758 229693799
    0x2030a0b0f0f0d03020c04050a021c050c041202220209040c180e06031e030301030605130506011403160e180304030b06010806060d0f0c180b160f0203060112020a 71
    0x10a9810800c80500c00d4600c0d031400144c05600c40c4241c02e04403507440d4090984200741c1ca040c090780b01c105900c00d20f03c0d400031500c0681c80340d90500741006040d682e43c00544084407840c0004812840710350000c19500c00034481020300344041280640c4803044a90020608080c0594003000010040c55044454416080420b45c401c2c090350700410000110343d400903044a03004041c2d81d070304c041c0e00d61038112005142085d0140e640001c001001407080d54414680c0c40390712a0311030b0f04480801e58941d5141d002c140910781c1392000700300c0d1032901c58508000079070310100540601c440c03403a129950710500f04011120000c40141d01e04a1192030034001c000c0d10112a40000350f020030b61124401950303000b9008008540088091020000038040b900a08680302e80b590b40000e1019031200c002402e41d0f5036825410b00815505000304440518041215030142c1c403807040b00f8031410186090800c9c00360003200a50705d44558800414800030b4a440c4101d5076100b00c1d4016071141c2c0c1e81c50088019101c12454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 229696258 1250 229695008 229695019
    0x6070b010f0b09090a24120302010b04020f0726070609020301050a0209090a0504080d0603080c010b01030b0d0b13020a0608160206040b011e0e011401030b1903030507150f02030a0b0f 80
    0x20601e0f8005a41081d44000d402e440510721481d0355080d2680900520f038041440000900d1b0310307c007496021310601010900545081d40307000b4190103100b140c0d1003610b60003424254094001140c4115003040c0c1e21955a01c0d2001554600c4d06040a1003e000d40d180241c0c46135107020003281540529108961202d9405030884a03513660b01c0b0600070081c4801841555032050811004480d8a01c502c00c29002c0c6100303091403515079000d2209142151001d6042d1410b141c5008401102d66480134007108c5002d81c403d1112855a80f44501c510190215080094001c07a510102240d900c0e081030341c5502c54081100d07000c1d2751500514003242d07507038000e03140940484a4038005004502e09004152a062100000140c2599880a0540c0201d400340e014003003005a01d4900744c00c660381401552050030007101c52405140f50301c07903400030700402440001c0c203004000500c9420440c8203410128000000f2604000c4181032101c40c50195004554000f10301b8500240c0400301c0c17a00310310614132640d02408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 229697508 1250 229696258 229696261
    0x90604031b06020909040b040615030203030d020f07080c06340c0f020a08010507121a0616050106180e03032809050105130302060c2706070206070b010f0b0909 70
    0x14407880c80044018292601a020091040c3ca0f03143c041c0d100b4080c0c0c0c40748150f08141d18050070103004407401e0505a00240381e081c402000540e8000055032454036403031800581d07554808a00003503a1082181c0105010740114000d48802c1e804107d06d0320030003c0c13126140da140440020315480000070606003075141c4680c21030f00c0500e032041d0700c41183c8621130301280c05900f40c50380001d88100d0503540f00400c16910341042000083e80040c0c0d4002c171261030351061050b960707203001c030180c3d980c400b4000d1400360074081904226030402c03002c021140c0c0c0d0840000c1000c0d68071000c2d07004200042c412008442801c000300788940c150f000040360300c541c008421029030b1201c848150400840381d500102b100356101e09102c2c0100e030b0203202d43da02074010303140ca050441800d0301c0c0103402d0000c02440183e1041c402d102c0c0650b49c4139190411000c1031a004403825805403071600285586c000c50801075048080031840e8402c104084c80114180d649042c40030040a56584080001d80704507644160050f09110 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 229698758 1250 229697508 229697537
    0x60503070909090816060f0c02150109090f080c0309091e1311030129040501060903140304030c060c020112060b0d0519020a050d0b0307050603010611100e070e09060403 74
    0x601029070940b084904d140b0b0486281ca86110b80041403505036a901da6a21000055010310f2090070134900c4a40081d0031035401e10400000d001c4014400d280700300d5143e178161400c2000c10500e80c90780a0f40400e0043e1214210740e21203a81e604840c00c00d82c05512060702240d038080d40c018009416017031003076001c80255a0001c50608204180d00101c2d80290130412031991a40e082c058000d00144009030b010054a0003101145494804160345001d986400700502c28183d101440030709898110325410403814129480030318503c2290700180403041a10804245d040d07200988601791030017603842c00b41842004145c40200e51440c815440c1c0c07050200300d191007a084980055070b2204210b000e080c21302542e00c0740202664410423035000091800145900085c044d07201e4002030040c107500402c44541403d021824910060056100b408050b070b4100c1d94134001089a2280c0b2424444140b00d41c11010746050b584844d10f000d109070b02ca42c0b40000a140000000714540300340d0701a42c80c04011170102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 229700008 1250 229698758 229698761
    0x30106020708061605130302031f0506090402060910050f0a17070f05030105121905010506090109140105010809030c1b010207061418030f0304031b080a020d0809040b0d0606060801060503070909 85
    0x15030b800ca80f411b410450020150364180074070703040c020507441d522140c0c0d04005080022610010030711845022108107010168680c003007a5004a4016a0741888030740700058191043d005502d0308001c110350020b50040d1059101100c40328090700b00d45500794a41390041c0641d1800341caa00120005541440101300714a004548100201010016180000f40c0850001b20b50a08460b080c0c846070b4462050200b2070804074200c50040500074020000d02c00002070050240c20306105460410040901146900e0002c2c800c4072904400041116149003040030300d002b6112031603c40e5400360003030407000640d26019801c640400310500080d1071600726000d00c0d08001c40011226560584548003a15624140c10002000514020b040300a0045104100311101d61085d0700010702c10f80000d010701d0700503102c0400320509580c0c044050390304d4000800c0400c0c01011040340943c0e00080440030301d4203200a41d130104090325450360300c401440ea25200107440130f12040c0c90302c00000740c90410821111145 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 229701258 1250 229700008 229700017
    0x501020a15051806090105070806010903150c090b0a0e0405160801050d030302071a010807060507050a021e030d0c050d090e0c071b03050313050307050a05120a17030106020708061605 80
    0x150419140c3c0741ca61400e03401d10704035044805802d00d80d902e50078004160b411004003075000009113003981c4001d0455031100d5004609240a401c0b19440c0e0507038030000c3e03004002c081c0c003070020082c0300d81d210480714100802074a8400c0300d0300c1c00340345000c0100c0c510409242116410b010a9114134016919250911600c1c0220882c16000c15a081c01b4140020751103090140340851000ea200746594100410581800e1543e4030a03403d2100c10070044000842c046196441a07804541310b800c2c08401010a4000d010311440c1e0076454010640c00c0c84031590040703890780038035000d01d0455440d068400c500741c6000c0b500c2d01890345411111000a54000000701c0140b540502c21340341c0c4a501c5a034040c20900411030384c0c1003100c0982020a60b18800c402007100305000306022002811b0b203914250120b080081c0c0c1c0d000e50380c020030007602000440141040400c4010b540501105105007039101064a40e400a0144400500074540002450400080c641c3d004203014881a000901c6840041c0e900d54031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 229702508 1250 229701258 229701271
    0x1318110402121003030807050414331e040e04020d0f0f0b040308100506030a02070f0203070b0c0f0601080d0309110928090c050d0f1403070201090501020a1505 70
    0x30200464100d03100b060b104a4040c1580e9000c0c00c488608514014100181c020000001c00c0b0003440b040000c55441d0401c51112031007a96030403031007105201c140c2c07441d1051f0715210b040c03e0b00303500c03d214210b015440140004070000405800d081c1200010352404c2c448d511510150f15040f4010901619150660040030f61061a018440c048559a01c800d00c0c0380c203200646002500300308000500d5004468107a00085042242d03a4660507c40001c1040c04060030b02c00700c0c01c0e4041008010000005903040751150000d00310703407006039500c0c030004603684020354501c0b07580a403241440750b8000010b0f0290503038504001030600054034440490080403103050035138000402d030700c50780c1664548003c058080c00c03c180900d048600c105110700c64840400b8a40e40301180381240500110b01124600c0c001e960007212503040340070480c1407844525525040c0601000c001c65840e2904103800001040d41c2032013a07c55108803650740005a85840380504060710030503c0d0301c50b500000c40c2c6640941d40c80760 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 229703758 1250 229702508 229702511
    0xb0a080322090e101d120a050f0f04240801090b0a090c0f020c101b051e0a060605041a0d050316050f010b06090307140a051002060613181104 62
    0x650316086002503d100c0d407480d80d1150072050002000140c139014034a50004041e001403c0900003502860740d07103044a050040380d400128046034600e114504613407400c80d500c1011038503242141090a52640603100c1d110b10040203000d80e088035020070415402090607615a59401e82c40c004602c00580340c40f0502944c8aa030417003021800e0803103881091003404513941e03003440032100301101034608880c0101c82c6115203500f0201e290210340c0070200052103001c1990103440b100c2e152a00c1803510400405000b40c0c0e4986460780440c0070b500190300d803c014000c01c2e003404000d980b00280701c1283c08240d80c80c04100c8851002c0102c5040c00c40c600c9402c944520b08030b03880c0000307180c008080d804916108455603000680e080c03480314424010364050202c22280c1d5803030001c0380b60009545194512a241e01205405180341169403000e0800d001000301404000465031600d500944604044500501c0341d03c05c5d08000720508071920880e03102d22013550104c0350220064403070700d018025540301558480d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 229705008 1250 229703758 229703827
    0x305093d060308070609140708070302281d01060914100c0503040f03060b06031e04050c06030c0c160501050405011101061205011e05150f010e030f0d030b0a0803 71
    0x10000b000410b13600e8003d8030b00007030a02c4d441c544030000da00c495034041da40ba44980000d000908000c1084030490383c1c111048100071401418080d014085208a0401a90505400600c0b000e01da075049600ca003c070b03900000f10740c4e22007206581c03400f024080c03203044503541c1c0045070f01c034146514161000011400c1c60040c0802e140d8919180d98407a40001225600415040003040345502580c440c2100465800e4114949145003c5905007000700b81c1e19000b15400100703080c00b0050140350000311014101b076a03240703000000d0003d598001d0003828618421012074070f00301d0700d490402c83c09440e0b05944803850036182c02c004488030000e107086000c2d99581d0707010008140c2c10321042070302018450300020440c0221551410100840e03003039120002c41c03c2004202d00319110084071801c0b400102c400c81841e0320007900480e503120035100480c0c0c25124a078202044d800c80001e008251170070301d40c0c0034424641d00340c00344280d8856a11501206610522061600d20b4100102a65510400c0e0704078400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 229706258 1250 229705008 229705013
    0x20d120e0607020f01060e1311060f0d0c0e09070207050405180a050a030807172406130e0c0a0504090f02250201020d030e100e1c0305093d0603 63
    0x40490a80d0b0320b4003d41e0101c40c039200020028040c010040141184106c2d040c90181c00140d00c403983d00030021b0a031b140344001d00400e951132505807104404d058030080c0d25038041d00d484000506900741064081074841c0307441c10300f1340703007040b00d0a00ca514180e0142c4001840c14040c0000360001819991258030040482d042500701000700e000d460340650020a1514404c2c10040c0081d08040c044c5800c1143d0b00c007440203804080e440d1550081c1c0241510420941c4640101c2c8a210524410941c881d5001503032035101c00c080700d90403050301c0072040d00a80340c1d240d2030700820b0244520170803d00418001d0104005109066101d406030014014015242004030720090f110320f03554a01c0165a0790759400c00c1e50541d42d0403c0740c0e90f46040b543c18100b2900545516856485d900d110803038031540e482e80059003628001740701503a45440b415540000b4400710520240151400312829240d511400001003004580c01c405240300300311107460301c3c1c0c000000c03064421404d001c00c2103510001c1d807030701d100200 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 229707508 1250 229706258 229706263
    0x1305010b070b100816150e03120c010603060c08060301060b0a0f0507021c1505090d211e09060506030c090726070905131a01050a031805070602100606020d120e 70
    0x800e09141401d89000c6042840781032000c5c4001c0300303400810546551f501000c0d20001000301111b08004245500c441c0001710301c602410759508005c0c00c45082000400b0139503040001640140400c40003030214948580400003140224400003002075840740700c020000d80140003e00d5800d001402c0d507404100701d03800d0318910240165049521450140541f110082e09100303030f0b500581801c01804280c1d04100b001400e40203402c04440e04000862260f0b02c0921480d4004820040d04014041d40c8450744066600109500740c01540c540d41070030001156840c0100b045229210003c1c110f864030380b2011021602601c0d0842d840c0c1c241c2510720420300101d5800841184034804540c0e823500010300381024080040e0410780347c80e0450303003071844c224002240b01d40d06c401600d00a00c4d000e5102c00c80e80324210050094030041700c00035008441e54000307015000c52030000f80c0d000741d0202c074401e5004030f40c140120b6089114020041e0406401210043e10900c01962048030045000c50341a5015400700d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 229708758 1250 229707508 229707523
    0x9060602030c0d0903020f060d021c0f0c05090607061116060923120a05040b0c01050a060b040f0308030604110a0305071b05070e10030507080a021305010b070b1008 72
    0xd41e1020072401510103040000d0340355092185003030441c0a10390b50200c0d00c11401c05800601c2a14080303038140c04500310b5410f8070014042900c80581c00c0d500c82043c00700810008050003016410101480da459016108031682c544c0c01401c5c241c43c0111304d44441005040d03e01c0004042102004158026255242c1801c2100c1c015200000e00d0003445ca000641541c0480c0e44405c2c65103140700111078010007246000d0080082c4121954030008040101c52521032500550b44030740b1b001c14842d503d03901c15804240b16003200c040801c5181c0e110444466140124403821f503c0c54000101030000a1b096009541c000502a00104000c0440c501002003038020003810700010351740c0d9042006056012092060380e59642e4603400000803580c540350744901441c0210002404c0d007002080340036514018841c01503401c0000c0c1c80c261a01c0e11800c030703140c214109041c0e1081010b001c864803101814803074a0304803a850400245420314541d1500d20701c0b44010503207070f401d205010000401c071000b0701218 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 229710008 1250 229708758 229708769
    0xa09080f0f121008030d050901060f030c08070503030f07030f03201e0a17090319020610051915030f11070201020f01090b0609091f0f0c0c05030a0e0a0906 68
    0x707a0300c8002540300c0c4900d40d07030010481103525582c90010009034001204580070310968070404a815580c44086502400b117560080d07141c00c155001c000140a000716081e420703070307507107000351942c0d65035440805560b800384a0303a02403651030802441c00024000c000b000341510650a01148400d03000c4010010420b000c4425680c0703020005130340c8000c0d80380b0b0100c03c0f00032072119021406e05483c0c920042429404906603030302e001000011034070185041058850356500f0000c140342c8441c03990b000a41303c00c82a209070000700c00c0b01c480070941e071910b03015480d03148004501d5489058501485d044d0050b00ea00500030505941d1801c1d480041c600b4000d034440d4201400103199214210b01c00280b41c11801c040400c11a45402d1182d000034620f4001541c002c03104482c0c1590030b4a0f1a01c1003406c0c450b0505403c600d814039450002d217862581c1d0002c130b52160540e00e04105141c1920002e035020042002c0080441c0c0042003130190441c001c49100701480303805801c8801c5280c44021174801c5610a4020 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 229711258 1250 229710008 229710037
    0x18010807050603040303200c010b030114220204240b03060102030f18041a0a050103050c070303050601051b0106050109080d020c120a08040f0905130c0e1305060708060405011a030a09080f 82
    0x220424003400d002b0a40c00e002c040d4002c0003d9032070a05040e54041c4040c100c05003113040d01145c04002d00d00032101c420003c1d00184104003ca040342064005543c0b41ca100c20941c42d8050303030004a080110080d41e00c60041038002c2d41c50440301007103101c001c4d071017003014070080400c59000c16400d0329103100d140c0480f40c1d61020440400913542c200040b80c50140d04c040d040605100030002c05042910544000541c9828045440c1c0c841000583d1075008546140f0340c000882014030310320900540005d0102e9000703032104030b0604d07143c1420030307142e44e050008440513030b01c4040c80301d5050400a800540000341c60054429200b42581c45503e10741c8940d11040080c441d40b0740034031603000d46200e11a0008041c0001c0d100b000b59640e510756035901c00d807044071402c0e110100040c2c40381103000c4030f074048980c0c4901582c0c0c1c82d250282d4003610a4000b510060f00641c42e000c00414078400400640d043c21084a1303103a415599031006a030080c02c50b1032022218203909000000c1c1c40001400640508160380c0d43c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 229712508 1250 229711258 229711267
    0x4030206060a0b25140706030b15070b04051f02030604060f0501020709051306020705030a0806011b020904081b071d0609010315061a091801080705060304030320 71
    0x14024544000540840c0c85030200e180100030080d098011103081c07200405000c61400350600382c1c1c4011111842005e0f0426800f48156683e08030040340010990348030780c90401c00344440c0f806108410b00e20395904803502104000040228a850071201e0f1701c07500c0369080390046600d4540001c000c2c50862816407a8035000300502900780380c140510f101070200c011001d5845842c00c00001c0d5603c0032480f480e4211950f490204421255101d80d28249036008001956220140e01c0c1ca10f0340da60260324068001250940840c0031580b0415000303c62001d01803d41c800001c0c26020040f100d6000782046401700010003a0300c0205440c85109050109294090840c1c11b00e0802c0030140100c1d10755150705000b000c0700800c01c039a0b0301d0181c080c1c1902c2d000703084a040e00190341780f210008c0100b41c000b2009040c807440b2454280c000c040080085203020f0380e0340c0c0304040740705441a0f1008002c2c05140d0b544c0d001480f06002a0600d00c01541d4413600910723005c560f0070031075000070304045810200400e62080005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 229713758 1250 229712508 229712513
    0x305011104030303061715090120070b070305100b0c15010303090513020310060c050c130204140915010c0507120c03170307020c10030b031203060f0d030c060203180f0604 75
    0x100d0f40d8020031b13488410b050311000118420340c450445a09036074a00522070f0110349101000d40c030800c49054100c2400d01044e414015006117600320b250200c0e280704d126400180410311074041d49001d0010115124102c504120140719039400600c000115480f070060a1030202d026a40024000c60007034682c2042c3c02d08110501c450041041a0b00d4541401001408010000d0307811f6041280d24501c0c101b44201c2c00c518003030342004000c80c0720b00e51040a26072814003007201c6038010006c546c81031425680c070700b0821040c4080307500100c54030081c1c0d006500d06001c81354000c92060407064850070a0b240166291a5500c181031818001503444040f210400e0041000d1315980302d00f162a07003914941503190840009584481c10300040b070040b145964a010103a02a41021851303010050540f003020705005404859908100c861510401c0858a1300700282840e21017800f00399050380d41c040f9962942d4440d04003039030002e020300840e20741030354210b007041c076060140581c1410b1550140c14142080d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 229715008 1250 229713758 229713761
    0x170307020a081b24040f0213090302150106020d09031509170306030d0306150f0203040801061e0b1e0c0a0b010b03070f020c060d0e0708030a050a1101060302060702040e01060305011104030303 84
    0x5100711440d81c14800354460201d01310103900c0c3d801540300700c807002d1001d002c3c030105006000350503072403000c2c40c1890f2200003010380105100700400b05c0d1000090443c0e0340c2c0c5908a03981e4103a408030034041020100d051001c91a4200e4480c40c008951101080e001455075406140a0703444456401c03000300030061221501d030600110440c2107240c602444814240140c0720715015101e500d0398280180041c254252a0003482038600808111008001c1665588100041c111001c0c6002600c003200351004120b8a4100007079400c1159a594110614054407126180592040e41d004034144242d12650700010302403083d1a02902d204540f0603100d080070207028191801c074110030000e5400013040e01c0010b0f02e920041d41c269020001c008120445002c20460800d28503420505190000054650090707410100921400f40e465030750407842c01d08030184c54200c0d203090000070340c040ca040003144094901a00660720003081d130350000513940d54a641c1c036421102d04a4a01e02c80c1c0714041801c02c18903416 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 229716258 1250 229715008 229715023
    0x5090303071b0e1e0c070303091506080f120f03180a030906030f0c0206220b04080301030203120405091b0d0c030b0f03060402030606091b03190501060c170307020a081b 74
    0x3081d00c0f40405400d0461215035080303000f0480f0074940e1000ca058424540708c0c0d000100c150360480017a00b08180d030200101c015003c1d07405070304924840c1c4040c040f8940c0001030300245000d106401d550a00d42100d88141c9103034400f03084450688030169603988000f00074000d062209209403030f51140b0ba0f207000d0300582910b090004104401d45040c500c88809a000300d00c06502602071441c041100c0710180c02d40398242c210030300c00350003013001c0320070402000b1018000314117807402101110410301907072074200164070490003100c0d0411601000b0466221444984064034207c510b061420302900d1240c1100300c07212080c4400000b40c482142160074105004800036481c000d50252855180c10b8000c00d0391402c01a1050340540002c0300021710112500c4140003031a407010420f140d8a04200100c48880030380884c80c0340f00d083c6414000a003944c014080b084c08980d20400c506600400c192a504294000a00c02e602b517002d4a15814000380312000207244400518942c5400010700c1003125142900 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 229717508 1250 229716258 229716271
    0x801141002100c030e0a140114100e070c050105070905100f14090a0b030106031b0c05060f0a06050316030b01050409020a09050c0d0216032a0305090303071b0e 70
    0x184025614500d0703001c036614000c1e480c41900818040c1003420220700410007003000950798012401c102c010000c001f405403865243e0b0030002d00c032401d00d040d0200002d0b241550100c40c0803507199130801444c441c8502d82d560001c0c1908140841d42440c0d12103d00f502c40440d08000000c0944009004919000e075205074200031914000c0c0c08100640c0026007a0003203811044002c00000c030301105255a2440340001510b6420b2003291a541c1d1140c01038054031525105030900e001ca40c180e130140c0d0380300381404511584c005006000070f88402521014141010f041d441200c0d440341d9012903103890410002c001d4401544040000c2c41c59810700424466068010602c510306000a0340701603501c155200081d038500f420300143c5a190100c10800700d105004500d0100c80c0003150700740351151004800e0352014080d48412081d003501540021050409a17000e1030741c0d0301d4450700c41002c05d2040c0301400c51250081c1c11289482103c0d11480984c0708040061070700c2c01d400d00340500080000c1205117802c41d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 229718758 1250 229717508 229717519
    0xd0914150714070206041703040614030705030610020127020301110a140a030209090a020c0c0a060807120e0618100b061e0702120705040e0a020a03030f110607080114 73
    0x81c5031100408200100d2100b042911011449a003956140c004880081c40300401840d04190203841c0d4585070340040c810070011030000a0f51010b640300f0b00041728815801d0b03680c0c0c113285580f60b800308800d5aa110104030110365842188800c000400181500c0090480c2c00d03000301c940340e0344101429100302c42c101d411a84020300c036424580d600000014190345810300384c01d0700c400c4488001c50080c01206400c0c1c0e8850100390a010b2100d5640d4000c1079540c2508054500700e066860610541d1340484c410723140040c0020300010360480c030983e5032100380d210f10803020070350300300f0103150502c1c000040d6400380c514110518010343c080d001b01b04c0d071390305c00410794810300c031400301400014080d001f47d0035440201c12007044460158540c0f83c040f5900700382d00030007895000e4100c0c846036940309018042c090081e40f511203014110b8000095444460364010420080c0f00c0c1955000c45120b80c3c0c4054500c140013060741d034050304040500540e0b10511241e070b1203c24561600c00d100e5044800d0140950250 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 229720008 1250 229718758 229718761
    0x40b011505270312030a020d0f0c09142707180614181207150504050a0b0904110a0809060115020a060b061c150906080a03030b04020d091415 62
    0x60358920741c40c02c40d100d454030004904840c08004a0705210800303d070512143d00002c20400d106000f54040c01d03001c1e40c02c000c2000400b08601100045030440d210020100b00070860800c002514401091035896019000c0789071161902016103091a6043d40c008010000c28100041c80398404660f02240c81000840744a451601d1809440c046581a8801406500081c00c2c16440c2c09014482002480504800e220303103810b01e031140c0c603000f840c0200c4650219400a0f1440544142c056400751840100717a03919062038a032800c203042e44412502600603403240c034444c11841449001d80380756001030311034988503e005005030703040a005801c5052103a41006070300c182c0c44d900094440c816a807007d80080c4421a0307800060b258002c003804006088405911414955050b8000c3c581101d0203c4c0301e80032031615046c41e0020744a40740203080b0941d010a0410740400d100303811001030407002501c01440c00304501308240c15540b00003c290381d014011a00003004000400004101c01f61081020405 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 229721258 1250 229720008 229720027
    0x91207030204050615071e210f0809033c1b01020415121401061d0f0d03050f04050a270e0714031c0f02120c0a020607110405040b011505 60
    0x43d0250900147c0000c1c00080040704441c048040d1131700c0c03150010300580c6030300002804580030070a4081503800064119585c100014055080316010305000c1000c0d6041c40b41d1303590020080c03a0380c0c3c0381d40080c0c544072011680c95450088403060b1a241c0900056543c1d001c10844480c2407100c1c1c0400d0b980301e030310403c030411210310402503149c0348503400d00e006018480c0203101030001d4000030b80600001e210b106c00000d15141c1100c007440c4189525400e00b10310488070700411061001c1f104600307410a902d03040700d0000a1140d0001d14541d200255031508164459012441c24210b0360440b12017050001e060100d02401c08040c0c801c129114a802d00c080b400608040e0b0310344002c0d00c202040d419461207041c0700c5903814001c0501580f2078103000403000c0407200d0014140007190141e01c025018202e0300106c402c040d10300310b482803008032000b0a106e10081e424020b450740703c8507040c1c2c0c0102100c034600c00c86a90f86c2c02070a001c0c9000300a08240740d41040c2411045090549d0700c06c06000040014901 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 229722508 1250 229721258 229721299
    0x219030c0501050c03070c08030c01060f0e131b0315050a090c0e0601020a1406060a060903170313080703110c300f06040f0c0b040e160201020912070302040506 70
    0x1501d5081c6071494603071050410321403039805682c000400b001d81111010450b00000805415543c8100000b401a01d0350b81003c0f10100f00c090140032040b11007080080d0990392071000c060303d0300303214003500703801988806043c1030000c0f0980c00403200600030000010154031540201a040314a40b2820881401c15548490b481d4280340701c1c1400000e607541c00100981e00902c010035a942e00102c440040c02c044403072440d254070040391224400d4140b20030105800c1d12482c00642900d0340044602601480132000c02c80517040103048503003410305c070301c450b0300040c0c420000727000341c14800e4407400f40040304017411504001101c0a0b050051010328408520300c244020300b207214413074490000340c2d650501745210b4100f81c41c440d0740403800d201351001d10040140c0350600010343c1c0d024508224031191211843c0109100c0c500c40c40704541000ca000c540200000f641d040750b48100c60000500e06031554000c00c80800d80c01c0321584058101420070001c0d82021300515510400488001d201c00240072588036 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 229723758 1250 229722508 229722533
    0x603021611010201020d020a0c05010e030a1b05120c031c0c1b02040f06120606080a0b0f07020c12030405030c120a030c150f020318010902030c131104080109021903 72
    0x8140190708490600340364000c1d411540200d04440c8255652250042c010f006007c40c101c048a01b586403042c00e0b4041c0101100383c0d0b61000c0365030340d05102c450301c2004019035807801c0c101c255424018601001801000e42d0001d2a01c6400c00002c2d5440703510100d404a00300115094003501d103810000300d1045198003400d0b14207401c00d0440e02040035120f81c0086002051980c0548040500d440c1c0085240740f19040c881441c1031141030240409600d481e12544c9800411000034902c025904c04038086c1c080a80000307600079503030303c100e0b81c0300602d51001a01d003c0e20844a47c1450708005004e026a007014080e155000c0000d50b4000100c68450740b490340e0f20440020050100070507000031000700507004204a461b00d410384024400c400b4409410341c003d600554181c2800700310b006e010040764206016024045400a0250601d410030005101260401900041d411a91140b11500e0080610040d0014040200000482940c14030500c08500000c01d804c0c000718800750001c2001540820340c41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 229725008 1250 229723758 229723763
    0x1c0e01080405120c010b0a030c05090106050a0813020111011d0705060405030304030b060105071b092a030203180102130e0601080f1609080d030b010e1e0402031806040f0203010606030216 82
    0x1980d115050104c0b28014500c071140c003a80a90340001c00004d1040c1d491404c416185e00301c3d807428441e641c81c85d05803050b100e224a00750100c1c041c0800540d4810404208114260060601e0001d609820304031500f150103100450b03036082103d4100c0d8a415234104864800703044265041031809080c42e000070380e2402503200c020044180b40700041d440d41d11503002d641819078400d0420440314428095960155094014000c8140c58103881c40715214071b6207a00c0340700150301d40440503840e407003080c00c4000c1d500c024845040041030080c1e440d03214201344010596481c400920100042c00d0201500702c40c8005010a4104102c0c41d0a100215100041d0990000f10900050640ca07502e2482035480b8403039607010808a00450907000300d02c5e50160000100c0e0b0790309030f8a851800801c001007010000c102d60380703007283c005402200c4000e82001d500071904070040410364003d03031b01c030301c8402e9180000c01c840440e84c18082c04014411810309020301005491141019420020b005c0c1c94058982c11040c4007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 229726258 1250 229725008 229725043
    0x17010b010815190303080f060d030e13060b07060e0705090903030718030807030512010807080a0b0402150c030d0b0904172214030c0d2a05031c0e01080405 68
    0xe107409a503c1581d860560b12101c50080d03c85503403818007030064141255180f00c4507007005c00046c0300d4a403e000c802140c9074103480c1c0070300d120500000d0100100c0c041c240c82001658403140803c44401807400380412300d11030000032441e0700710b440d0442c2c00c01c141d0390f0006001e418034509002d800b01012082d41e230300200324900009004150440140502840c0c0d0001c0d040709000148d440c14103910400410100c1c01040e51445244d07624080b003561461944a00d03100c0d50090310354100001c90b10f403915078029000a04090060004030450581944031980102c41640000303100c18410440d40181c40e2400000c0326a002d480c6003a1f10758a0600003a03841b00c6128281c0043c0e0b6841c640d60200f002400c00c2c0f110343c4c80e54a010f464003009c0300701110a1a0191191048090f04440e0b4502100b80c4001a503002114025440792100215424146410181c4180c000810045450344007002514090b00070800004c3c4210600100035000301941e0700210b040116007001c000100d1800184201c80d440004c03103 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 229727508 1250 229726258 229726291
    0xb0307020709020f0322050d1101020c07060c030207140a090908160b060a0f0f06050f190305010501030b10020c01050a05071a06010201110a02060606070c0e0f0117010b0108 76
    0x4101d04041c0c40380c1069a207644040f0301c40040303100c400044d40c4680415040c0d102c0d844200c20f022812019403840c000d14950007503608501c10340c81400b05078404041c03140013500b05550700b440700781094441d4000900140280c1e1400e41415810485100200741c40e2000c403a80c1d035400c4001c2258501c00d4021040070340e44800030a020006900d0072070703806075211042d00c00190a9031401001c2c001007518010b2017980c8501c1c010813011080c824400460303862074420701c1102c3c075041c8140c48030303040107082aa42030014060541d2103252000e902c51a02d40703075600003038a581058005402c03503080c8a45180103496000040c2c0250750001042c840070b80f42401c0c043c2e1540c1c51500200e4081c1700750100280060042ca070209452400984100d0091000340c001344103800754400c1000190203112507050040e03008002140c41c03410404000c000c000e001d07031440f034070f05500c07404800340072001560350b032542d400e040c40104007024195060024400c0389500900c815105200000c004040282402510b2196000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 229728758 1250 229727508 229727521
    0x602120708070209090a1727010c210f030207120c08040504020c0604050f03090a14040f050c03070f140f0c07030f0302160510080106080405070b0c0d120c090b03 71
    0x24140c076452a0f0007851001d03c1d140c05504181c81d00e01c1c2c00d00c11074904131105542c52009104105540c44c4000c410103030b1110000e0141d000da0680540c0400c0c60500032000c0c5000c000c10281c3c5480c450342641c2c048100b03a4450448002840d4008698107501014418805000001e0485030304416152051614017942455814003003943d110f17641c0035a512520025414840d4071002c1605403040d4050020380e40c001c841c18482503102d05c83c008040b54426016601800610100203005194100c098000190108500042400c80c1d50a440641c01010003104000d01150300540308a8501d1a5250003001c030300200400ca20a0b014100341444046000314864032585c2c01002507100864001580c1c6091881c02c1c10069200e00d02d144403101094146072000c54681080804181c508041da40c805c15a40e1038a0002c440c1028007a2048031503000d441400210440001d0183c0300000001001c1e1040d118060360180191601e603005095250818030500c09841d0440001380854502c00c1d0080d42d00e64840 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 229730008 1250 229728758 229728773
    0x170423040b270a02071a0a0e072403060f0504110903030a09030b0a0b030604080a030b090405030a09060905060406050c12030c12090604050a020f040908031906050a06021207 76
    0x1c802503a0070803032003800c0400080d100521200c03948490501100c95403a0103280300160300c12010058000d07144002c00a00b0190b0724003039903522a000c03640014480160710340c41c0c3e040100b15400f02a20240c2c034051034240c0078084c2c20300c200c152580d0a0400c0070503d440d001480d02c3c0e007a84a154440d82c0e503080d8200110a94000302e580d81c00d0000c0030b40c0c0e508c50b1540f40281800703490b40070588000341d41c0e10000d034951050748108401440d00800800030b5940756070714002c280d07000a80359410592140a58582e986510200c81e006d28400c1002d135445041800300100400a25406101004079801c03041015481d09011035003030301c54a02d40241c0d12061030101500d004042c0684d40c054050000401c8829a80c68014100ea016503060480c000e031942c075036169803008243c502601a80203002d5650052914a529110783c03280988041000c051546400b250b80d0400c80781100710f841132402c150306040f407603c50a0041c0100f225440181414079100a6450015103201a06441c001401c007003030010030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 229731258 1250 229730008 229730021
    0x705030f07030c1b201008010909080d1e0f06030c050609010311030f0a06060507030f0e040f02040602030d06090615140d1b02010b030111091c0b0c030417042304 71
    0x940300404d101c180e040c541310b00d04040b640b01341600c6407540c060800b140d01c2c0502038a803203c9070a40e80c2056036401e01c8414401401c0c0007070b013203512003004c02c5981d01c0046c4038000c50350051502134030600b144120455001c165810034022502d018641a000c1c000200e0301240b042c20f94006840807a1a0400c10300160001d00a4100b9400010400b204010001328040d843c039104001600052044544d41d420682d158040c40100401007400d1440b0035074558842c20300740c2c401101c0100045600301d16903900c041244c1c4190000d00c0160000520790031041007500441c4004e0280300c8042000310300d040da020750380800389402e4400300041c1d4401c0709505a5a00161864203400031401c201c0c00d1012143d60091450b20b034a400099400c1020f500082c0c80c0c10310504007880e030500b002501d0820408204000300c2451850103107000e46c030309000c03404180c0c007018051141003898060381d43d90400b424446020010b264807080400406c220900103154500e06c808114403e111240c4040c1d1140760019015041 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 229732508 1250 229731258 229731287
    0x6040503070b0306040e0102070c15051306030f06050429060405031905010e0627060f01090e150a02031b0a0e09091912030b042c0a150c080705030f07030c 68
    0xc10f212040c00a583c504c84120b64400c0401c50030344800060945140c0240371004a01c0308221504001c1c590190300900c210981040001070a00d84600010301214024000354900c01034500c10340305084d10980d010540c40794110b40450034180340000190b900e0b40c1c0900a0700e8680340309110101049825040080705414202c04c0d5801440c002c0c0c096102c0c840c50001c1c014103500c5586d43c6551516003c12010701a00c01c05002480980c00d018580c0050000c510300b1404600c5051408401c2c154603100407402102c3c0524056640e007000c041d404000160601034181c0300a0802450440603003144400c02d00780c10a0b101c1111130740d1000c0a060529059114020500505440d840700b080300c81c0042061122442e1010003507804103605010480d580c10a51115101000140800b01080112141c0361040f0041c00c480c1404004ea0780c60317003502e000611101c20340c0d858400d01c02e8101e400c5080f0580c41030492616904514100c0703060040804058144003e05a13150b01d01045280301c0c0211501818 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 229733758 1250 229732508 229732511
    0x3050d05091201092907090608060310020c03071103340b0a0e0a0f1805040606050a1205070603140604050411040c1101050c030103030503070516061a0f06040503070b0306040e01 78
    0x8405003000d80c0c0395002e82881400c1c000c94421031818075569040042e006c1d002c00d40d42c0300500360901c1001d03903400c42c014041d141c4c0b42c400d046034101c079242d15000a2a0031440c0348003450f220606842d01c100281406051b040c400c0d0020b440c1e81c140180ca1364001d0b04180e190202c1003607100800b91034000c2008039508003144107100040c16143e1030760070000380d82c0c00c0b90040c1c501002480eaa0701c41854204128064401903140c1c0c0d11a2901240f0a40c003c80e40140c000c20b40001c00f030b40d949000801d21309181d44810302030f801800c46034080c013800344108001040c40b800c080c400005228000c18104030000c00f07a502c92540c2e075010500340000f10045a10b0700801800802080081400c090034a10800445500c0d56003005d000a884511880990303040b00e915880d0030b811750b1a0114283e0340f039001b0589540f04000d600121f50301061490054031440f0b030007071481c429410070801c140591031320b004c1c8160b0701820b0704000c200f01ca5240002d07410101c0d0007000b0700725203c2d129640010050188079504030800d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 229735008 1250 229733758 229733771
    0x30509040c020a020a050a06050d090206091009031205090906010507032f0106080a050c1023030103050f07060f0c02061303050619050709060806030c1206090705010903050d05091201 80
    0x442d000110f4405072402203a4003010075940d4010000e80c403805018440c0000c10501c0403075401d807000c0d0800f03900144011f1030f090070b16000b000440c011401c0540c041001800e21003040083c44442d210b20500c4140700c1c50007a00d82445240459550320f80640190704120300007403a00c3c24544030b41500d45a05c0000352601d40b40c031103000d0306100d11400d82c41314003880c0c1d46002d400058082002030420300c1c050740a07000d0450f01c0303081e1341001040740300f8519060503c0042c9a19426080818001c00074000c80c0e4070074662607505504255141c60b91000b00b02405078071170182848034a41060745070a40708ca1528111441044a101042c80c9000300c80e41e0880f01c110805d4040100000494480e05c41d00c600c204201540c45007100480c182c80d8156100ba012540c039210501019201c0d121a42d071050018045644100c00240881c602c1c2040351400f030785641003c01441040001442400d000700703404d1800d40ca203e0b046454081ccc40f0048021280c3c2807240004a81c0c009d81c40d61114005211a0b440081181 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 229736258 1250 229735008 229735031
    0x11a3006070f020c0a210503040312030e0c1513080a050706080709030305091306080313030201080606040803041509051302030108010c0918050612031303020f0102012703050904 78
    0x9540c42510a6004609400c0300480100c2c4000740c6080e032824002c103c551507030314140251000d0048040382a54044110380c490001c41d00c03c1001b4001184501407003c04580c2d840001811078002d01ca0f00c444a801c210a0a102c81c2e40d03e0400507594601e048416a8801904014682c0d0f04c034241d2050006000700614501031003001310b00d1a04441581d151449643c0e2411801c80b101506400000c000c40c005220511180c00d001003032115075680c1002c0062040d844520043c039680001405400f6814000024011544e03c5003e054100f4425541182005e09007140ca648a0190b030040700c0300d40810302407040035188140c1c1d2001c000c03c00588200f5414940c0f50801010398400d002e00329075982480c20749490b19104080440880703880f078110404000119802c00003401c000342040381e1195180b034420390000c4040c4014018613900c04845000a403940c4184511103054031030311070559151408004680201d0100c0b8a00851141034148601d8036a103404d940600410010315040761401840c1d500 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 229737508 1250 229736258 229736263
    0x24020c0a030206040b01150804080f0702090c180402180d06090b010803070b06010f051b0a0b010b04030309080a050601030b100803030c030a20091003110703080117011a30 75
    0x900d00403240741703d090380c940100d14107078180150306800081c901800a1302144031007000d017604040c2c9400c92403400d00d20350006804a102034952403012480040c541031411504960142111815101541854008481c100c02007443c041101d006510000c1034900708a442da104448955004100c05004d5840d07214079692500400c0c001c0708c50038101c10101d80d4560203680c400146c1c54059546901c0c25881c0030580810168000e5070704142d01c540c915010015031800d2a03140030f001c5420341d2540300c40c0f85040090110074513a104000c140c0001c91803c011a0000c100541501e400c14001300f070503291018124a03101e42e030b901c02c11060202200380144005900010741c0500b0100c0d00c180441520078021a091044007404030079150020041a0111704003070f85003e00fa108642800a4420f0f00301c4007200c0c0320391068000710000742e410070051080b1080c00b14100920000b000003000401007c1c1c1c0c40040d8007a44050042c80746100540308442200c81041e0001051400c00c401281034000f20440396 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 229738758 1250 229737508 229737511
    0x606010e1807030b0310110306060d0f050c0a0314100e1b03090601230a06110a0614040506130c05040b060c0a0309030c05012a060b030304060518090424020c0a030206 73
    0x91203401b50005102c0100074900070000440c1450b080030703186071941304c100070180c0c1c05a8000c41c1c00c10340b00c03207000b0741751702c1e50380b26541c030405018080c40e94130540d005005044450b414071a800441d070311801e02c2030420304000f191098643c8840e14500ca901e88240400c19102d0420341100054000420442c1d0000d000c28154103c4400c0511010140701c2c1001c9103802030115030280d070b0810541e0308204582c912507440c0d4140c0e21001400c0e14403449480d02c461041e01c8202c019100130b042a8003d000c00c01408104140d4400d98900c40c2801804035642c0310303000c1011511a962007513494504510702a0340e001c084448205c08403003102e00e000760307a141c040d1a2041d00e1000381c0e49a20034440015580d4000c0300b8441044990328040d0449850b03a0b000320a6070551104151501a9200f84514454504100400281016886040e1203143c0c0c101d00c020040c0d541140ba81c001d240040c10f10001503440740c0b01021000302160107004050225076440700034001d510030300c41244a0f551000c5e0505401242c00e5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 229740008 1250 229738758 229738781
    0xa170409061406120403110307031e080c070b0604020f03190609020918180703080c07081c0807030f050a022203020a170703060c03020a021506030606010e180703 71
    0x180011555a500c0d510340d00c0b4004100c542000d410048515846000641e00d50f04c1882810302e811004221250289150030851044000c10242c050703022500b140b040c0d580d8030314805842c02016526041c0c0c3c0e02c1c00c1900130404014081c01203080840c1081e900d0b5010b588103144090030054503860318050001f4148100b03251100c50f2032800b180480e0b19074450088801c41c0001504400c4000507a1101600040c0300078140c4000d101215407160441d1400d1060364011070042200b04d48039019403030081e05050983c0d105060b280d121008124126010b91111301c00104503081440b2075568002c4141c01400150890a00c810b2400e0704104a031182036002e00240f00030000c0c0f94805a6510b0f1040d2601c10450001a51040302140100000900c502c0304402c01e1000c1802d0b00c0711140d40ea070301c0b0400d41d42e09070070782d01c00709401281031503005504200d0080300c0c0120500710300b41070070150080303500d80c4005001c00e410441c051005240d00e0f1558104410701043c1e44a1801d440c0c54510f10040c0202101c1030107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 229741258 1250 229740008 229740011
    0x16080d0b0a0e01140103091b0302100206090d030203091903091a0c1b0612010806061203280c05030c0c12070609060309030c0f0b0f01061407020d02030a170409 70
    0xc0d54900e0034400d00c101c0603202c40318400c040d0740e42014030080098074411825410151501c41140c0000c1e0409010040817029100c21452941144104a207500e01d080b0300008560102c0e0030440320000004043c0700c40d8510b404d005a8a840b90b05161b402d0626030a01400d59515060034282016400b031710480446401c1e844e142d902220501c1d002d4020710400c0b060803169484083e00c0203001c86800941030101200400c0c40b850821070b01e02c0c9a40c4d00000b40d00550640c1c1080b410441141007070503105404a40c000c000e145061a42d01c2d019603007000510081c0c08d1400640c101880c01070007866208100d50304802200d4880200d9840039540f4007114a1580c0107050011100c4090a000a141800d84080d03031261895581420401c500908140b076051b010030030300003120400f2441c23040720415083d024002c0e041445c90201005038403014103900c21010482100c080c00c062040c0c40050b101c0340c607411102686401062f00005c0e03d001d81100b0080c01c500d20b01c0318840480140613004000b2505850f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 229742508 1250 229741258 229741271
    0xc06040b09010603020d020907020102040509040503480f0109060e0706020c090703020f0f04030f050c19031103030f13030c090b0a030f0611040b0a031d12070816080d 73
    0x72242030300c50510000b0f400c90300078170091006103031840d4850b9001046100041c00c0950f076500080c410769055409542680001400c1e2072400080025005101d1002c40003040c020685202406207030014101007095080c00801e41050b184140030099010a40d100244880011420210010062100149118490f6a00c0001c40c64000710f0b50b43c0c0c81c2140200094000d984080069019601180490060203c10002d414030180410040d00c09180a85400300000e883c030310b015490001c0c460f0004c3e00ca403074881c0c030240c1c01c0704002000c00c00740c03684009494280303141e0300042495409403181c103005038400812080c030b900d440100d1000031203005100340e0f100f960390303108800c00b25640840400d402400141041c40403850303005152015611898002072222111941c944254000c2e0300041802e40300080c151802550501850522442c520510012a1410304c0055a68914510104400030f8040340a00c280709214007900c000c04144050005030300325514004941d50b1180ba03080b520f4a01d803c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 229743758 1250 229742508 229742521
    0x1120f0f020c0726060f07020a17030f15060f0a0e040c111507090506031302030601060906031d1c02031e0307080f27031c27080913110c06040b 63
    0xc8141c5811913002000c3c11494840f584075030750201004000005512551107078000081c4101884104580c4503096235440b410b004400342015540501255000d40d00c07855846059a0380c002101c122030802c201c0280e852955032010b9aa20701d040c007200307038091324100d4aa21120381201c0c000c000f0f00700420554043d0540c2c442800d041a5080e5032000005e80c1018051200382401d100454010a4030030310810103241070f03400280380c210260424800500c405d0401c0054030b416002e150302c244542100d00c2540c91f01c4d41d0b1103581d10040600c020640011751017044008038001c0c011100b01241c00800b60b001160110041c0e000d0b940b06403210130005101c40c00080d2041c043d180c403580200c808001d882016441400d00000409480c00010303010b001c05c00a110710012101600e54003040c4022012680c84008805240c800020054401440f20720382c503c1000035a125040740c02120301184c0070b09032188030560190040a071503480344480800043c010380b1000000582d02d10462180818490560398603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 229745008 1250 229743758 229743809
    0x9051c05010e0609100b06092101050604090f0b04060603080408010e16150f021c210506150309100603052b05121e0c040311040b01120f0f020c07 64
    0x311004c000d140c01c40e0000c5040c210715a0440701c00c10000030720090a1220f50000203402020215291120b5000340c803d4001070300e002c0c01100e50014044404100c1c15100b0380320100c0b000e01440000301000c0c07412001504000c8513038042805580c01910440d201c0ba21811000c0c0244000c6070310703201d21702c00d40c640140c8002d40c81b081c034402c1d650b0100301102c0ea1456103409a0300030f0101c40c4018154084c04921804a8030400341000200100c1d56484540390051317008030352603450807502d0702c402c241401c04000454403501141d104c2c107165280c000340e5a6407040d01d51070403d00701e00c0c1208181070910b00e000040c008000f910381c00c41c159280540034a00704034110542d41100301c040ca000891000e0002103804d4a07a0030500f9448030705042800c00441a42412040025044900081c0c4000204040c8244614102103102d105d038140c0c3c0401c11050b0120000e0000400d00411070740c0f607030302ca04400ca100410350708581e01c0c410720f40d007003075481c1c0d810074884035150305444c011015440e0361040c4115032403e19 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 229746258 1250 229745008 229745011
    0x12071409130903020c03060718091419020c0d08060f030f19060b10020f0709020301083301060306140607020d020105070f051207060605010c020a0b030709051c05010e06 74
    0x9168041040310807104801800c0b00c1038080d0150b0141d0090350002d9141484071030b105100c1551844020b4203081085404000250002584d41d0320b08100700c1d60f02c01da82c80e4415002480c1c001071203011000e1031010000391061000e00f60041c018508a4200300740c001003024043c0f681103d40d40380110350382007419034405414011401550081c0b09904003002c1504c04924840e01448004c95480502c0c004038404981c00b00e00303140141d0224102c3d10404400f4401040035040c00d100641c910751521118590719070318506007507056141102c0c680c0c0608402c1e0000f102411101c05c00030150340e51003002a005082c2c900ca001142140303000181c0b00c51410030b044901c00740d8010540e5a480f103194004544541080400722074502d846111103011a104101e100d81c90400d48000b1a03440e5080d103840000d9030840d1b8000c5052183c008103060045ea914503040f42558020b1440f185c0720751700e0320402c0b150740d06d59030303c00c6410400c1e052511824001842060030404e029400134046251b4035518199203580 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 229747508 1250 229746258 229746277
    0x1416020a0201020709050604020405031b1f0c030806040e061510050405030a0b1e090d020705040b06030a110904060902041703030c120403050403020603150301060f270e0102120714 79
    0x10002e000c0c403145175240d10240d04000064001400c141c1c4a80102e468440d0a1401c125102c00d00c9406502c14600301240760301d094a50700d1f107030000c1610040060402030840c24010b050182020001b0b45a444070b90049580c0340d05034046036110305001000da1800b00019103501d000340d400a502d00c518501900c202c8085420281c0241800030f0359407a030450b032a8004d4118000f035040b042c2612011003102d50f486000c0c0d14940042d05041c008540042d18000032a80000d000398185404042e0664400c4180d0b90310808c01c070070103d612103040034403014510074880c4071580140780c01c0c804981d0400c243d01810944441c903000822415034218100d0781c81c01b089507203222124081150304078101004501d660414402c0c2482800c15403680e000801681007110b082400b44408d940050440c0341c00d0107400000c0c01d40c800c0b07045030b4905001c170f00600d200301c4612440c0225a50a40c00741030704030743e50000c01c04800002c0210740342c603401d100b141004003017900c10034002040d0b212088500724030901113840400 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 229748758 1250 229747508 229747513
    0x109050f0108011109130e0102120a05062205070e030f0a031701050a05061303080f0304060c140f13080d020a03020f010c0504060c0f02040f020a0318020a1e091416020a020102 77
    0x80643e001c1016986d1224244900c0a403903140c500c0080c48240040d29010400071170b54946407a0402d000e00c00ca81d00100003605c01c0c0c20756a0804601c01c299003207400d604002410200c6c0f2075441841c1a50700c45840b0034142d41510840f0010442003801040e03032002d2a1003030b541c0c0300e4040e24034402070700b14503400e01486074413a8006208014034035000300103104218070014110200c43d03407a00c4070300807500010102058028000300700810000c0300d126004448256090191400744441103050071401500c801244a410000f40041c51000e42c400c07d2004156140859918020102000752128108e45040f40544607006c0e101d80150410b0090301d080ca50156030316400c1c9880e04030100c0718500105400d660707403001c190201025855034010420041c844100150b9100030700d4000404582140041801d580030280e226001681c9a07030030f240071122441c3e00c80114014a00310030001000c02d40c404000303140b9081896400f803000d510f1140c8146600c820561080c0340c0c0d9401030ba00c84210b440000c1c01038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 229750008 1250 229748758 229748767
    0x30a0f020a112107080d090605120105040209030a0b0a1401080a0b0406090303020904050901060608090313090911030a0309030303060b0f0a030515102f1506010201020702090109050f01080111 84
    0xa041c507015069142000d0060608014092910141051600d0f0000c81e40364001180710100103420161f039800900f010315100386422500092000781c108103028240c403690700029141c800f503400300480c01c01944c000307404030420f0900ca58103100074101400080c044030420030001400e414041420000c998100c05580e07403594583c0c2e00d54005041c4108105c003450740c2130120341c3c1c07591118450640714840034000050b05a0500002812170078008202d465141d100f0031185c520b80103c80b85110131285003207000700b04203240d0300d0142d482640748030340950103100d0341d4001428554401840421030303020f5282040035949614401790584241d8480c840007400401c14502c2c1036202342d110aa000349043d1800018060000004654001d12840310001030f00084103510810074010440210040c071152000000c40b4000382d40e41c451002420202c0d80301b00c03901c00507440c2d0b4001e4040380d9640d94024006540da41c0c4a03640710300240b4080e2004410040114008130758040c0c14494030507500100c1841c5410b0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 229751258 1250 229750008 229750043
    0x20d0305090301060e010e07020f16060c020a0902030c071509030c0f0614010f061103030618040c0b0d05090d0206042105040503060c1b0a08040e1f08030a0f020a 71
    0xd588a4112240c0565036003034001045040d06051902034002c18080b4915802c029400034900060701c001d2a00c160040071a500d00350003024807810485045052446207001c1c0c0740000741f515107a50f40306202c914000402c200040b4415001082a80e00c510f40390318100c014000b00c0402c95034201002408941011808808100c0000602c0354040c86400c010550f0881c005428554100a0b804172019010121080c800b6942010041042c109420015410b61505000041d40c42c6102d41104140d40c0384a00442c040c0241c0a01c50b01c040c0c545511620303503412680e10208000e002c02c0390746440724054102070382130151001c0340070f6000d140c104508142c03d95000007400000250141c000303040c05420040001c1d942c60921216100300700d00c0c0f41450716042c205506805172801d00e000220369400044825000800e10b20030790741580d00e402400510355032b415204a009102d44c423000211645621000201c000001005004840b030642e200e221201701000103913590600800b0050151101d101803454 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 229752508 1250 229751258 229751267
    0x3070b09010902030d0e13050606090d15020c1c0f0903060506040e0109050105060312030714090d06020d240e0103020607032703030806090c0904050a06090e0102120c07020d03 77
    0x400002640001614040b19400070345081184070261000c0380c5040b4520a2901c2d03c10300b02c07442074885a0040c031180ca40280001e03598849e59003620701c100519048003040c4801e01f01c0540d00d0300e680000466580191300a111380d50500c01d8408910008a500031a10141c89846a0b04082880e6104d844909003150340b620041c0000625040e00903903582e84288021500b4003845001030b00503000040e2508115003814140108424000d844850030014041d1a03035001c4e4444680084000b10941c031040c0b40000501d045250000c050407042c00400c024403840803940c89502100e02407082210706103c00c29840450800511500074010169801080036042000003054803501c24038201e483c44200982c10542281c0450403e000a500d01400b07004042e0030054281d00b129040300d21402e02d00e40381c520900e07144100000e840c000c5031200042071000030550443c0025110364a000c0c41400e140000c11070003504136100d90301d4822058070126114041000c21034a003030750060b050b072141c034569407400d84 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 229753758 1250 229752508 229752511
    0x1a09010e0d050127050d0804030804060e0a080408060f0a0c020d110717100b06030402060901030b010c080a021b040b18040c150504090e0d1b1a0a09050f06060303070b 73
    0x10307625500c0f50356204100c20b0110680d44e02d0911490452071403c140d05100e490003482c040c01009024032207060001007500003010580c4681c0c4040b0104c0d41040e111201410070580310300040c00c007400840c000c0f80840010403081d120328078039154980d00d6a55261494103035201095104090b0308046070400c019445030780300e040907204880858041981d114101200003145072916071150b0040c144142003039015000f8840034680c00c84a03181141000d400180e003511842074914103040d62400b0b842090307402800b20b07030f46290308141d58640364070361803a01949600c40c0c601358404840701c0544460b02490203108043c01c4142c050900d2444100401516040c910040e005480980400c1c10019440844481134079180d90b056840c0e584072132501400106a80340354404100d83d0704401c0c60a0031981d4451134007514002d811a01484250260408248503c0c4034261750707803d1150b003810401890140d801400036076106900b1510340031000c03152652a83e0b000d48885515420811050380800e411601c0c46 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 229755008 1250 229753758 229753763
    0x8030703150f12020108150f130f0507030204060e010c05100c180b040f0b1c020313050304031b060504230a0815060f06040e0a0f06030c030c1a09010e0d 67
    0x80440300e854a184208034800c43d4030480f800c81d14581040e04559124549a401400030607080303420900300030010b0141550701d0420350044400d03260240151884d40c000c04080301e041d0104100074284088010302a42c0079005410101d0000300041000d944201040c0f035803140c226028051450b86442440c0140038139080200402c2051000584110217030100e601c01400e480304c90540d41c610f0980b4940f13100d4800d505c0820304500502c64031514006000c0082001080f25078016500d507599400f460707051040c0076002e48144004680072040010700703000590806103400302000301c59580c0c3c000311842c0c4038602407a1107104021001066102d400b02c682d0521030030080440c0c481d103403141d1009142403400c903202512921420f0a010090a081c080d2007280c0b80e0a940481c98941080d0707000384140c9000d000d0100166541180d10403021541e80450065640482560600b99a90030924010000b90140c05002d400320a1483c5908609101322107400d00d068444040725801c0c0410008440c4608030305 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 229756258 1250 229755008 229755041
    0x5060f0105030a0b0f100c17031302150d02130f05100203042c04110a0506180d06090f0309030303110307080f0403020f0706050a02120307140f0c0709050703050a0908030703 76
    0x10001c2981d6101021040001554480201020b2800c8c258501d03c0085c81502e82035508109010040f8980924000e02540540e0070076244100e406e2000010703c1050302e001c0c0c0d600c0c40440c402203207413032a00c515801c880e2810001840300d034540b002c001c9600c1030b200c07008015034002c0004000281d07142082409083c0e514120011164844008200080b0111011940c862021040410a00d00582c011015290a4030f9042c206281e50603500066059030709a20b01ca2031105040c0420400c458000c005100e90090102c0c1c00d00030303d4070f005002d85c03005000440102c0c0c01e120302e1002c41b0541d02c080c0c0e481100c20343d641c103941d9111460448848903019100382c08602921180010190301040840300515150390f407240d45400b5554000d00344103050303030198404001041480a080d80c003046e0b01c52013410011340542d03241181c0360f003010a44968001100540105200000c0d02c0d10301c1e500c09441f4070700c103840a00c22540c40c401d88204031035050000414034482400490820340c4030b58415641c200c80d441c0e8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 229757508 1250 229756258 229756279
    0xe040f02100507030f02122d07050601030515240d06290102010501030b0a0b06070b010b03040c0509090a14240103050f030c070302040209040f0c0e030105060f0105030a0b 75
    0x81420421010490710110ba0006a12410980c1c0034891000c059503900c050039005110043d140068070079001c404c20045554a00241c0c0c02d04601da1105140c0d083d07842207640e86003035182154031810248800d65840c0200014841c2c0100f5900045220701c07913015440ca010a002301442d02c540c01d00d004490f030400541c0d80034200007080c900c07407402c1051201102c4184200745100c4a503150138000c00d02c90459040900400001e00b41c448807580014440902040a000d261b01040e0b0030300488901a16071410f2000026004841c1d000035030142e40034950303200b0032a1b243c00c20322000389003c1d1000041da510586802002c1040c851038034a168a1f000f098409944540d0020090300300080d076001d00081510b001002001020000400c08904440c060341c1842c03403412000342c43c0c24681c40080d001d0313a00018541d849603542e070312541c441c80c0005010000510140e100500c00c40079658054001c0d86400c002c075106140050b140121107205a5400d40356560b14011800a0440d242c241d5070084590070 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 229758758 1250 229757508 229757513
    0x1106100519120b060f0f03030324180105010306060509090a0b01142712120a1809050610081003020f030307061407090609030809061b06010b1206040212010e040f 71
    0xe240c54602e8000d49501207642000e408000c00001024455441165000c64034022034501205881c0e00041e10104021508111481c8800043c0805d2009900c00014004c2400c01c072541141c281c1078501c01e80c0c00304040d42d2502d005072060311440881c103600c48103043c00108210711903002170300a98010b14111504207143d18007603001d904036010040a80c80d40368440f0040f415001101c04c10000101c1d6040501c0903000c082da500c41c8003101c8036415083c0d0000700c10207024080e903407010701b01113070021500c51903544e468003030001c01040e00c40c03e04c00d000326060540c0140c03050b049180500081c8480340044c03403841d4200a10b414000c0b4030345d81c25000034030000001c00e81034030880740300e00000c05131040e0901d003142004108200503000b903414008941c8080c00071440203020744d0302c5c0c40b0042d2906951044c2d0641d601c00c8100c4202c0240c01c8511505001140740340580e8068001020f40ea405e00c006500d4407030030003080c0e00541d149500d0401e1a04010440710703076440c25145e0000d0240096101c00000354 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 229760008 1250 229758758 229758779
    0x10c080f030702071701020405010212040b040303050307140a170708070f0c0c09020310031a01180203040203030d1d010e0303010503060408070201050c03131424030601090518071106100519 83
    0x5c500c2c03890140d6020070200010358061103045c041e070503405030540ca02814103a14001c240914000901045800700c00920090301503000c4060200c00030f1041925503200c1c1308014810076004c1030780c014100b0000d0210b084140541c040d10301034000341c0c80e14800d0620405c41210101044801569441441c2500007072418040c801940030b03212851285600781e0a50802d194804809200d005081e00c05400400c1504114050041620001503015960b0303115400040e00d180100ca414425942c5084403884120301d1803100c44007080503101c001d001507521016082d481c0d0200b4070680740c06800082c0000c000a0002000f00303412481410024184510106200e143d80c101814040e50054070600034410800c0c0c2c00d800700d5800c0380440e42c1d5411031161004840341203110500381d070000c4201102041e0070381e0144118102a050240404101e0381e82c01000c491800c005882e844042081002e10058038000070880b50b103e21440c10340c5503001880c00302444500701a02d86012401c503400e400101e40e040a8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 229761258 1250 229760008 229760039
    0x4050a14160e07020606061602040c03020904050907080d020714100c0b0f01060201060b0f07110a0504090807021905011e030f050a0c0f080112060e01020d090f05010605010c080f03070207 82
    0x1c03882c200151406140c081d24181014094500c210024025042141c04601c810f000c180da054034081002440354600350702900409140681c020f040c4070800540080010b0400111074240c01114188011540c0590303c8042c81e005051155401003900c0e0f0607402c00c03005801030200c10f481e00240da070740d007916410210704050312045480300790100104110f603424041c92000d465641003951a041203050855494840c210006250180100456071203584103c01c12006043c051b00901c01f207521072415143d02e40c80907104070710503d0518400c001c2a03842c0c0700b02c02d055400686484203440d0481e003413416446100c2041c4810192681c80402002e0740a0044030b02840c03950b00003080000fa9100d01409000b0402c050404000350280100050080c44482c00c403040e0700000f0000e030805901518501a12810110301c0c1400e040400741d1301005041c90310990043e00a00080203681d41f62801101c059030240c5000d030100d05c061060314401e12601004603000302560048440060f542d000b6031000b40c48 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 229762508 1250 229761258 229761269
    0x903010204030b071815031d0f010902121204060c050106051e100329060c0105070509090f06060a1b0c27020720030a0c27020304050a1416 61
    0x222814001096002204a46141070010002e0740305806d02004181d00c0702c0100f828020152129020042500007200e0801c070007110b4026509a0016211030a01030158940308030b025880302254005c043d02c010540344445415103e1f8a45403620f4403604880002c803501054645542e00d2a00241a0f903070f040035001441c1c1e4405c00c040d44d1442c00010408044d00403504170080c14200b202000b03011010b851004012115280503140c076659000c0800c055000344000254198030704000d10031035a80200290142103c1203070701c5076040e40c545080c512080c100355030054100d00e050003200c4d4000c0c01420702d00460308400400031102c1c0d41907203583c200d0308c0f141d034810805004444403600440c0000d0141c45221103082d4001e501e132001e50b41e0b5041ca0900500864050f003282002a014603940602c04010701035042980c240d01c0c0ba0300d842c1d0401440ca00c01c000c225448440880740030100c890781c000e491081e50004050084410151940481c1e00300c1009400c441740101307400310b6140668600c00358081c05 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 229763758 1250 229762508 229762523
    0x3030702010c1728030b24070b0112060c050a020a060203060402210603060105030a02031c09050916020c09011805060102030c030703110c0612010324060602010b2b060908090301020403 81
    0x4410020305014000508400c003058140b0400e02c00a4503811580c094945a441405101f40d5502050507000d00900e203004041481d0312000141c5540b00109400702c441c0a03042c2001384641310001903549105080c90300c800341c3c00c5002c1c4140455210360141d680700328041c001520340345601c00b104070703000344400385507031003081c10414840242001c0001c1805040181c000705070360070b22600040c0d0b403610400040c2450101049000c00106d01c102298001004054103644050078683c000342c0405100100784001413013a80343c3c250341c601e401300d103ea04a441802c0245201c8484100d10805410000c1620b415031004000700014148104010120f040c0241c0e28000081c5403401c1003401c20b8400c0003158807400d01400900110960150800c0c1140c1e40414030300038943c07818000d48107050300c031480c200d0b4a038a05100040d9545e0190011011400219280d165803660340c051800b20b4605d0743c0303950461f0014524000d00080650b40000c18660082d03035101d0800300e01100007400da80c4079030012038881 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 229765008 1250 229763758 229763797
    0x1120c080708100515070c0504052802030c03150a050a06030204050a050301050c0a1d03060f01090c0833091e090d0c02010c15061e1403030702010c17 66
    0x19600c51151030700702a0202a60b1a0f0300d24210025050398017100e12458554000590741c0208500c4e14900b40007000090400e201500e44880c0e4110702c080c00f0281d0f0180340460001240e1807240500c00c1780d00c00d404180703c2e282140c6441c143c440c3c00110480115070000d07619000030031035503035402409000b4880360f503001d40c0d03550030070080c04a48006036228900030b03810030040c4101d003221902039502040303a6160144030606030301c1c84000c030840d1200d0059018024030080c8054514803002c001d05035111510180440d0b602c000c012200101304a40c1c0b54003445407600040c21038210040d900e49058a001e542c030101140840008103150425640e0428110129100c2d40d1103403842c4802d01e41c408080c00190035040310031031000c1c00a0341c507408002e04000c82800010200004c1c0d516081c044550b0010821100e030b240c1c440340c0c10f41d40c00400c41030b405204000001032600c0b40307000c441c854a803028000d1403c010003a401543c91303821801d0704581203050a0ba8002508000b50094505d0428684901c800da = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 229766258 1250 229765008 229765021
    0x1080705040f060513020c031303030e011b0f060213050415030210051215060f07030903050c03240603010e030a0e0a0906030206070b04031b060b03070e04120503040201120c08 77
    0x225600b80c41e1180c0a141004410001035659040901c4520803005025a80d007865201680c1181314000589055a101c1007000c018140d107e0403482580714280c032052001c1c651070540c4e20141d45000001800d0140c101203000024929802800c0300c902c41a04030705103540c80b140060182e0b1415140d0149101f030541d410000d51030701c07032040c2c1440e5245040651600900d01c100c00c0311030100074024442c07007041090b201d8141c0c039120102d5000c144080758807a00d8043e14a80201055214401030b5018401c210f0f681111b41350110301c81c079004d01d00076690805104103c1c16001451001000154103551b20300100340324403020301c02070000c8a002d6890100d464000e204100004031282c10840c40c0300c1c42d00070140700503128582103c0d140f98008140c40740a981d140750032100e000c4035a070f840701c0d66541c48401004002154100f040d2103030301203040d1101c2c2900c500343c2004e80481120302410100e0800000ca003418050001150070500615004121055000082065034880111007000424003010400c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 229767508 1250 229766258 229766261
    0xa0c1e1e03020405011d0105040306020d02030a0c0203090d0b1003050a0804030317060d0803100302190501030b060a020d0f020f0a0308061002160513140f1e0103030206040b040201170108070504 85
    0x901030140c14214281410440001c0c914483d80000b09668991998180c0742e0382c1c001d1007524000c40c0d111005643c1c0312040744200011350400d03118054100e06140e15428240d001100703072100840040c100c1c45002505481d03103002083c01a011b16201a00000044049803043c05465020784c095800d0a42c0c0f64a03602d0b0040215151702c003031440b108108010702207143c0c0c4455444800641043d2700c642ca0380c4a0b6011003005450a030710080d4010031700c83c010021800c803035410380200c54003600c1c100140083e203014024184030365180000140c025011601d9543d004030010b0100c0c13021441121140d0008010140c54003039404026000310700d20b8130810605107080341c21540c00d00c0300d80c400342021400040400e0010441b501407584201c0143c10103042070009944a0741501d013900300d8001d014103094078151001d0750306030345040124010b103403405102d04c07030005500d040329030590040c0455503440c1c0322004c403400003a2040f0f0400280280003040300003940178450183c41c0d10700103002c14500d007104110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 229768758 1250 229767508 229767557
    0x105190908070228090e0d08060604030210090305060a050609060105070b0a200d050114091509070c020315010503100e060c0705070806090105060108100e0a0c1e 71
    0x501490800c000200024071000580d45425816100c204100307000c1c906500307030340010090320402440c48040024610900350080c00a42c0c400d1800e540c407056101004860464003103c00d00d030020803c000030401828030200304018a82039150603201c15859507038860405e50244c5480300650f888106200080c82d00c0050590081001d0a1503454410f1584d50482e503050f000384a100304c02c0e40c81c0703040562a17403c118001501d58602d401c07107036030740302c1100041d0040c0028022036807100c400c005010b2240c10309181320742c06941120070301d00c4602612800c01110010041c0603204002d058910f131401620100329481c802c400a600a03130081d1304060505240c01c62480c40d028440303040035120301c8120300c0443c60641085102145907520005d505046242c02c00c5540800094810038042100030181075110314050700c02640d40010704e031581c5040c4401d0707003440c0c0a202607880d0102d000c10300314855a440414940c0d51402c02d0002d4105451041c58110326480401007c9200c036a8101c84030582c96540070b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 229770008 1250 229768758 229768801
    0x21501060503040204060b07110409110a031b0801090c0e0402031e010f2009010e030a021210050703020901050901081302100908060a0e060c031b0a03091101020d02060712020405120105 81
    0x140c1008c00307940340d804601482402240c0202e950300c0480050103245444940030f03080107000c06107010740d47d103041311034408145052a190015500302044100043c0240e00985420107100b941e12401c001b13509000441c003030000ca0749803086403001c903841d07294007940c0815000140000196111003051020070b440e802148560300c1a045030110040103001415901c41d00d50030f181245c0d1050303d0340c01191a050340f40304060f60000d041d618210030480001102d4001c42c10210b800e1066460300a8160140e010300d6070405e01185003401556101d51082120503442040c0e140c0c0c1102d4001e560700072644900040d2801e00014620310f500740040301003000b0840d00107003140800c000301e5400a080948900300907010020026001012500700414000c200100c1d41c2d26000107590345041e488087c0c0203080000048441003400c000003501c640c00443c0c0107004080680141113140c0d607a40303003142c0b040400f0703c1c02c4110542c2800042190348904606240300ca41d80f400004d03141c09e00240004c0c0c0c0900c0803541 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 229771258 1250 229770008 229770029
    0x121206030d1d0301020408150711070b0a03051924120f030f02031903060509010603020a0f1202070b0a0609061a0a0c06060e160f0203040b1902150106050304020406 72
    0x10203203050340c0802011003040100c0e06208402c401c02e40020301a01c074540c4860740e24801c11414414207040c1a080034001c2c0415213603071020301941c81c1229100c4d029481a90719003003041c04581c9500c1d0194001540c0302d40d200340d0344102040030120302812a1140c11007008852070310b00c0f03d082c40c1c02c10445004050702c42c04143d90f00c9400302d961080700380c9641d1180102009550750ba9105458020400d450700c07800c202c024500521901540140103100a11405100e607075242c00000b01c0354024401c440310202c240ea20000c42c03140050041d10b80301841c8025610042e801c001160104522260782c80c01081d80c0381d0085966882c0c944030000347d80c02900f0540300c0d410b0b128500280908001c4c04c0740d4a0400c681441d00340c055650422030f0041017036900116503040c81ca420000a0181d0104140a031045916210740034100040b0482c0c1c1d9014a000e1154100820062041c0070b03081d03200a0056200134cc412614091005091200103550a80c4042c010920110038081180740900912002d03040b000700 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 229772508 1250 229771258 229771273
    0x12010305060a090206040b0a020705060c060603150f0a09050c04020408010f05010b090a1203120203090a0311070f12020a091416080c030112050f0f03070c0905040305030412020f12120603 82
    0x14111b07100c0e51064540304003000425410700341c024800ca000412000301010303100e1000800d02e980700c01040702c1180c4240a0110743e4071a40352424a114045d948040a081c0c065a9602c4040000c000e0701006440501c51150080b64650300c0d4002000a030048200100303480b18498031203401d07540180c100c26000ba00520100099483e0044043d0803941043e0580034000514101604e0040070845070399850742c000001c1003025800001c6a000c002c0c400e9640490441442c407206890b41a28001d0b000113000d0101d00300411079024043c101418001000703410340c25610810202181c0380da011820b1421034401c00c00c8400c4640751f00316940021b00341010a103a10b0512401d4011b4401400307003c140b14002545031060110400c02c0c000003c3d0030b10111031011803002c0301190340f07411805c81103c111058030004900745449007d688d02469140d00c130b8605540b107990380c402d205044111200c085120340850781c3c518800070003070000c2240342c01c046203988000b04d40714444c1c00781000b002203002c0e500242 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 229773758 1250 229772508 229772513
    0xa05130e01030f0b10080a0f030810030c090b040f0608060711071413090c080120040b0906030c07050706091d060904140c0a0e0f2401080601090b12010305060a09 71
    0xb40f00c2d10900342e20403c20203c60350f410f09184011401500b02e18007a02c02d0700c00140800502d2240c444d031060003511254029030300c078a00b6800012040c000140b0000e00c1c0c010810071a0716a800820f21100010004180302900b8141c0c0d41c02c4540c103074058001c40c1c0c4400c092226140d0800c0c224901100d038040503003403080c1000c600703031702007100c6000303242c01402d050150b0504690140c1c48400c2e103660051500c20100d81e1a460300d40a0705c4200750f0f00c0d41d040d0604c07400d59603203000da108560494000521a07420b02c1015000c10485800c0100444144001040803034001341052110101500090b00c47c03003407180c10410b00700041c501c1808410014400312080c07040c0740d070b1105541c0e903005030f000d110000041e22401e190707420060305050f91178114036203a201188103d5401075440c0f02c1d095280c0075058680e210500404d41d0301c80061001864400c0501d0f0144070351007924a02d40c040c00604007040300581ea68208641940304005d07000c0501c40a600500030010113102e070700e4009800308400d005400503174 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 229775008 1250 229773758 229773773
    0x60911090f100503072109060f15060e041a03030301240318020904020406080d0c12080f130606210c05030d020d0815030703050a140607080a02070f080a05130e0103 72
    0x500140c081c0f1203404106d400744040c1401c03405200c000e1b00c01c1070041c2d02d110f281280241510300100d504481c140341c90001e61900d10602401220050f5849025691071801444010040f04e0030010504111004040c22034070108025802048144500c1003060b1100f01200c140e040001d07030303020030541003e10480c0c40074040030b40c0c1c90400c2d404984039841511a44005801812940d11240d01400340362058242d442c1c21080d0460b24500070103c80241400e800c03811620380c00220740e05104108264085811005180840200d06200e0700c00003c503551203003500c0c1080c42c6603151180708644204120020040d40e440d4503002000254004c000030140e0b8074000c2c5d1250000781801c0301300240880040d4048600c1029059408001340c00c0c6e035a11a100d00700303282c031910404800d4a00c07020802d5180d41070740000030283e114042c1c4c0d42d52200f0944410101c01c1c00b95125031020b586082c03509034540081958003006144e080307a10340b00d8a6454440d9044940001c0c0c03160300c110005012240104007140c5403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 229776258 1250 229775008 229775011
    0x30b06030f0a14090a03090f0b040b0d09080301030b06040f0501260a0209090309031c050304150f05070e0a060801050d060504020a120615050402030402180703060911090f100503 78
    0x71018a00e40580d51001144001c10412400305030141011043c000d543c2c2c0d0201c4c065060502030360310503654540b10080c618080c5501d21901001c110b0400080110300411005002e4bd501e001001044c80911911004000d42003a00140d40036514401444640c0c9024807500700c0240022805002c1c543c90403091184038003854460b15040e200020305d2440c0460b017404040c5c52158002d1020240e411b1202c109075490304442036980c080d2142444010825001d1250f0102d2400d00b550752524540d269900c180c0c04400040000d41c81030780b18001e8a400100307600846220386004d0342e0358106102c100d8100401d503259903016100740090b000060003952a100c40070740e94a41c20200202e209c1d01c0d00c0c800715003202c816a101c20409010000341004010b1580c1010b2004c1111b032020b1100d0329110700801c0128402510300035845416050240a4003014007282c540c4404d160600041084d0f4907105241614925a0b8412884400040b402450726100c2c80c0d070f139142102034031446105c884148024155200 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 229777508 1250 229776258 229776271
    0x15031b080106270f06140c070b0a091508070315050f210303010602010e010609050f04030311040f0605091203072310111e030702120906210f07030b0603 67
    0x103100d6000040c3c4421402c040d00403805100c140c640d681d03044d00103e80b200f14080c840c0002c1c070b48a249403440190400341c40150100801404110340381141100d1654030441d03800d014889110b4002880515920401d022210541c542c07020601c0c0460001f402c480c0044418491141c40c050144484e4640030500303c0c280d00262102e03040011424140826020390040d403440d1440000004150705506402042006140400902006407158041c4041e110219019a00d00684400050200748039070002105101c40c0440145006c2d1140f040007124141d0790882c002240c0700051210440c227101800082181d4220051030500f0714540d07403442c00161825010004c000020490900d010043c400a8031034140070710100204034005c10b281116130800744034103140c0018401020030591846045034070620542c2c1c0900710703040c100800c0c000710782c106180003600010240910b003581c406503000446290015500d07401c00c0c3c03500c80d1001d004070700c004050304101800c184503180c0b25100c940039a034100c039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 229778758 1250 229777508 229777517
    0x370506180402220b1e0f07020603100801050c07170c0a0201120b040f06030b0603070803090d11030f01021b03071709040209090a02040510141209150115031b080106 72
    0x8850f0640c0110102010301912010743c1100e001072680c4030200107216807545440048004d80c0155041c9500740501805103441000800c0240018580000190f60000024411041c0141c80354080d0b800c6034002ca4042d504001c1c0095542d0a0020041e1020890f0303441c12102490032808181c202e40392209004000c0c144440303404a007a401d05030343c0188a10a2000c0c2041120038600071240f00a8500351000b41c455068400c0030130807070300340841d401c402c0e80d541c60000c0d0b16000040c1d0030701880c0b081603482596952400100c000c01c2e80e4042c841c55131800b40e41d00000d6240e442d240d104220320358131003403981c00030383c42042010001405400315500c00344100070002e0302c40c1040e40c0418007030310400724213650103012a810030203904065400743c0180c070010313101d0140120841d1006d0391540f81c4d81040e44404c3e28240110b00f1a90440c4040580c828502420389031f900480c008004150230003a013041204450800d80b0f554041c1d070503c581c000354011800745d140a000d11000c050005201030003000c0400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 229780008 1250 229778758 229778767
    0x40c060c0206040e070302130501020309030a031110110315100804030c060e0303090f06070c02060403110102030712020106050910121101090b12040b06040b0303041202370506180402 80
    0x550318582035400a144c034180c0c410151420381303c000d000b50301c0340941c0302400c2c03c80c007400b0400e03510000070b5417116040900140200303002510292182049440390180512800104414946a60052401200168031403513124180240e045200680c10300c05a03014405040f481040c0790340c030208142d003040e0141454200c6503a2810040c001c0c140f9141801a41e12000092005c8070030000741d40d40c000c40700714003602c15039220f03400200c1c0c2d04452140d02941c061070a00040c0301103040603a58840300203050041303d1400a55960740100300090400c0440942d6540d001000a4101f03c1d510360351200c003820002024a0800010304520f070300c449400703840381105403d011056405603409801824110351510344580343e054400b40203020450b8112080c109900c041051818240500c2d4811800100030b10704090801681201c4515806c4090307a101400314945031490f40c1c1a014250790080c001d401c0c20402442c0c52607501c0c0c80780d0b26800746000b0441001510305441854282130020356044401580d075 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 229781258 1250 229780008 229780013
    0x9010e040f14061602010e03040603021602180f06100c03030e0c0603090a050c0d0f02010c060207020d06050618060f0f0a03060f06060f030e0304060302070f0501050c0a020f06040c060c 81
    0x5105400414032024031031652486480002d03e20b20a251074a010000042440340c12426519040c1080680b5030061005020070750103500071b00390711030a0340c42c0e543d103054103500001c2e10941e0418146450500384024092012000e0508076881030301580c10340668a488200101980700075540034040603560580f0126002d42444194220304c001041e4a0f1a414002c1c1841e4481c4900c400807642481011a010002c2c00c001c1d804e80c0d010303504908a51901c480c03a800540d202040c845084410075800c100000c01a40d80c00d10751000e0f24041d050015140c42c0c10750034402102e0b4540c0c080d690640440d007c2201c036641d0f9941110032100d00303540381c00c44050031001141c10b10a003904021b001030300706403000c00600400c0d404401211141e41d00d0300484401c0e40d100743c2c02c9030156600084150020403041c40754501075001007040c83c0c8104108056907040b6210b950841e9401d9078200031240c2c000a001210b144d04000c10b010fa040303501c015000a08083d07a41e00c14644891044505201c80400c80e0401d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 229782508 1250 229781258 229781273
    0x7120f020405061c0311010c0e100807090f15090602010b13150503010905010506090f070507061a032b0914040b0402160507030312060b0d20040308040f08010b09010e04 74
    0x41c00c000d013070b4141480443e01d1501811480e2006441c80c00f640c81d00c80d070184203600c00d030f103070201c0c031440074040e11007070300c5400011514000300509190500030f54440000d420030b041c02249004119a422503004c10740b584800425a100c281e02580440e0304115076443c084da5040c10110b191010701703100284090341c03504060246105a0301096055280c20b89080a104040d000284100012529089507035180907441a502005035256000a10280b112000103092540654544161140039036414100c01c400245803004850720055011100d9004208000079045004070b4070582e41040390200341041000c241c00c413000001c26104130f80710300180301292919411154801759504000c003100705a401c0140d9900000d200403000a2409902003080302c04e244203010680e400480e83d149418411055680a8202c1034031040e01c1c562282c8001c9040a0280d00810045100b03001454403103281c025018020b030103076842400c0036410601c500c9903a56411071258150b034410b03010420643c445080020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 229783758 1250 229782508 229782529
    0x19020307050301110403051501030b0703020c01110f1902010c0e040b19080f060a090308130c090c090513020406052512050409150f1202120111070507120f02040506 72
    0x180c2551903c21200d0741004c0160007042501d0241044074100440c000200c1003a100900c8094100000100400c4a80340300e50001e0a05581c83c3c000401c1102c034039a81158681e009500d91114814005040100c900d400200c00d01d101240780000c1113030401c03054001d4148607682000c40d00c030725910214600940d84080910540c400200f0140c04040c1c3c950b440f096a524100c031010a25100d6200065001003240c01420106c684c141d680c07030550746600c0020500e0207a000021140c400342640040359002962091600300d95040c1d5550784150310f01000d101042c83e00039402c904480c0100000c1c080c4030f420000f02d85041d0440199519400746201c020894208501d4000f080810010300d222109640840600140d60502c8001c0000c0704058500b551414680d20452071000316940e0104911580c0c404156038440c000740800b081d01142a80c09400c50341000346100720204c005c5240c4082c8501080860050300068000c49410707c51900c40c0d84403c5100e05009106648900c001030309174980d8000e21 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 229785008 1250 229783758 229783769
    0x1120c08010e0c03100b060d020d0b1816080903070b180106030809100519050903010f0e0609060c07030801050420130303030e030a050304020f031e030403021f0219020307 75
    0x3008004441c0c0300e80d58480080010b0b0340d101740314810106141040e20302c2014005100140003a03e0401c50310000c5010f9009001101c004541c0d43c0d411044a885040049100981c0c03910880b48034942929626600c0303000c9141013040155640811000c510004121070b01e80b90025400211550383c40310007481850700781d44421481d401c0100001c00c10680743c015008194080720a40b05011988800f16024020350030b07401003444d0488408140540030300d000340082c4034064000314070262241c15000943e202244280d01c0c90380440c0230000e00307000c00d0205a8110490200161906205880081804106002700c92280e5580c005070b09204003000c2c40d0241d140072030300d80552140080e181e4000d00313049d10701c000c1d4080303404c10081c040303100d402200703c607c03500942c0c60302821921680c0901c5140380c0c10503902d0b07070103106d0146c2404440c482c281d001d940e0aa4010f0081d50750740c3c11881449400320514102100010021601809141c2c001c10b2034400900006125128a185400001d18058450307021 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 229786258 1250 229785008 229785011
    0x90301091502070b061516030905150c010b010203070b0708090705270105040c0c0f14062401020106031211120412030306150c020108090f03030a0207020f01080f01120c0801 76
    0xd21241c003115000b074a1101d02540c3c4848555031008103200348000c0e0f148440340001810010707a409001e080b1425900d43e4046d10b0052611034071030b80460541e407000038640c1d079016004500c681604070b0074007070540d801c07400f8400340d130400000390f45903400940080c28000501c2044030009051443c20401c400c002c0000074039240000100403c00c4007803040c0003c240d03a024204000100e02420180140849600156a4442c40814a0b1506182c24107505c0781151064400184114115010403045010303444c424049400c44220710522840d03480003569150669060a104201081c060b40400000321001d0500c50801041200c0c00e60604c0000201e440c0411000f00e00800c0c0e12013108014480e240c4291010420585c44080c015840c807142c0b001da20006008001503001544280c000f0b5030003201040c100e40b5450101441d6034155002100c6d04040c00e41e001c0f0b43c0c0c00561905010031a50207034282001807545c245440144200c0f1014001c0c2128001d40c1180c0e2410058000310000040100400 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 229787508 1250 229786258 229786283
    0x904031b110f0102060702060a1104120302010b0915090154110409180503030901050f060d0b0411180c0909160e010311070f03091a07020f0609030109 66
    0x61000d0300881c01014035000b01c0714038484940a50000690078021800380d0001d00141c3d845e4000000940307880355401080e0881404005403005421070b1007846584281c0002c20150114001d0152801c1c0052156400c106071400d142c0c40c5407524070725181541c1a40b040c0a40e0044000968040d21069000d0044948208440f540d207086a450805d01c0e18101a0314528500711a00298019528505d1003246420403c2104000f4034920364040c00580e04050303038503620403076240c9400d0300310740040f10001456515482000300c900280b116480c3c0c005000c5996110035020747d1141145280020300041030f07140b1448000302c19540d1342d5255080b00205e892451103521b01268118069000440f8960158501c140800c800a05200960381d29628541e104010f000c0131a0045001d00444840c0440748141041000003103603d40034a95100d80c0280c0340d4000c220f181c990141c030880d102d154011081031b03081c08680e005039106510010f15203400c0390040d48400210f00000c2c014024100004d110048030007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 229788758 1250 229787508 229787513
    0x3030f06170c0a0602030c06010e0601140403050c04060b040b19031e06030b070503040f030804060609020a030e0d090501021e0106090204030336090c021510030507050a140904031b 79
    0x142600341103025140d5107030844d501c04003130340d07070340906020001d50f900402c00501040c4040002e40354032201c140b400f110024035000565604d940950015240e68222080d0b1072401c0c1414003942d00100b034006103003841d1529265400c5034038056081d01490291070b04001c805030900c66041880c01038466106050301089048040b00105a50f01c421118400f0060008404c40d00801c1070f00d1080340c2000c0304064120141c0d0f0111102e540040003103950075a00c10005c10001d1480c4054009003075a500d0005038891080d4499141103e0000c1000c01c1006481040c0b1903640d021800c815031800d0001000d41040c00352025501400d0341e60054003a16101160000c02c1c164465a880e081e141141d811090114800115207040d000e8081101e001d20700404040080c04401c0d480440703200c91510686000e0400907080d23154440d000d403120842448001014010f02009002c0e4600034842103a00e0140d00e450700381000070030303120700d01e50610440c001d50000e0241800354410040740326585005111444507403 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 229790008 1250 229788758 229788763
    0x1020f0d02010f0f02160803091f0c020c090709181803050919051807030f060b03060a06020705030a0f0f08040e0a1404021f030b060301090203150a1203030f0617 71
    0x3984013402e2101310420628140300311040c10002c50207040c0250700540701c124080d800071708004a0341c03180710785809500c20101c0281980b0030003140d0100c0e1240401710000e25148a0741364091240440c1018031041a403c00588422030301d4001c3c8001d04c0600c0007210707100624070800349181c00c3e510a01100100f580c410010702c0d4006040350082e6000c0d086070007034034000c12180502c1f50031001f40c08045030101141800181e0289151801080088204030408140c4080d82c1c0700351407400010080c422985096180d00028202d1403006041c46842c00c40081c0d0741d07040c00ca038090055a0030915031424020300c0c4209078a52500305040594aa954140c1030710702c4c40c412222007840c03600e49041814180851070016000e65001008030b02c56058125250301c000e003248030000d050581c2c8034040482d50321a40040c5000f0900c4540058591030301c01c82c40322259950810072449002181014030040002824506445030036240010300e03114121640801401d850b0405640707170020080b013090f9841700 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 229791258 1250 229790008 229790021
    0xd0e0909031b031b03070308010e13020d1a0c070b0c0c0304081509100204050121020405040f02090907020114010315060902040803070201091a04050d020f041122030206031501020f0d0201 82
    0x142c040c010944811340c19145e00d9003d50700c1c2c0180042d05c0320b0010040741440c2d1b40e5246e00580c00d250b06082e9200c0c2580081e45c0045030410460b050001d410344803500e060400c02da030ba4448011902c05103889195515500503420040560407204004100280c1c1d0050400665001e4035080c0c048603034a00544404050030300302190700c0d0302035100300d03940301002c22042e000f901c0490340182c581003203011901004030002804101c0d00090154280300014190751180204054010318850060f0740304054404c0c013014260003030518003960b04040d4001c0c208110110503504403a0800043c41004d80d14030002c001400d02c903030040d1004e90021401081000e0088000c6c910640700b600c4026541daa180b83c0d10302840c2e03501401d0550048184002c020700c0c1001040072404510040003014020036210001d0100d039103201810422110201b01804c40129599000500380036450008080603d907900140745440014020f00001c400c460b04586964001c00410340040081c000f42c90460408143c0240200305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 229792508 1250 229791258 229791277
    0x121c0207030c05040603030906030b010e040c2015060105070317041514010f17010207050613200f010309020d050d031b0e0a0501050a09090e0607030e0d0e0909031b03 73
    0x120b4040050329240a2144c0801c886d4917844d0065114a001030a0b80140300c2e0142d528180714050701d6940ca035580783e100780e0454040d45d49514102c0510010740c4070089080400c59502503000c40204075244400b0011a544098240780c9141c1d81c10740c030302e011920b185040000001c0501c04800b0700040007080c4541080442c046070042040c81c11022030341441403002c3c42000b00c040000a800c0c0070903440c0290101c80300e0b84003000035242480c01c0e0b542c585000001c0302c00405da0791010300100d0403ca00c2a2001c00f10852840c0d1000c5403e03c401d001414100001c42d20324141550341c0f03040c0b800c6449400041c820580c100742a29085c5403100703400341c094400d03684802c1e00d00d5200c446524000340524420a2455806860520700c1420000107644c2070384050780881c00d10444c2c1c1c00006008009000b0b21065500385030140115040200300078040c0d4012420a0840c0d42003540d04110341a802807640000c00340441d114885622000c0c5010f0840c41201000d1410700130b0401c00c1c002403800040108101d81 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 229793758 1250 229792508 229792523
    0x11060a02040e2214160f060221250f0f060b04270303110301060e0117010b120c041502030403021903080a030e03041715060a1202121c020703 62
    0x1540e0541c10f0039540c00700f41c0c80c034211210740c0c040c000110304030f88440b80100580034100c0c0c0303089550007000c0c00f5520035a44901140307492042c4c1807000d541e0511540201e640c8500c03100490300101403120400d4020190220341d40300d096404000c3e4001242c84056078541c014210300706040ca24100b200801042400a60740c49007000c000c10801d09092040d881c2c0b40070340c8003080400c00810082108115030706607080e81010744600c00b04041052160086000341300c00e0b01c480606000140000d8516041900c011054501c050700420007a05010120313420313614250400c0050b0f94600340e0318012801035070440c01d4522480c1d442c05503d5600000240196070080b680c06080d0803864400d801d1107146408001c14844090203007130907190207a040080710101c030300107880c2000e8952100040c40311800c0141c0b0015403004143c40d0f049031000c0181a0040702c00d55441d2040c0742002250303072008061580080c060300c96030110702c1c103564040c440c00c080d54403c06400302441c0640d510080d40c80e82640019207026 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 229795008 1250 229793758 229793761
    0x40b03070e150c0d0302070503190206041b0506070303020d0e010f0e010b0619050313020d121101110a05160803010e060127090b19060513060c0209040605060111060a02040e 76
    0x904598190b0340c50788202c100805020b41c00e01310482c082c2d04061002c94151105204030036940319501000031f541d85803a80200110700c0c041c14405405008900792071041590b5480c240200d44903003044070311041d007608015a07100a0403203100c000340b810254502c565441c0c050709040c4032003545c1285603200b402c5002401981303030140800ca0980705489100724174092014904c20200c0c0200e020390750007101c410350703003080c14116000320702e500b00f1031b007400c5921503409072400004a400441c01d1000d4080c080c000c1000040e0390b5411030f21032050b480d04401744407000c00c4070304104091100d44042c0f50b6000c003200d5100d580d1500018904002624128045100003507010808450000079142c1d0003100841d424281d480c041d2820300a10b604c01000d5000a2100048103540e00410340c07210052503183d81d180d40d034040c030009090340202c05400800401c001c05070581e0140c1c0d07070f1145460b0415007003800054039844000040c0c0d400c21100c0c03003199007800b81108100700c4468940c05003003120001110302b0000e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 229796258 1250 229795008 229795039
    0x120901110f0c18010e0112050f15040605070f02150c0d020c0a0203070b0f03040f02280303091e03170c070e010303020606010503040807110f030313172a06040b03070e 73
    0x1214400d0085c08400302001c0c0c0100180f102020118100034018029902c41c1c9548840503810302d100700151090380043e00d0700b8001004001d03c1032942c13105280ca00307080382c810411700081d166143d682c441ca6218114002040814010204491840080290440d07581d078801d0482074907130764410703001d9101c2e0181d071100040f02050b0380112a45101e50106280c130b956500c0e0303100780051141500590708500024031041034000030750100294080004080c06a041c078600d00140840b5060708031000440400b022251521883c41e40042520380c000e50042c0a0b1507000328203241070062000404182c441e46800141004100d084103050301c1c0070364261903195882c940155000c1c4030a8800410965041117100c0c08607119400748a5503100082840040801c0c9100092a5130050030020b0004035000d501000083d0354410300c0c103421036200000d40400302d50202c03887d0180001c81c0c00d1a4000105100c510b803107580740c00403140501040040c4036200c4c1040000100994140c80310310b4012012201b05080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 229797508 1250 229796258 229796299
    0xf06030e03030412170406020702100921140604030f0f0302040b091201090209090c04140408030624030411010e1203030105060f0403020a06050c1009020102120901110f0c 75
    0x1888020300d0001c5140d40c40c0c40d6200d10303046261145290400440c00b00c1c80b020100030f1000c0707a02444c01800d026882c1d058a00400a00d003600c800d55005200c941d000401094608241c81d020741c220415000c1004011810324039030440080500c01c0c070742c6c0910740801007055042074645031480c8190b40d980a5010826405404911440c05105208002030092121034a020941c2081c0c0d9000c40b000840c004090f0381c0803d120000c19181c4034810b030400c4401d0003841c00c1070300c2a4820b28010b5a00e6102d103041c2a1518140e9110241240e030040c039408494100464602c211040c0a140d181245540c0f0300d000d0404c000c0480107049158002200004a00381d103141110194484002c1400a0f40c5580d01c0d0208110b070a90000f40300c00d14200e03041c400040540c2e19880c1040050209071550b590310748400c0c400504202d808207141444c2e40c5484980d90160342c2c00501c552141c1e494400c03e0b55980e050f0300c0144d507070980c00c00902c22284910858500c0151010a00104400c02507a04105280791000f1064 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 229798758 1250 229797508 229797521
    0x7080a1b0906030f0807050c030d0e120c0f04110f030405030a0311030610050903010f09080702010801230f0609370e1902090a080109030917030304060e0708010608070f0603 76
    0x10640f0910131951004204480c0041049902c210200c800b000c6c0e24601280c1040303944e401800219140c1d0202d4129030600e4140c0589811075500986100784040002030700508035580c000b8002d9564104452400f015001111701c0142c2c00214039403a403600b460031654980c07088bc0081d00081c242003000340c00050041c10741c1d0185400811800710310030f07045404c9074a5001001281da266403500c1d03010001090074424000460300a80c000f41d507c1c00d05000241c403048041e808600349000daa000d401d90f003a0041040c2c40048002c45460302d0075914640014901e0040c2807401d5480030005d44549241690100c0308800180c8010200c0020301d80380000084d217100512441941015030000564014000d40215490038510340005040004150100744100601d0f004071041e80e55800510b014560446900b800401034980040002101012001e86a001c0503000038006500d03400c03034480024007803001c44d020b41000d100804c0500c0e034540c0c8407659222948192290780f00b00040110f40c40c4e100b4014007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 229800008 1250 229798758 229798763
    0xf05010b180601120b122a06040b0717030c03071e02030409050618040c0602010b040213090902010309170a11010203060127030c0f140102010b090a020c07080a1b090603 74
    0x240e825079a60001541e1440070074132040241c07552584410715541c2c1d8506041e02c049909801032080f01452945041081c0300307070301d01c03c0340d0f440710340d20b900c2c1070769246400c1f90140c80312000c00940307800c40b51408107640380b540c140f400d08034a000b00c1040b10640c10f074801b4603c1120181d5070361002d001014039000d603c441110301100141c008010a002c0d00e02c90750005a040300000d0410b4030161003c1144100505043d28212a8000b100c4020001c142d824003d011008008480451420110007052003200c41c141c882c0420b1030342c0700d003601c0c002d6a000b584a105015080000c20078840804580031586a11449804000c142d10b5492003038440030503c2900d00c1014182c41c0c040600e4101c0403800200940703661240151700464402100080d4424034040c01080c500700051041d5082052260032407540840e040d04580c50a001c03084665649140240c00090b0320400580d503044480480303060a081d60420806d40c42074840510810180c18400090180c902c829800c0d42503c1c0c10925060300d01a2102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 229801258 1250 229800008 229800049
    0x120b060d02130305101d06060307090b030309030d110706030501030506060607050307060204090c081f06050306010c021810080a050a021e100f02010e0304082107020a030f05010b 78
    0x311010650950042510114911014200d142d503560340030300e413000c1d48000d44022510f6500c0d0300780014403041005000d4003c140500100d14101d40030070781d0341e299845506000b64031280c2c5407401d42c6050003154501c19000e8107407044003040c03080c042c00d02c60a51000340c000e031007000000160710748a441a181680d034840e0140c080e517111002080070300e070860403003506d6a0004004150005505100400041044c4071001c00c02d00026800500300c40d800411107110300c0c1c000d82c40030788104031085c180d800303984450038169241d03112000100c0315035085c03d000940022029010304032100e02d141045121700314002c05105101e0b1648072140e111920f44100401d1035025072811001454098038628280d0038414400d03929144440010385001c0700d0010140109001072005079480360b0a00130002d1031050300009624040c98070303488595902c202c52131030b00d080c0c001324030b03150801c609841114801600100450002c0d07849090001070b5035040301040b1415880c00c0c400070481d04010340c400c1ca4032000c0d00030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 229802508 1250 229801258 229801267
    0x506090c06160b0717040c03030314090a060510170f0c0105130b0304020d170306031203010510200d1809090b06040510090e01020706050906010b072904030f120b06 72
    0x2e41c400000d0b0013803c1d80061007084e42c0404020785920b1715062155020301200003c561031800c01500316800030103078002e6403451600300600850005490010f0f10303030141c0000f0309661a050070303141b280c00c0d030340012450f0b4100d40301d1542540310008071661a070f01d0000c1a0740560308074400540d036034070a001c40440c0c0205031240c10407044170314401666000740040c2825142c4030040e983e18104071240d5000001c464008818448603007800c10070582d550000d4106d062565040c1400648802289809942000500d02c403000040c0548255400007100d0f0b203003194040c0d0302c0d0010291541c1848041e1a03c0546001000502078140d401032000c800d810480c0c9081c10b0300d500d001c1c0409480000d08030038010307100d0b810025101500717101d119540d407050310005071158114a060300540f00094000c0e002a0b114000601c044030220b4203d980260340315040c0744102030407280d03c082c8803d0890b441b08681d05118100014550445808110241540e850342916190142088202d444189425422140600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 229803758 1250 229802508 229802513
    0x11070b09210f0a1a0a090803220c080601031703040b13050102070c1e08010504021804020a0317040302120105090d140f16050f030a02060a15120506090c0616 69
    0x2072448000001d001030b2002540d0741c84825151105a0b40201e61010707407682880d8030548584084c03908103180d80020b1003840c44540f5104045d00001e801080243d04010390080420309824000c800c86038051741c81c110b201d0340c50080b1a2115000d2006865508041900720341c01c0e01c1040441e0f10440d8021640394242e22603c81074000c507440308008488a41d42042404041144041c2e00781c0241854510703048500145141c0e80b556003415440044141c0c1001d05010040c1d45002a220101000300503140d09136484e40009901800c2c6580050b000400c6100f0f00c0804922100051068a0003030b42e8038000e04010ba0109802c949045401c60340c2034100c01600c00e41944a900c100c10040000019982000d0000001c0006980803a105502000c0150707142d0042144c00c0c00b001001c010202c01540c2000c40b030f182c01030340307031a4001d110014095898000d94464108000903501900c031000c007003c800011490010354840341a12103107a01c0c80b17500d428034580c0c40d212040b111810a1200b0203a45040035a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 229805008 1250 229803758 229803799
    0x5090708041a0606071410060512030306040b040908030103030302070515090d0c03030f02040e010503011a03031c1107060c0228030c050c03060702100506062b0e060711070b09 77
    0x242c100f95100708104400380108070510803541c07080d030603100034041004140e40c0c500d00b01c80c040e0380214000c1322441100c0c06030020100a40381d024800303490106e02e2007070400010f001050030300401440503c000c800802890752581c09030601c584074904854000d86605155a071550b8203c071100b04603030151404424840c41005000b401d58401d08006c58071102c0c2075082003e0ba00035412502c1b200c20908010800b600c0d0074080c90205442c3c0e5032001c1650180d4101180d1203101d07228041511300c84141c0d61916190b0240c4c0300f011450f1500c101315846030140e03e41840130b4a24240440014860301e801c3c46070004524050f0040781e1098041400d0340d80040e42c05076003501d05c4c11800e58083c000c0044051240c0c9081c01b915101c1e032161f501805040d18507042c81c4c0708464004d08000d004981c10b0120702051a0b040d20f013070788240358a000484a0b89035080f2400c01910403031702450401c0c0102c00c14045042d810994100c01c80c0b40c004203498106482d503007610348501814402c02d511541c2038140030722111f400b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 229806258 1250 229805008 229805011
    0x312060f03060b0102120d0b0306061905060f0d0603030509010e030d05090127060c03090f05090a020705030d06062312070c23060403170714030c070f06050105090708041a 75
    0x1070054851031210503c0040c1b658010262440d0400d88400310540c691505008140d07002c00c0844001a159686018605081c01030340500f50050350009800c9420190700000d0b0344d070150f000700d0244255500c1c0c2c5001012070304110b00b40340c04901e4143c55441541780c003207080d0105000c00da031002e0030200b502c070045400000306000d40380380c2102d070300070007421000740d00c005406420144c417044a2001c080c0b800910f1440740768080f1000b60070742c2c070051100742e4451b822540c20540068025859074942d00340241503200d503090303a01c40d403841c0a40c0041c0701c1d90808400c50050f00070311051001000c3d1030070026114800c01e0f6655015078003090004400764082c2d0001a00103024600a50001a5503003040342401c4141c03190b00340c1640b04404000402d54040003a400d02c031507481c00e40d0107a0814100c040c2218100c1c1000001205021000404021008040c2e401035078200c0500701080e065400c0c1040280310038080e40d40104001c00000f02d81c24054510b5900480c0c0c0050b02100004000a40101001d030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 229807508 1250 229806258 229806281
    0x9040507050c0a2306010b03010617010602070e0705040914010911040503061f031509230d1d030d0c0c051804151b080f0601180b0d09020303160312060f0306 69
    0x140d84c01e030140400d03010000030b030203000c203880e481d0f80d03d50502038041c02d043c0c002d16000750b403200c2c1d0200500c202c1742d000c030741003040b00c0101c403604000b80c41d010b505482c0f500481d0005006d091030808461140000040800e04032864550200301070007148034070f0912441217000e1550150b000c48c002c07400402c0c1c2c3d00c80304000200340e070001c440318a07140c1c0e44403424204142030718030005403682032090512908140001601c1c2d04508800300c0940c03038a441640b5070413041d44501c180210041aa00262041c104281390704500500313070f9424102401c40600307442c10b8030f401600c00c0307500200d0124190074882c0007901c20703109042d005d0003190b4995072010b002d0101800c840038440d44480c1500c5105120280c4441d03400c41d580c42c0d1018510b840a69034041c5000240340c41c0c1000582d03000481380c0300c14016058141d6000c8034007e5a1601080e0f5484003512082034002e4041c07000143c400b82005581076403c15040c0700355910320424000030180c01c02d581c1d46000346000d450100d0810400240702d540002c250b0170 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 229808758 1250 229807508 229807553
    0xf010b12060310090b0a0e070f0303050306030a06061220010504150201060b030103060b1002010c0e0418020901090501030b0c030403090e130212010c11031908040c170309040507050c0a 81
    0xd01c00003000103444c0101d108442e0301070382038203010100149000b0011051072034001080780501d8811514240045484080c080c050000085803070703034600b40549400a40c205000384803407a40c2d100103d6104440c81d40640f103084034108000d000d0700790100e540050060581da01e80c02e050400d100140c01150a481d60000d41d940d8800000f2001090300185d802580184000aa07440700641400103401641510030110b91400c075580110726049580038190080642d4002441c2502c240099101c1d042810f001e98000508400000c010005030002e034180c80c41050031000b251105990000103000903140240402c02c0100240690540c030310105501450701150140300140300d4010440f40301d040000c030840359446160000d456508807001040140018005510b003200300304c80d8440041c0390354001c60401c0014008503003070107007521025000d0320402d40e0352255200c000035800c2d0b407907211031403c0c0c2c0200e05000001d010103000e44191980c008110002e0015101d1507501e404480350386d051803c5196 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 229810008 1250 229808758 229808773
    0xc030c04030b0c0703140a17060604030807120912080d090c050d11010305090a08090d140607050702150301050d0b070201020c070b0c0114040f0f031e02150f010b120603 74
    0x20304402c0d05640903000400310f81e541e821044c1030081142c200c2070321082e00a4402c000e01c02100358012120841a140c8500750307601798648030b000411511a40e40064928000424443d0900404104511003981c6644516015554400c00b0200440701090013a100e000c0c2404a150750000e550014103000c3e12982403501d01d10344860005c1c060032032044041d11800c04010f01d91748a940c241c4282504102c20800034102c0c00600d40d41e80030248101140c41e4040d90800025900300b000704408020008020000c0d43d4491401000042464000c00030992084560141c10038546095000b01da0507030350083c0c000c20104040341c403209203110010306854115942042504030001040c80014050540b0b03500303065840b82410000c60a480061004043c0c410b107240078840000c803200740342c2071150342c00511038400c010315040581e80602c00c50080c00d508103c1082d60034002c0d50108002d0403c0050b07a00792201600c07000400d00300300307109000c0c0055056003044412503500041c00025030003400101100c1c240e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 229811258 1250 229810008 229810013
    0x21203040203010b0a140102010f0b0a2c0c03040c050a0605122e0f0503070b16061e0504060f0b01080105041a03010c020102031006020109050604062f0913020408060c030c0403 77
    0x20782c850340c4118a011503101d00c2c51601c1d2303428041d0340c030684841e400903c5000188400190803280511030840204480b24200c007160034a04005d485040d08034030710b902c01d0300d46204032403034640c01168202c41c1d81e48101804103407460064a600d040d02d1550307841d14201031422001d0081d5640250202c1103440d040011442c480c841032500752284520560008805803520405600c0303a40c4580000d8400d400220040c00a24929000c4e034182c4120801c11060001241c100b14000300201a44c04010060001802d140c5492a811040c002d5101d004200070700c98803052800c0495940008150020746003c004000030300d0180c000e590005644e001001c0c024210000107401c480d00c1d00b09000246c0d40110030883e01c1c0007007406001c0100f0782400280001c507a580c2c0d40c90340314000244010320702c5550700c20f01d80c00c1e180d00d40e0003114031841e54a058251100d0f441405127042d00404001840f50200ba1300d03c09058815009840440e0174910007000e403502c444c1e0340c0c00e0700e03600002c0c0700c4120061305001c000003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 229812508 1250 229811258 229811269
    0x1d1b030c090406090e07170c01050a11010507021e0a020a030212280611130b0307050f0a08090d030b09010509040f08180910081005090106090e0724021203040203010b 73
    0x1484281300004400c0758a0345000c1c2804595400102c0c6041505a402c0c1c641d0400328a12480700000d1034526139a440301071040c0c41354908000a075a2175840c140c20480ca0540000301c401e076110000c2031000c04456003040195481c1c6540b42d0081d04030619040400050030420340307094000d50200700381c886141140600e8108a1a011000d43e900700207010000c0a0080a10588055050286940785042800242002004003500c03601d41189030000001d10852b1050058440c0340040c010b034140d50300000e2000601e401801da482080a0046c0da02d0303410164004d100b0840350280281048029a1914040115002c0c0c003c00544049003010388490014210000400040d00c0240310b80720b91520100601c41c41004c01020703a0f5146aa1002c00c1c03142c5000000e004440400590b000b081d0303603903003040d881c2c050400ea80c000c2c00c0a83c1003070440f0300c4402c00820404140c4a02424103c1c0e162844901080d000581d200040096001354004440b4144440000d42c1e0082c0082d0001c80e45460101c046403 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 229813758 1250 229812508 229812521
    0x309030a06140c090d0807061107030320041809080f0c0d09140d0f1410020a0e030102070c0b07080903030a1e021c050a030908040f1d1b030c0904 64
    0x1038416a480800c4220000288245504009003405031800c0003c114045180317046081000342c00108042503c40070083c0b20342092881070445404d55444500514010b4084d002c1c0100c1c1c28220f660b500c100000031001c030000d40f400c442e03040c801c1d0500d5180300f031040c0b0000c20410b0307410b441007030080001c502c0c10911440240150707103c08009154030004000000e088072495000b820440c03000000e00707d1503648801e03001f85016004072185154001038648002d08540c0200706643d207016010300f020362a0510b85c0501800d40c2a03448105452605804050803071060440041000320900401d20003162004084c064580c0315440f403e00c0d000d1600c0000b032541d0020005c410020300340705d00070341d8440070614092692101c240001c1040b80c04000d80000010444950705041007004141a8901c03072080d000114501e404c81101584e82d5100c03080e1840b1881c0e0fa0048c8414007201104003000034800c1d090340e80c4591055412450b00250042e2180301d140d0002c2c009084280045c8180c00791a9194892a03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 229815008 1250 229813758 229813763
    0x1e010e0105160f0804080414010e040f0b0102120702091f0909050105060109171513020d0c050a0602070623040b210a02041a090d12050a0206100b07030c050309030a 72
    0x2c0324154001000501c90003004107001c00f048549000d100004203110140d034240c03001c044007542110316840048804109202c0c02d04d60060504201d500303041100d610001c4107001c2a42510640740504180320454424100025001114400041e0020b2032001200000c1c0c96103100300c1c100255a46e2440060761a560008d558a0f503548003030040755a00000d47c030b4010410300000a0030303032114404050b21090f89003500da070030000c0840007580f007440f00d960b00d80107150700500c1c002240c2014140048664030310b00501c1d00814185401107001070000420340120781c4070303990303400403003001c5588000c8541b0318060841c0c0841c0e083c400811641480f0024000c3c0c0c00c00300d8084600a0880201081800c8000d030440458910412041c0b000306071416075140601130b00d2041544c0c40080740c0100d18202070054014088000c00340c00b00400e00d5000000b0700340c0d058075034219410f603120300e00110742c40c0602c1e2041451140c030400203940040d020300402280d0303d0040c42601e0400c0c92141c0030070300304084602c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 229816258 1250 229815008 229815031
    0x30506070314011202130b0604030f060b0d0503072d080a0201270201050310120302030712031406101403070903021f08040b0901060503030d0209211e010e0105 70
    0x400041561510482c0c4908407050080400c0d5490000c0c0650244503d05020f0300400544400d0b80c00030b0403d80003199600005410103584507039074140f52003407c403003040403140c460501000c0401850540080598240c001c40518034010080c0e0b500064252500b45c0b1f9454644807051203004280c1900e0000503c40c003484d4448d5031882480402421940960401814010110044407c0300400381c0d642071220303820b003440c568a8480302c0f00c04e800541e5551017442d4034103000440341d080544c04000b03031400603c120200030240c2c98400c07064003a00c201c3c102c903401949040d400100c69162501b04e40d03603008241d0a19014429441a040c1d24a500482c3d1150104500880070800c5003800300303035a603041b4840280c1c10403d81c14a040201b407100090030280c005516603001c1030455900794445c20040c00e0060459565110303203030118010b500701c9030b24113201e4810001085072195400302141a1110101c01415400200d490180e035280c03002c0242030059035864036903204a040900c185030280f51103462 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 229817508 1250 229816258 229816261
    0x6051009091407020d11030d0f150603090206030601050d0b131b030e0601170f030a17160e061c09080309010c0f05270607060e0c0a030201021e011104030506 69
    0x1910340680724a6820202c0c8146020100401658041400c3c1030710701561500300d03020707000000610303d18010b101c01ca03926645441510b02d4500d11a034000c820320241480c840c0c014030750310f15064007140c80703102c4080c0d040401000040c0c45581302d100201500c3c4a038a400050450b54003001c140600600b00f00c0c400301940c1d56181007100407031794001c3c1c20b0004903880c0501c6440c0031000d2131a25050180302ea102404101c20040781c000740c0074400640600249001c49441d000340041c010305985081080e1840c407524000852014200c6581c100c88011050301d44900d48810031061020907401120035030002d1120f010f6034031407100c060041c9001c050141c015a603ea050036046242100d099080c410f0a10484094800c101a040401d070f581885040c810642a0801c0402c1040d041520850b11a80103000080802c1000125844807407801d840004841454129405200c1210356500010f40035902c81c89000605445810142c5461102e201c004950345400c1301600b02980c105402c101d03103d070844030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 229818758 1250 229817508 229817519
    0x10e06010504150323030307020d120b0102030304030e0406090204060e04110a0801030f03121404050f0d1b08070f0803041101030b09130303140a0c0806040b012106051009 75
    0x1100d0250404440c10094900f080116001c103454502c03004000009031802080c0454070926492800b10b0524180d9507030b894007480c0251210481d006e01400304400c54035070403050402d80300303010808006800840c65a00c55480a5801c8600604aa940140c8600c80801c1031143c84c0082c200920181c0c84940613084d0841c1084203480240300b102e50184818000408203980c88040c15044980050341601c0368001400c0480d20180c1c140c40c07400c529804d1100c1c1041042130b0b040c07507620460140d030642c0c4104500b140704603201c050750380d0030000007105030400040783c0150142a016080c41412810314020165032902c520210102054030018000b20401003407080d600000f01040c00246000c0001c441d041d0002044114040d0000b01041c52080d0711204050290b4031660b00c0b0f8506d00307028500ca01d4120304c000040c2420003440ea00203075405c404140c035400e040c0034002020038161980c2c0d0010b0040c8005280001c0a0096140341a84440b00000c6e2074a0703940003504141c400d0b55603010840c0c00c12 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 229820008 1250 229818758 229818763
    0x4030b0622060e13020d2901030b04032c040b0109080a0b190504030906050a020a0b010b04150203030108070b07050a060f0204230312161a01150f020a110109030b09010e 74
    0x4202030305900300c3d4841c0c2c0300103944503001e10002540c08905a0245161152000c090300c7c84554820740407245140040244510124403611a41c406c6e030fa840d103c00d030401d480d626988a80b4a907040000380c0403144a2132072600750020010034006150100c40c4980c0c0b071508034a00300209a0a540004214092000030805440d00a11203081c0e21010b112606141e83d004001386002e02c0383c40f08001c001324003091440c2c42440061405034011003000782d5540c6034020030200343e100388600c40194030304000d518055800803041c0c078101c580030000361000070701e4610500e80700c0e0b018038800c46c2c89004a040000001b40c032842480500c04003064016220303810001407030b0140410807400d04180c1084195010300b80d0b80041d040b1030303954200159031b4559040c00f1680c918012200401805030310061000b140079003804010504888050b40391132003e01c4c1400c4152a03098500c141d050058101114002c041508042c0c106400030044c03410b00d800a90702e840710f9800d840182d60710300c0b50b030b51122040c0d109240e04 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 229821258 1250 229820008 229820011
    0xc060b0d080f0406080702030708041203030b0310060e060102010e06010e0406090503120a140603031813090807022b14150a0b13020a0e040510091e1a0604030b0622060e 74
    0xca000445c035224498940d072b40203003d070344504072842424040000c2014442c3d0800b09905002038100d500ba14140d9081c00d004d02414003900d421810a074001545940c4140503d5a52440200191003164200682c1c2003c8910081c0107030f4050b5154144c600003d10204001d01c2500b4031900c2654803810140e800e11305584114140f00c910310b101006009040c1d40101c11640303903c020312904840c6444000200b41c03244141101514440d00d00300844060010606c02020342d40c1c030840c1e004404001d02c5d807880a080403160b62300a0f2031480341c2e20250010f420000f4a20180c1140021a0380c0d04a81e042e82018883c0c003104e202d155541c4071102c90f251030a100e83d2001d0442d520400660501d40100801000c250843c581d56204a072900c0100391078000440420b005440e020805100c1c081c64440001511140001080c4400346840407003840b84003001148820890020940c0349081e145842d9a45031400c06800b65034003150907250301d100c448124a050744c4a0b0340d40c0c68085a410314207010301c81c202c00c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 229822508 1250 229821258 229821271
    0x6040b250c140405040b07050d110418050a0608030406110106030b04240605030c01050d0b210607020a030806090a1e06061205060a06080c0706060f0e06030d0c060b0d080f040608 78
    0x130305040c4000038079090f030f116601a11500c0c02c0382d221400d4800f00800340481154200c400c401c00100030070741c1070110a0882d04800381450501051711804501d0045800d984214078151308180801c0c4a0780e481402c000345044c0300310b030010428544a031500e640c00d11040d941210311140e074036003030242d4070318801c44203104400074401003040034501404241c4a0a40da61640c2c108500040c1a00000c0c1c140d031b12070301c15440b000d041001c1402e007003800f044040c10402011901846440c0000345c1c020300c006103091925a0542d100c080300e45410003404001b20000d0201d40d0300a48075000d1884030300e100b0130084e48804c412800881d00502d4010094224000c4001d6045803d06000801c00c80b502d0f070300e04020844444d845c000d4520340e07801244a00078059844000d00e41810180002400303888820000161224040884603940b03070300301055a284a10300c04000800c000d41d9008002c14036a0b8401c0441078009812581410515681c0d010f490f4001003020005070340c0450284200c0d540064200c2d8000d9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 229823758 1250 229822508 229822511
    0x7150606031a04020c0703150f050a0501081e0a02010302161e020a14091b09060a0203040f09140f040c1a03011a0301030206031b0405151c0b06040b250c1404 69
    0x24012a000b03841300c0080c0030103420766115505680088c0b4003a84841b2554141000400403170a03c2c0c0e0060005e0013007031007200001d100d079090250f604001c036000b24443c4100f0030000c0800041990040d00650001442080c01c00e5140c809040031468030404070000400050984001d1580c510420030f20b1005900311050031884d02c0b6600302035441e18114980c1240032131740c00030f03040c64850f03800410501c030f1640029003220b03010489000403a000405441901c0fa1940703400540358031203250400310340d2032648081035481600c002c2001e00d405415a0364006000d44110b2012a88400d5584048441d043d02100d0624001004200304030785030444c03080c4500b10002172840c552442e0005039140c08050011143c08803910091907426160000b240c00400d806451003030128840d610a81c210303003000d08505007003071040e040d54001c1c030103a10541e03200260041c1418202400c0514550580c0c001c00c82032101d10740b00545081001d0b40381c2009101c62032090010b4000f16050002c80c0710000d00904a0074000d5 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 229825008 1250 229823758 229823767
    0x822020604180f020306061803101803090801051302010f350609010608060909011407080a0b0409150c120906091a06011b0503190908011a0904060207150606031a0402 73
    0x180e86000c11110300700001a5120460001000000d080501d08844c4440309071030007145180042f8003001001c0c003c0e010317803602c41d030540e42c4070005401d8800c2103c160084c0380215038604015030242c1010040840e082c641800300c0d00c042440500402c0c00d14045000e8000d003c800035603080340c6c49030040c0d031004003070f00e005030706500d4140045c007041c0d009000244070340c84003000121154003d5010b805070b0004000c0103042c5041030b4102412a68054a0340100e442c281b55150710242440e00464034116070000e12002c2c419086a6141d00510500a100d000c01454103c4607189080707034080c0c400c60794007403080041c03c2002803909403818140d5142c81c030340384d40310441081030750707038014840c64501d0712050501392400316980740c440e003144120284585840310840340d5060440c0c0c0056070f0010340ba0a140208020a0301000d082c81306400c0103412039011020314005000070ba0143c000d0164903104d1101c012400d16000303103140a8034020303009075000994030b01c5c07510002c18031550905200c040c103650452a0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 229826258 1250 229825008 229825021
    0x105030d0c0f0303021e0304231605010809010f0608160f03080304020f06040b07030305060312070206040b36040513081204080c03070308040c0e01060822020604180f0203 75
    0xc0802c14040507051542c04107a8207100500d088107040c4080c0c1c1070802a50b289098a49001c5642c1400303058034448450103205c0300707185400503041403528040003400011a1400004441940e40103240c181c46540710003420050f458a4002c51001d000f40300c000c1c0c82803040c080c210804450040e84840e039480d07a0074400304082216001204c1d04240c0581e081d080d0b045200c40459034512559100c82000b18001407202c00341503240e402503001d000100c099868240c26290014964001c40c10042e621010800080000d113210380014050000c807020000c1d54524801080d55004c11713290b0441d00201c05594608806152074841c00390702c070324004030451503003519813191545401010941c4030581d01400108007800301c5a170541e01842143c408482d5141074601d0010001902903604403048082000d01041c9001c0090940781a10030540d42d02d0b800341c0d101c00c0a650300d440c07204050640b10460b0300356440540c503000c004102900003079a503000d503032102401884c102c8484041180c07074070f48180140542c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 229827508 1250 229826258 229826273
    0x21806011e05120f060a08032106040e07030c0801050601050307140c0109060f02040626130c08031201050906031204060f050c060f06031e0c0105210c030105030d0c 72
    0x441c504038000755031600e8003100c0240d03254403650004944040909080003401d0ba0342c00511480f0784000d40c0e00d00c480c55501c0c4101940c078040c0044003082902d041c00c503204000c0901003000d0748078400502c00308022455200b5141413410760740007603c185801810a02c080b440c24060300b5080355082c40c1035803451610683c000c0c056088521072110341d4000194014400c1c800b50001d6807200d4200404100c15034008503214001d40c01481007a001c1101c0380c1072514030f44c44038000400c44007000308031050541d40701c0440e9140380c0464403049640c1e107040c0c0c01c00f29049104101800e00f540e101802152554105010014580e0000748594400d034024070080301c8a502c0c0105031001c4984604009640c00c0390400309690301e001d4595202038a108030420044014039040d581340c0076403405e5013581c210071014211000031400780704208090b0b5000c06070281c0c0a52046c1c0007003c04074140700c0c0d803c2040d204800b040f150210141d40c5ca403001c000200040c0706a24061004a00c07a90317039800c020301040300350790300c191 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 229828758 1250 229827508 229827527
    0xc210708180d0806130212071805010207030b06060924130b03040201020a061d030d0917040b0909060418050106080706051c0c05040302060d2406050712270302180601 73
    0x90142241034014031840405d5010785401540c2400740503030750726081d640240030317001d0140d602c0020ba0301480c0001d040d500114201c0c0a480e000030f00100d650780e54005000d41c82d03004d6054a84c000b8091300d020642c601c003e405603030321001034440c0300e582c515422401d905482019040700c107208004106110044c0c2e00050450417680e800403010503604240307510034051442c044400707a101c0c000024850b0344581b0507403140120500c64440b601404921541003040c0e03000790700448002c0da004002290b910f140c41c05907554000801000440d042000d809a564a000784810072507450b91108000e1043c134030280f1000300070f01401d01c2c0c80c5090255104d8a80d001c1111411034004240c3e441d41d101059074494011580a1500541410360b6500f1008200008144280d499140301e940101442d1140c00b0003501941190380580e985400d03c4a983c95500c13a40e40d62808910a01c40283d13041c4005071200b81c1040350340074011101480e90392070340c01404040d24130080114115a082c0c401c00507103070f8000488a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 229830008 1250 229828758 229828771
    0x40803090409051e0f0d03020f0a14040b0f1803120a030e031603120b01031b1b050706020c0103140106020a03050d1509022a060c210708180d08 63
    0x803910070b403907040c1181800407140d9420490102c500c04505495000540c98000d4074040d0121901e180500304102c04901505204140c5150104a5544050300c20313005c01c090424050052860107598005640030380d4041071511100d01c4010030030030500e45400c0550240d04405402074014039520900e00b1045c0d1064405070424580d4885840b08008400c0060b01e40d0703510040c0300103000c80a14200a0030582444035800007840c241700314200d00794481d0250142c0103d40c11100a000842c40e02d080d00c6100076074129552003940c10080d1004a4010003080d8000d02441c1c014040044c6100c0004003a82c0380003003001200700940004016440c2d00051408000d1740501d00380b40c1b900d403c00700000213855521504007480c4007108000c11140090b80c010400c8100960600d1a5038004510181884185011004103a0000c10000e4a41014a00103045403510710b00078203c0043c1480d42020000e20503106c0d6800500035078100100012640082568121500c0050942c1454042c0042c2440c00c02800c9 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 229831258 1250 229830008 229830011
    0x6080109090f02061b0706020f0a0b0a0b0d0b010602011d030a030207030216030614010e0709060e01021f050a060b160210032a14130306090c1206050115050408030904 73
    0x380710a000b1055801c140c0c05600500b800c0c0d0b81c0451400f4100503000e9499100000e00640c0000034070a03000003000801d1101c080040c0482540a40b1144841e202c010725070b512541e10342010030043e540303000c3d43e1048503109980c0003a16504000d402400c540c0e401d420180c00d9002c54a103015000000002e840c880d950710324016030b454520349001c0f82007076808101c2c000d959912980120800c00a43c006e0355440380c01000190b1183c0e0307900132000d20648103983d002c01180001900380b0216100d800d010030b0801040c012540800511042d21400c020342c0c18501384505e40d41c07000d011906a046c043e10005108172005582040c0b19034000001c08103e01310000d00c1045401210490030b4001d811031001c01030201c9408000d0100d030207821881044c02c504807400204c030401f16401060215060b1840c886942d41c00110380c80c11a83d818005168040d8140d4000c1044031000070958040340403035011920031300000c115549081c41e501c4c0c8010341000c041d4180041071000303208a4030000141c400c0501d080342c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 229832508 1250 229831258 229831271
    0xc050d0c05150a090b01090e0c0d150c11031b0c0f01050d150f0803070b060901081b0406080d0f030f02190804020a09020a030e1612030809010609090c05010e030706080109 75
    0x3c01c00003040e49000003003401400030300000b550b007010380c0b013500760b4541c010648500580c1c01c0100300c3c000014840003401c202840c8100d4408980c240d0220203000440d01b40002d04001c0308181920311780007140301c069602d0018015581c400c10a004c01c00240e001038034001c0030121b0040010b04580202c03016a00d015a8030700c126412502c051204c0340051091390f03256403405403135a004549a43c00b40304c047d941030301d149000c910b05042c01c000003070407601140c000e8a55513014840803a11084030300e2003158007a0f281e40020501c11014480350601102c0b039140e081c1c1450000c0006400c0c2d40c2c4144408860600c140310f1034801c03c00c00070f480240039015182c0f04005613594400600117079003540010202034400310700400030343d0701035108801002c1030004030340c01c16004404202c42c0905038010040c0c8030100061942c000380c090b8080603001600745001082464079080d04c6012030359281e50030380c0c4409001c24104407a58010320528100b410640182210908115010307241400c18452208a13650f202c0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 229833758 1250 229832508 229832521
    0x12f070c21020a060503040209070804080a0c0f0c14010f0f2f0a05071805010f051c050d0e090106050324030c040203010f080616170402041b0c050d0c0515 68
    0x1401c80a42a0b0041c1500112034803040010700e1904215400c03801401d01d48042040c04c2c0c003c8105130b00c103030703032102650b450f010038480c00701c44d4603600701401c54408600d640390b00001500003001d507029201c485415200100c007074000606900c002004141400601c1141c102000c0d4420b21001c4031013031040c14241c8100282408502403612101c48241a024001d080002c00c0000b0174424115580c3c4007400c2c0d190808408800d04883c800e104403c011070703c1d00380c100014100604807541000050038540040d000a0b00c1e1141000020351916000032104410803d46240034004a80501518a0b04500b50328181c0c52090000310b071010850344440c0c00c6000300e00c45540420440102c0d0802500554481d40c0d80e01078920340600c6070140403040e009410000345060314841044001180c01d43d10ba084101400c00421204403003e801a80c105480d60707009500000b80c0c5000d140f0741105030b031350310005035541c0c103055060503070303020041040000c01110000440c50002d40028045085410f000c81901c1d403c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 229835008 1250 229833758 229833809
    0xd05060d0b0105011d0303030411041b021b0a0302030709051e0403021e0f0d0903060c0302090a0603200c0d090e06150f121003140a0213020904060305012f070c 70
    0x4154aa0706d031100204100401c03200080781c0e91a464207440a04c0381941070060a406550703130f51040c1e00142c0c000701070982800103c1d101b50034100030150042050a44940209080c690b00350012500c1e181c60303000703000380b540c502c07034002102c3c01c2c03407000408540c10150741c000e4a8013007216142c080079804104540c1228018800d085064002401715900341b035030498080c10401851109442103403a008050003031074002e00031201003010050480f9a0141416070540c01003842a49003501089001c013030704074213400100144900481c0714000d10400010aa00401c10101034200420012550007408510380368000c81000300780a840c2d95a440e410700c030f40000590b0040702c0c0480c2181c41c0800030700c0170302510240c1c0c080569002d034142031861040303c0c0003580c1e10f04401d40001d4100024095800700040aa80a0f204048004001003640e40d44c9131500307829500c00713003c04c0901c0c00302c2501443c1030740640740d04e40d5180142120020305000c25a03c9500c0c180d021403041c48070080c48141e400b0700c040f586 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 229836258 1250 229835008 229835057
    0x120906011a2a071412070803030c0f070c0e0103060b120c061606060303090302031c0203090402070317101508060f040e0a050712060501170a1704030609080d05060d0b010501 76
    0x82c00e086842c01559010b88003605070400c50034034054212618451040d00c000b081e10b0003a521101d0041d840d40d10340e116000700d01d032303c89143c500c10094203000b00000030700c0740d240b00340060981000b00201365045d8204201282c100e02c2e4141d1240e500d0361203000000602061001c400b8404a031215115140d42c0c5425200c01d440c00d400800f070340e2600307102004054005101e4400c1e64001da08546007451000085005403458515480150b841844000c42529017134004201c0a032091070500c1402c044a00b070094080020f54110100798031805041c05400d0450a58181c1d801c0946800c00f55400d01c00c0206015500d01c0d5201d5014544410391071254006c00c101d41140f603503019088a01aa980785c9209400200384002201c4003404e0900000701c151030084100b030400e80344d50240803640503d94400d0601d000f0100303213115401c1d0500c0004003040306c0317100b408151750103051985c1c0c0d05d100d02c04818040b07071401041700f4402e00e5104d07070b01c101169601c4180782c1540c1c8282040c2400004003050100381840 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 229837508 1250 229836258 229836337
    0x9020a060e130e071e0e060907050d0c08150301060e0103080f0405060d050a060f0305060f1911090a0501080f0a0902030c12010902030d050f220308120906011a 70
    0x303102c6030b0501c1d0140014403000f10752a80c5512021200805c0c0c003c00c40791070f00e10400100e145620040398140ca808840d250700280c0c030741401d918210307401c00300d0000d0703404440c021804600603000308480c0c40c3c170000b612562410210020404a81441d0807031801d2031040c007003d8001c0382d000c0703200641100e0000443d030140800401468440308052002c2002d44811500d8195090034098000b03000f114004440c03081d00d610a0141c461073b542c4502c2c00c0520480100301d0741004400219403d01c114013849801d00b803107206241c207696510260140403214203a40d000f0b50400c03007e241044002d031411a52240c2215181c980410303d04020300000e03140c2100722540300c0e802480d45404485a45056101650f00c500c00d800b5166040c1500c0b00503156805000e6078203011007010821500c4803114010141403402c072a901130b43c2025269103c1c1041600b14801250304007400e182440f11f0381008101860040c040444d000c1c00031006800c3c1035416000310b84220031034407440106564024110441103503400d4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 229838758 1250 229837508 229837511
    0xa1506090f0611030c03220b0f0712170108030903011b0207060507111c0b0a0e03030a090606031a0405061803042c0f100803070b0f1e09030301050901080109020a060e13 74
    0x80141c40b4140380d610f0501140031707c1349621300009411500100381c1710050800c8115500f04007064481003515610030b2a000200004200c59014215400c1c002034043c1000b0304c01181c0ba024080245400c450107540340c6280c81181c89280340060b40e001a8040503034120380f80864450301d8600e0019006100d64106a80c02800f80c8800d43d1f0440501304a0100b42c2e0003070481c81c040e900c41c1080f42048495084910a0759041000012005030f81030b040001020f2103400700189180c6d507070f20388050744000d20816103e0300c250704c03043c001441002c008d881c0c0c0001480044201070f0b06040589035581c4168480c641c0c51009500c003820301b81108400c041505031104580e01ca0520340002c100510407000c540613081e0719540e403804100b8000000a48041d17070380c84040d8108039140c40388080741c0c0d4070008000c5280e01d542036410300c20340e62038480050300904500c8019502c950602c0d04001464505800581c610381c0340250400140c2c2d502040c1004031a100e00341191620709810209a400086064081c840f0f07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 229840008 1250 229838758 229838767
    0x30a08130314060717090c190b0309010b030c03070e0f040c050618030d23030c0c1b090c0715050a0b0301060b0d050c0c060c09010c0b0a1506090f0611030c03 69
    0x42d40803038441c0c400c070300542d1381c002071014009212480c3c03501030b070300f4490079030010a030001103040c80d005010030000307440328041100b0b03590b03203610f5250783c4101c80c10301d006e075187d442d601c0340b03130604011000d000d031811005862003178103040941d2243d24005111414005e4844046000e001c951000d0301c0180401402f0b41c0c0e1f5509903500043d00510305e14041c140640305001403900014440e10208154100001968031041c060500112450704094400404054200100208058100070000035070b07240d815480c01400c000c10401c000c42d000204140da510408000800001e000c900d40c1c40a410740c0503000082d15100d0302a031301e0080900f000c415030150f1800c3e4004c81c10b6920403001d4009801c82000512041d074aa001e401c0070707030044550000c03140d444000424600e00c01c00003d030221042c180b40c86144401c5584460030804410745450450f99501e50b0099099105a0700c01e00c0900194101110b11500e410481c9200e18004d02c074400c01c20210850b801c80c2034006000302c1d00d00684010859854 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 229841258 1250 229840008 229840043
    0x40b060616030e011805100c050f0d0c0507050d111002070302030d02100515150c030f18010e0409051c0c080301092405031b0613090e010b0105030402030a081303 71
    0x81d84400f840d0b540401d100c06280d0b00903240c0c111400054403809402030383c444400e42801e07282c200c205034007112540102079900d49800800c00000078104815a2021b03035108071070a2a9007404040e40100d4041c000d108050404101c0041a800006905072111440501900b000b00c1c01c200b880c1c0c0000b0361600884115100070380d40056003001c01e5015490810180d00c854480740f0713890400b060956004281104a5018007100402405d01a10180180c0385016a16001a49142c1c00048840d8005181c00d000582c030b56030103203240480c64003d4a0812040000c1d40b9045e0380c481012181c442c2903000360000030703515440380c1500805030360300c582c0d0035440f9611840048051300314110f50700c607011100303014500b40b01900c0c04d2000c201c0380080c0c041d1200c990790501000308404808044c0b50480300030825180300d00f86441143d4002d0500c030340300285011810f184582500c5c000103a003810443c0602c103002c0541d1300400c885101c25440141c40d907490818210980140b40a41e00c098900881c0c03104d104007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 229842508 1250 229841258 229841267
    0x308090d06152408040b0f040309090c0306030605070206131202010204030b090d0320030106080c160506040b0a02090f061e07030c050c011115040215041806051008040b06061603 78
    0x4108039400d0441003d60b4088a084a2554040b0340180c0310507031200104201d42c0300d0303501598200b0f01034905254510b8440034000180c621000b9072500123551103004005200c601c1c89040e401007031520203084c0608201c0810100b2a80e40c01001d82140944a501e0084900035411980110b0340813000f12136904d0880034480d202e8644920460205e030420500c8510507045c41d00501c4950b81d900211400c5074242031003120700304030040c103020041004011241104910420181d2010b01c21402800c446c80c0502d08150781c00c00260034285200d00522441c91240e84e10301c48020110703425034900e9201c0b0503020801d08009201ca800801d0b04c200003a80400741503001000301c0d2034500a1f42120410b4141d00011207400309038201141c2550404640d01500e09071141c100e540146c00181401d8089610b520b041c6020380c800d501074801c13050145104190f80c40355010b401c00603c07007103400002401c0f803294040c00496005000800c00a080400540ca035941c003000d03145403001032010a111b03400e85180181 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 229843758 1250 229842508 229842539
    0x3030e03010606030b0306040b07090e0a2f18030a060501080d0801151d0109051003021e0705060c071707030806030f0a120c08120c0714070308090d0615 67
    0xd00a5003090342c0810780d14002d0007113045080014000704020b41c0c4d0b80e115041010800341c0058208070f440c01001420070740201d116400b80404080c001046007038001d07141c420703010701c2404030400032a116100710400600e8042d1442e0f15410341004081d85210070009081050741c035030051401c0e00e8000007161800300040c00841281c02a15203d100d641c030748480031b0100040e13100040c0022840a41c1211002120a910600705410705294048a481d40e00042c4040003007040f441c0006e5002c18064060006520082030300003000800d217180054079212503403902c900800416103581c0c00140d03030040040100304403051803e42101140c403183f06181c0148400801e592442c4203200b40d1034100d0020b01e000c2244851142e0280042403410300e05101a226a5948a016100203400b40080f00303042c0d961401c2c55104803400340b01c3c1c1d03584420a2130040054055070049070b030070b035000020900008140c00115440c01030110b400165080540c9440030182418a54150071001c0070740780060005003014000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 229845008 1250 229843758 229843787
    0x3270305060709240c02030d11070f1511030427060e09060f15030115150906050a030213120606030308180705040f06080a05060106200307030f03060503070303 70
    0x100e5841d21582003c0b60962190300030b410a548442110307080c03444102c0840501400541040520640103030002402c02c8042d46600c40451a004210004000d0900840d4003401030b4440f44840b19007880e00107200c02a10000e1a81408805540020024000c10030395000745076622540c0b0044a1030381c6c402000d07240841d4181801c070705290000c15650742440d071181c031440d101c0340241900e41e12608500e00e010005005e09041d00c2050343e042060340c50078003070683c3c40d00501c6000d08a5500d030100412074074440b02c0544c000c005c460381051040a03406421240440c109160141c1c40318004840c0841d18011984034078820915000038074100125134010390200d0340a40c452407801d42e1446c614070642c1403e20902665500240020f0246144c80e902107104035180c1c40c000a0820f8480d40e24034501440d001e0203640b9a0302c104010401c040c0e105c1400c080780c02c62003591004602842958981d40d0003074005c003e05000c4801015542a4070030391000c4003c142c000c0403103a4259172814058050810510709 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 229846258 1250 229845008 229845013
    0x20703080c0a1d010509060c0303010305070501031514060d0905010e0d1b08030a0b03061312030b010918140a0e07090e03090d08090406091d0a02060406030903270305 73
    0x40026050005440307a00d82c198540785140c103122415540350050340710045040c40f4051010f80700300c1c1c807104080d182e200705003801566030f541141411407a040d81a0700c0b2a04160628010b9041e40d51240340800880b9180000c07098000b10241c005070b4a40200318a42e014246041d8030704051000540000740907482d1901130741c50071100088100c520144212601e0039686164440c140003c0610700116030103080301c100020005940000a42010025030b02c1196100c0044881001d2240381e804144060300641030400940600c103002034501d100c1032084201e08007000c3d8000c885504181c10900c01c0301452a8050080c3c43c040344190001c2046d05542d410030300c00c5400119030380344244074080080869800031420f0980c03101c00c0080243c0e0140c4112102c6c141031082041c039885900032078019000c90700020928442c005003a6500e010420210312003584143c030004c0140e204c0d00e044074243c48030341c6000308054180f42015117800110300c406040310890b202e003840018600114a00649106405 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 229847508 1250 229846258 229846261
    0x140105122508150d0206030117030d0903050712030b1e04090606060807090909051b030703060c0804030e0d03090e0c1e300a0903030b0607201002030d020a0306081002070308 76
    0x84c03110640240d403000350081c400b000140003100c0301072070003000084140c040b03071302d40004080d07030310309840c94000c0c21008582c000c1505801c004094070b24401c03025640c6001c08c106245c0381300180d2804851258100e011011103072131070b1181c8580d001400c0b00340e0040c1040c07090355662000207180d04002c46034140040d03090400451078401902404642a4026004007226805c0e002800c03070044000e07445992610039008004002629070003240c4242d82e00b40c64041d010b01e03060401401821a01036070724401d2825001d00c40000c1d0b08807804400b81d4003580c0c14402240c2d10032240343e21910881e843d02c01d00c0e0402100010003400104001c104000f0410780b40f02040329500f4110704000d441032a2850424507031030024420448135401140300d14020710b00891202c000170049200ca900c80c94003900c0250358003180303426043d860b40d020b40d138803a07040c0e07030841020740202002500c0c3c0c0980d41001110a40002c1c0207035103170380310b03806c400d001c3d11510050f00c510071400c401e0344009510140044012414440 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 229848758 1250 229847508 229847551
    0xa050d2406020a030c060c0e130b0901051206040f02120109080418150315060324110c0304030602092b030201140c040501081009020c0c010306140105122508 69
    0x6842076800b54541c540e602407802aa80d00760103085122a150200140c00d180c8c2041942e540c03403101c0e241a60b24200140c158802d8051040e0500140c01c9503018041c0030090103200702c4002485a80142c1040c416250361410b4030005079441e5412040b04021344c01c024080040c000c0d114003c0003226048031010300d10100420801c001d5074002080b1028541700c0203000c01c04a20702c04542d4030045095180001c80035160780e03868003c0106000346030b20203032410b420200b660140b4410b45270b5000b400d1309000e06200e80f040c5000d1703892041d408000e00c0d05402080740d140e5900c51038100740d4485d844402c207a81542c1134822110a002c505102940190309140b246450310b42000b810fa4012502c501c441d520340303810013005503000c0c80040e09074101c0441041d00011051018070190848080342400b030040b030b1510900040503680150480000000a05540015683c20004071164000140c030244825504d06039803070380c07004140d18043c0072440290010585103901100d0b4510400301c040c617050f4a4a03c21 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 229850008 1250 229848758 229848763
    0x307090f080d120e06070807030906060e1f14040902040f0c05032d06040b0f03010e0c1503090601052404060302041703160602030a110d060602060105010503130201050a050d240602 79
    0x1ca440b5030030707040100450107047c42040210344c00552400e0114141310b83d555400215841540801010f40803003007400f610030505911120006540041e082100d0b003400e11105075012450242c610a540d0740c0020011901c55411000245040481c00c000300d01c51a503000c1c04551013200c1040d0301c8030744001141c440760102c82c404d4062101155012803c1d90741c16051100801c03452507182c0d03101c8076030002428982e509002c2c1c0c481c3c0b840240c0140222420b02d60030b00100c0d10743c0c0341c1d603200503560900c01c10114002c00030b4424110340302182c00564040b5400340d07810100c618218821b030700c024001030106405406030001c10071950442030448610031040c81c4580c032809480b002003003c00d40d180801c4081070f1603802a41c0c00c03103100035000a99020a03030040c0200c2e0710070190800e100382c40304000c101d5036405121181c0103140a0901a00c1c514040105643d000b01c0004002e050110204043c94802d01c03400698001c002c0a0000704213103065a0211000000315081032a1041002800403400d02d101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 229851258 1250 229850008 229850021
    0x80301050f010f08011403070b1b12120109180501020a030b0108100e041b0b0f092b060b030f0706030e060a05070c0305070510020a050c100b01050904180204050705030103170307050a050307090f080d12 88
    0x1d1007200cc9169007001a244083c1112207810182ca80354001c01002140b030178401040e00010f01c0c1c4002517044510b80015103000e0008100d000e410b060308604000c004902d0304000d5025520100e0400d5103241c007040d022000c0140d0b00150f14802e0082819420f80b51114002d22070414100c4000501c0d281040c011081c10b060384800d00d804d40300c140700c4c01000800300d4201300d28002c0010246d40440d6a5041e4141ca0724006030305c980c0000f078490540d2042ca002c20300407103402400040701401945424a800f410701d8014200040030441f0000b14141030204c00d205c9400c05208007603080d980c5a002c500002d150b034000c4030321108203020b4082401d15250701031140500a56040e194142000e034210308000061140c10360b80d42d01c0700b1140c586800140d0b00d9103c1c00d842019030741c440c41d45035415814400701a20b03c44680c403904083c10000d010300c0c070b6000403d0b1050306280d490955920b9507101800c5544003402d5104c0850021112400f00d000d490100e4a0b038402c03d6140d407030201d4088190382c1d60054540c1d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 229852508 1250 229851258 229851277
    0x405040c060e01030615030207020a050607050309100302040807030309090e0607120e010e06070504170604020609040203090a170a140414012604080301050f010f08011403070b1b12 79
    0x640c4503040007401d0050490b00d244020505000410326600c418200d0629142d40b80c0800080c2d0025040003140742194440c03014080c1540c0b01030501e089680c45c160383e44036101e100c91107540003d603c201424800d404440140a42c041507501d11a42c074078020304440d200d401102a0b160401d0404242020002110b92240d5080c0e134688088151541e9440006c00c90100c0030041035484400d03295603000c040049030f0007415103607901e5030355510b030030341c0004907407181c00740c5004540203e410700c001b5039603031000d540b030048003201c0041c0d5a84501d0b0900c0d25200f103c4070010035031a1072921036064aa040c1000d8000507800d074450691418410000d110305200320702900c9050020307408014000e511800113640907000c440346400b01148a0800400710f07801c219803c8454480010041c01542000400882210030a091102248500480107020705205000d00d0100b0a28007044080c540d0b010070814000f42560240da0740d9034402d00c08a45900742050050304c0c0c03140b10362034030300704401c4c8440104c0d5a04003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 229853758 1250 229852508 229852523
    0x80906161703061f08220507080c010e0604080c01081008010e150610200f070807060e0d020609040c020c131a030303040c1e031e0302010c0305270a0c08060106080105040504 76
    0x1900e09012121006e030200d01036458991030b0b039550f4005242082075602400c0300708018029590400001400c034000055014001c0d1000e10080200c1782c000501c02d00c040b074090078039101c1079a0b03070f2528441030b0300281d0040e0030315820110001d507007900208441c0c8140e6182552400719542d0311043c00005030001181c04001075a04812140d076041c0c035a910301c02d07200e42009a42441e116010b03640d1800030031b5088406d00d83c00134801040702d2504400d105d40022001d641c403080d000300e182c000440b02e016242ca01c6d8021911091000381c090320038040c0e0b92034418000c00b0030101c4001c1c1d0341164014628440d013004001082c4691003038074070b0008141c4c1e100341e91207000e00040b60b0a200e01290008215200c50010090110002c000580004042c2c0a941c0c560981d41c0314411140c06c1c02425100710480020a1500d444184841c5903e600100790450f900c2410170032480b03402002c06440d214500c107001d8001e40007040045142140451464100c2d400750352181d0480e6228000c03c012594180c50040102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 229855008 1250 229853758 229853761
    0xb150a020a080f1603052d0403060216080a0e0a0801050417070c081e0105061009140a09090b070f02030306010e010c03020f0f06091603080906161703061f08 69
    0x42c140c0c0014400307001050b52090074103034003100d110200404c1e01403c401180b804034412144140510042c0c001c43c0150403065088210000038a0680c800c80c00044c04654000840e0114000c105000c80a116400010b490b52004a000d0050902c101a08004e01c034000b80c000c000750004050017014000c6800c200700c9408031200c0c603041c4071242d0100c2021202c010b2405800151a98140b00c0c00d08a0a07103d080c10b1900c2140d04007542c219100100303e00d12900e0001d4040c403015034080c44903815070740381740300100038000d03882c000031404c0e07071258040c480030b50522050400300980a10032074021102d41c1c5031303450400d005140a907180c0c002101d605001440100707445186612031401003881a00900580700000d034682c401d1402d20090141c041d5050b4020000c0c454802c0d401c000c280c40000792408a24040e50440d42d800645120b6581120710403030300413031403c400a0807030f23a90144055000c41103c041106c0c0198000d819081101e950784191224440112842d503242c01107040e550343c0d0351368141035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 229856115 1107 229855008 229855013
    0x304090b040f0e07090e030c0303040818010c110402070206090301050a050103120f02060a1d031201030308010504230a0f02041202090627090a02040f0b150a020a 71
    0x291803504203d605526000724010302039428440c40415104441c10146165011b50340fa092020700001051000b04107a2100600c80c01c5072001c182c5401108050054800d4000c2c2640a81040c40780001000d035890711364002e00130710340300815117400d181034840403a003112021034000201d03603a0740d001481030240c250015502c0c0341441c80c01c00001105140002d440340d1000e804100001e40300c40d038030b00a50382107825011040b8821000c403601c81740ca03c011401c1c12807081c4403e0700440c6060000ac1489c0c10075004424160390010105c1c060740440741110401e17000014101d942c2c03280ea4042018030b89410307000600c000c2a80081c01c00c143c11041c01008044013024003001e00c00c501040f00003001d0f22001c1c0320b2402d00c83d1002030f40c0d80d26940d618640d50801450b228020360062500302d201d80b2410041d881f60752121010340c0d0340005000c070600c900d200e5100b04807014000d41d0152400000 = true := by decide +kernel

theorem cover : BRFrame.Cov 229676258 229856115 := by
  have h0 := BRFrame.cov_init 229676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 229676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 229676258 ≤ n) (h2 : n < 229856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
