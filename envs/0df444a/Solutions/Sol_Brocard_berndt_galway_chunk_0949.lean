-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0949
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:26:54.562527+00:00
-- url     : https://prove2.me/submissions/42e8a9ea-881a-4017-beac-e47f9f66a0aa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 170503597 ≤ n < 170683453 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 170504847 1250 170503597 170503603
    0x1a07080c1e0d120504030314013201020a060902040b03010f1b0203040e0a02400b0a050403080c12040315060605071a04020a0503071701150e0606030c0909010b03070206060102 77
    0x6000030080f03407441c62035008107505984180c1c0c0c02482400e00042c044030510041481d100c098100900d8500719103121028001c0d0004d4a84604455120502e030040302d0100003902d500d00b4440050045858000d480d0031952503801c061526280600208803a03504140c91401502c4600300c2e124a21461011045040388080304480590b88041c0c4141d490391140890381e4001e40c800038000350542d00114040303101652035011002d07043c0d685540303000c03c0c0314010a201820b03c880d03030150401c11800c120740d40317019400c00709070f8017140d4002590a0310340902040250828038104003507154480005808420010100301d000b000300c40b0711208024082e110f440903925846542ca019003109180121060001e51102c41c81c1da12a101800e841c1c0c00036a20000300e460f080840c0c01403038980600050005c0081404d00c42c89003075401100482d2110313454640c0180640328041c000c90701a0318008009000303103654400b1500d250074090140802303983c1d070705860007540d003003075801e800140a00408180341d98800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 170506097 1250 170504847 170504863
    0x60801020c0303060112090602030c0d1401030201080c18120a15060315020702180a02030702012a0e0303070807150b0d0506070806030a0204150512070f1a07080c1e 72
    0x7a10003507155445450042d41e902e140000c2400000740c0710810000000c00344d00286004140c2c83c00c0c280c2d156030500442d401035882c03044000c80303003032241e000410160780e101070180c3d0040c01e600322059982d245981c1841d845200c1d0010240c100d1101e06c8580040400000c0c4d00e8082801211842c030041242e008231420f45443d840050701d416146008020780000c2540242a01c1c0d00c01044200c40d2001990945e80e001405c0310008a015400300400c44c00a07020f0041e40031080712211900c2c0003003550101182e00d004a41c004404001340d03207a98940c03c0d1410070899a82c2500442c03169110109454440c2d0150760015200c2c0d012030a0414440c21424500c80c1d030480030b98024090001652400300c100c40a00000300703402d82c0b40c441e5a8003040035072100d11403000341d00c00001d50301d240941040d06000350520100045001980b10311001c214a2a01c400b00380255a445100c0000103046903442500c10301030104082c00c400400280d464815400040701c3c2041c1c010032584440b9011409030082d20f403020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 170507347 1250 170506097 170506117
    0xc1815080c0411120a050103021011060f07030e0304030609051501180f061e09061706130201090315050609071b02010c06090c0b0a02060c031e0a0f020307030b0406080102 75
    0x1c4030104056240c41d40246010055203c0c481d420300b0f8a080c00c140d0f07164000e0742c4041c0344507990001803041d803e005c0d504905a5549050860fa980800c141a954410f40180340041d01c0101d071012841c12032007a0000059484100d00300c85d1210345905220340201400082200c00b48111441c0220205131811000d04a07140c10402101503003007024140c0180002240d0f0041c0b1300d9542101050013420952503c030902050076011040504100104085a0036a0001d450726000c0341e4050090388400610725038080c984881500504105100585010075503410041c88042406900d00350080c1d15032250384076a50896440ca0b8075240d00d00b041d1100700d422030300d1651149009000502550041c40d107800d030548580347c001804101e40c0c5401031503c683c0d070030451620600003055003016030304124407500b080502c41ca41d0700d1400e04118440134103440000c401d10b800c5000d030010711100c510782e003c0c2d000d4061040043d0340c4d070b01e030503107005005003014006203110b40d18042d4040303900c0340d0510944020000d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 170508597 1250 170507347 170507353
    0x30c0e09010b130b030702071a25050703021c0308060108040804092403030906020d1107050904020409020307030b061512130f0f0c0f0801090b01030303020c03070c181508 75
    0x100b0000c000704160f00c8424000822035003000c000400f11580002140300d030506501074411182405610001c00d0400158000b0b01d94080c400b2400103145c0304180f00284d24592014151540c3d103140882c20803005a002035485442d0741c02c3c600404050b0103540f000580b20b541c51040c941c0d204401594840400e917005001014180402d00c0806c0107030703101d0980000342c0c1a03003003244800040d12195060868004800051600ca410410150100444908007070f06090114428601c49400ca070341d80d00501c111803141a125011506548455224a554580150650f90342c41c0c1c4a08164506e910162201805900440e0b01e0040c0484ea183c182d074034102c1c0c00c02003900640c41d0401c4584c481d1442e8a82940d42089108402e00003034001c03011360075107034800c9031010a402d24250050100101f20761082e0710700d074100081403001074803035020706055a5242c1401a202c1004802842c075500410304010803510040c4400b240c40948001c801403907032900c02c4240a07100010240e0144914144100385081c0c0c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 170509847 1250 170508597 170508599
    0x61b0807080f0703060b0f04080c010507080a050708071e11010e030a0f021903050c090a020403050a0314091206040b090a0203070e061818010b03010b03030a050f040302031c030c0e0901 81
    0x80140b003600383d04120940303004500240c075052804919072000000400c4a0300009041081c0b050900c1000c510340e109081c141d040020030327201c1a01e10710a940000003000720005143e4104507955054528070341d0000c9140f00640341801d0360040b050070a03441692502c54424003075001e0340c4581d0300210380000c00350141ca0603071416610044070746c0c211700c030490344401d1416100e000d408130048460b0045018000070588100231340140640341d039029002500d030500400041c00401c0000581c00d1900d5810f1911040004521809103003600540c03544a034450701185c108501c3c0e5000082c0c06000728000d007500f4941ea1140842a59900548100207415400c4480200580510708030400d80c0040d0203480080064032030700903e400c510b005c40d200760400d4080036070454046400d105502c018141900208440300a90000039580d0040e148100c04010307000a03c0b00051060009840c029079000d421115050341d01c8100e04065084119542c1c00607142800c2d4640c4d0300e01c5409a5034408a010344041e8a030f0b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 170511097 1250 170509847 170509861
    0xc1416020405061c050d1407170c070302060f0c12040302091602030c0109031e02060c0301050d02030106090c080420010c0209090a0f0c05120c030601061b0f061b080708 74
    0x81c00c0b0041030b05501c6011454010860030f40c0701400003595105101030003000c0403021016006048800c040300e42a142400440001090404980f4010320480c416a03254011000d240d03146c0011030700025001180171588000e0007040da030203042c000d512501901c0100198400d0760b2000d0190b40b00282d40242d030480130600316459018603c41a11003881a2403070203d902c1007590954440800c21800610703c080010302c0480c03040300e51821f0301094030151615050120f485030b40c2c0d000600a513442441558000011036400350f1242c1d00900d0343c1079080c00714034078420303005d4803504048030165442c0306100b48200e010388103c0180503038241b0584510941c0c0384a40c00340520f20100400000e440c4c450822200c02141d11003814601451182148000c91410801407040031888841c003081c0d00c1e844144010356540d00808c2c041c0c1034075480c0c54400d80240c5049030422441d001164050400940c0c0c91140b0207000c0103400c801010f01e09012151040c031581c0c441102c1448003107621000094407907010400b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 170512347 1250 170511097 170511101
    0x90203190b01090e04120f080f0a0c020307050a0b01050103230f04030c020612091207111201022802010c08061003050603030f0d090501200706090c12060c14160204 72
    0x1604010300d0203c071460344a1004126204040c0c034203441e0340c07040b43c4144040350340c401c43c8500030300c004c1c2c5005d0511f400c000c402c106030b00c40b0151480103460b4036a0401150b10344200309032120260000216040c56806080030f402c1d6600030302805000070300f0302991004581078550514504503d485025210f59688070b022145c102d0050000c904003e0483c00c4500940d5410025161900c065040c41c0c1c01d500300703440c4591400b680461146c0003400c06015010200d0907025502400c0c00d4296891009081d00c10f24950091042d915030203400441e02001042c2c842c00d50121281c102c1175030700200094650140c050743d041d881100c0e41e9521040169203c0d13041c91007600240d8210b03c0181c00c403801e10420390480e6605822030522900300b16038078540e410501c1001d00600d0902c01070101d80c500c41017030700103c1500d14071882e6409822a501c480d0000200038138a4003a400800300101440e0f12030503075150000240403035140d0400051a202021a02c3c44a404c086034002031429003900d080e40400d031b09103c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 170513597 1250 170512347 170512361
    0x9150503070e10050a1d1c0215070b180102030f0c07050f010614091501020a0305030705040302030712060e0105070203031305030f28020c031b0409171309020319 71
    0x2040088602c01e1410380c0e00c0e90102d0200e0000da980f038030390f02d0703000c0068003c1c4604889211689000d155418000c200e44546c00014501013048042e46410311701400490088601202c6207004c401e000103980b020b0090790160705e13010b0503e0b00448201c0020031550942070340001d4501b084605000c0011500301e98282d001404810f1044080e00c04080c042002c80d800c4500b40d43c8251328030780400051800c1482c10380c0b80e16901902040d085c510300584040001e50ba407031100c41c005c00740b060000100382824002d0080d0b82c02164010103d42080e6220704010501c01150307d01118000d0404501900801045c004e852040b8081d900031070843d5180511508800304517102915280000c0140136000d0407000005e010000143c001d10701d01107400d02d60050311803281d03c011802c43d04500484440d69a002c680b030508200c0d400814045a440036002170003d00b15500010450910148100c40803c0e40708050035508004402d442c6e80fa5544202c40c0c402d91208581d814840910f010004004040d280d000c44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 170514847 1250 170513597 170513611
    0x2070b0c030105090c0a0e010807120e011a030a08030112030c0c0303020c09060405040f031209140f0f0f03040603110c031b0705010e06040e28020702040c0509010806040c21060806010609150503 85
    0x4900042f03400c21038112107070840c3c0e800050b5107445441001d11000340b07810f941c8483c241c000b0800e00400303840e440e45500040c042c00803062003d003298802c0c140b0445404148680000051058a59030314001c5d5072040600045800782c0410070016445160a06c100b42c031598201c50f0b01d04031440e042e0b8007128a1045010442c2001755a8102d420110b00301380b0881c44400721040045c21103406402c2842c0c41d00c0c207001140074ad0340d402080c04c42c0e015000401a94100da1040c10042240e02500d81407012900548001c2411803201103101e03400d500080d40c60a0f0844000410b54040d2520703280111075000040f0b400c01e400c424100010010132180c0c1e1603c560006203000400003003c841172009509486140c0071181e5580c0108141047d07151903c5030040083c00c5090292401c00300e200041c01443e001014140700751740d00c400d1000c00d076002d0502218403900e40d0724a401c040b04180c400c400240345a000e043c41d5403261400101c1c440c0e0081040c401540c1c407960442c0c11001c103580f01144c2d03e9000810715 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 170516097 1250 170514847 170514857
    0x4020d02120d020601030218090312060f100509040e160e0606070c060909140615090d150603050601090c02030913140403030921091802070b0c030105090c0a0e010807 73
    0x9844a85000d00c21103a091407258040e02c050b5145004008c41c8160b8440c00c0c0040d0076401c0c0134030001d03180000c200c8102015407400d000041e40c42c01d001075000040070a0294100d60049880803550703a0080040a201504039410800d040041040580d10504c02a000c561403202100920440d40c070480707015400b134801000d03030349042c03034590303407400304030801d50011000c10109482808541040d001c0c0302446041c84c4280001454401d0008001c08420b0700300f4507070000006107404068070351b241000c0e0b030a038002c00c00707040386200444010014001e611094409004d0140007180d020028001c44520303400c1d40e40114144003609041003c2d01c40c104815600c07030f42c0d441e401c007010150155102c2d403107507000c0d440c00074105200d410443e03210728444a004a8074030410400a812940020051007591003050300c18a030b140075851141c000748560400600b07c40e00500420144200100095050b03c1003981c1e840d1070350702c40b1200040580070710544000800c6202d18961915403003030300c0155100d00c0303911701 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 170517347 1250 170516097 170516119
    0x6020606010c0c1a03010501020f010e0c2101050108061b03010b0d0b13050a0903031803090e0709080307151b0e040507030f0905010b010306270213031202010501060207120b04020d02 80
    0x14402c4000d03130311000b0300380740707038010004010039a010320204e010303501041d0091002c2e25101ca9100d8071004d03002d80c43ca1144038464035101142c66101410141b80445074000c0081d540c403002d90956409044540b03001a0788001d1a00350300c401d148060328102c0e5010300189092240c072429000151200b0305920341c11241138040100e04410701c2c01040c1c002e8003e03440005103960390341402015642020003103100d6034813841498000940c003184620031a403107035280007429114880120b88241030340c0e000030050710000c502101408500880c03050a0106007c0401400c50300c4079403ca0312105214644000c582480550794142c1401c1e0409a0301450307a260009011210031001404c607950a281940c0d207030354598102146503018456040a840b8488401c2412101e56840c80c8201103446000c01c1d070a0380114407001c0030281000400081c41e80300d98501e02c58003010400a000b400300740f00d40001413040f03a0000a6413440000001c1d0b085810003003446c02c41c1c1d1503400f40904500003040480e000301e03002c01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 170518597 1250 170517347 170517359
    0x17030c09090f10050d080d0e07050409030806030d0f05070f1b06030b030f06090a02120a080301031b051f03020a181205060105030c0612071403010605030a1506020606010c0c 76
    0x75140e48540041c080d0300d00d00e42809031100581440d10341005001d140203441c50f0000c281c282e0292441c1030384454020900d0441c03108001d040000aa000b50341060400f42c040d020140c01640c0e00c2c2c41030405a08484584003221000c84019030020194004500108010030202e9605801549200c0c041e0b8407401d074072001a81c0398041c100d2140d0003003000907515485400030349001d10400d0700002844005100307a080000c29551100c0b00f85400a110f54000180e446481109000c244105504003072200d0310303507a69040c2190140c103a0840564181d4119501003075524000015401090ba20080e50481c170058960940c020741c0080485402e11021000080200e480d489650b00980107000d02c00341000518900305280c000c06802a40c480d0b0805108080c99071107034002d9a03500b16115000805c50f858514040d200301d0301c45c041c141814100080040b6030b05412000440c06204080b204100035187d4020005100c4002d01407400140c0000022503125031042000e1180035019200340441195582 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 170519847 1250 170518597 170518609
    0x311060c0f030d0e1b0306060418080706150602120412031e090501020c0906130b060408030a0201140c03061e010e130506100c0c0306091403121006050717030c09 71
    0x20308414081da495407030413070400300b00740b00750380407000b20340d07203040703e6010802c0000e48540703004012034019940c2d032803800e000400c01c04130b816215070407000450b036545282c2005070140182402050031101030b12400640b4a2000a114040d0f281034981e030b074103107070600c040380d4400c5494410580c04c1281105070035a0f4900c403107081038261003c039294001028508000a4184901d80342080e1003150507008020240c1c0715070729813041e40441110006441801038000800500694111003418480880c480c101c0342e4056000380c001c3d585c94103401045645600300c8150320300c000c4510340d400000102440e20125240044a100707404141000d906000301c201c08038a07160101040030001544400038409075003031541d005e03020000f40c1d00e414041c1d010242c0b80d090b1f000c2610300c401030401ea42c4044140921442c080380d002d55440d810b0689035990404c03211140600ca054503404030800090310005840d5005004640f0410ba01003800216004040c000c80703060340005060501c421f80421500e01c0b699126 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 170521097 1250 170519847 170519857
    0x2010903061401090c03200c0118030908100e030a110106081f0b01050304020102070332010b04060801020c070512070510020d1206180b04111813060311060c0f03 71
    0x4003403554100e61404040e203003651685d0440f101414545001c0ca01d0b001208441d41000d020340c00c2e003560b520b180202e40d040c01451055072035030004402e80c0c1c60004040c0c0c05a5140c0454849030101d4941009042d400001ca450303040aa0016034000c11900c5c01281c000c10900740343e4114400006401562000058144184490700b0a2200081200a05071105500c89d030040c00c07400f860128114a00b0380d0002c5e43d2000e2030b01020f0302d00390548d900150000080c0c1090280b26012900d618000d12020041501800410b41c80c03070310507410545c5c0420741240500c03c3c2c403803090b4500020700f605881c00302030040740e0129252609503801a007a002c601c6489100d415501d441d03a81e802007030364580c07690006028045544002e210b07103040c08401c10a480400c809405030940004000038075481d00c5001038000c10340c001080d0540702000c1120314a600304801c0d400300500e025100c0d0010540c0300840715007120f11a000c010050f0842c1c045003169403e000010342500c1011074200c404a411600b40d9500c1c40c0c0207 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 170522347 1250 170521097 170521121
    0x60b031e01051c021212090316030210110c040207080409050a0c0914010302071a041205070305030403030c05072102010f090f241a01090501031b080a06030605040c0509130803130201090306 83
    0x1451081f500b010000c1c0301c0c0c0314201c0b1082d41c900605650000d000800410058010454410446c042c0c64206003c01015018014400c43d519042443c281606801c40e01c103811840e40b0b4071000895082c4640101507000d106942c68010f9182072061080d28448032000490405500740600c0b0001940608815154080c00b0802407862405150050707014500e10092010020241b003c040042d40050513640c01075410300300807404011008044070180652070029004013201c00a5043d0719980840b26400742d50281d00900050060ba9140d40a5942000703000784407409805071079000c2450007000c1c541800b046070700180c152404680c5002035480810264901031420350702c20840b0360f001114440202070a08041c080710034455491440c20842c3c5d0280c6003404102c000103500e402d403641c00a400703581d2102c070801044c18075040810600c45180650780c0109195400309107040c0190100341e1941d83d00150841c40c42d5155003810b00c0304c0360522001c9050001c1c003440480001c0b0b4030300410000000d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 170523597 1250 170522347 170522383
    0x1050406080f030723030a08010807050406031e0201090509090601080d0c0f06050606040506130503010c1103040308181e01031b09141201060b031e01051c0212 70
    0x410001004111203a0350710041c0e8582c0109112041c903100072050b2050141c002d17500f40060b140740c42c1c03000d800d072070700080042e001e000019180d070149400c405000d0680349090122040c0941b03410900044031468040039180d504502c0000000802401c0d80708a01481031500d201e4055490021480039401a0703040c01c43ea400140040c0325070001007000c4064090a0b180401903810b00c0c1d11460340303a0441e00000340c080354540000030301a0b2103001c101c0d001848090700081da030706200c0c4480c042c0e42c505070003074603c00d500340840400d0070f600c40c10035117040780030100155242030310b15a90905158400a80e0060100310381700118001c5c0e60b040c003540114004203d11503200c0400100040803208099402c0301108003046003008203962124175070055a184c2202d4000180d9650300082d09003041ca0a8101035609200c0c01081030301d00340002d14082c400902038503085078800301c82d40c290320b03000340901d07600084154060030380240100f58140c03c19002400d8103142040c0c0201301d9041c00020210042080 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 170524847 1250 170523597 170523599
    0x10e131d0d0e18130c08030307030204030c0b0f0307051803030a090501031415060c010b040504060c02070b0408100216060501081b18010b0f16030810090506090622021201 75
    0x142e044404560003540490b819040c041c00c4802045500f60081c1410581802182002040204414101c009001001c04803030b01c138502100d0040c0a941705000803124420364960004410890304165041c02034100d09082c00d5a50b1a04200e40c0740d0010007074051144503140380650740340c60900003010700fa096683d942ca441400d080001d0140c900801c000b014001a0400b0045840c4451400d81c1c0c0c0c0c1309044407440c0d65411940c5006014089025507507912a19080901080103001c1d4003410b0700311040d4095400540c0c0d41c11006004c0e024a01c642c2c9070b160040c01d4010024000b90307000f01110811046c200109000644684044510982000e042940a0315132943c89401380001000740040407201d4265401d01c2e1881c04c8a8240188035890741601c000c2594040d8002000540c2e54522294280c0414101c04d400c0c01880c000d000e654994401029160112303440b12240100c030f01c1000f02411580c141d854105c18010006100c8a003100c0f94800c1c4a4003556840e101d00042c043d21031000d20400d565 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 170526097 1250 170524847 170524873
    0x512040308070b0c07050a0201081e01080d030c08070e010807050c06042a1a090a0b0a02030304210f27170d0306060c0305090604090203011205010b040b010e131d 71
    0x11000d402281304241c24440303c0700007400000c2810020b94203103840c40035901c2c0d0f501024605004025018103100841001103076803040000c40001c0081259400d1003103010701f50059440480c00da42e80341c0041c0b0102c4050b03c4c05d502070740c0e0b0284c000f021883c00f60302e01810505101d00b0880c0644080b14100f0034104500002c014000030b042c10007003e18251700c98507241c8a940c0f610f0b030144005500001101050904140c0e40d200b50500003050072100f5a6074030301901e48001c0d140e40c811102181c12074880501244410041d81d49100f80000b41d440304400e26007155415103000301c0d151100720035010050110711000303c4078518140102585500710f0703841e00382a14601d00b0401a5061041011f180030000c0000c0d81c3d00ca55007040c1c46401d420613558a450010109841d880755401c001c0d0554000400000e4900074081030310f8034240190020001c4c11043c0302080151215803203101e000038000601c0351b14914001c5142181030010110004461400408110024091030403544441e00048814021 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 170527347 1250 170526097 170526113
    0x403080708010e190e0709060305060a140f0a0f0905030a03150b1201150c020402070b040605060a0e19180807020a24030903030207150e0705010206090303040f051204030807 76
    0x25210550b88000e942c5070601310041c080c04048004101c00b078a40081402e098000d0010402a00e206441801420303101d0800355550002503070261b0380540783c809010b650505848c9824010140c142d802206da8542d558420080c00f00004850403160b038520300f80001580c1000280040a510788000c80e07c1c910780701080791101000d500c500508501006035945030010710300d4050548041c0f681f01c41080f4414242211181c84440e0020341041c80001e0000a0102c0340250780d2055110750010b008035034940c0300b8000c14150512458681e0702410300400c416101e80d0800c0107408030103c03800150100450f02d0142d1944129009071409034000a00000350b082c1440043c0203131070760400c40d84071007540d40c20b40c80340c00c41400448d50405940361020f00406200707804461500390031070360340ba45441010b00c0e690014408811818141d00c11804c000880c0c1d400482c40603c6008080003a500703640e1103031079610640e400d0140449540c002c2d0304580c440361140700090000380d0300461030b107606c442040c94000c01c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 170528597 1250 170527347 170527349
    0xb07030b030a1a1e01060203090a06020c030c0423040f060507080f011202010302120702060601110a0b01032d03020c0a1d0610030f0903032307050f071109040308070801 74
    0xc00394116102680c0492252804841c921108203c0c0d44040d5641c1001d220420004680b0300c058030b0300050002906c0d50340000a0080c00c0c0003240c01d00500765403594241c3e03075011182d00140d0160803010f0000e007540303003987c0040e0509208845c01004980040d00400802030221400c035100c603003420b01d4409014003031060a901c01c0f600e0502c001c0780d08103506120701c20b0707005100f07086880010111030b40869203e501030b9560327550301c0301036031000d820100c001079211a422240c880c00100103070a86480030f0340014101e15000e0b00000e4803d810b0b42540c4800c010303001000c002c000340781c0000301000c400c071200c0e4555003060fa00070f601174401d2400074001c0003c0c00440e80e101d10421600781c111a2648130015142540007241119070600304001a901a4041c0c200424004511032420405906054060b044000b0104460903144004081c9400404c07100d28282c80001c00200705222030402d015812000f010094000c001307100b2480d07000b03400600031b06000c807007c5000940384402e001180c1c0d001400d243c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 170529847 1250 170528597 170528599
    0x70308190b030604140a0c1215061a030406021b0d0e0f1804020d0204061e150503072001020f040810050403120213050a030c03051513021210090b07030b 67
    0x1c4031103441c00d0002070381d0700801360010703020409048150041010070020384004070340c04400d4050055480002c00c1c151700351550709460403904d80c010310650511910580c010385540c8564803203000720124082025420081080300c1d40341d401c03c5183d203180c04814022004c0702614004101c40301c40040003d1104000a0055003c2c0c954031800790750340c0d40c40074a1b0303402c188052520114103a465000044030343c1d402c94406904149080b60210b0418082d1481803510b00b04503511541c02550354541720502034940080900091041c400700f01c58901c144040c4069030740041c1d18400d40306c4e16198035407c9a03c40c04809c004c80500140401850f2030901600741c1505002c5410015880c1a0f00c0240c00030824076001a1103503400030714203c05034200c01c80c2c00e001d0304002c2c220507401c2e41c4a14100c403445549001c1a41c0300d2040ea01c1c2a5072441c40704014600c00c02a0515400c1c3ca44402e60a1180e41603022540101e04d000d48000c61804005620505003014000c1d46c086d040ca090641001e0b0803030300c4020b00c072 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 170531097 1250 170529847 170529851
    0x110307060204050a1d160302070c0602031b0f12030912040e0711030c0606011b14030a02070e130f0c05030d020a030e010504050f09090102041203090503010b1804170c0307030819 78
    0x250901041054296121010386c554221210009000714000e1003504002806414809400b1400a0f80080946050f000c59503807014500700c80130126942d14070070400c1e0686d13039001c1a0765407144e0700110095904800c0850440c0c9200100d144071100c00e402581122035104140e80801584c90340c484480e03002c2d110050095440c1803480001603440d03010007816507042c007651101c50051800345458103442075270801c50100a2070b0306c151046841ea4026010480180f0a15101081c10110b00c00140c0c0142c6034000e081c0b183c00c095594a2030310100c0c0f01c8081c1c2e1030000740314000485072000d00c1261064140c5a000d000424050b02d0050610046500a141000703400d1005215a0312000c0603410b0805040724218030b142e071968102c17406072049420110402c940081508200340c0c10200040694000700c000b40040308449081c40034805c40760a101c081750120a02060110344d034440c1f460420407405800078600001d003080a072460b440440e003180021910800c004641009172040ca0300c00840c0102 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 170532347 1250 170531097 170531129
    0xb04120f02060601030e07090207060506090117030403060507020106090c0c0b01060e0d0807051006030b0f060f13150b0301062c0a0b0319050a02210403021b01110307060204050a 78
    0x30080d990000200400c0c14580e8401a07604c8440003000180001c203041d5800750355914043c903044010740070581c1e51a005448000c00840c034020066081407090446000031404c141ca1030f116034000d446c01401a0003503558409011504d0310040c011465516460740b0740031196011850329046e00340c0164000010040d02126902840d92080040410940c00044454a03606a818102e0501c03d45659104105140410000030007d840060510480e240705503144540c1c0e1710818800130410140c0d0595001c115449204140003030796000c0540e201c84081a102d550707407595295043c9610a030840700128001e004489403090344004000c020451214025019501d01360104000d003203035010700910880040002428500029051102c501f013480041c8814109078990000951041c0d64441e00d000c440c40001051181002c2c005000d42e40c5580101400d00202541c26201443c10b42420b0400c81101c400b4292031a0030000707030411078020400140e59074070305410408101e81c20351000355020b0070000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 170533597 1250 170532347 170532377
    0x603010b09010b131502060402011209050607140d1416021612140102070305070204060509060f04020d090f0c090b0d080a05030604321003050a0206071407030b0412 72
    0x210442c11584024912902e41900181200f182c00282e0070200030300b50440c890402c06540002c20790b001ba07000380c80e840241402209100c0949142c118041c00da0b80c400000729030610f200b00030038444040b074400144c0c00c00c4005e001100c00d80d241103080c8100e490b825024802c0c40380300c50140302d06c0d00c032941c001000580320746d0300c00d031443d4080d9100d00d1041c0444000100f081c45014039200c6d52440802000319502e40551401030441e40040c04264040e07454030304045100c1c104064214040d0344003c0c40040243c2c1404104030180d401252501666074880c03500500080354046c00100b020300c900091060682801c40c080101c1d501100c2c000d106440c58801e06d404541440c080745c0010340b141c50929600ea8030354000c90064151079a001e903074080e0040c0741d0030302c0d1009034101480c0e000b00ca501000321b94640c642d6460351707040c46001c0074155400ca01d05c20001450828014040d02d03124180856070340814107001d50070204103030310684403642d4420420041021b41c0c1c1a03d1100f00c880d040482d0104000d42c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 170534847 1250 170533597 170533609
    0xa020307090b01030902120d12020a0816020c030a0305120601090614070501140108060412020d020316060906020f0c06090d050301060309020d020301051e0901230403050903120702090603010b 84
    0x4424420080d40d034500c41c2c1c100d41d00c02e402c8075540f2500980141c02c0e00145080f104e035035680080c010360004000e49803820000440b4000c0f02d030180707519928000140c5908402e02c2914009070800f43c1035108001e1007000f2034405010034103285019071034041d118400a00321104906004107024104440310009220b016001070191001c500c03210030143d1500c100b031030401d0041120641035410341c01d0340b000004135030000148041c030452081600741d4420744900420b90340d400560784403001503001405424034030410441203030902030103041c000c130380c04a50340c0310b4800304c0e13000380340e4820402800035541150040421155400c002071800030488841041b000a2803404103020b18010075842d00b00c64400d40d584e81011348500d03074004008100d0380c1441015610042c00032020395181d040700c200040c0d03a616040c40707135010208014644c1d41d610380e50b101c02803007271040051046050107014010074115443c10000301c0c00b0442c0d00807110f49e541440c0c0c01000310016004045030b01c2030781844500c2103107407200e07 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 170536097 1250 170534847 170534849
    0x603100b0309030432040b06090613120c08070f030f020609011e030218010e03030a0305061207031b0b090f0f040f050901060614030903091e03030c1e0a020307 70
    0x21220054076501c9030710310142948111340c01009048080d40042c81d0150300c1c1da0140d10029109a051054004081d0521040e10038a5040380d40c03100040c007a84145040642c01000c80740302c0d40c0b07900020103032200c281e030f0200c4014400965640d07100220134450031004015031009031001c9064400054a95544d4580404c1c83c19402405010042085480da03406100c15054000c031121601c800790325000c50080003500044901c0c000b088483d04401c41395401900d0290544801402079461b11440e10802d40282201070505604071000442d850140e4000384030384400765100d1600c058004c48510414072106540790024810003108011610f41581c80d0a00b0140f60403003036403c142084c101000248c01094030002035003a65092800704140c1031010340c083c0c004e403449070711401848200e1404140407400201c45201031507000708030f5000149130800700c121004120403402030b04014400003113404e540207124444096031103c0e059000001c0da0300c03a041451140e050040c0104181070b00004d58070001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 170537347 1250 170536097 170536109
    0x809060c0a050d11180f0411070b0601020c060406030501090f05060d0212030409021303020916090905040203120f0a030c110a031407050d020307030e040c0c0b0a0f0c050901020c060310 81
    0x80051120784045076a0031003842060280050303038440d0000700c0344560281565070200d101d0071b680d1150140e68a0684109511022070055460508005a60f10023a9407400341001d23044d807084614144159031014000c10240001c7c0d46c020920354509640d502c29160102000c0300704e14104002c000a50b101c000c6000c02c0503804070782465a0b000b01c0c140150651040da040044281d0000500240c0000803802010449200350703184000d0756256054860141d001c0c1d200800041d0101305c0400854007150066600580001e00361050440c0030703824035410340d019000c60301c904080400d401a02c01d070588a020914146820054001c4e007030021065101c464041c402010710100f075200c0d15940b00c4c840150b48600e41d05c1800c0f0b861071034081c84003039070302d42001380120001044012150b082e401e043c026021f10020703c0d1620b8484e0300702907803588035a103c000e01140150b44d4030042c1e00b0010302c2038040c003c0b20300c900751a815664658a03000900f84011041da460046a00b0018840d08084805503d0b0880720 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 170538597 1250 170537347 170537357
    0x10b1902010605280e13020901050405010605030f070504090207031e0216171603050a022e0806060c073b13051c05120a1a01120603060e0c010809060c0a 67
    0x1510134050864644550480382c6104980030070001009a60768040031218021504d485e4260b0303903401000169442400b6510002c1c40c24008951846216003110f034100030242070003401c1c00e884144031000ca800c2210300340e0008002b0103450808040b07058008407040c1080c80030700000701d5100c640d06207003051071282003a00080f0423040c1c0c0c1e8124090042c075500141c6080f83c0f44600d9a24140542e07a030195050981c80783c401c00c43d403020015003103a006c0c05c58040080c0050010120618251002d000c020086038004400f000500d14001043c00b00340080c0103c401e50460361007a480c1003c00102d010040c0d580244171a45007500b07851400032420750b010404001d8040724440b0351816a003030000c50b801460440140c4040400f2590300302c0060200041545803e461a80d200d4255200b9070700f80c0d6041121040c0f071428440c1c10755204402d0f084403100741d00b10105020396a0758545040390085008044142c0180703199496039a40008441d40000318140140020f0030201c80031003547c802c041e41c0e40c0a00c0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 170539847 1250 170538597 170538649
    0x803090d080c0a020d060c030506190608060a03060906050921180d021305190209220e0a06050105030c030a03020d0c033f0501150e0604090203010b1902010605 70
    0x21004022003c40c43c0c0c1d000d0002d00d003540301ca14040000e040ba50b189003004c00d042c100002c266041160300d5212400743d1010860f0f032540b074003105480c2140301911881e0005003030000800428054001c07121510310410b0005010718025000b20309100024400c4410310420300c0250341c1c0f00d2008403d4900d0312031029014000008400300080550280d588020742216056150220f00c64595002922400e1003000401d000b024095081c4224410b0b180241c0d07108080040320025110020641000d059034140001020290301c0c0c40d031841c062008104452040c4c442006000c181010300c00361141110907002070100200d99500a501c50414640c1801041108040c14040c10b1103581984500c000c3d94400c1141300385a1410940040e0b841a0f010104591459005060320320034030071941240e2401030b520100c44224030f821110700506603c0d69601407001e010102c0e90b4142407000714002c1c15101c45480c2d41d400d030b01c1d20a490078507a00382060107691400d40104881e4440c080c48800c0e030441c0e0000c1000741 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 170541097 1250 170539847 170539867
    0x17010e01020a091e1a0d0b0303072a0f08071d06030601030803090a120906020f0f0607050903010f0f0203010f0803032710051807140a03080c0f0d050904060803090d08 73
    0x4500103501028403040342c8413545001724014001080100011142440307028400d03030a0558030304c221078000707106201e80c0c000081c2c460034407404011078030440e26541503c5980d58580300c0789440c15420a82c1242c0100c80100400d2510051107801e003101100106402d151510000e41c03200d0052202400c080400800600507141c10b20901d200940d102514016030040000010300d0340d2030b1030143c034001d0712a11150300006900003442c002407a40541c018481681d4880088460340c01422000d0340664aa101440e041811400355080e607502212006032a90701d001c180b1101128a40c1c410300c070304d0b002042841000e0502064000060500180328101a01c48620051a20f001078220125040c0750509000400164140d601440d2030000304a0304c00c00d40728100b00b00c81307803809000560704c91304000b4100000341c08900507082c60190320050310030601d001f008540c145079400c0740c4280003500026805905140622420000d407101100450610043e5408103000c1084805c000e0f000300700c089107551030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 170542347 1250 170541097 170541149
    0x510050f0621011805131e0b0103151107030504140d06020307080a0b040608060f0a060f0b03010503010f0515040e0c04110310090b06190203120117010e01020a09 71
    0x141e01c04081611a0401140b140c00300e00c034200380a040b040e08220040307401501143c0c01024020001d821a00b8902c1005a6604040480b18403d200042001c0030020300403c444251042c000c50103840326202c4c00420001c0704086904400c009080d907507051010001290b03200d0141d9003503465070701d900181000100006400003504001c0140001c1c00041000302e403d91250300180140b032961814004103070030500b0441543c80d117000d491600e0380000c0c0003400303041c0040c40c6583c100107003503c00601c8946800d107490808031250045082020700000410550809101f08040982d45040c10485170811101061140004c811a00c1c40745896541c56003008000380802011044010000c02801c111518202d10941080b00e00c4d0507901d020b10300c0080c0c04038180c0107201c60720100030071440c0b8021460b0701240703115500c886150118031080c40100b0320340750401c050f0b50203081884114409254500142400e4500c03000c000300d026401400055001600000c101054032501c44801c580001805000f00b1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 170543597 1250 170542347 170542357
    0x4110102010906020a030b040b060906160206071b140307150e0a0503101a0402071a130605010e010e1e1b0c1002190309050606010509030c0904031d01030510050f06 72
    0x5070034030010700c20f941e942d0580d001c02c400301c0f1f00b51401e01000060308c08002c29800741c0c1078031640250080020003100380362840d902c0c0c0c1c0c0300c0c40200014202034058075981031032031942d141e907414050b01150920944c10030320b00c400e00d4050224001d003141400c040903540c8075441041000103008120340c45c41510366504540b500600300160481d1034403401000200b002d0400307489004218038001c1200c0a85040070b008a4443c00d41082205440100280c01102d441d00c000301442c004803007411440f0006040d5004a5008181d541822049035041413005855048040c08021075461481c0c0441034001450046e5648241401d42c480c0701b217070203a01000720501c0f1b12220a03255000c3c1144d4012506540ea002d8016402c3c103500000704c6010b074580039800ca07980c0743e030050802d9002a0000e802984a80003c2500040140940340040c0114011aa501d401510220f002c22119031881d022009000304000030f030700c400d01e8284500d0414208031501c3c91840d029050240c01c00c0c100d003514944070501110 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 170544847 1250 170543597 170543603
    0x1015021005070207061209020f09040f06111902150103030e030a080309010f0c1b0803060411180916120203071b0f0b01050d021c17070c05090f0f041101020109 70
    0x10041d441c10340c5009450308014045c40000c81e0a43d80300744000e100900ca80c0240350740c007401a040201c94072040100306080108102e941140708180000001c20500442c3c1000742200702040d202c1400c402c1c04961064002c11503411588030f00f55900b00c0314a1851860b045039018100010a541c9070b10100781010394140d0050180300c400000d002010b441540085910402d5401c2004020386000701115814914401450108003a83d1041c0c0441c080400130341d040b0303400620000d01e02103940801a05a0083e502900e291407a001e4924120f0a260070a154000074104100110100c015005800c205000c0c00050700640e010001030001130041402108200701d41e40010502d030810319014400f1411950116582c800740d400005490600c1641c00d80c9003503005042c034880c85207020020702c0500110304251015000300400c0405098404000c00090780600e45164005e410581404800380b4040c041c076000040d40070400c100b019120280a4200e903000c412103d01d00304003c0103c0c00740c20120349c06 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 170546097 1250 170544847 170544851
    0x6090e06181b0903010216050c06070c060305091603030302030a0609020405060a05030a0e0a0f33020706090b0a0b03010e0a02011b47070203090d030909020c0a0c09020310150210 78
    0x104a64132001c000b1f405a0900c10703c11680702c4100b00003800300b507003c0c1070001001c10310340c05001d00000e406500407507480304112b000c03a450302c070341140b0f00014914980c6c02940429800000e1054807040c40c002c510181a9840003907103080d24000116000b0b1003480e01400820034040046480d964484d000b400c20402e954084441022083c1003c0342c0103100040c04a5054655000500b071064218a541d000e49034030b40d0b425000380301024581170296000f50000c4a0103a0788100050010f00340c0f84031140600c005080000e000400c100506003180e00c02903601c24564007003c0102e0042c0c0e84451b000010500f540400044950ba500c0d100310300080c103808400300c11507208200b01003504c0329408241c03800501449000107000b490010802014196900f6005070030400c101405401d00322200002140b091070840002d940d40d000d000d040380c10502800001e80c002c40c1c80741043c00320000c01900a0440340308110b247d8100301d801e01000184510690190800385910692420f000380702e8250381c50f10401342 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 170547347 1250 170546097 170546107
    0x60813080f09130603060e0f0d02060103320606010215191d030703050d0507031a06030915090106032105030604050a06053313090b0301090c06090e06181b09030102 72
    0x4494087c3c102100b80c114544651020300f00071810004070300b03003040080e4010700210b900355200d84640a05001c8c0b00300c90b46100414140d03c8050032210303090240b00c004040c01030340c107000c4002410049034840e800d10920901e4180302c0d910340703000c00c00c1e45440907200740002c91400038012500b82d030042074081c0c2e000c2e000c040f42000602d034003c1d00405032240344807400c011341e640d09103003501262509403644004c0b08030780d001a24617040c40b2000b1b5401c00c40a01c00c80d01c0c2402c242d019120041e804452402603a51140030400822040346425035298041c0b0300920090b10089100500b01d0200034142481a600d0f0404640a10441da2101c0c01a000c068540d007805a0a4a110180451807010f1303404404017001c03682c2c0e40080081d080c0e81c960310130114210603081c6407141e098044c0c07210240c001d41c555a182d0099000513500d4401030b000302010703101c0501a51034401c030601001001492640600c80b0a600140350310510704145921210303030480c0c202c881c0011003000340706004100060b40c1646c40041c7d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 170548597 1250 170547347 170547353
    0x20102010e1614060313020d0201052b0606033c05040f05070509060607060209030f07060908160506070b07180f050307080c0102062e060504060813080f09130603 71
    0x3190a5403d07445150000340180001d1100a1108841c0400144c00c1e02001c0300040c0f030015005810680149855402e01d01c40f5480d6050039041082030f9115091400d1071301c40c1030f407841d000700030050107a41410018049494401d0350203515074503c0d01400c02c4280d040c0044108206107031206c1a0441c00104464038007441e2414030600041e00507103a6108110703000459150920700248140c00c00f0f0000c034108502c1d0b035200c0000c3d400c00d2515030b506000b0720b01021640700c0c042045130f0042542d61303507800d5520f150240c40d43c2041180d90040c1c0880003152018403c0f501c1d00d0b0215101710786d000300758044035500c8040440715031075914403031070094081090004080b0208200007054400440c180c0740c4456854043c00d41d18442c11449a0140e041040002c043c6844016214903045080031419048048540030300a8120550030481c0854408a0180801613111b007090794440b401c0d048c03050074001c450303ca40c4100d001d0306c05810704200002404071686d4035501c2c8401c80e120724120041c8007007604d0386 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 170549847 1250 170548597 170548633
    0x1091802070501110a0e0a0b0901030e2109090f04080406050304051515040612021813170a080609040506011e03020a0305030d240b0307030b03030a021c050f0f07020102010e 76
    0xb20000c0c00155103c4910044e40c1f0b00101a08216100a42c529280c08600d00054029010715070400d0003d00526010803080c13075001c90744003000b012280300c1d250f0b202d03001c07420840324010180c00d00c0c0496012808120000e06488100c400340e40f11030410359126521450300700c0c0707815059250441c04d182d40b181403000c1d41608401003418400115828006c0a4030344000740c2881501010280d0311650358a8109964504264041d4000d141b81543d00001650741e04e032212007000190b54160704550014002000517803120b0f8280d0000411180708445041580f203441d0380e91410300415540c00c100210a01500340680c0e0800700a59025046c841e5140c1e503420700d00d481350000c5032180c10342e9003415592800e55420401007201303a1002caa101c00710301c0c1090f000d02e03100c1d04010940d006140d07440e902001e459400308007616041900760f005203449801c8103000982603864018507000d205050140d41c80d02c1d850f65045d958115003950500d0740b2040c0d81d00040740504038101000c2101d02a800131241002410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 170551097 1250 170549847 170549857
    0xf04020f0a0825080c030c060d06051005032202210c0a0b0705010e070513090c0906090209010e041104060305060a0905010303080f07090b0a08130b0a0603050f0304050109180207050111 81
    0xe6561610b513a540060f0700e030107101d5461a8550401c80701003265180010141c5518030b110302000449a0326080494904054003e2003070104001100308202ca2044100780000d9004030301c005400d017070342a400720340c40e0104e0302c40520000b08000c91403000000304000c0a0364001e00140110415580ca40000c0308560000000b41d8540d424000ba4641c2203900242001c2181c00280944400009419026001b451400c000f00d415022220000481e81a01e01982014003544000141c0e1251050009030001103010307103081c0980e081070790450320511001c046c0c9003201c00380d0a01260680e2340000190480c2d00c25088a144c1601d84000841416030006070184031311050110f100316038640617001d0311020014810502e14900801844466a21070300c14190030000242c1310100e07400d0260380388040c014084071400b107400d40d40c04041090000400c402c200140040001e94982030030000001d200346005d016410682d01c10725282c4060602d143e044031b5407039030410000c109200c0a80d1612010340c1c00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 170552347 1250 170551097 170551153
    0xe01201309050603060402010c11060706020904150e060607020a031202030a08010803030408071101030902040f0203100509091504030c060501140a06030e0d030c200109030908060f04020f0a08 84
    0x69110205034501d0314890a80aa80000d000345020f55030365004651b000c089034021105880c004c0041c246079125240038000b280d2142901586910802040c0000c440101c86604055611000200301c0c2080d000320243e00311034251450361382c5ea40c10740085204107045a00040810056495440d056540413000c1c10207030301a55146241641d83e4980b00e40e036400291000b500c3c000e0100445400124450b08113180003806040c0811042029000541100c19412110f00800d03000410892001145452807010700401c403a80c0b000750600704c1140d40c0d070b42100480b42c1389120b20280886c1c1030500441d40000c116030b0003c810f001d5981c580101094404d60303074103100d000364501007001c07a200740a4059075103004038083c010212680202001c8000d00340d240926030a0120000308444048100c10b0328011900c1c4c03420002c100030545240c0201042090342c4940f8042c0c110100344507071982e0081c1269001501100d0064400d2029000070300400300d0f950000c407851003240003000500e011a940040b004031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 170553597 1250 170552347 170552377
    0x5012312061005040e0c030a060b0c070602070807140603040812040602040801050a020a08041209080a050f07090c02070303080714040e0402031204060e061308010501080f072301030e0120 82
    0x10280b00a4881d8003590140380c600c1048440050005401300002e994040112500440c800d5912000f0300a42e40c00f801c610b020a401080c014041603404000c4440107000500060441c01d203030a002c0544e6518050b0114030484001021034248041d81054690410841c510884a410145000c10095200c1d20a400041d424030700024501503191085d2001001d00740c490000d5982c0f250346048080e1317210400300c0c0500442c0b03c804207400e00c0c104032000c9603920500c02040002800c510452400e03030550b0044550301e0500c00b11501da56804200082101e500d400c2c6610142c0f207420f401e0b030750006100b008000c00d0101080010302039010141207800340780290103560701710441c8125083c8030302c110f01a007004034400030300264031404d1580c0100703a510031300240d14003a6031311540350f113094540c20390000f03e09a200c02c003405241d10341070000400800301c50700d1040607181c12141d0301c481c0c0d46040c18090b0501d5603890311284e880c1000c0d0060040d0420a1514511906134800c101005822410112041072 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 170554847 1250 170553597 170553619
    0x100c0c081f110304020108060d03111b0103060b0703021e010209042310150f170106020706110d200a050f070f0e01031104050601110604111302130501231206 69
    0x30700c0c2c0707040301c1c01030384c060f900c184142e0307120030511001c4815070700f00300c0c20004055401c5c0c400c4072041c0711001d003030b01c1048061241c0d81f03010b00c001004e0b02c0840c2c0180c13180768010800800061380000d00b8580440b1032042d0700c401c0c50110009180240140c0da10a5009810095190781035041c0040151301214011503e00594a40701004102c00c5524010001244454a481d0b051203011345144041100c0902d4075150003158030411062101081e0b0008016902151041c4103960b04900980a00c04207039005000403c4031902c001c040304220b00300c2051011014084017040b180600404a2568100f411103495072a10f03000d04ea80c84d0384a1203902c80a4000410100708030070584e911904894002c101d402c0000d407a03c0400c001064060309990500440d6141c0705000801800b00c107209a0280c011a0340750450181071001818180298a0742c103803040210340482c070000010502610b2007031909040781804d008103c0b051707810100c0d01080305000411604582d0381d18140c070501c225425254002c5030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 170556097 1250 170554847 170554871
    0x91d040312090302070512010906060312020705090c09191e0509070c0203071e21030813030c0f0201050c030d15050603010e1308040b04061805030c100c0c081f 70
    0xa03000082d0003001a04556010040d91400c8a1110031004504000040d00411551031204031071940c0c1c412036810610b00c44918001e030b0140603080040c84165010003640c6441d040d01005e07840344044940c07060080c03c03c1080006003441c01907019040e11002c29000c152602c00482440303010b481090b01c0380e02008000b1b071015100d032180805540c0e01030300400d80303142000d01c3c24621807a5400380c03801814041d040012103501e580e000399a00e480c0703a11540584460750600800d540c034002c06540d00c0c60700c4075105400080d400705040a800740c000f588602965410710040b0b03070030300c141940344e51540701c0410210031500c015808032038a100f41140310070700a42c0d50018440540000d01c600c4002c03010a4002076014810044403000003841034282500c3c0940b15180502c180d00250032440001d9040e10050380800310080c01e140150008030000c0c4a125100400030700607a1100b80d03500308001c40d44040008120b22044e5220103404510140c0b805071465036510110180740991054005041418511075 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 170557347 1250 170556097 170556101
    0x3090405251110050a0b060403030906020d03140103030e042408060a050903040e070302073e1f1209080307080723090f040911120106080c10091d040312 67
    0x6180b0300d94029001c06074031126144010301c80107015030034068442401c8280355032070a009001070351082c0c89500106040030402850300003802c100000740751a0811601c03900f06004c07030590443e030f0f043c0381c500e02c07400080700450043d10f00c04503c4c03401c428481d10001d052220564919058428440803141290f407401c0411080c0d4a05440404903500704000c04e100841c1da10170341d0382e0b00005a090162070300c3c0c00c0340d031180c9160806041e0701000c00300c40003030103000042550807900c2c4c20070b685080718106c2c0300329000074240d01c02c9000201d41890000700481040ca010f17010201d06006180c000f002a0301c1c0380d060180c07182e88202d4440001402880c00115607a00640d0f000b80d00410800b90022544448054144c40c5d900240d00150311284a22a042d0141d403507000340712b42d4511a01c419210788a8100500518184803100c1c0422641403034401d1081c00c1c0b0009000c02c55680031150003500d071180c540c040d0b40c0d00c10503820089509400d810b001c0d4103070101500150086100b80d9680026080482d50042 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 170558597 1250 170557347 170557367
    0x904090632011505042408070302091e010c020a09090203060609010303142a0109020103110405032d12030601090504050c070f1b06020705100206010b040306020c0309040525 76
    0x314900e1440010311446161081c00f10700708845092070340c90503858110902103001480303c580496035a4000503900035602400d200e811030720b9803c0070350a05680b500014400030020440c5040c0c00042c02c1d070070006a200b80350105007981c019102c2c04215803600d17003110190014510990291007507a0108085080c060701c60741c100e80e0181e880e188060000741644816074420f2400c410107a400380924840c01c00301480c814017101c0c900c000081e610040d4030000d010744018a4400d8006034050004202a03180856503003076070303a1519025030300103003680b445d104280003000c4506650710406200040032589100118090341c003d03201c1d14000d95844007008103613401202d0f6513134005800e10078100000c03d102842481c4a100e982d10803132481c5c1e0030740c0c0034207140110f03480340005038040b000030800c90608058840705042c00303101608d400d6040c803a03030202c24895480001c2007141d000842404000c001d206a4012007070040c0140028100040594030005140e80040c241400c6a00d8091156001e041c00413 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 170559847 1250 170558597 170558681
    0x301290301140c04030f061508010b011103031603020c01020f040f030606092903070e090a1b050a06050705030d1401030b0601030c0206191112040c0f05030a02040504030509040906 79
    0xe840d142c05e60f514128515094030302140d109440b0700c01c084400004000312030103030000308000281d1b140328100040001034880321542c025001001400300344588211108041c110506001d40c0d18940300560310300a20403800c40444820380414040303000c850864a03a0304507400f41000b4043c0d030340c039844081c00300c0700801c6c0194030038900b0440340303103030004082d41101844e01c0060603108250364691481030030080c21a41d07407046400100c1d005040000f150500c011031074684050711100d40c00c0001244074040b1901a1000b4018081030007400c0007400c208035444010505403d00114081d02d240b105058001e000440d5190142400104254072030712a50000c01003d40c000d02c0a600d07462210700003021450034282c07050703882c0c4500061000c181c1000f004820070840c5c100460b031500382414401864241c01600c064168038400f00a1660006145814507404070f0307001800340c0b079034a415a03407482400402c680003414485d503e410b0004030b911000986004c1c41605004000c03507107083e00080c1c4c180c00701c1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 170561097 1250 170559847 170559871
    0x2060f0106031a0906060706090b06030d030209030c0f0a0b0c0106150309020a050603130c08240106080609150316081c05030117010b030a0803061009030302060f06030129030114 78
    0x94443c514205000d5a0041e2000d40042d16250041c0c5074401607411030310f030545501c5406000d2180d0b0303003010044d850f51280d80d8541181007042c1c0d10006600ca00c0280007240c4203410150f1400d20396501d5210b500020540041185c0c0d841da19005190701914a610400e01440d4500c64140320ba18000d0103440c0b005540240700c1000d040c20b00d0308110107a0005410701c1c1d070912032010000c00254000f031201000d8100714000300110505510f4000405140000c14640c00410000420031282c200c500b458000b00300301c0c1c0303144090f500d480b240c0500989041e1419454400c003200da99011070603680c40d80644880b0301c10740e800c1c40d0f8603007801180c10741c2d0800c40f180000c4081004006040e800740040c60500341c0381c80003140c518202c40000c0d19103038071000252845e040000c1030291510700342c000c2e1144403a403401c0c01040c10340307035031000707920b803000100b00c1c2003002600c800198007580c083d8030414034550b118140115203071000d51500020300c9603201c5036000750300e00300000f032070080d100641c2c83c4915104030301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 170562347 1250 170561097 170561141
    0xf0c0901080c160809090649110a170a060906020708030403080a0f06030305070b070207180e06060316050d080f120403080a14060d0c0b070302060f010603 68
    0x110303030901c0001c0090b401480d041c011600591403d810700c04800c1d0140c0c00c050f40703a100c42820041e0440014081c544160103e404a400c0a058030880070246440b800120304281d186400340000e2618290842c1109015400c00c0802c00c142c916400511503805d403034130b800181c0c8030510411281d451003040c500d15030150300c0f880009a955000441407034482c850160402107107540d1564580c2041c1c0d000c40118011000b0001c400516109111642c2d118120500c0041c2c690f840250244c45414405810082c43d140054007960003000b0600044c45003d03991040407044d510103c00614150484003542d008400200d01c4074a400228a8980720401484010552400080242c121018101101d910005000e1110141d6054000d01214200546c440351a440c10340340c020000a40104280445858170404155007600404000d030304c01da0079504450300c0b05460810249010159010540c1403038001040d0041560108074140541c50446c044502e590329950705030b0a455010007410001040508 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 170563597 1250 170562347 170562349
    0xb030601050d030c080d0e16030b0a0908070c171e030306010c1e03090e0a0515041d060a0c26070e0103020405060c0a0b010605040e06040e0c130905060f0c09 69
    0x40c95140390b602c241004924074600d99100c402c0c640002280e0103205035101d03d4190307505414000388884082c40c01c3d048030b03841d0030b50751940c4041402419120700302ea510701802040190240c08c03241941d0f00b1141903507040e0350354418102448100300252425000e000207802454101c4090140c10a5014010303604560b90700c0011141e117114118203842114640c0290401c868401c0d286042c941e0082c2c0d5004211401c1a005d400c481c8070140000c200c00d840c09003045001c61109010146501c8200c8011039601c404c0e6250006075510a101c6020600032132081c8182000c10fa488081050f8954551085246002100c003402804c50310801d1724400824001500480c0f1035552802e45038014140142056282c40114201d504581e0170b4070b840360700c0341c045402070045020a6a00401c003030b1920074070b49400c0201014034030102420690156440380c403455804401444564183c11028006190052020f030301c031800f506600c803040c0c030300d4051440450340103000540344900c68182c4003505498550810 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 170564847 1250 170563597 170563609
    0x206071707021c050607050f0a0e01020c04110705060f040308040f0f082704020f1b1504050304210804140d080a02070f090605090c030406090203010617060a0b03060105 74
    0x800d0080ea0800d04225100060340c55801d40d8008505040000310b6000c01450003514111014041d10103219062010f1103c0408000803039004d59914503010004214920060f40381c107921192550340903040060803986202d0103009001094020310447d0340d03540340c0d480c48404074001502c0150000d0310100c00580820f00038000d0200c110b202d21140f10080134162522400c54001e81c4000c0f080c1d8074140801c41044014111280081f041210304600e0951140000c5a4601c40d1084214216641640030540700340e0074400b00501043c0c1007181c803541d203400e02d8001d441e40e002d802207210340c04003c0e046180a03285494810300407a0311036805072401e41050a900607031600d450320150300016140081c000944054080c050214082d000ac11025080c045c1402140a642e00a110032611b80001008155900707000c0d6608903e401c5861903403615075042c40d8000d40401c0a0194040d070138044005020800b400a031204410701d10306550258031070032004d60541d6400308503280d0540c00030005104610b010303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 170566097 1250 170564847 170564873
    0x1050d0f0515070e0102010b180a0e010213060504030c0911030a0207240c0f0804020604060e030f01021908070c12050a052802070e040302151e13020418020607 70
    0x510100d42c420000858908002c0908a810000058103400351900b203503024040c03180902c400f280c001d820030010305074000c003500d401002e8145803070302e400184c500078030b0a60403503030140583d0744034407141502d80001505c0c9500501c800c1307441c00b555101c0081d9610a5106690f0b100011900b4a8516194491524042d401048040e03461050007196203503480c580034024418201c2c54040800e038400e2034070000d0f2403854100301e04424000398004000050f1707030303100858090799028200b540310340310040042031400f081501d03404280d600c00a64503005d4160441404154000b5590b00b0b561507a038107504442185150304014030203120b40150258860140016005070042d81c50024140500e916490007182c8640308000180c9560310551002c481d4180070210161407036000003404d9007002e40c0c00a540f2001d00010158030000100800c0540f1325002e0041c48040c0c1c6098008142d0501c41101050944e908000b01d00c42c51600b07031965020680c120f40155220307001058a41408400c0e12810001101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 170567347 1250 170566097 170566103
    0x1a01080d0302091305150307090209011b03030e03040e150f010c0f030315030605060a0905070210050903040902070506270c060d06030204060e070e04020414060a0306090513170301050d0f 82
    0x16604039800304c000240315191003240412002c10b400d91032081814281003054102c2d05c403d50041000c10600e980003401903140c824480c0c43d000c12105a800d08400500c40b5081c00c40f0300d40000500011020007015946000e40c003005440040a9076030b00400035107140c62000d81d40810303280d07210a804500040900941980203080118181e1a03104040749901256041212201e41e503000340711690801d801c0101c003070035040300104040e0620480103503481c07a00c4046040c0c410341707400004101c40414000c0e1070041c20114825911170185160481d183c11080380d0400640303034070700c4a1903000b43e0002ca0301e80d071540b902030240801050100030b1201035030001c22010030b215114000080140c0312442907000038111802e40d120305007042c1100501082020310b42510131350051105000c010384503419a191104112038156441610301c3d800e4020308001da0089050758030b007038104600502c11106031044107100d289403052808102601407102c0c0428040c103604070224640e2240082d42c41107a200348140 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 170568597 1250 170567347 170567359
    0x3030e01050c011119030501211212110912072d150509091005031009020423090c01050f12130609060c0e091501050306010e03070b03041a01080d030209 67
    0x3140711400304c1181c2c030840b04190441e02c80200c10000980c107100c5c081c09041d41c00000d0000c1048240b104040c0b0740d82e220050103000c5d202c3c00e04d0300b546010300810002038001e50024004060302c1c44805505030000411b85000315000d40c1c0b03150030b8410200301d407002d54031a980e07102140c1042c8040c00241d600c20103901e240040c41d2a40210701d407940503800d518400d800c0e50f02d41d540c0360300c0034060006140300540040303006510020144100d68011512868260040400044031406c600003d00600480845602603481402c4064900205c160001c0d10603104201201d120382c3c1040c004513400d00c18100240d4180c0f0082c050180d81d03000d10b460151300044001e15680001c5001d49a0341c0031a504903008948143c0d0310043c21003900d03049074241e1000c03007040310200218600f100c040092600c5c05202c090400c1000000240144e000745010030007404040d04507180340341c0303d8503e0b003100d174020f5606452005100150001541c000800203058443e0540901042401090194065003120314080d9000c9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 170569847 1250 170568597 170568611
    0x90b0102060403030f110f0a110f0a030804060902091005030106051c1205120702070806010918030e150406030501080c091003080f0f270f01050403020105090609040e0a061503030e01050c01 83
    0xe00c902020b0401191060400c0c3d64840c100823000c0c214000c144c441842d940c0100d483d09210074400300d9090720668050a003600b65076682c0c90701400400c0f088400030b501c49203000a0040c15041000d8190642c0d130150020061705460380c080082c201d0860780190011400d448511001600101a051400c440390601d00d0800e000d05040b40103040c81160040c1c0180d00c101d10801030301d1070401c07500c1e0060400f15401c0041d09041490075502c01c45c641d0001c0c061000f24213031382003242c6400e94142040280318166039256a00e03203e0003405003000f032180c00c0f064412641c18056901e440c0440c580134101007550101d00a1555a45003819040311541e0456070405001e10758203202c1c484010050310f01100100350003200703075803080b0030f103100e1200b02c1c2030013040c56190355101641c20404482c00d0380d0702401e00340e448403441c800042161007603845154106086c0101d0301c11001c0001042c2cdc08062180700103020031013021301c01e0094030140e440042c0015000f01e1284c00e442d40904020302c1001c0038a000400c502c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 170571097 1250 170569847 170569871
    0x120c030607080a050c0906030103060506150a0e0a0b040b04030b1503010501090e06070c080409091b03110109080a02060307050304080702040509030309070602010b060724060f0f090b0102060403030f 87
    0x4160210340100102e012441000300342480c0388620383c0d011404100e682e05007040180418407030b0005000041a00795901c010403815520840c800b15142c1c08902d4041d59000700c1d58000304142001c10070306004403044580803a2003217841c416201910300d4410720f64241842c64480200840c405811031050f0090050a030b00070752401c4c0185806000c2504020031220a400c1040f4a07204c4010500ca0400292002d0301340040c112500321800c40720360fa070020401c41e03460300f03000700d541420300d505c82070a5071680c2c0c0000810990740d9040b046001c1c26202c0c51015070390b407900142c03200c40e01d940c0294444810000106607a000341e01642d04680214860350400c10a03602240c202d07181501c40000700c3d4804020449101c504000d80ba01402d00361000f80408007800003c1a41170140e10780080c0115040b81a2452808506070034a0b511b0251460501810f03560300d81c034110b000c80350700441c03183c03040c0c500d004a0100b41c0380c0160b005881040e8000c00065a41c2e0f2011001456218041020a41c0f160366034080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 170572347 1250 170571097 170571103
    0x112803030c2a020a050609030c090711030d150b0a05030f040c0b07030801030b0702160b0f1309060510050304030f0e0f0a0311030105011401020706050c192306060a0302120c03 77
    0xd2203042203411602c100c040c010003501c0c070050703031215119401c2003014264035100410b0b40b0030303104001d81d9400902c2d140e0f1035042e600200c8000021210f4440803031404080002c0d84c02c00109008502c1e08554100c0d180c1ca20002e13584685542c0b0004110200302240340c141c0340c5140c40d54024050055814a540c0b50012080c1c5517111503815000039451400500610021589194008080b80018420881e04218494043e0258400d811a40c0e201103031407112545d0640455090303030910720011420716101c0c80d80c81c0041c17000703001d124011400f545c100110300d03010700b007224003039034150b01c0c0c1132010445000c080300d455801d00300b120f800c10f00410301c049071501d808118070050751142c15400407040d241400d050031100143e2050548200e001032490360b60740c0201f448016202985070895503040d49400551030502c01c01c1804007050904654003052080c1c058410004941a0300340c025011101c01045559040555000d6402807498104000520740304c0e14501d840d0100354296410003003035100082c2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 170573597 1250 170572347 170572397
    0x2060403020a0b071b110906040605130b12190b0108010606080f09010b060d090317040c0302011b0506010b04090e06012d081912110a110d020907112803030c 69
    0x203100100d000d4901b10760320303110317040647c00380055404002003450840022440104049a0840c1d15030365421034010792102c0f00044d076941443e4044442c0c4002c13403a903002035181d41c00000e450f590304200c004540f0b0389041c0902d03400c07030308196150b064030380700c041c6103049640000e04445000e65072054004040d4075804043e0040302110307000040e40b036006050241104062070510014110100d00300000680310703034040b1003038a40a10f000c0310662540b24584411081c070a20207006841020300000b6480e4a130340080080c0c49130380c101031001c402c1e40c4000da032341c5110030700440e4043c45100e041d500c501103459039074444c00045c900d420170303100b6503401ca40760405c1091074030310030a082c6054019082c010004840b07454031010349000391120400c441c0070b584449080701c00520444144414411968603480201c00550700180103c41c40c0c01d00f80009040700007042210b1950303000381703078510300202814241c1e04c030042044030382104100740c2e50790101c00401c0d01064182c107000018001703032030b41031404e0610b43d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 170574847 1250 170573597 170573603
    0x6070c060f09140a210f2f0f010e131a0a080703030507021c05030d1a010f05040302060304060e03030a02040618061e030e0f030301030b0702060403020a0b071b 70
    0x1c5420103451034010207400300340e001030441403e4852010728588900208030205e0f0190311209a6064481d103840c03602070f009040285c0050b503005900340a0001f035a00700390851030090b0300d4801c3e21045101e6813500204412404e540506241d0400342c04e54007074030b03811030850001000c2503d0540c06000081c210b9448096424034002c0000c0c204007103040403404c9101401d0220018580f5a20303503a80282507101d0b151000740900307052103803680041c90952110010a80c040280d98550100700c4910300101551241c4c070407480e034510708005055020b44005c170160200e0b80d48691915080d5000d0254562015200f110040e44d01d400020001c04144051805180724005c00341e070769442c0210042801c55040520064602e60ba1000c100c4960010a50702c02441c040000d000803a007501e0742603000f01082c08203404140603000c545c65078a04003100070760607244100310464042c1c481d113101300d80d1004102c2e00140503034018141100030441d0356200a503c184940b6001085070003441046d034055120341421 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 170576097 1250 170574847 170574857
    0x221061e13270317060904051c260601030506060a020a020909100e03040807090c09050d051c09031b0303050f180a0905090f060405030418020d09050304061d0607030e06070c06 77
    0xc50624000110031310b42101040321680481d0600da100c0310b8458107020752142c04100310303020880600d4014494030040700c071030345000c92880340c82c03a0941960020844070b082c0001e1800000400b2461300c0029210300540690080407003100b19070074080035070f001030842c1000e03201c1c1e444a400b6403100350084100245c0e201010f591240d283c440c0c130310f142c4580c40c0c0060401034240359403a4032640e80005400210b6000b15180c00c160450742c1881400d000d0b1000c7c03201c1c0d4030040841c00d2880c2c3d0790420900340c00c880c803584009248428000d4a1444603805000050024400700300d08003207200c10001a28000391414104040341d4040c20000d52640c00f5540f244074010386600401c9081c83c000e01602d1324610118000d08980d16059598039100d01c107a00407188501c0f80416000c2c108905541a81d20b00c000a01c810004001c1e50b017099682e0741c0181c4944000100c0352a2400070b800c061141d200080e000241c081403d201131540c043c0c50303100d003c840e4140c0040050010b8401b040645500d0b00042c025074441d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 170577347 1250 170576097 170576117
    0x1e0501021009080d090f21080709030b04030507031205151908071202180703050a0b01020a0302151e1305010e1203060607060b1c0302010e0309150a02010221061e132703 74
    0x3030040440200270f04140300d1000c80400c04107143c8035505a0151f4146040c580e13414003440c0c26280308001c814403092480c0392600b00309041e4014034a25403000002c40d04400300a9006420001000c058050010f03a5004450100801da84100714103030814401044d0702d150503d00b820707003203407184110768250000380c40300d00b88081200c40d88030344105c818007071010f81300030300369914040c1d5120120502d1901d209141d100040700d00401554586004840c800554120f0900c150000f90041c0d0402d41070ba419460840340038140800011125200c0703540d680070a04541d0752600300300981c1c009903001c1c2d0f03900391125130a1070a0b680c1c07005010740c080201500104c0180310f0707080090859103142001c1040e80e204000020355940c44c095210080381c00314001d203a59400841c81203029005006002603800000245c60300800c0c0c258203054070414040d10032810020740c200901d911507049503d07070340e0407130750056034465403090f02d401403a4080042103600350003244202801c2c0d00700c0c040720004e40028006180d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 170578597 1250 170577347 170577413
    0x302270a0603050607080601030f140928120201020409020a030e0d05030c180301060312020d020f010203150111120301180f05091c091e0501021009080d090f 69
    0x1a90540100d24800304000d01d9040d03588040d60f41d6070240c150801c0c0480540050040d030f10079040031200020103207007400340c00a407280d51840c9210984e0700c00b0842c000c1c14800348220b0b00410300450070843c01c03000001200200e4480340c40c045660110070007155001c0102194000c134500041100c0302c1103a40015a140303514094604114040d68501d04201b4200280410304550740242c40607000190002107031880b000000900400b15540b0040c81200030008005055030041000e060300c11040e02904d400401070600c0508038441114600d4411642c000c138080e00c0c1d4400d9013042041c055a02c1103a80899a242001e15a41c009a000300c0800d0f0090914068020f002c0c010803404000c031090902840c01d1501c021512240106003c84c810030042c131900024520400c7c80788020700703d040820310000e0f40ca11520400c00d0039402214050700c112085510003142c240708441a5940000110781849031504441c1c002d005d2445054601140e03562071003000c181001040711600500c80302a0a20b101525 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 170579847 1250 170578597 170578669
    0x20a0b0403030615120e060403080a0e010b03070e180a030c030804060e1002090f030705090c0304031b08030609010b031003080a270f0509040c030602090d0615061209030e090408040302 81
    0x70f8030b2a041c5400010500c40080c0e080780002d5082070112f6004542d1010b17034803030540140b0b4824911a8503204858002070410030b0000ea20b40500010340d003410401d1314200b03409690380b40078000180064041d036081004207110303128a54129104200100c1c4258080808501c0e00d1a5001003040a560014024496251582814120038819030160280c0d910f00070024072400001014010710610010025041502c1188480051380d0902c4912400702c880c3d0401520380d41044031068020f401403000401d0856181d02500d01c15004940300c0e0030312034219943c05010740c1250301444140400003020704444940303061040e4185a5413281202c03042d1034020441c0c2009907503444903010306602c070140404a00c0005109068030382110026950712649000302d2820020b03035001500f024034054016501c50400d41d081000c2314202c0e0359000c0c000034441d0710101100d05911004010900060510030103007802d900e02507200c0d0092107070754101540ca4000c02c00701c007045241481e464007203903000e00742c64401c6 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 170581097 1250 170579847 170579861
    0x30a1104120c0f090c05090607030c0c03030e040605010c081803120d05161103190c08040b03040c0605030c070605060619050a02120412022e02101407020a0b040303061512 75
    0x100c1c082c0981460804046c01c80d03c1009204c5003d40c100154900605004503410184d40c0d030b02c8040d02d07103803640d2804c0060044880d40d8690b8810703030a02200240562144060802007034120b42c1d118034090906121107444801c403c10141c0600685001c1c204001136040a840881c00c100e070003145c40d1502c010480e0188401c001d140d000e00041c0b640724403c1c500c0001c190340300103c2d807415103000c40038801010f0711500c94444c4020600000080c01181c0f42c425070f0042c40c02541f0403040c00501c02e03101c1700c00352440e0000b01c4400019038014000c14012555035004103801840c0942410310300b14032410301c0101103010303c044d00081100003905440c0594100581c0751000c000310009814079003802401d580069181c1d0019204840405072544000d45c000d86c1c0303400d10b00c481f200104a031282914047d448009181c00080a20f1601610360303a000702905949214030702c158040e00d07100d0340b81d954401101e00c02500c2501019507a05000c01d0300c0c980c12108400100712502c0e8414404400d5031003100b52060 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 170582347 1250 170581097 170581109
    0x10b030105010e01060804060f0603030f0e0411180d06050a0213060906080103170903011a1003050903070201030903142b0e150601030f05011202091b030a1104120c0f 73
    0x7401d801040300c3c0c600004840c0c151036952600500d59161030030110003070085104000314542c40c01e40004101500010351410380022078913061507460b041001c00c411102d40103d10f0702c44e40401c000d030001c2010841c0e00ca01646000800552030081c0d82c0e00c6050849400b140ca02c00d44a60016150002f07503c0600b00270010b00551400d54185401d01030000c146600601c4010115440c9054019004001e2015140745040180003000218584c4810ba13541c80800020507005802d410a8043c0d258840c2c0250b601c600e000340c005629091031540110010a188101642000040325030782c3d0030144410002d0002c00480004a406001701415580d06071154114100246150144c1c2603202d2030081003407030300c1081503401080310b03545610060f0040c001c05001003225519040c00480c40000e80c880f8128090f000703842c001e149564008005540044107641c3d03d080c00000d00001c1d03002c145a42042d006441c1018150382042d507940c07181c0c00c00e4082170340121181560b200c07090001d1030380c90700c1d12002002 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 170583597 1250 170582347 170582351
    0xc140306070c0609020d02060a0315050d0519030c0b040f03080c1c0e0c0402040807141002060f04030e09090105090f03041202301605041103150d02150c010b0301 71
    0x100514094590b0700c2050008200301d0b15598640c040d5030790305054204854000e0503c076607618505c01c00400401001d410700b034000154500c0842c83c0d041004115420a512400501d00c002c01051051303406459560102c0c10080c0240e1901c00003000344903030783d00982c8100b03c42842c00800e85405000090010a101301c0c600040c40080c04c010144201c0c401164075000b00082e002144400d5181000500700541d60454000540001c03160700002d4500b04552508d05540c011050803420000460303039403c2500d0043e80944089442c2c4612444802c2d0840d100b420401607945804010504590b000c80e1baa4a081e55103c040184018007400800380061090000d546014100300c038052240a84000c081d001e007000404021000212040003000000154201d1a14280340d8041c95940c269061045a407a50b807240c0008003401c00c0d0040c000c0403031590424509503640c041c0340c02034103186200056404002c0c0c1c921000540c540b03030803440581c40480a41ca68a000080c1c00c81d0960354a03c000e140a0381c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 170584847 1250 170583597 170583601
    0x30d0c1809020d061e33201203010905060108010b030a090501110c0c0a0f06050405040e0a140303100b03040f030f050720040c020312010306020a18030c140306 70
    0x4140d446481501d026640041e200c10500300e09100800c00d07604810803800c000000c00391407032144401d1504580301c80c1c403038040c1c1c64144066034803183c0440c1c5186958040208070391000500503506a0142141000d0b49011007a040829901d000400c8010030b030058400001404000558054640d001c2c501b030901404c6541340c00b0101801c8e2200030305400150b071392040c0c2642000404c0d00500e203070302070040031030b41c403900c09224003611202e5070100244169040b032000a100610018004100c4200303485480c10546860180320281008406100c52400344131140000280810001610004000000c5031640f400c0e58903903458071030b40e4101e103801319400c0c81000006088a40d440240640c03510b8220491080d00c50251940d00415030700900c0604020981000c00300e0401c00f540c6c05100488060002c1c9500c998180d0f103a01c1011070010740021301da401800841c84070b4008040c5030344145030000d2803410403998440410300e50b4000300e80501244800304450140348a642c3e2444504401400c154 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 170586097 1250 170584847 170584877
    0xc0b06060a090b090a1a040608060d050607031a0607060b101805060d0e060405010b09060109210c0b0406020a020a090b09040311070b030708070801060306060e091017030d0c 76
    0xd8982d9200703c0c40141000a50381c11151182d0032130f40c0040c0748400c1c1207410b02c445020f4803689500035010b440c000860305d000286003860407a580c2d41d1800d411001503c1c030390711400e400f203000e040d594040c3c1c4400c026494190081d074035080010b1580d02e0040400044903c1c0540802030302d0700003040c0030001c01015840c080c0740a814045010121642260126a03600841c1c0d810009014010f181c0c0e800750003000d04020074001c0c10b4021901030391300ac581c049015500c0b107005564600c114001c212030110f45201c4015950202e117411441c40340240c2c1e02c00b042c541e9076052206c082d03205401010058100803417040442c180030303a245000e0080107200703020b040a1040494644640144041d0821144411054000348148280c40203011000c030169a03a141540000d8080c190545100e0001103009000042c0b09110b88504400d941f440d60b10030100c00c484c003042101c1c5041c0030300010508410480c0004140818621741c9820540e16006152519503500e12081200c5a0070408003d12404010a9141e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 170587347 1250 170586097 170586107
    0x90b0715050c0c2d070602070e0109110a03020c1c020c012606060d0f05010b0403021806030c0609060909010e040201080702150a020a0c0b01061d0315270d0c0b06060a 73
    0x68908000a42844d41d0390307001141e030280704080c42c5030140c5c0240040403c0080e400301b400000c1d140c0704c21500c84566a103e1907481140e07036000c4800e070700300d109105008032244070350000e10140c0c001c2001c132407141c00020500001c4034541c465130005030b0f208a480540a50300300e8942e0402c010720800c08280107000c0300f40d003510031100805192103901e0014201d1a120f103039030b0080d00380c80345218040007a50303181c10741c440b526401404103074814000710104840660140d002c0070f1086502034050b00708200a00184401908400d040705c0d80107070140a40201c50b102e60b49140c2c004c201c2c6201015150a04c1d00026000100c0078000c20b007190061041505810050306c00245c004402e40001a1b0310005800215080e02030101c00920070012040001840d60740f01d0b40003a801c00080c2415030342050540100343c0d855003200014924050904000350f0240c8d03c8540884c40000203890310307000d07590844941401c01c3c8407080d042006c40d11543c0751009004046114550108065401c40e260548811010782 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 170588597 1250 170587347 170587363
    0xf0f010e0c090603070906150306050d0c031101031413170408060121050105180c010509030606040f06030803190f2a11010c1205060402070c120201090b0715050c0c 72
    0x8041c09800b408241039440404c0404010900c4030820003001c0d03107404145600340e051840000010382418004200d0346420103040000b07030340c40071841d00320300c2c0b55903108075103c8040c1211605259507040b2540140707040e401054841c3c2005038400d158080c51f440c00720010b00301c2400c14a1722950500c02071205803000500c06066501e84600b003c04449220b0b0780e18510403010900400c0d81d42030109001c0901d14a8202c25250110402900c025111401c011034803070042200e075523416401000812214203117a0b02120700015480700108895031a612004a56403094500743e0181c000100682d40c144414894801e001c061103c00703011174200d000800c0d030302c80c02c100c0c846103150105074500c1354402d00440c259240c0b0b016450081c00715409441014241e41000203030340c800e41c3d04000008000e45020b100702e41c0d00300d40c003524020f9882c2c28094200c04480c407854049050010343d00c408100403480300c0c05001d0b0b50b17100301c0c01501001d0703e414855043e20b401500005204505201e10b0f2145c501c0410555 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 170589847 1250 170588597 170588599
    0x41a040b0a2a0b100b0f120907080f030d050903180405190606020d020610060206070f030f020403060905100905060c07050c06030c0c19080f1809090f0f010e0c 70
    0x240580ea48034500e00061406201c000ca80d0441a4407460304110a482ca080e11513801c0061484040c4e07511480c42c0400d00c41c1d88041c20164101f001002e0030100c0403c8601c0d040500e80c0102c4000c0341d03c6040c0d040c03500c04810b5007036100b070b80085190000380506001c1c00c3d600040c400050350801030381c07038207032900c1c0c418041c00644550b8480c1c0016070241c0c402ca440301c0d02482c1c80302090003240c1d81d812002c0e4903036851213052001406110009a1164820a2003204541c1c05600800c469507415404903901e80940e08181d0400d51600451344044215002520103140122000580c01c1c0706071034807914050800100041580c00e01d007205021031404030b00e46a0000f03090400320b945070740901d003440c207121404058590040c0301000303008042a642e4043c000a03aa800c0071218851054003100d00030101c0300f03100030506001082a14006118180505000c2e01071031001c4402c0c90a10000900840085420012503030090040c441c0b109820414941e6441107000200607800c0c10905454540490400507 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 170591097 1250 170589847 170589857
    0x705010914180403090801110909060f06040b0a050d0f050f04060515030f010b120a05030a050d0209100e01090b040b040e040503040e0f0106080115080f0c0d060b041a040b0a 76
    0x1801c0d5110b1410080c900c841a80a40c6541e25092401405d55503542c080c5207282c0d0318003060688d0382c481d21011101d00980040400030a81d8454041001c6ea203d0f840714a50130500074400001c6020740440945070300801a00d0f89074540d8080d000b186c0840d521400c5d5000400d0a0005010120607003515894000d600640c3c0801c0550712240c44454400d240400a5054803400101c05410741c2d043d405091200400c17680103400b2101740c00b01030303502c6d00c064001901c0d5400822180d00240e0140c401814075521584000d8248004076001400b50038004080e2030100360400040c01c2290307413180700d4001400307200114504007410900b04090030302850042d04600706107100032806100d000c0050743d006150b05d030380c2c61441e03103402c41c204007000c00700388280c2c00402d25440c00458596072803034071020151030030380e0b45010300d545600700ca85144402800f03420f408001007011211201c060301810029140d039040c1e00e03580d986072001c001c0b0801081201561100e005110a000400c4400203d403100c2240b17280c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 170592347 1250 170591097 170591129
    0x40326030705121f0305070518091203060d02120a050d0f0903020d0606080a240c0503060d060b060a020d1107051008220c090515061e040305010c030203011707050109 73
    0x1003942c5404001419030762048100c400041000000642c4200342c80064074104840c0c085c0c40c1440c81c272740500341e03014505600040340f00c681c1c070074049002c0c5901200040016030340c00075540201d24503000d07050750107180e604400014024000c00700080134480300c580ca4041992518050300500740fa40c5400000c0c4100300ac041d140041c0841d5411039006440300350252941d84015281c80304041c0100b018101403589030508800c40c80203541304207800c02a20340c030740c0c2e0b00e035946210400608003040c40c011282c60380d0b200aa11001c0e1580b0010f860b144851342c00501c9100403692003e41a2081c00302c1c01c00c100e6221000a20903501e508280021559003414416555118036101c004c0c108072500360544e42850806015083c064584026411200122020811b640310a000500c44042113981e4540011007000303512070b5200034108180030600e50010503800c0a48a039605829103010348e5025000940100041c08018400c00c2848103171410038000b00049850a000a404004c0f2441a50210703649803007 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 170593597 1250 170592347 170592361
    0x15060804140c01021f090c1202010914061e0c01060b0d140408070206030702030d0e0307020405060102030a17060303040b0c07080106050316090c0915031b09081b01021204032603070512 81
    0x4180c0c055440307030300407d96917201c00d074049001615070002d90010307280304000500c80c1c0032921300707102506024182919000c0c0d003c01980034014040d15040c900310007001202c4c0921028030405c4082c050508074143d8801d405040d48040d00c00680c5030f080c0400910080c000000e0044081f9036646506071103898580d614000140d00303500400d0b003810001400c3c4550946802e00100050250500c00c440c104140c2c6c44803001245d890003500035080115030340c070890a0138602e03a0501030760f01810007002c0f6880d00c1c4d103510401348540c00840c5a807205a02c00c80f42800b44c40000e01403440030b010194001c2002c001d9131208000d0a020300e01c1101191340d9a813103101781081c415481500070781249a141046d1654001c0700030b0041c0320f2035080d207070701079030903e807200040d84140000c0084484c0c1000904181a11021a20314405003103000c03410340c8a45650400c0c00051344024100540c00740304004012041d003400002884080100740034401020010400c070160401e0a8860080d100c81580d503240d03031016 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 170594847 1250 170593597 170593601
    0x3050a0b01020a0f020d121e080c1b030d090813080c060a050a03090f080714010c090608060301060f03051b01020a0c030308040c2403110403051f15060804140c01021f 73
    0x840900480d0704c860000c6842c0350041070301c0c0400030460101c4c1d00048c40d02007007219031400580d109481c1030810031401100e00d1034601c9404920030310030140c0c0e2070400c445500b0320460f030b100403048800840101d001c0c8140004c03001800014401d08011300b5440ba15080010242e2041c90201c809101010411220261091380300c1c0181300c1e4481e00d40240002c1c217090201c0c1503003003502e00711203101c07107420000b1a558041c02400043d0b409501d07510722107809c001d801d0340c85280003828580c00d590b03140d070006140401c0750a14001180540c01034442124000750107404140300e010981d0666002a04880000309494800320403250189003046154603140380840c000d41043c0d00040e4040720300102d004983c220310307108103840181a203081000c05007070100f4510074000e503c400b80c030303a4001030b80800400140030801c0d00e107114401800940e07003500544c3c1c11402d01c941d8111200040887d810442080705488410340048444030003071010302d81a0780002d507075541c0c02400e1103600601c1c02c50306911024903 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 170596097 1250 170594847 170594869
    0xb0a03030813060207080309061303020309040c14031e0705070803180a0212061006020703020306041b0b0703050a170402102003030f0411060c0c0f060408060a05040303050a0b01020a0f02 82
    0x418410340d920703106030a2030070310b039082523500d40782c58046c0d0300104050340c1e401008564002d034150061400c103c40d49003048002e184110341b41c020301241000c6128284400300003188642c030301080301c0e0b58804410349072031b20b6210001e0119060007020011080410007040949034080c40f0030031003140300040308070300764200010b411009422040042c200d10104901044280c454050f102015810aa03a5941240d0b81c4950f84030185d019000403010402044110581d920203818941a0180c40382d0744881d103601507400f000b8150002240480d03215500740d44184058144e0200001030101d904280e0001060004901005400d21400402080c040700402c04004d10003140c150580f500c3c0c2c40c147d5010600c4900440e011146180200a00700c031501e44001582e00c0020200010405c180d02a0180080c1d28032246a0686c810824000094070b040d04120040c400c0203500703004a00d505282c50040d0541d003010b4040101142080d0f203d1030166030000342d0300c080c01e4000358102c03150b8180e4004100f4003844 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 170597347 1250 170596097 170596103
    0x31014121e01230f04030c14100516051b01180c09050603060403091401050706060303030b0f0a0b070201030209190f152d021e0a02130b0a03030813 65
    0x694107500e51407480c0c924020301c8449045000344008010142c80064184108000211007825480407500d25880790701c50b55030003482418504e003000e40d65250194444031a100301400303640189010f10300a2a00d00030a0781001450804e00205019454050440d020386640030340f000c8160460034040003001d40000800000c02c0f4402d024480460509039034444040c002d59110605002c0440c44504002504c02d1045416a03100c4400c2170034500200f014a10920300c0c0b0381080f00520610b00451250321070742006510030740780000d40302c03d480280007100581c07443c07092250741c020b00100070042c01002102c0d0792980c2440c005941e504210300080120120342d04550110240890104d400403000400c1c100b961016210300601c1d1340304010854100c404003180f13607602e21200410360301c8800c031031440488500250050b90a0341c0079090b42e641c44c840c0708103044100ba41c000380c0c08200b9400c041005840c00c1d0a40201444070016582c0414114101c510008040011100c0000c220030b440e6a09510034a038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 170598597 1250 170597347 170597353
    0x80f0901110408030714070e0105060a02010204032108062d04110a0c0c0e060303040b03132a440d030606030b0f030d050f04030f080301080f0303101412 67
    0x24403403202c240c0d60340101d1170444074030020b003000c078611003400114001100c081c04040121a0700b05010700c4110f411041004007550340070700c40840007510080d0340729452001004c1104070506440d900520f10500174100034080c81c2079440d2010201545050206001c240c3c0c13804074000340c400400b050091908001090f074034803000c58075130280780c0e01400124450f80640c5501d84007544446103294145001d41b11980c2c035074010041001f4000c8204013a44c2c0c080301002d2040d601c4041c076115405040c0c105566080320480c0004076a00c0042c40158060190040104106100c604090000318041d240d6605075005c0241d111030300300111400c0780c01c4174095010f0054881c845000400580a05964020310010032704010018496080518043c400140002c0007802e035040282404d4503a54449200000785800030400403010880321024001c8840c0324040b507680d41d62424030594242100d00107249800e80040041c40740e100c011a189009480741c40c01254030703c001e014005801071581c407407900c100340 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 170599847 1250 170598597 170598599
    0x10302071709181305070608070203160206040302061804060b070f1b0302030a1208070509010203120414070b180a03020a0b2107030c0e03031c02070f0c030828080f09011104 76
    0x1303452100201810742c425401c803617595032100026a6a002d0880307a140c01a0f205014514000d002a14001c2e02c4d180085c00136440d03d5100d80100d0040e6001900c1d6042451a040b2840c00900f054400c4200a004030f12416051007029a90040304005e6040003a0524800b00a540d01121040c110800113541c0141225110f0b2030307078941032010440b800b1001c03011624030b400081505028000301c8110700d0059000d580780c182c0c0006c000a107000081c0040d1254484880910b0400208100c642d000d0101404051b44480301c505221040f6003441501e58040c2503003410410050b10b80644010954800c0310a080e22409801d1071400400014940d4a44441184040c4841160194401c2c41c0241d0345a81d035008082c1c40c0000e06560380302e50807400503081020311200d6a0351a8036806001a98032030603400484001b06e0300d40224000c42604141c4184100040000307010001100d410680180c0c2c080d201d41408000002401c0a280180b650b2103100300396002543e00f001c2980901e001c43d040c40350759a25a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 170601097 1250 170599847 170599861
    0x130b04021903050105011e11010e01020a02010b091003121b20031501030b060409020409020423160c03110f120d0e120403030302070215030411040b01030207170918 72
    0x1078558503034100003182c60b003400810700794030541840000c140d4414842c02409503034001212102e4184418603400d56840084030b248500030700040100201030743c00400c0d130480304410400c162401829414070190403140c1080003612008800c0c501a1450405c81e111202c80341da00d070b030300085942004041c0070f2800d080c12a00c60120714203070900d460903000c594182e021070407039451b42d032420300002d01118211030008140d481c10f50465201d5600c064030200b03410507140d01080079220000480300c500c90740721100c840c02007035010006501c118000451001000c0d1241301420190601d10042c00300002d9075590401c0a10820003030b0b1003420740c1000ca0365400b1071040c4201190300300c240d4511011703007007411000301a500020303480d030440c41803102c01d8038051079543c06070002c0d403028a0072a0010180346100d4103031000380b0050b501c100c0c01203025620b60760381d00f8100000c03605840e291034180b600c1480410042900f0703401c40030300a0200c882d016641c9007890005040d400840c01641414850340d8200400f07 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 170602347 1250 170601097 170601127
    0x90c020a06090f0b010b03070804020f121212071e03090c0b03071d0303271f0203031f03050d03050a0e030c0a0b010f1a0703030204051002010b131109130b0402 70
    0x1490140e02034042c4d40c2d03200c4600598501c0705446d54000681c0690115002d490150700b14594403a00030040c03078140e034400591a091804116080c4584140030403040c110000d00c2c500b081c0d105503685040d6412411005420b41d40800480351801050303500e58920f010400c070300340c1c0c240c00741040b250515200d29000360001c00800c4c1034881072070410041d8101c1d4400f0308000003a1171029885052500340c00c003510799000b04c05440c030400c56078440000c1584401c50b1001c0f546d0031200d56015401b0310303940e00d400e00e50461440e06180026003203841c499420404281c010403150715051491038081110303201ca0500001a00090140650a01001544656000000400c41b008522640f0340e620583e0780c80c1009801240350340301c0d080f44044605641466040848010502c0354420704005091944841c00714012960048800015079510510800d0900d0081843c81d0100c02c40c84e424000782c09180400302d05070241c3d4507064003408400e0208801651a40c00140d20f0742005030085449261182d80740b40 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 170603597 1250 170602347 170602373
    0x19022107020c011b14101401080607020a0b0f06010c0512070606050f0f01050c010e060f092b0e0a03060f1d0d020a0b06040b1503071404030c090c020a0609 68
    0x1001d07110b04481c000495000c1c003c2440403985411070444480503c0d03c9038107050f00441c0e20507002c0e02a10182c0d00494070a4420585c0c002e420051131980c070342c1009412441e044000e040d40080d940f01c802d810000031404994541d20408170f000f8200f00b03407100c40c0140c0f00c450b1021401030190050f1070702c0516030752501014107802401920207025881e41c0360240001380c030f44215015042203403100306034450750003400101f04000c1c00d2400011710071099905c6604050b020b41d4903140c7c0c402428240010010104540c1c800014030f103002100304218003280041c1020400810000c0c8846041d5021580d90b51240c8000159004076050022681d541c05a0340246404043c4024981c0e25448a0040c101d0000d00c9600e03400d826001411801c10986944481c41c1e001041c007030b440b40d00c44031000210b44648060b4203100b10340900341501c81c02c10b204064100e1a410401010750134081c0010004a500f204010084401e14580001c64047d280c0b000c9050003501031001d400b80e818580040200060028821 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 170604847 1250 170603597 170603611
    0x60f15120d08091009020303070b0c0d050a050a0509010c020c0108090f030c010207031404031e1104020a0c0204060503210307020715090f05040239010c0809010b0a03050303190221 79
    0x2d01c400382144c940b032040b540505406500740e802405220002003103518000e0304000b51840d440e040658032017054054600032a01c10132200e07100c0c01400700c8940540a41500150030303100034440001d0ba0039000355985281c0d001c1504100204010820421003407014084c84c0c100441130b680d640c054902e09034040d6019540440004954641c0100081d50210540d81500d0b40b051018078250000c1c0c1c1d08140c0c0c0400d05c0c0090f40c14003500305606045686920003007a600d4540e883d400c0d001d0b5800d0040004980349940258080e400403040381004103030b14203102490580500490303444e61601c0e80300301c0c80c1109903040003a510380c00b40c0c40b0041207500001910100e882c11070302903a07034603156010301059028605558001262801c2120200700c400703080003003e04442c0b26010942c0114508039801d41c0c5c1d50518281c041031600085c002160420701561046801c140d4201011b54a50b036a856528440201422120348680da81200c401000b0780458461b40c24000510000f00801c1580d160004002d403110 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 170606097 1250 170604847 170604853
    0x6060d0f051b03040b0703090c0b07030f0306090605030a140a020a0b03160201110318010b060301091e060509060d030e090a0e010e0c0f060a03020702060304080a020609060f15120d0809 81
    0x10b15001c600ca0300b02e80c4075030391000c1203180ca41c03a07101054015141c18001103808100c040c4000c0ba400c1341500243c00c40354040d5a502c1004118488003604031020783d0005c184c2c103410008144070303580340011500103045d07210fa10815042590458035043c245511030003076000a4411000400d9140c01001d180211082e01000c0301c090b09401701a4203e900e43c10021252000c1440010061204c10004e026200c0d0000000301c0d182c2610300000310144d000340c22600c8046d5072091004d81c030840507c410700324213550050400102d4108400a84070400041150b48103110f40c98126003010310941c0809243c0c20090100725140c00c0107043d03c4007404260701c4c000d4081d031800000c54070303410000814080c103003030240040d910040c1031810320055074412000c1c40b040c19020802c0030011385660008503c16805041d09a85489400c02c00030706004014000c45966440301c001d00080d1020f251461390410219904024605a26804148800980740c00317000c4034041c1207900c3c3c401c00e4102d100f0500c83c600c0790040e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 170607347 1250 170606097 170606131
    0x1060906170601030507030f150c1d040e0a081c020304081908040f060c051209010603050d0f0e0d11040e070e1f0e10030c030615120f060506060d0f05 66
    0x80e299644402d1002410950007a482000032a01100c882d51280e40200b07400b580c0e0b00b00a4940c04141d80218014800060104038510485089110ba0980130074048400340705071400840000d5032250ec078040501804d10000e0703040714a08040101c1005070303100ea42c040d91280f4040c1442040c0d034001e11503d2240c6104003062211091154100502c2031b40c3c0420094044042178640c8001401c14079400400d000c010802d0800840f44041142d01c5040c24000104a541c15880d0039030400d14811044014000f00032003071800c040c1c20a0038a04098010740303c2003041401030812820b0300d64032404240d00145807840c24880090081102401d0343c05030f501d00143d6445188061010205403020180b2034461640207101c8038040b074441d95004119030420100e5541c580d01e0381c00301a00e01764000c40d145560768452412143d0040702e01001040400c8803140e18410b0303521144460006550020a803da0301c000080407980c0e0a4296200e41005000800803200b004503c80000c02042d01c0240c5181c82c0090 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 170608597 1250 170607347 170607389
    0x4020904180521090102060a090602090d0507080f030a0507030c050309040603080309070b0301080d03090204200301030b011212050903250501020c0904030525020415090b010215060f010e0301060906 87
    0x4030b40e0050130603401410140e9918000800800086004490568081003030040707a0740c80d03203a08000240a6070180c015070f4030740f08141d8030704100d0080c0300409400c10311001031040e401c0410340e051076425080031103000803d0f20340503046206246100783d00500d882c1011041c00f8201d805503103d42002412290140c1e1980003080c0903002c24420048194411010034030040e00c250808140c991010340013150001030012801c083c0703520414900c2d10101c0c048010014000050702480c01412400c19514249045440e005148001e084444043c000c00040703686403130720100041d6080c003800100b69103401e9011000c40500b80c6a5203e054010300c1380890014030b5141c0410014000c03589a11801e00c0e08101c2d00c1c05101c0301c008662844040100e80032640c02580b40c13801680c08820320030410045940c00c0100d900c0032104810007a904551184e5030141a112100064036000501217944d036940b00501001210b60051702d000d6141c040d400d2080014510300fa40c2c0040c419250a8001448005031400f = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 170609847 1250 170608597 170608663
    0x3010b0d0209011202180112021c050303010504020a0513060f0306060302040e0a09170309060a14060102060703020f21010305061e01030b060103020d0e070305070b0414040209041805 80
    0xa10301a50200e10000104182c080301e00e407401145101902110403c9005410a42c54030000d90102c40200e89980d031400841c81d0401130709402c402c07c0d0b11039860640154031071981c3e90205010319400383d64005015400640510203035406084030004081915840f610005c003d0745408085401081c00c10710045400e500034020745068840c0c0e044000507030317a6020581c0010340038807070b01542c20300c40c00183c12811800c00402580702d411844000d100c0d5041482c51a000c42e030880321040c50440284080c8200382ea40802e055820481601e0050384910b11072842c1517062203080b0341000507000d5a1505000d680d655241d85040340d008109030303a840c3d40c492035101805c541c000000404c80d024000144001882d411019802034810b141c018103180c59207800c2d404403425899030380c00c154814203080041100421110001d400c2290ba030f5070425241c065900760410001c55910303c11038001c030300030b035994446500c10107205a41388001a035038034413401c0180d20340c44402010380170b0225030030310500c5200000c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 170611097 1250 170609847 170609869
    0x601080d0519110a0305120c0c10050a060b04091410050d03030c020304230f01031e1a04050f090709060b160204110c0106211208102303010b 62
    0x1600d46a240c0a0740c10201c5140c851142c000300c0510403034a0804101032801c001d18030040740320f611020740d100003c00301c04031803203030003005664104010400310302c03141c4001c2030640350300c000f00342d010401c1c2c1c541645102c09841d081e0844044008041400515504150001d0346890780410300054240c44a603d4101d8034a4039001d03664110150682d0b00000038030917800849488032a1064074140b5480c0e40f21800886c074500c400207280d141101c070284c40b510b419101108a00400d00341040030714401400180c100c030b0a55481d246c80c66551110b40c121004610051101641c018001c10040c40e002089020000c03003030310b01d65031520610710042680150b611501c019121061049810f003a4000c003226003800741100d080760455280d03000790303000f154140d001e030044115100c00414490f0900d1008444044c3c03403681100c0030b85070800c51901060140d040c03413a094556140580c1d00780d6800d414107040f00d08a600079404030517402d0550b14032013080c0a4031403a20200310000d1210740303014403c0295203150 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 170612347 1250 170611097 170611123
    0xb031f05060a0e0705030705091f03141b070f120906020d0c020d08031915060f030203131412070501050708010e070818010e030301090515100c030507030e030a0f0203060108 76
    0x14060104d80101e000d0b0307016552000c09441d0040c80c4c4080040454010003a82440403807801c44030b0b40680e48240c250082c144220704483d0075035403501d40002007200f100d850300181c0004c0d40000404105000d089040c6407103a6400035004e60b429207410400500d0a4018031469006002e0880001e60240c0300e100101d0380145c0090090046030256210701070343e9407020b4a04d81640000c03456011080390305028034000482025101d50050f0301e014009445d5550b10707503010003058410001c00820308100a402c0ca2070503001900d00c4080c0040c04003007850507020380032550301d0400100d02c034020080150800d07881a40c45030307900340c03003a6601c0314a801c4102081c0c440710041141080026801100080075198001c07043c4004503446000503c45801c40c0d100f138200010507501c0350b042200b002880b070304a001c01e40c0f043e2032401c95440d800c01d000b002c560001600030200600000c0f140305140c810f0521007005440101a1804402c85260110003c40700c640e04030302070b000300400000e2030140441c503070b506d100c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 170613597 1250 170612347 170612369
    0x60206070c080310120b09011d0a060903170a02191d12031603050c01110a080c03070314011202101d15040816061b02010903060b040b031f05060a 64
    0xc07695490010b03810083c030100a00801800010300b07903100310040c1c1a22030240300400c0f51420248417050079202d40e0b0402d4814140c07210295403841000242205070f01d508810006140451890100c079210041401110a0300d030749402d00a0a9603c0c7d801861041c500028403140942043c9042d9001e844884500310781c00c81c01c1d0b014842070704000384100c03d4441902e050300c0ca00039800c0140c0c84c0b800008601075002580200303840c648a9000d11809202d032428001c45803d058004000a04510340141140300201c000b00109600071300a800a5900030701018102c881e0390784031020b9004164036150240d104440e06e100c900209400741e809275010418a814010b00c039410101403100e284141d07441c2284241c030030080056080000d01c0601a60901030b06000d400354039049004102a01480c441c815905a040c090b80041c1e0b0030140c4602140c4d0b000700d010030702e505000c00181c010460008025014001c2c040d030f03051880034280e92403003c142d52280800094440c201803142d00c038528042d29400c0d207 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 170614847 1250 170613597 170613617
    0x606070b0402130e0c010206010f082d370c05010c020f13090b09010204150f050d0c030b0111010e07030b04050a140313060509030d120e0313050a06020607 68
    0x15103000365095100c1e0000d00b2040075503248030841012244c14204103e41500540f400b10010f6a040c080140181010400e03003680c5c070f08000502d620398040300701c4401402c40304040e0558285040208240900ba800705072410410780d5030740e41805007100c0c00900300d50048030010208030030740d15204820164024110f07a07006424100151550007040343c0990b40000340300655012071365082d84003c0c0d03100b68090003061400d40751030400700081d40034002402c20390051206002c01080000308500e041d0b0b8529000601c0d519003641a03034a485a800d800392101d00300507035a0021501608500300e214001c0e641c1c9015510b0040c801c2e07080300c10380c0b00140740540100d407007080460140c0d4031040c1c000d4000e106903103510440740c3d0707a40b02a6403a502f82e20700300d810202c0c0f4581c0c004403400d00c0c400108003030b082c00f0303283c40c10b00303000603456455500703012090102400740c21007019070b40e0b8022008100c00714100c2c0d41d54003140d4600b0b000c1c54107e1040d00d00c14843d55402103100c0c3c4c400f0030414013901d01529020860 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 170616097 1250 170614847 170614853
    0x207060e0301060504050a020403020414041101030b01050d0504110102060603190609240b0f0904030206060d030302040b0a0507020a05010c03050a05090f0901030602120115020d1101020c0a050d0206010806060607 93
    0x60342151880c9a855926180b02260580da030b486090302070741c411103005907540c2c0b861041c04143c881c680d0500c0c030134546000070030011480c0120400c0817140c0c03d113400581201c1c28001a00c050250103603401c0d11070301d000100010010201240c4400349000d03001c881980d51140201562642c040700f01c01c0b0000380c12590000000c0481c1c01c041000b52165a02918440081881c05803801004692421844d101d88601c04c1034141042980c2d101401511074080502d8191406540c8040240c03100d8000c4845505007800c4c14401c0d0305071001740c40d01007040c0360b0b40c401002d0f0081a68202c40b0040e4403404855400003104d41c06140501d4015034107448450506211482c1030354660486451035030440381940d51303c0392581e50042060f003c1c3d4880c52006803034002d00e40303043c081c084058110000307890721b00c04150903aa800156280c0c0c003075030030301d44840d203410910803840c0a4016074180043c03500c0380603007a400700400883ca225240480d5801c46031140ea03915002c0356a80c40035a0b007560805810800c0c10f001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 170617347 1250 170616097 170616107
    0x5040c0e0c19050d32061201110406170c1206012c010207050604030515100e010902180906060405060a03060e090a02091006050d09060b0307030c1707030209070315031e03120c020706 80
    0x12200006011016104811100231b0135605029200702c010280041c080c4015a00101c9d040f8500f8008a03001c0502e1400c1c0c5200105841030601d01100792441c500000c040340c2c0308401c6504410825500e07440c9090310040c21480c1d100201d00454050b000701640880d2608100381601e007100c0e000401491118041d80300d041e0145c030041e15a403001c24181601103040c20403000704c0c60090031102030040e5100f086280c0020701296aa075001d1003024014140252039568000b6101907641c1100d0441c2e0304d07484040150020041039000410704c01e034800820291460215010907045e000b541c06940ca86c0d585070009000045d40d0190b000800c200f0300c944802c206003548507404080c4107000c005001c0c4404000245004815442111004800f100521100c1c003c1e92070003200084c5a001002100e0450340042d8050400070503041c2059a47d00f001840403c41c040c151008680003018066040c498400c80c020740116180b00b940030031048018031514a21038810303100003c00503805004418101102150 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 170618597 1250 170617347 170617351
    0x2a2a090109050403110601030803100503011a0907050c1209040b030307171b1005040201021204140d0c0b03070507030f0e060a080903190c0c0905040c0e0c19050d32 72
    0x1041002c001221704502d042001402d0285002d100e8060300c1c3e160040c2d10f08680041600041d0099040024070420504810f00740841d504045410413000e980d401d0045503940503040340d450175442100c80c00d12092020000808815070305a078240140b61000c002e160b0740303100d440341c000c00041800442160031541c80000e01001014500442601c140307030b000043c03074151088000401c866454091008541c0c0400580c4820b070400c030749240c01c0601d082010542140310f008001d002300b00e404000c00030450340e080100090612490110740b01d04006400030115040070034100c000ca0905940c1803582c81c05840521500c440050002d460484001d02c1142c400345e0191034800544020300202c0700c00b040d10400880050071941d15980401c81e04d04040030300f0000e0707034041601076160a0074000814030b56050041500d10483d0300d4603003512044607180c01d0713102c1e00c01c15060007030090709410140d0340d03c8802072195450310340080c080c004185180702c98030004021511849121141880306102c00d1510760340d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 170619847 1250 170618597 170618603
    0x80103020a151403090d18230301020c01020c071802030f15030109050d121401060801031e050304180f0b010203031501030e06160f0e0d06022a2a0901090504 69
    0x1148103c030b03c1280034260401e84910940b0b030050301040f1070480e1f10261a4114403126120340381114600700c032586090172105030405023440c0c00c00c05038003561000d404a8144001110003152303103031714072401035480300c2d10f6002e003007480c0c0000c1c0f502500c41d4881d4000d40780500319601d80c194503a29002401441080b41c5c1c9650703a015500c625602000c5071042c080381090041e55285c0410f441c0703800310f54200301c90708002c0c07020184100b0b500520919600c030f071001d4107480c1d02440c0417051240c4e04420035040d2440c4400101548400140032450b1251440c0d024480e02840790244185c0f001242e200046d513144020b0a40168001d10005c0d06500544445050804043c10002660101445103d081c000c1c100e0f0315400c024035a4a91810b290f41c800c150b02228445490b0200c0b00e0043c640025800300c024910140030290027082e100d090202c000e040040030031070003404c41c08003005d241009445510f10548915a800040044484000e01190403480c0d17100003010103039147c0c00d03c03009000900c40a0026 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 170621097 1250 170619847 170619857
    0x6011209120207090b01032a0203040306020f040f090c020a0209060d050102041d0702060c0304061a0409060c09060e060d0e1e100b0109050105070308062409040507080103020a15 78
    0x384042165011101080c103100d50281581070b0400c00040b041e01d0190340c0050405140c40c0d810fa414001c1e0031245000500081180102907851960480c91401281c1000d40718500c0064203503195100030b4014022100c994144602d10f035030390032450045070903105509000d80c00c198044001840c0440d020781e80064004c0044107849030544031142243c20503000050214110f440b40c0460000e45400c1c0c45d0300000a2008104032b11b050b103081e06e458080503000030091074072201c0358a06d6131510100c0f00d203004805082049494601d0414402502c100c112400108040302004140e080c8113003080c000c46040039040910340000e60341114010b03c6200d00d0380c8120700454814411007240c1801642e2001c854000400b11001007001d0003044404811480341481040342080021341d0704203065074001030301401c0500b0302d035544802103030201d0803508007240001c405d2091055032a004501070140144140c500304450358800f40f00b030710388020a0001a600a09003003040041c0f10001100c90305c51140d500d41 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 170622347 1250 170621097 170621111
    0x30204080f15010807061205090102091807080c03010b0a0c020f0d0f0b0105040203131101020a0506010b04090b2b110d12030f15051203040b0307031d011103060112 72
    0x9001d00341031000c5a06046a000500c0d000d00c0c22035040e8406001d050603201610043d4076041019014580b05400d4070496504d5600141000c8003c5d0306842c84848042d00700050300c6c600d84580d481c241c41c22241800402d41500c0803c404500c1c0710152416035000c512482c2c82c12040c40b9050380c051140305000c90b803203019492009c02d00e846941c04044810f10807220b18010041038a0701c2000624160402801903105004110248000f0170340004042c0d00240000c0141c20030100403402c0c9260004040c0c032a2007007074000074060340d9810041c030855441c0d4108001e080b251004000e140c5c10060524100c10181d181162000a800ba1540101c9446694102c0b00101200080381704510b0010080c2c07000c9901d0401076001c00e4160062100d5103039561002c00a51103542640c20850341c803406040d02074658038840c07014400080086074041d113040100355032280340000300200074100060b20185179900000a207500e4400500441440502d003603150360075591404011621a070891a1a0781045c0d01c0d228 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 170623597 1250 170622347 170622359
    0xc1524060c010e0303220b040807020d05250501090503060a05100e07030c080c03040209040809030709020c070305010b061606110906070b010e150d02040e0a0503040e101a19030204 79
    0x11600303d50454040140d40c4034540542c51925000003110300e2402103005102e10340010701c2c513501c6564091b600590150719400c5600200e146104035000040c103500c04c9988102e422082c12100b069400e1829144403202c0d621100110350308809841072a8240d0f002901080301d500040c0c00c9642d000002c120410704059032009200c08800c42940c0d80340c0803941e00d0540500156100d0f0003142e101c0d90400a0718a18102070303000c144010001080507095510100e440109a50203109943c010904248195183e545854005803950594071040301c0961a1a146140c9820868242c1d00d0004480d04852000900ca45402c0d01500b1340301c12081da406030400032109140d8410016010440c0560740c9030045605100381c048503100098024812151480740c41021950b400c040c07007560300d5050f18041341c098454550f562528080001c000c0090101240c08140e074816040c120344104c0542116169203a690b2802c0041880b000d150518400b10401111f044c0411440d1068000d00d4240b03401850305544003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 170624847 1250 170623597 170623601
    0x1410060839040503100e0d2307060506130608120d0b150c0706090f170a080c0a03032012040f060c03020414060f04051c080406050c1524060c01 63
    0x1080310700444400715090020b81000c10860303510000c01ca20404c405140340091035510440c4080350380410609440d4a43c641740310740c000340d03200002c0c1442180c40e41c0561030540c1c05803a045811074000c0c280d0300120992043c080c01480100c43c141301c040c09000c4c000b001e04e01c00d80d40c040883e0005c819207600d070224045d2102004aa1400c002c040400d8407404182c103110f043c03c0d410b41c001410000b100000703100c02600c0301503c0e000c5854100c412200d8044c2c2d0462142005070755200a05504004100714a9548010403e00e5a035880303580c0400c80c140000071841c2031000c560404202e603c0e414403442112403c0c1040d031980190050702058800310050351001c055495803c130020000c0e0f0003043c10454061401204101d5450823115a810060050b2050905014611842d40301d40031505401c480461100d05c1c5800132600b1013542d9a5582c0c07038070030107400c80c2c2c4000700000345442564807020084030100c08141c014180307038040804450441c0305402640502400f0a13501182c10809031201100034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 170626097 1250 170624847 170624941
    0x911061b0a03030e0d030911040e010b040e01060303020f07030c030204180f063204080a140a08150409050d05030c0904061d0615030604110d0c020114100608 69
    0x3d07a0302184c1c8150001c5400c0c02c00070502c0012042c107045c107a100001401c030a003a0440c804041d940010b000040c150b001d030141901100140d0028074204541c0b203020720640200d07040e00d000341c003290382c070b4400d003615030356500c3e5a440060418020b0500901c010324242d0403150002c138985600703030100000e44e1030b000311005a10034101c0d0903540e14121090f00e10350211860040c0c0c603460f100c0080441d100030314800c07107a070002c00090400a0004440c94014000c8c035051400c014040040d540b1849645000f1707019030000c0c0c50ba803200c0343c0303441240d16081ca054002c0700589503009002c0d10303400100e500140c60540014064020840c000d000014498641e4401d2a0090101e80c144010040807546903240780003010700420b00941c1c2c0a000c000e00303109880100d9402c644142d40014642c202c2074403607112030245991403920242461001c4c40482d0341500140304c044d900c0d9166900c0390720b03131030715100c40034001d0703c070b0b031808550340d9000034185c2d510f102145c2e180803070714000d80b2000031185083d4442c41c000c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 170627347 1250 170626097 170626103
    0x60b0301020319110906030c0318060405011a0d03120905010f0f02030a110a0813080d0903051e090a090b0d020409080a030e0309011d0406181a040911061b0a 69
    0xc2403940750003680c3c450003071601003000c0400ea94680b500e1500800d11610004140030000c0c1c0d400800706124200fa20980a103000302d29041da85641020b1038958041c290905c0850318030807250300403a56138540189070000f01549521845022805100448040d02d0ba000c0151004d55889849801895442c000d00c03400045800006a1300d04d0310311070b0081120448a9180c9480c4400c0c0003d9003202e401610054014030099100782c010340c0589030422080c81a040b101d18668240314510040641150240041e500c200030700d800807c1c078501c0b00c4604c1b4000c81e102280e0210404104005000395a80500603451010b41000c42141542d000300b4256843c9103402c641d0508000f0f015408240d0601c1808040103c010295240981260008250032418540102d40c007044043c4d0740c00720381d1198003000007024600c00086c400d0300d55404410003842ea4011101c07c0000901c0110003501e05489080d00c4141e101c1000c2120b20101020b01403941c00c140400c1410004c84615007d010008000d19106c440c4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 170628597 1250 170627347 170627371
    0xf15080c04180c030b0c0715050121050607030f06030503070506011e0506030106051605010903080601020d05070c0618090603080a11061302061602041104050307230d060b03010203 79
    0x40d8405010488001140000c0754403001c0c090240002c52210894003102d4008410740d5854650100c2080644503080c002040013644803060045180c481d08014100c440145500f9841001c4c1284001244e07880c0ca0002c16903045840024400341c041d40c81205c007554070a0f00061450307100d13610203107198402c1105030b810780e1280e0010460504640b403845000c002c00840104100e1801001c69035600040c007900f024001c0101e00e480101005854800d460358011009100030821401d000d040c2100c02d40711341d03006001303035459280c003140100300320744a50f94000c449a05052900700102c5001c1d6651000f5409c3e160300c04000100103110f8050900a0750181e030b402940c031004010301424540d002d030b080e403029800c00310805c4180b04034005610340b05d0341c05803002661181581c1d030010607020380c1d83c3c0095100d490103080c1c501c0c000008003d031054034810340031900e103d0740710300c00e482000b4642c000075018414032084009a0341480b08400400a1041402050300c0054000182c266001182c40c454908 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 170629847 1250 170628597 170628613
    0x30206040815060102030c070303030902060d1a09010902090a150e0603040308070e0a030b280213080c1815040f020a050d0f05070507020d140105090303180106050d060f1508 76
    0x110403100d00310f8210f8001d000035883c02000001c5652030313140f548005006d1580e42d210342c006545070f107400c441d0300d0b00700f0385030401180b1008800007102c481c84e80b501501a81111001207100a00c034400c03200d0800e001840340301c038140f81881c00c1000f1502034500008009000588000b907480c1c0380c000e50b0240d071194070394040d00e1134440701c000c080d082801980e91040c0d8000000300049180c1540450b00281030000c04504602d02e0b451101d801c2420380040c1000e5880050807040d1103103680076500070317110401c1c01d840240c44a00304000d54158181580180c0040031004035807030300e9842c120215041c6000d0070109190301400345050403038120201400101e4400540c9a0441007144120000070750450001c11860500980c02840380c0070750300d4000d001e4126042404148900780c08096444580305000b44118a44100201c0d1280c1068035490004134685400c102240c0060040005503400a440c0d800104160384482c0e0140002540c40317071000c0d035100e5000341445005501c1102420300c500c020502c030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 170631097 1250 170629847 170629873
    0x181b080d080a140609010b0a1e09050906151c0e01021306170c0a0f0203041707030309080715030504030c05060711070b030105091308040e04110f010201181b0302060408 74
    0x303240d0f44503d0400e0350840c0f50400116568110a2a0544809a84003615289812801c0da1002030740c907501d14061002c239600001182d40b00c3e0b41a41a11010341c3c020300d00703846074030502000c41400c1b100824114014085d82c5801c440140058400c800842d4010840302c503e4080a4226480034410003116910b000051111036000b440f0900340c08001031844101d840d001506a02074010704440304104400c080c502102c0e18420000c0c6da001d0804c0d1203051760070310461103080c0d9480ca22480102d0204000c3c4400286080020690a0460300c82c2c105049004003d2402180103010080048040c40030800c004000b290080019500c12000c40d100e030316541030b80340a021329090310b5510208900e182000140015141d10702040e810259441444031524850300e01039109005580000200000c800d0400091084c0c80050303c1450700b09a490000342d4441c817004900741c0340805c03455400c3c040e028800c3d5000510145110010482e07004d40303c1c017055120741c00100c0c1030b030155000042c568407055019042c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 170632347 1250 170631097 170631101
    0x901030209130e062409061504030204111806040b040b03060406080102070308070219020102120d020f16060c09061d030c041409060a0903090308070512030a020d0c0201181b080d080a 80
    0x59040c0c1124491710b90900440000c090507001482c4600a0b640c020b01840307049210410340d0007a507030003081403044224943c071070240c0e60020441481218052696401c06080140032030341511102c8801c180b4081c20440f07404c880da40094103898000d03a80310000241e290082c03001c2d1a10610036075407003c1c64105080c1c001e10705070300c149442e11415481343c0c0300001070703070006070f04800714050902941c1c4410351f1004080c001d00170b16160390b0540c2000506841214103030850117803c284150400c02c01100c0c07010003151107010030f00900300801c0d00050a20341200c0001240410898010100d40c0403115610114040d14061280c4114850000c0c0611202140910440c1d80c000707a22070081040e08c0a80d14010030000c06803102034254200061002d050240621040c1d003a844400e2400c1daa80c104100001c00a5100309401b19400b4903020f0035281d03043c818020900e61054910055041c10150303211f01040c801421410010a14040d0f40000e4100c420f12910301440029100c012040c81c01c0082d0b001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 170633597 1250 170632347 170632381
    0x901030f0509150a02070b1e0106081603020306030106030602040605040f08210a1e17180705010e0f03120c12030c070605280c0f050f0901030209130e06 67
    0x5020709000800c0881900002d42d680b04a02c8001d080301c041d02d500e54040c00034840d10401924004c001c20030003080701c1c0c00019105144441c01241070480c0c0c0c3e6500c040b14028010303503010091516901d144414580b00307401660708900c0041c000107406960b607036034008a0f40261310890114401180c1088141101003641d0300815031a4060447c001811508144220a14480c6801c110021903400382d101e100c0c0400307041c0d00d00e480500c80c801100160700642070a4151a00b0007141c12050009a4070241000140d0f4200682c280103012580c00c103801940e2a4038a0840240c000079a03064903062a41d0070400c149141000115150780c50420b04405030600c46d212450f00d0880c1d40800501010503d04411504880c0e00280000b86549410308422041e02e94010750b00e1103030501d40084040040a42c1c481c0300300240b43e4032a0074801d0300448040d0b400d4060f887d00e081e241c1b40140558216540a50003c01c60080010541c8404a0002c0500d0080703030031515040b140e56010400708031210603103802c60b030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 170634847 1250 170633597 170633621
    0x91110020c1305040c18020306120c090601051b060f0402010f0c051213050904051606140d09050111040801090506010909021e0a090207030c050105010f03050d0305090309040908090103 81
    0x1101e6511080c002c40c0d030a100c0300c00c1144070340e0394800c000380520242d8007400300508a6841d1090484485010402c080c0d041135400d11312402c01c01440000340030001070000e040240c080c0c90b41201d80e94040054402e0b4014400d5404510580c200010200a00744000e601c0741c82d68001009050070140001842000700d42103040a101040d10288080391002580943d024400e410150b500c001078002141150050360140e40c0140c80002030004209021880411340e03106502010303941070b0b50b0b410481d003090307441d180485504010080b09074000225082142400d0061001003a404e003213182c0442c460b030040c0d2050500d0f95640e1180340401c20306121540c01007128a030280f208036029000204070114042e1003090b510100d8600024980313962012100800440f4030840d101c0e0881d0070060900600387e003003218903501c0c003400404c2031942ea00038141070700d40000c0184991618000c080d0000c01d0060588105840103114101144e5034500840701d80c0751258130015142c034002d07800075080d0b4820701000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 170636097 1250 170634847 170634853
    0x509100203010b12090c150304110f0a0911070c0b0d0c02071404021606240f1208030421050c060a05091908040e0a0606020709020c0307121209111002 66
    0x400c01c142000c01030701c55011081a0424081d114a5001791400200240071904042c00c00134841b00314580c4d0018500c614010030409018115038020450919029400580d000d1110300b000d024140c1507520032603452400b82c940310324000c110340b515010f03450540d0000c0b07100200001c038600a500310f80600580011140024803005061500f40305500701c0030042540903e60220b03078061950544c415a820302a00203404020841d003450701e540e620241d10525440840c0210b0700083c01401c00845501159001c0000c071000c01115a1020695400a0400c0d03a00000c00c01c0005880541001807900b50304864442c02d666190154203103040800c02000040300501c0e0608103c0c4400012030051140070403010854400001442c00007440d01954101040108820003000020f0b40c11ba40a801a140c880d000c9800c40e82d0349080210582c485e800a4a220b074009004801c00500000e900c017040340a10b0500c52000a40303050194203c4034440e2017591115202c0e4540601c6080200c141e080c503060705e01c06 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 170637347 1250 170636097 170636099
    0x703031808070e1905090f0c010e030d08040c0308030a050a0b12060c0a090b0708210403090302090711010507020109030f0509090c09010c021804050c0f1e0102160603050910020301 79
    0x9665242e0366540304006401c01c06500043c3c01c07003410484d442d28500c02220400603410701221480d83e42c0b4482e244042c8620035401c04012542c0100501e07865001c0c000c0003804880c001c440c04540011004c0c108494030000304001000052019001c1c5100d101c49400000315440d09030400e2040d28900401c07503000c8d540700000d004a08001151969000c1d021142869071444d04d10b8045400313502a0784039020600c0c010032440c0c204950600101010240b00d8015020003051501035071307030340d41e09840040c0410015a4100014241405810307441410f40c14000c041011031b243c0542500d01c1240c0000060355500d0b042420140c0013007504030140340b40c0c9083c0e0304084001c0003041a000c2e01030840010001e010810b00c1403603115000c00c082c040d03406444e044e80c1d280c208100c049208000c2d20700311003a0060203580d0400d0700740802e4100b038109c00100b800078800c00300345802101107096602ca078114001c45a00800c800d0300315034500d004001c19540050781e49010884242812510410003000900400c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 170638597 1250 170637347 170637359
    0x90901050a110702030a022b050f070603020c030301090f09020d0308040501140c09040513020d08040602150c091212041e05090903041703220905090c031009030e0d0507030318 77
    0x20f1880c400a034103991501c61544221140303070030030074030600c08c1c2c90071100203a08004209022929040544c0c0220841d40050b4480c40d0035002c1c0d016141113606954000e1004100a086c15040040f8034041d00400292028164004c5503020444090580203c5c0c1580c0030f01c000c0000c01d22509898440240c8483c2c402d04006446c0e1360140b060350720040c8540d4a59022400a00c01e1013417401200794024451a881940d500d403d4590f60803601c00d100150107042c031920301c0d620824150a03ca5003680007007501e441d00210400c5030040d60860181c00300d21a1128494001c031100c0e0041c00a0082c110080400075a480c3d06505000300c5034121134001e00d01f0b0020302078840d000000352001d4401c00b016200c524018003c0d514954041c1d070400041100c054000500c03074100c1c8040d001c09450710074030203014a0303889a0000c0e96414441d0744094251f80311155824100340d081d0b0004c03000707078428508603051500000c00640c003c003519000340d0759034004c000f04000300760f00b05a200141c0d200211007400500d280c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 170639847 1250 170638597 170638603
    0x5090105010c06020c011a0307090e070909231c0504030c031e0f0803040309060e010f080c0f070b01080c0a08060106030f020c0a0302010b0a0603110d0b01030605090901050a11070203 80
    0x84a45414400801000e800700f010b65015556050740342d100800c4060032150810401c001c071203071194001d00a14001056480103806201010b102c0c0310000d0020703506d031503569001410030402c01c3e625510340c000d100c4555800514841c12001d0450300600305981c820306240801c01c0c40c00da443c01444410003003000080c0808110701d08482d0001c5401c01003a920310242900e1728000900249888840048882000230003000795018034020740d16683c06540f02d000603908010125107041c00308620004a00d61503102c0d83c10f841d03200e031050120500300300f4204080c60030350300501011280c2d02c02800052204140c2000a130041217070403104092402d1030b2121164a4600601400c801c241c3c54033741d80d0002e110a0f40403244140420001c540d45202c00d420008e000700415881a8841c0000f40c1c80018201c2c840d0191301c1481252078031962821404101c0d441c02410240c25490500d0703103881b00050543e403603481591280d001c900c004241460540301100450f12480c03665003080c2401c0c450314001d40c80c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 170641097 1250 170639847 170639849
    0xb10030b090c0f040e15070302030a0b010c051e0c03030d020c0f070b0406110a0c08060a0c05192006010e100b1c1a1003020703020c06120402010c15050703050402010e0406050901 78
    0x19a000605400c01c0441281400c0e00300511484252002042c07111f41c69150340114070840b9100ca0030881c200c1030b00d0044074414034114002d46580d001e00d02a0249455614804038600710310000c0721400380c10745020038216001405004000c5034040380f042494071060084442008000e000b610740c139820325203121070f80e00450080204200d03042c8200040c2c102c082180d030305513036002800d035408180cad46c1d004a66105004c50b05001c9084c104401d6081080c040c0080d03540003071203000b0100d02810f018108490010007500380c21540c0d8041c9090903075071101070100d28040c00c007421501c60301d0f2911040b42d5042d10043d602c10045400c0802c04c102c80203840c00307200c55080100160106401c01000c920354401c51607159000d601030702e21805c00c3d000540650061520354465000d944068480d9020400c250094200c0c10502c00c0340180020019885268001016880340c0d0142c030390000c0c8160481c084860803241d0070b0200f81d0b200309100556801042095180d00d084500344185414400400c3e05a841 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 170642347 1250 170641097 170641099
    0x8010f0506040b090708042609010f0806090105060a030f0207080c0706020303010308120a0e07061107061d0108042a0e011203351005090903031b0706090b10030b090c0f 74
    0x10400100e003c00403400455000f108101410b070481c45404023030285560f00030100c0c54041a4403080700b52845014144035486204010700350a0366a20b00b1007840581c0c1c4c40403029900309507071000c051002c41d0340c0d0b1015010481c000c078102034642e07a405a419151441d04e030050310a56205100420026860f1011100000c203040043c0368241c4482e1010b4000d0100d41e030024a440c090b440003c00e11507400003c0252807020401101d265540c0c48900383c580c1d50001305019030844880d02c126059500510416400a100790840b09901c103011a100c1703215403000d40006594890306000300007052110060300d02610300302920781040b40965502600b5100852100410a481c5440c40000e0368005a040c0c00e40a03080c081d00502d516140e0012001d02205014a511600702036001c40c012030400416684120031060b10540480da0034061041035401c88541140c450b519034100350000381c020807081e80102c82031034404810f2070451a00454018008001c641ca580c40007002815aa50b0100c0c2c1040d0310340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 170643597 1250 170642347 170642357
    0x9030c0d05120a030e030d0c080604060f14060424020c011407060c0e040f0f05090a03021209040f020f0901020c010f09030312060902190906080601050406030b0a0f08010f0506040b0907 81
    0x100500354050311798a8941c8000f4003011032081c44400d0540c02c480c0500c9515a2402656510700007081308a41003030084c0b4001d00e641c00414082140740c00e007094800400203020504044d50380004440c000b00c035a040505004416140706c643c00e03010864166602e100342040c0003584c0040700d010805000d085006051192205520300055015010034120b4520192061003009441c03511240505244080810b01a140c0000543c544034003080340034071982e16a01800c0440030100b00620f89070410310407141c0c8250741c1c840d1100042500d03c001c1000103a070003070503034403401084006410000030039062030501c0001074410100940c0224504140d030f03070608040080c4d0821242e1a00100700f10382002e049144006a01143e5440307840d101100d02400b0340e642214039031594812070b0010001c0d510107002ca0000e01c024406140640c0004030010b0014100a40281c0c2e51051142138441c00d900c81545a5035500100082550501605074040c40541d028800143d0080c085150064024a0081089 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 170644847 1250 170643597 170643607
    0x12071e03030f0302040b0322060f140c04050d030f090810050603010b010c020307060c0311010222080d02120703020a050604060501091a0906040504050a05010c052809030303020d11040b09030c0d0512 87
    0x40c00232100c00106c0b54011004000c1040d01414000c02046200000002c000022000810140c40c010850b82940c0c40a030503406808600c3c3c0d8240e034040c800d64500d1062005103c00800e109400b00500f44c0d040031403007408a6142407110505003107800d1a6941810008054112009a103002580904507107207841c1842c010220b80c141181c010720f0350100c65025500000d22004044074071400701080d0150240003542c0d50b070b901c410f002d07a00e5010507502e43c003503042800403003080d00c41900034242c10b50003401601c00b2110641e90b0a4109030b0115021a03502e5076403001401038080a11550038042ea01a0b0f00d80680944400000c1d070f10a801004a8415a2100005000c0060a02004004940c4040248048185814060036640081c1c11003081d0b040f2181080180c41c0c0035030031001c0c800d5800d8980b101981d041d0340341180698810041c10340450b403907000301504100010f000303100815403802c41c0c03601d032880c00003018200b094418881d44540d080c244030101040d40416030034411001020350a46d60 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 170646097 1250 170644847 170644891
    0x5060f130605040e030304050601060f02060703050402150c070602102d0b03070806070e0603010e06090703020f040603050a0c030207021305040c0f0e19180212071e03030f0302040b03 80
    0x9000d1a4004a070414101502c4d02c41c03400700003010710300580c032800c03d1781c0c010380c1c07220021120902c24180d2100180d0284010072440e901035840b540c1c1150002d06071902c10790360032500a039554000e00c0414641d0b0b200400401c8460741c14480d05c03100541e400000c2c00724112900182e000052143e14089210b50f811140b41008800d56200284086010707081d18105030781ca89440351a442d0880e8407c0204015940e040c8451402360708590589400711b0217030301141c44a00521000c1d50b001801601030580c00c0000c0c0c083c00d050000075000070711341c44da40414103145c1200040150340031845080d05060041c00742d0740059641e10415014426690f000103a10f80d03450604405010440c0d0084500740c95150021410042186d0544d201d05003103403128240b0381c06027140b8412144203000d281c5004100c1c01c074810040c0b40442203902c03c0c0041604a42075251200c609801160300c9078200314031f2912903042007040680041c20021038880c0c0d414110300f807078035140742e0075028840280451001c0001002003100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 170647347 1250 170646097 170646101
    0x714031f230405060105061201091a0a0807051f0f0f090f06030b01031d0606010e0f0a06050403020108221e0f080c010f06080d0e030a1712060405060f13 67
    0xc80c10403200007030380181c001001e12484001c2030b903094845015060001c1142c1c10980c0c00c031204021140003030303011030b841d00e2541c200828074450f0030107081c0d5007035540000c00d644007030025020701443c0002c0c0c154035280404002c0c100d440421180c12406102005c1c4a46c55002010340b00c162400d4100038004042010080795800c0d02c54020b000c15a14154021030307850303815848041c4a04003a20108081a0202406540044032800050183d40a040081c5040d403252404c00f0741000060b00c500201307044080000d0040200d078004c0c40010700b010404006540c0c0c40402c140d001030700b03440c15080c0c03036602c220031032042c81821f00d007d0710a000341040000035042400503940002e800c90ba160600c0c81e411b2401201c0f41e0b0102444808660070b10304404030348040f0744690400c9800b110010510b556400b4010341d001e142126209515010301300041011596621440600152040c600c99540c0e14441381d030390740a80b0107048130b4011441c200801541e6280c11203c00c1d144801111101c034100c0801040c140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 170648597 1250 170647347 170647361
    0x41a1c08190504030c081b010507120f0e0901080102030906102103090312020105090c0a0b090906041119090f06021510080304030507090605060a050d0e1911030714031f 74
    0x101420341000061100003c5080c981f405402c00030025101001c01c01101c05000c0e407039018000c452142e890b056154010500700080103018289592000940c1c0c0000d00800c40c243d0201c078180c0d40000c2048901030041c80b1007540305401c024240c070701c9030400002c140d5440005182c81e00f40c20707035840128240342c0170f0f1011400955101000941040308000024042d003001d0354004043d108020003410107240203c8404103555081d000c0314144a401c0040200b803d0015000a41080d500c80d403541001c41d0410060200c00902d43c90039225502d6054002d140d100c041e4000c0c640d80702260400c2c0301056010945050091120304181501c0e1242000d41010340104d520414852000060000030002c0118454080347c0c06a42c0412004e580e070300504c4241e110700364800000038410880d51a0041d42c0c1d50042035003500232021100410b012001008504480c10400e58100380b2141c1710000f6440e0401600000d403c420354110103154440001c20340c0c0f14800116070030f40c64050180c0045001f05907100b46 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 170649847 1250 170648597 170648603
    0x705060705030d022215020705013b030a1b0b030115030f1b0e030f0606090c071115070203010e010618090303090b010611120f040b0307020a02041a1c0819050403 71
    0x244801b6a14006243d4070030314000c005015019550b00001c03c2c0d8050f00d00420151291598484001d2021540d01c08201225107074406a0355000e0221146407810400e00040e030b403103880301700084003503044031600c0c04655900040d0009801c0006101d074400c2c0203c0400d0300b01040c10f000ca41d49449103207000140141181010081d042d040c43c140f0030b01c1d0700401a105851050f0290382d041c1820101294403014201c401c581c05c610040046105844400000c0451078010b03c40001485038120001c0c0c45001e02007040f8200920115004080d8502840380821000b1820020400c440ca8035040c11a0444000141c001c0543d58909403806e05010b5000b80c4c62241c0d110600400c6503844c2c0074090000c01c4159030540c8284a490101c4900348201400c40d2040c1c844bd66a107424246020f01140345a40010880021030168181e03200c0143c5603030140180740d0722503480100180480c1c0c0d0901259aa0101841c513034a00e007954a02c1c0420400812103402414a0021519070550450150f81c1840303194002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 170651097 1250 170649847 170649907
    0x207060f0516060b120c10111609050402040e031905030a0e0f010c0305090703031407060624020c0303040b090405090a120804030212030126100603030c050705060705030d02 76
    0x2420805694800c44d0400d100712109884014905212039403669425034440e0803207000505564054090302500101401c120704542c004146460030004165850b40400300301600c41083c03000314602801181c02511000000b5410804000f08400210041034801d0051010000c003141d005a034940001000c0706c00b2004076822034411144007030003031510041c684e0010740f8002c0401c2c8244000304100342184d8040c1d444068076440a26801e032140c0c41100100d5074580d8840740000d03401b800c1801c41d0740d01c804ca826417003a403a524079800b83c180709070410394503c250810002442038242e07520a8403400d80054038006203c0d501c10317400702c0c64000001005031544a05a1210307800580c41044140715902c01d500340c5040c807200c1010001580000e0051b041a6207a01580703001c500300c14107551040d0000c14049416407403003101d0110841c2d8030b84d042500000d40240101051100c1008000b00910741501d0651515500e0b0702c400d0340ba4012610500499030700043c000000c840042c0100c9070030403e84d036503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 170652347 1250 170651097 170651137
    0x3030609060f24050a110309120c0a1502100f0605090c1e030c070b060a03140a140304030206220504230a1407140c07030c0e090a030207060f05 63
    0xa60800441c51250299940c0f03450720400c02d211a4241d01050321005403605410b0100c0355a041d501d20750074070310b0062903201c20301c114413071035448003000d452091200c0301a01080f2000303401d02050760110f4220701400b40c1500e180000c1c06900042032417800c20300c00340000d94582d110300203902414880c1e1000307500203010310500c115995003000a0018031800b035040110101028000c45040c0022030b0100b00340142404000003048854600c00e038850b000070402c60419890b40c0c2d413241c9210003c59561295440b40a6842c108405442d100e00d402001c04001d50615181d54001081403054800313101c01000c0419410340c0f2940b00d021503202400f8020070501c104400704040090a240e140007003480380b241000860160076080c41076010b00c8102800005940c1e407106000e941500307445602551211040050b01100c1006000301c0d8003031486480101c0e083c46c504484480521005006100d0681080c1c00304c10011380c001904904072201401c160b03071090700080c015150b50141c1d000e821110114803e0b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 170653597 1250 170652347 170652359
    0xd0605010e0718030302030304151404051e0606060301050111030d0204060210050a1a0f01020309060d23010e070f0c080c0120070503071e0203030412050d0f020c0d0303060906 77
    0x10207544140000ea50f1801040360003070280c15220403a100c0640542c20400c08076001c00c481c000600c2c0d2a000618001c50398034a070410101c2c14072000c0f50141c6d03568000c00c26040d030182100346100c98400c1741038002c0200f03003001000221288410300c1040e06001000c0d040c0c0c601720300c1c18402d84003002e503036950441d1215a5144083d4442c0002c569682006161400141c1c25103800e01c00c1090b40ca03420301f042420030b110102840501c0420800c598150310046c0032800a541c1c581000300b1440c26139680200e8213014107010001200d05840a000001c03608030014000302d0f0032032111f81e500181514007088005c9500001b581c220703c1401c005800550000f131090340c0c00c20150001e40b0821000c810b210030024450500f00e00502032000000c106800420895010400d04000303400300c5c07440c00c1c444030b21042141e03002a140d82e001da804104002c08001c00c420030301509125840c84004641001540d440074100300948440c0c0030400a07110b04d0700e5036903110901d0311030340c44600904584481085001e031100e07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 170654847 1250 170653597 170653619
    0x1602010b12060106140a0e1011010c200106050d2d05160501020c0307060c061814010f0203040b0a0c020a06021b0c030106060503010b281205130b150d060501 69
    0x10081c800828605420780001401708030446a0a4a81e85d503442d00c4403009004010f070440030b0f60300b001d08120300c201005071110380038441d410003201e154459914401c0f41c54892209041c82c1d15000e8410f0345405000c01841c0c84001100c0419030b0301001044140c0c0c1300c0d003c09980042441460300096542d201080f040203c0065000c441005a45110901c20342c0c800049a0303a5651904194050700181400c2140f90700030b00c14000003521820307010a01120802c1c110010a02e00101647c032007031891040310740414203110f52128280c4002042d403075460982c8400b070100c07801804000e52a44c0e01e04280c45020310038041e448002c2e900040a550307851040340e00c01550000f1103050307c4640205040342c001445c0501ca80d40441c0d103140c403014116846d0040d210302d190050403008155803002c42091040c03070810f01c0d0107900240d45444102c98111090305083c00c0300d0000b40002d004000841c07280c408242d1010156a0104004000040c540ea0041c040b5a1001861030002c15044c14140045074115101e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 170656097 1250 170654847 170654849
    0x30c0d140a03120b0406080c0111010f0c0c0201080c030601140702033a020a020d1b031205030109050601030203130611160b01060e030a08030112020a150909060506040e1602010b120601 81
    0x703c0030500480011200b040100c03505441030f081ca035808050422242c1d4001e400c4140740d8a02c0e500006100c2c50100042000c2d203aa6500800005103076214200c210b41c0c00c015082e402c1940d000703186e0b08520345100060812002c12800e1142c048000c5030440071980c0c1008100002102c1d592201080c1451805220883c1c41200003034002c0c81d040407000303420920014014180039001005401c600d051034071018011401d002d21014a185108000300c080b40400440552809103640c800c5e999625090846040b00c501600c024105030042092010559141025148090704a800000c0c0d11848887c0714100d07204e542c80d00e629410500e03010806000803481118102c50150b1500040c4072034031420107440e10889a001088103e0900060280010300100380203002c0c4060100c0392a541c651003441e06000f010140c02c070000301a1724091101c40014007507000289030603074225003003c1c00d016030001c05840c0104141401c50381340c51410019807003500810701c0c02c9800b8040e002480400e0b8192030300c44100b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 170657347 1250 170656097 170656127
    0x150103020301110f0d090c151710050d03080a2003040203060717070e031603060b0a06050c12092806020d0806090403080711010501060c06060b09030c0d140a03 70
    0x181c403006048180c114001c540300030504c0c9500501d44114051080024a000b5000f62001d0f100c0210108130240c1515280720610f845d0740b00c1420300c1010041c04400c441c0d008103040300851814908211a4854550481d00190f240c10944000e41d036881c401030082c00b1310000c3c2c8911041c0ba0303540b260b5109800008600981c002e5003629215520b580090b82c10b190848000041d4a0941e000540c1d0301e440751060854501008080e02c090342c0d440054400028141c3c1c20559103282d0303030000d0440500e01031081500810190130903030304008002d081c01361100b1214145450f40100001e940420390b96030f44c007000198003a8240c3d40c10700190f00711b00d2125000c1e540070721009845404130b080025401501d0a0f0712503180103100003026511554219418400509540e0074050070a07840614848203015050103401103940300c4444204504104081c3c0b19a42d0081408201c10020780722036407008560120014000d80e40698003008078500004500410481525a402000507076070806900c0106d0700c800e915 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 170658597 1250 170657347 170657351
    0x3020406020609031e0f2b05070c0312020c0a050a0809010828090203010209041410050105030115030207140f03071a0601080103150e0f0d0305090303010e070c080c150103020301 78
    0xa11079541c2a6030f8411405c0140707045005030040d0812405502c01845008190400c240c03d0250140c49440c0404884107110403085050b4841c000c0c1e21020b224140d4854043d251282c003040e003d48001d0441241c07403d0303c1c19040e400141444928104016024070f25612900700c41d03151051f4145019181c101c640e60301e002581d4040400c10440205010601c0007041d0942c002054074040202001080460800c0340c140d50203103c81e4460303236220301c0350b050b07151a07001ca01241850408030750036514007650030031814032605000601003a4400400d444181070716040c0180c0d07800c6a4142010300d0304030561024924842c08180d881c05034008405401c60131321901041e0240c42141d0020307000080200d4104d030004205100400c00701315901d004100e10714200f0b40006048a0a584c0a8206140c2403456016a4410710341045119410300c80e981e8010694005181554144058050310000240c40c0c0020800d0611060050000708000c0b14041c106030421030302c04e801c082c001010745040c2484182d120354 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 170659847 1250 170658597 170658601
    0x207121208072c1813050d14090d0c0f0b090103060603060e0f10182307140a12051807080c010c03200604051005061906031a0a06030204060206 63
    0xf8020501c1c0e1201000e078900aa20400f500ba001d0003000b140321a245602c460710200d158240300c0d100d0100b03402070410603280c4c1c1000186003405850031440da00c1c44001c0140389080212020005416150142412680e40035415028203008000d544650804458a6200000000c111600b58024444814280c03800d1000f590b903481c0c190115260307841000e01040208000800f191111003089a2095070700d14210074003a10740c800c4e0080a9a060454100e403580d820310180c4a02c1982c80c5503c2c0601c5502a07200640340025004040900603040c003a0b16000104d37001e591140941007001000800701020459440d007400002088003403d64070038a603025811000c544ca0002140076200000b044c0c480b1410085a0703502281c8801c000c6e06a22080745980b20000040e807001c1c007265001d5070241c0c0c001d180010b07a40408104a80000c1c211510922100e01840050f00381c1402000481c0c41078180011099038020740509009035404401d580941d50354008500e42d901603001d007080d600c05500300e805603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 170661097 1250 170659847 170659861
    0x1503091c0c1b15030e1203010308120a0b040903030506131a0f18040c031506030f0209041109040c080d14030c09030a0807030e130b010f0f0207121208 66
    0xc0c101030162800000d84240c070340c8000c141c010207501480001c4921050480d40c1d030350102245500032803c0e40c00000d4481d10742c000904810400c903010b420041c8005480c40d45503075689507007071044010366000c0c4d40000000650301005640119560480030304184041c2800e440c0040051108550a42c0300b50480444130b43e846155124200c10b403403580c10114442c0010720704100f6454034000401c0c0c0d214101c01c2c040324031268404004d6000718810040307103002c3c5003145043c1d40084100815010a2031914000f0400314194011a400840d0140da00b00c0e0309480342d00380151402000500e107a001041001401300f0040f4052025044414503c140c40d06003402041c00c45503541c0340c400c0182c0360031041c00070030384541101004001e01440101220101d0409030f03940c40c029004400c0a80100303007c00c43e460344900340300c0604202205444410803081d03654500107018128208550340810040242070a4614001c1262001800c05201030302c1b43c2ca402c41c5400075418192a00c40e000142d0103401040030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 170662347 1250 170661097 170661133
    0x405030d0501080a0b01050913051b040605100507030507020619021b0301020a081803120a0207060f0b01120f020d0603081b1c081e0106020f01050108070f0b07060b150309 75
    0x5982c0e00180d411106c0c0d00c0e0904000c54040050513200c1e4841300f030000b220008100704071050020b0030440003103079007070240e0382004211121580818043c5c0c0c0300880d003051a0b54001c080721000c66250070802d03103c4419002040c01401034a00d10000b007000743e004003074800d4001034003803100740002c42c0c0503039503414032030606081c1d016110503480443d81c039002146209001030120f547c000d04100c222824a504d96621644003001584c000034802d90000d4940280401c4d03003d8007191056241040c02162001d80000303001c102c945041c11001a9560143c212800d61a0116043c0f0b50542c4000d0042da0389a0400c030080713a100e484d8101250001c03100c80c070360681d4041071003c0309403000084200d0949200030103840142d00144cc103a22181141d6911003030340c904103407090113041180e0080083c0c01c0c1d01240542110410781292681ba40001c1c020410720203400c0541082d070f5102011551580d1030ba01e00000640458403109e580981010716501012100802440c4116041021290100345050410365 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 170663597 1250 170662347 170662363
    0x1505070f0506094e071b0b040f050d140102030a020a09050405060a150207030204050c040e1014040218040906201204060b010e130e070e2205150405030d050108 70
    0x5111350072540d00c00214001c00300307140e211020014085449500c1803000c0759190300c00b0030103c07030842c00d5424145000c040d00d1100e03c0585400c003080d07442c06080500103070400d41144900380c41042c80c21032080410410301c0300008040b29a2000755241d051860045010b900300c07660000000320901000600362506019450280030302420001005007000404400404520580c6040d4030640c02d000006071141d110340c2d481128102c08194546040400b4580458809040010003141d01c000074044011407107956035145404541c0143d03290810f10704080c0c0301ca50011002c0e03020340741200b1030b41400600c4e00580c50381c2080740000484101601c000c40098080d410020082c200b24600103800109141e1151106d1601410301f210303042c81c0440001c0030800c0928060795265200c103032080080c03104000d208050700c00d1081c2480c0742d10f0300c402404102b84203e8940050600c0c40c0e403c0c1e00602a0610811002440c001c20041c4030340f4103401e04540e42e81c090381d1075040d0707580b5190001600c041c010500c02 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 170664847 1250 170663597 170663653
    0x303050d0e1506060f073507050c09070c1e0201021207050a1704090c0f030506010c0201080621060412020706091202090a0605030a1b140a1505070f050609 68
    0x61032507260b00061000c117070030400e1001c0d64204e08010300008500c0104402e403d070070813410050007404842840701045200428200002107007800381d04009103000c900703280784c01c100781c80c0c1c00b5071039962000c121780300f85400c07a02620700f04542c03205651048001002400050003a005c45405180c01c0250491606c5011409001a04403d03010800140d428121200b0010840002810301e41c48803582400c80303000080010100b90b41c1080d540b0000d030980152603011000f4205865202c072140c0000e00444002051140300e030800402115180c16590010b0044020403022982d0a29007444c000c0c0001d1085034403000940b20b21600000d07240e129040c448169503220310014150141d41d420301030404805490b001011381c480300089002c1d1401c00138148a50b000c2ca8001941c1c480150102078041059008580100600b1140881580f55088074008440408420028501606804840502440030010a00c007180e81d4210300340000040c0143c040c66241c01500d40c4040070100044400d07000300380d40 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 170666097 1250 170664847 170664883
    0x5370c08030a0b0a09181704050a05010309142d01020f25080310030c050f0105032205030301060807030b03011a040e010209120a1415180a0b010303050d0e 68
    0x15181c1c881e10f41001d2401e260140044071165100c0c40d264081d50900340810007008960f14406080c840d4500c0001d000b00c4115140074600b60800d40429402c071201e01480b8145502d4000040400814101d140700e401700d40001e4441c80b06c1c1042c0d0844118940d14a0246074000002440310301140600c2103030f4112484107542031500f1011071a80100182805200c0e120343c03818000d250102c2d034800300444c82854007030171078501c060840c504500400d40c0c41e000180150320801d9180e100d41d82020880b03800401c0f00c488100c520b4041d01c5a403c0303d050102c0e0041980c08080000079885800c03100c243d0140542c1c0e01e05124038881401418203e441400002000f0708000e40505010308040d40b01c1c5000e000f44d04c0000d858040011b01203034905e1541054002141e018000040c2840301c0c6034094080c15007a180900000b4040c04030000c0c0761a005461641c10411240090785c001100300081c960066001c1d1141c3d10640c1e40f810b014045410060f0088162410220359900300700021420b0303041011b5842078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 170667347 1250 170666097 170666101
    0x80f10060e0f0405011e060602070617010308070f0807062304051c0e0a03050d0e0618060f07020d0b070305070903020904081b030d050103030306090b061905370c0803 73
    0x300b080500c00150090b41c80d55a606c80700080712007440700281704e100d42c0328004103100d40f40a0000b0f1505403154405002c000070605214003c485803468141129040742e60261248001e0408121107038102c1d800905440b0300017510010001d041c1c2101e082100c6c841d01450b13004042c1d00c088030008500f214014403940100d040c0300400c10340b101c514000c01042c7d241030911444444042905403c458009442d00d0344006003401d001e079031121800d5115031090301e03480c0c182103000c03000801441280610600c01c91020800c1e1b180101d0300c0701a0391400d03800a05034210b41941c0d05054209010a803028800241007030005070340a03003e828400101c030307409858980f480d603690302e0310101500400c609002c0e00c44070340c42d0b0ad6040700b4100b014000340001400001419451454007800326205507001040c128180010751105a0b9404140c48030840d00c40301072409841042e20480e010b105100c070707a081011040c0280b0284482032006e440042021303c1071410016480201900c0042890358005c00128003040 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 170668597 1250 170667347 170667361
    0x40312030e0f07030302070e101514070614040501050123040209031507020706020d030c050f2d0c011a0307060f050403051203220302030d0b0118080f10060e 69
    0x403210141d9440303002954032009502a4190510300305500a400580c410709081c4012103071005020340001038403118813001440c10047d500700d840e00b20030341001d106052820607048180b003000c50f2403071580315004000d00f41c034003500c030303074403036005503819101c81d841e0000100d4100850002c4c90003c026403506000d04017100c3c0b003000f002c1d501607107100d9018000d003601c0d00341c0c2c80100000f15001c1e44054005e0182c003400c1c00802483c000c41c0240010415003400703c5401c0b007907040000c44100800364541c05039900c548800c0b40e96101200d0140350b4491100760150f01d10714150b00c019000200303500c40240410b082801e012800154402006c50b45600b101e01c080000341c2c00b5506403010314a8504141c0d00f80340e03503521100d0600030201d0240140700c6001040101460a5200d10901408100c2c040c5107aa002610000d5486c050b90022805055440714402c8250307009031040c0c0501d03444100c0c030b221040d46583c0c01304d0701c1c1d9060f11300b40c001900c146c0740c050306e02c1d2001d40110070a88a186500c96607603580c245c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 170669847 1250 170668597 170668601
    0x7080c060f0405030607050a02101e0c051605031b0703020f0405040f050604060c1115040605091e010b0103141e070314040f030e0307080705090c1309051b04031203 72
    0xe905a414441c10440010703e80c6007032010380d2003030075a40c4079107840c1d0a0703404019040201c00382800d00300502d040502c20714012400c428404c11f95000314005050015a107040d10688200c0003032500e081b038440c00ca030f030802400000034600062903540c41c541d100a11580c5d2599101540002903100d41070703412081043c10079500c402c0d4014000c0c00e0a0502c80216100e007402c1084c1603800b07503103080d01c40103500c0c0550340094a00d2410b41020004152000d443c4105641c07501d4080d000404040e160800300e030b07a484040150501c4508800080c8034412081400346000b1f21018841c24013080c01c1a20101d6107840310300006100d03511180200c0c0c0c04805001d800f2060300e5008140c141810355440c010845800411020b40c400d62040ca8040414000c070b06000d072002c038103010020712030390014000b03000c10740f0023081c100120b8505036641c00041e10340d0b028000310340c0680d07004c141e5041080d0360300042d1400300d0b4000a0081e5a0120740d08420400320083e0201440396000c003501c0070b500c207146110f81521039 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 170671097 1250 170669847 170669857
    0xf0509041b030b01060305041e03080403110123011505090a060c02150408030912060702030d092901090b0a050a12140d0e18070c033204060e0307080c06 67
    0x140300c000940039207907601c83c2054074007a0030200010f550b1b602000100702c80c80c249204810b00200900400c1161075500400d02e00c0c0081c8000e0800c02c5084224180320401d400c10401030700010384000d520f100d135070b03040103c0540034420740850010f68004000180c7c020f070212180f0710000f0784401c0d415801e100b41512000c1c07131008126001103208124013405210a0003800240410740c01840c0e441017020100b00142c07818400b8841a508100140029250000112030207a6000d4402160080301420061305402c0b6100840c01e881c81d080d0b148102045115040505940c400c071002c020112620040c8051f4aa0b6800380c1c41e00704403202824031843c0302e540018080d10b48070f90764180265145c400024109618031030b007180410640060207041c0d1910120f009503034803140c5051078503803500182c01000c00103a1100a03051042003211100324284a050100b524171802d00c02078845284030700310300c2065215104810000340b541c088580180380c0440c0b46411a070b48807000b0403c102000c4204050355003c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 170672347 1250 170671097 170671133
    0x1905070303080c1c020705010c020c3102160c210308090f1f0f09050309040209010c0605040507141e06030604020d0905010203010608090d170703140f07090f050904 72
    0xb4400182d03142040001440822091340004d0303103c14080c6081800d450300812440195040f2680d1007100c0c1d102d43c00c48003503041005030a804c5c1d0a440d0405a65080889001d11100710b000050340008001c0d6a058001c0c1a8402d010200406a561200e05c82e4103a0201405c0c0032136068017500d20202c0d00c510a290f80110f0502c081c0c0b40034111210602d41380055400000954000800041c500314a82e0b104064204003404014007100c00141e56150726881842c441900ca02c0e8049400c1d081c0740d103d001d82c005519030100c820001030800703013007080e500e00540c400c0206401c80d10b0003ca2890a04034484007074501c2c0482605150582031041061a80000f8041900140d00348806001405540581200c2600130800181e0f40d5040841c01031070180700030509001c90780849003003040c2c241e105448880000c201010114542c03123401046010f05080c590700d0b07202c0103d06082c4102441d0005001d0b02440490700c030b0446150341c0340c503003603240d151038800e0551042020b0300243c04508488c42c0c4908042d0b07 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 170673597 1250 170672347 170672371
    0x30206040f14030c0601180608120d02210a0b0d080306010815042a170f1510110606030601120f02150a180b030c04171501060e0102190507030308 64
    0x74a03500742c64030315044050601007550040c0010003a840030305060701e00b0416414014000e16040080807039031000d589605690114001449210001890381030340d2612110042c100720b90020080007000060082e60700a011505e001c21050380d0303160420806080d03a03400f02c4e41e64150f64032070006461501000f00321104031f0178103020902003591580b056100e0710380d5030f46a407000342000240100c0e00312078149025040c00200a40795a80c9075640601983c00b002044070f0208941d1100320f007e5001e00703850203280e0051040503090500703941040e00544401c14000490354940c0d40c00003096600c038000e114400c002c0f407138000500c02260701d1820000c003550000e4004031218074031603820949a0b000041e580c0020710324071580b448003151804170b10000c01e4a5090b5274210300b07200da200360300c511a40c0b0805a4181020207040c1d084241404452103042084042d60740d01c1d1f9441e10060581b08041c45024010b0003641c010f0b41c914050f00e030164100641040003005143c0c29030354141d89405000d00110140340c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 170674847 1250 170673597 170673623
    0xb04020f011112071a040308010b1c0204030308061e10030b06090303071110030c050301060c03030905060c180303030c0f09012007060f030203060306240d08040e0601020a030206040f 80
    0x12810844910200b00c00b02040343e84d00c42506240b940031108640b0302da0b11406101c1844046580300016505544003440301640c2da114068090342c0d0094149405022030b400402c1c00410300d030700010340320b1141c18299000646c00d5840520055a04905069907a1091030802046815882a80b00c1c8440fa40701504440c940a140d6002074603603000b0700c1003101e103008508003000d614101048001e2550249003010710030341c280c4410107407186c001400b948007004004240f02c4189031094008498160308403040e200d403030030245030207015030b0701c82030441c020f4285100510707409040001c00c40744103590240445003807441121030784004c0d901c4001418100702000100354821900031300039900081080c00280309444c54510050140c800843c1d400c0141441030040164070344000c20941d0744803144400d152010b14900e4a0250f00c00d140c005c480b0380000003c031090041100c040020402d07980804030941040d680c00004a80d03c03400108014016003003d030220300000c030012400b0180c81d1265031201262 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 170676097 1250 170674847 170674877
    0x706050c030f160c06110d030b0a05060d050a06050a06020c13020c070605070302060c071a040215181903030f110c041a181003080304080910090305010501120b04020f01 74
    0x7a400082d01c0d40c156000c88501601040139411402c001020181401c6c07200888020b24640c9403612004c0304400d150b11030400104507030f0b070403110001410005110703988509418049100901084401c3c045070380c0307845c00101c0c0501c0c1040c043c0003260903580c024402c451654091121344070b0820030982d00030703400303120b007002d58801803042c040903103295070302c142d02c80c90982030080c80d000020345005040328040044c3e034081410704c614003d000c05080300c02c2d0340c2ca03182c43c4080344680c3c075122505040603501143c5420f000050b0141002001c02c1200c524400b201b031010010304400d001d200c024046464204a020518010041a04581744400943d0600759038480801e058038510400242c3c800c81100701820a8070744150360510311070810b61940800d00e8000c090042c0900e2500028080c1d00f00172000404000424044901411024049008400c0182c0e030190900e81daa01007100c01e542003900101c1d944000c2130031844250303004601d140454407290240510a41c5020403981080205141c003010 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 170677347 1250 170676097 170676127
    0x40b041b08030d180c0806040b0609010302100305091e0d080a0e06130c0302040212180a03020d0c0c1d010e0702030313150f051017190803060d05070816050906030706050c03 76
    0x1086d261010341400c0c6401d24000110540041c02980700c2c2e00c09000500241c0c565605441800701c080c2400074881c1c0b194562203144c05583d1010b080c1144000000d40b075800404208088460aa516820f40c20341314901440240c1d0310300405800c07140d20240008000380b60305081040c80d20b001b80740320307000240c403034000c035080c1c0c0d2287c04810701e0b44903820f06100701040404203108241c07446202800f14402599002511101104128400c0240440c542c00c14401210170300360060044592058024401128005050100340300740f00c000509034002541c094004002c0340e00c10344c0e00c00b41850844e441a520825006400108503003800d07510001840c00c3d10551098901800c20482c21424081c50000c0c00d1111413104401c00d0f0b66504040700b5160f61021841905d402c05910601d00e58aa54420f070108582c0b0032031002c0030788640f050510014584c4008a01d40071140300c3d5003805a41d00e80c0350028400800c2013990401d03050b030f10002e0f040054a114a0192900c54002000d0780d1801c0c51344007400d40c2c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 170678597 1250 170677347 170677349
    0xc080409051005100f020a170d06080109020f0d03140d02070605190b010f0804081b070e0702070e0103051f0e030403030e1207050108040f03030b09040b041b08030d180c 74
    0x40d225428020a10652524034004c407911602890032100c0700c4403400740291a05030030b00008040e214040c010030000100d9009440c11360500c3c0030204029955092640d004c0d000400c1c2c1640600d6044a5142282c100603107041c42c0d540c1c054075203122200701c01c1810415944010254005a5824020140020000c1c0940e501034000c8182c20440c088081c0582c0003225030003422141440080381084a001d03030049100d946c00754108a506881c0c0184008101028924011440147c003481e00d0108203590180d00702c9006001702d5003240c8443d41c442ca2401c460210070700015003160701c800040b1801020207142c04103403d00c1f04501141040e154a8a2850354103c1c2d0403c9021408400c08070a03942048942c442c2403901110007000e42500d04030019000420142c0041c08401a075130703081b400d16020303811503484075001400b0540d8615140c18102e55000040c1c40849404404420b0803500070f05204d010b5058030030b0301c0061440c200160802d2001400030f1129006105c141c04400d401007110418900 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 170679847 1250 170678597 170678611
    0x40b0d140a0b011205091b0d05120a120204050607110307080718050f0609070c05030909040309090f050402100f09050a080601030311010905070506090102101118010804020609010c08040905 83
    0x812102c080710700252032030a0510130184054540300420881c0400010300c296030013641100b1025001c0c0e100e02180c4681c62041000d0b141d44104202c15450070080001020151300c42c0d620b0300b02c08030400050a05074800da200c2c455111078140b0244010465420481c45040002001c4403141e6684d007100034145045580003140c80740385038410000c04d411074081e07150b02402c081e10b01d04070362821030005100c600000d0f15a00c00c10031000a0a4100304c001c10844080500003007101c1070030319003450010100401805100d20035402d00c410b000c2c04564a01405018950003421403420000d080e400322334001d105503110301004542800043c00e074a52546840150036440f001d84125811414007a040341030f03c80c4180d10301e86c5070088107000b140b40492802c040d102c04882c019500d12107200102c0c6412904241c03071505a14094103d031078099124000c100403098450015001043c250065501c00022180039410001c1000400c80c9036214000c02e123007070746c400c1064900703090700d640c130310310840e10112802 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 170681097 1250 170679847 170679851
    0xb0f06060909090318030123041506080303070905060309060403050313060501030506040204060e040f0303020f0417070e070c0b0a09030c0506070201021812100e03090d050106030c05090903040b0d140a 88
    0x80d51780a07403a1482c0c1c4481032000e40083c000301202520301c0140780030952200380c86842d0000841d00f04100041c030295550380704001405250786540380c2c66100ea000b903034401d02040f00746030f000030725003441e0301680e119542041c050081c1d961a9202980c4c240d00091295103e544800c14003000510503115160103580500c000348a24035040c0f0502c02211165000141c80752150000c02c0000364480050030801d541c90725015071102c009a2291006000359008401c1e60b00c01d03202c98007135210001404d031044a44076800414280c0320801c0c1914041500c00015122480010000d00c0900b4241c02c0a02601e20034070300030410200503102c09017441011b9456070010f035000654000003480207040012007010440c2c44c4004900000c60480c7d46180403e0441c85907038072428100450380d414001e880c0b9545002d4900c0c0c400c51060300d0301c64000c000078082111403841c9040c000c60766003003510000c2d00c41e6500400640c900750411910010035001064250140307a121411207282800d0202c502d80107071812040 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 170682347 1250 170681097 170681107
    0x60f120115051c05030d0207020607120203070b0c1e09120303010320042306030705030303012c01320d06051801051005010f090305150907060c0b0f060609090903 71
    0x800c42c101a00c0c408440f500141c01d1014000300384040304403102c0e8101c250005a4a40f91480440d200f4018a0b10103016080580d01000f1400d4022000f04461031046003101c4841d5540d4080413070302d00590050b940b548180148200314819160300800d802180140070b02d0740461101c81c05032031640241c0084840c920504682052050000e07051891514112024440f200080c05180000c0c40b07a0074104100c030b4031800100340780d82c030140200005000050244ca0303a968403100021040521140d11100207024565021300600444081c41c0c16038843c00c048421318002d50f2002441d080c40345e020034601d801c1c2e030b0300e9105043e40c41081d040c001c03d120301404901881c080d02c100c21004101584031400d64140010402e000001e000120261202400d01c10200030f80c011041315501e203242c200416a204198851001c00095101c1a2080c0c1d01c50080f14107a9032200030440d200c254120004140030010404280c4207400600e070709600c1320000d41050700b4041c3d0000003c8803100d0569102c81d1941001030 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 170683453 1106 170682347 170682349
    0x12010b062a07030b072a0b1f1203090501050a2712050f190b01090b01051c060612151401051603110d0c0506060f12011505 54
    0x800c41e07100070b44915144d40c1d04242a182500072480703000300410b6a43c01c03401e0a100040e80c1d41ca1804240c040d40e511800c202034050200e6052001e14241c0100ca103000f904814010010300100c034140e580d003414060700c120410f40100e410800304000300c1900603000741c07074400d40818602804104036071114049100d0645a0024020284102040b00510000189044c8415101d0065820780350400341e1012441c0304440005000040c108010060100140d0080b0001101070400500c0c1c448402032a070301b100110300300030a1455882c1414440385500888800001048040030004005a125200c3c0105400d1003001d110300741d10039a0300c41030f0f4460701c280d424048804050303020881081c42d024000d00f81400c0998400e02c00c080240c09414031503041e10b01a581c200024014980301c0c00c090180c481841c04e003c2e44c1000c0c900d0400040d02809109415410403070544000400f81440c4c = true := by decide +kernel

theorem cover : BRFrame.Cov 170503597 170683453 := by
  have h0 := BRFrame.cov_init 170503597
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 170503597 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 170503597 ≤ n) (h2 : n < 170683453) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
