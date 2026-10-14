-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:38:05.754417+00:00
-- url     : https://prove2.me/submissions/ec4f0acd-041d-4e20-bb2d-c12174e6e436

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 10791374 ≤ n < 10971230 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 10792624 1250 10791374 10791419
    0xa120510030f061103070306140f061804090803040506040c1401021c0302090a030605010f090203090a020d05030708030a0506010f0305040b18070302151b0a0309090209010e0409030806010f030c050301 88
    0x2542400c001303c0e421070095100300256a03001036124217082c061410400d0030ba142501400401c40341084a48400d002c0f81c3d18422404001130345020100f0004020b0450900c008000035408000c1c1f0080010000301580601d100303940c0c5a80031034035001d040580101208405005901031200c454003112030700080c0c0b0300e4001c3da103000751825008001007100c608007a4001c880b49580d44004015005420317180f034020f010005019451411b000403100d07130323402c65040040d00c5a10288084400c201c020001c8841140c0c1c441610f9403030703240c00318400c8000c140840d4031301c0c04030ba02c0340081b0114511920030180b00729031080511420f619082240504407000d07a000030401c1c444c104012015aa0f5515030701100b04403500419560001050034203959240740c0c0340e0002640c461207009000130f0f004918103003520545140140c0700c07400c2e072004980c00501841d0980d00f091400400c0002e060344a002c42348260001c3c1c0f20340c81c01410804003101200c001501c1600020000c0c401480005120044040d4500c0c21 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 10793874 1250 10792624 10792631
    0x60c0c062d090d03050105010e0607020f0307030b0109020d050f0c071205040807080c0a0602030403030918090807050109060b0303180607060e12040f0e070801030201200d050a120510030f06 83
    0x81d55000d000103400e035240d40c030940c80440400b020b1503040c000c56014290a1804100c1c130481c00d0007164442c0a801002441043d020b004c01205032410081c0303000444e041000e421107942c0d90351150000754005c0103182041e03403d180019101c5e00141d800e260044100b0141c0ba8649035968844c0007034040790400c20000c1000400c000640410b007005008041d0500c40701400f85840c005081060958041d8004401d54000b40020070103e90480c008030216074907040058000d0358130418040041102c14001032403c8404101c1d08184035056001880c0d0034403506042103001d805500f00340d5a0301a1080d031421001144100b01e0250600d10040c00f0040d1007140080303010281d0200c031904000c03250f1600b0070302210200e41008000170301542070740107042d030084110090038502c2e0010100241400047d062094103880c3d002084010001d03582c14281601c141e9038891440c200041a03036014403020400150781d0054000114011303c50741d40100d09984100c3c0c041c0f461907507040711800ca050001d565403581c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 10795124 1250 10793874 10793941
    0x90a0b0411030a020a09050a0e070809010204031205070b06090103021e030f0601080105040201090909030905010e031f06170105010f0e06031504050c180f0403030f02070203120c060c0c06 82
    0x7400e070241d802642169409603d400030f000000782080015880340c0d1103203500c4001002154065401e05420031010310b00b0710071340d64442462034003920480c2c0c0003e10354045038031202d1006920402910181d0300c00c0810000d0764843d0310406c09800e9003800065401080c855036080099910040024480c4014080c1e4010000e041545801c10303009a000746e005944030020002103680c030043c0d801c041c220840003007104800c5614014081840703400b450341070080c2026001502d560800441d461807242c500442070ba40307024015280500700c548242c40d0801c0c8000c1002100c460180a442e040c0d802800d4042d259034900346440403c600701900c281d4250084130400c5051307016000b640b5109500a5000701182c1e4070383d906010008041034048d40700f1500c5034040c08200c030503001d80c0341e8105400d8907001c606040c0d44040a8000e02c55400300a60511074090480542c085060207824015008010380d80c4030344d42d58003004a43d1141a143c056144c01060009500c41c07070f11005018000c0000b92f22090202 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 10796374 1250 10795124 10795151
    0xf09050603131e060b010203070b060409020d150c030b010c031409060f0307030203010312030506011b03020717010b030114090703030c05030909010305030309011b050a0518030111070506070e090a0b04 88
    0x81d0038070301d031042c01d0000b403e0242400040d000710316001500f031006600d00102e5484400c03c0c070001505040c401c0b900d9074000d10075503880d003040886140e0091613090495042e0304010000f007140c034407034030701007030401651501960180c100d0040482c0c040c0c540c240303140e00c0845110243da011795401c0703038082c030b00b40a20155403070518065441440c064500603625410740c05c1503108400c02423550001c01d4244010000c041e68451200c1c200301170300b1301484c440d41c200c43c50203a0810311140c02900001218a1180c0b4003a80150001101190260002c02420b42e0307079444030f80302d00c1c0201c40340001071340880c40410000384030b500c2c064440c1c0d0250b800c1d00e003442c20f00e400007850504d0a074001d9903941d00120030f03c03802080070b11800400940c00d034011401109031050207890b070b0080243d84024054080b4004501142c580301e09450034000800030070104000c98071501098120003820380d881e104c0d040001d52040c1c05144e1703040000ea002488a2410360ba1034603880040c00034583c1903034000344ca60110b04800c4d07 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 10797624 1250 10796374 10796393
    0x30302091f020d0e190b0c010b120703020a050d080901080903190903060e010b0a050409050709110403170408060103020f010e03060c04050f03061b030907080d03050a06060f0905060313 81
    0xc0c803258050040c512640000074038907150190300d68030680c0251041d40c00c14171900c00319000c4402c140b40c241e403205070ba500d00c40d0041501e012080e4014403100381c00040300501280030010307a8421106030003900c2d250707404c4c4030301d103207078010f00610115007040319003c10f6001d102140d90110048017205e103840c82e50050101078a9061030b01c103022a40300e034028010844a4010740061440d400700801400d0344101c0007490a10480c40303170901580d5219840c009000342800000080d0030340c0c010031300000c10f411800c920168003921044e120740603181d1200810101c960121402c0f40c2c000340003044164211b80801040059004401703060040c7e002407007a140e1030074041603114484503003e1627181c51906040c8004201c0348904c0314440d80040d0300b00002c00140190b800c600c1da21824460343c40750303605041a490194103800c62215480341000100b6041d5141d00110300c0f0b004140302c1402415501c1100760b0f0043e100c0c9209401107492070109220506040c000746600460186008104c0074040d103030150790 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 10798874 1250 10797624 10797679
    0x60a0f0602010b090a020702010c0b0601050c01020301080304050f0111150a06080105100305010c0c05060f040609080c0c1908030714010b060c03180303040e0a0c0504030602030f180c0d03030209 85
    0x940d44500e04200c1604c2c0100055510012282007540781122550009000d0924140020161900703180440c0c043d9104106480002c480740008540e07030750311088140c4c0d03650814401c65100306001c406512481d441200e000c0c02c8000c03410010007001155501020303000e40018208840265504800624003509005060003035101900140d290390a40c00c02500307480d202200f001c02c1c0a070030601c420001c3d10004046030303c15000d41026846031601c0c03500343c02801e170000c03010704442e2000c13407820030500001c00da1816140d021240c018566024502e030070500301440c490310349681c0090040e000415460440d46c06a02d0034a000000d01590750000118590031480d0902842d030b0010601160844082c60441d840e5001100118141032510400c2c11440c82d0040a01c03050380c1e15904401d0300741c1e0198007542c0140d40d1042e41036442c3c1c2790010b500c080c00f0b442110042c058411800011401c04400b240041040d00050b010388592200354809901961042881681200e004404084202c0c06502c00e03860 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 10800124 1250 10798874 10798877
    0x406090807030e0909011b05070f0605010605041e030803040b060a0e01172802060d020408060705030402090f070f03090318080102040305060a06050102030a080a0b0a0305010605100e09010608060a0f06 88
    0x503011244402e11400300c4c0000e044c0c0e0386980c0b6000d140041300d5101551f0b40300360145850440c0d03a50106240808045102c1e050090442c1d00707200001c40d0480d0440e000d0b1096841d66020318001140c6014060165030442c1300240204000b080894081080341040c01d40c01000682080380455031244030b5840b2000990082c0c40401020300c0303450000d40f050220244074003000d8001c0051101c04401c419586500035002485060b00090318010307400d060701078a00a000140658003c2d142100011702980e0048404a220346042c00028040e00d11558060b8003628880ea00c011031002c8018003540203041162066007809040c0140002805810015074040d000300d40000d41c4440c03031468000e02e09100600302c40c0e03145080c01018006a60b000055903805406c1d4a444c40094550740c541c58020300044080a8101596040110900005410036001c442040c5c0d00c00f000401400012a0303d207034010111940500c080004101e5140309101054000c140240034520785541e86d2024620700c52564010307070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 10801374 1250 10800124 10800137
    0x9140f09040b15010206010f050105090a0b0408071d090a03050c0102040302060c0d030e0a050303070818010c030605010e030d1205040525030203070605040510080702030c0d0801090501050a0e0f040609080703 91
    0x5048242d0f46480c404140a00013090b8650400b031441c0b1071401c090055504100001c100496240e8030003030440014058280051365854585480036100e1499024052400d000440d5855940304102d00305441044c107440582081c664541e421550b6602c01e07000078003a99003c0c0300210259070344038000e00c5074403008001040440d04520703014047e250021520603a942003543c3c2c02002c00e00101c2102d52200c7c2134a0184448e82d145c3e0b200d14240300c00da01c0d58407481d620b803412003940c05425511040c1035a0382601d032070701c02d00205010940d5030324042e40c4100000b14000c03080e04a04074207800180c0c109105400f51144620318807841080402a0f03a0f030010060032614041055040a00402c400f03000310b41b51442c90142844c0110300e00300034003881401000001400112558402c1c020345a00143e002c06451008581901c01131203c10280241210903240c03000000702403820303c24007001c40754000110303451a030325000c0404440000400607500700344c0703500c40700000450080041554074401d880d07a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 10802624 1250 10801374 10801381
    0x30d0203061201051e0604060f06020a06050c090607020d020d050a030c0c0e06100c0c05060a020a03090504020c0a021201060b030f0103110301140610050405060309070e0a060609140f09040b 83
    0x2202940824410707a0103070340361905101355029082c00713000c00040d06130017540460321840c002c40c00511181d400f481010610300004201d09501142143c00c142c043d80b024000c0343c9030700d200840c240c801c660840344d0101041080d00018100800103d24641c0004d181d01e9120030580c035164180075001e003048000411510501d402c000c400c201440103410030000864943c40d01c500410080958440ca290900455078000810801d000c2c08800103084041c18050300c503540c03158069650344065400720040b805500b408a040d0520b4800d851222141c60b005291442c0250288030011603000036440c200d54032010b0118034050220011801500316400407202c642c55410110300c2e03c03492041407482039040109517806405103240712600000100c82249210321408001e40d62403007240d01c2190407140102c02c10140001c04158141142c02a10032451541d983d4a0100c0c01c03540c10340285004038881d031409005072045603100841003000a400341c548a21014001140c02c48202d40440c1c400890b44d080 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 10803874 1250 10802624 10802629
    0x100203071101060f1a07051e01061706010504020f0c0a051005090303040b0c09060706050f0601020706050c1c05041206060609060908030301090b03011b0c050607050703120b060c030d020306 83
    0x145440c181c002041584d0400e0403000c10340545100300d810a100703490fa9084c00c000e0940880711b0303207544041110075803421b04210044c202000040060039500e0001d0000d901494040c0d6200000780c0c5801911070b80c2e003044e08010003501304c510007404806050203907410100081000c1c2032024016402040c1c503440841d6040e0950f0b00007030201c40706030410f100740000900d51890503030300211505c0e02251900606404641c083c015640041d02d65410030041c401c030000c40300f00b064010282a0f0a6a460302d4a68a0540e030720301c240b85110f04603920982c070b8400d106684c0002c00264107190701e0414034241c0d45500d01d85c80300210b82d000b03076a03256071001c3c100002500318843c04010710321030802900751850191140e8607400148220516240c0394a0f030492581d07070030b500415410b1051400f00d0380c50101d140000304040c07034a0004542d58030490f0080b60400d402482502c45091703050f620200e0100b11300a104000d05520300381d04d60480300900c01a485900c05101900c1d40003041140103031685000402c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 10805124 1250 10803874 10803887
    0x403170a0e030d120507030b01050304020f042d0e0a0b0c03060d020a060f0e0306070210020c010605190617040c050d03020a05060118061401050f0a0e0d06020405030606010207050a05010c0503070510020307 90
    0x40c500600d450708e00424840d0741c0020039264410f80484907000360814540100707014003020200d5030004c00c01082c82c0d8010704180341c0303140100c43c80b06004001c0b46030141c081030740c0c2e0f410750700b0041c03c030012034400508400003101c000c0da409400500804c1250002d940030401a4000d5004000866116031b81040b4141d4003105011407807800b180105200c2c1000f01010351a01e00030100c403401c41f9000920010000025001030008010107007081d411892048070801c0303011454040d80b0300086010b0340713003c2e030101d1007040315005a41040804002920b04000c00c4407120402c0c00c11010f6020310030410022880a0007028002c29a0804288800c0c800000d4481200c03500d03001012200f111131645192641e000d800d462580e1049000259240c609500c00d07100c80402140481d40139a0900c001030412038260050b104a034000d404a0f60316844490040ea120750090050942000000c8804c0240c0d603c00c0702c0d0401403602860549240c902d094407500e00303010000f441610781540000600242d11b60214 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 10806374 1250 10805124 10805131
    0x303030f0506010306030201050d0e19030314010602010903050f0d090f03110106050303030108030d15030606080a1505090c04020a0309080313020102060105100f051b0118020a0801020403170a0e030d1205 89
    0x2070200241400c6d0b0380023030700c640242c810707549500d41e50b501e009003420400c2082d010303140038181500001c0c03125890010042e110401c3c84c5600c2840c05000040e105005003d024419035058642e0f81c1002c01020780440e9035081000c0c00e543c201d07242c80c0c451001c5041d81c4602e44c0160b000380c1e164104001314079041030965140d940710781c1c0207038400c10041212201c00b10a5680c070110190000c1145111000003100c2c060710b94001402d200e2620800140444000802c0e004103486001d05084c45600740300ca034000c560040f82d01020f0354000501c07521451030035500500e00c01c501401c002800d00066128070580ba08200e411009241004d02c001d0103543e010000030f0f004000c00c07942202c01c044c04400c005c0c1618a4840b03410140308005c21010a0455900404d0f00400c1041000b00500e21212141d140c3c9182d501a0907402000d0f41803021034011018002c45065075002882d0504d20940e1400a02241d40440350311700c1006402403900d011560103011110a5445554400c0800000c0d03024400840d03c029 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 10807624 1250 10806374 10806377
    0xf0a06050a0501080604020c12031006020106050907120c140c06010f080105090d0e0f090415050a0608070e0a020d050123030705090408031e010801020705070e040c030b04080d02040303030f050601 86
    0x20301d0100b1150ba80076803401d5002c142624050f0322800400100e9141407904010340d080c05801004018800005c11600c0e0300700e41565000b030082341d50300c00521490031b000340c88103400140c0301d51442100741e0050f007050b04100814502a00040c41c540605070007038008880c0c0d000070b41c108400410280118040c0d0001410b404e800811190070716044c0c165a81c2e099000060501040207081d2080c0d80d15001c190344c0c192006080d20b8450318080c40c0c010917a101c081c0203501c090380340030085041144144110000c0d03c038280001c20703200d41002c9041e40380c5900104a0028650200240c0307440c804240640ea0080059034959109060b1050118503450000c0c2801400390b48491010000c80d9200c0c0c0e007064015030010115652500c0c3d81e0528010400098040600319200d18000555400154000c1c4650390051090341c08040d101c011200718104151070141055503ca002480454842d0b4062900b1622440081340740580d0424410283e802c02e5000713501013541c8651065420175a80241c95001009 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 10808874 1250 10807624 10807639
    0x406080603030f2b05070504030614010602030a030f0b13021309020c0a1104020c0706020c10050309060f1f030b06010e0609010c03050a0504050d0807050708060714180402030f0a0605 80
    0xe1261440c01c500810400c900011000c0c20140c1300c1d81c0e1000c40b00d0f081003001c0318051246141001001d031447d40188802c807111490320707000f142030070303003036241e46041c4c0381c04c0d50280d45020740110080f009030064904004070a903881151081d581da4241e90150641c00e83c51b005078440f144144140803401903544018102801000f40c842c0344800072070480540c9070b100c4466074515040c100410000e0180e4414448540b00d603080100300d4680029401d000b10310103e401500c0310440d44001ca0740381c001a00c0310082540600081032000c100c0c0e2020039800001c2c5441409054000036130b031303040c0d601954826282d030401042840100e580c0818034411a100503aa602c0c58980e0440008002e41d0003000050100100405c1e1149402d1250b0211070007000020880f024030901402c100c5e10662200300112110322400d00c002a1100000c038641e446440f840c0c41d005081101d182201038980d001c5124009000c04892544078150346510286008046900c00360007103290107a0500c1c1180c196801c1588103584 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 10810124 1250 10808874 10808887
    0x100308040b0d02070b040614010603090f060e0c03060a02091e010203070f1104060905090c030105091203040c0306050c0306031203010803040513150e070210060501080708040c08010f02040608060303 87
    0x40020468084604050a0aa44400c01c91110009025000f001000318103200c0c14041805041d402c03004401c14404200b403d00e0744c0c0d6410503401c88007400801001c6c000c880e41c46a020510640c40403104200c00010740d004070030b042000034103000c02107480360f6440f607010130726007a98140315031003641c22010007001c410840c0d0b07100b0021707503a07015503040201a00980d224480c100300740000030802c1c404016000307100d0302c0e46811601d0050f1070111503103034080c800c0e00003a2400380b605018590055030342a01030f10300000040021501030744020420b440c0500500700010008801b81700301842803828041440e01d80c10b05c24105420000c103900e00c452801c41c144014414090080229401c1b11030440ea20000c03517403c104486d0240084a0718200c1d0b6141068000039581703010080385110310001c1c1d0a407160040908036407012903401d0b003c2d00f40006c40c4000064400340c042c24010f60824041c1000c27445442c6c0e42e159903403e403109902a84115a004102040459040307012250416001c0780514140f04 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 10811374 1250 10810124 10810133
    0x40e160e06150f0307090f090902010201050c0304020901030803040303020702060d05060102061e070f02010605030a2d0c060309050f0d020309010f08130206070206040905071713020108040b090114040606030b1003 93
    0x140d00f208210b2400300002150305180a1600c1d5001080401d1581c54000d6590040c20000c2c8004031013a4090350038000002d46480c00c650031a885550300404a44050f401e6483d201001d40000f441101450b03400c018080150b5160009072010408580000c140c82c0341a000090404401514218800c211020320025109a02891940c4611140741c045600e8102c0034049014240e1a440103415008108000003488903d5402801d445088060a202200e03100511026102a00340180068030000010702c01c2ca4442e03004040980d000314115000d69400c2035803a0700380505480b81002503400020a02c1c0d0958002e14182c80b64200ca007000307001340c80c1007001c0322151075004000074030440c80000d81d02d00f10343d5100c0035140074144e9100d04100d40d107000c00024000c200440800d0320022070440000c2c205101f0b40c40f588200c0c42d41a5903021840e19159103c000380900508804425502d03504040100848621420311440c0901c401145071450760414500b0004080c040d84d010780e60843c0140b0114 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 10812624 1250 10811374 10811377
    0xc071716020f010e040e0606091006050301030201031e0c110607020705010c0209070c05030a0305010504060e041121010c210509070b03040503040f06020d03060801020306011b02040e160e0615 84
    0x1150160b030610501403802c0b00480700d1501d40480c8592080c9802c1c920300311140c00007400d610603a400c0d107441da0345403140701c83d20070540038600c11303030001802c20030051005501c2500240001f904007040031351341140380c2c035081d001c0d02c1c00d98901a0000d0b4507050880c0318601c1c1004036030380146580c00a00302c01c1d402c1c0400280301403102d0002a008034080c102290103244221040c100711904a015661202c1d5411802400f500c1d00f0b1103802d01c07480c100a0086503030920301c03040074004c44d44246460300f102d102d1424003180e400300b070025a036040041510844000020300a19203000580d03034070502380301014151040308000922501c604585441c08000340701c0f500207010816500c07004110341e226078072450103626505c0750760403602c030f08540c00600041e040c0c0c0001d08040c3c040070540f014000c6540724100c103800c0b80021254540085c3e03c400c1d194100480c5c222403042840d001a0001ca50f10103c480c1840c90500c010004c0402e14031a0507042015803010b0260580140040b101d41031600343e400100e41c801d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 10813874 1250 10812624 10812667
    0x12090d031506081806180c0114030708060301090b070302040f0b03010605030106110a020307030804080d020606010f05130503010207140607020a02060306090a091401020c0d020703020a06030c0203040e0c0717 91
    0x1c0c01910701c0070501101c404e4041014000760351085034181c1c50140444082200003502100d002d02c80c9403401100d560150001d681c440b0014450141503560740c1c1c1048401c00000b415040d00f55503104441790110b000b00d20903c1c071039507140e00d02690351441c00e0b1407603080e0300e03042d40b20004038001400148a440d60000c200d9046032614074241d082e801412034100e05141211038020351511507408000100807454000c1e00032210410150b403014074103841c083e42c4940040f14110300040b41c00c4004107800b0301510141042218403400d0b01161525040403034220b91140d58280c1d000c510301808501b000e0000c014040e4081c2c4584060888041294089800c5000103003c1d6445a02800001180d045260340000009a00155005400c3d0300c400e151900035807204c8070304c6800b809908082e490030340c00003800c0000c80e513010341034010052404000b100207003899141c3c5000c60100308800102080c41c9400d55024541030079800c1e07a6034050b8500f009007040f40411b15200e00c40c00740002c0045180f60319040c0740307 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 10815124 1250 10813874 10813877
    0x307020f01050d02030f0601030c050c0c012f0a11190501080a0b0d0f0b01140906060c03090d0606060e04051e0403110f1b03030f040303050f04050612090d031506 71
    0x40c1008454010389a0b401000407160034030b072001c420005640110460a40501c0c0700fa2030403c01003000d20800c85441c4200d010f802c505a101f1200e00019501c55009419101e07007440b00115a590042c104013142c4000265000b2103500203001d0f0414006481105e980440003101d40f0820341000781040d5806140c0e502c64070741403200510004e550307114a40c00022017050002c1036022040c12902d841920a82440410740d0303880484000403d409160703150494460100400419695913550200300340c0741d000c0740400303100740401d0207100c1242d110034070f8820401d4816080401c1160610780010311080340b10b030f0180e00c902c2c144003d100c0c450300e40901103e030400e520301000359640d035541070558400d09001514510780c03040c103915035a108408900407074490205200c898060507500c04140e901d005080c0a03e414150400040000a00900007000001c2d4101610b504003991030000030104c0c0c0004c09011228006a420000d04071401d01c91104248203604042001402140c00120b40d01524000c080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 10816374 1250 10815124 10815139
    0x5100b0309010f020403080304060b0303030105060702040509010b0307030c0e0901021204080706060e13050c030304051008070207030206030a0f050604050108030a0c02060f070804030309090203070c11120a061b11030702 96
    0x8100020070f41110410348030442056544560303a15101100c1d910444080d6851072070013529203001d00c2c1c003104481c125034004090340d083c80c0081e02000300400003c5d121085543d620303401c120480e1018030489005501520702110900c0c504901004008001802000c00d64410001a400c4090011015800680100c0101c0c0c5485140c908400248190342041c0d4120388032000700030402e032440c00c05c100103c0c13003582075400556808c418595640a00e004040c0d11000315240358900138801c1c000291301c604a88103c408203545c9802041c0107900550300e100b00300e40c032505054206911030281d00e4000c0301c03c3d5801c0010b98900046103449006081d0b03400104890348900d4029980d90005680d200100600710640d40d048a1520087d1680103100890118100960025000c6032510a07a4480e00c41c030b031a0b80080034084d075118842c090800248503800001a2040f804a040c00c0044030b054a02c43d0400142e140342c0a40e440349140300f0940350707800708420000b021140c210b020080d264901d9056030001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 10817624 1250 10816374 10816381
    0x60302010c11031f0f0605040912050c15130209060306090a021e030303011701050610080a020307120903181202011e02010603080a020d0e0603091f0b040e010501150305100b03 77
    0xc1c0c03c0902c451130b2400c2a810f10120140d54216952100820010030342c0200b10565640c01404140c66081c41d002d03040300064aa805140327030007900142012200c0307405803240b42c05003506011001e4815101c0000e00410715400c0c0301142003038038145401010845c014040703840c11034406940c2d41131405000340905209244890301241f2401311259005000b002ea079103070768561960f545c845410300da41d80706560900002c0b407000d00341217010654840c05030360350494503598040d401000e548050800ea08010300701160768501c41c40c5211f0016100d109640d0114444244901d012040030303da04512141103003881da260050780c00c16100d0a440b45a50401c40d46695500d200382e00600195002420650f00040c04001c004d030301142101da030350406c2d111250320060040901140d400211105040c40e4421020010348000200641c2665912507102240c0b00c030010340401d09960850225035850382d16a0014444090705d804c4000b00f000807490108804d00e000ca039051584a034503c203a00300c045000021 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 10818874 1250 10817624 10817629
    0x5031809060f060a120b0a031b1e060c150207031107050f061209010e0d02070905090601030f0b090a1506050a080307020108060108040302070803040f0905070306030506160903051e0f01060302010c11 87
    0x1005a01c6c0018100c40c4401e079039003040c440c800d0108032202c8140d40304050118142c00319800501141e446620a182c4503818408180c1e0000d00402d400c0c1d9102900c480c014059086900050003158840c1c2d031410110508140c00c80e2802401f0707000684038044c152003a8800c2c1d2603441c1620288030140d0381400842c1c0310141940d0041502400c04625406150148080a81c00040410131904444410813031a07441e02d0038140c40b1402800000c1c400c0c041102914046640d242e0965048000074091340c07124965a59440c0300c0381409030250070210b413204403c0085281410f03140005001a0002d14a04180c60340002c000100080c0418140041140401d041c540708000078406010b6aa0072603560300e40740d003c46503035185144100c20b9141e0401e00050b00b054400e0142504681c2d200005100c1c589a400c0440205003401244104000c00a103000000c510208410514076080c044010b051450000d0703518200341242c00b111542e85c0c1425070810050b41c1c13000c0c0008103550060600c01c0800c0f5203500 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 10820124 1250 10818874 10818881
    0xa0506060f04020c010603060c020d090f060c03170103031119170307020304080102070606031e0507060f0e0307120320060a05060112020706060e01090603080412020a0305031809060f060a12 83
    0x130f401c0c025032a003100402000071550104029008a400f110080d1000440881d0382481c1402400c40003c0d00c4201088081d014004000515100b401d200400322558440d901d1501001d910980000e503011300c041105242c1440f809210180b180141c030303c070070185d440b81c00c00c100712a89881c80310500000011550740c401e00c00e0b500605102e00096680d1150750a2210240c00a4007040d00c480041503520798041c540084403012a80c3d024010300a001d1030b200042c1c1d004540c8032110701c00e000c9140f10426140d03a080c06120054a54001580940e0815040080c011800c5c0340c0c8496400401042c19840c0341c000080e0b0640c0003147d01c0f0080341c0c03030b074035100126040740360110300d840418004101c0d601040b909070130131400e4980541100030b683e07986038050002d44807648005441b2050070030041c071005800d103992051590019090782d20032a603990f00c45165620481004106241c0001d80601c1ca10f8005102508074404480da1510a201280080d03c0b501c00d0200d010309021801d01c1c1c00d114110740b44c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 10821374 1250 10820124 10820137
    0x1b060408060106080105030d050306010e040b0a120302060a050903090303120a11040305030705061f05010305060f03031318020f030a090204090b090708120c06010b13081c0e030a0506060f0402 84
    0xd090352895696040d000c0d00c0300200380070300e0b4464010055030a14551003074040c4d030b2046105075a001c42070508242448010110246410f400859a4001280386481c0c040601e107114802d500800c15881c105203544d0450f00040e0101001d90420400003100c0d40c2c00106440c40504031030314640e80f503201c0c140118000c0c190500001ea11a0000c00c0000900a020014040d214042c209072803240c3d0fa01030014040c00907a0f08010200304c83c08a080c0010b500c0313603000560103600074003100c80804510002919540085103103080302c4003504c40c1404840c1460210351b0801a801c442541454109442c001003400700a261079004ca0303840020005641c1d07141c000c1110302350071864848a60a260302415211403840c0240011071080c0c4096407403009004048070b002c8501d030405000180d0030002c0e42d0304147e00c41e6104080002000310301041c8120103006510b004c4031031540880e61012002c0300588100c11040d01d040c800e07000301d20f610000c62008184998454821070f00d202e150364ad0f01001030024024813 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 10822624 1250 10821374 10821389
    0xc03040905180609060705040b0d0908030a09050d140307030e0a020a23010507021003110f04090c08010501020a1101030b1809010213050a03030f0305151806010f0306081b0604 77
    0x400c0c00a500c00c00d0102e119428a60350036101965141c1842c5580d91030103607248800504100401c0000d61241405032085030040035010800000031b444000142c1c005a0740b0300040e6513143c0303101c0108502000b104a440f4224204801150818640541c503404000c10307520034543c5600d211501c00401f4040100540c1d4000e000c0461641ca440000354020140c0b100c095240c2c0780400c40f1501507006005490b001640284030403900c0c0d0750312000301c01916518810307244900c1c2c00d00401e802c01c3c1d9286c000e4005400c0300040002e24000c12140200034000c1a841141550042c1000e080814032925212001c08028240421540024008503964040c094001602c0201070b005100a6481c19002840c031010018103115241352118200700001c8154440103000c22211944001118060f401140c0d00400c0d480c0031141ca100c580c0081090810310f1540648070800440c02c0250315030304004034514080c000d18003000000d00f068140e41c2d40f9480302c40035583c68000f104c0000115920b0508840140800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 10823874 1250 10822624 10822631
    0x3060308030f040302060a0608030414180108010b0117060102100c02030c01060608060f0102120a0e01090e01080a02090901050105370b0a02010c02011a090603011b050714160302060c030409 83
    0x21040c0c14202d505841c110010700a02c40400e03000e807298000c1c2c0003900c15010146107020f01d0400316440a0030401802c0360030203020b40300c402d0100c04e46c180d5a030082c09040c0011404c4101c5200042c1407845d030050001c0c000607600c3c1400a240d074002070300b01e80540100d90015109030001000d030b02d10b00480714898020760801102207242540021198003c6105403074031903e4450b14401680c0320b0321502c00c07041d00c2c84018400700c02020f1040b50074030800316040c18115000c0e43c42e00309156480401340c01840942d80241300d114118100b0000d4282e01120740070080240d94104400540300c4131404883d50070b11069007140e42600c24801d00440c815501c0d61014108031603892040c0080e5810090f40c040c0035510f4400040f08050041c0a6002c1c003c10360034100c94010f00318020402501c01c09410913030199030307441034405101d5402109840001690f15229120385003841c018281110528a050076604102101e4003840001d1400005503030b0304840c9680c46030713529544245180941c0d880b01d20400d04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 10825124 1250 10823874 10823881
    0xc020f01021b06060604030308042a090c080708010807050609030c0604030309060f03021c02030703180302012405060306010c15110d111303020f04020409021305180103031704030306030803 83
    0x7060140b14011210440036140300380e843c1300c1004403c0c01144409808648a03400040004074802070003402d03072490221580c26441001724008543c66127800c0702e070910341d45a20402e07800350000c1c251580800b10780f8204000398105070304941c487e400c602c21140640b01c0813071400c6156909001d801007400d0064030345500d503652400c00038400c049911074000482c840728084080e0600c207000f00ea05200d11503038001d0403078403c140304070000e6000401142c101503840461000d10f0004c505000d42070784c000d900200c0d0441806100500005c4032165042509110030800c1000c0d40f620400d42e64007800034207050fa004106800e08613000400761085254407803a024000700f60a074040c02802803604882c400f04040c0e030400c40e0024041c412800801003d52030359804200600d40185000c0c1d10020162025003001d980703440d640141d81040382000720a5107101410f200324105410b410b604c40d000011006100e500d580c4002d007075648000c100111001c0300000050a05009402040066a00840c140d55070714 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 10826374 1250 10825124 10825147
    0xc0f0a1206021306050f030103020d0f0203010903030b010801060201020c12070f020604060f0e0405041a040201050c07090218010c02060f0d11040605030609010510021519020c03070c050a0b0702040c020f0102 91
    0x14451000302060310340020340071814620170815158a000507807001451642180c08010050080c40750803944040c031051154010b8a0a0060066492280d140861240f01490024148400580100c0c046a1041c0b008500e140800560002a03440007600d5503681c2500b410034480302000000c003c0e40041c40040e001402e01c2d0300030b0391120048102d076241300b080050740c010002652000c4d180500012620469a02c1c02002040480e40041c03050501c20b08e40040e942e082400c288a59008400b116801708840d0302c140440d90959104501c00d103090051003001c0e90001d1041d0241540b2003c164002240703480304c6509070342c0903901000c11210074544559440c0c0d0000c0c43e550003243c429020f100504000a0b0a06003840489007102c1141c01416000001034244d00c06000010000300003000250140d6009250920040421002c4a0042d640c1c0c0e078124209051610600d0303100e24010a6090300400c5400004400d0b03850990381280c000c03c0c0403040c1d0400300c0c42c20400e030700080364a520008032060240d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 10827624 1250 10826374 10826377
    0x605030108120909010b0a031512020a0803030c030c070c0503010504060606120c090b0708090d0b06010807021209061803060109051801090b04020d050a0803090703030e090601020c0f0a120602 84
    0xa403900ca00311880ca45441540001030b008915002e0b41065013400180031a0300e621020301051041480d0000b01d0807800d49054014000a510400b900d00235055604298209010360302c0c09000d420300154910304100404002500c4000d0500c2580c0d040443c04004100c26100d1820040ca0018000c1c041030420f030403c28020a0310b440b900740481c0d003000c0600042d941600076000d4206158803100c0200e0f10b4803d4981041c1d21020080b200c140c000c004140f820360300c01a003040c0300742c00792804040e2881c10034005010410060b2400c015940b084110040818290040b50b2003607400b940e2071511f41c0f4000340701007160104030384040d5050140d04004110305010341e000c540b152004c5005440c0345111b9011181c00c80d441e07034a015000024480004001d810440e03207600100f0720840803a941c048a94854090b550019030300c8010b1034028601c20018158080703003141100400b10b55411b518100040082d65808081d0f920758003d41080b8003c4150355100c00c0300200030021149140040e411902c0e000009 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 10828874 1250 10827624 10827629
    0x402011b05010519270305090103060b0d05071403012301090306050a0902100e090105150708030c030a05060a08031c0216050c0307121509050709020d090605010608070207060806030304050a06050301 87
    0x6081c0340103100b003058400d43c1c008a000c80744001040e5411715080e00c04071410b5000c086401e06054941e600080e625940700b0041003081c98103c4006464285403400418004100000f44040d41c001c1c0010320079400c480d02c240e500c1c44480c04007200d03a0301c903150050b03c079510a0781c0b01400492500041000e17401c0c5070780044450602c00c81d00240b03502400d4400341c58602032441c14a0300450310740e0061000d403c2006c0c501036102d0350603203d07509118403940c0d03d09a50b44200c4075000012800700500c80705560a00810750009070890b185a8000d082000317150b500d0080c0d405000400d607180d404108843c1e2247d044446002440d8035200454010f410865540c14800700c05500a2189000020348400510b603010440c41c1d10130515040c2c10741d801e8000000e41444002910707203000d0701d0030000d01d00d1120303c01480304500c146004a0300c4007150410320704a40d8164000e00c00d2100000410940e0f0398041045000c1c2c5200e400d022500d03481e18808a4134602450f00555041901443d01180b42a08880034504 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 10830124 1250 10828874 10828921
    0xc080307030518011506030e03040b030709090b0619030f0f0e0c011107210804180501090b0301051b070309050901030b10140a0306050603150f011703070203060402011b050105 77
    0x941e0300180c4a0307401c031296940d05031105c003540501800000c0c0b00343c000c2d05001082104407800c003070301d400362141154415555400070500c042410006025207000e00c00305223100711010f034281490300400400d0660240d260008060340c0f008204017440c0a43e0010802118582081080c101c1104209549680f2072582c54003140070810b0390b5444510014240c0295805100845600310000c08076004d0182c24210841e100f131020711003c2000320455003040b0004050050100f80e03035241c03181c6101281c000f420742c0f600a034188800c02005140307a0b0001c4104508040380103542d00c946050840304da03034044d0012a03006d96030717100000038400107550850044032003081080c91140c1d241604010044c0385c4d041c0c03681213540b0800400205020358080c983c000c2001c0c06035207091030780243d103942030a03046034859066040300006010b1304c40d002c0501004103a404009614011094000907910b040040c8004c8c104190302c3e014560b00b040c0400030007040c5c0d9100d0024040c506004107809054915003000c01c0c0d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 10831374 1250 10830124 10830151
    0xd02090105160510290d030c0503030702030301051f170901060504050a050a0c020d020c040515030a050a031803080306060d0902030328080112061a03070306061d04020303030a0b010c0803070305 85
    0x8210240e01c4245400c80170360042e0b10100c03022000910244070740c591001e030140118450200d012036014402503125541b154003541c3e9a40c10035040110300b501c0051510760901001198000040d082400b11403c01c0b00400c1c4120b072659002c10325805440940c0000350424100401c1c40f400442940150b03001e400b0202c414820040034000072030350f0b103040804d110016448802c2c0c0780340d24107043d400550031003c00c2070310030000400d0801003407504074a018100e82503408540305000b49903021000180c1030360382c00240e880491860703c5003c000c0c00054070891003010b0015038000101000d03805203a070f03230740e0207402d981c3c40c2e40200092900c010564041c1c1040f020340e02c2d0718880802c0c42030942905840440030200c03203000c01500c1d8100204887c410191804114258050440d5810018080210b10454001c00c4003400c001611581d0068810105074000e1b01d40144401030380c0100550381d00c05082280000c05104001c01220260000384000d800400c0000c24014105d506411003842840020b4021 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 10832624 1250 10831374 10831391
    0xf0106030609020f0f100302030702010b1002030307090918080d020403060903090806010503070e040f0c050a0f081b01020a021203040506040b0d0e0d02030a030e030d0606080105010912080d02090105160510 90
    0x1110072001030140e91b0780090007101c0032400c0c034007940c05141c102801e4400066103110540c04194012664a00940917034404410819660f03030200300440608154241404040440301d00010f0a201d047d000419107400400c81f8000c600b090b505540045070004c00511010a181c00c1c0604200b60502443c0300c00d0045c80008180342c00c0001d00c0c8801c903001400c0e90001952513446800d400a003401088910040745500001c2c0340e65100315200c013901e00040c2580d5602e1510303440c3c900d4100c80d5004884800d004101d2884182e80104040c041d594050b6155402040510141400e510807034000350350000703000c00e010903a44c002c2e4000d8004c0602e0900c007085070060084219558070541e200300ac006074010490725145c00d10036001240c0b031501502c11a4100031031944450182c501d00d030840d03000989940c0c010070403507902241c81030060140d8034840d030540c900354a80510b02e108a0b0981c0115503000595141079900c140111003910500c462050070760340280c5401500c03a001da520401e001801c15851 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 10833874 1250 10832624 10832629
    0x5010906020a050304060c050a0203060a020a030b040612060c050d090c0302010f03050f041104021204060902090c0309070b0315030a030201050402031b031b030f0319080708090309010309050f0106030609020f 91
    0x10b1000e0503004402541054a002801c46440c0f0500e07804552600616003050016182040740600904010b9400f5841e072103102070040403142c01c041594130690402104001a0800d900d26101e815003141d008960b80701c24450a450901c600c0310515005441c06428100340140c9440400581e8801d9031a0300014181040860640e4419035400d003c10404602203000122441210889480c02070800741c01c010030680600404c0030226412f555858aa810b8042140343c94000c0a9004420200160135805c19080d055580c00d128041c540784000d0005c086524032800440d80500e011000301155003a03112464028060401502d080b4020b129100b450040119610036512801e40050001d0907042e5000c040d2800000000b6103403a0580201102800c5002c8280014401902044042007031010140401401c400b170042070345d02040b80e81300034030080c031001008403a031429091801090011440c240182402d41d104c48034003444d0710300300f800020498941c01c0094428000c61ba805848000c2006 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 10835124 1250 10833874 10833883
    0x30507061e1103030a090201020f030f0304050c040c0807030504020a0e01090c09080606010e0904150203010e07020c0402070206070f150c030b040614010e010c060e01020f03041b050108070c08070c090203010501090602 95
    0x10001400c3d003081c03001031482440c650101c607215005104680c0110480190706080d0760150a0540704010000104014000304001c40d80c0340b69070a9601b00114060b079580240701e81405009142050f03111008a81035584496080300504082144003049517503030040400202600d0700c0150126011f402c00040202c404a4168400d61040e10381e0901d10340454204062403000800480e0303405025401c50401388814806540a856810584c180c00e082500e00a440d0101c400c1c1d081c1d100358010040c10300103807280002e8564050b4080c002800c50415480c1450201307951101c2c0c00556850001303c204410f03815000341036a5103064404122107611000a00c640e10070340c2883d107001c5800640e40c24110351084013070400c52030142c2c00018001e00b06031605800da030311155a13480d0385030300402803000340203013841ca482001407400040307040249003e0001c0c0c40090002d01c0305003401400d403242d10a00101c42d08071120360f1b501c2440309c07800e1500c0d401c040d8001c0d0000c0c080c1a000844111020507400e00004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 10836374 1250 10835124 10835147
    0x305070c0309060f0201020f040303020c1513050d0203030c01141e0105150c030d0f06030209010501080417030705070507030506071107060207180b0603040317060f01140d0204030507061e 82
    0x1d0b6030342c0d03005040040a40e00070002c03060a40840d90f080009500041d849005400518032030f42c091320060a016003003061a840800342401c050604000700c496403010b8040100c2140c1c0103840081c0a090b5a00029056005544242c040c035400d01000f50b04c1d0b0070408180c2e5100d1080e0216004034404c0c3c0000907280d56000b4010389401c4144404091840401c3c0005040400031280440e490a40080c101c902540c45900309080b01c2a00c40c0300600461420300d503943d01401082c070f0610000d01e0907440d0f55803c43e07144030030a9070494001010980c1948202c3c00c0750801c0e60032100703c60090f030740c0780f90a9580d45021203201001540c40b10b01c2040c0c43c04003081c01e404441c000e40c0201801401c0072202080c00c00200351092840342e58007a86140740d200d08018521660198440582420207180d000194503802403a40b441001c219441038440d88e004100062041d000c00c000380d0710b905541c010380e0028410307500050194822410009a00d40e171104442484011410000c9602c250f051008d40780b048004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 10837624 1250 10836374 10836377
    0x80c01050304080915071a0105120a02010c03091707030b060405042003030405040905010518031c0f0608010509030403060b01081015090b04080a05070815010e040f06020f0702010305070c03 83
    0x7040030030041540d480190504101c014070b900c8503d4802100b40c8400d60002d50700f2601c0e54101c05c40a803c88042c400c065004050075904581c4210700706161640320800c7c000024148208103e040381811310541c03c040162200c0c0880a104811080c5001d81e610b0791032104917600307400341000802d1030074203025030f90241d40d12000710716210400c55000d240403452910b0301078041c4401d1200256503070356401941600d60003100001500d0800e108140b00da0120300c146e40e21158420400705119407402401d844a06a1524000403082c03002d071700080141411341c0c016401c641c00d00050101d03188020009104403441035000300407681110300196072820003140c90280030706c0092010410500c00a9040340302c08030929102c80100d85414041c582500203030444007441c0d0000200c1c0307007004020001003010b03000c0358000f42154400d8520b24200380405016419a20084101003000c000140700381080301030b0b102e1404c0d0b4851001c0e05d26241d05401c02d03201640042d0800012900e0b05000310101417015815 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 10838874 1250 10837624 10837627
    0x6040209010e1203070f03030203040218010302090a0c090503070b040503070603051005040e03070b180f01020310050d050a060c020606011214060616050610090e070b0301051e030d0e0a080c0105 85
    0x1102000b0443e824518951414001008207400103003115035803a0f8128807a4500580380e00f880d0040c82140107811418a84210007400144050f036101c411060303000d0320940e000301e000c901d6084111a01d501da5032000f03070540700c0e080340402c244904d40090000d552050701240c0d69642e541e0011020782d04103951070101720103884c40a000d03500f403d80000e001c004000301203918210040c2d4a60500301c1040317600003079200320114040c44014080c0700110420154000075800c0d421701d100e02864505040c03045a00ca1440500c1c0c0300d00b008001d011a260740740d040102003003203010710700340651103a401f00c0d0442e0004400324070b42c8111114604c10074500503050b074841c14240d80c0d00e50034010320382d1104584007041e114455000b80010790800816100714404a48a800245054004000d461002089003003607044034405022a030702c0c3c0c200341c80c1114001c488190310200d98403c04d02e0420315103d12580c15001c0d2040e400c11040c0c2040f80d4840c8082e00707030303010500e6070354540c4040d8072508840e07140313800202c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 10840124 1250 10838874 10838897
    0xd02010506030a03050f0a03020906120609060301020705100b0a0f0b0301060206060607030c060504080c070902040302040b100f0c0314040602060403020d02010e12030411030703030f02010e01050601050301050108280b090604020901 101
    0x10785001825007e007040c100145480d00030400110250010310304921140c0940c0108240d07810240020b80c0c00c000e05600070341c02d00500d95219611090a403006255440d43e4402c00c2c00656a0104034400900c031a80242d81240c0d110200111194802d00422016100300004030f03a40e414850304450b816501551003558840b000d9545601411029000b543c40400501640b04400c0d41800354000401c0e1407000143e07100d15520500c02500d580c04040783c42404004414103c0c01e8000c071001798140040d01d41040580224901a1091a1044035049102001060200d44a42c000404a018600903000c0700c0d60b212080c2402c84c00e990031869800140d8112600d070500c1d01c03021901654100d03115143c0706501c0d20001020038030b0b10009034000d0b0000350003020860764440d02849482c41002010009004a241c24800688103110610038541088003040000741c4440c94000e8060174100d0149503190346010182c02200030340302d11000072b03126070135102c0455000c0c6400c1c42142d0480c03e041e1a80c0c2103222 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 10841374 1250 10840124 10840147
    0xc0e040b18070503030a050c060a06030807030f05160b04030e031f02090103020702100215010b0408060402010c0303090b090304050a08070e0103060e1c03090b0c090112020307020a0b01080d02010506030a0305 91
    0x49480c0c03100c1d00901c501400426503940910161010603942d07541d650311040c424400a180c2200030700251003503450118103001103249102103850058040c1400121285200c00481d0148540c2e55422903082602c84480204045011464002d0b40070f07540d030000c0700180208240e2124020039400e2070611140c44c490b40f414007613402500d43c1c1c0d03205041c01070401c2059000310b10300c0c01c8401111300c0140c1111b099180c28141e61003107240508450f045e85814035060544560f81da0350042d1003e810704c1900080507003010b11076000480c00c160f01184000007400c0905060b5a07070b402900030684030300f0b000c80001c00c420500158120031514030340c00c0c1000c181d103103882c0d400080418400243c903a00524040c2021700100307000040c08508542c0d400900b4104ca030802d00d01012000e041001030399400c00c400042aa03208291030641c544121006a494031035607011303460440c140c01c0040a9a50030000059000c0c0c2c081000300e0800601d03002804681e44a104060f100d110780603004000c50800d0000b0b10140 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 10842624 1250 10841374 10841401
    0x60a060e0d02130e070b040f060302031018062408040209060301090b07050403021005030609040209150a03030201240803030c030411130905010c0206011208070206040902070b040c0e040b 82
    0x804007504126045140c1d03000f09014041c00c1c04120b80c540d448407400b1813130714020030040000f41800910241814209064441d840702c0900c074520401d500030000c681c2c2e901c880029600188101c41b00c00c10a80102c083c44000303842c0b075204440b150303401e000b542c410355010280c00300c4000c01e1907076802d441030b62558204646000c0c090301d05074156503240b580b0400255003c0005004403a180c4440d902e840c0b541c0f04001e420f1402585540400c04180240300040d1502d420264109030704136041c103102e507541d4181501d402c1a16030215072180e026900003040c5501984072010500d815146c0080300040130703500780620040340c403480d08a98010800510658005406590070901c03c0d00000100f061440000b0f4030031038100481d000843d5540844007c105007442410f054621a001620056151520700075201c0c00380303440a88a40d01c00180b2400315510002260040c0400c0d42d0b046440300094280650000c00468040303880481c03d20740801d00d1712180c07410603c541e500501a855a40d214410340402 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 10843874 1250 10842624 10842647
    0x70b030105030706050d180b0f070309080d050403120c090501090504020a05160302030c060117060708060108010501030903030207020604030c03051207020f0d0203010e070b0c0c0d050c04020703020a0606030f06050c03060a06 98
    0x201c1c3c0e1f40e01641c4104c2c1050b902d032000f494024009029241440c2203c640c802c08080d0a4400741071800c1800c0c40044c1242d41992400c1c0076909000550b40d8441c1010f5441405595542c03070351514250003056950380111001003990000c1e07031145100c6444605206c2203200700d244450218109019080c1d582420101103c0b809102c0c0c410b0300d080c540204a100e18240081c1c0228031900c2190020010aa60070405940c1c0002c451030245c5207810240c00207040301c24180991410942c407141680705050181d0119038040340e0151150342d40300c3e82e0782054540614540000c83c1e0900031001c40e0340c01d280c03e80d82580c5031300e6001450303510981c04007001c201c0c1c0001e0f00d8800700d0705952514404200c280c000d0080d0700c001c004d844202c0d5507030b45410740c800342010400311301e103440340c000c40c0300c800c000c20070010b40440c04c2c840030384005035180c0c0c45044c01c1c1d01d0955041030084c5000c0c24590302008002e880101000c232544151014016501c601e0802501400101e607110381040034050204081441400415072 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 10845124 1250 10843874 10843897
    0x40203060d0b0f0103021008060a0e090708120a020106080d02100b220c030c02010e0604150e030c0304080601090b0d0204090303020f1206150c1005070e040617070b03010503070605 79
    0x8010701c00c1d40d550742680710840d01800304820f200d00400542c00d000e0301003490050589400c0415151560010700000b003140200400b841c940b10009152900030042c2101170b00c203005c00c0f1003030541001040c54003a801501000300550030704800260140f80003800142d541c1d01900038008a0605510341c0c8014070a07005840c7d4043c907101003042300101c11b20b00420007004c0740a000700e00c40560031000b0301900c01c00b189650440e803410074110541d02012a4103038106502c000400b100600c400b91420103440b070414420550b000004141d03055510000040c012106903e041d20040daa071200098201c03580030304450380000d4054401d200500d059072040d001e240c800d080050800e40d0304c0b00c564949400c6015040d80180220741840b0315403814480c0d44107107000c03061015140c030504564094540b0215441c4c07025403031720707080070840703060040504030000b14000d0b104000345503882d50410400f03054440003c50600030910082000460b0000702d13410380701c02030002e007280c500d071001c1181d0b103600c02c007060341 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 10846374 1250 10845124 10845139
    0x40503040e040302030703030b031b0d11090907030b07050a0c020118030803010b040e180307080318030f18041b05090609060301080c1008070c0f050f010606030203100504060b0904020306 82
    0x307480d01e0421a0140110300a90081d07480701803e1a02500b141c069240c49032281c1c3c4036211081d074000394006000c2d42c00d10192180d17074010f00d240c42c00d00515580840003d91101c0410308108803040c00103140000c4a00170a9414210f8941d09800e0310307644540d80500001411001992015500030065125103140e44100d81e80075545d42d13284e00700180c0003a00415000500024208500310905000b80d41101210784d51400c1382050101d0150340e4440d0640041004001200040d291481c45543c0f80210444134141d95039601d00d801418100e5100b207440c0210074807003190103015420b00c1c0c891381ea607a12840e03045040d684240c00d0241d8898005000165000b44108044005e58840031301450007854460014420341040c0820080b03a40303150850b81c020820148100b00c2190380c003c490180141d000f0302d0080c440082400c02c18107106110745c43c243c0c10b43c2010310004815600d903004521904040b913030704114548035800c00007510140d208551584a040c000076070549010b900842c0c100c50b0003807284 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 10847624 1250 10846374 10846379
    0x705090d060501180f020c0307060908040b07060c08090607020709020f1c0606030e0604080403020f010e0603090c03060903040e01141909090201030609060b03041205090d0c0f0f08060c0304050304 86
    0x42050b00c000741c03c03101d2080400c5190700e81c9143c0b14041d2103c4420311202c19401c140c0015929aa00d002e80c003000b1f000036846641c0b0b07100703100801c402c0f80d02800340c1022081d603075990780c00d08034058440f00c211400080c005200164950001240c1c00340911a594081c3c88007a04d0b1172840300107900b0800500c80301460401507603880003828900f100d016000c0da107001c46c00c0342c50580060100c03403504100d05000e401150401000494040840301900e9044231020341072420700b4012108100d504e1030880d0409000002d1080702d000000f07062500c00390440460303c05680da11071007a200e0059200b01202501802c0040c041c001e03180032500c690840c082e04026803050315000c00a2400d82036030003080c0340c070755800d000c2055503418010440900081d0070103000c45032078041d40300f00a2200a0014203000540e40180d220203100b6011248840801014804414000e0500c40002c89840c405c2803241095540c00058090441080c2c1c0100e4518802070089903981c000450741d6540004c008581d0382c042000003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 10848874 1250 10847624 10847633
    0x2010807020c0d14070602030301050105032202040c05030a0e070b09040f0902030613050607030504170a120e07060305090d0504150e040f0e0d02070f060e010c05010c0c0201020d08010302090705090d 87
    0x2203c0c00c500039109101c10341c00c035100b200d04101c056000301c41150000c1005000d1a600071040b030344c1110184111240c1c15800243c0c8114140511350001e6220f428440718141c015407000196014803140c520230000c1004800d0515955001881265481d84042c080203110b0329160b8490048040080004a40402d01e9130009003490030031608102407100348039401d418400304001166101c0c0950030200b08504283c0c84041c4011035100380703403010020000d09601468481c146080c088a512601848580c68650000342c0f100e055006400c0081c0c1750600040a0300f50000e4500c00c44000ca0300e50f03510f09030400c03940c01f50100c00400c28405114404000200e542c80d02c0c840c80c400c0442500300040c81040c8442d1681c200f0b00b0300c8140300f00310b6000e160300340316401d00304074500b044074000c1c01e180e20100c4988005031600740c4105c801621075440e185846005030703005607d039000a40b0076400d40d6086943d0581c01c2d148000701b8000a50014143d030000340109008a0007011070780c000511518140c00380d0713030310b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 10850124 1250 10848874 10848889
    0x9050114070801090603050303040206030702030c120a12020909040f02030325020103050610021f060b07080703020c01140f07030507060504050a0209070c05150a11040906061202040e0402010807020c 87
    0x1900310030a80184104507400b54400d0a0b01c0c050614102d05121403440c0d512074585c2c0b0f010140c0060f20942001010a28182c002c1040b0b5103020850002c0c0d030051246c80d00244603a0700065001f4001c01c0a1401210130421103200316050136200034580c42e00381d1501e844400c0d404038100c07002c98040c0710400c11210f4008240c40d980c903a4041340021000c5c4034907184001425240e000d420030f070080c184c40018240454010550040b82c6441800710002c83c04504107100c05000750b40e0146c0000c07040020500c0c10b121034900100162170194080b0340003500201c00446070f2000703404141d10980010b0150361100c6044800801906000380ba006040c0352042e00d41d20b04a60f801d8600721015480250404210b08181e03415603800a4541000e8203460065107426482e203401049449a5140b0440082c0116105a00c540180d01c010307007429880d07546600d02c600060103d8060100850000070030300032207020034002c460988038040704015580c1c45503801580e11143c05403140c8150302031441e5026081d10703000d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 10851374 1250 10850124 10850141
    0x10b0d0807020301060509060d0201030504230123070f031503020913020102060108010b1c0203070e1e06031b0d0309171e060403080402010804051c05040501020c0f01080112020301090501 82
    0x4080581e1068203204050131100c1c650700c5180542c1c035407010000e00746c1c1c500c10507444e29a0207080c003040700e650f03a16010b21041240ca42110ba1611507828840307001105611034503401032600c03000580420034039a452000c1074100c070080c0004a0362540c0100480c03190300109110005040503a00d0580c60742c0c009004920b04a900100d0030074091414002d541e07040003040e00504401c0003c210f00352092010401407121000565007108140c00018115202007203100001d00c0a07200f8440e03642490703224609500ca185e1034080314014800c01040d42460f0106040d98014070301904400980703155020b1000c445500c0360b0590500041300400101070460300349034140d185145002d0003c1d90003400030a4541e82400444500b507034802d400b08000280c124921a40003902402c4c00345117580c03146030440c64090109282007410006420110809410001920546030300344c0136107407901400c200b404000100c0c1025603002035481d400411141e1f410441d10039800d4000390000c02c0004281e118a42903c1200 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 10852624 1250 10851374 10851383
    0x81c020d0b0102011505010914030f030c0a0b0c120406050a0e0106030524090606060714030403030e0a0501050c0606090703020f040b04090501050306010602060a0213080105070206040302011b1b0203010b0d 90
    0x40503607401c07541c1d0a1141c07000c641e80117044002035609140000b002d0603c0c4d40556035801c10000c3c0e00500981d42004620f14130381c40c2004496981b42c0f0425070588548203160211041c0400001140f50000c00304152203e90502e03021040d030940e501d071a10000f5150140c20507100c01d56072017680580b190300b80601c60166004000500209000d184c0410f01c04c460b2007850a9503108420138880d140d031021038a0361f004102202c403e5101c210b80d0401c0e00d00c243c02001c004480344000940007041641100c200c01d4450f030201c5850030255954001580d00388188043d0a000303810403000214036107000d86c22503401582602e4018101460552100700c142e20640010300050004102009000018060240904419400741101e5498030602943c3e442c0003070140c07401036401003080350303042c22555100c00050500134000d2055042c141e4000e51980070a541c10750040d402c1200c060f0030b0082c04003500740f1840326650f903001d0700108513003041c08600d231411081780d165484a0480f501a42d07210944075419009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 10853874 1250 10852624 10852631
    0x303060f080c06040905040809120d0201050f04052a0d080909070306060507080325081503011802011101020705010e06090c0307030f0b04020a05120127080403081c020d 74
    0x144000c000c01180c00754060403056200c840400c0b80c5494100607a802c5506901012400782c0711807030468464011040090f8128850741020b0940401c0003a104c00300d81b585400810042d165210000c106600842d0058055400041d80402c0b5030540360200243c9820300442c804125a140001600d442e421141070302c13040804501d07003406182c600030380c9800500508003044000c1c43e01002404900805901521041b0044000740584a082200011807030300984000c841f05030075000503140e01070980c1c0320043700c60310039229001401c0501c00d64480186c4011075902043c0305d54011501007081c016450803954007448000f0004600b401000c40042004e4040d003614541214041c3c94400c8281c0c9480c4258444c000420118a10007442101c09800400020b4240d40b50b00203d160318840780d0205401041280c1c45800424066010cc5003110745102c007144031070801d1034030f007528190700c4001601c000c03802c00041000400c007000a151018001001d05400701d42055000201e801c42d1500b84a0280c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 10855124 1250 10853874 10853879
    0xd020406090f0e06010b09090f09010e0a0f0308070903020604090903020c030f011b140d02030703020c060f19020f1602180c0a0801080f0d030b03010f060906090605030f060c071a04030306 82
    0xa0600985001d411b144d22a1810401000000b0301d81c01405440300d40d035038071140d020507002d10082d000060403100e603404555200c1018034003030302900c2440704140d0008400501046506104e04468400c694004111034145810081c1c08402440e40c0f000480c194403c0e086103614549061160b4030750003092000001d2504d803a4050f01c1d4052180c43c2040d0200220354004980d42a080c8050700e5141c104030400503283d0f0341c0e00200390024803500480ba075140c13080504120003c6081c81030180700d0000044c1c4400c00741c400070b03103980583c0150700c0c8125070440305228007100c0340808481d0b0440f407230000f407094801341a01010000f0b03e600690342c105805c1c60005c1c03441e4407140c00c0340d0b4550041c07403c00000d160a454000040780c40700c00f10121001059200c1190b010155800d41103856901030485c000c01090380c0d0390103610001c0242d0700c50903604a0034240001101d182c0414a201d156440d0405004140c2c0d452a044610f940001c00845240d4141c20001481000c80d41d619445180b00340c0300000d01a0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 10856374 1250 10855124 10855151
    0x703091703010f05060c0d14120414070906050109030b1f0303080714071109040201030f060611010c020105060901060309050a06050103050307030815060a0c06060b03100303030e030a050403020d020406090f 90
    0x84a60013007030181800f00b040d5201110002030070b105a6105203090004140d544400903010300c544115010700016800900c018046102c20320008503040c00304550069a0301c81e401801d0b01c08510840380890104942000420300c03601010b6030081042901c00005800314104a09490040e00b0660000354458200803582c1e40000c1038541600400d902d007800d00e40103640380f845d2001c00401803406a003950010404590082d04240d542040103a0700384005a142d0700018101009803200092660030441031080f000e00600c500ca0054230040e1801c120341c0e080600c19000380905181c102da940c89500036010101b1498820103020710700c940003441c1d0780d01c61410000c0407040041c2c0000e464811910280003c0d540d403038200c44099206040c00300c0141c6142c00e20200a19141d449002241e03400002c00111030001440802034038480e4a080100640124000307523079001381c0c3c4903030002c503004010031b2007d8a440e120400b0641c0c4014004140140c5400b80070044c4ca4012150f000310689503075007c9410b4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 10857624 1250 10856374 10856399
    0xb030d090801053709061802010224010b03040f020d0f0212010c0e0114070209010f0608070203090a050f030c040f02030108010c021203040303150803040618060f0f0503070309170301 80
    0x542112038102c640c104c070100014039681d40104403c4070182c90502c1c4161130b03203600124112600440c0400c040e0520725100e03003101418034804c07030060291000003e6a94580c0310b80c9040500c0d61480d072003903a030904942464541c0054001d03108801d8695602c00185d50b22134805007030382e00c540b2240551501903c140100911100f0304c480c99070741851864070905d540407900d15400413007403903c0c2e402e801c0081401000d600c030784203001c0c0d044246200041344103b00002601e048070595a15011160344400040303031603014040c061f0381d0141030401c0400807854141c0c0801903501005003542d00c00400500014102c440140d4104412038000c80108100f0100780f1a1401d0901c190003e050585c00707040e100c1d2218880248001c044c540e9900c10b03810070611a07890b017009408240122552161600350107026614400c0c007075401c290031190302103103044c400c01341d4140f02c802035141c40c0d10203074202005a400d238200401a0701010780d196a0000403035509109107640441c1c1ea421a5969411f15003d06c049 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 10858874 1250 10857624 10857631
    0x8100c050903060712060305011107030f02030703080402010f0504080d2003040b0d050a06080f030c0c120a03080c0906070c0e0a02032802070b0f060102010c02071a030a0b030d09080105 81
    0x91000a111541c42034401062260744040649030007048600ca1116000040c81d9940001c2c1a56182044804034280224020801c1a000b03807031310007140c0781401040b65a0312400000500141ca80e0000c58019402614240712048050900e14101916068110b182008440d045400502034920000703d446400d029a40050a20760103585014140080c1740014481e101000d09203079546d000003000d215080d400100500200c0c020781e0540280c80840c160340390050a00106640900450840213151420940202c0c0400b035000e450b08600c1c5803401d4500450003071032120080420000d481d42591880c00030425288901c0000d07401506144458600003001090807600a00c1001401146403040c048401d18070740d01e5214001c1100302d0051103020340070740c4030020405010700060140c008100c10304140304690a9000b000104283d1100320380d00c660500c2000308805d50040c800c28015170120007940d20030000c40010800c0120540031030315040e5071a001d000000c801000c02d0014010a0060540 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 10860124 1250 10858874 10858877
    0xc020d120614060706150303180e01030b0411040f05010b0a02061503030301210503070b06120106050906060703090b030702010203040c0b07080909040f020405040506060301060605070b0402010c03050f0408100c 92
    0x52030b04206601401c80c0101c54440e11031040810444100003441e001500b00030070750b0803403610079a984c0c0303009400c04201c2840c0b8070344105007a0f40421061240352100341200d8024181003010b4030b60342c5507110245c02403108941c0050f00d45841419443c110b000e80d0b4000c0c81e000c00307141c1c3d0310411150000d082c43d00240c000700c003e203a24180130b2125500002a00d0644015501804070304013005100c4140203a80f440045c80740c0804151070082c8000c08a503203118510a407034204540b01c900c20114206c1d10203029060f0300a4105010074140d0911030064180e451180c10107001140c1c580740700ea40343e80c008540c8540142c0d000410001044105600314009200520b2100e04001c0300d9500e803c000c0c0101c44040d8014400c2d00002414004140c0d1500c10091700500f042200e0305060402d0364850b201229120700a42c201400000c0c213a100d036084500e0315821800d513088544940c1d004407006225814185c0403c5801d002d00c0303900b20340180043c8010104c01d070052100021000303000c000d44004022400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 10861374 1250 10860124 10860131
    0x601120e0c010f110106080c0406120c0603020c0a0507080d030e0601030309030303020a1215060201050907030809040218100306080c01050301080d081b0a05030a0605040b0307060305060409060c020d12 88
    0x80200c8000070360424807100900703100b168510003501c21641c4aa4001c1c034405950700b0300c1e00001b580c540100c2c003201c2100d415101807101c2078030341d40d080000c0341140d100140b840c00042c0c01040039900c280d000c0c2140c03203003801c15500744480a44400d031405200d40c01c02201a04407010000c0c105400d446054401083c45010b40723081d61440c1c034041d00c1c0c281c50340b02c05418103030006082503060f40721f00014110314004400c1041200d50344135800b55489120b00514015610f000c020400001000035841d00f200ea04c9440c01d490700300310b6010311000e03400c40f1280419050704e01300445002e644540c82c040c0100000d5400040e45840c000307640d8a0421112451030502008200500c2169004070b5140912110703030800c4c0d51240c40300c0000003200c15503000312000c500c2021621b054041d9210303009501400c0d043e40203112940c0c45000300f104540b030b50386545070306910007101081f8860007030700583e5122000600019001c05241c03244800d0700c101507003080068120400501320690131010403d9042c1c414607081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 10862624 1250 10861374 10861391
    0x30a0308040303020703020327090703060b0d0908040305120d0506041109090601020c030f010906050901050105030c0d0303060302060f041508190b060c0f0f10090201050906030a020904060e060112 86
    0x608001030140024080640001310503050600802c100c81011090946602c0603902e0024118204038415071300714800c10244e00811942d5102e030003580280c0d140388985070b1800d00070710b401c0070003441150b00c1200d10042c24000000424410320003220510452401155a0b0488254400071200006c0c0740c40d105d249000030080e000c804c180c3c00d81d00701070001d075803210054403080b0040c0e00d8a90b07448191035052003107190703212034000107401c01c081c0c291251300c0500580d01c1e80c40445007a180240100340d055409001d00018500e8030402010701a03001e03003000681c840d140e4010900da139100114508cc0504000303010814050499035201c02d2031040c2c42c1c02c18007130034a5102e040c3c2c030220081c0e1003082c060b1aa0490314540c0d40e81c038215410701300418202d80301a0040c1540c1611401c00410110f5540603100025078211f0003801005c901c0b950582d111860100c40300200105600007802c3ca1701110380c02d00c03880d581d503200c038030406000d0000c48100d40c0c0c007894001c000421b00585a07800b600d00c241000f800 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 10863874 1250 10862624 10862627
    0x501083c0c01020f070806060913060606030c1205040206070b040c1715130209040809010e030a0507060f020610061d181b0408060606031302030304090b0112020a080711010204050a030503030a0605030a03 89
    0x4142e000f90b2300311610f0f131482d00c90310380d101701c1d1555002e000340c8064500040043ca4a0b0103600c0b8039495503150f21820320b4040002009801c8410448000c0e42082e41084940000f03000007010980c001d00c41d40380808815203510a500c42c03c400a40040041d6000301c1c0c407036205c4644590002d60003c40d88122140c280c0e41c5501250394504080c00042c480403000ca45580142c1c0034440814907180c014080322000061424020b68030a0148212000300c0c00c01402d541e01c051022410030301c40c1160940f06262186001401c4850f80c5d103038000308800030022501001143d9805400d4070600886005410180c2000c03503003d1041054010ba10410f01c01c104005c100c0b445011481c680e0142e42220b43d582c072561000303121001c076402604003e502d8040080c0114001c0348aa000d52600d00c002e07a00d1038002807210300301804070f12a140c00600070a0550001803400ca02ca003104582d03c4120000141c10a41d4130400304262200d41d4004032002c0d00080104113141c1150b12a001c000c1104800070166141c05840 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 10865124 1250 10863874 10863883
    0xc0901021e0102040b07060b040e01020313030c0c0e010602030315010801050d03030b0f060301030b0403090b0f0301050904030e10020c0301050604091e140a0b010602010c02010501083c0c01020f0708 87
    0x10400304503460301c0d1600152260a605640c01410150400c0b40d88580c24500789000301096110140720754501020120034010510a480c0f03c1c1c1d22190000341406455101a40c1c010340c9601c08581200034150003003084041d10301518004d1041e900116201d080030201c03801074500d0051142e042280f05001041565102003681056981500b400601c048141020502c3c41e0042d0440c1900807030300000000810114901c100c0c1300714000c0c3e503204102526a2031000840c07051841c001d503481c0c2c0600040c4003514259803081d03007092280c2042041112000c0c045401c004d280c001070380160f04003031002d0245050078011664022001c403030400015400da0343d040800e40c01c04011040000c1840c070305a040040790007007403480c0d104030402c60f004488280f4104507180d0b400d004000040d4200065480103500501a03241603c8000e005004d02c1c00000901e050307080e22420101900101039044009000b0012800c201d80e28601e0b8044d1100707030403610002e8600f58001d50300500ea40e11458041060000110307 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 10866374 1250 10865124 10865143
    0xf0e01021e0f01020301170d020105010302060702040b0102010e0a0503041401020601080a06020f0c030f03010f0902070506011404140f01050a1a2b020c010605040b1002030315010201060e0403170c090102 89
    0x185a00105140c1c0c0707800c500e40020544560b10541c800400030a0786242c2003201c198040c0c00c1e1044480058100c1400c90980b50288402904014280156401840c26412811140c01e0601c0000f450720300301240c00f49024100a030a540d150070006080c05100c860b00c06d03800c0081170030300003404554076003c04140e64200304080989800ea01041a030020307040b11084407910b1140d00c08503500c0300c1082040b40541d038428451052040441c2c540081c48042c18026506d4040e0024040c0049030b190000c0180d450b42c4038103100350301030740c1c54250b1300b0701000d2881011b000e400f441d20000c0c800d60404050110010858103e84541e0480c2c0d032041e20126281001c40b00101e03a0702c0c044480c004d48140d0708422212700840820101400400c6400080700c0540c0120f04139482100c0a01c1004003030000d10441400c12510b03100143c20400006080c90303056400c80345801818400028026683e07200c4602070b04d000e0707500328001064810900c0c4120b000804c200d4002d000c0403070080c23800e403030100043c3d41c2d00c008a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 10867624 1250 10866374 10866403
    0x1215031b06080a1a0d05030c16030305091002071d040210110703030c030504030c08030903070b09150304020a030203070305070816060e0d0204091e06140106140f0706060e04030f0e0102 81
    0x1081006113484041c280c20f40c03d000003800c00c564044492801603180c0e04840403101851003144e803c10002000703403000c05c0440f40c050b1100d078540f9030a02c0c280681100c1d2052064198802d0400000780d46012b20300c0c2c00445040d02464040604052041060b091951500d100800556000b264034205011070501700b00d0790325090170307001c010240c5001c0e1102c0c0140c1d4030107095072a12a10001c0c074030a01000070281d1074401c60a5500c0305441b190201428003c0341e2006420240149405009400003c02190024001006503500590381d80c0040d152141a030022034842d0040c04080080f0101000106030f00b03440c130640c0885003401c01d036005081d20901030b281c034440c02c034080043d402c1d51540c0e07100304002130308000f840d00150020f82071009100040001222114541144100111403000c4024140c0c0c00720740d10950003038605040075019801c03d0000c2621498204103020020310030744903240040403c0411140d0724075050801030445003d24000b01c00744002840741841980c1c2c085420450f81401 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 10868874 1250 10867624 10867631
    0x604110301150903021807020105060118090b0301020f07030c120305010b090405070e0d0606080c06390106060206010608011409061009090e030c010501060504080a030f1215031b06080a 81
    0x30700c0741100d075071000f54000794008002c4006e80c0007079102c201425114000540007030020352200700045809413014012041c210103450f105002401c0c0c02e400c08040d14000a001600b400c600182c1e40c00a588200c10403004600301c01b00700003c0040c90301d8100c042c400755060410a5601d130005d904814400d41c81c4280c421503035040000c1d50240204a041d4080307501400b000d00c401c01600c3c00500a00f41e900454203c1e20400f5035105951402c101145e03401c000c81001031592600070010f403400b1403050071500b8803035a8012040354280710248189401070002e58020000307545800c002130a04807040e00300c11103994504d0603004460300c6000081350401d2058440805280880000300c40004007a0407062070341c1e0504000712404c240000150452400b04030081080380d80e1120295103d21807403040d0585504800c1402000c06d01030b80c01c40194080f0750a00015644c80ca4080c0700171590710565200100752540401d00034007440b803120103032440708900090396650600310090403110004224280381501e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 10870124 1250 10868874 10868909
    0x60106020705040b13090501050105040b030c03030d05090c03030c0705040f0b0d020d06020f0d0203160801030201020613050a0b010b07170f071103030408030304030809010f0501030c050103050702120409060305060604110301 98
    0x46011101c6170a411000080003d00c80a15100b4040c110070b10403c0e00c40e50420741c1c5007000d4580401c1c4000c04e014000c0080d40307885c0e011120f0001421000303011184a010303090010782140c070207000405494007854058a174090a00c03007000222148004a900d00502d08107007909140c03511940e0b10348191301107404d0703960b0015a10b025006840381c1000320341200d4001c144002c0842154020314082d181405400300710404112003203a0b01c80003440041d00503031009001c41c4026060354030742d801190044050315800c40e410344454800f03400a038410100c06900060b0300c818000075140e110003001e00c00c90b00e6440d00c850b40140e0003aa00034200302500c0d40c003880c0c1030300721217960800c1154010a440320940b916840d1a040c09400d0040440d2042550750070700101c03007140c8040d40b0845059940c4450074026090503c001100180310082c008000c0d489007005420524500501802c0149881d4101240c4e0a0070f51905a0030500087c0159000703604000c1c0740402400b500341941c0c1501c040d0220741b40300b481c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 10871374 1250 10870124 10870129
    0x807030213090e010605041808030402060f0702060406090509100b0306270405012403080415030207020d08090310060e0703020a0203120a02030f01080303060108040209151c060e060106020705040b 86
    0x201903900040c1018a800243c0b0500c003410340010301180d500720740400c507080ca000120400c11540e4000104044001c10004005260220290801d0f050400341e036405c1454540c0464019030050300030b0004500c0d20001003103a450032400306544030045100c0030710480c1c98620001c545000c040c003210b218540302a564052144518101d80c442c10109407604014141b80c28180c0c02000444100211020060007615000d180c0d41d100708222580642d00f140317018a0324a001030720003000c0d0058002c0517020031840c00517a50b07400c08950b046005101041e55918040205407030a425214241031a500700002001040c408a18050340043c3c28200543c0c0e030940d045013241188905410690181c6814050140da204568080e612078001c107030140304035989a000803590303400b040703a107a40001c2c1e840000034014204607004d150400d00140e043c244400400c00011a844441030030301168612011081040c003041d40110040c004600c00a0b00b01035060520094480809000700d500880d200c881c0189180c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 10872624 1250 10871374 10871407
    0x110111100b03100f1508070602060708070e030a0c090507110c0906030a0507060c020102010f0209030a11060c0f0102031e0105091305100218010e040213031403190c030315030308070302 81
    0x200c140d11400c205031020440c41c08010004803800c0c012400d04a0b00204001b20001003100907101c0e540c0050449540d042421a02c42c6001001d9008101e5224100380030340d101000500c02c19403140c00f0301144142009142030840314003c081d5001c205031265550198000030641e889a00320070f0700c020716265510350100b80350441d10040100244650000001c45c00d51005181c0c480e02d200b640288111203070a9444000d9000715003126a06801568031500001d10001210403e0a00a08100d041c20050200682000c0d4030302a403005d580d4000080059045000009136081142e41a81d80d4030f9506003400300710111002072550040c001407000410034400c2c1000000000000002c1c15540c584d00d440ca08050880c0056055000c160111410481c5281070f0081e108500d90340c24684c5402455620b8950040351034140c0381070140400c0010810104c49510280e040444544800261180c1840d00034100c400042c4c0d4102c4004041000744006070f444207103e90000c4d12445c0260f1100c021504e13840d40d0317 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 10873874 1250 10872624 10872643
    0xc0309043b0c100f080609042103090206040f0504060e09060705030910051e0a0c051c020408030f03040b0c03010302010203090103020d0b1815010207050d060e0a080c0a110111100b03 80
    0x4201c45203512000c09600801c103005103012a59405c035a9283c802c1800940311b030035100144954648400d10180c4c2c2d0342000d04030000342c56442c0100d04100707141c0110700766600c01c4c1c00030b6001c80300034a001e01aa08090040030000c15042c0155441da160043d81151120000f071700d040200200040447e011100070001d03000c0103800318508002c542490707200d250080e0711050540c82d0310010070000840e090001d11404071503d0007610f80d07030b00c0c1c00110140300c01d80c4040b010542a0310b07030b428400415155401c1020b84000c49405010380d41c1e82c1014288603e84643c0100701c0b2020003420001480141d0f8048140d8114000a0130056101e130341c0100c00102608402c1d07c0c0c0d40e004200240c03590025007125403d00e0007a803521041d03001152103600126160000c1e809416040704a059062000540a620055581007100d064906454565640352900d6100c680b1404165010203281014802490300010754140c0900307080b600c00500702580e603120705181a2006e4026520310005643d41c40c140400801c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 10875124 1250 10873874 10873879
    0x405060604030501060605030103060c08090a02060a0507170406140406090608060d0605070e0a060306050a0b03090f0304030f0302190b0402040509030c1e0c01050309150601140c0309043b0c 83
    0x1c3e51b11094018101d400911050382d00500300b92040754018000c0007485e00404a600141c25240c007943c0900009034400d81801b010070804100130000304000e11503116015003104481951340b0b20700340008005000d4101944610b031002c000405c00705401c100d40108a136124141204160b503601c0008205203c40240070303010344e04180800a903203912851018000d9800c5a10151060325110101c0468425024241d0001c01c4541c00f0b21003504810081c40e84980c9000c122540c910218510320b0450300b15078401c491403044030450200700f540602041079440c3c80a43e007580001c0f60b981f07460780d011030040e202074001c07a82c55000c41c01000003441140d0145103603204440f17040074141c80b9040034014054241446000e1607415150543c4203104a9005411043c0240101040710080b0811010090b01c100c0c10f00c2002890601c00c7c180c41c1d400380034207502c568050b649a14036881880709480f0310404c2040e107280c210388400403800540603440409044020110241d00700d402c04c09142000060040381e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 10876374 1250 10875124 10875131
    0x504030e040c0806130b06040306051009060b0d0c0302090604090c02160f0503060a0507020a0312090203070b030405060603011b0e0307050a0e010f0803070309030f02060d09080a090803180405060604030501 90
    0x30b00642d0491003040c05404183c48140c0d030f01030360404031000c1310014078030180e0001c01040104045030789074014640124840e001c8681450703440c03160340304640160740500074105000c203929205220030300c00c0c50b080014030f0509607c1c22002d540001c28511a902420411654419014420920801652204d854802c00010404fc0c03a503040c5003090450f842154403e1258070001068680c450003018000d005d541c008010309980c65600741c690001102a02c1071482d41d40c82001c0160760708100d5107000b41000f410b401c1e5241050300b4194102880103152070302903814080c0004e100147c80300c1e64030752111245400380c000c02180c400203081c1410f541c01aa884103602e480803e030003130740030360050483d403010f106174801d1992014a41d4680c00b0f21080500815200c480810203d1a440060801144010466450024003002450444442500940d910b000226642c040e003a0030050200c003801180000310b06104020f03040c2c0c0d200300c0c08034403014002d9031070340003040e9103403034250643e009594000c00a0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 10877624 1250 10876374 10876391
    0x108192102031306020703080a110a060f0f0c020d0c2607050102040504140c09090a0207050d0e0102060702070302150c03071a04030801050f06090d020102031b160501090609090504030e04 82
    0x2d58a40000c2d00c000c803044501c0c3c800080850001a4100c1141d81c041a601d00700868501e050724140f103c1102076410303008440140002a446104607815260455000241e00c640c03070554808403410390441304295800080d8450b1850741142060f5404c40d0701003068050303004400c055108a0040f00e85c20308001c0c60100d5900c0400030306401070300c262042502c0c100302900401c0d40030402c000c001d070ba400046400402c84d40c9401d04000840640c04042c1100145c50310045039106450503402c03c07900310000e042c01c81c4550f0103690510400d5040325981c4000c201443c00d580024425065000760100100f01c0050f00003a205000c0c000e0390f03240d5400551f05005000c3c51a040c0d105034108603821800241814000b00d054503058418000d20a40540000c2c02c2c03117240810b0002d210341e4041c0a905500c01030100045c02800b00728103507000204540501010035001c82070301041002c41c1c109505102c68904207004c1190720071140803c9804d05d58011034a601d66003000e0b14510710116060f50424200b1600 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 10878874 1250 10877624 10877627
    0x70e0904050c030f030714070e15040b13050a0506010801060512060d1220070303090b030402040605091003030207080c0105032715060f100210020d0e03030103030915050301081921 79
    0x86c3c404540180d5030140001d40308004641c441c01c2601600341300d140c2ca2004074800321548016402c0d148006070000500c0640c540000781c440e03941c0e0203c1840d650700c1e00304111200340781340260f42e01b0075800c0c20607800741d5047c4031010b03200e0300407403d20306842c070145000221150740c0c807103a0080d0590014150f1744c6443e0000350041212900b41e1141c7d00946604007034408140380054070404032a0160f030383c065842d007420845259540043c02c140d03440703511500c0c0815140d40302d5003803a000b2004d125208150f24511314002e4185110b96003c41615003004106444c60798212b030403260300103841c94074114040e078140d4006c441d4121180414005101d00280c50114015281516000f284200d582c1141200742c041001254035481c0c0303201c1e0058110108a14044200c0d0f0003412100f280c0034000308040304034854280c69a04264030980002e21401810401050002c004001002007031410515541c1002d0350203a4680c07007a620801c140c0b000c10035100511095082a2500102841c055092808143c07070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 10880124 1250 10878874 10878877
    0x904110406180e06010c021519030b0f0102010510030206090a090f0906060b03130602090102190606030201080606160f060b041a01020c0103090c3b010e010b03070e0904050c030f03 79
    0x100034514642ca840c042840b2a80d21112841060140d40340e12408181c3d0782848601020114488238410f4180241d90380d0243c026100b0400240d590f8001901c82130050422495902c82045107041da40343c0b0091190002c0d804590805980c2c05891440d6580302e41c502240c0c2c0075074154413184e901850001c080c0000c00703d680108640d103003c0c807000e20070a0b8032081043d240b031009035801c1044c07800420445001440940191007032010500544000500c01c2c4103402d40c202c0c0e00401103039051303903440c0140110741e08407000f582c2151040d141d2904140405800a800300c0070010302900c1c51640000b540100b1101740c0060079005030140003403060310590201d48a401d162041010301600031840c50300555403191103089103240c0c001c2182038a007460120008203418000d8545402490cd40d03400a06000704101071103401081104600095850a40010902c1300d041e001780c607a8220030000d02640f26400b8a869641e204100e400085503195854014680403224540075054018003601c011455070220 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 10881374 1250 10880124 10880147
    0x406090c0506040b09040b01080906070c0201031e060f06030213031b05060403060b090601050a2a0507060504080d090302010801091d0d02070911030f07050a12050a02030601030b040504020108060103020904110406 93
    0x161b05020354000b4800642d1200000c43d5546040d601000004a5203032042903550042801810001400e002c0000c050a40c01c582909420026032130303000800c10031445400a40052042c1c1c0703030031428000805107420a114081c070014004981c40910480d940d1030b0a40788a0081a0003050f41307070b8442c0c2d20302d0440c2c054046018403e204139001303000202a075002d5421207000e49241e079142c0f21040340002080009030401d103800000d01241014090005004008080c040d00c200c0d21560349491900c1600d40c98940d440c49c03008100641110200010307604009028107544444030b010441c0403081241c0c9421420b54500c420741d600c115842d40351002d0300807d6180644002a0003884614115041e01c0d500744030585450802da140ba00c0000c0d0307110b2083e00a001c54298030300e07040c10034202614028090f6130701603a030802d0302a0300005103c010741c3c040c031800c40540742c10345051100d45429000070305200fa008001c24145900015408008d40d22a4445181c0c880407031041d94035070b520b81c08010161805130 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 10882624 1250 10881374 10881379
    0xd051603060e0114060108060d030e040510030506011a03010b0c0f0d050d0c1b0204050903130905060906040905071a041206090605010f0305100b011707020a0c09140406090c0506040b09 81
    0x80040c0002e03024425513a44103c1042c0c45281c001d881d50780900c040e88040c414280c040043d80c14000a0320b540300c0c0a242e005190420602c0032450031810705508118041e030185040d003c100303501c070b55070311106000c1d80d0449664052039a21400c0481032030342004481c0c4907004060041c41c018840e01500f01001e031507a800c1a480411200780b0219040c0d130681000f40e490b0b16940020442da4006244c590401c85c1e100c01780707000b0307241000d96510b406847c50700300d0f1300a20307141504c920802c0200d08090085a41c4440121814020074036182c941c00d0b120032032030240d4003c08194441440d00610030707000721002002c0d44111284190b030b85060203001000360000c202e039031a00349000001d400c0d014015520681c4d41100207030404c4c041050111004100608409050203845008001c1240c00100200d2107401d0f99000392140400500d841060b9964603004000c01d14580b280354100c1c0c0751000b900c5c030703807082c0e0120000450052509000c02420380c2540302e50790122001402107402448000684000c0c64113 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 10883874 1250 10882624 10882631
    0x30e0f060f09031608070317101802030402060a0806030f030a030b0307090b0a120309091a01030506010203031003030c06020403051f1b0804020607020a05041811030c010203090d051603060e01 84
    0x25905070b6a00d0b8410380d1404030200102d025220081040d020003004d10030700ca07003008140c8504040111034800021940208040c6051504000794050031002c1185d85021010452035460698000b0302540a6003840b00c003040084400500b458170204511420140604212510b40d851044000d024200d2080154042d0152607400102c400b418000c1050710b940040c03a1650031030500101c582c000e100008103400b0061018400206811070340304600c01c841d180e003801d03610f019441001405443c0050b21a904544c802c108202e82c03d410305030400103590781440c1c80101c1400174107058010f409260000342c001d000d0300540e4034003042041c55521a6507040711091100e10010442c24807042030144503800403480c0c40000900515000c8014120513200801010700c45844001140491740503610301c07405602603107050414820340203080036920000320000c00a050328600000e44a000d007074200b6001e000341d6820301040010501507100400f881c0040c0007007460345e0341800005400041c3d0303030100e607500c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 10885124 1250 10883874 10883881
    0xf090c0e01050a0e0901020d0911030d110c10050c0d0306060f08070e0105160605010305010b0a08010209060403020f1c0b010312050306010816050c06010e06040510120605040201030e0f060f 83
    0x440d608958101c0d90010f00031041e0a241c035076001310483d0028590b04032550708000e0031105d20b0044c450780c00c3c1ca90184207207024005659003498907040e0266003030300902c003081002040b81100020960078080040e01d03040c0c1c10b2450140d090b9928064207001c00796a01078011028840381d8140d02040c00c480041e518a480494464800d4800040c19070340040002d0b0f00300c100c00e0807540190003c200da01039400c200002d10080d501d82c034040301d000380c004482c0d59464200c104803d24002261101802c02c2000862401030307103000040d0700380710700d02c80240210041300d001801c2c0c4c1c0d40d1080111505442d01d038620042009441e1074407043c0002d01040310030180a01c4204166445281030303030710845068407200c1441d01c814540019184800032854100722040240f84810002804003900074080c0f07034000031080c01c2c40020001920310007044004171903e46441041312003050003100c400c407504100c001071661510b00040340031b06001c2200500c0c41c4113008072071904241c00510079102e80c0358980002c40307946 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 10886374 1250 10885124 10885139
    0xa0b03060615070b04020f04150602070512060115050f0a08071b030f0809010e0f0a020a081603030c02061207080405010b100f03050903090a0f03060506010504030b190f0f090c 77
    0x424042e80900c10900303000c6076000420441c02c043c1c0150009089880021000740042d090f04c0c000510502e03500c8500c107041080380d80403c002c402500003280e500b62132800202881e40e890300148101c001350003091500c001c0349805030741107450300c2c582010840d5480441c038801a0048909403400d00010b0a03440b50b00103100350f0328501800c8980d15648500f622413240c441202c1c0c0030b030050b100e5030042d585c50b400c2c05001c1d4010851480c8040468029082c2d120090040016903070745640960408d8000000c00781d182c8003032141701400d580e418104142803103428004580703240a07480382c0004500001080c050075035041061b06100f01c1c8510000c4c004456a04240405d01c41c0c81c6800700c010500814040c181c2c0c0303003c0d41209a101054008883c1444e2105c00081c0d00e0070006d82c81246c60003186442807003408010b015255125100307003484c1d4600f910310b6465014916008007078086e1440307408204a21000e8641010f424001c0502c401d010280e07104035150000c3c55905000c40e41e40f48400c00c00035051 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 10887624 1250 10886374 10886389
    0xa0b04060e010306030206070602070212010203130b0109050702030906180402030c030f06030c01050d0c0c021005030601020f0102040e04031d0306010f08070603060b0d020702180103050105070e01030203190b0a0308030a0b030606 100
    0x45e079018149900b051125944d941c0650881a01207030302607560325858410560910240d4800c0d60031200541040d04c960420b403040b83c01c1a0030480310740342020104000c2640010441e000d64409442c05540c580404150900c05c480402506511600020900c5103441103400694055094241c400071140c480004041da6070020343c01d8540841d4081c09560401d41e500d511040e081c10303036410101c1e140300709640001c1c0700c0c21703140e04405c0118801006000103944d0400c001741140d9460402189042c0c00c0107030780108260010001000c0003c0801600f900d01c40002c503a40380c400f40030b0222989541c49a030584240b403154008d500709403080140001d036a40c4640566000c489401031100e240940c21800b0301c0c040e51000c1c20990f04032403040d00304242d80c2a100ca00e0380c000d500036070002a003420044001400c0040c00701178241054010b105000240c8910050141c3d00214100009201c042c00b1001c525000940d600144c502c40c4007000b0000000655040351240010440a98055076115800c11508 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 10888874 1250 10887624 10887629
    0xc0815030601050603070306080304030602030403020d0804050a0f02060c010c09150f0c0f0512070b09010c08010e0601080403032c060a020301030f0807060f090312060807060f05030c07020a0b04060e010306 90
    0x1035118200401044c20a0b200039900071000d40f8000c6589500c503010f0038a10390066000319681d83d80041000180b40d4140700c40d00c0c0e0b44020b46400d8590742410b4407996500c00f00400054607500e0041d1180c0c0443d0b0b2074000700caa04914820090146901410024045000c98402c82c070741c01c00303403000f42d01180d8422164281100ba4a481b00c01d00400d8945504115452002c4116010701c00c0220006401c040740e0090480c0900c40e450b100004c2c5070003111300e03003942c542032084018410b410b0010704c1850f5000030090761248081c0307000480c036942d0b0706040f40030748880d0009090072114102401c80b41c2e00864400e052a84191081707850380d40321254200c040b84000d110140c8061050904000001d00240041900d14091a004070381d8105101c0380c41e040f0b070340505c2c00f10017007111400d0442080d003050190708020300d081d03030241412a19058001e0320070740211012004110b80000011508680b1100755115241c02a1110358442c3e190002000a98464001c50000ca00142c000c044958481d0281d4001d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 10890124 1250 10888874 10888879
    0xa08030f04090b030c06040312030e06010302060d3812030c0a030c0501020c030409060306050f04020919090807080307020f01090807020d03020307060e1b010309020f12031c0c0815 79
    0xd0a890140250000c0200c04107880d41170280c0400d0900751740d0340c0c42c0500040c5016000c0300c0750002e041d01016085502e2403800035180c1c5c101e800104056512902620500c2c0c5881c4004a000c640d03400c0c0300300282842020040411b400c0c00340030800e10390f036008143c0c0c0045082e079090295a05501e82a40d40e40108550f0344415803100300102c0000c0c0c4036240b01c3c1d08092003400098203040d030b0004024110b40140c0c1080400660300c8000b0014800d40b8015660040b580c2104800207003056000708402c0b03040100b4401d114010601d01c402503101544c8400d43d89a04425090344420f554588191182d0064600500610072451400880700701031081070103042e40720401926000300c9500340300e59015501d0301a0150700040c020407011882d10b00440f0034030280303070010f000e42034500c4080d10080c0c2d40019145040500c1c3c0b403034850041c0c4a440c0e0007001444105d51030005040b03030729611441c5204500c0c003401d0b120a01000844400a10703000012044000d2300c0300005030b5103101b403542c05452240917003507 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 10891374 1250 10890124 10890127
    0x40501050a15020f010507020a060c0503040f0305180603010b091906050d09150e0f010f09020a090906021e07050d0c0807060c090f0803070c0902030c0406080606090901090b0a08030f 80
    0x1c1d00450580250300503d0041d2040c0140030301e04c4908494045900f000982c020040101c1002501e12900c9245081d5091460950820b40c80b498642488514000c042c05030003d81e141001210582620800000421859482d078680407011495000b0320b9041e4082c0a980180c1c245c029240340c11075046d43c03015075426040c12003a40481000e4085880e0030384100912109501e4408135600030040f010003c0d900404a51080b4862182142d880f17481207407401d40340441c41c00050b61071900180c00c6402c083d5021030031040c40e040020007072080c2109005080381007102d000011178550054024180203900395082041d0401c0240e0b5106200740d0f00815841c01003100000260f403907849091030998515045440303585030f10015080c100c5503005000b0395880813032900200300300c01c0365010141c02031a006500718208821540820b00030b034010503080c000342400048198070b40505545078080c000740681c41659540289500409107141c01d64000c3c04000008a100600081119003074041c110320715 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 10892624 1250 10891374 10891379
    0x7080a150b1005091e010c080c010609090b0108060601080103030c1b1505070b0105150702060c010b0a0e01050306070206070905010c11030304031202071d010311010c02040c02010218040501050a 85
    0x403030105481215403009a95030740100e00940b10025035092201042d1101070b40c5031151410441103040b1403c95100f8490b1000054405076400000d440c101540013007016100c504ea50222400342c0603580180005d00d140c00d110000b0710401d805518122401c40c1d0644519445d420700444040500340806404034a5450a900003e90880f0461043c468880c408040040d102c003401005001045811000039401003100d01c18040e4400b0303c203004103412540126039010200b2012124000e40324045d00c29180820011400d00082d04502e1700c1240041c0001c0c0c09503210344010860440070700416002e4819180001c4c0e006000007000380c080c400603110b0030209483e02d40111744803048000220f4807951140e00e03d918585003080900061442280b00d0310b81d40c0269400245046850303408541049500b0441c1b41501041c0584181966000a40301410701ca01c500103903081007980700029002442e0030180341690750b065010f0040301c035640d201061410002810002541c1083c02040e40c409800f9504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 10893874 1250 10892624 10892633
    0x2030301030305031e0106020c010e01020a0b04030c0507091e0b030d140306030309040e0601031e0b0103031b02060705010519020702130506010318030806030c060c031603050903070303030f050907080a 88
    0x3565005c002030809208003a43d0b001d40c1201c81c0c10a92000000d81d00640f1001070968000ca140c0180c68000e20090822040c07070b40320107100040c040c10180500060802d2207050000070310240d0054800d004050044550138040034000000106001106600d8402d810180e1f14002c0b91204840081d59580341c035044504051038020352020303101c20f602d03200030880d003085521070740145926000320740c0181c40c0c90b61550a00700d04121205000f8441001c40c0145d40c4001110340c03c8090640303805d0300e4031410120003151852064403041c0d2000c0d5202c40041801c0f000c003e41504010301c07441c0f1103040c00c0111500b010660080c1d015840000354030a0040c031a0b0080c1c45000d81c0710a500540514011810028594030103082300c0880034281c0c00103540a0030808136040400003001d84203000d44045240c01c010f00c4000b030b140d0050211070a000500340440c0c60502d44540709483d06c54030300400703407500c040d9649009001400022081c480441c10131000841d085004110030040b01c504402801d072640749a0356 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 10895124 1250 10893874 10893877
    0x60d060b0609040603081b01020406021002030703090b01080a030e060c03090105030907031a07031a0603060409050709060611070b1201120f20040b0a081f020d1109120c0102030301030305 82
    0x304150040300500ca40d80c82d5079104c1c0500e40065025042c410341d5203030318807150343c00350010341108170040e07004010410403554005988240e44080010050300c82d180c0c81d8044010786812200a001902c0d0140003194011022075000c01c0b030740c880c0d00c451a0100424003442a28000e00c0c42507507007a0018019101554020701c01542d1010100e426180c3c003644940c1da0400c0002101c00ca00d240400200411507800d03018800c11000b40c150020780c03400d4801020014140b8800101031030302550326141d182d02040700810240c006480c4400b070602415448042c0102040c4039103040500e00d10410304001580c09038202255000414503200c0040340e0700b0929150780f482c541c944112041c0c5210411030700072031205403400c00751124016001d410050103400b0402030724106d100152050010110070070401c02e00240e490460304182003100910000c43e01010002d000303840e50030a04e107041c40c14400e0b01000f0700c001020f034141d040350882161540030700c240d41d40d5018250910b015a10802c01840401e00600 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 10896374 1250 10895124 10895141
    0xd030519021b010e03070201180e01032904050606010219050303010e09030403060c02010204060f030b1011160e09070e0106020d0c0c031a01090e0c0d020d1a04030c02030105010608060d06 82
    0x42c40156031140c106660350131200c150156012940011681408542e44000c45003030244540301c030102074034241101580d01d03075810320008201c21490396290550303400f00710540c07100402a003566081490035051a54548500300e0703007180140640190004070300305103642d440c00160080c005600b5a820000c007002c881c3d070043c0180c995440103000010026000340654029501241d001684840c0740c0040a002080321000c0d00b0705050030214901480d89880746d00300500c92032131901d40c0c0c603541051380d03403400c000303e0040030f05511018440214045201100080c0100c5c000021203240b250f544410280d1004203004030300050b0020b5803980320303552184403400307541c500441e000703040315940b40e445010720892084c48021042c1e40400402502d00144500d94103110803501400f5805001c90029030b8000c0490b41c02446092002e2a10090244468004a44945907002e81140341807509002c0d05c0070208200c128429801c010002c0350040c85151000d020705005440000450326980e6650003418800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 10897624 1250 10896374 10896397
    0x4080a020a05120403060615120504020a2606060102060405060106080c040f0303080f0105030708070303030f0f0203090a05010b060403110d0302010f0606090911040302010e01050f0c0106090b01020d03051902 91
    0x4072040440d1003400800740300040c8000856079546503241603025074906a01008450604c001042c000a0304680c180440010643c00042c8a84e52840001c40c400d085030480c80d40201402d40030b07065016505940d44d6011164000c0314611741c0c40000490b83c1302030803903000300b203a0855401041124080c484031a00f000c0010708a900301504c800e100c80740729105510540014460780184103070b440b46040010301500d401d50140201508222881e40d1745d101611004080680e10210300b01003c940e0750044011a000311015550303400c02200c025075820b01064251429442c1c40e0026000d407030300c803048a0032241d2020300b214141c0e5044081004c0000030142c1901907540303545035068406058401e80010704059280c00c24614108104e480132079640c1c0300c10045000742003009001503030300a542c03001844002d180c00c03540e0f043c02242e1082c1e20f000c1c0320396400c425824140e01150b0f08046030051140c9100a90884441c440000d904400342d0310241c0388a4010b4840c245801c80450b92030b00242484401c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 10898874 1250 10897624 10897633
    0x2090a06030602120f130209010b16050d0302030702100911010804060209040504030207080706170604090503040b0d06030213020901080414010b120601030314030903030604230a0603050607050705030304080a02 92
    0x480d2078150582c0d10207251130200764450020081c1c580c221051311a0000c3c84044258008207070303540403500712441801810076400c000318003005000c18410306040c405070b02c80160707200d581c01c42c20f015010350000d4803c0e80244c09210502c4844030170501c03a94050303580101440480c84444001541c2d407002c080d00540d0f1458080041c0c101320345450185500891180c0e005100c0309103070100183c14140c0c0d40c0c10460403c004084004420420181c0d020780102084a0000d440801c03842c10360302d1481558486030094102082002c0645603a9011908480c000d41394000000c4030300c10b07a07404921038521041c0c04200c082c0e010030f02090013200e440144034500740000030741d0566035000510442d0181000c804c11340c420360043c001c0580c810b40c500003020084402d18110b040040040e51030b070000401c22030260b940d8080c0804207030071819403007140c540150b4000000d4145034005101600d0b50b030105131070504c40d40d40480c4040b4400c070116100030703030000c010b1070460300e0380e903600a0385511500005045129 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 10900124 1250 10898874 10898879
    0x6080f071e05160b07020607030903090509060105041502010501140f0904030804060f020409020912030a1d060d0c02060402010e030c06070807020a0806070c06060905060a06080703060e01061701090b060702090a06 93
    0x203009070010000b40500544101840c085c80020702c0c10400600082c205070a10108100103a0480b001d803044d0340d0110741190090784d507400102c40d507000d164080400000503030006c603902501903204e241030741d00656004e0036224a01c81404910fa100703088070794101c00602c0008020030b204034a410f401c2446034002207031101002540e04166003240c2c00031640b256000520010900c5c00c04a111f4140c5810400345d4201300344190060411840580d01c944100084e840094855135031200301c69402213550010402c00c140880025601e00007210100e01041002c120700040b850001003606071054020825450070101d55140400758005800c100c2e08080788040200b00000144800d83c0710303640a9603000340c0c0318201c0c20802c0c1034036042d5000e07007100c5140c00240025526200c91070400d94202d410400c4858803070940440007461280d0040c0880702070b040010800751b5000358900048508411481e0641e40c803100c0f00c00441e1044001d03581c0c81072080040e8001410414412640003080d540b000a1055 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 10901374 1250 10900124 10900147
    0x30f100306020a03060602060a050c09010c030c0501020307031d07150e120d0c030815010e0103020a050c0604080406021e07120302030d050a05040606210201030b21060106080f071e05 80
    0x80040075101d004c071342c45200900140d5810000316030701c8080b0701c10034481c6041c1040c4ca1442032045044260410801021034018140603900c082d8038a94044005c554074501241c0c01002484400400321250852016540b8201d800203030010a950452034403031450540c81105031014503400130050b03008035030303100b00403000002400010358013485038a0342042c0b82e102e8a8001e004110040c46092030701c0d66680c0c254040c0c0da010808652564080c200141d5032482c0c9401640d4a0003156102c414038440e001c2000304100313451000e4000c0301c0c099001c80f0500603080010403910340c80e0040310141944528010441e142c0140d0328802d030140603005992801c51154403030703025690101c815800e001d072039505100c2005803522440d0020002e8600c407000c880c8911100b80e81146100d14007078100358803a141000d4540c3c5501800c0b80010341c2104480702031040c06000c80e10743d1001d220303004c00f10f0020030004042c90356a510061040ca010b41d14121401108016515415005100002000414400301d500403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 10902624 1250 10901374 10901377
    0x120703050709080106090c0f090b03060108041104020c0c0306181213080303010915060306060f0c050c040207050604021804020603070302030a0204050604180b190302060702040209040c0801032006030f10030602 92
    0x601d496400460b8054400d60081d10100481507488c04001c4614000c00c2004105425250440824608030701c1c82d03203d6041c40e4400302d1032507011590083c4001801c0389400b4001880c0702d000c4000340c0960301c01355101020f100d8075840c0380c402d150130f50b00080304448566483c100100b141c0b40c030169814641d03030b80f2006e040f071558009801c94403c0959600c08400001801038000f001006580380c24060301c0c0c2842001003800c1c00514082d010f01c069001d0765410410700f031100300c10805010300110740381d01450810304d0341c880c000d540a9004040422542d91800d0042c80f2040c4216000340c909442c54a50040c110300035800104061603c43d403c1c0000300d8140d5980c0000e0005141040b0910007200c0740e1002081250700b1140038920402c0042a666540c10384401d00c1801c590301121080e031540c40d03900114000e44038019405074024500380c000c03031400380c0008980b4103890180780751001c2c40c074100c01c05001640711607010540c003000620015208204503201d0981c00210760092a071815626907c2005a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 10903874 1250 10902624 10902629
    0x70e0612010c020f0601050306010612090201030b060a120605030106030506160e0406030803010302120c0f010507020609060a030203010f08030c0307060209010c050f071e03020607060c0203070f06020706050c120703050709080106 100
    0x50304502590704c0003602c2040564050a001c80c09030682d1352620a02030031008150340c0b400c0d8996200c5920070203581c000e502420381c089018043d41e0b6038071240440140541d07492186410503a1500710040f5650405120303003000d42e41e0190013480c1c4c507112101061107605121040c07504204e04105200c040d40c6443c00303404c000b1449001344e40d8a80d4194410000400d1401124442541c40303c0d0304001540d682048400c8422400c0c2425a5036403500c0c000f01b0010301ca030085181c3c01840003d0101e21140d8968011812103030314400e00c0c54103544807900c0544a1090070f40c640c01a6100380403d4003c00e80e981e006003200e41e8141021181d008081d5602c4d406c0c10b1303124080d00d5454000d07600400485c1520780c12040c4174101410040c0100f410350380000c2da1070084c450040e20140d0740d02e00300d2450b1030003042182c00b4a604440c507102d0002076071034800069800f400e81119003a041c2004218610120015184010a40100b0044a90300c01e81c044000b80b170000d04800800205031000501440c0c01e110b035501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 10905124 1250 10903874 10903877
    0x622080c03120c030402030a030e04020d0516031103010b03060405060a08011d01060f0501050f070302010605030703050705040609050c12060301061a040f0e040305180a0902040b03040c17070e0612010c 88
    0x21a103020404224500d14002c00f401d007184020020080103940204249028a505082c00f080d0540d80d100418001e018050040c0b8a051601d82407107442c104160502801104a175010300c003000700a120460035020a204064040f241840800c985240c07030781054bd401032029240035125541c9490303050070b40340202d54446500310403821020140320203009640c0239060030348000002030701d44000207002d8800e0060f8020032000200320201054401c1d000900103003001000c5a200350b0310f03414080d40f038030440c4c86564412850910300044024885c0607031840b45028a0a003800c0480202c4132001c52000244019415503a40102141c446042c050589180c28040d011585030703410705680c0d0040480a401503183d21a0785000c1100081c1c1c050100c40925450540c005261142a40407462265241c1c0050400c10f0001c50042900e5428034003661249010312400a0850359482d00130045901c2c48032034041d9178104000910041c84500c18482d00306c00d004e07022803080c901010102d42100c408020b84030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 10906374 1250 10905124 10905127
    0x5040305090603010b2d0d02070203010906060b1c05010b07020d1406010b070605010902091516020a170c0409020a06050708040506040806040b01060806030a11030c0d110a12050622080c03 82
    0x102e020202c06c40a034900c50403100481c418960130000e1506a0194044a1103080c0d00010448115242900440c8040e54081c0041c4405502d0343c1c194071503904684038201080c1c07154841001c0c40644d60084034103d500301010b180c80d095541d001d1042442258205440c0c140c8400b505084103402003008500808012107559103036480c0c0d141c00c1c010f940040e8070180d449801170005060741e9880754103030001000a0f401042d03440305030140a00d40c0c04158003001c0d501591810001403401244940403208007600350564040c010f1080800044a285560103034100e24288003e00070103000384c00074044c560041440d90b003065520000101c040d80150840c000704c6d000b0401f80300412000c038007000d02426a07030a182c050f0f443c007140800d607a00807920f8003611698016000d02500d0b04d050007503641d00c000c041c2c40f181492100341041e003141a003100040c1d000d61900ea600082548500c428003a105030f0060241030180c0b0768284208407604454401403d07040c40f00703100c2c000115103000402c0720801b44000785 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 10907624 1250 10906374 10906387
    0xc05101e030c02150105130207050a0b0115080906070c0201120e100903030b0102121602010507060c020105160509030601230a15080105040207260d1d0708070b03070305040305090603010b 82
    0x84c200203069030403000d0025810010720180e641c0c0c004001460313105c0c803001a2140c0d02801c1440c540800c0010103030000f41c0e88000440c061031108501d111394441341d1108042034898005003a0b8452007107400704000f502d440303006401584180c8071100b650501c08804202c41b903010018034104117507003600c60400d640d2403410604054260007400d0240100740040c00c0c06170034000100c5d4003403252081c0c0080304d90154400305e0440e80540309840794150060020080000155406402050140c030111810789510840e211001d1040d401c0340c5902901401402c00c07039180c41e40824440d04204080e0a01083c40c4ca46000e454603180030040c000c103101e4403140c109842c041c0f0003418981c41a00038a00490041109001082c00b8280c40c5003403c0b4114000225884800c4450526002c2e0500a149039820100700c2c08401411213151403511103600c051b00c06990780c03601d009940d1240c0d486400d1042c5000c1c000204c015009900070b03903216000f804d00510f081d445400203400341d8001d0b00302800040c0c005c01c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 10908874 1250 10907624 10907627
    0x40b0609120a020907030608070306020913050c1201050a06020a0308151504030311010b1e01020c060d0605010311120f0403090305150106020c030109030909020f0c0d090e0f01030c05101e030c 84
    0x1c0c4d07030006640d040030058907041c1007000f5260300441c00040d003840d400013402d2a0300e403100d501500c28003407400c004001c00d00b043c1043e07100685c044c41030380040c1041c40d80045854580f41a8000c00c8401c95001003968a885544c180c0327500704002c00518003083d980c5c015054945408000039034034441201003940c1c860035441d01624400c02d443c2d5001c150f80c500450319000d5102c1c81200200402c407a540f40180000c1100102d04d00350403d0202c64004a001c1000d6083c610703240c10010690b5001d80341404040d0b04680e0518880c0586020501c01601043c0413a4a143c42c555074240c105000f86401110709072640c035668908490f003d94015090300640c010440254140800c40321f00c0002c030001d0100300a65140200100b4070350140c00314241d400142d07120203600101c00c66406480550980e4101c0151b40005850000e0a2042c1241c1c64a2940005c4103000c01e4185141601da00140101505040000f40005c0e82912010300d8144542203580f42c0342c5400e04403503009200c0c180e1740c0216840260640 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 10910124 1250 10908874 10908889
    0x206010602070308030a0f020903010c0207050f06090d0609030516030503070f0c0f08030a0902040f02070204050f04050604081806180a0f0305030319060b040f0509060a06020c040b0609120a02 84
    0x1104640100c2d40520002e6002d004594101540081c0803c11401c0745c0b2640c0028416074068640c0b5601e05000840303400d40100d160f0003191411034540c1d1603a01808244071702d0344600514a0741c801011100840090b945903c6096590700038a412802d24424000c4400300c0d00c1d0703034241a00425800320821068550008440c10200f4007860008544000c0d903030b907488d00d6a40c18000034103800000c40040d0903600c491348280c804980041041c03104400885204001358000a800d90295040070002850582e103168814021176000300203050703690340d45e295059590043c40c0c00040300c0701b01e400c10702126034034400607040781a000d0182940003442007040203000407641d804088203080d00c6034104041a0003006580d84000b0003119400150aa50600401003000e034100d400c2d0803102040102e2802c40c110550810355009039a18085505e400c0108580500b5501c02c000041c0d10040e11500d107800c094100700744040000c1c05807401c00140d100013554040d51078001118950002c89600e095107040380303 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 10911374 1250 10910124 10910129
    0x31005040506010b04120201230708030906060d020a060e0d080c01020d060812070204050c040306020c0708010501060201110d0207020a0f080d030f0902090601140403150902100306050105041413020c030901020601 93
    0x180280d1402d81b40c5000d04182c5141d6460181c18403184441980700462541000120321400c0721450742d9507060b500d8503452603002591140c94a11840000030b22504040d240c0c0018030f43c0050082120a140a6088500c00744a550207074100c01818201000501c05001600c15142410000350310360021285840482e62140e01c074819039800b101120621074040b0089940d00ba0301501d0201c0e05955011000541d4410f580c0b0051910348000740c10912031101151410589211000038800c990344c81c0000c034280c0744021003015000ca4100104041480d46500502045202038000b00605566940720044103905038002100d541014103c00d00c0d82e80e00d4403620b01e0b12005d510082104418907000b21b0490800188424140f1607503084052000230583d044d1002554408000d007920488541c956000d001038440480c01100c4070319003001864024002c0078140c1e001a074907d0b0500307292095202000c0b248812070782d00701c60b4000c0107005160440c001095260440802980d540c10307030310002441d240c03059 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 10912624 1250 10911374 10911389
    0x6190b01020d0e06070519060b010f0203040510111c0302030702010f090807023007031101030212060913020a08010209090c0408060a110405030a1a0115050f130503100504050601 78
    0x681c071502c0760780c0107924034908520640d50580c40b4107291070a2454203540070982d840180294a03c0c204100a94000c0c11a10340e0a0744d803e0107091680c11300f640c1c0d9014900503e64404810160034000c18072506075002c000b0004000c0310f8004200c242002c030081100c0ca0803000003500041000b8400d80c090180f170748003075030881d41089100840d46942c00380d401602030091107900441102e56001440c1170804c0b0302443c01c80810301c00c000b525485079517189640d10041f0b440071050486c0552030360091094541000b160620a056035071a201080004403005101c81000200c013607080e400760701c40c0c50030b90019041000006a403241c043c002c01100b05030040c540c0c801400200f0051045034008244550840040130000c00c000c808141103c119000d203405c0316805110b41c0d0315581c24854006440c2d030000002c0100b40729640d0300d44100391900300080c4000004104d0402c000c0d950070758900028142c80c1408000070f22321503280c2c40000d0801030310301c07489080c0a49580621042c001709201403030040010 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 10913874 1250 10912624 10912633
    0x501050a050910030204031e030e0103050408070b07120c020102031906120303090804030b0c0306040c02070807030b090a05010606050d0b09131e02030706030c030b093606190b0102 79
    0x800c0303009020384180c54070603014140f648240e6200034001e406407006150f00101056a041c060646c0b400c2d14038030704106400007801102e407206654000d109050107660800b045524089541c0c4030041d246030084e084004100c40811202d0000074584200040c0804960005d6a00d081101d4000c4042403000405640c161420004222002060340d03018500e41c0e150030049400340050401001c180503a0b800502028154401c0080e084039075001544520400c0303c003000480234240c03040369039100078010b072074242c3c2c4110018808580e08d28111580007903240e0031200c184800ea5920b50948026a22030408114049070041400c9214020b40c500b100099801107810320303200c810b243d03614680c0c9402500300422744110041c00c601080f8103c071941e4000c0c0855440d6596024010010a2108100c2001900c0d20f84881c404e450705924003806102c03820720149000803c0b60b2030001c030044e60700d41180030382000521030f030003170703906001c1c80e03109007121400c0780341d404d8a0405050a4616a41ca130300d045400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 10915124 1250 10913874 10913887
    0x9050109050303032a0904060902040603050f010302060412020402090a030506040b07050703020c040f0e070b0310080102070c0b0c030d09030207051320090a031e050c030307050d0804290a06050105 86
    0x1c80c2c405001d00c02d10545e02c0c0d2100b4440b802444002c1d0300c01c2544240d0032038189100441ea440d0260003c10484086590420043e41d03a40d500c640841028000254001c00c10002007000f056400f03850340140780014070040c0303804440c50004100750825441101c0640010041005100c0041c0d030095001c0f0103810018505040c0795002515010000345070341c4140c3e80e030303960602008540d6014941520805040307649550300d68202e203030303036801c00c44145861016030400842c3e40030303041c025504516484035981c00c109082011a014903000151490703030503c0180316036400007510f4080c4181e0b0600a8020301000e40c1400188000e480c50282c0b629805420020a0406c014025812895080a40d04056251100a000103c11816681c00a00184c103072038200301604505045032201c06105000312641c031066002410303220302455001038901d4000c986c80c0c801d0380c0d0050101c142c0c803170300c240728000d4840c0d081021803072581445480c080c589244002041140310542c801c12015007000d00700f440c28038a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 10916374 1250 10915124 10915141
    0x109050102062203141b01060b040303080606091804080306010f0302070b1602010f020c0601090e060609042607122d0c05030f0703050c060a0212010909140d0905010905030303 77
    0x20b006440c1c0c00320349803482480f10915100b48182e0f0f0001c01d00d068100c0da140c80c0401d0340750350700d00c01e03800b0074030f065180540004240d2201001c4078102e07580340d10b510429a0710304080200c1a00035186d940e40060361030843d40b660300840c0070341a00c914400d80c00d883d00d82c01c0c04000148803030086401c8809161040115401265842d816030b513006112840b170700b03540d80300b24070304a0240008030544036107903001144000308901c01080041c1030720180241000080c000f61000d40d0b4030728040da850f5401110702d030081004500703084203d0401800740501d000c0501c0e80c1081e403110703540c00044141d9188801c51003414219070301c00020019096003c105c0ea00d414400700d40b0701e002d81108141002400016240742c000c0020500130340b1040d0707240d00300c00d503101d10303803420040c3c0710350310503100100c080c0a80400600880e0861007a902503034079040502903543e08200400d40207060b0340c00d00360392072070300000019a401401c224a502d20302050b03440c201d01c10300c0c0000242c40c880c4d00d0342241d44260000c1c400c126010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 10917624 1250 10916374 10916401
    0x7050c0f09060607060f06060c0209060301140705031f0b04030b1e010b0901030b090708040b0a020a0909021605060106030b03010e06060907050304140304060c0b070503040f06050c0f03010311010905010206 90
    0x10112072203135540c6058036120000302600e000418180307080c14800142242c000360180034040c003c3c1c8000c003a6a036020101130884095401c000c8042d00070314040b0b002a44581c02569201040c60b1071000440c0038810941d41c40b68290740100620600020203000704403440c01c2064108400c0c0110202049100807030b8594100d050003909501394002c50303002c0700ba130300c60340104c6100b503c003804500c041e0410003001056020704440650703031040f010340898400c1044d8400c58894000310741c0e03030b06039240c10215602c029502140e060b88205000556003004641e0600107a030003441c4584001500280300d40c00c2c14252148120481d0743c40d000745003040b18603151030380741550224803450902d940740c0e118035204074100c000c1017942e081c912003c54007084c0d060b00000103003d02d900407070784d0111640d41c1601c00c6400d880201d0300103021000c90b890b01d03000503155400940c1c10001d90041c442c101541c680400c581c0b03800c00d0f48142c0e00398500c0b0b000360980d941c000075810040c10003031020300350516104d42c1c00310b0300 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 10918874 1250 10917624 10917631
    0x20d0206010311011809050106020f0f060c0a031407080403020f03041406070c080604060504020108100302101d0d060605040509060c0724020c0d030501050105040f06031104050307080307050c0f09 86
    0x400c1104540002d032a1712501d443c2040aa50b01d03680e0485548030056100200400d018030300240c0329407d81134040354400a00000f005140e507000700130503a034000d1620b80d540c0190124805041c2c9800d81d1490098540754424422040c41d500c911440c5418203009241900b0720310a0b0071560010001401081c95000361440601c0c0203452440d0780c0d9040385004401c01ea000d0740400003d0046506100400c800380d00924000ca0003640e48282e2501c42e030043c0395500e01c40740710003503222036441010342e1380e1809010b03211440083c031564852940300e02c00103d107800b6250380049a14079a82e03070301808107180a209088d00031340a50010042e51801c10f15000c254819450301601150203040b0580e012030380d02d8007040b1fa0007810783d0155201c140340100705a44007201601c50000c40e05010001c40d00d544201305071030440c0e52030707444c1d0550180b030200240d00a084002c0103c00103402007001240989040110100504009004607a25903482c14028202188602014490b007901800c050320783d5150500300780c2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 10920124 1250 10918874 10918883
    0x9050118090804080106030b070905030303060a120c050a06020c0301050109060e130606030213050105040f29190608040506090d0509010e0609090a020a020c04051306110c0102030a0c0f020d02060103 87
    0x40c0e01d0114142241e203805980e005200384c0d0b00f08400441009485009140103501c41d450f0040180c1c0c4a104054885c042110116000250b81c40100000702c00b050038100342e01d0240c90505207064030b0743c011603000401a00220b005d6407007254046400d0400341314203401401c080780208011170500c00c80c0050030901512042c1038500501185040c081c50b40d02907802540d00410303a0384900c14001c10742c80075007000d2282c94442c80c540303030403d1405100d43c040c120410a65504c942e41141000b401400810310b0010007903004001402da0300c095082d01d000b1174000c0c21160302d1b081e215280034646241741810040040c4000d82007a540ba0480c184c00500340c4014003005d007401c0d01780481900100c4c00b1400b0740042c10b644401460103000058509900900b040f400990036a40d41082460030701c0240c9500742c406510305510700466078040b924a03800000341e010002c018a282800581f110341c00e90b0015115981490303a2101110030a680040c0e0b01d580114507400a40300c62518620301035141c010502c405030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 10921374 1250 10920124 10920131
    0x1060806040f03021507020109030f02030a14030c0d090809030601081903140c0607090302030c03010c050f0901031d010e010b0a080307030806040b0312030a20030403050a03091a0402030709050118 86
    0xb41014000c3c452844200e050b13010810107441c21101c000e000e020321090a50110300c29002e80c80080784007004070b071a40c40f8152203035894655402c503034861a9200070101004c2180620208030516900c0c01050755050003000c1441e15070f4041c00c101070410b03006074040351260344803001052401021800e1805200c0e0141811002c01106001e2491507200d140420745c4603028440422080ca6004900c50040c1d03402541200d064111200505088a282e02c4041002c190140401c2020b940c0704001019865418500845d04d0359006001040480e132481caa0203459448154403840108244104508a501101c00f4902d0918100405841c0e1040000140c104114080010b65544454001c40820302e00130f400c0312045480e80c8980e802039003040d20141259400c00703080c141100c0b0a401040c001c800380340c4125107591560358040d5100e62002101c80103050b2a400310300041081225030029104000da642046460984101820407525405c00580b55113803100602240320740c0c1304082000301d060381000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 10922624 1250 10921374 10921403
    0x607030b03010207060501030305070506090102040f14030a02030610180b010f0302031b042306030105010509010f0e040f02030406050f0f070f020c03030406090816140907120609020414030106080604 87
    0x7034003902c00c114000c4e1146051800000405038010b0003483d0b41e60140003660075a0300d40392409800c0c0d03c114442c2c603a15051110050000c00c5001e80b01c000034800080803261040b9081e030110382400011219150300301d4182c00100110569600e80d0300c894581810b00300003482c88500041c0142043c4282002019030100c00200000c050300741560b060801c0c901595211542c5201582a885130341e001c03e40c018074000c60007049400c0120590b4141c60058403642d09100e24003004442c503140d1220b40724100b00c540301d56200c003500c8a102c0c0a4182402800150f683e1a2a0500c0c9042d02d5000d018100303c40030315003c01524031040031603150454680e1a10503550030340d1460407031030114080780850341408000350020304e2642141c0c105048640c0d0b8426140740800122140342c000803580310300405005030b051203144500d00b038906181c1c04800c42c204840c02d0180001200308581558002c0d07200e50787c0c0002d0510039444004e4842a070054100e000740117050810b03180300c0c0c4442000d00018421000d41c6502c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 10923874 1250 10922624 10922629
    0x102120705072303071401090905040c1e0e0106030c0306080607080c0f0705010212010503060c0403080a0f0912050d0905040207020a051c1203050403090906080d12020c01020711040b03030405030607030b 89
    0xf4141508070050450b0302050f101d400d00c40e0000004034144d40414440c12000030812070b24020030b40f00d15000300d43c00c0200351600c24280c0c22298441c6480204650300003000c640344c48c1082409010341941e59001030313404200c00c0b000c1c0031180d0603040308007580c1c843e404019500b54000c0d902607116101141e21078860000d401c900701c3e00d01407090010201c2d40080b800c01c001d501114000f9040700c10407002c4400e035444982030350303103148100d01000d0450002003001001e020f0040d101c0d00e840f18441e1400304801d03907032014850201c0c4800c2030701b19056000200d1703001540703502004130005003200f200d08528081d40c50380080c413507400f43d10801c0d005200003e500200710805081080b0720b2600004081c400c002c170844010002c0c10100c03000c40c0442d07041c0e2400305202c280c511810050f43c000303000500c06940d42e0303041a1604e038000c2d00c040405030340030811000d40850078000b0302000c912440c060f00540950300c1c104001d540b90440ca00c0c3c0264010705c000c014550f400581185c00c100c050074000380a2500c0704c003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 10925124 1250 10923874 10923929
    0x12190c0c090906091a0c0f0306010207030b010303020607020d030507020a0609050a0602030906040b0c0a09091e0204060203041403010e07050108041e0c03020f04051b09030109060e0c010212070507 86
    0x4182070841c604071201080c0b02050b0020503c6a201c1c590800344011344598501c403406058030a42ca2245042c40212a6809100015038002c4014011143c1041e030f02d60b1000c003c85802d0f081180141c1009080c440900c0d01000590f41140e02ca04003030040f450b001800940d1120410b00207403a698990307044034180b0800b070284c074a00310741007074066649191840810b5991102998112190620b0200148a0400300410b45010740d040d50f440c00851031038045260003401c2100481001c4c400008030b40395080f609440144000d11017600915201c2d03180060381e10581c1414108071307000e82d040501d04001c80001140c44410386209003406105500e030f80c206094000c90305405084411305000200082c00700d9402151b003104e100701c82c02d4111000c00410302c0140c5805541c800c00502c03000d04003101040400307020b0100c03000c0c0a00001031112203030319904146d49441219441d6904003000c051351a5a0601c1031200c84601c0e030901a16101c1e41750346032541c83c000b900ca0804a107181c01c14141c03103000c2aa8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 10926374 1250 10925124 10925129
    0x5091003020f030a061502150103060b030309031c141201030b070c0804060801030209010501030b090403030c0c0203060f0105010e0105071101030c090806090d080115020c0409050102090a060207030512190c0c 91
    0x50b40700c2c0c503031900b0708105008083d140924078284004041c010b21480c80028495900503950310b01d0602d60340b0f1680c840c0060032078180303040d525020610002903ea2410042990207803151410400540854030011b0301f460212400117041c000c04009865901b203114810b10304580d0300100ca02004d0303032205d0b030450742d01c0390941c3c00916040e000100018820391090700035068a008a556410740d0b42e07500c3c01941200c3c049085903801000410009012034002d0388680340d081c41c1414900c0810b045903000a0401c00c08494074100084100d00611255078496546100a0030030308080e49007084030303101e40f1705500e58040580e040549540c5140300a41c4548072070401000c81008a078010308241011580342c8403052014000680c0d8100000350718007110003680c2402c00e40303801070188085480107010280402640076101507408001040e800c0d10744440e90703401403010b039016081c02400c602c0d1940c107103030002503a040030000a000f59421240c0d0b166040103112510305080b0f084140c54603240c40e810309644d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 10927624 1250 10926374 10926397
    0xf0c03020d080d050a091a04020f0a090e0601142409100518030111040618030203070b04090507050301030b0c07060608010608030403021f080106050c070302030607050a02011503030509100302 84
    0x2480d40100b0850307000050b02e40c140c0c4aa2050056903105200340741100d00c000030280a03200e1007911400140e14900c896504640058010b500711000c91020440b055030300d500181003140c1e10041d4582074031061242c0b501401c4261129040c544640001031003104000b000c140303045200a03604450140040c085034060340018140d0b41c280c140d288009001904503104015610880101041d030303515040c0f06500d2501700302e4140c10309050901c0e0080300c102c1600a4141807501c0f00c9030700440940d500f00708001c01041d03c49855540d45060503000c40075070314090112814000c1c1400140001010740c1072113503201c00b0301080c142d115080c5050080240026034401091546000c0003c40c02101c044000d0090f01d000b40c41c00b0ba1130f81d65030001905840b002c48480d0002994001c010300440d0f110340e00520f454a07070041150540342e200d80009041070b80668911010401c00281e56402035028003c0d05980304184824144007440c6840241c128072034000898030592000b00070400190081d4107031100844071 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 10928874 1250 10927624 10927639
    0x30f08030c0913091407050916020c06040905011a0f030103020103050712060f050111030f03010501050c1e0d03050a02070302060f07020304080a050a020102061006090510030b03030d06050f060403030c0f0c0302 92
    0x1d21810092032113400c00d484004680c07030b00328100c0c0e02c0058540210368029255050680e154070b0710343c988605450281382103000c1d039603a014081d81c5042c0030300054038100000240d103500d0840c10300d02101d901182c14445107014841c3c54654615035003a641140d40a00780820190380b0311400711540c00b81c45051030310007403410901098600700c1d0402c44c02965401c0e214408540c02802d00c06075030b80107401006003070100800062009500c110040c04171f90302f2040440d01100c1c0d1200042442c0002d071140015035911400c101080c2a40c0360240c0d5400c0250b40c00d08514104054400940b91140100102d03032055086c0d0101e58410320030403c030b1b8010601d80c0180d65924120b454450f8403516158000d90040c4288008104501841c4006004071340302c039140c6146042c644006e00c89080d170791a82c03070f2050555032940d4802a480510060454076102c2c030001034100c0c02c280403c440c084004400714028101400180000781d0060001c00c2c0303a0b0f8003c90030343c0d4400301c50f1400d5004101c203900000e400110 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 10930124 1250 10928874 10928899
    0x50910090b04240303020601090902030c270405030306090601030b060d0c090b04080c03060a02040e011202010c081206100807020a0303021e0f030a0f0c090308030702070e010b04080105010f030f08030c09 89
    0x103d2049110680c0e2095090342c00da03980c0c407202071003910181e0381d000e54140c0001c18221101e16020742d0020b1090b420300c0401c07480c40e000e100c0c401c00040c81110b0946075a08000200b182a260903000598401c138242010000051540080340060080c000695034041e5603030088004d243c0a004090001c0820840455030340351281c9803580c4843d2040380c1c0394000d100d418007095513019503009490540707840d1a100c40d0162310306407c1107107030061400140d05110b100741c42030b00030032035210092400b0307500039080c0c2ca01402d001050000e00c0d403803031b1040b40030004a81d00780450254042030310456241c15140240e107518101c0101031010480403010b00c40100c00243c05020f00d51140041e6214401b1454100034103d030341504001510703141110113000801d0a517003400001c005601941e0050010b104881030151500c2984003c100700780c110010154000c103080000783c03c01d0150902401c0144560445140395654079060304040d07520090182c0000310008000110300c00980384501402070030042c0741c09 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 10931374 1250 10930124 10930181
    0x402040603090209060405060d03051c0c0807080912031f090e1e07060804060908070512030a0f020415050a05070512031503010c0f050a020109020909070609050910090b04 75
    0x10120040703000d00b060100203545c03441c1c6849902e1040d280030341503c03c0100c15560858640c0c1c0105034400240381d000381401350422440c0700d002405851900d49020508040c100a021840000c0a004580d800500104090407105003600e4221803607c0e810002c241c0a00ca0619074102c2c285c01c4410760303510307061080b01c40400010308540344d812020048800150681080d644840840c042c1c0b802141012010800180032540031480c4c0c0c50181030454200019135880c0d6042401c15480140b00901c0801800315900041c81501ea40303170904401145040d14101d40b07a44858111424002032003004035014043c94007d2046428240c1d001c0c05980c003400f5084030300c01080c0c10a403082041c10031082c0510784c16040500c07600300306000c03039141c1104a4541100841d0b403075100c40b0004003103549890403c0016100d089040c1c1c0280c04080151241d1030418200400c45442d0340d0015110318810030500601c1d0510100c500c2c00c0e1090b900300031502da400440400c015001010b00002044102c034040005038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 10932624 1250 10931374 10931381
    0x70b0109050709060c0f080d0507020c040f1406090402030a1202010603120504080c12101a100e0607080d060b0a03021c060617060409080f030f01120b0106030b010e0402040603 77
    0x2a42444000c0105460300203040b503003c0c0c41e501400001c2400c0d0002407001c610440310050415200d204603c1c904007000340740b04151542900c0c2e44015900c10781100c0c28610f850b002d040995011648204040301d405410038030551b8000e85014002c8100c0d030003103000c0d5103003400090a029084440712038000d01009009008001500c02500c42e0015208202e445600c56411142145d55040081030030382444010840c07076001c401e83c0e032192441010401b6580b10041d004a40c0440721401d0840300e42031800d4103010000606205070801c00105052248131656103030280c5109036003102406441d03040c4208031070003e0034190006e120180e404a81d124005a054004010065000c00070040384d91222003194150b40250040b400843c189001e05071540705a920000c1c0d1014008001251094540c1c0311b41070240d10903403614070b002038004104000c03034030a110b03040e00604182444050008450310b90480390312060081c20101a21540c0c1c020181c1e125001e1080f410f40024000c541d610356520014004 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 10933874 1250 10932624 10932629
    0xe0304080a0b010e070806120a0203070b0d050603060405030304140c150903011401050306060609040207060606030902030d05030f040312090c06030e120c150601050d14010501030b1c0b0c090303070b01 88
    0x1c0076450b0001c150703083c0b842038284c0540d5050703d481000c0d403141c508120602902c241043c80612503c16100d0140c2d400b00700d0035001b0030701d150303410380d43e8102c15050402f5603c000348840d009521050500c03000070301c00412640c0c403039000303800e07054000f0030980e58504007a0252000e503400310a05201d240455218002090b1100c4214020400b40c100349500d00400c2c03400740300d61589600070000080c50b84c00c0000080018180040005140583c1580d5120490b2100d4120b031000076540c131440e1027103007402c001040c3c449919003009800c3d840d081e5000041030800910050420881e49090074144800740c200c1880141c0c41078008000e9616014014018101740c0c12201084c46807a00d0a06503107140b1080351072080b1402c014024004e0140303603c0c2181600941901c1c1000000c1044016000217445441078594005189159035450400014192504408490b2240c50080c1c98124403102c1c440e0341e03010103030744000f004e0f81503554624900303058011980002e41601000400c401040101003806d0305 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 10935124 1250 10933874 10933883
    0xa030e01090801290d110105031b040f031707050c0409080702030303150a15080c0705150a0b010f030c0c0f0201090b0c010603020a080303040201020d03021804020c0a020a09020f090d0203010e0304080a 88
    0x112192690802400815200c006072200720803090413183c0794400c0000f55030ac0b0070082e000048901da0f41c0c000c40742c0765111707900040032107811000600c108900c02e12020046540050ba807802c040544e212191514582c5070b0070707440b90b961183d50408001f81c0724240c4070200d8004055030740307e00d0b100d401c0c01d1105161402044c82480d10090108220701000345080340b8440944c2c0300116981c90341580388055005400584480c840c0290b0500c2940240d0006807140c00c41400128400d80880000b41002d84459155801d00d41810000780d003071a40015240c040c19045804600304c0111400140c1c0e556030980c0200b52441c03c0040d801c124002d05402c0003007128400d41c1d501e58841d65488950340c0700e020584000740180c029940c000400c9202e90050810081c00f006001c1d2110420170005049910100c0c282000b03800203001d540551915030414401419080c00961a004040c1c0b81c1413418031840140c540f094070005003d4040d510258809414a80404100c030354594a074101780e5554600c20408a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 10936374 1250 10935124 10935191
    0x305041104020a0203090904020406080a0c030c140906040b011101051008060c160f061506080106030c0903030e19030c030c03020907050c150606070b040305040609050a080a030e01090801 82
    0x3150381850300c21240c1c58503607903010f1420950b031182000940c1002510603a801922208041740a41080c40040326491040401e21003040c514034041d218820154002001d600090941c4001922950780841e800701046600103000034400d070050310340000b401106c03031a540c030f07100070030600c0b20203d80784a007030700d500004844c010f03a10350041c99281d00c20000000c103102d0742e1a9802c0001030204501c5048248034102c0400c01310310030703000c2c0c2400700704950180340028680401080306a0705845401000302c071525011090b6404c581740030701503080440b2100d01940c922109442581d9070074149002455020080e4a00e5556a0900c2034103505039020a91042510001240ca014080e1045844201014001e0a8030b5040305281160502004207102c2e0001c0082001c10005404245410700c143d11a4a4444d203035400e0440040101030f10b50420750003805844000d0110160018000058590500d0b002194808007001250303181c82560040200750300b40555840e100724120801c021ba84007424008 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 10937624 1250 10936374 10936403
    0x50d0503100b0f070f08040902120406050603010911060f040911040e0606070b040b0c0408030304030306030506010f050a1401031d07050f041b08040303020906040603060e0609040503030703050402010201140106030504 95
    0x1503548110f102c4003651840030015030b40010342c00b040d0040d049000310780160070150b03200d000c01d099038031480850a040c08450200000c0014621079140c00040c1640200001005030703541f210b48a00341400144120001f040d50588c08401038100d0f03015240d8004103108640381d8104070142d03030300140550307403011500710300103032050034a031060710f02468020500049a40f507580f01c0200701c45014150014580007000007040c9072100704001c3d401140300e81d8002580d00c0c5941005400c112068212b40002054110300300410340e41d50f4803400660b005c007010341c00440f0080006070024200130205245825041280710911040415540e085402c15641c00c20803800f60807c01c0210385400954840e41450300c0301015400780314811003580544203090040c07030b02c8004400100f040d003150f0b011000194a83d10140f000b00b2000c1c00e00d603041070090303a000140b0704060369406e03120b000003001001003540e20710006003036a20035040440d410b00c1b58906080c140d61603c2d40240038290464055540f5440306114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 10938874 1250 10937624 10937639
    0x90d050304091d070b13030b04110a0503010b130209030f0a05031e090607030503192c0105060307060c050a02040204303302030106080618010303020607050d09050d050310 75
    0x30b1010f030526030001c1c0c0748075814001c0495071500304003043d5420107080d8502100150f81d101c0b03c58011806038850382110121081003140d024501d4021901a074188401400d46032120080024040d0790f011001d41c031113602102091030440038110605079403040070742007024444040002c08072000d40c0d030095550400d14030488007151045140503030704800104400e0f07011a102d20043c540145c2440000512a030444452009403901d201e03031022506030071035085540c801c503411201d605140110084c0141e24108000075100c202a21684090003018036500c401c0280a202e10b403101a0300038403c40d00c80f500d440e039211088407147d0030303022402049a4824030300c5103030000c0b100740583c0c0001c1e0710b040000d02890541203000c0004041032203070324551940317401e00614000b45000e030103940d5401030301e454100208036000f620305401b84d02400302a0014004030354045041c940c04017090a10996850055140c10002c1145540240c80313800780321141c1401961150085000781c5140c20000207890704c50b5807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 10940124 1250 10938874 10938911
    0x20d0605100e06150703020f07060906020f06040f02040b0307080a0803010f06020a1205091302041202010201060506040b03040809010c14010b010915020303010909030512040506010501030f0504080706050606090d05030409 97
    0x2c103903520803090038044c0404460040103102e01d610034416240415965207030030786088080d4001901064000c0428484a9810403002810800110040401d418152645000c01e03c2d51403000c2e00580d107840c803588040d00c003000424010704250045034803140987c104030010382c00030700a041003100f20800015040d440022180800f90700b14001d1f400d040005001901c3c0d40d80000b1105401000c0803564582120541c4044c000a22000741c0c181030860162000a013142c29a401032441100280414000c103084142603a900543c04000595500040c0340140d407440a14800100112a44609801014019000b02440c42b00030303298044019110121680034107601030345400160b10510041154200039013282c0002802420405d1404d096501d2202584070200c40c1600c1c5540b168004004039603142c4108400002c59000400850810b9540d01c5968800c0390005800c2e1078503039000c07038843e5441d04110b8000b070b10020101d03c200610b500d025602c03508a840b0f001c1e00d42e85000802843c4400140307 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 10941374 1250 10940124 10940131
    0xc111204080c04110316090506120f060301020408030f0304050102040b03010815070e0f011803020901060f02240a050601120213060810120b0703020c0105070507020f010e030706050d09020d0605100e 87
    0x200207802c586d50800a2803a054020042c2010000300e0400040c03951210320084c080f030242c00100740c400b8074000c0d006240035071010784040c0c045c0c0e204010030000000003205550806040782a450b5590725141045800380c000d0ba006180600c00000000942d440005140d0700001e0b40b00e44041d089a592510540340940030444881d003003451100000500d40c810006084103698044035000352503140c1d0080351200d9400d80000d00031445d51904801400c2d010441e4940c0030401c4054200e8406d40320071160741184024010124490310303a4003290441c6c2c01209071741803889000000b10b440d40c18100300760407242d800c1c0c481c90020608040101d41d6038111191010183e0700300c142d20180e1a041551449140b0200400480030550b082c841641200001e010b50303400b03003c456403500d40382d0a80c5d00400084003800400301e8184914100c3c07034042070f04d001c202441183d2040c18126240c00c86e0740300c60301c0545800b40303009600c14808140a0b041040c02e1303020b00d010344065a1986080b03500d0342c001164102c0140c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 10942624 1250 10941374 10941401
    0x13020f0a140d050304170610080d12050c0c0a05030310060801030503030705090303070f030e09010915050f0102030702040203040503030106080f01030b0606070c210203120414040c111204080c04 85
    0x3040c50200d410701520011890b07202e001220302c2c00b5a1140c10200c0c007002c3c00c0300d01392180c00500c20320885d0742310301000a02612005015101e2861404006481e1005003104980002c1d107038000200e0798219001030341c824140240669800f0409407500c0d585983c012144259101812240824040c0c42010011f051b254400c0095141d030711003040a4400d03402141d080740d40351004112100000304000300185142d480381c1c079241d100f400c424040010f403190503002f0315030301441c085482c2920740c0402030b010111001a80c1c104030902100004074111301c11f03090040e40190000060100700800000114100c41f102d42d0f810442da03c0302c50312030540344428030000e802c0c1180e25000c944245410001003146a00c1b52412008243da2a540d0808603450150744c0d51041d4412042ca44c04c0d41014407041150201001c1c0300f0f85024100350504590b0b030010003d503070180360340d4408010300e54094003800075109010300850f038400480c189059200d030700a000f598003501a0b007840c046c2c20b08083c01b80d0032441441e0b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 10943874 1250 10942624 10942649
    0xe070c060e0106260703080403120305060f010206060909030d020a050408070504060305120a05040906030f020301110a020a0f0501020d051009060509060a0905060a090606020102070506090a320613020f0a 89
    0x14440900707555032a5041c4d400041c001c450300040001d1402c001040198800e00441b030120028041c054100c1d04d00616941c00360b208184015666a4041400d40d40288116200d12503a16000c1d83c0c24030794000d00b201000514400290303200d6564012001e0021148140f049038200c51700c80040c042652a18403004020b6400f44d080c801d2008040c002410005072145070040c00e140c0e603001b2140a440695206a8200c03c1d249a1582903003400c0c001c06440c81d421550151601c0c8604400a550316402c060192400ea948204402085002c0d012588822003000d03051002c0d0506400309801042c00384034200b00786103000ca0015041c20400f011600c1883c1c0241240350152820003900080c0c0030040c0184d40c402c945e00c1010400d1041c9120b030301c0241c10b03190300060b1100b540d480c006240000291504d02d541d40040300c03150009036070005c0c0c2d12140490603070600c0c40c182039010051010510860038941030150000301300b0090342d840c1d5108000e40c0225011711a401a80d07080c8015108076009004041c0302 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 10945124 1250 10943874 10943909
    0xc0210030b090702101805150c0d020403030801140a05030706030c11010204080d1101091203020705030702040e010606091403060112020a08060708160503060a05010f0e04050a02040504060605030c09010f03060e070c060e0106 98
    0x8c0c404071a40c1c8009000715051420491008d01c00880e0720980088000c81c80c02c80040c01500c8201c40c0404030540d080d00c0d0044064181400a56596030301e01c506000c154480d0c0426840070710402c101d8222044210007903446540b80c07401651107120042080e000500d10404110210380c050003040420384c1c05c0344046e84039500b0903500320007039841848107641c944410490f02c00161503d1090543d0000220000581076041450041a050050b0301940720444805000040b07980e011451a046465000200c0d45080a520104030882c08a500018580c0a4503041001c615004a8058492802c1100010030f03000c2d1590305a400340070640310710f5009911884240465402030038416001c00507030a2844622103a44001421380304211a20a10782c0e070041340c200414103050007854064281c60510030b08601d82603c030005a405501d60b114104003081d11807003210b40c040d90041c40985005500f104051070181805000000c82910894000d450072800040a11040c0700f01c5042e50071410001d086048c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 10946374 1250 10945124 10945153
    0x807020f190e04020d12020105090f01020c07050d020a0e01090f05100608041202030c030d1505010207060c06050406020403020a0801050405210403020405150402040f06080106020705010c0210030b090702101805 92
    0x40100205d0b00700380c00400d0310000c00c444070003040009030740d58000701e03062508a0310242003050000b000d083d507a0060003004403151021a124082e20020b076025240100e2038000035a80700080d500202e8000c0b404000031425829a4201c0407003005856803d10560b1102404046084c215221300d0b400a008000800e00186240b004120b40c401c0c248122801c0c24020300341c85080d580541d040d54030255a031503101d10030a6060382d07004000c1000b4000342c011240341c40310152400c0c000705c5004058030f07584e40c00201040203542c1070f034001c0e580241504c01a5500d07180c00754000e05081c0e80a84052041c201c2d03da030158000301c0e0005180c81c580c442c00d03041900c1c545c240000b8210140c286031143c0940040120140c840f88003070070041005820034408240b80c840064800f0206801c000b08540003034605020716604101c0d1983d903140c1c1910b40202d08a00f95078100c00401411400540c4105036030240b1a102e82d00180005842c42c00034000c00c290b8649550702c0490076a03503030300100960043c590001109 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 10947624 1250 10946374 10946399
    0x2010302030a0f050a230702030a050c0304030f0606091407020c06090414070c030807030209030703111807090807060c171b071206050109021305090c090d0807020f19 73
    0x200710000801c1440c0c80301c20003415510210340311806a981d6100400031034511040c4c1101b001000d0f00300c0300320b50801c014025101e11400c075620007070140c000360444804e070040048030000c58000c00c00b000401ca1070b2800d5800362a4601c94403210905107229a0500c101d081c0c005802074a042d00140784100700751040c0b04841d080036040035441917890810300d072800b1610710340340d00c40d40007039880962075102d914020b881000003501080c1014818050303403083d5140010010142c0b5080140c080203003105000180c0e12108440402100b2500302c0148050f55130000c500f4000d8400d200c1c251101c1c0ba071200011100e020f6035003000380256a000306c00368050a441e1005040300c0d001080c4c440111031000d02814034061040d40301700c0409489803080c10074082103101c1d01f409071604000540c9024042c0c404202c1e807041600590b4410608800440c5030f0084140844082c90320150a10000c41d6480c10151500d400a840583c0030751079a95280359240f8084406081c07141c0c0301da020600c42800c003507410040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 10948874 1250 10947624 10947631
    0xc030e010c0501050405010e0607020604030e1507080d0603031d0a0506030a06030c0b03070e040b010503071110090f0204060902070c0909050307081207031a180603010204090212010f05010c0b01030201030203 91
    0x14040d8030101c040200300c00303008480c03040e4042d0b0004a1024000c04049140441c010003040c00c40d0060028040001d81c0710802210101040b00d8010380501c104440303291601c1090002091214001144105402c00d600030b041124040d480381c052100382000030038940304158820700d600c400307940d90502c094508200550741051400e41d00281032612503590742c40b00034183c0c101c00e5003000048104003407507a00040300742140400740c5003030054085000001c0c04a00002d041e0000f8082407500e141c000c0307107003040340c00b0342e00e100218244190009800d101c0381d0040c00d03400507400b0318107090022039400e5582c0200c1e40c0c2940d2015071303402818a02400b502c0140411601180c1d140400c02000c4046018580a17045043d805080300f1510b0400035409801c90780b4190305503003c081035905201d11651030700071005032100d000c0d110031403558843e00020f0092003690400c6810510100c0e03800d0695540c284124140c40750004e0b0300040c05e8461005485001410700001c0c4032441d5000103100652080d00039540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 10950124 1250 10948874 10948877
    0xe0a14010804080903010204060c17121302030a0c060f030e0102090102060408070c030b040c05030c0102070302150901020a05070b030f0106020a020d020d0602070c03080d06090e03030105090619060806040e030a0c030e01 96
    0x10054244c0009003a07910543c061400540400040818480c0300c0c54007080c5980200b005078070b040e40c0c0308052010351200800c20401e10354440c00c2041591018009251081e6100403600503080c2ca504010b40341e520540c0c90380000a1421485111004c014402c0b50007a4405800404441d604ca5591010592000c0c8d01240c140140c0c120000004015090040c012440345c052034004500740b41c2031603d0481d8142e071241c1194450f0604101680380e034840b0a0451200748489680c4508441c0180d140030751030360008001d4030402c3c100240c0040761001650003030b071826881100c2c40c3d0340c0d600e0407039569a03100340c081d6000c2444100c04005150050000002134800c2c8400740c1000d000b5194101070441980c0700380d450000001e8000703010210392060002034885054108007a075069a607140d60780c0414000d8500804102001c42d10f580d440c00588202050008004c20b1244d80b01c21004104007003e594244c0968100807242250f907201200351100c0c59100d03034482901c05441d0b02c04807884c52901e8052070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 10951374 1250 10950124 10950127
    0x70e1003050f01020702040e0c0a14040b0a080f0705090f13060615030b09010b120a0b030304080a110312070201020d1d10020609070626060310060806070e0a1401080408 74
    0x398042c400840c04207a11000142c40701c145005000640b01c40c1c00c1460f02c0707a0444c190388031055582254201c10350750710035180c001c5207016502140c020590b61619580c01076090300002888040010700d00c000c078202a040d2540655a40203002e250107090314801c0400200c400007036491060000c5285d103038cc2c080c203030210310f40f5641d40c5103440e00380d1a010910b0000351280c1503ca17044c2048003101d801801c40303c006520f04101005103100e40d0501070100c048194035100c1640310740c0d8003001642c019110820644407001100d03d0000032030f810515030f050090246104020b04190040c00784c0e22260340603009003440c104020700441d21082039141c030b1420303120702c9001c0e8400764460314000000f0304084d800501c0e85050040503207182c41140d500140410942d000c3c80714442c15000c029040004458203085000c0d110040000d08000c0d80d247c000f05001d15144000401c2040011018001c0506882c1c504500d400d101c00d1241c3d0742690301801000c000108000076aa500c19400a54064003c49106 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 10952624 1250 10951374 10951379
    0x7030804031209080a1107050105092e1e03060b030406090201030905030f04060e060a0e1909110306040c02060906130510020f040609120203190206090301050709090e060603070e10 79
    0x50007220f00d00e03c000c0c1c80d1082c0115589881e1904095948100c02c103d200418105241c00002002d9100e01034906014526084961484188007a0302e0820514280c410380048860480c004084101c0c50740000c21851819504007072071402881000c00f80c0e48007000d120f2841d6a55111000544500c800480c109503607504524041641400a06981628498405c2c2d03128a000d40041c5191401c220052080504000c010782458202ca1501501213066501008031780100f9480d5010960550011400314200400f05000701c00b0480218440e000c2160201701034802c1d503908903034421040314500aa6400030020881001c000703010348030b50b075118400721200c40c1c0c3d1242c1d07000180d0308000b03450609150041400d00400d50015001005031540984451079050b142e00003a0362940f894075400601d01650b1542d5056481d10411618500d00c090003d0200d814050002000301c2218030034070411602d010317a09000c400700822170900807000100100104c3d4200402c13400042c01c0a0b01c3d0a13011b0301c030001c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 10953874 1250 10952624 10952657
    0x7090504080909150f09010509040b0403020f10020d0e01140406110c0114040302010506010c0b0a0b04090204020705060708010512031903020c0604030305061801150305060a12060618060303050703080403 89
    0x22034800e82880d16100e0091406805210b400311041d6004c86c880c3d00303090010701c140d840300d0708440d40c07140c3c0000b4000f10940b1035050680c24075940450722500390046600c40310b403610098004200d0640084400c11060042404181c00c0300c0310403240c03178991111100481d011901c0d0740c00982c00c07019112440e078a0701800303a03030060846a10040710000c3c0b00c0b10400700300038142c0a114590340400c0a090240c1d20542c5c0c2c0e0745042103002d000f8003105415944180300304440c1c495522417000c0503405001150f50300b940e0f0902e50350b0303500b080365030000181548001040710b00384903141c0c0351a010214000d5041c480b502060010f4446001d07501c200b0594203101c0d11a8031007017000428002c501079100000c3c68109541405500b1140b54092070103841c04000401048140c0f0582100341c042c1440c000806494080005400710880d41c040800940d5002c2e0840a100b4190702c5a411100035240100b0200c040b86130080564001c0d20029022440c18808030b000b0901844e000d503030117807081c40c02c03600c03a0200303a24 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 10955124 1250 10953874 10953889
    0x190f060612140601020307060c1e020a060507020705030705010302160813181b0e030a050708010c1b020108060d0f050703030302030105090f040c05060705210a090b03010602070905040809 82
    0x140c0009800203615144120360384900315401460302c00c014494a01000040e69a106103034008003140e035a081c990114621401c500c01d001007050054808901d06100001d54511070441c003a04e64610300004a42d050740001030f80b00859002130050300c055403610307006600940200404240e03000b400c02c0c0b0300d40020440c40090404011261040905c42d040c40d24a00c8424115018248010310b04001202c0080703c99121010a680520b401071445c04903401003424400a20350007811407080d40d401190204040d00005c0d200c1216942c3d681070201201c07040080000a55000390104854102150389403c2007104403094034055081c070b44914200b0b87d00c1c14a4080d40e40c0c070540000350f0110060100386080c03203e99402c078880c1803001d9020305003910350348242103e61007114031030140040c642080000070301644124090350354543c500c0594440048000703505c84400a000190090004280c182c4d21000703490596045900401410342805000401060060019215441d082c00740141603503a024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 10956374 1250 10955124 10955129
    0x1050c031603022a0604090c03090f060b03011505060f0a0c05030705060a051509060f0126090d0807170c04030602030411010305010b070201020a17070b010e01050a090203010b03190f06 81
    0x180244440304000751032555403540c503202c40d601411207130100d1046540e14825141a911100381c0013030000d440305000c2e4020041c1810081c62a40e05440c06014409142c0c42216840340030b80c000c4c040d040041c000d150440c403003400f5007580644284403680250621001400940106007032501664149403240b510303541180000702c0d03071540301070100401e8400c0e60140726084007a05403001e04850802d030006a464100030500c60250010007001091680f05065039892041c001c001c090160120b01005240250116400d4850707100382c400d190076051080c0c119521030582580d90340d8060b10808680d4120f8070010305088250041400084046401d601c01540224403401c224140c403400600050f0035544c0581c0100110340062100b5070150742c0201d410228590301c0650100d500781000f441002601680d9009082d42c80010004900200c00d84a418140d80d8200d82c4070854a40e81c45aa0b8144c0c4024055441c9a900c00e1010483d0a89800b0b4814140015260081344050908021034201c0d50103a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 10957624 1250 10956374 10956377
    0xa1409010e0705060c0a0f050c04110403020301140c16020105040302040e010203090105011a0708131d0108100203010609050105030603070306020a0207090b060a080105010503100902031e070903050c01050c031603 93
    0x80384200c00828040000b5070052000303135002400d0641c55205a40c682d007240e40040c2100380c0031501c0c0d604000d401d1240b112080c0000b001001200002d0704c0741c5c0c10907001400105e000750301c3d04065015a01e404000c0a01c5400c0161000b131511001d108059880b210303a075022410b05c40203000200059485014680345c07480c0d1203000507240c0c83c0c0010301a094400607030082420070441250303440380722500b0b401c80c0c1505401880c03a994642103141702507101c8010341d2122444040b401c0007100d560a00e001c0550499000d0400c540e01c078244d100d024004ca100a10030800031544d009010022b0b94000d030003031603009000800b5120700755076036103601c02030344e100c03012071801600b0003442032040b2000c61050640740031080d20b03c5030038003002c1c2030054250f19060290a060000200000f101c0301140079465001d03001400d0700355124101103440484800e984810300d120110440001404ca52107031800204480c3c00400525202e030102d80151455071108100108500003041301114007a800201055024440d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 10958874 1250 10957624 10957631
    0x52413031a040219030201270807080102040608010b120a110702040c030510091104050405060a0801020a050a200a030302090307030f14010615080415020c010c09030b0a020c030f030a140901 83
    0x1481041120380004446041001c4c02d0704007400580d0340500c0c100d5541c0b0030070107151405c440f92840140b01c0c8d51103605c43e442074404c4a80c0402d180c041034020303208a03101038031640c000e030343c80b10f811030f003603000f502c1043d212410802c0024250b60281d0300841c6103242030640d41e03440c4c002950041000e9401c910304038400f182d215070a100c0028050317403c1c40010300101c00200720800c001038400a1038826480f403d407003603403101c000c50365541d0340a800c1001401510000c540d50524000c01802a0300128202004903502c0d0544c9e900c25050800d0401c5250705c0c3c9405042c900110341d90581c020b4000020f01a00b501c0b03040300220014145122080201d03005070503640c3e10300b80c006540c509503050b64000313004031002020004402d54001c54040d030060b41c042040155507240e49102c0b002400388001c220301c10340c04c180302c12490640083d101c10035240503403e150f24541e40d005224007a40300311081c510880d0310810000c8401d94510b8050368001003103030070114104d4400d5226000038031050f02c045006035903 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 10960124 1250 10958874 10958881
    0x4060605030606010c05060105040b0114030106020c030c01140d050a0b040c11060c0702030706050c150c0a030608030301051309020a050d05160e0c04060c03020705030d021501052413031a 82
    0x1d00b044503a40c4100f003444d0440003400d09590302da884040c107101d543e01803910303040c45e410240c1c05900142134400c1c0d16140d10b6103170b60303448400960ba0a03095140c0b034040d0080c80d150740b41a510030400d420300608a8034040c1e1500c0311f802401001814010311000b0f58030340d02e8050000c00e03503450080001442450b03485a10b41d01c0c4400e01c2c5400c00a01910b024031403103007008001c006890200303082e800c03508203051080c0c0741e031420609941829145100303200000250020460032006040c041d0540c1441a6000c2001c5a100c8503016503038071081c00346641c00310303100720440303481070068100e186e40070310250950300c681795101c000c504a120308640480d41d5801810300b15001d03402034491640201a001d5040115040c0070300d00804503c0b950244104104183d240d00701410700801400009040c040c0c101c0300c14052188000352940c4400c03400700001e9000f04000125860801c61071546003646200c1c400c40c10a200004065503403012512183c00f81c1c2d2918004046102203807900903024203100e40e80040d14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 10961374 1250 10960124 10960129
    0x30204050609090a0308091006060c0308090601062a0606080c1216090b01030e07080d030c02030c030307180905041a0606030403080a050912040305010207110321090d060504060605 79
    0xc000421150141d0380100400c20f142c440091500e4405816040c02801c1d0f803509454281820100081502980e060542c00103100d5803202d5407065460284c0c1e62a01107440e0211b04d5500c0740d60a00c2441c00091401c3d804408241c075103c3e458588218030108802540f1040e55030b081a500e2580c4003060350f801c0601c0083d4982002074211490800d030402900185454803080450401d180c054130790a56501e00480001d640a9403081d4981d561000481302182e58410005030b88001c1e5142c150300080c202402c801c2c0760342c0000241c40c0c0324060710024508595811108841c102c546080f40401032000c02c80000300841184191070065028803e14900c2e00c1e84811000501400a0304150040343c04008200110b81d0109031150000c21205d80414544c070364028640c034000020807110a15180001c3c0002007090560082100c03510506120b00111a80c0f020591900c190101a0085a406084502104200e10020031182200605030450486151502030071a402110101c0f82c1a030785030b10901061 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 10962624 1250 10961374 10961381
    0x90507060206070f02120306010504030b0a09060e0109020d02130212090303070215010602030304060b0a08120c070609050d03032307050a0905030102040605040306020309030702030604030807080108150f0a1b0306030204 96
    0xd03c050404000701030380c540000350388a03003c02100402c040c012010071001c5c1c1c4501c00322802180c001000402904100c0617160062550300300c04c44065140c1200c580c2424010300410840075001446070310480019002c0c001a6000100e40c02c0d51540e082184845007580305800600410006004540ba0301c6d0012001e46020b03e40301180c48101001c030010007040ba8008112540958015804110aa0103001061801145030007404150282003602180d11285030090240084281e0481d5401552148103954002e05030040c5908080142c2d44080400d000350000c0314105d4181c0c282c50b10761400350b401203030a0706060b20401c0020350f00152909030558801ea00030068030f07080f002186018078102019100703210360b10000f084241c010002070034051042c01510203160b005001e403840743c941813034010308441046034040c000ca0007007000480d001d1400256102d08011800580c1c0c019285c080c814003003a40000c044c40c200b241c9411207104805140341d1b10381a070345c80e0b949000c1031850031407041005a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 10963874 1250 10962624 10962631
    0x2304030905041e0b010c080c011a0f010c080705031909050306070f0f0e06090a06030203010503100b060304080702120d020303180a050a06050408040902031003060f090203060105040e030904090507060206 89
    0x11403c0c0807402c4840c500b0f110900b00260344a090004031080f0000058444591001d000751000b400440c021900100c1900090b00c48450410396058401d01a420001617001003007149000803100c00e10540040c04800041c61000d000304212801c240c25211080c080300d00170b841800000e0031800003001241800c0121a0b0030000b17908081c0d903008911070004040c01204c68105041108404c14140e16817220700c202c07501200082c0502c03841940300c6401402a510078071030180203201c3d03810403d22244443c8561070039a400249020314544440d200c40c0d4203a04040743c142d138081071150420a90880030061556152141e4010315100d240c0b48800c2a54580c45070108201c6410211040c000140b001c2002e07801c1c5c0d039211400080d29100c0307080040c464060790b0403102c00b071440002070049024070000c00707204891107001d042c030100d044141042d081d11a000c2c030081d0148d0001005008500d002d821503ca4600500100c9003007a5040001405980320242c0603a5281c00003c0c042c4a0940d040c805180d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 10965124 1250 10963874 10963879
    0x6010507031d0d05100e15090703020402030c09060309102706050403020c03070b0d0b060901050306090702011806090c080706020601030303020c0712050c09070801080304060507062304030905 84
    0x10300d06192006085800d500c1020340a40780380281d100981d5465a050b1901203411030111080050303409040c2c0001c022461240c16140f00700d03032500081c0305800c05450312500621016050355072550b400d0002a4002030b1150400300403c0c00f800410b62a008095489403c6640092480c90540c1000c00101c13989100d1400c0e903d2f581e071600c81e0000c3e680030b02e81c0d0755040e8002c070001090f070fa40d418120b007822003491406038075000b2244001080303066400604010b00407020100031100902c01001098454060080c2c04a03a040c0001001454500007055002c070b4640004a048070301031880c4400d80c21602c00440c0e50564a40c2c80340c00740142c018240014000c1c040007441d4442c00c012000e940d4103814030004040603000a1071900040046c0200c20003020140702c411600b4001d490843c0d01c0c1d014800c0c0d01400380740c11360009002148659a1b01703048803043c1000d9440d10f0300700700080f141c40d4800700003a11425190807080140926247c054107403414059824850b41c1428540200712401a038072051 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 10966374 1250 10965124 10965127
    0x40c03090606091109130e060108030a0801060905150903070905010f03060510081c1110050103110102060105130c050f03090f0706020a08030f1812040602070522090f0b0406060e060105 81
    0xe40008861382100c02c2800212080c5480e002e8520307900d0090300c0b49016200640c09a40000560500e000020f0442e0415503202e1182e00d0781c075414104c0340c0042911815034402e0a4110703120700600c41c40300422420710050251402c1136125000703102550f00030f80c403500310104c2c40e4404209112541c400c840e0020304049842941e24034100306075a803051010110500c290440ea29a03d80c1030140b45203103481c00464058810302e48580e01d07600000c02003403000759103026400c40110b00f80e600c089243ca060380d0f002054881c1c01c010569104005103000202c00090040401031215120b0000b40510b2056091000070403500d9000c508850402405030f00c48400d650120782400d000503201d00a4035401030b00c9001c1c00c007582c1c1e078403650000400c044000c90714182c0074800c0240c54425064006109441803034003140c90443d601c90a01402c45080c010000012141e070714111710b12661504507130111401a0742d0500e8841030b40e10b44c0710910034140c4007103402d2a51858100301e07051407001c03910380c00342090034001e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 10967624 1250 10966374 10966391
    0x8150303070c03020622060309030816080711030c030c010b0102150118020d0212040506010305061303080c0306010c0503040605130902030105030c0123040305010e060912120a0605040c0309060609 86
    0xb8501c41c402d010080c0301d04000304a454198110705074152018904008108596a0343c060207401007064031001c0d0b00150b034003030025914612001619094040690b03690304655141001181d0080340b0300d100c5030150108000846d182d590802c040c3c09001c54403000014a00303501c4002a18041040c032100b00c1070504a001004140c0e2007203010f0641056603540913a542e0188401c840013071182c11030034508500c0a40501040c0140015a24182d1b40310760200c2d6260744032510108550021984018002101e0038005219541103a0146402c101c2c10704003104289059074903d421900b081d00040000390000c200340240307040c84681d40d0010181001d0441c515418080801d40f03c422a0040a0600c4020110310b503121808440022a110500c4211900d40d0b8413272500f01d0183c50b1071854a4064850140440d5014801140c001c290844000400d0301e030500b00400400810b5001300306003c0503a80b80000180744c1c842e8040c442c0302c51003039030b4001002503051800c902200c0b1070341c0060103400d00d040c0b8034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 10968874 1250 10967624 10967633
    0x50303040b09060906070308060f010806060702010c020406120b09060708041a070e0415051e0901030209220303020c060a0b0109050d0602040305070605030417070309030b0403020a0c060815030307 86
    0x200c0d0305880403001242ea403400a01c2c04901e4520414445980100000460030281544152580d000303983c1280e140c694082d500b40110fa640d102503960b9903004404001500042d0f0180c80800d14842c400303080881c401e581c0c4c00c00f0b1802c101d03401009441841c01c1d2003c01c20fa964050100307583c0000a4280002181003c1d00ca102c0482c41e2800c0808040c401d440209016a0142445c0700285000600a00200085110b4241802468070809000c0e2500807080400101030300e50b01d00c040c14020700082d81603841c58080100102000e09140300c0941038a442440f00072540c04680d202d42d002c1c1d08c1c00741c3c0d0762941e206403618158000702662585864044981510fa03404809202240c2d0300b1600401c02a04904001000b40300b5544001c000d0301c030f40f1000241c070540142c09588a40d001c0c608070f003508020000c0048561154400003030006072030340b10900c001088426a581c119000748100c81400d410756941807100d1001d9003000c0701007a950420808200f030705916420045d81d0641c05141484019520b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 10970124 1250 10968874 10968877
    0x70602030306060d021b160509040b060d0f0b040305040e01050d1a0a0b0a030c0303080612070302131e0923060a050405010b06030408040e01050406140d0302030417030c100501050303 80
    0x40b1071049a002400034030440c07050701602c0340301c08141100c0c5e040492680004d507560702c411020f180c010744110070008291503e2240c0e607100700c2e04200900b80381ea886004201800c1c1f5481c00c01c9034002c0101c811403020540c0404030b00e00c12446074640c0740c1d40d1410841126004c0005a000300d1241d000c003841d03100082e2400303a036102941442801222580c0768040c400e0050001242040d801c2402c0301c0c2d00000307010803106484c0491f4002c0d10740d0045130b1118130600852071040c100d0401541d102c50000c0006007042c06030b031800d0901c20313007001815961030070444040a05840346003070160b0701c0e41c9142d4140038009260903100c1c0380c000000c117140ca012030303100c81d200c010040050444540d500002000e0140c01e401c49a54102c000304265500c1c03a1030b284c19403484e000b0b80a640840f18805001050906151041505513010801c00790035400f0080204036000d00344500480443c00b0600002444034100c18003003140c80348000256031a03c034140140ca141145202d01010742d18108801000140c40100 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 10971230 1106 10970124 10970131
    0xf02010219062003010b0a0c150f0c0f020d09060e06040f0806101202010503130303150807230906100207030c0620060103080a0e0406080102030702010b09090706020303 74
    0x50360f2003ca40424000c992400c0800c04c00143c0550045980c80e00d060b10810b10300c4a0180b05a2600c010f845142c2c00c403c01c5151500c00c5078540980010062074280584d10040c640c00c50761074401040c0050610415041c0000001e154887d9280c0400700c4001d00f680a2243e90020b80d110b441c03d990740d40c100d6250640c0d520444020440c080c50300f080b0580a60165905400c545400f82c04d0903880b6007101e0100c05169031180d03506003c080e400003c0300103011a101810040f443c18060401721842400a005480d0845040002a94075100388607000070040c3c40c000d0b1070f218072160981c5411741c0d540001d41110b07040000001c8030741e48111000700861030781c1103030110007840007080380c5c0c0c0c2c190031b02000f82041410301504e0342d0341b84140040c070842e6100900201d9400d54458074142264400d0b1903190051351181a02139450401c1451035810220100003060102d150a030000c1d16400045c = true := by decide +kernel

theorem cover : BRFrame.Cov 10791374 10971230 := by
  have h0 := BRFrame.cov_init 10791374
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 10791374 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 10791374 ≤ n) (h2 : n < 10971230) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
