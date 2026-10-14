-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3317
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:18:28.612488+00:00
-- url     : https://prove2.me/submissions/97f23625-51d2-45e0-a1e0-5121929c61dd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 596402877 ≤ n < 596582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 596404127 1250 596402877 596402887
    0x10e0607141c08160e06040803030a0f0212180f070b09030105010e060d06020a0c0b0732091905061c0506010c021302070516080109020109050405060108041202070f060807020f0111 79
    0x20320703132000c0c0110710442c81c642002000100400034142e81d00130303071200c0c0081c0d00100500151900510442c007141c4900c040845c83c02203002d9040e401050700a0200034034000040b404200c6035000d100d4520070b103030700313505440d0360540301c00f050000c40c0c001070002d40c000e40c0303010004a50410308403603290040000510080802d2607913500c0d1006984101c02c58820000020005c2c030004900035032460007107a03140c54007441c12440c600d50f03d0940544bc692044415061300e485030b5010101000c13601d0b9208140c4454514a4901c00b0714902c00f8000da000f250032420010b0051032a505541030f80c010303109080d10601041c0c0f06c65004586044e0b20703101c040e50148034030039489180c4070f40768020518148988241c0346210310754007042c0c0c0e440106074424061130b511010520110341e0710407004000b03400101c501300220304060340001c18810004000820814a0911650001d4000c1040c0d030020250585030170202c98580c5401089442e007a5504005442840c000405c800c1c4103009000150907106002c60a107 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 596405377 1250 596404127 596404141
    0x10204180e030304032307060c030609231f1205060711070b040b0304141f14010e012c040c06030b01020a020d08030c04080102040306020a020c1e090402010e0607141c08 74
    0x421b40c14000b501c2c03128420007418000500c58040c80340e0319000703034400040f03803807070031b034004040d244180c003400040c038130f9540440c00790850461080d4001031940710310040c040b5009003550326803580e42c000c240b034000b04904810411100040c124800c1c1003d075203007120b110b081c4121964940d06406a00b4000e40305000900c84c080381c1d50040c681c098081c5416103244101c030440d0b50305014854009260f2108a0440190203118602901220a21040906040b585440c12130508000107002da62030a40e450581200351001c0a03910449a08054150ba0040d050920303021884074064883d00011030700380030040280b0b43c00811861199500035019042c0c00440350743d1000607a01c0107201d94684442804046007100c803d01c00f07040614440c400c0140d6664440d00042d1030041100c4905104904103a09100002c0c032400c00d9480c2e5500035100e4a446403161310068640807a0501501e4000e0b001003413600c2030204c200d1003040307011280c400f5640c02400780c090741e9440268020025001c241c1b540049259 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 596406627 1250 596405377 596405417
    0x70206070f12051006030c02030f070f0c052205010603060b0702040c021e0a0501200a1b0b040b07030c021204030212070506040f1a091818010204180e03030403 70
    0x5620345840d1034401070301d4050400084410603541680c406401a80501c40c41b5018410310300c2516847c00190b04020481417100064032512030001d14a06540581004010201810b2809840024000c010070480343c0040c00070740c004104118040c4d03081500000310640244250340540e4a0b0082492074822a0b4013800302a2000d05030304811842100312000600003c85000c48207441140c0c050030000100d41052825a0881c540b07281c0720768041682240c01c4d8a1543c100c0d425900e09040c0340c4050925a49c3d5080d02c0040444082d010400481c100010400704540c028400d10443d1801c00c00d110606e41b080380c0d1440c0003650103d04d02c0081106201614040003244414000030085500c82a00d4901081150300264006001101e00d4081804910504d40d842144120903040890034600320200140e100486200d00103801c890f0303600420030500540001060320341c40c1d2002950380d07540e2600c0c419540c0078842030440050780342641201e820b0001000b00c3e800f480d05641d411b41103d091b100004a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 596407877 1250 596406627 596406647
    0x1d09040f08090312030a0902031e06040f14070311040c03090222331a2a1b0a050f090a0507050c0106080c090a05040b0a02030c0d1a150307020607 64
    0x103854030501c501205032800304e000540c45140301e04e4020900306040e105052404c140c1d106040080d010034440340e00300740c02c00240c665016400030540c090105460801615200d80c2c21003251940c0141d000120901184191070364802e0070030b540030001c980900e5400c90031240c0c100c82c0294803a0001090004000d0304072074400d00c0104c6480c00080104008204807000350854110f0703001d4018603400c5082c0040c140142d0001800041da40a0011b00d0301040075109100303040c003c42281850b409a05c0c0c100703001416440c212408503089030224000f03003072106544000000058442c0c5403a0f01e0106190605c21000320016001500074200c540b05c078080030b005480024070440c10424284038030141d52209000d6040203011010141c4041501d0704240140e00400401c0008140e0400003400006400900c13001d80c001e06541c401a200d44074031000c2e2803203205021503e00c0d907600700100f039401e181040c081115031500407030f051b040c3c40e060003054461602049079480c0250300300c0400102018003520804d1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 596409127 1250 596407877 596407879
    0xf0a03110c04052a1206040f0b030a060e0615061803011808030a051305030d1a1201020301080c040e060c1c0f020d05060f0d03050c030c0d1d09040f0809 67
    0x41e00c4644a40e010030b00b1544100c03665819030441a195151848000c5840d500c03030800440001e2601d08401031741c0c0c14003180640318034061660b0b642e401807001c115038410082010028181d42c0b000c0c445091040182c00c003040e580d00e5500580c80400c0c14000003442203274650101a0045003040d81d43c0c0421410304204031180e5800d5529410700c450010444500c0c02800c0d0312541407240c0328140800e044017210401070406068000c4c02030508045075000054404c50b0035546004079080c0c4202030380d1204000d4400c859900700c4611010306103400010340155040e141d44804441c1860001c0d030401041c1c8801040711415a000080426840c144040c004d01844c1e80c91010110550001030740f0804030341e40284a0313401c0d103501081c1c00b058494076020301c41c1c0140044455aa40c1e01c0441e0001c0c1c01400310900c000d06114000070411201c4205000ba1030000981038142e8010350000c0f400139125061f51401c60001001410903620185013018031180610b0f001040012600f41554a1002c181c0c0008181 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 596410377 1250 596409127 596409133
    0x70e091509092104150507020a1206061503091a07081605071e02010e09040b011202030f0706110d020706050406030c02010b09010312120212070e12010c1806020f0a0311 74
    0x4904407881ea0403540e0b1440c070503541d00655507442d0107500c00381030800995903410000c041102401503275600d10030009940785484045100c01c098074100f001805641e00180f50310070342240002000780c040e401146010b00030200400c00e08062110b11848040440740800070862440100d080b011103ca584000002c1ca42086454140030340c554030170038000584500294107110f25100b00b1560b000c00d140d00230390300c2074651585606240c3d460000140050180d5116111303800e4150096640400851603601c0d030260664441c907898500003061981001d203201d8003032140c0c1c0c00e6485a01c0c4000b940d01c0443c0d0310b0380d480504080c20300034214003030009100070200310b40d200c003401419681c603448038500a600c6248485001c040d484406404900303841e03c0811010f1041c0680e1015040d04980250302c03100ca460841d40c4c0d83c842c400001c800c0d65007501041070030b601c0c1816030480260440c1030b0810b07106221040d0b4809039510303101241d403002c07251110203540d0898010880001d001e09a540c008101a41c15 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 596411627 1250 596410377 596410393
    0x209030a1e0b041b0e131203110d0209042d1109031e010e030703091203090803030903030405060a0b0f130e1b0f04020a082d0708070e09150909 63
    0xa000c5842c1015202a035280c020200840c00c4d402002031402e00030006881301140c1e0340350051020880c0182040e018003d14500c4010202c3d0320310a5201c1c4500d1070700852800e44640c81c48480d10020b42000c8480b6004629040300054600000d0791401204105001c0001702d82d120b040d402d2000e07201560a2140b00001817000d400da9070f0702400300400024641c1d2021090014400615082d182c0340600a42260001c0082c1c0c40841d6121441c1015200c101410741030020f00351a0488054480e540105054003020041c451100d4010000318010b83c00f13002210300035100c000d81c000840d444c0b0500c0d240d0040101c8074400003410a0302d4542e5000054100004550600850307003801d000783da03154421000d1741c18100c0015807400e401920400d40056904501340860000d019108600107020300300d159285100391f1084000d40030380242155800307543c0001c0340c1880360000d081904c094654a0110f400028100741c01c2c145100c0301c0388a0b8910b010044c4802c121542444030044018000441078007036004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 596412877 1250 596411627 596411633
    0x37030209040b09010c09060903240c080702060c03060f0f010309080d0e100212130c0503070e0411041413110306070f021b0d03030b130606030b030c040209030a1e 71
    0x6032442203000d020340d60450f00e001d0300302508440d9648411010b000310f0303c009004499014404c8400e8030f5000081c0d61000104126443c000400303a40b045c00101c0c2081002540c0c0c40e03004800380d0203030245800f210f0054031042560300761030204850f01c0b0303084103101d2000f011600e040300d0a082d103070906040c006804d010544507c040d552081d45600382d42500d91342d40011501e401c1210100c142001441142007400640a1408010020b808170304880300941025041c4100c8000205c005d01008003200e60f100e036a04548a000070f03048034151501ca00001100078a403c15008401c089120150301d089207076580030a41c4001d0f10b0380300050b074003000d40b10a4003450f07840c204aa103000304107d031a900062404000000c3c68000581c00301401c2070b800c1c0b0f1001606849400c1280340070399050801007614060038003c40e08020741401c030b8240150501c0c00008500b90940d001e900a01c03016000c3c0c800f100c0000f02404142e1044114140e0143c1c440460719000c0f50700c0105401c411040c1882032000030381592 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 596414127 1250 596412877 596412889
    0xc0f02090c1309110315150418050612070317070b010b07052503150920030d0302070503090402090a0e01090e0606090f0f1503030703120b370302 64
    0x8a100800070000a404051030680000c1c9900070440c203441800407070040c4841010034040981901e080d2160701120141a0b5203007156a402052480724090302c56039100101c0e0090b5004000c0c0b504081d25050205500b824908180c10128298900411000380303581d03994410411400c130188441401402600300185c0c10400c0c10b80240094203509440d501942800c60400c91300e044001c210000090014540011004034082100e8004401d012204008130703a00b80500408000246a992881c21012213206001c20940031280706800b1034001c0c4e16030101c150202e1242082c040e12303d070300c10f005c0500c1928054000f005c1000300a03040300c1c3c0050743c0b13080c0c1c02c0c00d048083c1c000316840e6468414401031000104500b580c4440211011101401c191042a802201c0174201d0701d5241496000500d01c0c000411040100c4036000d03046a645141301d04004124500e140c4004c0fa20a08100b100485847c203103001c42000c210050303035012007044021100a40c22010118941504114070000015a07549 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 596415377 1250 596414127 596414131
    0x20d08190e010207020907030615121407020d020c0316171e03032409070509041506050a02010f0608030313031101020d09060c02010c05030c0a140c031306080405030a0c0f0209 77
    0xa40000d83c444684d0320400c00603200003060001091319000d010405004141c00c2e0301000c20070744c1040380c400d03110341a00310050601d240d0026151403485051104595000590800526240d42903440c4418604e0030907442d1100c58541c0c55416203c00024029008500b8440c6001070140e011604580c9004401074443e44841240d141140c201008000035002010315119088040481544401350600b00050b0b00d05006080403081001c045030041c0b6a403110390180d44c15005100040081c01e030f84100013031803030340a844410015401d00010445e02d80c030794040e10302500c000710084c508642e03513807400ea89041c8507001d090301088a0742b000780d50810020f05c010310b507840c0391241c04a5007010a0030143c4c19500300d2200c80e41160315221318141c12590041c19a0303000000800310590350110314508072155501c800314480440e0b000603d8282c4110f0000042905281021024140c960369080c1138800800407103000d0b00a420130000c2281c030911a0800c02840f600c15922030448810039000300d01d4ad03c4003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 596416627 1250 596415377 596415401
    0xf12230106020d080a02070201051c020d06090c1116060509130513020f0d050a0803190501120c050a0e010303031d010903030f0e0a080702040c110f07030201030c0503010303020d0819 80
    0x10078503412441035808130a596001c051080c06601e400c680da800244948503200c1103040103000c417912580c440f151038041302c81c0c412403820184011512000e426005007040d484000100310304608910b00004c2c04500c284c1f143c4903c601107041585412402c0e1082c1d4040b2004650100b600c0d61003042d0380c680f511503980641801c00c0b540d4060f01d16031050022602c0f0301b041c0c0f58403840c0f850800c3c000084001494800490f401080d090721b80d25841000c981c9a606040b0742d008080c10400033091003640030b902c401036580901ca017080034a6030b603024441d41c10224002d00300041041c80050010a001c1e400c0000d03408242c0b05907218480c001e010040c2180c007281001c80c0040d0f168280c55103030714030a000300c2d64040d05080240407101855521110346110f4184001c5c003941e20b800c0b004100c4e07402800105243c801c0700d0182c51201c2c0d03170300100707645601c0580070480c0400c0c50241441c4107544144c041e60305881e8160028099000c03c401c081c0d0b00f00303200800074100b4090103081d1182d0b403011030183d0310140f04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 596417877 1250 596416627 596416633
    0xa030c030c0f030b06010c210e0906100c0b061305151003020405060d150e13140309010f030509070503120d0b03010e0c01080702070302220c0f1223010602 68
    0x104524200d150001c0035406445004110302040c0b001c54100412076030405401d082440c200c851500c1c000448042070140101e22118208000c0001600540c0002d06c07c1407c6520082d141d8440303040003144000c00d40000c0000d08500d8004001a200c00541d98010400a0048000320407107940b59068031011101e1002480060000712020300300480742d000e000650717090641c1082e040801107284d500803000d5400306591550a0303a1340070b0032101c3c3e41c0000780c000d85c10038011500d44450380003150b00356200100c83e00c011344141c84405010101c180c85901105940751420040c3c4200110060900600b02105501500f5400142d955003042150107040c00d5040b036544460624544904070784800d4402c9000340d0401080308804800410000c003141c0d02400c01e0103258441e44022450b12030107400c002c0d000300c602040e020507000c50200b00d10780e88811040c2440001020081294490420000d050202d0040c200c3c02c00f015245070041c103420841044a078010b841da60b102404802c00a03072040016030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 596419127 1250 596417877 596417879
    0x30109120f0e100e0402040306020c0d020f030a1718251d06010f1e03060e060609130c020a05100c020d09081f0921030b0d08030615090a030c 62
    0x40e80200114204003810b0900b460345a00324004111601800c12241d0104041130b00030640d19565a41620041d43e0001421515505400c00c0d0300c0d03403801c0c03000403040584155420521464800001c840c902030090b9103d03c910340080c586641e03200000340c00e1000040440402600780d1074104030803044a0003514002850074400c0c100c03a0441c0b19560403044010341ca00182041301100f4103002a0040750a1070026564040b4603800c032000e96180d8001210080c4102111a24551541000c41aa141c0840c0d002003600c0e003800304101344c8110080c507900071901520444880d80a80d002050710101030060351885841c503030790a824190711100100301140d40d010038941b0581d0400603ca50f50200382007080360a0b08010b40c05584024840c5d9049840f524103441c1c50300003545400038100f850784002015110500041c1c1c4400b001c0898284d003001a2904400300c5076482c26100007103203640c01c09505407640d10f801c420b000011810401920b01c60b1400c20046100c1e480300c1030351030021402906641c01e05 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 596420377 1250 596419127 596419163
    0x90d02040e1b090c04061b030203130623120a090c0503100504060f020418020c160b1207050a090e150927010203040308060409110a08010212010b0a051215030109 71
    0xa942c003a0490b544e00e1410702c0284182d40e00314140c1c4003104201c180b81c54100001c1e260481c650300c686041c2c13400c0c503821410f00066840d08280e0311202c050078014401246d4500016100207030003070341d211000d440e010748042007018125500c1440441d01608200c1c090544900c040380c40c0401c244100e0081d1a600ca04000c2409102d100b01046001080c006501c0c0c40d207045240803c01c1d01c00c90944c0005030380060300c49090401000120000c0c11441c1c0c800c80e00316079a05440e84150804001206410210740014403070394820000ca1320341d442d803a107804050b2414102c1c61619040b006024283c9840d0300e07008011103a5a0043c003521540220541e4442100e1883e024241c1e0300321203500b80c219a0040c414400081e4001440c5a0f010b05d058800065601090410741c0301c1c0701c0e0f041c4060740c22030050180861408410b400034a8078400d031704403402c1541d988203440301c0144100c0c00301d080010030a00805010303c108501d03503500601c0d58016548400c0503903002078211503443c40220f80c010a007002c48480 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 596421627 1250 596420377 596420389
    0x14060111122a0601030812150d11030c090903030106030f14010b040609080601030809130f0906020d0606020304050a03060b011e0816030504050d0e030a06090c081908090d02040e1b 79
    0x20b04008a0041d00965140d60f661005d18050031042c071200c80c81d544005400e5000b180000800020010a250004c0641e03050401d407003041c46600c24003078021842040824180944024080c80071380e0015880c60f031030a10110300901080070103038802038071540301e044410b0320380138030902070090011201d6595280103000740501003550712060103034010b0320040001c83c44840659880d050140c0700b038000070142060b640003c1c907440ba5030040c44c40c1360100580902c0f60680c0981680168000108812522110240d03a00e00807885500da02ca1008031007400000c00315006a20211010304246101910300c0d220710000f080c011049100294088040005075140b001007a000b90040b030404100794207154440c03507260280620207009004a003801c01c42107407000c01c4060750700790b0016010805029103140c00d00c0d1a00184c800d420241c0700381362080001c0b05240405001440d403020710289004c0c0700c282407009504001c10141d0780f00746e442c0c412007061351091041c0b40644942c0c003031042c0066140340c10001 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 596422877 1250 596421627 596421697
    0x604150b030f24090d020604031d0306190e030f1c0b0d0b0403030c140702040e031309050105091f0909050a0b070513230402030a060302150a02010e011406011112 71
    0xc41d50081c110b045c0f14640126000c0c2d00180c06d4a4074004c0c62582c0218540b82000c8100309580510031001080040d00e1f610b941070031040620311081c40911440300741702e0782e203005076180c0040d2107100b00102462400a001c01c80b802c4011540c010400c2c810003c00291038090044040d01c0201c03980080008059040c41004c070400c1c0d9500300743d0307000305030300310420013600554100902640d03640d4107612224904000741d40c1031180e02d8446081c56030301c8a010b807003d08020b00c03c0707901030401074000c0303481642c640210000400d808403851845d586046203030300107410385800c2924540110380c0c180c804504030907031b414810741c1161212a03a40e000c03605924a503419030f5102d012201405001c1409040a0805000c5841d80407900541c4035107038080da490081100d036000035030000c8401181010790034080041c101018060b0020001c0c1c800c00c8005a00b40c070540305210790b9080c407100c005900d80d0f010740031401804a0700402c4034014103a6944031540c550003948490341c800030070075010403251544210b00d1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 596424127 1250 596422877 596422891
    0x140d06110f0304050f15071d03011b02010b0a061e171e06030d090b09060d0606090f0e01080a0807080c0610080d18061110050f0601110604150b030f24 66
    0x804c6e9074980020b0850381200140c4420104840f5000b01c030b0503540c4009400c98010f00c000c00808c14084a400202100d0640400b00c02c055405c1c2032030704009140041c18403044510640701c4566941001401c5218003406d00b4802051110f82c8101c8203071442800403207072281480002600c170310114500d000407003241c0100107a01c01d504c564198901d541d44a01c030b07401150002810141c4a091200003c2c05034002d20038483c582c1450154001650b940c07240e0703040100e0b0f03805484842c0d000c0e1640307039050f6104024000d282c0c03680e02a412007000a142c48006088190140d40c546040069418000d410008151441500c01074651800d200164003440819503007182c90074040007258030705440f5008515980f103a20180807603058940c182010500c1100390085801c20304002c640340a10b00e1404000c0140d034494000b0780756035180965200c1c00907041c5d008a40064401031003111105001c0d0140c0301e4154500c1d054015007400d08072070780041200880e0303465544d20421030324494800c480b00990000301070b1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 596425377 1250 596424127 596424133
    0x6061d060102150601090308031f0b0a0e0d06020d02030901060807060e0a090c0903050a051507050a0804020d030302160b190204031e081c0c03060e01140d06110f0304050f 75
    0x4404940c0e00001e280503e000350441000703860780e4000050764880f2041c0e0026200c2840001005868281001c05070050410304800c52100303920740785009914080d00042d400403c808100d40c0b8510300d4a813104848682c0b0401c0094504030400804c807040e82c0040d512001c041e911004d00f07200850341400560040c00701441c1c803103051030190700000c804a56603c41c0c4c00003d9500d540c021050b40c03107041c4403030203550820202d55202c0414602242da03842c42c4510301003115444d10100d50b03020310500c01c0320301c501c4540d41c40a910362540d03020401100340c900012400d1560821614080d80780105088200700c0c01840c400c101c500d015a41c034921034081c030704030102e40d9104000a0000402d4110284071032100981030381001c0c00349140096036407007070200c0e400010b8419000c40450020f160071005880240356001d000c800d540e40318000d007112003030180109010b11066102401c0c18402a54030b8514024100801d8a0b60002510074156004100c9a501400300208200901004100318200360300d2507401 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 596426627 1250 596425377 596425381
    0x6090b0f19030b0411030f0d03050615030403050c0a23060a0e0303011a0d0212180a150b041107110108130c030f08190203032a0403061104030f06061d 66
    0x1401d000241c0c03400000c00908803030000c5070074803210500c003001d4607201500f20f80c04820010401541c2e00012402000041e0911000511318100005600b0b0221144040241140c903159000e407590740140010036050b20440385a4400b04441e1484d990103200e21600c5901c02c5288000d410341851b13001005100000c1c11702e2034030f8201c1240081103904584c0c080154000c030840100020040c1d2150b618070441c0e441c0003050081040b01c2c2c03204528020b2141c00c0c0c0c244034031502c2000c00c0d41c07110506c84024240c0c0d40c11810700319032011513421041e05450014000140741303c0c54224101ea50700813075001e03200c0c208171546000185d604203001c5500030313030301c18850f030034035109a90303000c000d07413034030700004001c1c1e01030001003030030801050240c85620301d048100400d15602000c0095903a002111203110f09108860149448035074529a070003000702d4191020300e010305540301c240c05003040566126400c1001c10002002c12503070341c045e20707620b0f02c40c1c040451100c0c54070b11300c55030910130361800d1002d400001d81 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 596427877 1250 596426627 596426659
    0x20a0905120a02010e03070b070c0e09061320030f0106060305100f060c03050918090c040c1b291e150108041e06091e0c0b0c010f06090b0f 61
    0xb04180c10640c2468112070410103140400c1c20034190383d00050613480040b514400300b028410416040d1403e4003ca140b5954a280c403080e6130316001d50340c082150840508020100e01e42040d259804107039600080171040461010030b1074004100340042e00e0765074428091202d01e5150243c079803c0010212060b07031315824894960300f100410b00c035180a00070300a4030041094040d40a4881c4004001d250074614800103010350701c004012250b24505010700c041403038541c0b51900c52262000c03a40d554413151a40503881006c0004000c6909640c0f489507401c0a00140c032034800c0d9221300c6103200041c2495420f104410351901d4000084110707110b07200204106003020980201c0400000c00d2030b02e0050b41e01c560400688404001503281c1034420308800c500213108840c3c00011aa521440c400b4885403549640402031440c03002c030061401501200030041d5034070b007c0c080d0082f9400c100000402003880503201c0221003441d44441103e03034aa140c03039506490901140d01c44920140e9504140c03480c010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 596429127 1250 596427877 596427883
    0x130f1406030a050a0b06180103060e13020904021c200108010303140a0306091104140d020306280626060106020c011404030605100f090b09071b0213020a090512 70
    0xd1904402c581d58200094040c541c0c0c1d0003000180202038103560f034403c0d41d0300c13581440c070700d802241d81d000c02d06007180000c0c881e0b000300c1d405d8403609401082e4000c07290564208a1800e0700a0000d176032105100303403190039161200c2e442e0009503202c0d09070724001d0b84101241000d03080e4240d64050610006000400c00320750420102ea003d40d807000041640c5001d440415030060400c1d42044a0391441c0048540c201c0c2251001001910903642d0b4040500e5642410451045150307503000390940c21450124560022560300640044518010036101c604c0300e100440480f141c540c80815019581c10504403070030055650782c80b144d1000c102404070b0750305141010b540c2c1c00d18122918100074a04800c0c203003008994094a01a590141c0140070f10b080124560b5100c14840c05401d04a138402c050000c0c08078503a06c00c203240e41602401205076503517004000e9079004004440c10f80524940d49480005030340e003811041462113801001a162114001c00500310316103900024020805034902c1080c3c1c030000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 596430377 1250 596429127 596429131
    0x32901030f0f170901031104050609090403090801020d02031501110c091e0a061502060106020a15091a040c08010e03120903040e01080109030216210305040803130f140603 75
    0x500c0c440c6004660300d404035550400e40b1010302100a8050700250a100c25402085604026a81400090154100c0180d20722441c40342c2588440c1c10841803819007458154242d100d0300a04026407199920300b00c082c2664070000c10180103540c00001c202d411050703680e007140c4550080ca04078500c8008078207066a03031154001e10b00d00c80c03071a110000e1280071749600810000c0c0c0f402d10f08082ca134100300c030141c0d02800f454001c50340b5a280d5542d01c0314aa610024005048540c0c55000f405050703d1a15080082080142c50060540d110000314001c01e180034007220145c0c0e21140860003d00d414180b480141c1e4280d048450303d40d040400c64103014400000703071554100307421080d034a5034450140c020700d544900c1d032140b02c40590038030001a4452042d80250850f0b4000d0b004e0390540c020820080342d59007003a0203a440c0701042d000a00400038049040d81e0340182c0300b410043d2906403a07042003480c5401a001c0002c00042c0e9450600400c1e0000900d4401021800380f110624424640001d100c1c0c000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 596431627 1250 596430377 596430383
    0x2a14070b04031d040606090e1b031302150c0606150906090927100c0305061309050f032a030306010f0804050111040923041115130f03290103 62
    0x140081c40344402403040c407111a030f081c00a00811611b952440050f04041d9903100301c08000031f01000103440c5d04860f1060011a0004031002459680d54200070450009a90f07016a00454900d8224207240d2001004100e5001068000e0141d850280d04003d8003040300c1e107580e0f0441000340020390440d240d14068a090450407221890300d581c4030f50789200b000401d10080495241c1c61603c010b040b4501140c03089844914501c144248a1088000c0d82030703c900fa940c00d904840041210501580c0c5580408496480b54040e681d801a44081d02031070b58004408041d541021840b100c54054012401c00c000060100c02075411468041c001034081100342047d1b009115081001408100e0294003001c3e800441010381a03c4079107c88064004082d079a0841c14906407054881c1041c142140d481840b0b1303a07004c00c9110f11300f40400103100e2180092400c118800006220064061060a1090020b400a4104100060324504120540d004902e410311741820b4011b100620031480f110b40181900d370 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 596432877 1250 596431627 596431637
    0x307140402090d062d06030201020a030804030c05011103010609060905210703082701020105100b0f0d1802010221040e181c0201150602100c032a14070b0403 69
    0x112500c040fa181c0804010024025442c006a1004420300c0d541421031610f107040003080b0520914583e201110903d0001030b0241e07001c000c03070790000307803243c00d0750341c0d00ca0f01c02d1400381043c01d110307a56203094902020300d1200c203c1011005101c3c1d203a005801400404603131a0210f00710f407138000401d94400c0c450f4074008200600e4015113005520802c0030b00001c660140c80740343e0b1075071001b5143c01c04800c814040642200d60055070000c030362050040e11f00440c1c8641c00055890b240040d21029507001d6012280c01c1d5005010f1200144070600c222402805042110420065248002410003c000090b5900040d0049803000700c80e100400340c50644180d040394035803030348910300e161070008025000f040c0140f0982558224520b418944c58003000c20680080c0041503104003045c1001d003990080c40c005034001c03000c200c44980540c101401905080c10f0020701c41d83e0710b00c10600200300300036081c51200d488040d020b0081c0d50040544003816200c540c241d00344074440d543c007514484040c1000c1c04100b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 596434127 1250 596432877 596432887
    0x7020a18060f0f030201020c090603160806090601090203130809030705060d0e0d030204060507200a030b09060901020316030b0f04021326071e080a060e0c0307140402 73
    0x1489052111014112103039a2040560204012101030102800303004015651000000358660707805000c242030b41e60580141280514038010f2282840c0c005203120707818404c0010f1022091520f801900151003e50301510382031902c2c050451624906a02030007509104204201d2683d4481441d48505a4001c640a548040003c0024940030082c0c10166100c80c0005220740300170113903070050300700c075900d20b09807004655001d005400300d015503c9500c02042d400c01c24800000c12129008a5601681c074440e44548200c41c042540ca0075a500111500c99a8100303000c0405c508001c4980d119100100039072a5241140c002c1826a080303001440525886a43d5504250340d0813460214406002d402107413140b8007958081e40c01103181c85103516a401e00040c9504444070700300c00420040d1140010700005280c61450a003909408040302e82c034100424000c201c00106010b40c07020740e40940004185001c40340b80301d6040140d80b40c2031a11139480524200606800700c80141a682003c50300103880d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 596435377 1250 596434127 596434129
    0x516080301290721052701030b030a0506060103020c01021c0203250e2106090c0a050105040b090910030506040501020d060e190c0e0a0e070e010503130605220b0402010e04020414060702 81
    0xe0103a103646004000942c43c03001030303400b000006c0f0095030130241e03024881001550701740b5496240d00c100c0500550840400103010754041e4000740781042000000500c0c10202136041010200c2d0f01040400aa400001b480701040c801c850022280c49450002c07000d000144034060301000d048040300c2e01400720051225002d51304045a020300301c071030307070150b0b0380501e0038218081d1908819040b0610078000300e0400300c4d0700d501c83c10a0320240c60410700c40b075185c41c14001c02c1051081c4028100d021941c461070010000940070b11005000328402c00000d6121a01c01103000e0654030349801c80c0300d101c0d010000f000300c0030042980c03280c03107801c2d821400510441152411a01007960590131500b1064403900050140c0305002c500c0d1068010360350745004650035000450b01c5110541d4481140c14816101101148440c0c1c0545e80014001403880602600c1d0550100150007461047e030724103194004000c155608405103079000351003103070110328203801d1440d09400c4944600003a80145030204441c030031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 596436627 1250 596435377 596435387
    0xf05060f030f0705120708010e01090612140106080a03110601060f081603150609091505061b150f040501110c210c061f1a04060516080301290721 64
    0x5c502180000b180062501c0400507019950070311412000d1610f000c000205c0039800d00c80c0c0e1050364800307460f00d010f211041d00e4a8403813080782c1d48003c10a550342e20b00000d0303070002000703018001842030721f0f002600102440b040342800416481b00c001d0264400400c403019a1014040d98400851401c044501c3d6604004500810030158200c4060992080105119800101440441d06603241c140f0004c5085502c00d640c40c07049105854104034207000c4c0e40c00103d030b159500403198490760111510b20f0090a408040d15100795070138400e00c00541c0502040c40000c0c05070031000d443e803500701851f10b20308801d59662032602216202c404c82e52498224020703c5003108540c00200c02c20300301c038107a0a2060442070580c4d41c802d8082a50f000c1d02c038001540402c80b6000c078044294081c01076041502e403244c169556840300d211441081032010150700000c2144002e54040c01e410764a40070100c811900360807415a112560100c941c2c424031008000980b082c29086444982800c61008030500d0501551 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 596437877 1250 596436627 596436637
    0x30705031003021c060f15050907140a050903010e1609020d0e3307090b0a050c0a06020c010c090e01050d031806031a01030c0206010509060a09020708040f05060f030f0705 75
    0x2500c50200440c11300c081d8409a40b1482c10b9000c0d00080100090700303a103000c116040300600c6983c2d031208803002c1040c1d14100b00000d504c04102d0a0444013044104c00400e829802189868040380000c120b040c0141400d220b500301c0c1c0728050380144802c41c1042e03d0480e4541c903e20071421400d80000701c640c0c0c51001508070100e1303440020201c4604040c004907105500d1000f0031281c0b414644603403140c064003640445180154402c2d12030200c03180c00c00c41500e03000e0344003101c0c4006001040056019251041047d41b210501843c001616007400801007420364980805080400040500c140100c0c4036164000741158011699100b00011034035080d20308040c01d54501d00c8421002d0700001d00503405410078800000594980c1442a03180300041d000c03103040541060040c3e0080006000320b04000c80080d801c80c20007443c100c1142e42e21203051050707030702088040320030540100c0e0130816010002c040d00040c1200310707401800e00412480c0800c039404020300ea00401140f08000c03074011030154007110 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 596439127 1250 596437877 596437879
    0x109020a0e0a0b0c06060312070f030c050a0c030b0907081b0f12210a0e010807021c020102040f060c0803040605040305070c060221031b0f251e020603070503100302 72
    0x342c409945101c030380040d401c83d40030071072103010f0032002440c0c078034010800c080601070310200305041a02c10307101c280d09984030381c074118280216100043c010800c108045241d15100e1b60140c81d9080c02c6103041300c141400504030702880e80c45040d0600c030002000c2080100d2001c10f5140c0140c100554001400301640000c901d9044440030500d03040740c96010400c0c005080f4809154129070b0b208000c0d080c5244a10010348000a60615035a0b0081d807107450160b0b0040c0640c41150829410300705c0444035500010400310240c0c0d40000c040061f590181c1240703008203480e05002a4240d51034135104103900c00100004d080691304c80009003003500601c103075100150440348081c2091f84a0030080d690301103048084030308801800340c0b406001d46100071248a0300f00c100400c0080d5102c1c840c40b182030340003840d91103540c9109000c00c50480700d6a18004151900180070500003c0007401c003485007142a40e0030308503a00c0d0000d01d62000d601d8420840307400c03010520380250399a0700c03101c43c03203c0c49020360002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 596440377 1250 596439127 596439139
    0x60303050a082a0904240f0e040308161e03050919080a0309030e100918050408040608150a030302060709090209090f060a081501170c090109020a0e 65
    0x4018554040d02404032040701d515052465200d20302c205403810200c42d2004001140c0709202c0c044070a0f80405815a001c0180010841e0103401c0c0100b04054040b401104001c08203002c1000a031240d582035000600c14481001722900701360b20700829424004140380380c81c1502003a0030030900c6c450364240062626550001d000d8000200c0020085d14040d56079448901c01ca04141d0384840320000700385440b5071701540d8145400c1400000794040c1c0080c0c03009509200480002d601180c0310040c48090061183e540c0034a42c0c1e0034030004000d410011000c07103140705d140100b0400003407124403c48081d2a0107040c54000c4e50f459030040110810b000140e5900710009540c0001019000501e0354003070361150701e4280205490f040c0d018103d0142c02281c1d5440a04c0c900030450403210040d643d508040701030710301e00d602603c1d200c8032481d10101c80b01020b0140c100100401440100c0000320103040000700140c038906200000003808110f06004d9464425800901145024000c01c0780c0a0700440280c12 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 596441627 1250 596440377 596440379
    0x7080c1c1e0807020a0209070c06061503050708150405060a120506070813020102060103110402070b0903040302030c0609011d010207080d02070503010b0114040b0906041d040515150d0501060906 85
    0x8020700d44455501d1850a2049001480848038095060701c0e114030b80316802004c10551607000c0000040707000d05540103000c0d200100d0f80c08143d83c3e01410003d8450b0159041d248940814020212030000f0042030403c84d142d81032160b083c2d0040300314201c0b07030021a03003c611925100002280a1101e9014126070000140c0c054100000070406a210f820580c40d80103c6640f900300c286445030800200900680040c00180000398408807000c0a5040140006080810079503600308902d00950ba940070507800440d040003107240400081078040c000351012820548583c0029054403040035641d03c000c1c8200285e0a01d41e403081080d4002000d1032400c507440f441031084065101c060318003d031030003542405c90804103035002d4611900020020617940389854a01040054690000d070400d60b8031140c00c11000401201001c012441025044400c035400e041030300d800b1345010805860100c0c15a09181049407049445d0aa2250040192000260700003503140650040215030040c42a00780b4240c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 596442877 1250 596441627 596441683
    0x106091b0221180616050d02030c031b07120312060f0b071202150a1409010218013002180906240d050c03010e010905010509040809010c0b0103141e0307080c 69
    0xa22000482d0103102540c0b0f90b0b444192049880b4070411b41c02b01d142ea48208a20b42034442d9054030355201c13041450aa50559407200034000c1041018281507000034a612840840c3c80310510039200200326001c6c607603115500c0d1905409690080c1500980f407418641c9007922254000d02880704180034130701c015041850000c0100c4001c1c0003060900d04400d0b0704000013071a4207030510031200ca04000502e002441b10981c030045542f4001403004141c6e00e81d12a9070315000040164548540740081c0a0260b241c0030b01440d402c000c03600f10b4503000c0c403c2103040180302250702c40b8420007003402490240d100c140c1d10094190107c901c60302d4070621226240c4020042d2600320403001d141a26040c02181060b41d07692268002510001e004480e84441301101003000504003000400301424181004d0b642d104031602d6140d1400c400f64402c0d2900001c8500c114481c40e8103010441c0e00c50a16041000150383e80c002103541c0e801a00d000400440002800c40c6000004000b280c2c1d090311050741800c04035003414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 596444127 1250 596442877 596442907
    0x7140702010c0b10170105221a1905090307030903030e04020c060406050103020102060f070906051e0c0105010f0909080403060b030307171306030c171005030106091b02211806 77
    0x885400c64144503502c0110740c000040c0a203502a1402c00c082c0b0038030214a030680da4080c4d010384411142c4407001c0d8400701100d502185a582b04500c035040c064440c0e4a40350519041e140e004083c201203820410034400002c0e00b082075041920b401d0300e0011450081d181c0030030000d1040700030801036446010204030410406405ca6416a4400e03402d03910540c9a00100b420001c400b5596880402c0d0345d0300c3c0c14000e49200b0405072604c040c000e02c40f082c680803c5031403c0d0040c0c1c072030031403024581d464000620074140f02c00e850300c0080800080400030566646c485075034500079408010710301d42d03d800b42c0490581e420002d03501820b42002c107060382440d43c1264a6420b510030501f1031001540340e00300240e42e6020707108548070145240c031001500000510507001402d0000d1565881c0c4602880c086082d841c24401c042c090540c400d40010420400e0382c4031040294503481584c1154030407000201800100855400b0360030540c1c99142d10b8505025440d50b141040903c9070350042c401140f2080811010 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 596445377 1250 596444127 596444129
    0x20408010f0c030e101a09010603091703090c06131a07031107060509040504030225050a14010c031b08030717240f01030b06040803040e0f07140702010c0b10 69
    0x291a0421a8102c249000d4050320a40b84001105800c00d841020a070141900401910f61130030420502000101c400035060765020303000000000d0380e80301e40b00e081001800c0c0010240307a0f80d081e41811480c1a03800d0559408040700d115010f404041003407465990849031050141580e001001510980c82c0782c04081d5404c01c0f06c00345c00007001c0b00d88400c02100045282d0f403c0d20b82568441b0718103020b50092001400c0007810840031072003840d00014030358240301e02480c101d65440c0b01c000f12051901d020005061941c0c0c000000ba501c11220080c03460ba00492111600e03075241c1010986070040e1b410642802a40c44000b41c68540000b0400c003026a01c03200384a88003904100310072085d2100a02d015403144440008281301c0c80c04400003d0500c0e141d080d40c401c1400c1450081540d4110b607001c03486540056000b03908941c00460140720808590808660010700700c4403240b07903840c210350001c01c425040100c0a0444400151403425a44658032428455410035103507441810301c1d1030841100015 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 596446627 1250 596445377 596445401
    0x1060206330d050a031107060302120112020d0606060824100c0c080d020319080624090402280c0302060c0a03020f03180c04290612090c030601212402040801 69
    0x4598001c00c2231402031080c0c954401e2941041d11590307090003107050300c070080031800341da1018100305910000b40c040e001e042d0240001ea03444100e00d0800044202180340d2540e80c0c85011151450840c2c1c454884403a8425500f1040c64403413103210103814420002c40290b04000b40d0343c0510603180c00309540010040058448606050300d11503455082200d420300b045e602c0a40c01040b041d02400410101060b06161040f071f0310b5024504426200054105d81c0403802c2c030b1400c3c1c80c811003d109412603503d44040300910700d041c211503400440e07030003c1d01c0f804010090400c10001040a11145100e54180e0707002c40c0703500709195a44d040420b500420009450a00e1956204507441c10140c0d0030a03029001807034100c012a0000c0c140e10004100c803100a51403119017050f07050021b000180304001400c4d02a9090802a0aa41042c40203250406074142c010101030000d01413500030440c2222031a070383c4260421300707128065000004408045180e06102c01140b40089804a5003030b40c190311070280c000e5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 596447877 1250 596446627 596446633
    0x607090b030903030612070f06090302120307150222080604150b030309010e18130b150105030601031823060109061d0c0904050c0301060206330d050a0311 68
    0x15550140c09410312040703031003800750380050002c92114107090321012002d0700040c0c2600d03030044e12008405181c10aa52118000440301d040030800d6050480d00903c002c8480c0000d11314010355170703ca84100308038a03004401c131150300241400340c0b9000803003201d039083c0a40003e143c803555140320603603991406960030b85000c2001e881c0d903520701813a0f20980b42c100e907000d009141003208130300054580e1001c0c0000355030808900704164901c06a403250341e900ca80f844818002c03925103603003005555050000d0203456404101000c0300c58030381e0001c050f00d6108c882440c02060803512030b054012028a1500000d0070280001e040300c0007402d0100c1210301002c410703c110b030150f82c0d0360a602015113845109100a0640c44020003041480902485901841113280c49180498000109085a50486100d5134800c0c1c040018445164140540e6400c10302400d1010120090b0140012004802403505054040041900502d0751a070b504000011a0420b0a80310fa144490a026220103400c2440a40ca40 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 596449127 1250 596447877 596447879
    0x5090d0c030516080606010c060917071415010e04060b03060a05061e090f090712030c0201030f02090a0e0907081203060109051c060209060c100606090f121101050f0c060709 76
    0x10a0f011140c0f000c860f1441d008102948030040152440c0d405503070191101c5496040050105000c5012899061300c5803001907a90921070514501d82c1500341107042ea036410a450090084421400603410f490005501c958151034518007030000b4003030f1108454041c000c00b0108981c10030103500845c401c3e04151b484001c039001d4003e11003103162180301101d50240c00000481c1e540c10085408560000c2d284044810260703d415940c022641001d02c11800550404026821135074180900194040d44600079820200c13010009030050f07100e0f015508101e100800000c0c0d00010410540c8014003031131056802105030304240d0095076204403070244c0032070010b5100096a09103800740c0ca103017080155001100d100070f640d036200617500c01c01039640d000e402801032140000082c003080840301c00e59100020f02c1071500c200a045002e2a40c000081c0b01040340082102c0c0c0107483c4149480b56120745181c0100c01302800580b182d019001800c54692000328105801e0900040e03030502a100540b2110041 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 596450377 1250 596449127 596449153
    0xb031b09090d050f030403110f1609020405130c1214041b08030d0507031b0203070c05060406050f0904060924120c23030d03200403030804021005090d0c0305 69
    0x642c1c00d00000c0e200052003040052180c480c2000a9038106100746000d001a00f020f0200f03900d015164000d007166078210703514581c2c035010140248002401031100c00e50500e8036100010700004808004115881d0320350b03414545451150010003085100d26100b0000c0b8601003000d0400b00c4070031201102c0aa00801d100e2008800404180e801c807070785007009528059050744110042c040180110040c9a250251034140b01140f01034103070340d15038a6009603254043e50920448154444d03110350b000368401c01080c0490b0b64400200c40b200442015501d55462200012400800050f03124845103460088000000505920341100d140075907040c5454141d1580406a51082c0e8280d004200702d028800400c11390400c4e015808142c200c28407050500c4020801290070032060016102c0080c0d40c80c01d17440d000c01e401d180001c40b10b60640500700e080c0750070341d40e01519851000e0b0000e031084141c580b003a19a944038034201c560358540a40031a003280020320304005190054007007112180200243c11080c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 596451627 1250 596450377 596450383
    0x20a1112070318090204170105070309151e0603061b0207050913020d14010c0224070810090212070e0f0a05010503060303090406030521030108100f0b031b0909 70
    0x10024481412515116182d0741c2551811030341200f210b60394803042400102071310302e031001c0e00c0144881d80d4040e40f0800d0b030006640c00c54600a090109040ca400280f0001c030f8400c084034044107104220026135180f078800907104003142e010b00410220b0416102008011003030b04405003404501440403111042d080c3c003641c40301100e0050782e030003009100c0011408816a2250346803180081c11a443d60b00d441c5e1034544a414440f4521603c0d030791036801100c40d29034104040c10b42c00710f8911800c88d048841c1c0f2561080c40030051300640c20841018045500c5500720301c909802480c00d10400c6585194a600c2d41080c0881100c6150214100350030340c1c0c495040c01409600c80300d000030003020180b801e000c015555a0409040d00e5094402440000c3d0b03542c440f40300300c1d40654090f000602d0300510450702800b40d02d5220100c05000c0105000410440400140c6400e41d0442c0d14404202c010040041c0700007068000e0341561b0500c102e900c0680280b00103400c41400d1901030320400300c00d9444084c00c82d9 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 596452877 1250 596451627 596451643
    0x1807060f08070c020a03080a0c02031b0d08030604180c0905280c1b0c150309020a06081306060b03090d030c0c11120102040803040914041e0201110102030a020a11 71
    0x3020401001c00118000c1c400d1940b0448140700410199241ea20398940c2d03402c40d048240c400d00070030700381d058a00a5140812043c1911406452540c0032241c074140401c2d809150114003c3c4000300100100350a55260b03000191100b86059981d560b06c59103040034508080039100340348001e80781078082200780d084004031022484104415007154081541e10600401d1a00ba10b0000c00068407070105070003000c035040956050081018810341810101080e2601d034160040e00281480e00c0c0c280e10040c0c45448080303040b0345540c1040c040950700d00c4260710b401c240105c8000c003544d14028011500c601034402840c040c00c8190708452401d692000282c00b180c0d120040c41020445441c0800d0001d00c140140350030301180900103034142495186828266001030b005038049070404103082c001c0000c50301c100224022460703000b1985040648034280c0ca07a11240c0d2000c211440d01015000356401000580000e62000008541d82c0c074080c203081c0000d40100c4d17a0000080c2c0710f0607184e44466400900c1c14 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 596454127 1250 596452877 596452907
    0x15051b03010302090405010f1b02240c0d18080d051b0f090607151e150e0702010e06091b060f0d050907031b0303031d060c0a05070209180706 62
    0x14510703425a000c004c844440200200c4e01d80d92035582d982c01444090148100040c010a4050040000064081d080c0344000300c3c50710f40c04287c40c688804000f0305221031508040361014540e51075451901520180101e4150451142d14006444042000c1c9a00521000381161410403460316000d242181c0c21101d1905014501c0041c050186040d900d40020007900c0c80062076140382c9005a940c01c001000a03241103085565030340001c01c1940c1d00b07110006070586618004001360f03480090390003136100480c01070132040c0c1c00c1c6000107070600e17000f50300c58282503903900200c0c0c00e64684406450364403200c050b034008450740c050310402c201e810504140e40a406c0f030070598074107102c1d0180d0400010031006090301e034070784140c20f40000480c1c2c1100e025464220402d200c02162415420045d09403100b0303800340071820401d0542114507107008a0304c650003164910545a65140c4079504403003900503a1400707540039a14500340729288504010a20207180d0080945012aa6a010603106406004030b85 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 596455377 1250 596454127 596454181
    0x5091f0e0402090d1505041103240a180609050c15030f040305040e01090509061e0a09111c02030d0509010233070509130e03070807050c09041505 64
    0x2030903490150050548010040c1803d100c4034915280c80005000030f43d01006503aa9031010720060024019040360240e00590042019141d01d0b03010f804007660005210f03803480e001d000850000b95194000c00c814004240c620400c841c0307903051850041c0076404d000c840a00c42d43e40b0b02c2015050581e410029010001089401c640e10f081a0300a070090050044080080800c8041480c40d4400c2c000380c060084100009010f140c4100071520b400303000740030b00000c501e020000d0400504030031440c0d0b600110110380411440e44528081d902e807c600101e0b00c6e0702031080040f1161580100b103000c00228000c40032940480742410301a1054442c00c90b0f00c0b030060f089078640c00c020350081800c078840d8444006011010408248949103140020b41c0e002000803c002030703a807514035001c0c0e90021014880d03c0c0401264074000042c541e02d1088603401014110b010a680040c05024460000030440184c4110114501464001441d002038a00328080380c4c940400315218014050744904003c040580c4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 596456627 1250 596455377 596455397
    0x50a0614060c010e0d020604050607020a08030a18060c02010e070f05090127050a0c080601080108071e03080304030e120607050304080906090d08131a04140109090c05091f 75
    0x34824035030b1110068094941d200c40a00c900d20004000780b0b88a2034059000c2e0589003890320b8420300b008000780c590005c6600410880c000310311013804482e001803540c50b001039140c50200610703554400101010745000d10700180c0d03d20154064000008084614003500c0d8040c5e00c4107109888a00c10b405015040f00455005011050020003100000301100e40454241d03070900040f4410303240d044a030380c4105501d482c01c1d80c1340c0030741001e40d845d0010824200b001096040210f0340355903101500c1001410500306400d00c01c0c011710b092001000d107801100c0d0650b40e180c103040107001440004a2a4040d80e000c011305060034102040b503501070015580c80c2481d40d02d440d180d0f540141c2000502581c044001c0200304c82c56568600c10001080c07180720041e441d00d98482c0c031604000c0c9160301914581400088055041a080085400b501d0002d0611141984041d00484120407540c1082005a180600e0000420740000140c40749100c2143e452140541c0c54680122140c00d192003c0701103094000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 596457877 1250 596456627 596456629
    0x1204081005041e030203040314070f05011e0f05040906030c0f120305090123120609070e0916030e030d06080d17060d060b150d0b0907021e0705060f0d050a0614 70
    0x45001c3c803134002e20481b070405480b5150025859203261940103140e001440802c2400c0102413034034000c0c5002d0900940c2106120030b070101183c00d4458000802c1895441184030380c0c0a030017a41c0140a4070202048a41d4491501c02c90700f4081d8080c40840c41032411001a200801c0715141c84150344c1640c1d0b02c0d0a201c1c2000041d5031748500b044944403144081280c001d80c0c0c100d50f502400011800130803119480c20b20720280000841f001e0041c00411070380401c00b170380540b0f80000300c3d40c000c070300c1482d0b800b003414a44000f10000c10808080100764040014041c1a214440e00102d055664103025180e000810300701c240c41801030540e040c1801034000e40001c00d6842c2190005021502621012900e41800d0001070188801401c00c5802c0d1030f40411190f52498041c03280b52001e00c0c0550380480c90381090390780a0350320259803840b460000f15140307440e04440028046c3d50002c3c000900b03100c1d200c448010026126410119035601070b1490140007400301d9100707004404c00c4403c0c1644001000700060 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 596459127 1250 596457877 596457923
    0x51e130507050415020a030f1812061d0a05060a1a01031a030304060507061116020d050c0a0b03070807081614090d0602091504150e12120408100504 65
    0x500001c00d0101c1880000b41c1443d004074809100400c0340d02a0200f1080c2d490058041421400d410b410000800600380000303503011400c100382c512002c00c1d8806000f135450100c020b045108040d07810500801441e4014034130000b10350103c107107d030080e103200b507540c0d0010104a89042010b803403420a160018042940641c0c4200b040f50454202c6c0e608224445010900e1a4803a034000e0001400000c1c14406110103441422002143c0007900d41c035200e002541101c2960700000040d100b4909a1090010803c0811550480b8000a85a100d040359038004501d035030742003105c1d49000300f0103141c0080d41141c46100118410417103030400e00b140660100044410b840c1c507003444058601d0800042c80160ba614420700d001920925015960b5030070311080c01542c1d0b02502c00e40501d00c0d001e000c1404040c0340400c0e10544401035207850507000d04080002480c0c03858001e145605409100c46050340011101b005009030b071211021501d0911040541034100c55048030702804190842c0e1011140000309 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 596460377 1250 596459127 596459131
    0x1121104030521030741030a0e0a0b011a040e0a0212060603060d030e031e07060e09040503040315020f0a030b040605010f02030f0a21060501030606030c05180310090804051e1305 78
    0x5491418001c05e580d03008031b803110b00c1d8009000c8500300040304000c122284c50088201e80b40500010703103041030007503440a0b8002c2060168503800c4031202c0c6903102d90289070050750000c0800b41140446420704604030741c0254421901c040107014400b00040345030070080101d9010301d8014204c4070704421141c42c00c485190480700700c4c42e810b00400c00000852600300005080300c00101c40500b1034140f92040c090007500fa031b00c1d00786006402c050b04001c045a4044203440c07c582d080030707401c84400e0020602c81d000740321f1124414084030000ca030510200394503a2162b41320046c29030b420054a0345410054a56201d00d140300c0e00103034400c111000d24912104098403800810741007408c80f2180f8011094a001d284520880c0100e6582408200d07a603410b0107220024810780c01c042000d6580c200004000703120304000e442c00c9418113001650702d80c40400c0b0b0b000c01b88024000c00c000302426460040716581c81071160910452510750a1444c031514038100043c0a400101400d9103448690a010042c2c840 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 596461627 1250 596460377 596460437
    0x605150f030403084201020a1502031f0806061e0a06050702040f0501030b0907060503010b0714120f130b0313021c1502270f011211040305210307 64
    0x810420211031074030007100e817105401410651907552044c0c004040718580300c1882d05d81103500c1085900003150b00160541e56102d550400907035a507032030100016800002901c905068610711000007958400814010300403801150012008150241205c05500280c0300c80c640c486910a003c00c0154018802803070030a1010b04086040e440900d8224201c3e14260701c10f903004c501c410104150181c0c203201c51001b51460b8107146096504060319040540240c4000401c0c11050340d601594060003006010041036440d10000d0fa91b640b2004007000c0f0b83c024041248054460182c0440c50302c04583c10399100e0041c81d0900306901c0c800c0c2d02006800400d4445250185101519090100b1020640819403c0e08030307002581c0c50302c002400c503103d4003c00d940056a011456940c1c00e5564034035003403000440c0240b80551400c5c101003605401001d0700500380c0306c030f00c0d8001400000c01001240b0341082c0340000c0340c1001c196000710580308551108544040c0019402d080c078001a45404050401c0b40c1c41d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 596462877 1250 596461627 596461651
    0x22020a030e0a0807140102070c0b031f060201020d060501020a0209070818060c07031e09030201030f1d010b01020d090f0b030408071401050f100b121b0d0605150f03040308 75
    0x50411a860800082e504140c0301d0303101c00100b8000348903812049a1030810840004c601d40a01510b8800e82a00e45001d070302907410000021a00722000900c0308814103480100c0307054081d55401c0d02034000d622282040c8401c50810704002025800032501c0d10b00d00c1d4000d84802c003a5a50008201c5440b04000e2000b1050002d2250251100d54104889481013449250007541c42845040180601030a1f8075000c0e407080f1071355146254103521800342001c40790b080c01c0201c1c00b07001407611440600101c030a01009103a50020762512000305404c091081d038000e03000d840004142e080100c501c0030003400381d4007100b0003801041000821480042d035000d4040e00c0780c2420b141c45a5200d0343c082c2860058415103a440c0e00510000c000688038480d04000d6aa05000020b80341500382c0200340100d508001e80c0300b6105001070045c807400d683c01c00c5080d1000e000c0316510220b40e224400180482d0003201c0c014060085a00604604441110b4600008070300e504c1c07c640e00d60f50100d0340c2020090080035112 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 596464127 1250 596462877 596462891
    0x50c15090304030f0309050a09110a1107053303060a031104022b060e06030d0c2d03090605040f0302041503021c0b0c09011e0903290622020a03 63
    0x54138000c400d444507202e0340c1c8454010789040d0811807403104942100c00d80e107140000245000ea00201183ca04e42a1424030100c0e0203505140c82c0d040400725405941c02c516044002e00d0400e03048540b5a0b000041c0c9112000728a222481c4c43c040d90004446250f00542c043e0420720124400d5040e0920207a8001d0025140c07001d84098031080718940000e02c5001c9561000d0456203000600600f03001c1c0c040c6080705400b5182002c002a543d00c1c60340f4a80c000d01c03003c47e590805010305003505c0600d1403030120a00c10152640400e40c1040618011f0580006a01c501d020425901c07603030441d8200c031070350418960f2140c211f4003040028811006011070400c6046400001a00d914100c03114110888503141c20750003250914a0410744010061301000c0300c10414125541c0e04451030850485100c158a803400b02ea000042d6181040b540015041041300c0d0340d802d80c0c44c0d440701c64401c49e42002111661090701d50320248250f4015060962184070100404007014103a10b602903c01346030540340c040307400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 596465377 1250 596464127 596464133
    0x304020d020603091f1a040b0f060904110c0d080f070807111c091406090a090902010210141e090a0b07020a080c0303040302150906010504020a0c02060a02060115050c1509030403 78
    0x3685c15042606207890300c2c0d103805034032110f000703405da00d91032020b072414000184070758006a4465103034214184a607070082381049039526280c1c051984580000e5005546281042c41e140c2d0303d040c0038000100240070500043c40014116a04900a12844d20b4101d99611038143c21744900100d8a5568201e100e00f400b181050500705000840b00109030b210001c109040c0a01d11302040d01600351140100420010810261122541c10048440c404400a1050180e00c0101c2c100354a40c04034200702801c090a00c00c0381e03054800b80e50f0103500540409100c00301281c111030120740b81221860455000205028080758040030318507800340f4907105440142600755105040e0307070084821903950360b00c0270040000b0950104019050752015600346e06883c41d20000b182e54170074050003403501968011441901280c001e41c00e50241381d900403c0e00c0c0e21141c91880095072440309118038001c1401041a040013540501c00b12042c2c41f103030001030003c8402d03c0c0360320504000d01402120302480104000008 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 596466627 1250 596465377 596465413
    0x609030a14010617030d0c0e0a0b0d0605010f170a06180906050105091006050a0e06040b07110f0105180d06090311010605041109100c290a020304020d02060309 70
    0x20361841445040d0007841c8201d240d60846016130080d00d8200403041c89510110307800020390341455880700b0040f4610842400480d10140188150354000031a0200495912402c074054240e04c02d21000400c4110303a10307001140e0544e070307100034503005c16042221588641c10f8004003079441640700c000450f089658000f104d8100b00c03003100107085030f03581d0f00b00071b02005105e0140794010401207035900d0407030403d54100042103205210711004e0100004070900c1044c002c401e40170034400c00030144e503140c680c0c1d0035910030703260b00c200c00496060501d81711009861030511041c801090040c0d50305420701715448a50145440030720b0780640d201d1440d90f4101d0000c0d44600524681d0f0340300342d03181039500c68640000d90940345142c1029101e01d00700100c2645000308e20007551001350044440d00d00110010005448060350301c4006048071011507042d286080c1010495151012001100d03c0c042d5036141548040740400c7d64000e500c4491041071501515000c00510b030410741d0402607030000c0c46c603c007580007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 596467877 1250 596466627 596466643
    0x40b150303030c090a08060f1617040f030e0108040b1b04030506041208092a010509210c0a0312141204030f080708151903150b0f0604060c060902060903 67
    0x540c252002613086100c4c103068008400420741000100881e090800e510398013000d0007480402400c070070b6030300a0f46652003090304950310b41d4070300d072003010a0800b17003007080c0510b0f0a00e0301134010175103241c0f140040354401c15000d88101e0b004259016192901401d40080210300c01845500b02003c0c480440410020310a240c0aa4031400c100310f11761030047c1e0094090b980042c1084502d4105501c0c1c1e21902d4154614560482490b00e8450b0620031081c0040e40da5028a81408d03400a03258241380b9136401c4108520f018410b0050300305c41000c00e00c03404001c5441e65601005001072181c0f07660490b16070081c504894400c80b05842a410041c10b00108001628110707401ea000990000e52030400c507030040100c2c1c3e003020052074992642d00e41035a20400115010302c030b2502900c0c0c00c00081414029640154018603171055664041210303446480d40500018011103204000640c14601c080c43e08604407812500b0304d444691070300c110f9441e100010031b9034420a9801c51010002100596002e2010300 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 596469127 1250 596467877 596467891
    0xd0c090e070215011e092903030c120702042408010608030f0d050a0603140115052d011b03020c0f01030606080411010905100305070201140105150304060e06010e090c060909040b15030303 82
    0x9000f00001900c401c41105c01c7e4a0030a019400070001c02c0c007a0100422a0380342c03030821005555032020f0a1021400609400c1000c6002180c011110303401d84d440c620055044610780343c028803c40392113030016902e91040074140d8808079010040080a1003558105a50005605800080315a529101c030b80c01400007224020b0f00380d40d5520b001440413034440350a40a0070055400f240c225070282040d01010310440c0200601e2005108000300f281c1c80740705d8a08080903980b4660040402c90301d0b02075624252080018841c041075417a0600b0355101c1e204003401c0303c646030789000382602c5548410078025540c204050402c1403880000c82c03640c58000040b4515103403503400144900c0e0800009086546180031600d981c040314004220aa82d1341c81c2040720b00c0200d0b400a580c0c1d4403146804c100904202903203610314004c0000015010441000c040c1c440c54040003a039200800000412046102e00704019900c0301c3c1000105020580c00c200c02075000241d04e6401c500120280002491600111860 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 596470377 1250 596469127 596469161
    0x506132403120809010605010503190905031c050609041a0a0609150302090a1b0f0e0a1d100815060103020c010f0203180313060809030d0c090e070215011e09 69
    0x10070784682c00301d2211343c0004d20b10b008100483c20310000902d0b9100140c074014884006104003c40348400394841049035030700108403aa54801c0618020b4400844104100700c44e160400050790f500708204420b01c00d647c001c20403240100040d58101070004003074103081c8500d03034400001c20544454413404000c411a0300c000c4250904e1841013088001c002001e803120710342004102031038250340300c01c4481c074410365090030080ca0380e01c06d0048500201d0b8141c0e42d5844089054001802400885140d83c0c0c840403075a00e035900d65500380700360072198481c414403425600c28580d070540c4a814620840d04000b0500d40076181c032040100140c00e450b40401d40c3c0741c40303903800014032210300d160f207903a4180b00403018080c506011045466103c030185520981c01403084c418001142c07100c0030f104581c03070b80d0b0303080b9010801d1111060300106807440c4c601543c0e0050031400b021031122400020020004414400403100030b80c20000e00803440111000410f01b54841400c006c542403850740505030344e00c2050040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 596471627 1250 596470377 596470403
    0x2003030f040b130c091802090c0301050a170312130609111002010b06030c090103062103030c090e060d021f08040c120f03080606120a0c11010506132403 67
    0x855032801000c1c0c1061610400b0081d54000071300c100003000c0c01c41d6618035001600149400c003880300c800c1e0b02e4100070341c0001000204040030a2042c0918141c0b58283e41d040495030b00c1d1402032082c514000100c0e14140e0082c40700c001216401009207a001c0155040404014030300c0d0348180640f15140c0c400c8810b824000d04901047c100440f0056070301d4130030302c0244807004008001c500c1520010b401003070441d60003d10008164041c4c3c10160017001444403a040800741c0d640b00200340026040b0840c000703414001d0b144070711442041c0360710603100c132056150310340e0b180c10003040a0b8400c1d081040360000807200001c00b40c0c407480c0340c030703000348c01d045407215141031a080c544540c405001c1d0304403404e00000c1c41c10704400b01d001d07024060200d170740c035080100c4280c0394000010300a00030800a003203c00c0300b10003040b44500a907008614408059203c444142140000c40c41c00e0f0b545c1100c129030401c418584001c4950004c1d004006015a0865031654a9541e03680c1c1900c1e100442d00305603000c0c2c5070404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 596472877 1250 596471627 596471633
    0x3100b0c060615160605090c1c0b0f0c0f09031018030e06071a0c040f0311210c04020706020409090311060a0225020613030c0f08010b060a2003030f04 66
    0x40050804824403c08510708072a400540c034207801c0c80c3d6005002c981d40c950018403003003c100409609035030001c0a041c520407203408080750644040d1001c031480000100400c1138041d8400205000d12113401201d400e2000413403a42406801400105505110b000c10050541d0320521a50511211009100c5183d18a034140500032250400445000700b80c204115804a881070740d031403002840c4003104a0164a40840551250040e90040081c4102c030000010800290a00e80e056040c1c00307654424a000100e018050308501502d01c281d61031700500c942c0c912629083d402801031602c00c480060505844201d01d800700d5804100840c003290384d0000742213403050104406540422010010343c9412a0744c10001d900c8007408845005402141c00214219030300c1e40c09484144000c0035443c8085541d07030500746040d45540c480c04880a82c2c0c0f020224410300c044c090464103ca002c1c0c100c0345003140d00f1a08442c1004582000c4200007442502c85909100c14002180210400721040416003480e007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 596474127 1250 596472877 596472889
    0x23130c020c060306100e12030c03040906060e01020d050d0207142404030906230a0e130b0f060c010b09010905071d0906040c030b122103070c060203100b0c0606 70
    0x99a407912951050003000071980d5041c07008103400714640350540f840721001c0e0210b0700502c140440810325000c00300780510010000800340049410740401880100c3e920f08007552120042602280143c10614040c42e160340590010081034540f24001440e080f5241c844003591840c96190343c1c019005607021407908068039030986081500000303190b905041680d00900b0b200418407032f030700c02c1c44220000c0c609001074030444144840b0500c4c0c44545e41e042e2401e002001d5034100852940710b42c064032480c0c420410544070310380e44c0c41800742508842504517020007803907400806054241c0e6480710384030492601c0750300c4458002e1940d03100210f80c9080a10000d040c081041d19080300d0007011208182880d0360705900e09800c054103880001d04807815030012009403030104042a00b00000c0701040280500014001d07441c1816000407064003000101d4413050703440283e40480c00a0004030701040171419076402540c1003034600110600a65481051a0351604004441e90550f0403140411039582401 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 596475377 1250 596474127 596474143
    0x1c060c0c02060307030c0e030a06200306030304030b0403120e060906010f06090b07020609040e060a0e06040b060904030306090606050405011202030106021f020c06250c08161113020a110a03020723130c02 89
    0xbe5400d00b14a4600c01080d520301851002a000200a00c0490141802041ca40200310480d500c18415000031281c225907810003078906100314414480005284100011641c040e102141d403040403561601351010007981007d04141c0e0b000300204000b80301556240708070040c844146002d00100c0c134004014404a5007001da402e24079030031590400c0300103102040019402401140c2c45042500da03030400710000c0c505074000448007450f1042c04540d2540150103070086807801d903139511b0706062801004003a0b010070310078000547d01039801c0900100c58090300c40a25034000c24014140882c5000c11882c00c2d00030707108414544444140e64800700a064110140c4a460303083c40200b02d42d559a0700c4219204410072128041c02283d0079904000071025603012210000303000c02069101018080020341c00b0110f01d1010070b059800781d0804000205000203001d425801800d9020314182940f1980910300610300c20b840c4140d40000c019035983c05c1c945190b8180301c0e4001440e6411850068909403074 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 596476627 1250 596475377 596475431
    0x101202032a0403080304021011070b030603010e01060e0609070203070c090204061d18130804030605100617010b1b101e2708091c060c0c02060307030c0e030a06 70
    0x8100410f00c00702d0081001c8030b8001c1c0c0d058401c41d904500a107070071500c1c1c8a032182c5001060140e40e40014520071904091406020118000c001c20b4602229641c00c84001d0712030344100c0c0c18400c0c00904c0c80d18203c40203950000300d03401640c7c602072040c1d40f820524511504403444555000c0780500c0703080d90060b14003a02c1000c520481c0320403c00381c000580102c1070040004030380151100010981411050031350321050b84200d0f420307202ca8403480c0150203010100c400d40300c000300014000408034441c5800592005429030404190f90030843c02201d0359000d0300d1041504c9444500842c1d0206041040340c0300c540814400180300c0d02950354184810051130b20301c000f03071303410624001c0e005c410b030180c00e050303e494452284090030100e2901040d03a014820304140d1190881d02d0392044000c1401203e04080d00c60882000760a50800c0c0a5505d13400c035100103504440c0074000038103a9400780d0304c80c40b03901100c2d06262105914038400a8903151000004880c1103407a8002e140140c44c880c00035441c0c0c011 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 596477877 1250 596476627 596476711
    0x209070c1b0320030c0618090a09230c0a030f051c022805060106080114010206040b04031805060301061106090f0a030f18030b06031b0a0510120203 65
    0x21454031290340e0340f201500408401c0d026190040700d07654040120140034000500b00546407030141c0194200000480003d44c0500b20400c000b030390a00541c07080c9040c1c254410f10b00351407203c030f200d6040134100c010110042244200920201155203003041e103030042d4800c641c051183c00f11032900a041140d20b41d080140c51000d1200c0c0410741d600401c0c3c450f883c0c05c4620707191080120791424110555404080a00303980a03072000440c00d164010525410781f48503550142079402c0c8400126034903007089071b01400c400c01000124000034404c0074620000d03403210008900043c0c94400203044c80d402a07201d02c1c04a600c8074100c41c18800c3c1440710540c41101381e405068508120b4200a0316241d083c00010108800360f01e28144036802542c404400d41a80380082c0c0500303450b031070718402c80c1c00e058803010311910400c0d0200c030001c01300244c0380e80c4a070000f82c050b01280f0300d040f003400740c00c4440841032400e1003402003809400c650188007551042001011196020300d01180c600848080f50540a09500d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 596479127 1250 596477877 596477879
    0x20405041811060705100c11070b12040206072324060319080d0612111009090f0e060411090609090a26070b01030303050705070f0204180209070c1b 65
    0x1802e0303110300d04074103030b020344000703640312494580f40c0d042a4403104a812175502d08000013680641c041500c05d070b00d0000008442c0300c580c5801891805001e800030b00042003070780130005001801d040001d00f10103031190b0300c1040100341c90300b109107a06810a01c00080d66200424006040e00c01c4858124422840402c4018904180c07010a40340d8034009008400c0c00e0105c0306c03034030070005140c0c100c0e403030b890b81e00d4010040700361643c0e8459189400c40905031005540e022540f21a0f10b42140c1c0b0007034098143c1c48071610940f52180c1040179180d142c0c03e04944566818103400e65000910240340b06a10580d124200403003400b081160104c400740503035018880c52800c010040c0302c0000c28840140d0800412410007240301c0010852003001044219107401c00b04100003009111499541680c0c03098909000b10b80d6409012a49409201c0000d02110380d604034200c0542010341c011411280e01201d00c241d160915000710ba1184000e44200000078410580c2c0000d000d20300e54004d0b050114415121049 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 596480377 1250 596479127 596479133
    0x4020c0604050a111903300905042d09020301150e0907080105040506131e0302030c1b030d030209031924020a0c02450907030f080d06080106090204050418 68
    0x1c8068080103198091800c8100d2969000070f404403000a07c0c140c0701000c461020710f0062a0380b10300d124140c00707541441091007104a0200e034540ca620400124000c040c0c4503a14004080c0c2000481031f40c15540c1c50405c1300c044030707000c0c5244010305030b83e448410f9207042c0700400c80d10f400415070006409900d41300500c000074901080c0d0300c1e000131500c120f0350205070070340c00c0462000300100e80011001c1011280d0300704240d008005810120102d0b41a01c00d00300089039003003130381c0d00e45a01e00c41e0315412405451003482d000c0d40c040e090701341014040b00c0e103012007030f618044034000408003910060000d1840703640600c07400c0d8a01d40d41080c94030b000d40c20807078100006029400a900002d125110002907a084100500c501006480399084415107000781110000300d110b09a00442c207045250100203507501ca000038403001203da00200c2c8807102d0809407a07504045c2c121100e020070190b00e50800048040d0240202d00c0600341020700140d4036442e050420040700e0902e0310250003140945802c00c04 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 596481627 1250 596480377 596480419
    0x111030c07030201111617010506220e2a0909210a1b150e03030f0a0c021606122301090509010f020304110a05060301080c010e04020c0604050a11 64
    0x1102e0382805c2c103960103000400d016040031003800340c501404000f2880018641e242140c07109403081144001c0016445140034401070300b121703950440f0000f0405003c0c14410803a540026401084281511005d0b114003140ea8882601402424001c0c00f600c00a464180b0300745403084d4002060350b0017440580400a0f0002ca20310b0141c6811565900205d802c2c26028020400f40f15a0501000c840c00c0101151800079980201100e0f0002d0f1146400034250340004008100c90107800098182c80f02c0356560b50302c44003c0c203400c110400840c0581101ca03801525801240301c05072006890f4035000414a21081c4101e840130b084900e4071108121a84c0e010181010b009415948012800310300e5503520038031180940707003a207080280140f0010030003060100126030314101e410100c4034503010755035a2080041d540001c1c041c1d000e03aa0002580c15059602903103805100d110083c00250030040003804081c280f40c01203c0c01c2d0744542051041208000c403185ca510584181150300c034120001299440b01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 596482877 1250 596481627 596481629
    0x2a0312100e01050609040b0303130305060105010e01080f060406030203070b0406020d0c030c0f0201180b0d0501081203010e1005100305100f0b162604030605070e0f300307020111030c07 81
    0x2c0a544001917280445c3c4403600300040300b08002d81105c1d81c80e04420940030008001d8070007a076640c091301001007801e42c400d00760900480d905a640c0c05683d240e1079859940c400d8080c0c4402e911965905001006840c144180c41c014420703562159160352a14101030300b0056500480c0302000141601480003e0300702034280300c082e41010b0810080c80c6544010303030b040900190004010101040300141402e500001000020240076050000ea6030307403032aa690f6948114400c034040d21083c401809980103008005500c504403440300e8008a0f91080400c203140c01c0701034801c0001e81c0341c1c0c08020401400340841c0006220900d07030b07881554580032540b007441c050740b41198043c480d00781d50741e030030301903508642c800c00b0750b40d0b0403040c0000412040080169000d0300c42140d20506140004200358090440704100c0080a8143e0100310203560030449000c81d4200700e11240000b00d200c0b04d010305005c040116042214070300455842c81280000b600c040d020088074421a0320401400801d000e000c07038a00c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 596484127 1250 596482877 596482879
    0x6051206190e090f01050c04061e1e0507021009090b100807031e180b130c06052511130219050f040306021309110705070b2a0312100e0105 61
    0x910035032a00703c1800e081103610521800d10b503090100340100120300c03034021300441d1240d8139811036105513101e18500c2e20f02c01603109030124080d06d07071520f41c00c860007003841046200d40c604586808010760001d0820740603460018005142c200050005031200d10642c0b00c0040125001c0c0000350b96094000c008840041c40301d002c16445007801020040e25411003503520b02c54210500c080c021112403e5a00030340405c0640e02103d000c1d003c03c90b84e0164100e00000030f0340001c04c0814580c1081c0042d181076000c10a0384280314400200501d19240c0a4820341ca003c0c0b0034440310880242140402c8404000c000040812a1040040710f202c102c04000220b0406103d0501c4c03500d030a1113002c1c40140340901d520150007940006100400320b5150300c0010140e40d40b040c1c040000008600c2c0201d41d9004a98006007280d1011070144a92000d030b00241c518120241c6182c056194800800748203031385112109042c0c0d52005c41c09506289029542507032101c1c1690451200301d181c81022003141106100e41 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 596485377 1250 596484127 596484149
    0x100f08010203190f112d0703090302040b010507231c020712030504031403091011060f19110c010c0f091806030b07020c0f0301110706110d060605120619 67
    0x1852200b10175000020528800c2d002c0b15110030407000555200c04420f842c00d20000ba03040e0940d1802c0380241c0581c1d1556070569079600c00507046500340002428a044032906024092242d000001d03104503d4105c207900c0c103d80721802c1e80300303102554540702c080b000c0c0400400c0c0c42500b01440641c0000c80000f190415548030744481e1490a040c1d845104c3e030b404c05860012400811410b03204008000c1260403010303103109060364191201203401032250115134407660010004074200e250003070b240582080c415147c0c40c01da02e246040060803500f92101c25411488041004000d0312001c0c480c901070103c075801c000d4010114020018003c2c5d4140c09410007050000c241c09240221950103403010b198003010100b05070a00e00700103595100302c91055886140395100c0f8000314101801030b03030b1540c0c848a891034144074240c0c0d2200c010b040707005200301c88007a0500224200c01500d003d030781c00800c4980c5986584503180101c4801c90b0000400c414003d09003445801803440c0e2400c1158100daa0306119 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 596486627 1250 596485377 596485391
    0x112050a140903270a03060c18060c0c050f030607050c030f030f010e10080c060711100c03260f04060207020d21141603020a060203100f0801020319 65
    0x150500400401020441d115442010408032003000001040b50b918200c1402c6400c0d0b8180500e01d030b4070a07103000140c3d00038a144c1c42c10000603900d60041518540a41084842819501c81c0c4400c25802648132030002100c1811040034041c840360312102425041c3c1d2076100551041d008680e403000c0103044401000000550b140c40210107100340c0d07007121115800c496403804c1c40c40020103615000c0c01070402455101010414805400308100e040340c08541c086c1080c10003500400005070800001279a148400021107142551090400c0351130580c65198a8903038011402c006081c01421000c610302c0060309801c9054100040720340980c081280c2100d55940d642d10b2030000040d0058a0000b500b00041c8981072040061450207820680ca04039000c80078901480c00468424220140c40b200107903041003089005909000041c02e028000d00407a01e00344850703500c1e01c0c12680220341e1403610610405051016000300074906004150f407400075411420100c02381c0c81105c5144a000f503000d0b5071780c15 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 596487877 1250 596486627 596486641
    0x30f07080d0219090b161b050d05010c11030a0e0d031e020703050f071a0d02041a04080705060406021b030c0a0e0a05060406180504240b12010209011205 67
    0x1c484240402003001d548a5007140745595401980c031124201050352800c001ca451028203041c1ca80800395407040c21701d290410b886801c0350b600644e6100300050248030010034151994891085150310641c00003035140e1115000811900041200c0d03c03468000700840d480b484d130b0203007441c801050110744010039a0712606d02034036502c01c01940c200105420321040f802c0150007040034001c6900607000d41e01d511105187c40c42e12041c143c0103480d0803044004101c41251840310207803103482c1c040301c0c1c010314050312036078103071a107074904202d01c81e494200180c00d004100741401a50000e00707055440505213820140c2c0651510140c0e170074440340303124000074a2150382c4c040200e0074a042c0e010302240d041c40d441d540141c0716880d08880300360300e4509250101d41e1508240c4112800c903100360006000c0795800089070009440e0141098411012000600041c01c1c0d54150150b0704280002002501616200904c0008209968240d403241d205008074910741c0d0700080900c40c010801c280000d55a41c0d018 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 596489127 1250 596487877 596487893
    0xc17030f0708070c021f02011104051c1103070f030c06090b0a030e0106180c180308160c030515070f090506030604110d0606210b1e0319060c12050603030f07 69
    0x134040c0d030000c1c82d001c40f455144800c80700d64240703181e964024040d50310503030f4000c60390f403281d44141034000d0300089403d0104c0c561041b1450007184500b4407a804501c403080003c0c40d209440c1c1119030310b00c0310500d08108105040da2010010402400e1004c3d21915041c2c0d242c1150080340703641d40505803a803803524902e000032350103100030300040541c0c030406400101c0c4a4000300700060310300001c944141c07285034040900c2c940701000c03a613020914a107428585801c03c0c40205031024212882c04515102200240062204401103110412102241c0c5070105004203040c4482046805011001c41c048c000da8644404903644498240c07000725201100706116452071055a031420b2042e458840042001c5a0045024900051500445a034100742c100f6240442e40380500460b4040102c0e1360848442648502c03c0544800c01002c0d600c0e203801040d403000d20301c1208a01151000c1d0b03514040502a500a08501903e000f0000c0400c240d20304400400e41d240305000403d000b20101003005001c203d004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 596490377 1250 596489127 596489147
    0x2030304200d050601090b06090303071b030c08010c081812030903040b04080601090c09080303040f11040f0e01050109060602071211060c0a06060b07030507060b060c030a0c17030f070807 82
    0x50100c60b008400c0d418100d03115003083c0a001c000d1400c00c10800c00602d000c0c01560464400180035600e051100d81e107034160140d031925503180d0400c501c140040400c1540354800c0080010400109000550781402403010b9002040c04036421900e00d22008916400544056612011100d490740c039107a200b07560f451030103203620954055200040210f012040807030b06030b040b140c404c20140300340c1c080000103540580e0f19000e082c140b0b038001c2c00020086000c40c400d01a0142c0107941240390711410801003000c2d5540425502140c80d01c615a00c440400c0900c50240104400074040183e90308000000b901c8184620401d511154902500d5050000302440682c1107407008140c15920003c01d10321584a00c03100340c00740c80e690314210000130101038540c1201e56455041d510395240011076900c0301c00400f052000b40b1307000072041c050300c0c0c40510208014a5054200e441d442a02030301454107068070302a00c0c045d0295000305000b4030010a4071980c4031b0f90007090b10f0604014540d07074580e04031041001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 596491627 1250 596490377 596490379
    0xf240118060903020a0501022b05130b13090c0c020613050d0f2a090f200c0f0a0807030c030e27060a030c0b0f040906090b0306160203030420 62
    0x31000001034641d4020310a0b200701d030310940d000007016a8030380c01a40c94903180f01000d02404c040c03001c000e603560f800410002541d103850038000c0c1084040d013005060788801e41c002c1c04170941c0004001c40c00705081e0030000700901c1079020521045001c480018116040424000d0280001045c80c09170051070390480806084050401c1c1f408102c03505080c0382c056002c0006a0310000401003c03031100c1d0b052440741c0c044c80c50100c00300b114030f032505402c1002040012800788981d9a100c504040c0300c480f0300c1040182d051841c03502621035000d0340300d45081c440d50f00701e41c1c29643d000030800b00000c5d9030b09050790103c50305400c1085002005041c140e8100802c00203543c0e00588104201081c0c03891030300000503049034822482004e03030f50b0400340700342001140009413080c148100100140752044c00184000d0705220b5009003800d03131304c101410680f12541c201d1180c11b500c80a41c04002e007010809030f90700c0008000c4480303a500d44130601944910002c1d1005c2c01071b00c6640c038a5100d10030050301c250b8030050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 596492877 1250 596491627 596491667
    0x3111c0b1003031805010f0f111204060e041a060f12190605040e060406020c0102090621060a140d060608030307030605040e0c030601090506010903050a0c03020103050f2401 76
    0xa8809031909207600d440c001280840e070541d4111000c030801c0034000b0140d07a01030b1101b0750030540000c4103983d44005040c1c01402c2200154500403c0c2c08140701c466140342d400c8a0340b940b03440c10705c900500f2284490a50f14040c40c600045001040b04005040c10f1054082e50070039a1340864250039080342c07048412210550728218180600b084d00c2000c2d0001494032208100000364460701007005580802d13540c03400a51001c004203000c1910346d4018021030010800040c03902220102203000ca03040480142001c1c1d0725078044041304500110306950241003110558001410030030782505240d18510900c1c01046104a034400b040350aa00c007001401c1203008aa03240d10741100001e0203480a8001c00e8000c0f070416400c031501c1c510001c0c165158000040207005c43c0e0303007130a0030000104402050b40341005010f45000011510034801103910500511481400a0031800003509450000d05507400d4228402d0400170000c0d2124103044801e5065101641c0d10501c08004880c14040340d50400300c0e2403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 596494127 1250 596492877 596492881
    0x7021206040605130b040b25020601090f0b01050a052b1b08070e0f1c1a1005010903080903070905011403061308030708040321020a0e030703111c0b 65
    0x210004a092159108002c02e005607a5482c903240c1c002d010b008802010f1081a40102d00003481c03060b5203d500032035003440c464405402910f016150300c81e051540e0056000500140f03c813801501410342e40780710103882801040704c0400002e01d01d00c0f99500341d0301081008100c0006400c240f1120302d24182440154003800b6078050400001045134031303000016050f1510039200814015010244901c0c502e84802d0b2010b2030480c2408440c0300f404500d1a0701555030132001050006d00589502d40e41e00405480c40343c5600c03200c0d080e61030540a807203041e4240848400b006260fa01c6901c040a40ba03004a0381c585aa003103101091411000340c2090200300d0400c2c0001c0340c1c0800e064502005070364220110337003040e1651144500200030f454406801540c08100041d4141c1c0142035254000f031003454940d800400c0c3e203c0e4030302d500c0740540380101040e400040e20802c0d6036100c205006030701e00c120f0240402a156550304003500c44e84212403400307011240e035440021300d9540070a54000c0e803c081080c00074 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 596495377 1250 596494127 596494159
    0x60f0907050a1202191e1b0503090315090601090e060606070515040602130e060a03060b01120c0512010501020606030d080c0c01020f130e010b071707140a0c080a150207080702 77
    0x100706988000c40010301c5000c01d1088203140f003000d2a4840c03c43c0c0c54200e151f110b03161130201d0310041c804090307809200410824400d80c50420411036030b4040c0c14107001881c100b42c00410b051480c1a0322075135581e070400d45400d0a035840825000d40003141150704542e04c001c0c6290243c20f02c00c2e007004040c6400c0000d42004140111500200720351011100300d600342c15103c8400146440e015a4907a070084140c0d0390a00010340b040e030060140100505050789607080f11302140050700c4039042d04a001130701c00720f85040d242c032148900b02c0c0900824005000a841c1c0000400d90361010315501604000444000c102801c10000c11a45211600d5000399528100d2410800d61680820b80a000801001c0b8001495070881d001580c143d41121141900d4080b1503214200148c65070310311800c54641c1000000e002a0040555001500c0c20f007000d86011901c40c280b549561400d82c0c004580341c0c202d00350410003c1c00707240c0c0c04c2d000c940111500607224016410583e840340100f050013904a45002c24a50007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 596496627 1250 596495377 596495407
    0x309060d09061802190f05060f0c030724090503161b06080f090a0f08131223010216030309050313060206090c18070f140d0204050108060f0907050a1202 67
    0x1590090b05e03602c81a100c4000c105171605400d10070b150303105003080e03020700c254070b883e800501c40406c4e100c44407401c1081032003407230b821035108907011070700380c141b11010140d1030080d06a00d0200c1106140100540a215140c0e00d03101d100d121000703984580002c004004002c103009800d080340000b426015002500e4080240c81454141c50354803d900e20303100040c03505800010360340c0e8240c0d806503680b46c0660307581e41c0790081c0f6004034100c583c26030507001c000302d4040e1030900e541545030301500c0d806030718000b501074040c0d441000702ea9003d8140d00401c50080c0c2d44240811a03014250315180000740a1558200b0b141540107061602c0e1a0461268001504960001d03010b8041e849082c180c0c2c10191a0f10100060010700c00b0311040c204460b00d00080029005807802d00000b4070604080c0f0a660140c0d07842030042e440400c5a03650b0703035808981484075503031207026a13502400656896449210202c00603010100040880007000300c00a80c1690781c80c49841140e01662499030150340352a494405858 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 596497877 1250 596496627 596496671
    0xc02010f050a0c2304150f08100324060510050301080f0c0a0306020a05130905090c010c0503040b0906120a05041208040314090a03020630090309060d0906 68
    0xc11800c000110319035201d60710460070704080e41d896210540094407078065034260030100d8002d400d6024480010382400307411900082c460b09658105903054002405400380301c01034500f80f03401d50415420300019076071291141501c03011514240f49440f8034900c103006480280c01c00c80e000340109070a4002c058024024506271107030401521000c0c403c00e503001c0d664a001c0303040740b41d00c500a04001c04c04500c0b150b004110a04840c903080c0c1c1340c10070000108203540015801010507541d20000c00c4003042080c000018415401d00c0c210350041c4081d100c2555038003c6001e1280e1580300083c4000d00d03075403000115002e08680407545040c500d082e010000c000d100840d0165092612900302015051266050794410b65164550010740306441d6942030b1190840c04106c3e03040513085001102580e10f00000d8102180c0c1084038000920070039614800b040480e0140286510300d03d41440610600442030b2140e005050b1840e540b500c0350200308401038600d0040140c40701c0c0c904100600c0000f15189852 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 596499127 1250 596497877 596497901
    0x30103120f1d0a270e0a150c031b020d0807020102040b04090f180f0308010b0a17060604080a06060504061509060e1903050d0f020c030705010c050a0b071206050a120201030e0a05010c0201 82
    0x1010840310f841c51030302e8205940d002040d41c595441c47e000c01c0311041c0e00c00c2c0c3c80041035280006460800c9028981203400b001c0c000790250380284280b42110b6070050706151300c88203610095040a250441c003c0e0343d0301490103031891040c1c841c020070303082d02c1e81c0f944407034030320381040c00c03100d001d020740d8104450252460001500021140400400d510300b0401c01c41c1c14102240d07907046845080c0da1580d0690490290000b944000f0400000a6841c0b00300024608940a600c001403031170710340002c000859005038022545501e004400880061300815a04115070700c80c00d0072040245041c2c0000d41d440070890120515004401010051040010703001250f802144c80d41460302084110980c1d80c1c1541400035581580400c81c10f003c954440c810200c10b05200703030f04a80354041c00396548114041d04a5440f400210b030010407a00c106c02c0c034000e80001f0941030301d007803084a0800f44521200a4102400383c14151602418041c0e94401c02c18481c44641003402005601e80c980d2000b4040c040808500c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 596500377 1250 596499127 596499131
    0x5031317060901110910090321021c080c030a0e031305030c01030b090109021e04060215010e011a07030e1315080609030a2105010803030103120f1d0a27 67
    0x2034001901442480000c02c0c1d80700321315082407004010414000003413040c0c002040764440001001842c00410040b0400759034074082e52050035400d00a1030040c902079101082d4071490100d0b00b9007600945d1854004444141e030594070f40d1020440009441010808002440001804c4030300081035012001a0358088048c0c40350a40755000440640f46c0f04603034944d0142d0654010051454580d0091408404203005226900380084852280d608240d021501680200302c1144d0440701829403d4094071013032500351665410112304414aa4404520380017014000651f002494010004001c1c20040188043c0d90540300d030749060090142c01c50b0302c410b05081128040781c0150045045072140c0343e0800203504011904000300c52010030b18a40c88105548480701249074441c0b805003038064010702c00155a294514900b0103c48060f00013110200b0034079448000103e80c0c4019040b0b100ca00e035061004a85081c0d40005044454560000c00c0901010845414030560300300c120703820302820300003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 596501627 1250 596500377 596500381
    0x10302160803040308040c0e24030c0406120501270326070e0103051302030a02061e030103030f020606060403020306162a0203100c32030a09020f0103060506090d0503131706 76
    0x42030500c4c03201038030103d03611009c0403030300700711040382c090b200d44440d9000b0700f2960341050b80408501200c41c20b4011440c086481c050300c40034801c5c01d0041c01c00e00701010a10300c0d14050315402071030380c2c85200c030802003c00510460300248003045a464140314449c1402568403401c1c0210060003101074020740c0c9012a0801d00007d0816031a4031440454540160150601801c981c0c20007419a10082003200c0040502c000d81c02d40b40507401c0a1406184247c68400a1184001002c0e20f4044014840d074030602c0c00f000180010f071000f00e80e80d9000b0034104d140d520003406040d400d4683c4080c51107044000c2c0c010340d42000604086d416141560f500a0b01a5600100c0c003440c0ca205944448903450003042c44034400d0340450140e0344203011003100204851861009201010500d94825590010604d0312242e0400541c44e202c4080c0c09034075401d0031704001c890716290114240340101e08609200b80f02820b001c4060103010320854200c0c001d21080084619110302c41c220310003840058648a9206200c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 596502877 1250 596501627 596501639
    0xf0e0d020309060403060510170610050405010f050d05010b04020c070611062802070c030c090b040e060c0c010207050a030906090902091c0501140c0301151d010302160803040308040c 80
    0x2045410125000c0d107844d00d8581503454a03070207858050108048071013506400900074003901c1d440e88003110540040d100b41d00303104090900550090f0081407095150800401c031400700404008121413064401d28200140341c01c0990043c80c410001b643c00500014002d441082c0105580e01942c42e507450340c151000b0450803041d554030045640002d14500ca99104209400b0341c00380b00140e000800d4054589810341d40c80d01030040d00b650044940d0040101e06010741401400b40d0502414284d1f8108481002040d1448c1e455402038544e42014500180300040c0003801c2d0101d80304103070007a0484040d000d40b4070b00248008010f10038200040e898100120f803c5030980211113070404001c1040040f00603d08107501030402110007103070b82e5969200301c400c0401100d260302e4803c045c000a0151a0b61606030002c2e252000341d544842000f03a120f640118410103501907a03c0000d083c60700689480313242c0d140f1902d6644007078000d0011480841008200355016003010b00c102c1c0b0a0440c0700c10560350341 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 596504127 1250 596502877 596502883
    0x5090415090c0804050a02090402130c12110717090126180f0a1203061502012906040e0a020702060708030601090f0608070c030e0a0810051e01090207030c02040f0e0d02 74
    0x744c0c004140307800c189070755000340c902088078a410900081c481d8680c014074124000c1201e07009410500411450960310015140d94415240d1200e91046640e240c44926919441e400e88010324082150101007035402244e440389c90680500300d001d040c100f84d1140c01c2c52542c0c02c944000c4038600000030b500708203900c540d40045085030444000e1802808150745981e2140014021100c0b50800c15a03030b01c000280070f043c0c007581c00da84c400d85034000080340810710304111000542c0e15444102032403154106411030700c6100889007124154038142c035141c0c03282c0307035100003910a11401950008004c20807070b0074005114020750095800741c0b603100e03510703a903003150681940da81c0c800c0b00041080100040e2a40d030054030404503c6200b450102d41200710580011440046908800b950340e102824211071980140700b40c5810403145401a80c1c1103d14030424103100300140690001d8076004162201014011700f155000140d0003041480f044240030304460007090240845130a41c0701d04e040c04030342c440c008 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 596505377 1250 596504127 596504131
    0x10905060a12030e04020910030504030e09070e0607020301110a090e060913080901020a050601170f06060906012607120b04060501050f0c0f0a05030c060106030501050a030b0705090415090c08 84
    0x600e8144102e6036202a01c001441303513030b1250003035000c10a51006590b80e061071546218280c900061900301420300801448102501e28065240c1400380142c442d000518134100c4001100c10507624405480440d0150074100081c2411110203d02040d9140e001081c09050300e0607200391940e40d5603082c04101060805550041607080580c0b124404108480d0052507450b2041c01182c0c050b1019a641c00c0c607104c02644415440b01014080403015201800004899402d0704001c240070b040c21400666180f8001e0a05814007440f286180079980908034001c069102c0d80101d40c0d028a0a1030004d0124400300c01201442803515078140708918107442948103031981030f900c090420b40110082c240c690b100c20042001d0303120380940c108103000100700e11100b1621581c0a140c0303a072012000c452920313006130000400d16085c10300500ca01c0d214074441e00100d0f0781144032006c681d180d802d4107850a00c41c109000ba0402c0c00c24422008424840d4205400c440d422001003040c1d00550f5000c039040003003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 596506627 1250 596505377 596505389
    0xf050102040510031e090f050d1e022b12140103021206192003010306020a08010503120304080d0e030d1b0c020603130203011b09050a172a030a0308010905060a 70
    0xe00d00b02c4005c07102c140e40040b03000e034410032184082082c00d490b80b51910014070140000124030074407136262019508403045030450940001c2186031403c01210000824217074000a4400c0d801e40700034811486040221148504180c04100208811501080d41a42404107a0140308240c0e82c0154100001810520691081c412000c003994401918001341c600c2420404502e22400c000c0b01e1a071a1040055000314800c0e0001a034030340e203410014085050503400144282c001b03140c00614110800101d0f0740c0150302040c101c0ea1000909031080c010800c211810301907101c00315040c2400449584400e911600c4041c90030020340c11020122061184164000d400200620102d40a020300301c0c40c807000e152004001043d030b10b442100314804c800b000c16419002a040100810190a110a018003c1c100708410156091048062581c2d0307010409a40710a01c900b0034000d0f404113119040092064800070240c1e440e0071003504000f89a03100a00034503050300c1c5404d0210300c19145c51000300f0100d502c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 596507877 1250 596506627 596506661
    0x702070501170f04020609101205161d01031418060a02340b07210c0519030e07170705030703030f14040e1303020d0e09060f0109030f05010204051003 66
    0x18442e03643c0042c404010788200d80122040c0803030b011700d42d95100285040405550340176028110280c803c1d050314400303001000e101c1140c0b07441000303680d44980c034001c1c4c0110540710b07280119140fa004070700030300e10006d03411410032025040c8582d1003c01440c5200b040c0e00001260103a46400c2c0c00242244203c3e0212021480c0d80c170110414840034a50800c2c07070301d0343d2415681603038155440702000c21400700c03000000a080c80c010001050b118514001100030358000c108005d40809501030a9071003005c4050900443c004c64415489200e6005451181c0c0c4a2041e90ba0f195551421704503020300030744201d1807030b02640001081606000807441d0440341c1540d00c12600000800090340c80c3c280f000000100030390308000c0481c5290042401500400741002c402800145e1814000c0c10001e00b1480c4004001003030659200c587c0c1d98410709504294110b40030040c0c0c440680c01a201c0003030710380c401000b804002001c0707402d11006601800813240265281282440380340c0f070460440304403c1414403540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 596509127 1250 596507877 596507881
    0x80f01060609050d050f070e010f230906240a030f15120311191502130306110c0f03030402031e071809021f09060e0f1302071a070207050117 62
    0x46440c0004c494082e010318151510781004c3e00c9201d06041054006020f00303503419004010001c4000d41e0031000f00100d462000000c0c1d5400282824800c41d002349074031a00301000032400300e0390b68604c1c4800b80500d01000300f0b480c240018107588140c2045c0da01b040440c6c40c146440380220010300805440b00881c0100e1081907040582a00030750707032281c0c4103404210100000c80010801005802c1c800c80d612010b103224000f1600d020700144c040c005551076101d00520208064003462946070080c0e940c0004085480014807450050b14040c00211500f28030500e91490241c0801000841c000d0f4000d6041e0307180061344854021821810750100040b550124804005108070078107251281c0c000301001060424180c0c0025a07400300900400c6003801c0b045d41c80c0714107150003504460003000c5d1030504010f0008480c2c0003c1e0340d604d0604c40d241c005c20070a051450540744070340c1202d400755404060380c4800e03910796420b0f01d211341c401c4071004007512800c0c40204556016070000d03681e8602c0303008005c46035 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 596510377 1250 596509127 596509129
    0x90708031c0b0d0c031b0b031816060c0501110c1f0b060a1809061203082707080606041401060e0d020a140f061809180303040b01080f0106060905 64
    0x40016541c0c054003160366000700031415030312400d810051601803210b680100e0300358103109100c001d89038040c401c1c514125004100b03407104802036039813040310341104840700c1c01c0041c5a40c2c1000b40100b02d046051400f61004103d26030012082c103c114010402040601004c00840c07000d0320580000203160341c45484d401501020036412000d0134401140041606503221003c40d44c560020000c100108030b1390001e42014007001e0ba260401031401c0d80091102c0c9145c421a07400e806a6110060100041c2c800010081103102c1c060605610802001841d54041e243e1002c0e220742090103110079070b00400d40460010314007030080c030441200c2c414810380706034a0318000b44c540c18600b104150300b024060040390096951000d21400801070704007144e0b01e030350070f0104010b03420609800c1d00380b15480522040c0070410000010031310f0341c01d0a1700c3d209042d48641c1ba146091800c00b40e51482c00d8400001004100201c920f0018100ea034441304444d90302d0010b000031070a8404c2400390b0000070354100c00402c11 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 596511627 1250 596510377 596510407
    0x270d1409060417030d050106031a031f091a01060c0b0708060603010b310501110703080316090f030503070605070e150a03020c07080a03020708070b04061d03010c0f030509070803 78
    0x103c50440b1044a00c0d165490303504805481c0c099008c040402d40d101822241c9982c6c4520355981140c088014000104410254007541e42d4042c580c985640d079034100c040100000240c0f0000101240500d4070010b41c3d40e904000e203030341110b0208582098507100425500ca00847e103841c0140801858241580c0c207002012a19420403060740c0220308000c25000710803148108805084549240d051301071034102000917101190300140e00da01a40703c0001000450448403e4035001240410f80001c2611540400c54408130340780c002d0354407105110400010440008002d008482c4214014000350341c591005851003518511156042800040d001c0c05904111000b42140c0409040060505454807041403a04071250455440d81c3d110055281c14180c0422a40c0d004003014001484020309000c2351391014065449401d003400fa000d02019421244c40e00007071080308018008020628080c5801000c0164a18044020920301000300d160900b011a160302a200c8500055181c0195a502ca80c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 596512877 1250 596511627 596511659
    0xb16060207080d0c1206050a05030c0f030c12070f05060a0c0321152103120b0f12100b0301020c150c09040c0f020105060604031a270d14090604 63
    0x1030301c0708100100072843c40310380b1901c102d801280c0d5610108071038500d22481141d201d50000361107011108410842c41d50001740c11414140190341680e6031b000c604010a140c80100724559520108402c0d60409043d0000b48000c212481e682c3e2180e070490f5070b0b8041c00220308c920f01ea803a0001c1c0e00ca4003c40046401148501c5004030400e1504544440c0e001c21001101c9403842c4090011030407000802a1680f40b807080c9c03c03050700b49a181407005145540252510350034550000080343c484815204540d91100c4c0d409500c0c40103803180c441c0800003014a0388405604000d00f0b6170340d1500cdd420b80c0742800d052081e500081d113614000c00026820540c1ea036101c0e0070040c030000315440c04111015030b540707450103240b031000703525100c40e1000100b0070400390030b40e03500400c5d4900450041c030080010601161502a40c0e1401c401c600034180c685501141c803144046041d05120072075166284d211843c0021002c02c0c0015641d104c3c64941c0c640462450740b849201100c540c407103014403090082403a9881e002d4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 596514127 1250 596512877 596512883
    0x4050103080409053c0f010e180a021503011d090d120609020c0f0d2a0503070605150f040618050c13091d0607080705090105070f0b0703060b16060207 66
    0x44191703401d0f500c03c4c0c00c05074407466080d0040611a40480c6405103403002c6810452031101d54a0799814041d40c400360a900a1800800d501e22120218280f50180851485a42c000d032801d03900428020110b125540207205803c02e18120b60030102c000303240441064055400c010245c0004144c6c541e04844200b001c1140b162032640c0d564000400b14241c0c40201500f011000282401082a100c2c107410502030403900340c1070060a015003030030b140c03041c8400219480f44582c0c40b4a981c51070b003002855402400c100130714451905040c41000315480c4155a01060129a160030180194017031001b03641c103e00c503212a41441b80501c080d404280d810480e032207400400312604100e803401041d602c0740b0040c4e101d0800b040d610700000307080d868100c001c0c0c86400c011034003d081c0c90810030720082c400103000780300208100c0c010406031a01da01c620200d40420f50402000c0c0640301c0c00b41040b03a02400191102004645804c0380003445800d00c20680d03075040d036844649400c6020700e03204c41001e54402d000031 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 596515377 1250 596514127 596514151
    0xd03150e0a060312050415050a120f0504150b03060609060102150406020c06151e0f04020406050c0f240402040f0f0912090f050f040902030712110405010308040905 72
    0xc00c15a044014440c401c150002020035040e19504102282c0400b9007203440c200002048107000801c000d403000a00512585441640e9040d2844102c0c3c0a40348000c00b03503801820f0041c1c188405071180c02c5035002d140501c03940d1030781e84240d00300b5108840d40e680b07500b90581c03c1000000c546141650302140e010f68180150b07a064031100b41850340c902070440e82161059800708a80d00e030706208200496001005502e27144000200e1070010700c5040c5402c899070040d01907035031050319940341c500e81c200e810f4201600942d11282c0750040500181c00c040d111303440c148240d8541c4400326900041d0040d110f0003004900c0e086003800340b0721403580403004006982003a220380307480b2403405040c800d000b2082d40351100003e44881d245000c1031881583c26003034080041c0043d0910840400c81c075900200c8404071480241c0c022910003060241c00a01c0d0080d6060045070000100b2801200302d50458500c0751511041140740001000101d4800b80000341c0f03081410b00c030a02c070407215540302d160404010100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 596516627 1250 596515377 596515379
    0xe0613020306151902070e04020604090b010908030a0f0311030c1b0f07062d1409010216031a22081c09030203130b04080316141002120a09050d0315 65
    0x1483c0c0c0d00381c0c800c500160a078100107502c0d81d41c01c0d606118110141411000c4071030f0f18100f6400056039400b03113010b516015540c0d0400d04200d60700402c1010000c1c404441680d45499002d4006001960003038509808a810f0076000b08032820030b14112481000c0203100982015650000250140d042c4108203c87c0d1085810940c0b0b2040c0400c401e000400c5680c0ea03442c1c043c0941424600e0840d60070282c0e000002a002105e051160880c01144c0e01007540301d0034136151164080102d191107031001c0c055140e0082d08401100f80107085403088a001e5a500b01082c4613240c1d2140e40c1c4541040e4000c0382443d11f84450a07070001500b91000700801e41c2164501c10303050a0808061080300d2604008a02503400083c3c42d00703032015140c402c50010201c80c6c81d110b04091030b0807011520b030310402c03d09101c45581e0418040810031700204007050510b00700105d42c40716021491220007580034010701e800e100b9808001403402c1096002d6803001c0b0341c0c41400380c1443c40c4401016409400340a039424040c411b0484 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 596517877 1250 596516627 596516659
    0x20304180915020c011b08060906040c051201031104050c0a0503040807152a0906090506091203040807030510020a02032205181609051f031d0a06060e0613020306 71
    0x9402004464130001130140000060718000800700b01c60f240500900408100c407903503d01c2e058039070158003614007094010310080d080318184a40da2624000b1040394002000b03101d00408804800c941c1a607041005d41c41b03030319006440d809180329400c000b5204000042c006800340c03000d000401d00c22400021800c4560880100b03a58001c1c0040450340400d40341c210340b4402d44003480d80c4145413800c0880d1101d0030440300905662840c020113002c0c11000408134419241c03403c0130b110070900681685c0e1100e0319411550f440d01182c2c40181c4007482002074203958000c0321720840f006108543c00562810004c0c0038042d418030708420003d000078690b6640010b041d00e414203038040c3d242d0085540c0400b40740216820200010141c460002c000c58040140250b889250003a180a5030383d59001d1144080303410f04402030301030401b206032001070041e96403030300e1480040e544558500c40e00c2c040c0600741d2160347c41504010202d880550210041000c0b04c000712107980210f4100c900540300d1542c2080883d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 596519127 1250 596517877 596517881
    0x525080f160204140402030c06251e05060f010f180c11370209010522150302090a0c020303060114090301020403030509190302030a02060d09021005031501020304180915 74
    0x15032130400a450502c1017000714542446a0501200115645418611400e44210002d03808403a0304920b58040600d410074400d1000040b075070038034a0043c00340e0010003880d251342c8403d01034940b90340300d05001d4004640c01d24404441c0050320320b02d404164041c2e01c00b800c40fa01419200b4008020b201d0004a0004094010703c070300280031106194240644800a207154070304840c00d07034201c003490100b100c43e40059507800900f90440320f0843d800c1041426000344e024140952004840c01a072601c42c04955041480c00700c603003203e008598000450755004580740a4650b45038660b0f0040c1c01c10400500700c0c1d80154130340d4100c5a41c05290b02d0501900e8004030b07007264000c1e00141d0100314003060003ca5850315422401c8c0403580083c3c0070782581d141d0740c0880d50300e07105050004d11600000c200501f014240758030400003550010418525021814006002548203445041481c1c1984440d6403d80d40000f08031130407184584014103d81c1048940c80d030007844c010360700721280e01b269010710801081c24 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 596520377 1250 596519127 596519141
    0x6090c120c040f0f05030a0609210305180109032f1504050705122112041401060503070303020604060207230f011b05030a0504020109150525080f160204 67
    0x1140700c00d940c507410b00f0300c42c186207000c0d58800e0f1600c409054062210f920f01003500c00c2c02d290301180c04030740110a898084012801da6405121b0303c01c448508040c000e900da0440b9000380c030311204010900c1100340c9598280ca0003060040c2c04150702e41030107250581000311354294110110194040358411070803003400e29511540501140014100303002c14040309102c500000d00080710b0603e070041c9070702c030300d503031505e0302640c4a114100b21380f890010600d426108440101d1710503400503c0600c0c01d40703030480c0c281c1d4000f210002c0962800380041480e040c001140001d9036019002032045540380c2d0360b88406580052812106850480040000c034580140d104500b941c40d2405004006888a201400c603110f014020081c1505400b00103078154108003240e8000850150200e110360369400180c5041703285510404034400420300710151241d0140c05000e05500c54640313541404801d00704100c4011008901501d003e804000e01e05072546108010500100c20743c58001110510b84c002404079521 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 596521627 1250 596520377 596520391
    0x905210d020d0902101e09360c0315080102121506251b14060318060403091a120a0924140c040b0f0c07030210030204150921050c13021201061706090c12 67
    0xc0700c0640d108a01000c1c240bc1c0507003600002103003001d4200c45513014655000d082c035018110380ea082c0f02840e071560030490350b00400455403025000c0220058540605a810f010b80e1014814030030842d08420741d001c45411152091400d41808006d10104a480c4d03201400804480c1e0700480b8611500200340401c51040c0d000717465480f60649802188185d030303040150f201185c5141041001c2038000c190103c0f54014107030b10780c005550101d51030011340c9500d0012400c1c1c440d0000c015a03c8402d41c1c2500448101e462074408600561030741c2c0c03601c002c17a010358083c518941105101c140c0d400b08020f0b0103010642c80850807543d0040d07487d0041900ba11410783d0590000381c00203000c0c400f01c80c03035440061070503019140c010001440d01071299000041c03120741a0a8108558180c400e00c00b01300000207007140020003800540410303090f01c0e0001c1d4000c81d2800b5054911600004505018503046442440c058034894400d90b10722082107005070b001810a050070b082400703e4900740404000d030a2103465 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 596522877 1250 596521627 596521631
    0x1302160807021503130320010f051e0103080a03050c070f080d0c020a02030d03050702010e1c1116030206130b0304060905210d020d0902101e09360c03 66
    0x41c0e0380180000d0708040440e65100360401c1050201450a00c0784501250740c041ca01400140101c501f8900c440c020b80340070340341035030a180107003400c002c4c0d617404240100305034030302c800d80031074684546d0701200800d11002d0440c04051050584a9002e40c009540c4079030240c142d03a02d040c20660780c01c424600100310070b407100e600220f140c1203100e03100d04c074039040b8901c030b07000800300d2003200c0c1e002954410f0000c495600f01912035020030b040d43d00035001508418480400c0d116258050303055800d41041803100000080c0390a80043e03040e44010680e54000b11400d40e0985456085400340000c41c0d0042e45a00c82d0030103050070003c0d440442101a500541c440c140114644209003402854809010413802c680720301d4208282c0d12803c00c204445410703491b241d0160311103074000a400020300c0c85400203500641c0080049203070300d6001d21042404502d0201d01d0348440860b010807541482a40507003800a21101c00c0c0301d001c5e04171500c80700c482d43c0c0900c02c1042c2c02d0790a00021001e80e003e019040000c29 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 596524127 1250 596522877 596522887
    0x3030a020706080f04020906040c02011b0509030106060801060824180a0e030a0c030c060605060a110d030203040c03061e0e1006080c09061002160b1210050a0513021608 74
    0x15512503140380d008244e8010498032402c20342c002920402018080b036110710b50718502031480368000c0d0400c0d0756042c0003003d4014140680b460240280c0e004500c0e07240320354a401d002141843c0641c20381d0b41654520365030400c1944c0c4086400b400c08117180300000641400c00c900c1182c0341d0f100a0382480c1403c1445405072581421443e050a8400303030700440303886070024010308115580c0440c1c4c0c18000c503090b00d00002c1046a50810b01e0081005030852608070380002032804506030401458080000f1620458803021000c0c80124100e00040e5401803580100c01c6040010604a0704032154a00100c4507003103901c02400d502c0e03022140d8004106c80203812020010f004041d0b544036031402403001c280581400c920340300002e4001c05004058900c101940034242c00c095100308031102060354280342000710ba03600c48500e00034070b0b0004480c0c0a01802c410380050562180e07080c40e0303011140081d05001d10710303040c00204801c444922210190307490342449480e040441d83d0b5107850225009032506d690714 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 596525377 1250 596524127 596524139
    0x6030e0d030605030d120b04020703020604020111010c0824030703030f0f080415051e090601050a06050a1e030b060d05040611130909061b021f0e06011203020a0203030a0207 76
    0x41a12140304000780362a0034410080303501c010806418041141c030b030501302d090030a0000801050300a281940252021450808041c1c0010300b85005a001f601c0c0c079010650200e0700a801da4045821020004220701d0200e2000344800380f09003030742c0201c220104d0302102d00b41c1c00b203403414a599000b079002440c82180040b4194021003036050800c80e51815640f9403505442d80150440812503c92259a8840010300c0880c00d00c0d10078075207000b8000798050b0700e00700449901e030740d10820300401c4d11400041d000016940e02810450300300071465145c2a54209500d00142c5880314011090710a054442d98540f040740d903000010f051030511085c0020740c48c10942040401c850001c0300a1001e08401c1102500348840c155002d01240e0105d9008a170100c5103242020141558010240f01e0007821040c0032041c0e500460700307a03001d4562010701c102c00328000200c681038400035642810b00780c10000c01440710815948000381c4050103030044801d080e140303a012a2075640540450700060304000814018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 596526627 1250 596525377 596525383
    0xd020c09091b06070804050d030e040513030c060506031e0a060b0102031c05090109020616020f010513140604030c0b1206030d170402042004080c0402070b010509040f05060106030e 79
    0x52616030042140d5249800502e070302084003440e0900c00c500110302041000f29101c02c03600588000340003840010011b24001d40000c5c0c0d481001803080e81814005200b0600d0702c40d1558420707403d651500e0b405038080c0c507400001c03d009010035805000b00c01a42c901c1484005102c5114181c01d00144032110341ea0038000115522421007a0464008000a4019661101d00c5291600c40d13040b0014007038698480181c010310a00c50000e421140c00700b0040401d81c081c1c1c00ea8084123009641124041c03540f00e00454080c400c0020f000b044030f4940394280310303941c83c00300340707804170308000e4a003a240070b40300d44404035100b1082e8440b07881036070300060000449a05062594100505900511160030040c1000e0841d16854001c905a040524001415944d03640c001c01e40707441094a1404940e81c4000000c2055440f42c007c4280c0e5119000300c02015043c1403007242d641d550403025280c6182d003440f0801800807409481580c108840100c1c80021942c00c1c440b0314020050340c2c800050f51454584c09500f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 596527877 1250 596526627 596526631
    0x11d06130201020601061d03060c180a030b1b0d02031f0b030c0708031315050901060e041709060721081f0b0a02011e05040b060d030f030903030e0d020c09 68
    0x494210030845040140d07000121541174031550f0400751722003503243d0500d11a11070a40e240781d0b414800d0009000d980003068008102030b01000104d0200c0d152010240940b00801e803000030880d641500015801580240281c0c0c06c10618620092403d0160f42e80720702a40c105582040c0391144100110b405904c1105a0314010b0292401036400c41c6010151044c060240b1400500340702800000034100c0c4407121900d0b40940e600003030112001d0300744c03401c10000742000c9452800561800b6404180341d40d440c13800c07900c01e80d0700c10740702e031071380c0007900c4440070190880c1d10416000b0000f03208010002b0000300852070b14481c420a010901e40030807400401c00140541300b0406080c0210340c48035550308441d8101c0603141e0f40d4503150f5a80c49019000c900400040b40c1b001c1d415094809010200081904200c1c091409080c0c1c0e0102d0741c80745030401481302e403143c40040200d17120122030f5107524000d07000590103074041e0a0004500c0c03003c40f01c060600c4160146200142c1000802c8102c6190500d1126 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 596529127 1250 596527877 596527891
    0x1005100c030804030c03030902030a0506010608100503030f16171309020a05070204090c081015090606020709050403090b070506071814060903071a040603061212031508011d06 77
    0x52110350854401410500c0050005000c00c80001e90b1001414040c0c4c10070450340354041d0450724041094100252034020a0054200052203980481c0101030045c0140d4251000280551718140d103c0d0000078541c5d00440c1280801484000e54170081007078401c0c1d0007010038070b200100c0e40d60300703040b505654102084d03001079204a1040c01060180d0380c0c004151040540d06031000545584103041078985800c041d030103000309108a0050180b540802d41003030000e24a26001512415101c0303070744030107460040c010100160710044041024000c40d820440d002801f908022032805d444104420302588032000c1540c0561065040c010910b61106804014a281d04034114102e81803503c0c1d805c0b010ba844402e140f2500010602000c80d607030503c01b440042100355a920181180d000140069810038803035040401c1c42e00740300107803890048148a01e4580d1103c011400010030f440160002d00e1500c0717094542c0c3d802d00d00c000c9050003091013440f81100c145104d20000180800030103140c5000103100e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 596530377 1250 596529127 596529137
    0x140405031b0a151d03130302120312041b050d0c0501020d0c0c06050c25180c12020c01090b07050d1d071703160c050a060f0207031103010207050105100510 68
    0x80003160f4010f0000210041c4900080380b0101103078008070340b104202491545074040094980600703141e000130002140c3c800c0d6214003080604003080e80c0c0300d004071200502800c44500004000400060320029403060328801e00d40d99075110000706840e5075a5080440e034010340302105101e04d40c2c04211808149207140303417601764518a550361001142c00d5125660034040c01082a00c4850000d10103078280081d2300401001c4c403e00083c0c501106019803060100e9a207550ad0709055101443c005c0210721142601da6080380800b01d2040e40080d40001542c8402c1c2d50703604002c0000481d100300303890060045645007920f40490201e00c80488400419400c40a45146031003d0088c0d40410004c0c200c0c1ca90001100c90740002c5540c4604602c505228100d680b844001c99108120381003a122054070380c1516003038952901c42900741c03058501002c54201503484110300708005041507140c2200c000000d0005420700035207a4481c0d09441040d0385905030107400000500c86810840d228000b01801c510305 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 596531627 1250 596530377 596530393
    0xe01050f0a06051305040e060a0c02030703170c0d140f0703021612090e04060e011b08130827151c020708130902072013020d140405031b 60
    0x61041c0302a110b40e0050060200d1281e0704021100e1982006010190051064031914106240c40d0301c2c003140d020003914680f0400c10300c0107100101b070310b50712030307041d118440c0c3d00480540701c5448642c0140380c545c0d0302004000110102041c0e02500c480948046410740060070b1400140d81070340d4004000108051050080407d80400907003a01e038096041202a2840041078600b00c0710102e0540080c00baa01182081c003040003003603800102000050703030003085110000d0940ea61054040000d180018800801003248180100002c80006202d20402850300100d8050f4985003080d04540c038459003640510b00c02c1c64200f9400d003030401011600801c0c030707126030447c03011a400c01215045084031b0380464002c2c100400f0004441071800d94a01880f036113680e84060304040d5001d150201d03102030000d4114280d20412101c04caa030604002c0407885000307a08900c1c030009410580326500d00f01d03103508031020700c01085820f5500036405500550354800405072241000d40d039011100f00250f01c5041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 596532877 1250 596531627 596531629
    0xa23060f06101b1b15030612140f0f010b09010b133807031209051c030204030f0308061f020718090506010b0c0c010503160c020a0815010e01050f 64
    0x10081400001c1401d000e143c1d00d107a02400900568203881c01040e0103195407080140d11044015441110801c0b070b40303884a2000030800320b05840440c8a8210150b40032140c4000040c1d1450740c40d5081c0320031000300c0ea0003407050b0495905c0c0092130101003103031b0b940d141601c520702e0500d85540d40c050320311008140c0c5003c1001340780c82900c40e154401c00b44060060411204e1665070821030030720840d134481000f03800e0410110402c0ca1540241c0c01280491840212a008100d050180100140c0c00c003000c0c10292070500e005c401600c001c4070000e03040587c03c000c0400001d070040343c0c080700540281c0d00c18080d8500701092168043c04244104181c03030b00382c01040040c0c0c2d4000303045020707520070741c0c004070009a1400c00301014282c0c284008106029a400101e0000c02000c040c0894250400441d1070074150f0b0001910f5500c0240e8070150351550007041c5200b098050700d80b490480b84040d0880600c02c3c1c3d5110424248107504a00f6904141114010030101c0c03000c40034030340503003411140d007400105510 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 596534127 1250 596532877 596532889
    0x403030c0507080304140406060e0307060305180613030806030a1e151b030b0a03030206060d020a05031b0f0a05030a1410020403050a0b0916090506030a23060f06 71
    0x44001020009900034050420a0910056005240100c2200d8490392140070412409158203841070190340b901c480054003502c542900c114820003d006020658281001100603100c003d00c1c0d60115880708960220140b020000540308100b0b020000c07004420500c2d00501460003d0f2400c0d109900c5550040c01107603041e00b081042e1a407400808100d5020392402c000b01030009151540f045280080f401c004070014200c02040f09801d0303070100502d500d00400c1000c040c000f4040070b40103900000018074181881030b44e12100c1030004100000c0c4640d0381000074604102c00d041e0721758403244120755807054104216032101100c0204c4003800103905144c003003650307070050100c0901010003440c0c007064400c0702030204503011031502005550711502e0b414203d0355030685100c1256496034020000d0811403010681640d51101e03a02008501e80c0742c0004c0c0405444050409a81809122440303030004611111140c01505c1c00b0006604490ac041402d40c00c15078001d10070040c070198078040107015910740c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 596535377 1250 596534127 596534129
    0x504050c07120f0c0605090d1103040f090f110f0a09051f080601110d0f022802010c1104050a1d0f0d1101090503040801061a0a020c010c06023a02030c04 67
    0x5803400070344046007880112021101343c000034118510b4041800918940410115542e01d160703210000b42e03503a03034602d880c0c1d81d110300c0c4200d00d003109122106201e06907194112003840003240d85c0c0421400010303e040942d0b5408201c2043d9400300016075401d0b520b802c41824402040304954011601d407020051a1080090050712410020401c001405aa01900007107451440d100200c5003020071442000e0500e00c641c07051400503200d400c0040d000760904a8021004c40f0409400d1407003c22180e0043d264200020707c115405281c10072200310715182d900c1824890b05016030f0201d042d11811154441c1c14985000e03203c0581c2001e400b005c840d900c0014022900030040c81c1c0000000262b41c1c040340181007500005040340000100050700b0f00c0150440e409039040104100350325516000300c078446205000b43c00d00940c000303500c040380303560095005140281c080e100144c5024240240c1d841c00a503402c5454820300442106c824903401040054141c81e501c4240851850130000141c41e50f501075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 596536627 1250 596535377 596535413
    0x1060f0501030f1407440c1b100f050708010509150d060c020607020a0f02090709080604030309060608011806051e161803023708070504050c07 63
    0x280d10300b01c00d56420b142d00500f40d002c00c0c3ca1804e6002c1c01c0c04200144501d000f01c8030540c4040f806040110500c00c0070074800703c001920844c00b81e5040005804202c410401840b009900b0030902c4049000000125040d014001e950040c02824280c985410111280410780480852a00040004a540086100b8151401110404295906e0803810881c000d0511704041d04114100c004030304110242d0820886a4510340a640a594803000c00300c0c1c0d913441916015084c88690341c7e04130003605181003001d821203100d251050415843d15401840c240040d1021030009986003004802c0c425244119009844610000e0001caa64500e0300002140e5442014100546e100c012402a1044c119000280e00c0800d1140700342c5c2c078110b2614144440c0d0a1104808170b04000130704035000d8100d865110540382d00812504601110030150a6504414030340d01503983c541400581d0b2201d0812112070062280e08000d010090400f0240000d4a401070b01114609000307100902c00100010210105148 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 596537877 1250 596536627 596536631
    0xf070f080d26180d090e061c0f0c0906030f120f140904140106170604020f0a03050a0608030c0f0c060a0c0b10180204031e0b0604180204020c031b01060f050103 70
    0x290001a00b01603902150702c2d010f644200f1a001c03582c0c82c0c0041c04c90080746c0c1849a9007186980700814080010510380300b06241c08548a01400040ca00500e240b058034000c01c8040c3d0070a481d0300446003240d10681068441c0325485242d0001c00003035031041500f0f03088926048010105100300a08140f2512054105900f400300701d105a646941c3d01c5143e1403030b58040d91342000c0d41d50f0341c0701501c00200c180601c8055491480001c050341002d00803110740d011041c440d02d10784861494110018030340070385100c480c9601c4441c0015010010000f51051507600805030200e4458090911702d040300040002d4002c0c5010320040920b103401280c00f181007500950f260001e5510302240741c0111805070061580d0b00800602142d444003140e001d40b0907603220390035511a403d502c1119a00c00c501c2240024006d113200c070001091030130280c00000d0ac203101b01d400880c00c10300540c0050180d8000d28544030340365001183e02c60a600c0396140490100ca2080020000d0702d081005000e203004242c05401c0c10f041d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 596539127 1250 596537877 596537881
    0x50f07050102190f0506160f030b13021c06080303060406090b09060409080f040906530f0f070b0c10110913060f060e130e0f070f080d26 60
    0x2400008130241a80c004203a400910b003c203041951340b104000d41100042e0b070304005081e0320b8082e1056402041000381815490a00742503184041d40c00410914502002c1c0744840105a07031038011040508100005551203107008000d02045812640c004c5401600300081844640c45003a080750f041642501c004c1014090342c140710b40640f26000c084d244040c0009000240303035903198018415a008009a40c01e203001c1c0c0c000310608019800719504404141c02450012611031210040100e000c4102058002919107501800c0c00045a0102680d403c000c1007a140c004051100d500500310000c1f8403418901c0a446035aa41d0003805200ac48940e40c5184107110010340c40281c1700f295500403c9844102540c07800d1a003e00401c3c0304895204200b141c0c00b0507240c0c028018039045081c050f005c50820003000100c8804ee204005048526004054001d2440d040920601e0050407940001c04002d900d0144900e2030410030140034000c10107200e454000030b81465203940044a10521650865 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 596540377 1250 596539127 596539133
    0x6050a06031e23150c09040606052b0e010204030308190618020904092a14060a03052d10090c0507110f100f09120321110a0507050f0705010219 63
    0x240080394003083d600c00d60030017403c1c400d503400418407034005840900c031103a82c0c2c41040e145400b0701400358602c88000c1c216180400c000301070050b610fa07035283d404600d8010081000c0d00326400b0303400c01d9001400c2401040800d507103072a200003801040700410803140f45404070740c0884014030000c6040d0907400050640b12903646402481c005038000915007400102007a03004061022241480f22404c0e030b4030303000a1754241029005990660242165140111644c0224010f01000b4907101c400c4114414101b9548203a802c543c030309003c006180032590a0202e005144e40f00183e10240e00a410700701d00ca808240c1c4007099500840d03200321300c0740d200c040303820000d01d00c49103101485420001d0b00000d214001e50084140c0449812a06c46000c0310380c42e00c015040c0c0003c40311000e004240c0b95910038201403050b1440e5003002e00b0315100020002066901c15006601048070803001400100361a001d00400b44289407224400c1c1004000051603c80040d48610120120f0000003801020394414 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 596541627 1250 596540377 596540383
    0x1005120a110301091a011106060118152001050106170a1b0801060311040f0e0702030712023d020306062a0c01091a130306050a06031e23 60
    0x100d201060070580b41e6031141e0004000300f03020240f42002e4110f9210400c0294051031103035400020340d1010702043e50316280192501440e03140d5032801c42d01c84100005414100003090880e202041d554031650035203040c1158524100000d60320101d0741b4003030042002d0390704811031744803648941a0703101480e514441540c004166030f6141800341107044d90000d6155902151070360580b07200b03403020801b40c1818040b10b001800b4501400c01e0940c000c9200f400010400c541c080e5001e14544100c070b24154041e0740300801c00c891080d42c503026a110043c44101542050300d001070080300481d02450081c0210400696001d10402c600291940000847c0243e11400100c0d03400d5900c0703c1e401003d50040c4c00128016400403800e0010b24001c944800b0003941c07189001200700d49603541081c2d8030015003d4010141c0d03001440481d03242d2045c49002000500070b000b0288242c80030513001a032185541802050481014606281e801c440743c000310020b8500a1340f0841d0708800351310010034443c0035501601d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 596542877 1250 596541627 596541641
    0x70209100b1c0b0904061d071a0c07050d0302070e0c07020d02330403020f0103090b0403030b010e2d060a050d150506520201021002040f05030106051005120a 69
    0x44c00144410411061208503003012085204848800034007a00740143c054846030076008201903070701e511007009003056680703018000500c08401031365000b50380c0c0c50018103055800c840490158110700b80070854081841e45140e402050380482c1842c0c0f58940d8000f032803400c0080c1009105c1e611404000f223002c440340c803600d1038030091502648102c0344c0440b54080c00b90820b12007284a9203240b030300c50b9101d5100c0c0c018418500d500203040340e100e8540390b0301a0094050110114100a601c40200c405540c4013040c00842d000810070080940d0668115509000020711881e405003030100b1000300034a074840700303c819846005400042000d010308500001070041d030f025950045002c2032910945480030344412281800303940c0220141e1002407003000040805101c589100015412004540040411158101e01c1441954040544e0308413a030202d801c039030400054210f03085400c1c03200e0b050901c51440513120403a64080c4400c50454004c05501c15600900054040f00c2c010420320038007504804 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 596544127 1250 596542877 596542879
    0x904080306211b0906030a031709100507090503061803040b130308040b04060206130807021002030c0a11031203150d0c030b040b0a110702100f180803070209100b1c0b 73
    0x4542d0700340f400b009003144141001d0079100d0011200032410754500022030b400b2540d030607180c0c0140c840b8a603a8603a0312220090400c207081c003602d10352a03a8442e0034494188a41c0e00c640701c901915040a0a2600d40741000308801c2400c6002005503801e02000815a01140e801c89107050303990714030011000000c000340c2d100910300c0c1008540480c403000b01c14090400d44641d50b0841e500c1c1c0c1d54807202c0f002180003100d805015100e081080c10054244100341040411f55401200e15101000c0152450449001e5054035103003c20a9603e0b810700c2c0c01d001c00f04100010300780c124114185214400300c10000c000380e140c40786c00c211050404202d0b0040d050300013184c1208c030004a520b042d040c504800003040f02c1950399035141100d84924150070009494225401070725920080120020694034085600010001d000000d00b0071000d85180e900346030090700c0580003460302c5070400d1040c020036800180c600c60400481d00f4050043c2c0c0c181c0d00950341316204a03079035202c20b40525450304009080300c007155 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 596545377 1250 596544127 596544133
    0x60c0a020a0b0a06290403080306010905090f010608090c060d090c152d021b010908030a0e040b060406080c09130e060402010e0a0b09090a06090606120605090408030621 74
    0x45407088150380500112a501c05450f81c0d880405d100d400c4280c841d011030041403aa05000c1071001c100706c0c401a6603c080181407088800352a500041d003944021036941c1995441100140500380d444003109400c50700d440010011208403100244042c000e4805d455001552082c62000340001540c0603c014448602005180845a14000c164481c1c4001001503ca4003102c04e81c0724404104c04003030350341d10681c00791800d0740501403138203042110f80901c20b04114a046001c5000c1d2410720050401440030740341c0e280d441d100c1000b4041522241012944075004c140320821469410a078415408160030001c03590303880314040001e07070742d041c00c100c0700c2c0c3d20034502400c40f10100c600107901c1d070040d8005d88401f01d02d0350b20102005010b01c0e40d8010500c148200340405001c600303001032080e410210704140400c840d41c40b0a40c00007190400e9001d8000205064400032100c0114401e40003d85410703103820000e49820740741c0344c6952002411440c00381b2610031a40d0320800c80c3c1b10308100010055400e0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 596546627 1250 596545377 596545381
    0xa052802100b150c101d07060521131403041d0408030106080408070f0f031b11060703170f042a0b09030c090f0106020d170a110d02030c07140f060c0a020a0b 69
    0x10b10741848080c00c03469140340302e200d90100e82303180150306807a80215800b5070003028444040081c0b030781c0c10303002e0024a640300e4682d2004000601540c6e080240c0c070f1061006617190744c07401054110202490440d21400c5a4401c1800007144c1c251040303a0641d0340707508107100c103a250f9103482c0c0024811040060582c0c02c001640000f004407032000b4250060007a50780b004d0380e4890b60045140340700e103201d009000e03c0c4505001203890800001400c4c07514040e040c038404080e02c180003c501d504044032241d06407004e04c005c210400c0800382c0000052aa810241410065102802c1c0d00342d070524003500b01210804500c1170b000c1d9504004100041d03001401c5a103a0381003610b49607080403c00c0c01110f0141c0208401c10040a205003180781c0b0004080d00036041d00d494922a45000b8165010500800c401c00c0011383c80c1d820711400190b0140ea0044d045a5031682a030414101c00550485091b840b0303001002083d500420000301c094010594030f071f21a60300d241c070440991401c2c0c40004014245680c20017 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 596547877 1250 596546627 596546651
    0x102160e04020a08010507021b061c021b0304030c300605040209060f03280506010f0305070e06060715020c011a0f010c080a03020a052802100b150c10 66
    0x18003a00a901c01c0e11080501c1ea100d80e8001e0907160200e0301c01006a00c1442c036000b041384100079540c0d041c030001d80440c0c0f500300300d4040f610070060402c080c3c888094000801200242c1c400440300010741b42000a58200b60465607400d03143d10b09031040d80341407004140700e11441d04c5440300501460b886628006500c0416140100252504543c180c0c0b280807410b00181203800c1641170228100c10050280011000e19444c02803030104001c0c030140100110200000021420006c0314003811404d40c1c0208414607615146240c4801a0040111070801c0e41c10701085450700020f0740c10055019a40c0300c882003400400b000240a540c2a6200d550300342080f0821038541d503017040204c054140c0c2c801d101d5a2030b980c015502d86060f8003008107008010040242c0c1c6501c00e40c0034100070403035481c0442c980411003d1218920740f86c032a440070306d200c0c84030030803010503010801402c42c251096024801c2d042e0010005480d001d400c2d40c002040c2000040207101d0400c01c1c05103242c2056000000c00400c44101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 596549127 1250 596547877 596547899
    0xe060f12061005032205010b0a1e1a16020102010e0d09030204061d04080d0e0d08190506101107080a0c0f0609031509050a02030a060f061e03020f010216 67
    0x2442003400780000c203841d00c182c0d42c8240100c80c460080d4911900a0b42004907412458404c150b00036546950b03200502c03491a03486006510050501c02c00c1b6823140340220f8249010f408040e070160303207014140c00c040d07004441210240c4403102e03a0750501d124485001d00060740500f1100c0c60040c5240902140841140e401100c00d4054034000c0c0c40c100320725a107400ba292a28081e0f80d4841e2400b8a13018001000101c0501c01001c8840c0580f0b030120740316850030740d6185090248500800450080020443e0b409001510b18060b24040304c814061810100c011400c4140000e00200400c480c80641c0e1420320400c0200400904901044904c400c401d41090410340c0c0d154014105010000080081c406226080650503a500040c2d0000850709004212008011200b81180c4e0be0080c5a415005030ba8188180903a4501030117012030381000503252034003160303403503000000038004000c602c030b50b620101e11003001680c0e81920360014004101d80103030303d01038150350300804445c0c0100e0003090058240c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 596550377 1250 596549127 596549131
    0x30804080d020f06151302040308030a050a020a0c02060a05130f03302321060a0b09090714030103240c0c0f020609060f030f060609030a030e060f12 65
    0x35600765000000081c4040381c480c4180010210303554400c401107103100408184182d6001c0004080780300410700440d503003051341c200382d0040e030f4904404002c1041609841c0070391544011004021403400080c0080607204142e40d40d00640110400f24101d1540c1c2e01540840d00415074520200d504295111050840001140412500000c0d01c0b044014540e03101c16510101d414401e10078038509800c1c00d412506107070204c50582580c00c8480003140701400319401806210042c90540100c1c8040d0b4007040031119020701014000c6402650800200c103515055840b5000201c8000c4030540b540d40c8103d0340964030b03003003000400c0d000100000170840380d940464958180c110011340d188083c4840ca40494007000b20f40c0010442c08207020000600c2e00d45c0c5246079900c0188400d090495030000310340c40c7e8110340c2c8130400c0000c0c00824030199482c0d030034410703500c2030707080310b00c546400141404603440300081e10707004052240761044c49106507100b0082c1d64140c4000c40003541c89030307001030301c4e202c1f03886c02 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 596551627 1250 596550377 596550389
    0x9131109042f07030801140a15021b06160807081e0d140709121a0a09020a0f141c0f03031b080709053102031b090108150f0406030804 59
    0x342d41d003000c007604007940075580c8890301a140e00e01c46030301e00110b00b003c911101340d03a181e00c000344000204514405049400f0407a0b02030380104070751400100e04031545c0450142d5903100e98018050800300c1e45011a00d8540d8039400b1403030607103404040c40d08407014000d00e07000b02e441140c0c110510f8540800c1d103002e44a060300101c0240030b14a800751010a01440558000000a684403028046030701501c07a0020300500c02c621401c42c410029107031440209041c0c2d114400c6d162203d440c041980b8007004400003404080c5034260181c0d1034109510601c41607004040c4c02045864482091560b030050515640c5400503d54000b16945140040c024004a5000075602c076900d850058004d2250400a11810135a114159400d04080802c6051185902c0d6800e0309070f0028282291102141301c10348048e944208056203d04001c000000c1c00c88028070001d01c440000e12054000740e070322240040d00080600141c108009820010501200c0400802ea401030b0910b140002002070703041c01002240d030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 596552877 1250 596551627 596551691
    0x100b130f020a020d0807091527050a0807050a17120705030702011215030303051b040807030c05010c08030c03060a0503030a0f0f02030c1209010201290f060913110904 73
    0xa940f0384145d80301c1d0400e0f10064005882014140400294101807010380c16150821410817a2580011802210036250f141d12050100382c00704440c1c281217008402526080003d40000340c02c20002c9047c0c1c41d0340344110107202c5400051400c2040040c400c1d942c0c0d105c03100c0b94882e0342d20034500300300c0e030f580c0d024403822400120b01c1d2208200050044c490301101a8045041503080b503d1501c086001d000c01500d141e010440c041c00303d00c0c50004040c004c20081c800320000c0c11001d440c0d400c010a030b01c02d1b583e001905100c0b030340601c100004c5401007100d82c020388031110540c60f515500b011030114002030300202d4161100080841143c0d4000c01c540d0b000c01115601d4408440300c3c40e0080743c803030291104042072540300c56110f440880c00329000e84803150301840001002d80804490079842e035a1030800303581100203541d01e44290b0400c0203201550142c2954000e18141900006c1070744405540d0503c403906540e005881904070340c8a0407151f440700018401d1100142d11040e40340503109040c40035070020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 596554127 1250 596552877 596552893
    0x170a0c020a1a0703120b1e120111040b0a03111b06010f1215091a0109060b03100b0a030b0919051302061909120614090f100b130f020a02 60
    0x24000c0034040721211802c0703100e42c2030410603a0706941d02c1c46501904942e181c5c44441c042c115407034031801781146445104001c01ca20401100703000f5005440c0e401c409159060041c007800c81d8850b20104c508036a5051500b40d602d148840c41100107040ca2050200715000c00942691502190044401c1064050080d0b44081c0d80c0e8000c0d600090072944500c021340d1030b200e9049800700740c00300403159034001c0e605004214000c1d81d5483c2c000050754143c007100c4203041000140700780d004903c1075002070401061402d19504010b803507102404c5052203100f01c1a0760020318902c0d800e1098010707062840001c0c1986c50310f0300307000212944c20344082140303015040ca441b0009005424021001d64000d03005000680342030307025039242420046203600707802841109000010745041ca4082c00340c0c1d0a026000000d148004070001200503100589030b1040340e0300604644686040110366110542422080000c84140704e6020407844584241541070781441e02c2c0ba440c44080941d00107004102c0307203600f0345140f4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 596555377 1250 596554127 596554139
    0x315090603230d03090204020c010203070305040b0109090b060409050f1c180e0109020304031106090c010f0e280f090c2309061b030a020109050c030f0c0904170a0c020a 74
    0x840088120a0388950212058890044c000c1d03204d0300f4040d0010300b000d850040500ea0035030a81c6d105071500710010750358208000921486e030007514090240c0950038403803660291503a0b09080400380039140f095aa410300781c2c08004082000c44440d20003041991550709800681d2102443c46002040200708200b8182c00181c82c00300681041c0c40800384404141e0342401032a030001d4100900c114140803681c112424040360801c0300031f01c101c4d4030b61300038082c0502030b0700010030030355119501000f4000f01914800c00341e03440d100d86165882e80404030340b00401829464440b009156400b6103100210300c000441c114240d60000f034201041511400480c0520200b0358072020031000000703452100500003c101e03850f002c4000c18001069028006481080c280040c0c116030100c8191400b40c0c1d51600070400f08101071040c80205841100607000d0140c0c01c88840d80c82d00950019a0304c5081600e000804001900d0003086142d080e0182c15901c40954800240480c6003803103084e4400c1c500c0d0030000904c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 596556627 1250 596555377 596555423
    0x91e010606120c02010e120301030501110f03060d1707050a05010b03070f090e01090c0b0901021b030a0f0212060115020c030c0a090b010e100e1206070c0f030315090603 74
    0xc495940c0e84208070782c006a80311000500c2092003220455481e8018450070303501c100104440800300380040ca590794954030f005401c5440381c80250b8211003007408800c101c0c807a41400c2c0e035806403091383d5422a400b42031501c003407501c10b5000783c1d600c1680701042c92001d0010004012002030b100d42e000300304041c580420550303100c4035403013108030600c10711500f40100301311034001101da028054008901e401a65850450408041d00b240442080105251110f0340e8104640c454925540d07500416500c00040825180c032940c5601512650b04400742508540b41c0c918915005076102e4103840b199610b42075007046882038401d14ce001849030310910440e628001c54176522000b030090040e94568900380034400540000c01c9540e0510080f400c01c0040754071107081d9010704200d596036120000d590101003001011000306c0001442c0d20440800c00100d41161128840340d40142d180d80341101c5070700d805c80c00b5107403514940b00a803000c2c00001134143c1c81904903130140c920482444d401c0c0e002884003507031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 596557877 1250 596556627 596556629
    0x25050c060f0f0103030c080408030d02070501050f0f060402090117040501050106020706170117011b2601080c1c0503190e12060105010f090b160b13050d050306040603050105091e0106 80
    0x40c0031002e004200180c02150a0400c1a00c1540c400b420306950701d50150841e04000c11358428641c0005040082003400c0c03003120340c080340c04101080103040800aa41c0c1860005040c0c07400f40764006030b484440d0b8010041800c00380740f5644e49800300d2400e490072602070a004c1c82100050b120b00030005c203e080c0620390741d1030211111200901c05a1030001c07910740c050742c5002c0c4200b040d560780d0502c1d480c1c850b00d01085149140c46854042c2198161104000b189800840030b00d0380342d80101c014009064041001c4080b11021074945c141d07203840e03030769015040c401e90400406500c00002c9c810b9a078144102c214100c003080c0c0d101e44803405200c00074000354004054442c21203400038401401a5030090102c512980014a050b100c003c0c2c036094091020b600090100d0340e0075413400300d0742081003508210281c1c0700100704030038015040d6541e603965966002d02c04640c00e100000c000519a41c81d03a40c00040110f400070028041c904103540d102ea06c80320185804009030394010003111002c0014002c0b80 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 596559127 1250 596557877 596557891
    0xc030705070303090c0b0c0615030d1409030c12010509011406010516111003050906060a18051f14150307020a02120a080307050a090f030308010b0325050c060f 70
    0x207031400c1c0440d9012001000e06420071201030200d0b950210700b0740401d902926250581c440103002c6410000710605103170240140641c0302ea4003501403044110b80c090003540401001380040e50716500100d000030309000b2501c00d110b07004100040c03e41c41e91041504218010b061a400030031141d4904029850002e03401c4602d03a010480801c03607030324070608106202c443d850149004441c0d04018100207550043c0220080c1c000a40310420f2202c00b240511000b60441c900b15001385550345000e4218103807116140300541e40d107a842d00003641100b40d141a0801203802500d82d1050283c44000b884004940b11525034018805410003031103401150341105d0050405800602d203d0140398204900341390341c0d0b032007100e03203000f9210ba4070000f13000040510300410650725415201e0a002c0d5006211010680c40440300c0c0c502d01e40704101183e0404155819501c076006000d54039034134002c00f142c5c1f81c1705181080b82c0070402e4841001c0210791000180107680d00398000d9415645601541d8900000c0a60b012 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 596560377 1250 596559127 596559137
    0x3070b071d060a02101112010e04050604140309150a200601051203120403090821030112020303160302011a0307050a151e0c060e03161203140c040801050c0307 70
    0xc10840c581071003d0039055045204072512506029036240555801a007610038050003c207890078444024000d840c003508004d800d00d05580b90585481d640c8083c05400541001c3c542c03030088181c2c040c1401200c030740420150442d011603c0d14456100c0603806582074a0002c2c00124100d807961000c2d412017061604102d004200590a04e401c000e203000d00129030355028801000624080080d10051521450090702d8080d986403410380c940781070100900c80a0011803000945201c00400001586d0559030700240300d0610441d030340f002c20315501c101400f40581d421104541420190705401440174207103901e01004205d2854418940c0d568114051142d0000310001e0500040002d030740064100722035454122010b0181c01481d44a0121010426000608021030742042c0181030084480141ea54801185082003c20642c4102040381200411904400c0501082244a600101e41c03030f8115002d1910241030102001006500c640f0400c1280e500f001d00150314400aa01030b20300c507000716103138 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 596561627 1250 596560377 596560427
    0x3a0605040c0c02060c0a060e0c03150c0a08060a0b030a0618020f040902030a020909010329010e040210090b0417010b010c02010207030f02040207060608010f1b09060c1406070203070b07 81
    0x80140c150406010701005c0c1c410805c900c008154035005001d0308040b03000244c000d0500c1c800506081c0500120301d91003541c1400e00b4000540c0c260021107800303881f03524140c1416180d0500280451440d0350002d08800404414080d942c01580c4c002030448002c000e2080740782060781600d0040c0e0084000302c0303100b840140810019034000d034005541c003800410340140303000041c000240003a1001c0e001038920391441800010718030f070a4441034000d01c1c0c909184a20540c9401c506000781000204020301481c0420311101c40079015010500c05017100030320b905c3d251034860071354104800b04020300146641c01c100b02e095031940140740c112051501a4050110030703046482d0120b450000400803604140e0070001207020582c24820000074151803000850320840b02d030311010981e96100304040b004a01c422101e003026400c0480001115400d01700000140b61a08211001d903c48000c90072460081d8403c0212481d40400144032480c80743c48084140d4644810454203040142034907400342c00540c0c9 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 596562877 1250 596561627 596561629
    0x5120706080a0204080715020c1f0309020f0a172506260412110106060914010309060603260406050322170315061801053a0605040c0c02 60
    0x301d9580650300b010003503d0a40d48405032860a101e41c0c1c400b01d000b10242c404200c000740e040c41400d035260f0085800741e2000111503204040d0b4507105019006050f43d400440085484811010b00d10b020700a21190307403150703191810030025400444500d07490103100c0417503492141400304402080300300e84500e104142043c0041d107540503032141c4081e2444056405050a1030580302c40c034400da200d104640141c500d0039102030240800600400426410b02c0303000c0c0516648482d0780d00403a07d0540d116002403a41c1401a4000c2c00c130b14034050555405d118022052000c68810310070701b00400030326071140042a4884802c18092802400002030742013001c10b0210000e010200c10421030848400c40150740c580c0d50010a008912500000060200c1040314521820100c140c4e030840c1650b809187ca5404c412a00c01c02501c44509418400c0104040f0325541440c200050604000e84100880c01f1a4914884a90000d86a500002070034450041424205405a6465003490740c0f1048031900b40c9034 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 596564127 1250 596562877 596562887
    0x5030301050d030908160501110a03020a0303051003020a0f0509060a082e020a020d1404060813140f030705010c0c050312070e04020a3203130302011103040b0f0105120706 75
    0x10283c0400c49684c038003045129007408a81e20328050030240000b00e074508400034007003804000c001c0c1c2c001d42140e070b03e883c0400e40200764680e6066151400164a56a1020348515010b25420182d00815142c4c404034072029191a0768040c1d40e81161641038664801c001c011403000540502c104039080b405401060390088c07168088410303030a0707109414264110302c1040407a0002940b02c00113900c403510001359503400081121040451030a000e103054200103020b04200320241c9580c541d41c00a1050303005002422102c00400d80040042c1c440140c8454121503880c0c0000000f0f8901e035181c40901880035005003090b004003584080518100800c0c4012a011958020030030418440b58003185003c0ba59188000c200c001ea042d101e080c0441070780c04d003603010281c04410038090b00242c2030340081018001c0341034036401350301c1585170540c80e0040d180803400741003c14907489180d0008014881048003492525104200c5120340c1c208681e40c810030481c1e103800f18544101c0d00e811858041c0320441c8a0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 596565377 1250 596564127 596564149
    0x1211070b0609010b1b03070605150a05060a0e091003050303040b0103140d080a02031f0609081209010207173a08060f060d140f071e02070b0d180803090f0a0503030105 73
    0x61021b490819843c0d4584600380c0d0340c100d07060442e100b03988500c05103038900501c0345c0340600404c1d01c074282800c4200b0005008031840300303040e42c40b8101c8880050211010299020082d41c1e225060700e4590038203241002c03c0c1c0c10213020407200c0d10105125a0a200380c00203010f00c03107020564842581da2110700d002c000035440500705240b94050034480306541400d038120400213005070307038a100405150889046c00c148080c0e07440000400101b01c1801540c1e8000340311030540380c0c160004480640711507040303071a04200000d12010300d003040044090300700c411440280780c85215401030460b8020448200e50030303001111210307403190319a0000459424141c02030480110038250000c0c1d05491148002c1d02da43c8122403041624106030700700854503a210030306103000d9030002c0070f03d0180c400729400a03440b0f402501031070f91505c02c00b00c0c0300600398403150018200c0c40e1604518000350404d5051031170040c2d0080b00c08591038800e0311050140003200081800010382c001018606690070482008810511 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 596566627 1250 596565377 596565427
    0x207060e0703111c2d240b030a050d0305090c04050f070f080702070303051e0c0106050306060a050607110120010f0b0904030804121211070b0609010b 66
    0xa1140c6150420508211100c003450241c400d03400400e10141c20400341202c100f83c600c0c075101d4100030300400a84400b0582840c2c0410b600b07803001e8446201d41d00c1d01c5568190300060a070b0403980200d4890010070300076145034044101c2e0306103c001c400e00c040c140d03600c1e40103d00400d603074442c4c03035100c1106102c0d512241e005010002a034003009115400202660400e854000340c45855600303003c9119007003050180000c15504020002d89858170002e900d80006110140520200094000c041440c2094211114112004540d1030b0707102e04180500070710041c06814064481c560105490f4074200b80740e5411a080140018a0410f50369143e120a1000e000d11038188001640380e2603036240300741201c0310700300321040000407070640c0e110f00141511035a0727813020302442400303080c400860741c42288039900a800a0608803541a01c503001c48102c48140443c540030f526114501010064040040210501500108120fa05c40f10104140e00d8000c0c480e604548200f0004100b5060103206009400c03e0707 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 596567877 1250 596566627 596566631
    0x7050a050d030c14040602061f18021804060b0307110c0414070909050c160614010b03041104090210030b0f090108100f0b0d0b0c160b0402010210110d1505031c081e010306020706 78
    0x26480038034401001200c22b000e0004e0380c02140041c07414144849112408070101c4e010300100d403802180e02503c3c03101802070003c200030b030b84001100351310420480300b00402c0a4010031102c2800780c2040d0301c1c02c00941d00f0724000340e00a08009151107050007a00e008454801129140070340320b810212210907003e83c2181e42c56296050310a8114500d106e0500a0030301c070040c160780385000c0c900b140c0c05000140d05248118540345541000d40c90b030301140410b61566080c0000c0c2080b503840041d110030201d20311030303a00c480f40790004201800c1c0800c0c501341a00c040041804500e400d01c5d903510580e1310301458580c0005080580710f01180c04c0440c0903401840c01800c1910702841d0020084812407018410794440010000340411543d040000c1504803400380070070402d000300e800e00110350f44101c21172501803d0300c0f00403c030280c4408905100c002c0000400305c49148580e259200e0409103146a85808118003000042a9001c09407a1003c0300403a03000d004051b80c00c40e84c580c4001d407c1601c0580e0266 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 596569127 1250 596567877 596567879
    0xb041101021b1c05061510050f0417030910050a020723040510090c02010915150933050a0608010303020d081b12220b040807050a050d030c14040602061f 67
    0x158248802d80c084c0c240c003400d6001b0010040c081c0b1101d6a804103156041040400580c800540c00d001500c095480c05d003000801200f104840078a940150180c6503486810404200c1111b44c0100045c03a80040a4090755452965550503a10140d444041a41c501d684e501441116181a6202c0b580c42091544021801030302c0303045403401c44d910b8492200c00360b9943c0c041309051101884240d0450b002c9074400b4055903040d00d81e400d9501a40348280000319845152045989141800c4003102c02001c110b000f9941026803414110000e040c459a400340400c0c55001ca10244247c01d06410791340c1640080203c22011350044400c01d4000b00100e10062900c1020481002504010b160107404908401d40905007040c1e07000c1c84512102c00002d000d800d2612000000e020302254661064103c1f05050319111103007800c50415004480c003c1ca5401500d54401c98141c041d803204103d03110075034074401d401800100a000c0f6100705d000c1c110169119071300003040c420345c03854000d0010400410b103404103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 596570377 1250 596569127 596569133
    0x106030b180105010918121b1b080c0916210f0506060915070510050108060403020d17150d1209050306060307031a070504030f0b041101021b1c 63
    0x1003007610105880d10300d401994600780030034080e076409800c0f0400d04100f0103008005942c0c090b01a000002c0c864014403140c03940c11030090440201000c1c2d444c916561101c49407070078400c00060080c0d02185400740d030201041100000601200b2040003500304180c0d9103404040303807601120041c2c190108069410381c1485045c16080080b0500d03804030000c07418030000580d82041d1000203003250300504051011802c942e076060f1024400707805002150707584030304a040c628140b007180c44802000301c0c28280000340c1914005601d502c142e0099081c3c40100d81c01000413284545e41c207082207000f000000100c0c0800f40a480310100043e401000e003032001c600d5694545c40081a001e95501007844140100024142403008560010703044001d01581ca003141d41d4040c64450310502c080f2200754072000116402e000b0f4046038083c503009020f4012002140c1b800500f0780720206d0b401c84120030300200b50402540001801c482e40203070f0f410100207032500c1c6414061910a0040341c0c441035401211b400001c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 596571627 1250 596570377 596570393
    0x2130920031f030b04020f100212070305040503060c0406140f030613020909090304050130020c100e010501050a092c011d0a050705030601031101031505040e070611030414040509010603 81
    0x1180304001d802d642d49806c1c01005401840013403002d0068010501c494021540032a080000039025130708140c58944c0c1c1d06046809008a400980d003620405050104000c94440038200711802d0765140d40c2c849100c444d2640903130042d4a44840d04180c02d0021614a10b032102710004801485000181045500c1300040c8030b032201510000041c0e04000b80500c460b50380210041744156546140040c3c24500601400e036171016210041c0b0310741d901042004800c40184503007681010b007240180460101000524020f00081c82031a00c02c4414640001e034001040c0519030b4102031231100340b003404c1c800e002007029583c4d9000b003003c420b56a45016068a0f4502c0070321102104880c0000e000c500201d1a00034a4a0b066801851207544602d00400024054401302040018207190229103080710700c540c0d2120a000c1d4101da5402130401c10301c00c200250005081d411140b507035540d10640040d10030100d4480c42180246180c0503507003500764885040c1034100395041804280002616076803510b501030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 596572877 1250 596571627 596571629
    0x703110a0308151002100903020a0203100507020c0a050d02130f020f04090c05070b0a0c020a080a0806011e050405041d030403080d1b0806090a09060c0302130920031f 73
    0x440c2c00c40c010711034004000f501080300b051050354850586150214003031740e02c000d581c10000e603054541c0709410404d8401d110844c0304070760203421210034a5110807551b001c0c0400310750003401445a404440000e151001103d012110f0240c90a1074001d859000c0c4070306400241c41c0c8000705501c91040c5d9401c0d10307562009111074425058016111414641150251a20705140c40100007080c8681d401003071500d02d0503900324180a80004541b445060141c2c141124841d001e03000702c6000c03c07804c140030b40003142035104070026a07411a414800030304204081d0685080b000003d6400d0105000d2070a01d13600c015413160b44650203160b07104c00d00050705e280d0341c041c0d0012204d01d0b03004107800f1030844040c011091450241103514100e0310f0001802400890010140345c8240c0241d00400d00d0074140d40c2c4003240d020340120050241c00020100600658003924440707440007203800c000580907a0b90b20800b0f8450784d40502c80c501c00305070481b1306041904041c002071200c1c5e0100031800c000c0c1c213818040754 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 596574127 1250 596572877 596572883
    0x30b090c040f08061b0a030e030a0504090510080d03020906070507090b01120b090a1e05040309180203010b0901081815041728050c06040c030203120a0507080703110a 73
    0x36a440341040540c5105003416800b00c02c450f80520705202c850600c06021028080740340c041c0720303190000ca00045001d0807142d020407049000003d4102d581c6a0b2107001401a41e805120610454685d641c201710080403902c20500350f6004a940404564400e070001c001c071000003030038941444a541c8541e41031070143d61140c1c104a039910003185203940c012100707072486500c880c010032003503a2031000b0aa003401d0081075111815036451000c1c100502c501303150740e440410744c24100300918252074060100786090041c0280c41c56145100d41c1d4031003e60088a059030030b26524141401e000c48015292034801415441070001040605500d00c101002504411000035040030058102400c002c01c00c11380c0512410000c140401254200d484462110000801c105510680d509203101c4202c50300c4c003075020000814003480c018841440a0542202d003640c3c0200c0175112140350781580c0c0030a621a2000707440200f00d09011005c0841c1d85c0801518121340030341041081c07146000030560411041920403 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 596575377 1250 596574127 596574151
    0x1514090105090106080a21031404300207050f060c031c0f2d061d060906010206040f081606020d1d0102041202120109020909150f0103020607030f030b09 67
    0x50b080c2d01340502002025500090a803110050701c407150040e2007e0004c2c09202080500c60410a01c0f036449001e661041850340d81003401d0510702400ea40070207402401034880f28a0240c81c14410340c504521946581e43c00506c84145844c00384490200e01440156102106002340e00107680140010944189030004036070101d030402a005080f10002100e09154500c1e000d940d202c285448084020130880900d814034400c032540110101070304041e01310311582d1401e900d074080e1b1420820f90f170b54040d00c021584034465582c0c00004903911001200c0203007600c058013203401e000c96410f000505490008031240081c4020039282d90f01603901040302202c480b80d80d0504100c4819062540801c07106a040003540b4142c07520001d0407889040d40c0001c4d2082000011100405800354001c03041c036036000e041c00c1e0707103803501b2100700340c070742c51001c40b10041c840c225400a0302000300c041c6114140c9600828660030000303e601c0469002686541507803e06551303407440c540564480030301034880e034018950 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 596576627 1250 596575377 596575381
    0x4051207080c01150b0a2f030703091a0a1b050703110906010201060e06150415031413020a26060103082a03160503040b0f030f060609030a1514090105 66
    0x41a007180d400c80804c4020311040b02040c03080045076021500d042a01e80380c408540106180300311038002c1501e20448035615001c0041d4060100032004d00f40311030094469200182d5102c103401b00440d120288002c8046040040c80c0d4010b015000154141040042843c55443c0c1e90f030f16185020501d41003a5005003460406031981c1c43d2034a0303034550000c009e100031f04c40207182017900c0d4490030b0050502c600c112840321001104480082c29617000300b08075140d014242c00e0b50440500185180007070200302d41c03007280018800a40362440801e050b940503041400c039614085041c010000d910040406c3c003100e0802006000c0c5080065502030b60184036030a6031040c0100720b040030782030308a00e05465404150781289080c9008020f46800f550094075500e00d6440c03902d0050b06510035070304601c140d04800b042d503001c403016100256100e9114480c0c0c41c00d050711004200607103800b807494006e5166001480700701c0081c0211003214800c01c003038030300810a6a001440307100d080200700c4156415039500e4003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 596577877 1250 596576627 596576647
    0x6190c1d010f051201291908070e040212060a240507020a0915050102010e0127051f090218090a031206180905010507080103030203070b041109070c03091e0e0405120708 74
    0x100c6d4240c410102041c444c60110110382c400910b00032a8140011b00000c1d40010b02401e0007039a880b0008040180300319a104514040e40702c0e40c11050351742501035644c10320f0104070f44c1c140c0e11101d0461948100525452070460710304a603180e1080d2012600300320844800076400d01c3c203004041500d40a030340e2105c01d0b20300344400242101c481c160010071683c1030a10b0108034506588a5002e201007200c003045800c3c84a04046140c0404a000e24030304914110020088407085e0340800300852085904200c4200c801021039418901510122265008280c4010010b40603181c240030304000b050b404039400e5a0341c518058010700340c054498016486003160010020207228969201e0b4507820a02151350554500941d20301426500502e41004071001c01c0c00d105128000303c032400c800030194800c61800041c0104611145541100403c410080219103001e0780800b1244414070003180d8541c1626081e200e041d50f17a4054010384944c014081120341000e9140e00030f2030301502800c0c250b582ea100c814 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 596579127 1250 596577877 596577929
    0x1e05070e0c0918190b0d06020d150f0602070602010603032007050306090102070204050609010e0c03040c09110c0d0f02030a0c080c01020307180905130b04050f06190c1d010f051201 79
    0x180d00c003608140b84c0000e140c0d0300d59032645c001b2005c41e0480343c016104c0758480c5100b802040480f02100c4041e5a1040000d126045190803205540c00d55003a1604150790f908140d00346d407001e000081c0840c2d00070008400d00c0c0d0b001040426020b07a08012075022940d9076010a09040007074031210345c90b0350000798000941c06d183c01400d0b00b10070151410946507140580c030604131030001c0c0103100c04500c0080420140650304244901510003030f00c0802c401c0c0c6140100c1c1c601c07944014242d000758000c0d031028240e0640140d0000741076400680140d0f181c0605403808681404000b80100c5008400f84100004600d0901c042e5100b21401d4072102c000e0402c0220344c1c2c50261881e809040300504081c2080401e03080300b0101d8061307a0b4170800300902a180c51410500307004d043c1007a541681f0802c010020b50301c03202c89041034031046141080090440c20401158048411104000400c04401c10020b80303510034100402031000318030b8254101452100f0030440d500082c0c2c0485840d003209040030301940742d14 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 596580377 1250 596579127 596579161
    0x1b03020c1810050111120f070803010f060e0d1a10081209010207080a031403041109040f0b1003020604030f051207030512060f130c27031e05070e0c0918 67
    0x1d09040d42e42c00c41c05d003403107a0740300115240d040c01000041100600d032079a81c000c2d101071640c0141a00c1e00c1c0e40c1c5034040745c00c500b4040c0c85484001081c2c180842c8003810840c00d40a40e443d04003540f40f0503030440e000d0410b400e9074081d0050000e0545050001303250070040c8403070103640c18120701c2d00ea41c4040d41c0d40028903001c129045170b022a0040e0000d240001c0c2c0009503072443ea503102c01c105482c0d5a45043c80001f04598483e000d4001c8110410002000080c41601030300318403d9240c94059181c2100040340041540002504043c0800c814000702d0010b94000d44c007148284102d6090250349030400000d07820055084000c40c401280c01e2441c003d002c0700b55944044292003d505e05041d6070700054a15440d007100c0d003000c0d80d4030701c818410903104041180e001e495422146c0c265004035411880311212520065800014040c0314035410312400000c0202181c010000b0004103080c62504141d466000d031003c485031004200d000e0880c0c8442d101c007100702034481401000ba00e84842514540444 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 596581627 1250 596580377 596580379
    0x7030b0f01030c020f07331d03030d0501060c0c091505010804020d12122004062003042705010b1b070f090c03050f06030d050d0b090f1008030a1b03020c181005 70
    0x402030f040521f0b15030003d60341800321041d04080041002401c0841d09504c140301a90640300e081c40c001040d4660002c44000c0b500b4840d1040d6800c6580e42c406134800c0307a800c1e009148201c00003880420096101c0c445e92500580018609082c002c800d5a03803400a004c0c0340d40100c04106030001c00d6446a0b0316200c2d0f10314011540481035900d45200c043ca1719207100768000c0e1424400d1014650700c90b00b03c803036030b0203140058020850380d4030703a01d44c402e0000755107030707014466506034203020f41561f02003240c082c0c54100c5402107411814134005400801d8100711001400c80d2500c280b050018081d0040d1551f40002c0c2951a000600c0510a1100500740c1e031004090110744140001030010f1030301c4c00103d001e5141103030b15050b500d031809400c1010140c032031556660707840072000c403e00840415400016000700070402c40a01ca80ea0b490704c90a40324040c0e901803402080400028030f40480700750b12031030b554510a106491081403140d0004102d00c01191200741440c0c040c1d0100a0030f00c1c00c040480d00038001c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 596582733 1106 596581627 596581709
    0x6140a0f061211040509030c0304030b0f150109051e04020c0d020106050a030f061a091302330c120a02030702010807030b0f01030c020f07 61
    0x8030303140c06048185001400076071103165281c0d809903107074010106090b01d0000b50420005280003001041c0c180020050880d81c41d03014402000603610030130040c01182032500341c00d503034105c004141d0b4002d1a4890009207890f07070000009c4003125021207041d40401c80101c4030000341c2c1c0072200e2454001c2e0011819801510000c10030008415031640204a00b0390380d5070800000c010719200c013824108290403690040754003500000320400c80000c0d400021a00e190205425490850b14a0b0040c03c030346001c0401c40c5050300d0075081003140030464014803151300f031009096600c69412030811075400241c88025450a00200c00b4680101d840c032501c0d100c0314000039481e6840580b08a002501d90b40008141901a20440b0070045004d8456042c058900c401900106602d050b134505501c5002c1d4078812894080220402a00440c410010490100c030042c101c02c246130300303074220900 = true := by decide +kernel

theorem cover : BRFrame.Cov 596402877 596582733 := by
  have h0 := BRFrame.cov_init 596402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 596402877 ≤ n) (h2 : n < 596582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
