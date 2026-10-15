-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5448
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:53:50.260808+00:00
-- url     : https://prove2.me/submissions/f4b84984-8def-4b46-b7ca-18cb0c9afabd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 979676258 ≤ n < 979856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 979677508 1250 979676258 979676261
    0xc0c0f100507080912090303270102010b0901081507030b03060a050402100f140c160305012f1206060d0908120c0f160f170711030c060a051e120a 64
    0x140b20945040159403490480e546580707400400c50f000d424910301240828058a00300180d800245206401c040341b001c0c0140140e041d80d4114015070300648c2400301c0c8804c1c0e818902d840c1030407922050010001030085c8090302420020040445003056540c070084512560304101d0a0b002c0c00d0251000640c508150052140d2020350302140020b00800603610010a84e00c01c05407503a00b203011400c551604a460085030420401b598801c4036038070012004010704c030341940944083d0461000d800c0400880394201104900b0000316452191401c0c1304010fa4400080e039000c0e80002c0007058035181c101c15000320411a5544003055820f01e5002c120f81101e185403040301a0850b8424015505212074040e00c03544911400c0405131138510200e1030401084110240580c005521035840c2c40084659400c0c507034141c2140c1d0301070300c0d00c60605903528981d04000c6041402d05d80050400703413500b0050f038015a400e511401040d8208144000c900600e02203000141c040110b900c803251049007000103001c0c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 979678758 1250 979677508 979677511
    0x40e0a0608010209131508070b0a02010506040c1d010315230f0913170a031e0c09050d050c0301051e01090b060403020114091002010e0f01050f0a02030c0c0f1005 71
    0x5620783c410081c080d150341c1ca001c8a00b04010b4600303804240c02c44001c4801d03441080c25403003040e00780b003514004600044080042d1003002c5080c1e000b04015580d00d01004150f401e02c25480340031890020f09003030040d00d504404030700184103043c00300c1c240d03100320440c0503140703150350100e006140f148405440035215030500c1000180d013142c60020300d05200300014003444010b8604441c01640c5031044003000420344031a600341703051200542d16003090300070203006062061072a5001060020281d65410300c544114040d1010031354030351000c80d040000b03110304100086001d80d140d2180d110407d03016a4240190b61041039100700d51212141101d540d854010410b13000f9000650801015103216160102601c080f6602481c280d80410070034214061988640078046400a40c02c001d5520320980540100c0b481c40305e848100e5080b010300318a140d00f214001d171031070180c19040c1e0001c144081c00b1707900074640002c41c0f0f01d2950715142c08141c029141600f01141400716d50800710700c6259040007842081d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 979680008 1250 979678758 979678769
    0x10308042d151b0203060a0921030b0a080d09090507021002041412070e0a0203061f0903020a0906050108190608060a051902030606121f030305070c06030603020d080f0f040e0a06 78
    0x4818030003e6500003519060f00400117402c6690b2140b102c81800754044142084c21107222400f003a0140c88003004002d040c070196218001c2c9c00c3c07118002185040002d90440884503079641028060526807180090240508a501140320340038001030a111284002e00c000c1983c140707007600310a903e40510183c0c10100000400680004a040014148002d025a480018183d0040c2e41c2da440c00d000410b621280142c200441014402d03040714250400b1400b23042d45d008441e503200c9203644c1c1c9180c40c02e40340e0314050540010801d00c0800c2c55070120440116540411060124007d51901150391a02d1001c40341ca802c901e44800500011105190070950b01150903403040d0b185240c5080407071004d00c030f482051040740204400140b01f1000441241c0450321070759201401e5250303079041c0204150802001a940150b1205000404502034424034003102c0d8003a0036a407007480c02d610b560005412403000c40441c88020442441d101c141d0748000c0024100d01e111460442c104000c0c131004544458005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 979681258 1250 979680008 979680047
    0x2010e060d062907120c0c080f010509030307021e0f2e020301030314090312030106020d08100f23041b0e03150610030603060213061403010308042d15 66
    0x28540e01c4400e4101d0340d03665042045c213804892282d2003140d513041d05c2031b0003401e1071040707601c042a0b42d43c01041000305c4102c000004d01046d1038a030455600c81c071044d100800940e1141d40c0031081c445040c424111980c40c6031064034581074809100e603041580070301c00b40c0ca4500c024610314441d50001c2c146d03030300d03080d42e0b5400c11401c660550740c0c058030402e05452103a009440200d03803d1400d41d000c0101a01041700e00020507160750790381b14040d41d9101c900d04158041084000066140c400d07800d1045e08a078403070824416007500e0085610080e92494503540c403200d0f0410041c148075126405200c96403031501025030488400408014140c09008011134030135004107506040220603040320542020701142c0f01a80b05120220503001400c0c6680000c01142c000f080c0b119022401d240307683c0854010ba100d608981b0469440c4239030620090200070601501030005201145003a410902c00318204c90458001588000390100c0c201120351029110021480c1c0140d00745902c07402090b00709407209031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 979682508 1250 979681258 979681319
    0x1110601061403040620090a120b0703111603020a29240415050a050306040f06020703031e1a03070302031905011d0102041d040803040f02010e060d06 66
    0x40081144001109507010090044041030a0095552000e48400141c0e03586d202d00032a44001d5071903c2d0403007ca024400c8a0300c0500041d03c0c3c4c00428501840343c3d02c44500b6000b030b0b9810384164014031651010761000c2c8024880444100c0d045440026040e0103074005003500d14117803802e0314030119654442e07240d0301a142480a00048410075854200054040320400c1c80da420018580014490302015030090612482414410504010b90180d8805407000d00406449805060b5128010307680106036010700f44541c1c0c0851a10303800f170f0403054468a8013080302049401405640300c44425104105076840d6944a103c180402c20b80d240c01100b07602401c000c514540002c0c1d00c0742c408910121034604511140c80420000b0b610182e60016a00001c081001816020500030f400c2401655660019140a8440201c080320014400c076484000c0364030715501c0765102c12031504080e00490502ca03540d20768002c030b5a9940042d100c82030100d4000a0000d00e03065003000707000751840c0540c107128809131 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 979683758 1250 979682508 979682519
    0xb0d0b100f080603033717070806191403011d0d030e07170a14120f090a080102030901150e040c030b0c0c0312161d12010b030a030e01110601 62
    0x109151441800d402d0201141e83c454010a0651080e13012107004a007171202042100c4813030b4001711511a0007400e80300341480c210b141c15103c1c1400301c031b0908039400c11b840c0083d0405e0700c06c450555100b00c01412582400003101c030240310031652a00700000b11104101555558102444cc032581400c400b0f1441c00202c0410307a06a450b010303001110010142c8410250020b80e900300300900c000d0400d041401841204904503a80303c00084000315041310001d0b04d0580d100304c0c0007422132028515610300c0c500e0405180c0324104d460313011114807a04800043c0c0c0010700100b0078406184146545000428554400144020b00c90055000250440520818030000c41c100d8142ca0059940c0052103100903113a0460700e0107540291030302e00c0440d100010b100c2501040c6454454051840314211142e100c01c01002900c034601880b92101845012921510041c6004e00c00148804510701c00014000e6109000c00c0c10844002810f0780803500000e0368080c80d50b807100c1d11580d62014140900029410003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 979685008 1250 979683758 979683767
    0x100f02310501030e01021b070e0a020a14090d0f140c01020604230f030703031e0506030d03020a03060b07060b010905061305090613020703080109050a02040e0c0d11040b0d0b10 77
    0x18001c550402d03030b403288121052102503040319070b030241413038001007a074a46e8180c4555130001801001404850540415140322240c000d590184130551900c000040be42c54a800180e0440800158450940d41946010075101c62242c0c241a0145c8110030b20b00c8090700806152100310040d0b241107611260070003020902c5e07001c01e40744560000e200d2134480c1c80151381b0149000c42c0080d180380301d4040002e00008141d00f40d402500420b02c020302945c0907101c4c003000b003800c0340d004558458141e00301206c40041940300b94000c210109441c2800100b0319100c03800845540c0007000202d403004e946001c0c200b840d6070881d044c0c00007090115415850046840c2c1409880c08141c40380500074a00c81011a105647d920b1491005c1d9602075400c644400ca90709002302403841c03c2c410440410f141101049603816140222020381d001440d88600d15100d6405031020b6a2105d41c0384410300d50b40d40040b4100c00030910041008180064100340c0380d840080d42c0108075452051520310030300800620350740340d0f80c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 979686258 1250 979685008 979685107
    0xa2909100941010b030a09021f020115060519031b02010b13060513050709052206080606420a080f0f060607030309020603011214010509150405100f02 66
    0x140c2101c64403503c440c200d2002502e081f880096002040082d100c101c160b00054055859000c0e5000788038803600800c0c5280d05400f54090000051410000b41501680d5480300302643e00952600050108080704142d1034003408260520060751943c400c248d60b46855100d83e417081c003001d1001c200180c038220014002520102c1c1810500d40c0703580000d40030303070700a40c00d280c000e11010342298200c1400d04000d410184540409040061601001082502001504600c91400540781c0c074008584040c08031007224007141217100d199951a07402a500001c6030b041000b83c4041a600c0f03031070741508030000e003103050000d140000c0c041c500340800c02005c4001e500326800c01029203038156500002c1c10300718082e00c044040030b5001200000000380e80801003100034240350040040d42482001d1501840c20b807403050ba40a9080c0d40010205825403420740c0180e41c10a10442c11a112448004030340800c1c2d80c0010180520b0320b502062000302e000c0c45c4112244151008075002001980001404142205 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 979687508 1250 979686258 979686269
    0x1701140a3c03020d0305220303080a09020f100503071b0503040918060905072303032a0703050d09050102011514010c020405040602030a290910094101 66
    0x101d04641610200400c480c01d4081c6401414403002440203050140056202008420107110041142c0b0300d414500701c07132141500c0d4036903200e25003030325030144c484060005240d05036402002d00c00b00c41200d035101c1e080309110003c2030300d4146e142d00c5c4c60100500a200d0242000c0d6000c08031185031000541d02204881c19282890f84c00a901c6c001d03540003a40c4415044801032845280c0285e000074480002861401c860340801c01c0080c02c3c1ca1690603580c3c0700d500b9458a905940248440d02c0b080d501d140d01c6440286d9039103145c1c1a10846034800b80c3ca054600d40c016a900c1e000440100c503210303841040c400c081c01017800280080310040600101401291044424000d8000c1c00d00006030b02c00d5807c08180d070340042052045050a0038050029801a03507a03002c441d00d8050307082900001c500c4440034101d89100001080f10651080c000c40c084020840d068842c040000429100398604c9100741410102c100114000780d2070749081000005400d20314011141048004011305110300b0450641d030707 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 979688758 1250 979687508 979687589
    0x321042306062b06060305070b130b0c01140c09041b08070807022505040605150a0305070203190e030d140426010603050d0801050d02090402060a1701140a 68
    0xa4a010f0340b220408001002c201c4070082001ea8140810b40d0040e00070b680c010400d0310f0b801952444601034611a610b00350741402c00c020420000799000ca40901564600140085403000300705022404820049500a06191001c036004a0070f040610695040034900390681c2218600240003420002004140500f00702c911000145028400d0000d242035490304400d000f01c4448a00c07050008031620300405000c0c5180000004403482e00c0514480c8a043e4402080c0c900f0204030700881c041d140040c110020740c8000c10451101c08019480c81c5595601507450841143e40b003001c060030401000c3d11502000030741d017a0200440d006504030340445100c10f414040c8071140a280306040c0144583d4451a5481d202c000001d101d000f02e50b40e08032004542e94403101c1ea072035004106d201610018080e400210010005d001402d15400518442c02c41e81040390031250240da408800362802d130040300603d591480441d2440c00c1c64001440a01580300d40003090a092128800c0380c404e0144002e010348 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 979690008 1250 979688758 979688779
    0x80d142d0c2505061e13020607030f140f0c0c03010b030c210d0203041503061d2a09190e040b040c0306181a090705010e03032104230606 60
    0x100d2403900c0c44040e654040165041303071400b41e01059a119080c100304489022810000d820310b04403892680a0a5000b8000c50400f20300380c4048409641b1050790105001d6603102402603c40f014000c0c00105880d814440e68030070410480509001030800c10b18001d80c10140030071000d94000c50b115020740c7c400e440048a0000c014040c1c000220070b6400210107024002d11128400c2e1b003c0010005d45e01000f0788102c161454000c12001c444662207844541080c40785808240d42c2526125a0800c5842200b04524104611045c1c2c204c0c0c0a10408035444c40b00141d10681411310346c0d108d01c040e0914241010032185803c8400884d0380307000304010207491001c0c0c00241008210340e0f20001541d008803041160b045810740352034040340f510a0035142141b07aa104814074820b8601d03800e201b14038440141a0340c6242400540f921071040d84c038543e1501040c0240000f00704130700d40f02540000340403203402d1141803038204120204483c8103a0064074100203244403485200043c55500000281c0e00c01d09803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 979691258 1250 979690008 979690057
    0x4030c12030b06030901090c1d041b0b0c010b13110d0e0316060b011202040308090d02061c20120103110301061d041a0112080d142d0c 59
    0x1d02e108075880d58440720210910495410550258020038405c022000e19243c840c0b802581c8460b110780a02e08842544000900142c1609000c2e01c6d4004020041d000040c0c8070b24018030715800604203d034035699503214010a5242c4501c0400207091904002c0002589003c80e000161003180218104c2d0b586900b03845545800810498101507600340d100307000c0440d2032070204007511400c65480c0c009030820303210301400c007840e108990860fa40024903038544006c80e428000c0c124801d07001a40e000c0d03c14448100c002d01c54116444505180480c00a40b1010051212000684035400d402d0300301002d102c0f6000c0c2c80300e41c103000c60540c0e030000d480c07011103010320f00002c0c054401c40e0402d03040e0345000d43d206940920110f2801d4000e51040c030304a4184007038100300071180d45013489401c10303055106843c07001184c8514002c01c1d0180740e40078042055482005c3d200020030341640c9a05c100c458200204400942003040540c804003414083c881ca41080210600c041c0100d0380e805202400ca80103006a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 979692508 1250 979691258 979691261
    0x4141603120e0f030a06020c0322030c0b0f0703030b01020f24130c0501051e04030804080f15012d2603120406050901020c012c0f1c05040e0c07170304030c1203 70
    0xa0090243d00302144070ba07150010042b084006110803102c0c4103616002140c0094036000703440c4c00200031100342d41090955102140500b0351080c1850546c0210f84c035180050209004c0756078141514181f0141551000c1351600c1300000c0240b80500c00c0549001d0b10000560088200089034424a03026465420704100200d440c200e041a001c1c002c02c0002d0000208405000503004507042e00c01501c1800c501d000e01151036088240d855039079181140c00500248201d81c0c03280803084a02411500b0851900c444240c007120550000c03d20007c410700a912070003e48402d184448500c800918104900308164120a01003d40001e00740d1342c43d60001070341c9500075416210000904002030080400c000118803001004080c0c180d05981d100754500184103000800f20380080408004124240b4144001c90024030030008620802804200014070b03200a00c507150700403031000e60b000c4d50702e8001c1d1500703481c1e948124620016103030050040202007074001c00800002d54001520301102d0042010450 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 979693758 1250 979692508 979692517
    0x30f201507180909060f0e0a020114090423090f1209180a0c03050a0e0303042009040327060f030c03060f030b0108010f06050904141603120e0f030a06020c03 69
    0x84510607000b00040c0d603c190303400801d03003e03001d40c40030401d40c80035441020a442d80d1104500c180c1d8030580303180005522034403200c6120600c0c0312a8038100900d81c40003034141d465405001c90705042c82c071508004601e8080d00710760882c240c18010841c2211805d011504e40d00310407110016402c0200b102c1f0310a49034084405100c130700b941002d5000d4600b007a4004010003400848200107481c0c0f80004200310f050344a51070000c4c2c0d00100841c1141d0340c40e42da50042502e250781400024089401426032070300c44100c035038002c0c0e100c0e0f00c801508106050740000300c0c1c043e04a241c444100d0402040001581100c1c0106078051940b9020462032407288081d0702904055000e44207101c803c11000040c028810045030590304894020300c50010920103000a4a0550081552040141d40450005070402d0034180720915004e065079031120b0081c8005801321001da0007030715048000303500510701c0c641c0040002e041a0b41190102e98500503500400c3e47c0708510742d001055158009080c6074000000c10584 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 979695008 1250 979693758 979693787
    0x106030c1e090515130807080a0803061201020c0a06051302010e0906030a0c0902071718010516060504140c0103060803091306180903230d0b120a030f201507 69
    0x907040080034280c11030140c0c010b403c124003d106542c03012034025400b10b5980100c5001800805500026894003002ba620290505500c20404400d0781c0c0210028000703080c102d00400c02804010141c1c1c2000d0003621030046c038081c0b007540e0744500000140e8010948440103074095450750703a2036807070301c002c2450407500f040080d0501803000d40000e062501a001010410700c17903004010000c0c4901b4071544503008800000700f00711100f08c445803103540706101034030b100e01140300e10001ba400203442e020700301c0e082902c0596203555803052425154008029550b0301e12000e00c1e0410096180200140d140e009652007103100d86a00e90009032185500e0b0040c9018241c00c40c80307805100005410b0300700400c4403a03803c9001c00d0402143c86c80c00c52565100c1d22002c2100c688a62510300e480c1104401041c031280d460340d2000303001c4580b0036074503010007509541c580b1940b500704400218007006440b40c01c1e0710140c0144003901e50608200ca00021400207010410100c600300251100c80040c0c03a186010f9210 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 979696258 1250 979695008 979695019
    0xf13050a05070f1a03060f01050f12040b0606090915010302070611040608091b0f0a180906050108030c0a0f0201110f0703030e0603040f021012020706140106030c1e0905 74
    0x141060040120b160001c994401d1400e2012030740e54921024064005a150002c0710411700008115060000300483c0600e81450b02c0e80c41d03c42c651125005642060355415103a0440e0b41c01c0008000c0c4e0038410350740226040f11042c2c10050050005280c1c1400100907468041e012801880c00347d004c0e405680c111640b010342401341d0840400208640d4000d4407900b00020b07800380114101000100e050f840c105141d000040360744400e034003800507000081400982000d10b901c40081e500020111086103100030035404a00443c0a0030010140c0e801070308000400c0e0810000040740d1080010b076020029401007028491000a00050385d4a075405944413805000b103000e55000120042030307181c10b407480390320303000d4540e4030a1040c00303a540002c4038002c014400c00307640d11000d49000b441940c002c411910b820004100000d00302c1069030408041107841c40c2d290075a1160000c8040c42c01c0780074000354a0200042c118841e80103042040148150503140102c208181e5050b00c58082200517004c003920 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 979697508 1250 979696258 979696273
    0x7030f0e07120b3603070611190801210c0512030d0609110702090a0609230c0306010503010509130f140c0d0b0703020d0204050409030c1a0603060f1305 67
    0x240700030b0321010744600301c500c05000c0c00010b55007803841c02e6a02120014180d0420b0007449001c003954075007a00101c0c0302e8184410700280000507030a0290444200c2e550850320340b00c0c0d03100d12804040c5030007100c880050056000c01400b80a20b01034403603070401010b490340303424540319040c00c4034111007940043d43c112800c00143c090f4103070000f00a1003584400481017118682c0c90b0400d004480240380c0a0203411010070050002d4605103403c0d54120489180004101d80d494016200300c1d5841d81a8034580307450300802c052682428030075140e0000c80d11580c3c0c0d02c1c6141c5640000c020740b10502130b0502ca0820b400103d051910a620401d0906500c02c1e1100e50321281070600103011700e02c8011003000c2c2d10441c0c10f040003505141c250007948503446500c0601c20f85070000180c000e9080900c141c04069408e100c00a03507980e5a005244c9031038042d480d800d0810301c9a082c03100441811120303140d0541c0320f240c28800c240d01d0028030343e0ba12000b40c0210060a48800f9205010600d10f1040074005120300d94 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 979698758 1250 979697508 979697519
    0x3010b0301061409060409021c05090c0a210305071e030305150d1205180a0f030b0105010503130b0601211e0c02070302041814010204140a080607030f0e07 68
    0x400035410788403a500ca21512450303001040c0740a1141e0401150004000d01c81044007150980140c8126240454014842184e55030050110750040701c2c13107020b55100110340004d030300381a5030500181c4401b400d8490802848032a2078548000a88020304000d400511442808146a212007540c84020081c0c40000000c1c20014040c1500740c0701102c0300e0803210003080c414500702c20840306469100c900280c1c102c03607244c0c00f1341c5c10382c02a019603030406440c10180c0084e940e8010440c0080c0c884140b600391030345c0c15420800d01c40c110503000541400410006d00001c1c0c4a13100940015942c04a0300b407880d0b81d5504012500a0b908d1418100c0500428a64050040d01c40e040079886a80d80c0460b202c0e039a020f0008082600d0f92100c0c0c0d8000340c0c00c02e20040c00503080503040b10300c040d819108058900c24881d901c40c071583d401c0640b00041c1d0b9601040c2801004401030840c0e45081007121001e01c05030610031f0840e201ca50103004501816030b9018039a04001c00d03504000c64130724549080d50350550396074 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 979700008 1250 979698758 979698779
    0xf060a0311040b040501030b1206060405090309032505040b03190812073f050c0909040309060e03070506030a020901140a030209010320030f04080c1e060f040b0c07060f020301 77
    0x85c003855002c682448401c0100b800c26915885121440c40000e12041d1942e40c01d00000340005458032440c1c0c0410014020a0f850401401000300c41d5981d17034000380e540502008081d09040d800c030b42d12590034001c4003003050390000313000c0c00c0014030401400b4902c0f5540ca041d964500c101030f110f51644018008004101e600704a400d00500f03101c94518004a00340495200c0b42074242c113001d084104d80911004032101d465100b95130250064541901c1e0021107000100300c103030704039800c400044040c1c030180030300c07903000342800514881a0010b0244506200008070203002c010500041c443d801b10741450b2b160f00c150605c40782c41101c00e40b41540da18124000401079800b14000c1c60220341441030403140c010350744118280181d0195440307829921013040401a80b00058015a0440c07000c0c445a0b910807418040140d2400b00c0c60380c00049441054445804c18100070f008000d8240c003e010040443c03407140d02140e0107810740300c0c81c0e580e981386441c1c514000d00140155a410520100000c40c00001c1c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 979701258 1250 979700008 979700017
    0x904140402100207060203040b0f040807091b0903051b01030b19081203010b0901050a20010c090605090907260a05091c0926030a0c020f0604050f060a0311040b 70
    0xd6810b218800d07a60714040c2eaa90849214001c010b0344108010812406440041e06221458610081c90a540d17030440c9441e00710140c00c8588055036030204561961030f410415682039800b42007201c409451500d80c02e480d241074818103405490124440b840e144e100ea84843d80080b0024045810002101d002011660342030040140070b00c01c12913280008401c103c1628100c030184c1c0c0416141802940044030241c10045105050110501d03001b80c3d491441000c042c5400c0000b000092540f0000342d000b001541182d00540a03c00704010548868448120082c1d0002940c1040305030a12941d42c200848001c41b00050b00c000e45000a01818800b1600114001d8050508444a00702400540151001d10030303d1031b000b160020390108004c00311811040d007a000155000300310203031034040342c60a5602c120240c4001400161a2908500c0d0500542c40004420380710941018144030101d1031150044242070b100e0f0f48046541343e6114400d4101c2845c0003e640d500320b40701c6c0d5aa00340c240e810b811 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 979702508 1250 979701258 979701263
    0xf0212090a050706180b0a170112050606010801030f02040b06090d0515060f0a062d0c1a0c0703080a1506020715022a030c04110702011106070c03050d0209041404 71
    0x18004000551034450000782c0e001400000404020626103032008180d68411408001802310301904102504100021580204103c1100500d0001d00386081c034240314008103880d06200070341c40140040f40404c6000c1c842c0c81c0d07068a00060012201b40016440c0c011281300030b13405800c00c25200300300000030800c502c030b46c0340506105109031980000c01c00440480b090051700004048400c00c0b85a01c2249000d860800340c40c685100c2c0c0580b09004250382c2d90b4030303118502140c455044141084100b801c0c0480c0c240c824803410034182822010b4100c0b503c1420405030800c1403050110345450519440048010038030703228085a60b545c1c7d10003a4480d040b07842105100d10780d800c00d00c0c60383d50010031403a1140c0a01101d04c40030300b0031081e940804081039a12940c152050220301070080e01c0394455054100c104e00600ca44401d0340c0d10004022051b0110608029007040090166aa801880c51814664141001c50711003030400c400c0002401460705007507000c0d060a42d641112145468a24001e50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 979703758 1250 979702508 979702513
    0x31614180301140105031c110703030c1101020708030a030911060c011509050903090d03020c2d0117040605180307060b12010203090705131d030c0f150a0f0212090a05 73
    0x1070f180c400345032461009101d07140d050340206000068482983e03201030b000e40c4042c1080e21090f030600e1075661070440b8540003100400c00c052151b5042c440f0440301c0d1070103003a00f4401040c3c42c07170402c506241c89000c3c2506900a050f2550700c08400c100d0700d102c0d958082e00b0080c201300e8440c896400624080d003041c101030041003404907008608208140070f007510400d089002146044010760034000107818442d026000c42c0900240e281071079581400e01a80c2e00c8007000702c034001035074403881006501c44510205061000e0780c1e10055003840401400b60b4415004800016036035581031403c806da4611b00c2110099000010b114401c114940c0d2148601110035101d072126120b655110300c0c01c0b440300b6200b00031684d101881c100b01ca8a080c100c00c25030075030901d00101e0348880b03507602c042c0185034a04c1100d050ba00042071006501038200101d000d90308940005050040c614201e075266154003030035402201341c03542c0c80f140103803020380c0481c0c00746000104a100c0c80c0c070346500925195023a0035800c8a050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 979705008 1250 979703758 979703771
    0x6050f01020a0305040b090a0302091005040e030c060f130c08060f010e0c09040903050d060608043f140a02060f0a06060203040611100504120f050a05031614180301 72
    0x40d403000522895595041d116146403908202141280b60031032141c05074880d80040021005881e00c0c0ca41c1070044811880c2410a0b504090801050340d9000b03d503100103610611282090144c00100180c000340c44441d21007140d140c4003500e504014640d20041c2060307145400010383c860000616603c944a990540342103a601c4a800341c1d0020025501c10160500c01d1003a04190302d855030101c58140d00c24101107260050842442054550a42c001c4010030581402c10092101c41148000d26204040b88001084000200000544205014074100c205030800120440d0700445a01d03c085540cd01e62644601d514030300250344040403030305580d600c5542800306050914600466069560326000303581010709008080319500d4000e0220387e8284038a81601d421250540300f02c8d40580d0241911084011845001506908070308440508000741001902c600039071140070b9980103c0d05400162401c5528003081315118100e20105002c14070008401a000a40010000003246d00b030b802481007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 979706258 1250 979705008 979705039
    0xb04241806122009010f0602071d0106211104050f0109030309050d17040605070506090a02030d0f02011e0f0b1516080f0c031c33050301050a0605 64
    0x1614414841c1c2c0c2c0d20442c1241e040d00010303141030b001c4a0b0b05481e2101801440c00d090000070107142082e4409000e5080c43c0509011059050040102801e5402180c2c600035000702c11450900030144154010084000c03062a00f45029403078070601205d4440c0103000a41810410514591041c81398501c1180d440801a920354003031600d8408998240c0c44207400a4075000501000c12826001111405070303400b4100c60400e034100181001d041540e079040e40700c0381ca03450217600d80310001d02130040e59400f00e0380010041e5000581c40700414102d00e00070116590300001a8003608503644156050303202059800c0c4111540d5000302810040d80e0b03c03e20880050009111140c0c540307400c90400f05404000c1c2c030644c5403020014a9440344640b80359423608114541c5440241c010044202e0180c0001410717036415101c080302640496000e4404000ba003150400441149680c0b0350801003041300000300704400f60540008900400000c0c000740210f10304a4032210040119000f22b6204000241c107030b455 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 979707508 1250 979706258 979706261
    0x201020a290f1e070513030c1a070804090207060b0319030807050a140f04030212010b04050f160c06060504142509060e03210c070501021b01030b042418 67
    0x60f460508000d88071010015403071040c000010000018803408002c46c0b050302e0419040507000314060040048500d04041c0981040000810052440759080c481d1001003400c440c2150110b526174840140c4e5a6901e1510401504d20300840e44c1d0f06015210442c03510303045410711810541d1082e86c400d00e040e40c030100c081e9030300c0c02424641000503c680030500c1c244181c1100a0501c07109005040e81003d6503940003882d105a41e400c1074089944507480c0d00803c0c18140942034200c02054084921850620540800341080c001d0140c01c200345e0000040c10300030150300c50000340001910a124482140b08501381ea504150b91070030115412a0030740300080b441503100840d1a10329507a201e451450300b034040b9904428043c14541c107001d4201040708030440da03002800031540c440c0310640c90302c503006000c504265060f8005810b540000b1018005c100d9400c03a130030110102420300184a40100300410000d04603c01508001c0d1421b02c0d041400c0b0742c1855400089a03190f0300e001c2210141a0403640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 979708758 1250 979707508 979707511
    0x5100306061403011d0d1d03010501061d0102030702010c0f15020c0714061e280305041a040b011703040b16121b02221b0906030b09060d0201020a290f 66
    0x1001c0d802100d81a1a1140b040d07c001e03594900010548250051020000703003111000c0e1300607404246020210100d0f0005040705004100c0c00b400a5801e00403980c0000c2d15042002d91700603d44800c40f900741d01000401e08901610442d0380200315101c070040c04c4c00c02c0da034075028041c50403440c840200071b00e00b501c2c10704102ea01031510400700144500703e4800131441508905420300700c41045080911824203521000c103101c540d03540c3e0100300c904003428288616016114140694070580b010000494405820707681107820380d01150300d80000d10340ba1181140902d8100411410002541c0042500304042000e04507018000306c4003d2141c1881c20b40b40a41900c01070051030210125941c00351521042d141411100c850543d03105070010b03100981290300741d010704016140380d00c0b030040703032207a004100760064004c42c1400c021706090400000c45c0c0c0300700204a2440b841b5512065030071a407081c4941d560a590115203501010340000711880a0000080c800014080010000d0350021400381d10030b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 979710008 1250 979708758 979708811
    0x209040b04050c1615092613060f09030b0405010c03050622020310031209060906020d1e050906040609030615030308040201080406112115010504090510030606140301 73
    0x280340212814028030b81c80302c45a01a25001860345c1081002c082901420440c10320070f0084140030f4040c03551480e4040040e008100300900180b00d807400c0505062a10001d5840c40c3c1000c840e600c0c5005003c441c1e070205500014000b21459041c0010020150404544d07030507691006e110540d070f04810300007412082104401550516000c04e540d0400960003980c0100c0003c50101c0c4640d140d88651100480719020a80060129001004280d6028401002511070740c400b404641d5800c0d10020085154030300c01080c03054488600a504d07034040c0046034140c0b48060256030b111a40d0710001380c10403080e0b100550fa06070500b80b1450040c81e44165020a40b41d0580310b0b43c80d00c0e103803900111060207000304112074143c3d030f034094502c486440c103010380400e13480340d070503008004581682c12014a00162002020741e808904000180c5e8010059506846110b04002016507800d808050316186603403014112a10707042c800f01d803030215007070005078440e001c1d0300070701031038110301441c0a560702c66290700d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 979711258 1250 979710008 979710031
    0x306040f0317070c03110102030601020a171308060405071202130e070e0c07022d060307170415051006090b0a030f05070302040f0f182d0209040b0405 66
    0x5000524141900d80c03100d00070314101c941002004540c1605410984004000c50f542c040080f003010f501c92070740300700c81420030000c3d4294148000041d40d80c4400c1500101328040b490a0f0036804030086096660b040d07201e400101c1ca03140d45054071601c3c1c2ca4103440681f054021741c01c0104855000340816051258050034a05c00f036000303540745034000e0100c02d9061815000d0031100145000a01510034094003c4021b09940c84500748108040078404a074106001403040c10141501d04c22041001c83d5a44242ca0b0b00350390f030b0359a01049511180c8144400c800300201024401807100d0080d03030442d0f61030303103c004000c641c949220025441031284142c20010308401c0060002d01003040141c21220040e050104078000f2408004041d071324126114000640d0108040248070050140c100040c4841d0700140502400c0051400344040305032040341240b521001002000d450340d00002410703480741203e01c08400307031381e11122002c0d50040189511450500c410b4100f07900c0c20384106030054403050320 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 979712508 1250 979711258 979711261
    0x3040e1e0403170a02070507090b0a080106140f031009050a150b030d031e1406030606180c0306010903050d021e071805060a0e041a0708060105160804050402070503030a0e03090306 79
    0xf2403030910030000c2c01d242c4c4c490340078404480011001c200e11009001c94082c0411890701030030901ca1000810303441912181e0410504000259500e102c008d51703448107075007480c24240c902d40803d00e0803042c640400b0419150120381410300c0030100d01c5030840d0b841501c0151b00b1040740311020064610807001d0f6981074100c411130025103802940100ca07058207003940c18603405c2d1003d0f814800c9411802051103214882810081d2502e800c0c400603600c1801100c00c440d00800028200400c0300c8000c20203003000d41c0010104a81e40c1c055080c00d4011030f0301001f212a40f04480d600251626038162061102c1010030124140c1c80c10045100c406803185441a0488000414407141c068680075002c2d9412908441010030441000f226440c45240034084403480c00403c0c0381c80c040301c400d00604100402c01c1c044140615a0380c00422501c0b6446091809442110b81c2e0910380700c01d105e640e00071507011b0700c00a4218200100440030754071996016170104590021035400a89034440c8070b070441c0c5d041d0003490 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 979713758 1250 979712508 979712537
    0x150c040503060f0405120c030403050709060b04030303020f270103050906010501020a03050d14040c0305060108190210030627050f071715040f0e0d0e030c0f1203040e1e0403 76
    0x1103c165020f40a4070440d0507194450f090350b050340e4010b0b0059401c03900000b40900074481c0800c8610000c1c40000d07070401c034407850000c020402e401745000040405800083c13414a008012058800800040f200190b2180d42c2d03c01c21920200308515850110b4107181c0018640e45000c1036070341c105c070010b0700a0121000d00e60ba0807201988514244058184c4d600702107403250309501c03081445107100b020000d03405811800c0c154034001d0143d2252a40d9884040c980c00d00302d00008450241c1903054a05900b0540764000984c0504000c2d0080d01010001407580340402126484040c0c034050600303020080340d2546480000d90040480c0c072070020070399083c0007801001c951517034603501c221802181c2000c250058001415601d074000719500a648850003041c803007500f0700111008128a0425400702d40061001c81e844841310b2403524824081050742002031b80352403400103c0b0702c2440c0244c80d6115119611541d040f0005e0354100515101420304c02003240c9a81240d07405960141c0300c0c9011040d400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 979715008 1250 979713758 979713781
    0xf03090609050a0809010206010b03060a0b300a0e0109111c050d080a0614010e040c0302040b1902060601020a1a060a05040921020d0e0d080f0a02150c04050306 70
    0x4101100c00a60712082030010940a001c0c3c04001c0d03208441d03143d519500440024504081a0000c0d1050709042040c850355a50340c140724021244800b05842c0c90f200c2c0000e1003034000840c403100e544401294401d240c121103603060078522418034030004100d1074001da401c0c0f0707080f01c02006000b86420100400d20929241880c01e981207000340d0040c40044000d2962594105030300c124040c0b0208081c0d4007030081c00346030340c00f8180103450303446c011010070f81c0c96400007056901180c81c1280160341d900c40c409a0f2911a404407400340001c2e41c2700f103642d120340300240842482c204071460b006020707410124006601c0490064020741d00400700301034004428200800b001d501424003580b00d0007012001409896038000c080c41c0c240610600900411000012180010900c03400c200715040441000001d642000707031440c40324000c3e41d0702500c1100c3c615169140707100c0c2c0202c514a42e00d001c1071100b542c81e80051415032103010b01030280e52984a000c0d03411502d000303034001d00764590030040008000d80d050 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 979716258 1250 979715008 979715021
    0x609050907091b17060d050316150b06120405070915050a060203030c180d061103060111030306030a03030b0a0b0f0301090f110a0842121e030f03010b040e15010f03 72
    0x241b00201c24060356880d40e01e154030505421061840248604043c04400d03010011440e00b402d80030702070591400b00082d000d20850b044010440c80b144003041c103010707080041001405004030100001c401000003001d0641442c03180603c0b40c0b81e818004500d2510210a0b039009490312041076041c540100382d5085030403c44000300c2d4101c9800da1a040228049005070707001710700b800000035520300f408400100f604868000625081e8004c10501c619510005410880c40c1c4c0c0510b400200445140002424151f944e071189152480110b506074050b0000b44c0218100c2d142c1400801405410180d20720546004201e0005000001c0c4080642c0c54051410380d03030b000d46800804405038500e0f030076031100079a6441c460355440410100710003154103a621600e15074078048a0160242c84a1001e4590740c46881d8004880d10405000d001d00c84c80f010003c0e280c02001082e01541c581da11040d5000c000c0d082031180140350404403004c035020780c201c04410480300030103079280d081145061000790054081c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 979717508 1250 979716258 979716271
    0x160f050f060a0c06020a080108010f0606080a09030c0b072a080910120e0c120102091f0c082d1804051905011212110705130609050907091b17 62
    0x3015101c22002581318402003c06c2051600c40101a50403c0241800c43e8030b00a00075144500d032500c18000f003600f205a00c2d40c0110a1b603004907c2c9640f070324044916200030380b00104803021400501030b1890300440301c840d0207800744812595500e29002c010451540303461001e0300d10141000040300508003a03000d0940200e10381004581417070342c1104202110016100c074825500012080e8207640780203d00b911801c0b10140081d81400e6190740000c039800c055003075680d0248400f00c5c602046c0350055070406001d5810158803625112032165102041081c801030940e801074110b4801c24103034018040c0c400d5400e00000f070012007800310080c08011308020344251010382201c041d0710f01006a40c019036000c1d160079042d04001640c1460911404c40300300b11501c05001c46402542c02c0c1090006d103010803200d0490380c02090f140441a00b83c001d00198102034891410501004100303070000420b50211340103181e0800140d240ba1480c00d07244440d01043c080040d2000458400c09a4840c50781900101c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 979718758 1250 979717508 979717517
    0xf02060c07080d0b130e010f060b0f03070c0b0702010b0916081812040602011a0906131a0904032d020c01140904020c100b0307030b191409160f050f060a 67
    0x48040000340c179090704550702e00100d6407a180c0700c00c0001403c1c041c0c050800090035007031103281d0501e2070710050b0740507000c0005800000400000c5a0500c2a030072100392907040742d01c0d030a00d4104540f0090191001c11076480c002c145080125142c9200181c50080046440c1d0b111100c0e0340390813410780c04400d0300c80b035010b00324405c2943c0600452550f030002c01c02813880c3e4000085003059104411849148248403030710524a46040050320380303543d02c04010784c05a0701d40016a04901c2c0d01006082d91120407040c1d00020310b00100810140c211440001c880405101000481b5001d01e0140083d0a4071203441c0060b049613a60420715401000c0b81101310403c203401d070b0309141d01c180203e400ca80080c8000c040c0d6510a1403480200d8020b4801e101e4020401d07406003a415086840347c1d4a14500580103442c000d491a0b942d02c807907a0395520241000c82c0f8000440007900741146410791342d10485a640644142c034441c001641d070f456103543c1c0c04a800c0a002118003000340820440a604582e44500502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 979720008 1250 979718758 979718771
    0x812070f030c020a150c03020f0303011412030d060f05030c0409020a060e0a03020414010e01120804060806062206030b0307050a030206280c03030b0f010c06022104080a0f02060c07080d 81
    0x28100a0b0108281180d07980108001ca01e081c02890003009c84c1200686400402c010701103007a1b5000409802da00555940040156103801d0910b107100f01d01c0c01012051801c0d00c04915100390045500c110b85044045032081d408002c10070084a101920003980b194040f4410842c09000d0a25610840030017031004001c169643c02060540b0407001e00040a4031f101e84c018410003061915042c050201c9112500c0d0581060303442c01d4503480346003c1c0c2020b2250f0354000405640d6001d00700c03941c076180200c032401c2c0f0900f400c40d1030725841036900402c00460b061482c041c1d02c508000906004540c030042480c43e06516507001e108141d1b1001100c04242c921818980d1500300301c280445c022541190303142c014640b81400c00908035152440301d0340c0300394840e118641640c0c0e80301030484003c540102006940e500010421400b03131141e0fa45009040c4100000c0105004030807000d0b1410204540720443d0b031000410040380c54000440705022022000d103c03413008505084013400884071005000240c9 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 979721258 1250 979720008 979720019
    0x20f0a0b0d0f05070f1d061909210804030215090607120e01050408060a1109040e0703060b06160303230f1602010507200a021503010812070f030c020a 66
    0x8951066000e1500709840d0700700d940301080e062041c0c0d50310101c145085900d00401c041c000340b11918040414549818207400300e020780c0d6804013150400404050383d01145601a0300140048269110b00084451134003500100019038980903003129a100710f00c2450a400c5078204242c4c1c420740c1e000300305162014000c1c1511519801c004000860040d00d03004400c100000c40101080f407030800d110304110042c4810003d400000500c180c0050042c00013042000b00c4401518060041d141540c1e40581841511024003001142043c10340340280c0f001e10900c0321b0102481524403892400d25000303540c0681c18000700c0c4c46540320282e41c4110011281441110203c9a6480c5105803555280303442000244030302071040c007000702c500c05800d000910083c9003840c80640012000903c41e03041c540842c9c02d406035110f0501c0604c40650b402400d420703101d4150340441005401c00d000705015403184001003450406070900352901264450043c600ba10140e039812103900c402c07220104c0e0000150710000c0780 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 979722508 1250 979721258 979721279
    0xf0a2106030818041401140f0a0611211608160c0e070e010e0f1203030705030412020703080403020d0f0210020102090f0f030d030507050c0d170105031504020f0a 71
    0x19030081c41d045440d506100c1607a0310500311824242d100c0e07440e00c100c10010300402005c550444180e152440c00311081080440e03564030000d918542e01820301040410b00a810032201d40f41c13440b650044a00341000009000d04a2030002809001c0e0482408155480448440302c0451184a9050035080c0040030000e4109400141400c80348001082c1c4c05101c000009103040e0f6120405181c1000c95044490000e402d4030340098010780204650700c100b035810f4031806552903004040303508803552442c00700401481c9800075902103d9800d04c5180400300036100182d1102541e4215940302c0c5454503503400c00ca0588171840c0219081040c1e100c040c40940d880d85041d5100d841581c00150755400e034001040001d04c03620941d103114100146a02d4100d8400081060b00c48959040009290b154220180c50038056112200810303c0390010f400042c41d071204c10241c0c40f41d4910903c40c2941d032607500301503c801144440c002a410004000f50141ca082102c03e134400502912406003039448080a04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 979723758 1250 979722508 979722521
    0x60a0506031c03020a17060a0501030203060111100605100207030309090c0c060207030c060608010c05040b0904060f03050a0302120c0c0d11040609091203090807031107050901080d090801020f0a21 86
    0x40030980c0171510040d59038100c644240d5162040c04129000e15002e000204c0714005406480e040650110025020341d000c0c0c0c6c604005000c004007100e6034086c5410442c406030486004e50b074083c225507a04d40c0704007800094610140c07641a255040700d2810401640010b100c54840801000700c40101c0d400130585500c01040458025a520002d9050328201b940a85e070050f4084405a1b01d040c4a40b90301355803260030754041c1d40348440640d544418000010300603000541040c4880c8400070b00c000100000056005146846070b000c0e1070f0381d52500356982d01039028143c01c228607900b01040406c85440c010500c038032a58400c10090401050590104044400c560881c0c1d41555541075040140b004031044001d018469240500c844c4034959111900750107010300040c10700103e01c0505682c0314007404241c004c0c20020304101c2032581c1d12600345980e543d0030781d281008940c6050001c200102e060084490065030702e5030f421324003182804203c0d1b11460842e40e242c4504d409000d16002c80c4024000c95 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 979725008 1250 979723758 979723813
    0x4031e020c040c110d091d06040f050f041205030403090510120c0207080f0601060504120f0807030309021e030c100306090c0215221106070b07200c03060a050603 71
    0x4140382402c0d41c0130546803200c3c4070000c50510050171020804400c0241c6501c064002c680d1012155071070b45000b2801a11080c44100200d500b00020081c00044940c48188558000d80d14005c54080003202690a44400d482c00350018141c003101b404113041080005071f00c0205454900005010088014215502100a200140c00c100810003402d41c08229944014150b403001c0c6c1001c3d45000b202502c68840c1748282c400200c10400700c9814000c1c0c40c81041144c5800c404c405680c0c150501d0020020021008120722559044040700001c1035040b00c2c00708031200250080c0a4442c41d4000c05c4000900240300000b0141c4401011844005034015040e0403c0070341c0090104000b09810362840450042002014081e600d40444039542a11140207055422132417000f60340d41c42001240b46c3d44a01d040182880b814002400f801d590b10081e06004000e800c2040500401402c89942d1200300f0340385040c0d4550302400100d8090592588002d41080004040303449014403004545108210305940 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 979726258 1250 979725008 979725017
    0xa0509190507030e070602032110030605040309050a12020f09090115030506040b0c030f010b18032b020714062b0e150103050a2402041206060e04031e020c040c 70
    0x849013690040142c00060426400994182034406004414580840180c0c2480760064000704074180c04129216001e10381014080c4030500c2d090501600c4040346218050195003900d800252002800c407151030965401045910700c032481c8020031071249070103803d8841a540c1e8800703018624020b200c6850065108a0240c40030340b8050a010036200d000910403000004200200420544e9940449041d0b07411545040e88600c415402d01c0754103170b8111805a014401c01241080800e03d2a001d41588507900741600b42c0045000b40498845007584500308040c0e031891020104c6140c4040035120300280a43c038104618500021098941800400b4036409a81d441c040c02c070010040c4880d000308814080e15864031351641ea1031583c0d50040e900d002e409042e035070750f03118211102e4602e40c800300358032260150349441d101c40c02c030503100032680e404840041c40c0c06000036402c00440c000902c10f6030140c80e180d8400600c000f080c6c00200d0000c000310114007804c09402c01c103948a20845071800b145030385 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 979727508 1250 979726258 979726271
    0xb07150e010903140c070e070c050f010c0e150f041d090c0906041d01020c0d03060e0103020d14030f1201061b050318010c0203070803030403140403020a050919050703 73
    0x458200e840c150914003003641000318920109401c0b0021000d507409404a6560345c01c2006481c509060554000700c0d4407581402c144141c581d40000b80760300d0b603030081d0252011000e90581c1c0314225030403145030300d001c1038181304000110728040840c1c140c20007007841076500d04201c6102107495580950800d40510781540c0703001051500b413819841d030261819008250f40c00c080f40000d030382044009c0c149482242c0390388035811341014000030400d01a100030f000359101c200d5510f0301ca8031001c110300c00000203443c1c800b0000705500c00040035412250090021215503010b601c8030076055070b03404910300491204100030210000d10000800c4c00100c904107206595043c000001c280380710040038000b200110400a10200b0320110850b2144021034070004004010000141d406903a18400a9458010001e00040c0100040300452255210b991449908100100c5000c0d0301c1c000d502010b504078000840a10181c02d04042d85504403000c103c3c202c020015160400d030656204441c40c40000e0344078036 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 979728758 1250 979727508 979727543
    0xe030303040f031206050102030d09030c05060c0c0d1e050703050c0610030c09020c1e070b0c030309070b0408030a030f090b10060e2d0a03021906081509040f06060b07 73
    0x10901d07418404c8a81e030502880b450240000e60360701461010300c4007030b5a1000d890b804c143c0110b462085c00b90b840001c1d5a10380c98004c1076111560812001c0e824140502c004035000c9a201e403541c0e00c04002a101c040e80c014020507011582034000903030480500004100032450b0f80d0381003103802d22808040d40d1010900782540340100800300c0396800070300c0150045c000394450903004a0381418407030a08140d0100742d00210ba17402e14080055000f10307000c1c0c10010f20701c54010300100085215155000c100c5550550314910700540f03100301e10402e00c0369003040c040c1c50007071440307908401e61005000b42d0200c0d48800688501e201d03580151a20421080060410071820741c010b00d034001c2e687c108641105208030304002c0c0d2078903450b503020503042030a03800c000e4250720b9030b50f580e21102442d0080d000c4002d206a6000b407246404440c080c03240403030400070003e510f00ca4260361120328040027508225403504c03243d80e04424200c024a080b1011600c41c00040b0705101c04101401c03065000d2a10003a0400915 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 979730008 1250 979728758 979728767
    0x141f1e08100b090721140f0105030a03020304090e010204150302130603050c09060c0304030501240f12080309010605060d020406080a09050303040b0702011e09050c010c05100b010e030303040f03 85
    0x9001c1050503081c14202c8105030ba40c1c01c21164407000381d0800780d0381c00031041e0b904124400750a1a0200d003528281065080e0040714404612400b24001007031441c1c1d0b2540d0400d0750f101703504030b4002c00580c4100018841c0309102e0b040320040040b1b40780090700b85a111100c01c1c4e039081200307800c08002940422110800d001800d01c500041441c2e007000c0000b424050605c450741c2c4100c0c464a8050b060005000038045010001c8500440e0814003c1040c0010060068180c0a074455005000800344001081103c40c0b00810012244540c519958141056454400c0c82d00000e01d0300d40e0a540c0c1d180f0018603912248c00030308803040c0b2080010394650601c1c0f00580b0007030700a4070201c0c5151400e110f58000400000c11640c0054201c00f100c801d55440841c104d001d8500b01c41a9640781d48031011f00c007174241494022081c802e05c240300b0b44090700c03421401110254101c00024000350f0040d0a1910b406210341c0c00484c0005042c07520220400040011a02e981d0040d601111809095850f200c140f5510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 979731258 1250 979730008 979730023
    0x52215031401061d030c030706030e0d1b03030f15180609020c0a062f030103170a0909110c0109050c031614040b01050403060e150604141f1e08 63
    0x200807148030741d541070260081c402808241c109141d00a107440c0210296003c00601548a00c0101121041e680b147c900078050155150120305920030051607101a50088c400c3c0130404540c151032150403401614200c024201c03051810300c00c0780c0c2c1c4090385894480091300340d501400149203c0b02c0d1146802d10420101e85065010000c0a44188048902000c001c00d07000c2041d0340041c00810f20813000300052403c0140720704040002030040e50000d9030079401d1400756040786d0144451a04506c0c40d25500b50851040d00c41d4803002400030704e000c3c4401440e03584400d801091001400781001c4810360183c0c2180c81d100001e5440354029a1404040c1c42c0411080d80c200003a0000f5910183c5040080410010201c0b0028400d64440c82c0d00c01142e40301320181d0f00159085007050080b40c0645000c00d8581c0118079101107215680381c001022402c00303000740d050b01a09003410340c0040e5240c11003225030035140074412100000610000030442491030103414511b504980e012403840c5012400d41c031b800ca1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 979732508 1250 979731258 979731281
    0x1b0207030b010e1008070f08010605060405060d051b0a081f08100c050d06030f1205180607081b0d2d03090201030b040c0512060603040503030705221503 67
    0x5081400081d50030442181150825880d4400030344030612a4101c5018981084505102d48a400500c80d441219014101c68029008000064484003880100c1c0f245002e840d401580810a9032440102c80e8003082d03100715103002c3c0030440b501c1c0348582d014943c0808881d400064503001444080c082c4082002c204804009812030031514081c00d10b40c42d046040308422078a960755100110041c0240101d07200c68200711001c01c001500ca1500c3c1840e001003182c140c1c0c400060388114030b076045c01030040f030382000700300c41071059481c0030340d000c111035940220812151088203112050b0007041d007500da20b109041c10b1004e0706102031100b03070050440d00409201c1c42c040403018518441907848412a044a002602d40464007202d1800140d02410f0901a095040340c90890020701c06039001001d000d10742158002138030103485400810000d0302090302c0142c043c0e0420400729151070301582c0101007902030030341e201e2040c0c402061064403041d0a82e02002d08107900341c051001b05640f5110f01170001d41c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 979733758 1250 979732508 979732513
    0x30e1b0a09051510180905010306151809080403170a0f032307210c0930020d0b01030309051809070e060a0323010c0c08070f06060510031b02 62
    0x1d0700d03003841d0b55002c032800b00030f43c0280054004012128443d002840e804002960203c4001e503440340f211000f02030034403043c0c410350b207004200c5e1981505480c20100315200d150604c04114640d0140c0c00c010b02c00c000c012141c00808010000005680b034003410701030542e401c1159181c604003000a41448449641e890800d031806801001040c4024001c0164900100d0380d620903549224043e541c0890355040e480200110820a02080b48a504089100c96040d928103002c29900c0f0301030900c0c202480311034201d801108000109412641141000302d500003000d020306140961100004c4000a0f001500040c081060500c4541030a01d12041103c044d0112101c0078600310884940700d07003180c00f03041d1070b203218200803030416694005102c002d19007015540c0401c110100c082140b070109048500b03019400c0400c8c120140d0f00498400c483c8a81051320320385425030a07650922480c0ea02c140032240741b599520003055544840d00304501d0612180c400050700213840b0380050007407003c3c102410071175 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 979735008 1250 979733758 979733761
    0x807080a0c181d0a20010903200607051c05180906030c03011a09011512020d11040305033103080313020405040f0b0c03010b19030e1b0a0905 62
    0x401d2501044121503200e0006000d00c41040050006040400042e90925210040c80c0361005000b084040c652403142480400500c1299003400c2c800300c0560b182030100720390000400200741c9103801c03200c20700590a020b07007021a8030000a00c4a4200042c20340e4164001c0c1001d0a4903050088424050905030800304c2c04d1616407042444a64420305e851780c00384407400082069a101004100c290100080080c800c503000341d40031007030b15000c1c0e80d04070380b261000c0301c000110300c00c400c02c800700d0503803082d518413401440e0004084041d40c00701c440508110f6451440301d8a080c0c520300540091031044019507650320a02d007400c48402c0c1684220480000d15440c038004100c0d129407850700f03c0754000c03906620b9903150f200c40e200d0800d0690b0302035041410501008104500003454a40c0170341315100859250300d490610901501090081000e102c1080192180645800307c01085d040014640400c4491882c8103250030510ba8182c100f24240c0504500c03040c600d0040b1064015000341801080503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 979736258 1250 979735008 979735013
    0xe160617060a060c0620130b0337060611100e0c1e060f030711010c14030a0207061a01030e03030603031629180a0b07030e01021209070807080a 63
    0x10baa566100396018000740e080b1309010060181c024482980070310f0042603003014500d4680c1015171000c1d80201c05216842004141c9100410940b400303040250300515800c003030307000c040082c00d121482c0c031400c04040d5071400d4662586401410b01408241d80c611442c40311850203185000000f0343c12516035030400b0360781809040c000490285001048400d1a1400001c5e00c81081d4000c42c4900c650704041e00060a01809041400442c02405076580343d1400e445106046422034660048550003c0c000c0c104105010301002c01075904214070300e0b0010310b03061040e0b80d080c0c21507000415076009401e1302c205000156816205010000e00400c6c0a1880e52401c000060384912442d42e840c560091212211414803a982103002e418180c2840d0406454850003490707020803608840844c001c585900080d091401c001c5400d590b1140d001e040076225032214001940502100c0d81d100300e0380d41d405c0c01840451000702c9040c0e4000c4100c400940f11041c100702c09942800302c0b0b504541c8059001582d034000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 979737508 1250 979736258 979736269
    0x20c0405011d1b070228120b0a0b011e090303021204210c050a0320060403051b0105130f1511060106030209041e021206120a0201050c010e16061706 65
    0x5006907072111096440402d1083e809460007010030207074222009100217000040304003283c0a030410320340b002070007403540c6080c0d619200b02c4810300101000c507810041181c0940d142c00420340743d0300c141041c43d100c150f43c106c0c80000140c115444000905000020010306405100d4000106030b05608149440c0c2040221a40011604014007900c02504403020070f0200c001c003000e02810005001c3c943e41e580c1c90a00c01140004c526207060101c101600c004000e14006048904a030381c0314000c3d003040c010814469100700c0324424200e0500c80c04100c40000c10a1042000c0050050300c404070291504105007503440321600101070043c400f810ba02d00b02c010318001003250460b805854007503a2030680001003005424080d0f101c40700c010000e18044001026a0060000c0a007074a29801d210350b503010400c2290304640c50306035642d8100d2202c1c5405544510010580e44542d6800072614005900000745080b005c034880682c180c490040c1405080d51024403d0300400c4d000703072403100a04241c0300080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 979738758 1250 979737508 979737511
    0x303140903070318050607080a02010c021f0b010c02090a0e0f15130c0e0a09110415210b160908010c050a110c09160315142b03020c0405011d 62
    0x2001c0c03001c04c0c00c0f20f04c110301c05001078002900740507000c10b8844145243c100310300c0e048501d20f9800740d400d0030102c1da12349200281e4103188000c121405030303070031036440000e0000f00b611044885c10030039400401c0c00961203010701240200c1c581c14002070300d50800c0c3c4031035080c008000e8108005d904640094410303540c00014254001461004404031000c56150040e149503041d400852013284603400c000d1208000c2c1c8c03100c2034040c040c2c850000354a00b03940c01c2104941680d18103048042942c2d02c144002c0c6104034004452121403011031552001d1502c1c0c0003003a08084817140d23100c40c1a101c4081a01e6880f20384080285a040c2c020720041800520103440da008001540c41085400d0865641e00c246c100600e0f00c00e804c1c0a084030407c0e06005c949402035081c2d400361900442d041020040c0c1c924600f01205003100c1c170b40010848101070400030082000c06032010380000071204884a4902d041803a8034540591103030b001428810703021820f10060b0340c0d059120340c0b0008030780c62441c04441c00768074030300c0d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 979740008 1250 979738758 979738763
    0x3011809210c0f05152a030a06030206040308031005060a0e040221181c02190c030209070c06061203020d030b0307080708010f06080c150d02120f04030314090307 71
    0x2200c0154070400115900708607903901030980c8240305100401d01c000855040f680f0901d1a05003e41c2d5507411171300c4c1900c45081600200c5540000d134840e11920308139070141d03400c460880d101161043e80c1c0d80025140e5042600107560790500001442854254619000000c14050f1000b6083c0016001c1c043d08040300d107086c6900880c2c001030960300b2640c44050400182b444210180c206050034054404a0400c904016900d071240c0070083c18610000042610030030340070350040c80009019903400c903550690400454980d8413042d4040b00585d03510000038802d44083d40c0710051000241891400d503030351544142c05401820348141e000c02d03400320740c124030314582d41008500c00221074040b80c90110240c0c03200303941c0c1c01407000114041d581034004001c1108112801e00c071040c2c8030003129481d2104080c6a03035002c1140c20740c4100a90a0303c0c003424503142200d0005007031050011064080722030440301c2840c040c40e10001c0108254051103001c404007007200743c00c0d402e403801c07000042d40c0740b04400b0301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 979741258 1250 979740008 979740053
    0x2040e090c0a24050d0c030903320f13080a17070305181801080a15140420092509030b19110c01061d0f0a0c02010902100503011809 58
    0x50101d071800f0310704903a1181d0b00d10408011b59482d40a006005000094003100000d01c3d0703810315002c2c40d80500407076a404415030644900509240e2200c0f0143d4040f080c803480702e41c0705000c50034000066280d800000d000000c054180b814040c6404501078a03801c101007002d071414854440425402030680b11071158660002c8001c200b840c00180d40300c1c8400002542e41c010b1000080b034020340c0030981c00c02c810b1007950711520000b64500da05003030b500f10030703011141010f00c080002e0101f1820b620060514034110941200701c11020042101a06c0c215002c1900d0000c0842d0b4140415000400061030f040900d011409103045580f00c4085050103030400284480e496061543d41d22151700c0711074550700000600703a64900555815020303120501c6240325000030745890048040110102900c203800f4006500130325139481c080e180c010100795060000b10f6680c2c40c0e614006844200149000300602d884c0c05440c1d6140100090105010610b182052400c1203101e03000103d0b045c81c1d0601c844011103c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 979742508 1250 979741258 979741319
    0xa0807030f0b090106020123010e1501051204030f11060f0414010e06010f15050f2502030a0615060302070503160822050906090402030a12050d02040e090c0a 69
    0x1d89001500c403589865a002c200c000002613026015480102c00112070104188040ea0520a145042c0401d205110070300b504600007800c1c1d901034000c1900c6c1e040050500314100180030303110700301d0018106c5007280815400f0481c08000e40d0450a050748444d4480d008009502d032030104054400d0015000030104030385000c4e0b1f50b505000c20b400c03840540e80103008446107580d50702e000346074644e02e9104091181c22107603803403121180f00b401140d86415440000624010762a03004001c3c8011480042e01081501c0d00f0000050780c0034064110910700038040412180707100d00f24138813811031507448a000c0c140b040000800040d4040107031041d00201c0d034800700c08424282000f200c2c62140e505075040320580100e402100e16107172410b10f002d407030003520705407059680c40041c080001c00507680a589680711005c1a00003c840f054034460302015480d1213411320b80280c2c0d964080e60400c0e0442c61189841c0010041984410040c04549001c2144c100035a41e280503a030000384280098182400f0310420b6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 979743758 1250 979742508 979742531
    0x1020c10020111180f011814130c080f0a060807060c1a07051209030412060b0111010f1d031e28050306100309050d0509040b042a02030a080703 63
    0x1404102c3d207414116100c1e94811039030030640e44020403140218401e40f203806a07644c46511810100100818031507a40a40b03d0401c5d83c070110310102040200c0d401410b064000c15140010700270081410006e03290030f407650030301d64140c05880354005c3c90111840c1c0b030303c0c504002d244400910f5904644560500d200010707140e040600041c0101e000e016030000c880402e01c08540da001000f003031840c4600482e007025480d100c140300d0320783c41940328020f46500903491003004980c0c0b40e030010104101c141400801c07130003082d407100c5c01d40d00d066581e20038141c1e0307542040d07100500310031a64000030b20030381c042d61410b500d413001c600100c00042600c6102800124542c14104140c007008041c195003280400078000e801c1800411a503c01c40b14039010344440b04401100314081d0041600081d4800003034201061010f0045030a074000c0300801e82e0141d15034590300650340312842802180050824105001007101c82c040203000818141441103500c02c00c08880020352100129801c0502840c011038200c0070903 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 979745008 1250 979743758 979743761
    0xc060509060c010e0703050d0e01021e190b1e011a1b030c1b0306070f0f170a09052a0d0f1a2505090405070c051c12050601020c100201 59
    0x12a01e03030b00d42c0d07103002036a4035004400940142203c7c07140382215042c07a00f0b850200c415041c0e0019103405a80215904160402000f010342c04000a0804480c0440500788004040d00301480d0280c074120107000600068404030034040303001094200c9150140d502d0005510790056815130400750071203020441e400c4020030501c00400714100403046944903d0304482403515003d00c40c40c820b09240d02070b2241c0046080c04203610348034030555213411066104403802940e200e06508148000c100d8183ea070129809100c180c0030b4052481100d001a070715001c0e1404505e4804011142c41c0a07480c9154020000d41560540c1002d0007005c0d0340a4610303010f1403030020880300101e140101010015901e07031081d0000035008038407800442100c20020302c02c80c030212025900d07060150b4002407080004c04402d0419401098104806280001001e21700781c94040c14400c590b429021040680034140c19503ea0200b503090300c2d078102e24010800c5050420010b90341d8080703171b0412809070034545800d2030702c507000707 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 979746258 1250 979745008 979745017
    0x1b030c051827040b15010c11010c170d1a0103090b13020105071a0f010f050607140304030f05030d11030f15041d010c08090a050c012d03050a0b09040c06050906 70
    0x5102c84288a42064903010100440440d07030050031480d068034000d0103621036a501c003402e0381c1264141d0443d640311001110380d80c0032484203541e01306105064070030f11480c0030000e10f40351403103001c00a1038201281c04403081001c9004410f0400d400e0200d0b5101041c10010055000310b0003110313000c2451958801660503004110014007060403043d440740302500b100203960700c02e003405800c00040e60b803680004100000140502904154140045000151900009203c055188003160300700f035900e07620420141160181140d4980020a15010a1101e4081c5011031f205100d115415403400f60408100d10000909000c40403c20340b90b8603200c0d0302c030f6a02c2000420010700e140004080205001c034042d002c1c3c660361800003215a00000c1801c3c1000c04c1035035000360f1260242490982d00c20044480b60180c030044640b6450760000d4102a42b0000000501010f00d5100420b26241401e044022103c042207114000d0780380300100400a000840d003102514518140280c0383d60075000821954013a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 979747508 1250 979746258 979746319
    0xe060a020114131101090b0d0c0c0f03030e070b0307020a0f02010302090904050303180307050c0f13090b0f011401141e13080d0f021c03020d1b030c0518 67
    0x520814043c0441d01030030b940e0349041c003a0b10102c110440540044442100a10410020650034001008218a103070030408440050303140034904400140c0701d65510134074090b030403004250307626202c0199641c1884404000d02c4000041130440c030f846400651100016240203202c0303a550050030301103a01a505550a139100900129080e2070325240c01a900e910a403070305803000344a80c603040301cbc01c0400000c8990460344a4082c1600c0501e00050241200502c2036150780300d4407610386d95503104c0c1e143c0704d8070891b5805105000c0a074204100d00703808401b010b801c032950000c4404201e001c0c50340c005000e6503080e40001d0095985030900070302c1d900078004184003800c0e07000000800b14014006801100b0a941009080d40c071000121b030350030ba68007000002c41c10056000075000c12031020403000600100e4040e82005498191241040011521403420303400e5540030005020400c182e00d48640000d01c00c46050051501800290b4011050107010080d4801c000d902004003076201c000d070284001c0e84 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 979748758 1250 979747508 979747541
    0xb0703020c060a060603050a0902130515190f05060304020108160e0a0b2110030b0402270f060109060e0f0a030506040503030103170301030c03020d230c1e010e060a0201 74
    0x83c26142c4001904481c820303000002d061801055844800d13114aa650aa000300288a5010719100f11006014000e2000200000012448056443c1e0400303c420f1884800102c6110b60308003c0e400c80180403a405c100c0c004c0805108000050340c004003080e811545070103040c580080c69070004c03200420310801047d084104400d00042c01c0100602400381080d401c000030714101090110711951103401c45034500240403408081000c60040390700107420500140405140350b000507a844000440c8909030107000841c40c003000416000140860742040d0b0034a440a4000d103402e8000f800100d05200d0036203e0100003041765296510760800d00c00440d80601a5900c5140604169032241c000344811744448074410030316541c1d4a110740880e81600c1c2e0110086106900799001e001c000c0120744000c40d0600844031401340d4190050741b4101d02030641200401446145400f8451650641e448819500c01c4441c0c107840760780e800c88019540084140c6074a03842d682404422800f4144448044230b001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 979750008 1250 979748758 979748761
    0xf0d050d051b1603120b0303070b071218030f080c03220512040e070507150f0b04050a1a0f0906010f200a0c1e0b09030f030c060f07080c070b0703020c06 67
    0xc2c0d0f08100400001ca00985400294024150182007903440701c80d51030342d250f0001c114400001d841c2c1042d10350400d505140c00b00340c001c04c00314180c048070981110035100014018881042580c4902000f01c40001842e1400203400c040036500f40c0e5010141034003180900d40c40019401c00709201c406088180c1200c11142d0072083c1e03400855140c0e00c01d001d044081c03641d02d00040c1c0036a00440890724015407125441041d1292048004020001c04510040c0c01d5200d080e10b40f1180c4e501d0084c0d03405040341000018040c47e0030034560880c89400100f036801000040d065000c640d131000d0f09035178085020700b0089020700944e0400c85005c800c00c0e00422420210300c540c01148400010300c081400c0c410400c01d09410f81b181c12070b02104031b40507480300b0300c011110f90911011503040040d2010440180890f05806001940036007103070040394500b50380354096000c001d44d003840c0c80344c4290006103e0034407210034101811806500e20403800058500c10050020598a6120f681144d000600c8001038501c6d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 979751258 1250 979750008 979750027
    0x24020d0209090603072d170606010f11120711060a08040c09090b0a0b0109050406030602030619030b0c0307021006030f05070e061e04020712080103050f0d050d051b 72
    0xd4001c6400c6600900e10500010b269040c0000c580d01581e050070840b1780e1150007040401c5403092149094058440009030004e00c0469074906144c90413400310250160b0700c2c11800040501c22654400c004100c202c5809500c0b4040200d94491110080c0800075038905060030b094990710364a021294016000280c10003c1c03aa204a44500884c801c0c1d0789000f0b0301c3c0d515400201919007920380034041180c0d50703010441c40306160b4426600c0c0c50040c185009000d81c1c03a800202111140d900903075849030008100021842d107402000314888001c0b240c059082d0940d1a031804581c0001c06030544036074000f0102c1d083c039000708903a903048500316a0a11480e0b480b450802603a14402e402240c9500c11a84d000ca8103480b241d140c54032411024240d12102c680f40385113008020130300c040c0d03c0e401c00d1f42008028040b40750324039625010002a02e441103d07514600d0a02d02e000300d858500e00300741c0c002e244164a80c80d400310886012104010700400c0c9d9440381c0c0324500d0300c0d41c0c0d06c400c2c8200340e0f5030003d02242c2 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 979752508 1250 979751258 979751261
    0x90206040f1509050906130b030f0313090e010219050a11060a020901021c0f0509180c2205060d0207050f1c030605010908121b010c05041502010207020d24020d 70
    0xb50140641d480721071940c1c2e80c2d400d00c24404400e45015501440d0301b1011807050301c040c0d2000c03401403c001c046524914149407a5402d5600c41031011040c8d500c0c0090600c03c41c3e240e8000c2040e002001c100843c038000c1e03d000d00c2342900012041c65400c00c4400603404011038801c4c071081c00160096800d403252414040c01042c000e501c070110090250003016441c000701000307050b42003413202d810380302e07807480d541c581c207089030361354001050b485d072204d060740c00f5400403030100c41c07600c1c800c10002054554803c080b0300340e5032115003540721140034025001400c0c40f07180c88200694031001d040c40c0c40580c8403109403400c41d00700340c606160248a44501100fa541408c01d0340700c1c080012440e62010040c00e900c1c1c00045865101c1405504079507800004807001c07009c204001010700410841548814400e101c0ca064291200300c610b000000320081410312659505900c6404490018002140b03424609c0c3c0c0030403d030300c0c00b03000f0140c50341a0400d1680641f601c0e078111100ca1071040705045540c1c034400d082000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 979753758 1250 979752508 979752539
    0x2b060602010b1e150f0f0c070302010e15120406020705060907060806040c0203090f1917010f18020d022412010501030501030503190c0f2001080613090206040f 70
    0xf84101d411942c2540c0d81e070a00220401c074000d000d80350350001c55814103058203d0b03200440d84031000400f000a105403442d890080c001d81c8060401511520349140001840e10800c83c01040c4100600c1c40d00d0709802a1840454054200841c0d041040c3c1c0d035a420414004e003d0072501906034003646c0c2c200b2200a1021074000b0030350b0b203030380c8070300c4041d407500800c3c80115a6200400710159000304400e5469140400d035400b00d90364001d2201c41d40c0300314800d0302d5208000070760100a580700c1000c00444031030000c0c05a140407400307640082040b43c480101020b54041e210202034010100c407100f00b019512418034101401240341d0400300003484c1c06254600f15404034450780300b1180c031500086402c1d8424002c003070480303400c80010341c01c001640b45008094a82c00714040c00740803000b640700780050021b03414001ea090280d000c0009000c080745601c4072044801100341e040104c41c10130841580e8070031003170305080c041c00c00300056050414408945d03103109541101a4010030ba00f000505542c41c0c00501 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 979755008 1250 979753758 979753781
    0x6041410050a0b041a0a03020906061b100f0c080c1308010e07050a080a030806060d060f1211040b060301060c080f04030602040512010221090a12030f0605010c05032b06060201 77
    0x1003202c0e0041c00081c0717600b41c41e10540c50b0ba00c0111142c0c200054513081122580004009141c40d00c0c00c0301c4009948820448082101040c3e045800e4869490761903215091402ca2030010902030050321040051181d0001404a02c1070b040101c0c245498060b603460100c081c21240e030080201e8454180318a58455543c440c4611401181d0008940703040040b4a8005a6900d91914190340e01d542c130821809800c803000c000d0466a5070440011100d807280100700007408903404080e8001ca2a00708459005084490315020300d00302110300d81c45440d11000c407411540b09140c510000991860206001c0c42103070b4100010f80800315010091002580c0240200d46085a007880d103141146422804d070302840320f100c0031000c0d480144170400e030200e2014a07400381034030041c0c55142d10b6617a50f9000c0252000c001200183d41c8000e0021381d80c601d0722910001d020700742000060742850790740e040d0f900d106d0081c258103503080c0080d4a801c907030746284e10103412204001c818400240c403140002d0080c01030b01d090 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 979756258 1250 979755008 979755011
    0x1030e2a03070801150608061206040609032d180e0f0609160507020f1f1205060109120f020d080f070308060604050105120c040914040b1806041410050a0b04 69
    0x14083c20520894414a480441c21a489450400d09680e42c00c001050540c005021040b150581901030103424403492050f040010119200d050042c081101150040900d80c1900a80101440809542e88646d0024509020683c0284440b5505041c01da8002608456001c090000d006403002003680300b0181a11152040e90301d4401c1c0715882c100840c80c000102d03004022200160401c2c6210f500c9141024014a1851517494288001134a005e0240300c0010441d441480a803603060103019040142460700c03411513420003013403208206203943d0003405184000104011529041190300d0041d4100c40301c55201c600d6100e40d1403255100c0042140002c200e00005001ba1401c0c000b500e060b1101a0b43d11401c0100c01d1000c6400104080c010103a0325000384030010740d10381c9034026180300c0c0f20044241d08840c1080d00e8910011440a000c0c6c10041804015000500e040010070039030058005460090001c0180003050070301085041409045040500304058100c440e008034503000c005640 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 979757508 1250 979756258 979756273
    0xd02061617040f02061201060309300503090a06050c0c010b041406100905040e01020706061a072301020307030509061b0d0f0b030a030c2a0501030e2a03 67
    0x12a04045406030707001651100300042000715080d0b401101c0f407948013410980c9005100c0940741d45082090348004006034940700000c1c10401e4400300228000103000340740000c0300c00300101c07aa103d200185080f0130850040f00152801e0410001c501d0800d400880c200458206030080c80440d901024580e0040e41c205440794005041521070256406484000315200f600d0720010443d00b600e008881c0c1d410400740b41e501080590f11440f40540c1c218503a0b000683e114002d00e002c1c01500c80c5544644c90445c0c0414805250103c41021200e000b40d0001c0000781c0c1010b040c045010b0642c42240c204603561000c010040000d1705984164020078445048988a90707410421a00d20303802903c0c83c00e07424006010024075007680e50000c2c1c000d44041c0701c0110300780140d4000b00f440c044000740160002007001d00918148103000744076010081c401488200c4171050032030543c441d1b4059114090400d80d45400c0224816014007401c40e5200c0900000d590702c580d240c01881c003083d8507011451081c05400ca = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 979758758 1250 979757508 979757551
    0x4030f021c03020a06020901050d0e0607030f0b030606010c0503040906120b061e21060412080907060504141813200f0f030c03060c031b0a0e09070306080d0206 70
    0x142a0407207989036004050120360b655030071003e50000300000741840340a10021100d603030f981c0240d00380c0c04d8000d0010a40c5141c44c0d1001802e955130039010250141c0b4004000c0016100801d405a20110a00340854211a10702d05a480c40c8a01e03401080c0741c916180c0013281b41c080e90b16480c09501c0c041d00d08110f0a0302c0344410007080045140c646100340c0c0480300f4030300c2d00f03041140240416000d020030360b0b038420039030561145c1032180441e012070340c5802c08401070560ba43c002480c20380041e40c84000304046800c010010b00765124078000d00f1000038000c4503803802640c801e1419140b0301040710301280786050031118400035803c110b00c11039038a0001c1410441441c12070394088184c0000421002c0440050f00a02c440040c0640d02c864249c010381e00781262985040040502800c0250b48903507491400301000c0b01611130607641c400203542c00300180401d9075401524101445000c07501142d864840c0340c070541c000d1816034420321290048411f00b03984145c000c143d00e031050000e68003170704d210100b08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 979760008 1250 979758758 979758799
    0x421030f061d040201080a11070f150c08011a1303050d30050406020d091b05010c031202390105060607120c03020c06131d041502071704030f02 63
    0x8802c2298125a1000040156105000710f981080c41400000f80c030008400d801c2a26900400d000d031000711b24201c1d43d0f020424940c0c0c03102c0e00c03440702c00c804010340a03074444000c04500d070621803c014108171140505464001100315203d21880f1030122050640d02d141458a0380a01c9001d400469410205d203190702e0010341450071400c0c0325240a4041942c00c040200007084003420650710b4640c01e1000714240d28407803041105450207803124845a03000500e040202c5c58464005904100d0036030280c100007900600300e00407100c859180540c03110b500710000306100d00c500d010803000d00900d0701c44642d4400c0700650f40f6500f00141001f0300880d51250203008107031040c80c100800e2010080440307504288a00751511147c1d10920650300203000140001d80e2076049200e0305100005051002c000407060103011046004d00d03c2142c00c02d5140070389421a4100f005180000c08940000f544c1e41048068082c443e036031b0a096070f07610b0300d464480c2002203070070710b200030b0490068901c04461196014030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 979761258 1250 979760008 979760039
    0xa0c05100c21062103030906050703051009020f07020f18070504140604051011030403062309010c121109030a05010f15080604030e06040b0c06071e080f0421030f06 72
    0xc407035030480d416040300c00400031246013007641015070703a00141c0d000401d07500a082c020901d03680d004c42c030390622041c402e280c1031070b43e4400fa404070300c1041400030090001c7c00317485820350115400d01c00e01079400c02185182c0b000d5a0406000c0e824030307003000412500100904251a2200b25119098002e0f0082c804144507a01a007940580e1800020400c3c1c0d04c20f485160f0100c500b4015241099604c1d0740d1032b816180c1528016100214907403c0d1102c03410a0509186c0c00b45d0f00c01c000780700c1c01201d0314014081642c551060454903407603401c0c4058468206003214001080a0100c0f003580c0703028202a402802084520610a03003403925101c00d01001c07103030344010703111b01030003a00c1c2d20b84440c5c1d0300f40c13258000b099203190401d40610000980d283c28001821101800d030000e03201d035182914008120602d411400e41910342d43c4071804a500b540440f03c00d5000e40700201d07559840c0c80301e0518041300d6402190711002e0482d05078030084825410742000c601c001041c6000c1c00702c01e88481c808001c3d403d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 979762508 1250 979761258 979761269
    0x518070f170c10030c0e060a2304051c0203191203050a0f02040611120408030711030f0109030c0b06180c070f0b101d0402060a0c05100c2106 62
    0x520310180329004500d802101d80340924022281d0303451042001c1408a554589500080b9640790901c0300100d422114003021301c10122981440c1422484020349541200a030300442070180001012404541008440107040020200801c10040480c48443c2c400611012400790103283e501070503001c0d500203800180c55200b40003402258031860128000e280081c52072a4042c0c4402d54541c3c071007a28070050024000d16a240881e2003016a40a890320b00c10b0301082140210400c41004200c4010017a52035466000c072a030300c070346800c0000085ca00300352105900d40c69441d1114038810142c0207941022028401c0c0c0c2c5c880801d45d1180d0820101134a03c5440c003170b4081200c40001c29003007950009054191260354004401103060f1903420b10444c041310352070240c2c035040105109031a60103110360382c0d540d100c455030611450a40d000c201c0c035006150030281446002c5005008029050224208280d203080c0100000580c81c18002c01c0002501080780902c1c5811200c05561040c9000e800c0c140c41c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 979763758 1250 979762508 979762529
    0xb1225050f0f190302150a080609040c05060705120f1902031c0903051306082703090427060519020c070b0a0329011416020f0d0b0901051807 62
    0x141c0000c14040d108040d40200d00400101000100041c1d9940414040b04104001447d4850700c0d0400c0c01380c0b080c0c80207800140f007822058104400240a61000380a94000b5110b441d101c000c2c1d80390485c80c011409140f40da10450109010660b041c0c01c00c00307040005440c1c80d508110f050385210580c1c0f680305241c400d01d4801040004800940803c0d0040b11119102e454010310340324800c070f9011a0b100140c1c20484c002001c0d04140130f2000c0401d403102c070328054401c59800c62000103140d0196280304025815001d40e80380c503250140c00740d9629040a09a019100c1c018044030640342a40c000c0c20100c400b80301a181c403540c8406a0a528030a46102c440500018030400e401d00344000b40341d030444c404030130802d906c1e0a110300303056209894640c8041007008182c00121040d00000d4580a80d0000b550041030040c003a050790170b80001400c1440c01d4042d202d5a040040d000003142d031480b190100603000840d900e0520001c03400550050380714030341d03000031003007c002c10301989501c8150301e120350847d41 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 979765008 1250 979763758 979763779
    0x91515030705090d0305191710050a1e08100e2404060b060c010612140d0f050d0b0a03050c01090e0c0d0b0d021503040b07080c0406030b1225050f 64
    0x1800c01c904c44900081c020308005080440d8070401d01c80c462401018100080c840a402c0c0d0951402c0030110703900008010301c03500e0210306140c0412084000b610075406940107c3c003885850350410908403020300a000e09075044200802c4a8101800464841c043c0c90721409030241d401071030828403207000d280c0c0c2281e00e031a07540b1240c80f04c40140550684e007075409201000075010030349c001d10498000748005a4420140f07503250501d1041e45030380c7d02000342d035038001842c00b12103203500c2800c1021103105400c160b0340303990248140b040100100100281c10084038000441400f1000401d10300c07500c8240e030740c1c5a0481e1188122050a02d017918050f0084d181405200144d00180d044ac2c920340001500160301c80e03400382c0000c0d0300480e00514001c0103400c00000c0c003041c08403480c447d561000c0307070342403001060a0440210074248180d2081508141e552170b018030136556054181804012140110340c03a0b550b0f95100ca49602082074104001d1095904d400501401d12106000d83d188000300030f0040c1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 979766258 1250 979765008 979765027
    0x105061e0c0c1201091a0705031308090316081c360f0302100801260109212d08060a0e090109020111190204110405091515030705 57
    0x607500203822600c0c440c000e032551482c0340e071610f666800340e000c007510000c42d8480360790138588000c1e40040051012a0143c900b00054aa04941107a0304404481d641e100c041d038507814109054002d850f580395040c06586500c1a9106910354020151101807003903d08a02c2c5884d01c01d0045081922500049060384e15007400c940741c3e40402505c00d1040310b030344821584a001e00c0c5d15403090150051100440805414000c1d800c0107100f0120314607003424117440c59414000010501c0040d41b4040c54190503403842c039103903400290018a0800d50040d050070b450300d441e802c06440c1078050a10301000458100c0c81305060850036401c2445154500800c5440c13826580f0200c1e2011402061241c1110451600213101007080084c0f43c0b04110f800c00020b0300007000e2000404604902c041601f45510800c1c0d40441b9003180841c143c5400d038102d400045055203a06038400c1400b60758481580b01d1301030000c00c03104049100400320000e400322881c038181000c501c88650b080c002034542100040050102c03108 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 979767508 1250 979766258 979766317
    0x10f0906030c0e030124050108040f0f03050903060702060405060907350a030207060806150a0e01090f03032001020a02030d0f0902040911131b2f15010506 68
    0x8400e510f020f80d50303048102c001c41c0c20350f207060072080c81c000e040c0b032108082e03140c04580a1001e00300900e0856554207194440f00d00d032200b42c2c2c5000e4030707030417404003490f007018040d404540b4401c0018050b05c02c980b502c1c07507000c0d4031200216001d036480c0c01160006070030004045901000d8456000e1240c05010b007407a10340e030175410408610140550601c8408403440701c01c00000c80242c2c4a68001c10a050922307000400314180581000e00030300c008004040301018030810359020415500d0041000074604004036a10a1503504c21803034900c0012002c010716500171540384241d04035401d400403c1c503241d1500d508070311030b50b46007100680081c8964030940319550400e61a40e100c880c000b007a68000c60300080c0860f403203010101c61134842d03a003415046003008407200c41c0680b0141e408102100f0200102c0c0300200b01d900400c002c100c800e0310100c0c0f03090710f1b1040010080c00c02030b600302c5245160461140e6a03082994003016400144000040d031031a14004880d03005414241251102c40c80441100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 979768758 1250 979767508 979767521
    0xe060a08090c031608010c09030b010905060a150f02150f01170106030519120e0306131e3905010807020f1b0f01090518040f0807060218010f090603 65
    0x8070103002d10102101555010004441012480715100d4a450b00e00500c0d030b03003102c00d070f0280601400a500700800124421022050448004c2c2e1804a06a951500094540034840c0c021040c4001401140f04000340e0184d4806107040395a000c503258120090548031180304120380c00003040074101c0050015444504406400c80c00200001c50202e45a5640074180090b0702080c2c500400300c5a5182d09105010380c002141c51800e08007034032040d0b10040400d40311103006155038400d4860425950400c0002010110360b010700d034014984a103064600b000001322000d01c03502c030901100144060bc3d059070103814500c251a07402c1420701502d0a401900c06520081c800c1041d0300810090115128042c4200058580d500061107d4800740304100500c2d01c4000c030ba030320b042190007a018003458a40342041540c10039600f510304000c0d6107520b0084111000400010442007012602004001a40d005032403c0e60400e01c80030102194900111400d003101088180004c110f0340d42080941e000b580401c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 979770008 1250 979768758 979768771
    0x10519150309020310020703030c1707021b010e06040902040e010b030f01030201030c110d020d14041a070c03021905310b030c1c05120a02031803100f0212070e060a08 73
    0x724041720300500600c007286c0200805074040707512820340128031580012899001d1070300204c00013580c10079400003540c420704403502d4159600b6000095201e03a0046215500354200201481d0740c4545401980000e9040303071284008104010002082e44051182501c0c0b10700c24000c111310282c2c4c42c640044024001000016042c0018044030f25200241481072441440f0240c005240030209220000c112007000c3d807140092500c188003d0240251410030345101c0e01c040700b80151100350303505190501c10000d80c0002d503c0820140e501070b45503184003604045070000c4403007071101c2061b1001541c0400c8510002c1e034903001030480c03690f0441c0c555032122580300000b90440722080310103004650350850076921080f0040403001c1c3c481c10000200301038a8101c81002040e42008000300d4065a280a010340105100e60303508a10340c125201003180c8074140c0c804003c00e00040720800c01620003984602607440c1001e0f40c031000100001c0c0942401580940301401c024078115001c001200c403400e014169 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 979771258 1250 979770008 979770013
    0x80a030c020d06060b09090903130501050906040f2402190204050a0608100e0601090b0901150203220806060f150906090907200a0c06052b050105191503090203 70
    0x7000c641c641c49510090035003d903220342e03141400402c020681f0b1005019074940d61040000e21151b0892018480407100c080c02d000e500c801c0c4020001d0300301d001d0382d00241c0180100800004858000c0c04908000d065000403015040c2003071001281c5480342c01044404408104400a00500f071640c0300ca40e2084880c1c0000407010707120002c0908201444441c6540c0585440c2c02510350341040c810240140700c4110100008010384020580c0340c0814031400f441402c82c020114405402807040300c910100b00c0401c41c04941520070f640d01d1260340d40c040c1404c0340c031510001902c2d0303082c101c084058083e00107000348180c080350f50032100c844d0322844606400580910109040d61641c0d5441401f403800d075102e84a51419056451100d80890400058540e000800380c10101c3c07400020041551304a00d003050b554990000b9090841d030b2000312084405920000e00c4003148072540c007203810703290101c03610a990010403100180c29490b074080d0548145409030368030300d09030003a0b102200d101d101909 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 979772508 1250 979771258 979771279
    0x70e03030c060703051f0305060f09070306090b2d0c0a112b08070c0b040303110c0616050f040b0a20030c070b0322050f071d01050109080a030c02 64
    0x60307890070480255031800c0480d446505000001440d203c2009041d204500310544075071640c0c603201d80d10341002e002802d8805201000c250340d00c1007840703c0b00103140c20a005004034074075850980c110080403150180e900002c021010403840402c0704030583d800c1c9003042c1840b03685030300680241076031050b02c41d0020301c0407401034030307407641d0003840344400c040c1c44119907405541c60001a501030506152400007041a00400c11050ba5007101e40b04250365000440c6034000d85d1030303150030342c020004500040d10040011030740f090b031410005801440740f14400e0128188141d421000e848900030f0a61044050000303000c18845950414003a20800665240c00302e01d040800100002c840d01038100c411143c0c100042c1c4100c4401c04001b01030040000c5100c0c1407540c03804010701c20002c803041e42c06a4202c1c90344103050090090811504101e012100207907114981d035034030fa48090500400c03c000c03115000100004040d0b00800c219000c03260004042d01e030a5a25940c21104040d0704103040b079006640d105d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 979773758 1250 979772508 979772527
    0xc0305030412150e52080309060d050c0906040e0901240603020f0904020415080f0154060e0c071707120c060f060b180409080703021509010e06070e0303 67
    0x2800166003100700210302555644540244981740c1050700b00803040e41c41000511420f0300c404d0115000750b1001031001443d502e500000c51807134800e000801c2e40c080030116001c107050b0801da001600821941e0020040311500814518402d90343c051105110041500100040c6010f5001040c1001079105800d1403c7c4031100000d04076086600441e01e504445030400b02250740102a082e0071009103035207440742e03614021000f103a60001040003001e585003090120040c1103000130350203449080c001c2c10304840b180c816920301950781c4403010060607400d00c5000a121100b1080c1c05001c1e80c201078009140003085c0d02c41e03a0070f4412100e10000381c12410002c3d20042500039003402032300e0040f50384900c051307030b10345c24004107582c0e0b2294051481880d20f04100500d460001c1200c0825018069502111000d000000d004181000740a0a032480c006070040c2010350104042440100c9a8100d160f65100c1c644028201c0e6044201c0180c0346d40610041400c4600030055002000001021203113042c1148 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 979775008 1250 979773758 979773853
    0x18020409051e0a1404020607021207030b0604060b07050d030c11030d060e07050a0f0e01091d090105280506120d0e0a150503130c0305030412150e 64
    0x2115002c40018070304110540c41d841110215401940000051100300c1c42c5201000d09040c010300028420000000c04200b151603000c504400250349038241e6401c01e640c2e007400740d0024070459006101d6840d01c40b01180481202040e5803005030090300800c0c0c070100d10b2006400420001039001c061000140c10012200d0040006201d400311110010078144d2501b41400c20381e40d0083e014400b031040501c03680c03181643c402180e407406915881d2007260900c459005903050550760300941d4030416540c181c1c000c1c3e041075078042401160000001c20051b0b5400803000aa8564400c1ea18012071491850200c08a80c03900400c2d00404001c1c6101d080340030202d1150300d0400945002c2011400040c2c0c00348991400d5000f0400801c4016580c841c030701d2250f07034000e110784002404940d44001c0013511909000301031315a4800345500c5402c90f966191034bc000214009180c1208489e21100582c1010554090b405170300d0606058500134411f0b007030005d030000c01a4480b154056600d1204009140c90850038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 979776258 1250 979775008 979775011
    0x70501110c0109021011030a0305310b0a05042001031b0e10050313060218180f0a0605090705160b1302030c100203031f05040213180903091802040905 66
    0x1c000003d090320952041c84008180070070340c0d5080c400c20f00c0003403a166001008842d40c0c28141d290005690355482a907101e0702c000b007800500b40b0588440c0101ca411842508170000a000b14039071000c9030764680c407040a0b51000c6130000c0c04800e4030340f2007400c010a841c0f40350000307602c1410301007020031340040c80100303190b40c0c02c1d05407000810200c1c03a6449428140d01e8000311100ac0d251241c91890040c0301d840c80341d4007252000703100e5035000030140344000664003041390107000102a0f00d506801403452191a2109031194000c1c0c220314004140c91130082e216803401c58401500709041030f0f84210f001c0d0303050b400104540c80080c0c10b104058000030143d00a185c85505005100150b8035094010725240c80c0e8001c000b1400b40044041c0c50030403d40000940f54044100301014100389000c6a032180f040c00c1d194406074115001040008000b12040402d03810f03030303030520311595014140c101501c00f1395100c05d001502090504000f4003007090254400101070501c1c01c005441c080d907e01e040300803510b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 979777508 1250 979776258 979776277
    0xa09170106030f23120901050a03090c150207140312030403021609050109060e0f0f0601110318090a1505062a0604050c0d0309050f0109080105180c030a03050d0207050111 75
    0x118407031060b04000041005241002c603e5005061035045c03920108039070300c40d1040c020305000c000700c0c0b580140c1d442504103600701680801c80c0300e40030342c2c0c500b000000d13401b0340480320016000c3c2010204801c1d540064202e00709500a00030080e00c914003800910990000d00b00b07038110b0080e48521030600f82c255450300010000c8103c00146507142003402402c030350054120041d074180e11401d2012880d100e060341600461865858603c640312280141c898410000407151103000100e15404041ea090890002104064402c499565140200c6404590318400d283c01001c0200301c00303000070704094001c3c15a1f20458003038076104c1d859007161394140030b801166800c0710b80c2c0004200000c205040c0642c020002d000c0e82d4aa010000c1e503500603004990501506e80075540c0d007003040321903a11860b816001032039800001c015508cc51445110540311001d8001070710b109219800449040006840c0003254165694900340752011040102030341c0440d4040d5031940d00c1e40041000c03030001e0001040c42d5203 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 979778758 1250 979777508 979777523
    0x711030109050c030f030a05040e18060408031005220b010201060815160e09041104090212010c0908060c160203010902150d060f050607020d0f050105100509010b0a09170106030f 78
    0x400f010940b41105007600b20400760010305c2142100d40d04030040e2001d40e80d090001c0045642e503e14040c1c1e210200d1302030b5000520591090109001d060001940034080740304802c0c03a52a2a4010f00132190703070009a400c2c079682c840044600c00070040e0700031040c69105200101d0100c0c2d030f641301c06181c101c5d56808030b540011490140007950a10200c11740f1039082070704240b011501d01c44001004083c0c02000a045690855a039001c90755650b07100e0689950f00510f42c08802015203102c034002c084600780040812002d00d80461252000542544100560720040d40b4060325901c0034181003000b10001c03a01507480d104618010780c0c41302c000141506030181e10300d0320303a11420307844826510701d640a0000180e0030759080c425a00e07203800f1a402103405030748501d4004280e00d480720003a66050005400e5519010a111b0f48103041c1c40224100d4504035148903880c0d0301e41c860a0030754840d181c20000800c04540040140a51525058242c642d4250000803140d0352a2120f00c5034910b680b0084594a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 979780008 1250 979778758 979778773
    0x40f050d0201020a080604150501120906090f140c03211c0516090e0403030b0f03011a041a0904030806061c061802030925080f060603190302070b071103010905 70
    0x13641d101307200703603031112088800740f2000c1071814280108994a00401f030401c00b0410000003444c1d002d4018076151507100000b0040500d59040c4681c07560440142102d03401c600c0e50b0208411800050200b0340340d00700401410002480c030381c0c1074800c0311407056441500e55050240d592242030140500d0304420201c940816207240203000e905246021070100c4c001c0c441e14000520801c1d0000304e130326510030703458100011503051750000036803120007084a183c3c1c19801c11003484506030100311001c0107080141c4092180d0210041a810001c400409070340d040382e698000200400e11541c0300e1340c0c00030406001c1d00d00c0d0425a03007040d04a440b8140104041507100c2200300200c1d1880d4440c08215544001d0071804c41c00d1003c441c58440c03c803054806141c0701e03c3c0780000c1205000c030f80f03040000e000d50021039082e00c00402c0015100c003000c4a600d8801c2c002c0c0d403284035240b031029641c10522a81903010344800741c00c001c000101038000c2c2c2d40030307150500041719074622070700c007407140104840c0140001d0030706 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 979781258 1250 979780008 979780027
    0x305120c0705030609060411060729010506070803060d03050c03070c05130e031206150a030902090f01060f14070c08030705070f0f05120f0111041703030c0d05040f050d020102 77
    0x701561a072001d80a58042e9041206240d001b241582d00298000719001c5c803540c402d000100fa0303014000c80600b070f00341c0c075080c1c5c2a0700700003100c29450352002050039a903250b0f0369007003041842d001e11840980010000c00c0007440b82c0c03070860012100c50384070741802410070155502d010b1441c0c2000900304c1c0c0401d00e0203030604c01c038600302c518205008081c0d807052082ca070110100380c0e200c1c0107000c2410106a100c2c008070324a90b952440e02101c12100b22189500c44480000040191103001c0b402d80c01441e6440114455941e0500d0314bd05a803400d0301c0c0c4849101e000701c0b0803074183e030300b525030009402414000c4800003104510100700820041c0025520740209080c40703414017207180e11086481101002c1000b01d84040c0300c00d282214000c5400141880000c0c071301c1401e0846422018101e5440e10f1200380712054480060410f0307840d141c00f500010f00d4265101c655a200a40b00101120000d00800d002c1c0d01d02608059406032140361401445e044583e141450940768043c40c0300542d4002c22b90489 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 979782508 1250 979781258 979781263
    0x109140607020c10051602010c170a1202041a07061b050a0807230f0408030c07061103030402061611090f191509270f0b01050103021812070305120c 65
    0x40c103e50445000b00c14214145016046101c3c0c0c00e402c161203400c1c12151429a03006494811004d038210a0340ba108100000d884201507100801072401300b00c09030003c90072001c0078425901030307231000c1d468a082c51000005078600303030304900012142a03842e00001d40240803a44188e4410b84116218161910100348018013040740080040c4200000003802846c00305000591501400c0c0c2c5180b01551440001c0240c8014861070b00440010b1000040a84c10640001030282c12030348940c3e90005902c42c5200b05c070b9200d00c41582e020b9480300342030001c14440d54002a820051070b02c01e03c20703110720f5588031001c108000d02c1198116500c0444108229002c0500ba000302c1d8003522400c0200401204c0707040d032011032429070103800b14055940208104070007040c0010307a034501e210703850300c43c0d2000c0c0780c0751084609107506011918082e0440001610303501034026261800320840480383c284101006019454040e540c0c0c10105128503c400004075205000030199051039030074469803182e40e8000b03d0b1 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 979783758 1250 979782508 979782523
    0x706050711010507050a14240f060111070605030c070213060609080307170310120c0f090c08150a0902070602040815220f020a1d0c03010815040203010914060702 71
    0x341404010405500080c4010404c100025800b0400202c0d42c911f03803c2c1c0728507001c000710061140301c0070a220320500c92200951a4881c0e90788500a0301550b9403103004580c2c0c4440d801403c40b01d54009030301401301d40d000c0d02c0610750250055811345c1c100030311500016580501203001d000c3e126034a581c144800c40c0d01a8030040600030b80c0005504d0a01d8580e9450b1030482d01a00e00d1402d4500840420002d40d10140c01c42d000b070180e400d00c410711300150300b001410701556100341c1c6c1b41c4000c0d890f40000c0080460040042101e100d403a1100c10355542a0070b80850042c500045034407524014020410038150701c00307010b8090254400603211800d1100c0103280007590b051016003505032500304042c1d403000070701e1400225220395890030951024a409045e0420340d100c020742c001440390b008568580540c2c0c0c2c2034084420b5805c210516161b006404240d48020b005082c80c9410200c9048002c141030915140c2061024000044040003615411003003515407004000d00d8104105101106e0750412540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 979785008 1250 979783758 979783793
    0x1170a020a090f0f03030e062a1b180a1506030b0f06031b0f09041409010b01080603030a0302070305090d0c05032406120a060f0606090b0f030703110c07060507 70
    0x1814184c10a03800c0380c09901d45110080030000d4611494034030f9100d483c295005624914600d51089140c4044500b0764000d80b88141918427a182201c007070070081c425403030b80b800400740c40300301003e42a0091a0030540e0041108104a44901c0d81018111030340341410002c00450390006900104902081103840b10882c0c1c20380b14000501c2071082180f040c10003010b0150246031103035a42d400300707480d04100340154081581e11a1405c4900b658030040700040b02d00c5050444020031261000e0001581d0b8600140c4101d50141e0060029000b114080c4c0e00038980d83d40241065800c0c414001c001401c042100b160448280007410001c10440c10200f1400b0780700c2040398100d03020048241f00c00490100c0050000748140c9500746018000f51040c004040c078950010382c10700c0000901011400509210b02c20040010628a00011500c01c10f60035200b18294500b0140c1c5140c0f81d44000314003624a0445140004008002c1e0704100c5400f00450401403107035031256a1a0703191400c0104510742c418125 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 979786258 1250 979785008 979785029
    0x3031e090b0f0901020703060c0302070c08152701150821161514160504030b04080a02010608030d050106090501110309010c17041e060e03030a0e01170a020a09 70
    0x30300c507003041003056400c0c0e000e0b2000c12a40310740c40c00c1c0041303142940580c80981040c0c80d1011100000340d05400a10400d40070b00e0000d030180756100c01e40f41e0f84203141e07005100d500c1c00303503c0800e00d428121901200150802c074221545015080384490071160704900800c0700042030242003020716002e003d440601046016416850300c142900d442d001d00c1200390a00c030340c006000a001c02c11107807014141d0201c0400b28100150b042c0300b060041410710664035840ca4002e1031500e041c40300c3c0304000700e4065a51181e01d64550380c8855139034547c10b41008141e0380c295502d800d00461100e100b00050070910b45800d0cc0420300307502d44075001c2c0080b801c2d82c03c81810070403804c0c13a0602c200400012609400c44c2071030420144032040c04e000320b03500141c07119401d49220019001480c420400720b030a064084a01c40ca14000c1d0340d5040c10360302c40a4403200c09030550024004500c0d12030080e9034404445070706040456100c07042e120600302440f0f003200c001c09040ea02040d071100c0c09901258200182210020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 979787508 1250 979786258 979786277
    0x5030c0d03090303080703021905070312110703080903191d0301050c093d030501091812050d09030503183706060b25020f041a0a03031e 60
    0x700184114818040a010321500340003003100c1505c00d80c110b50f0003181c40340521207084004c0d0002040c03a4002502a0300060280c0f000001c008824410400f03031580c031818042c40c001c2547d900303454949009000a03e00c1c0018480c00103004180440c9140b0b4071240d07615880c00340a95880300b032000c1d0180350064007a07171406d000c105919448104844105e0400c071450020440103d000c030710f21680044041407140c04400252100c080c013450141d80700c0505407001d01c02c41c2e80300c90070030b021298030b20b409045400c50740680c231003c2a000c030041c00c91030860746007417886c1000c8040184280c4d401d20100b00c0001c0d800000300032017282c0c0c2451900300d484424002e048400b211a901c500e440e441e400c1e00092031310020346c54487c040b224080746103165921584c00d2200554400c400c1c00150030043ca82c004001050052041000c00d415580c84000c0c0d00400480058400b02e06101c02082900d40a00c00400348030b20611941d80d0b00c54070b0300025440b03691000f6809600607d02075174207200c030400c0c0041c0700e02c10300d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 979788758 1250 979787508 979787513
    0x2a02030309010806040e010c0806100806062203050d17070f0f030515120703140f12090a180902010e010f0219020102070f0b09010f0e1806040b03030406050405030c0d 73
    0x1007103800250091034107402c1c58031a0300004005040386400086d081d840c107114141003e030005080e91141c4070442c1d0106e910b850b00030b42a200401c1c111410796102000700043c0c070b8010342c4200042103c004500c000c01a06440b5514540341141900720f000104001c5070252000e00c03c0740c40e010b0740c04400c901c0c1c4043d0040014001900b82e51191000c0401e040d22040012041601004801c40111000700304201da440c800d0f203000e454004500003030307510108000f01640685000600d003003100701c00400800701d0840001c1034107410340060705e00b19071110700c03050001841032100381040000c05291000042e8084980300151444140d020500c1c18000750702c03404c5e04140e0300400c0803019030700d01800e000518410703840103e04241094100b120402080b803c0421510500405001035600c03c1c0c8840360550740312102912169088003070942d1041c1000503001c62258000011a04402d0141c000326041441400203801c540068003c507001440103d000c200c146800c0005141c030307910039500d4145903030194 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 979790008 1250 979788758 979788763
    0x1909020315090118031710050603040b0405120705030d0501150c06050a020c0a0c08120403080a030e0705030d0e01021b0f060f0d090b15040e03041512020a2a0203 71
    0x10041c07190360340070100054041d0402c0d000356280440d510070b0608404014076003c1c004001c04400050015510740000c0d070301e000c10501d520245c0c0c3c001000303681140e55542e80c0c415000310041040750103001d05030001c61031024030400380c00501e2007440030315103d4072035200707580864a0507804211041c0550031100b11311500018030000c8650030003000706260761095440300181c0710341040741106e40300c2c40c2c480310240b010008a401c10340d140300382910007022602e041d4207800c0c0294040070f000410100501503102e030080e8041140c29203104103813115160341c2e1001074102071100080e0800b1441d170525590940d07a042c000045815810211415804d045d8400300f07050381d0034030605034080d520001f420011414410207841401d103a00d2024812280d05203081503009000b40c0b0b80d511060242c0c1824036180c506402031610140701c1800541c105413510201c122002c80d411800003d01001070300345070940c0610f00061010010a48481089401d1031031001c0c4900c2420300001018002e41ca090001603602 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 979791258 1250 979790008 979790023
    0xf02041b080a09050c0d0303060302120c130903031b02010204090e0a0c1419090b040c050306010c0b1003140138040c0306090c021e0c01080c0c160e19090203 69
    0x920000450184514001e4a85103103010b00c540c6c4001c84060b03a900701685508400b090320310030750b0702e0710914900f118065500c1e0992902140c0c02940380c04440f102592a42c000540d041c024074001c1100000641198040b90101002c80c005035000a02071242c900d29000c0e140800c90303010000d200e0456680c460700865010341c0189000c0d600740b04000005960b4184420103040f4051049880d00340d03854180713000808054005600450411546851075070282c0141c030310621041c1c448003030307a00c1184d81d600050380303000b8040007100c085160040085400c000c070b0440c0c0000c006000155280ca00000200c0036540c00c404c01c04020000d050000c5240c8a480c0741c1c250302c04003030f2000314071106212400d40107072505400c010035851030b00d800c0584003980010f03403c4943c0d02c029848001131880205003900c0b410200704450100320b805002c5120b074030244c1c0060031245500030a4030000349101d8081d114003182503010018414024007408070011015003c412100e00e046004c1168050350350200362160b40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 979792508 1250 979791258 979791271
    0xa1410050306061003150815060609010503150312070f061103010b0a0305070309060e0102090405071407033501031106120f04020409050706031401140a15020102160f02041b08 77
    0x1490004c103960a0080d00034034800aa0681c0d0300302d000c2d44404000742d90700c0340080d400c600c03600c0540200d0058200074045464400040c3c0d1181e144d650341442c0140485039941e5155054440c040040250801201c05406a076205600d14400003940d81020425030302c0302000507490340070410040007107411080803110002c3c1e503070402042c03da0322a80207400410420380c000e02858145441c0d890140d0066004201405048408002e40d884840b82181c8a103032800050500da1410895000440c1c05007540c00ca203411511400709032005800d180e1801c07044052103a2800405605c0107004100801c800703160a260240c44050600020304211458801d02424603d43d06030700001190941d02e071600030042850300310302103506480c3c1d40d910040040a60800e080b050075a80e80022403c0d1064100820821500078102c2c04050304045081c20a603a40e962490705666007086965480940c440c10f0202d254021500c1c1a0301c01118010301c02601c1d0180000d41c09040e240000040c1c264201c50b80d81d40004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 979793758 1250 979792508 979792519
    0x50a090507020d0807110a2405010b040603110708070503041d040c260d0e0102010614182703040611010509060708180f160806070c081c050a141005030606 68
    0x1201c0b1782c415039855a502803962041c0c0a403080050510600e08001207007035000307000119000c8007642d4030004988003030041802c040380400c001c000c02c6100b41c0001d41c1c10401665003601d408519980c64015078402a021216604041070030400c440ea184054003444401d510180c0d070f2840c2655039554208540c1c0940e0f90100100901240071410701600c44144171980b604450000501d8240504208003121049005608101c3d0205a80403061940c4a07500009000405424401186141516801441c41082c0740c5003804a40031012141c4440d01c2c04a0510041c50382d40342410b40c010010320051110402e00e178106030500c050040c00080803540107215242c89403007a107400300c4d05103d0752550354041c0703d54442c0301e40510050401103040e107010006040500b01c080d43e940c07000c94032450202c9000010809071034240d40030a440c800242403410710100c6003200e024403140c0201c110340c0140c80d2910f02e00e9894041c0008050000c0407a034020940c0e4004c141041e02e440d001a0b6140c1c402810107000302e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 979795008 1250 979793758 979793761
    0x30a060e0c0a0c080d0608010e0601090b030d1d012102030f0f27250e010504090b070509060403170d0f06180f0213120c090b0a09150915050a090507020d08 68
    0x8172280d200b0000b9051a20007401001320741300c0d005a841c030003070098000c001c4c548441c084562400003815000e01d682a01d8045a82e04821100c040e608400c8030618103010100c46146c030400d075091101c04550200b03400050301c0741010603404455401c002d22005140700c511060010011015107114592071604504141e04001110294200b00c00c503000741d15246920207444802076040184841900d07141c8805051907a60341042105440d9142d50140400d0034810100f00c14038818401013a58400142038903103480e9407a62400600d00524040c1d10600201141d82c420304402d80c051041611320500040c0a05130510101e04445d451101d40601c905584512584035070707486e6019185900110f00070000060b644400320802c50310710f103004994030a2400004038140be0701c0d1181e64210500a010035071000d007400c50000040403505121030041c0c0324907200094102c070b90700035212094084802d08469620b13003420702045103640e42112001c0f9090000704402e0f2540050120b5100050b440c4c2102c2c10b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 979796258 1250 979795008 979795027
    0x9060304020a0b0c030703030e06060906010f090312030c030f0903270314030a022514030a0c0f060207050a1a25110a0503010c020a120212030a060e0c0a0c08 69
    0x480e0598003d1092110100c0c4c0b480da0040080040c1612070b000792401d0003c0710449a070203880b814101c80d000c0d4450010341c00300703017a94405c02000c081514075082844215881c2d4a4481540762000c8100300000d845010b42c20300311794180179481c0303900c0440f0340500c1700034159139003c2d000c0c4121485200142c0c8480524106080c03806000c100155004850507400c2e14485c078845031a58403281320b08000d8450308500400040e80b40e04207007100010103544030748071414021aa0b002c142c01040855041c414401c5072004211440b0814004000d0051000c07800c5d407074140068101030595010302e204801c040410804598000c0c2a0800460300c0f03281590399240001c040c40c10b2020b0090550044d413100d10803841001207151140c0c2c0340d1041200c051060641c0d5804140c240c50003104418010307000000180f001508100105005840c2c0b80180c450034410520fa6140a400071111641265281c00041140000501d10302e03401044590180f031601e0103107040900341c001c0b4018020154034000521152 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 979797508 1250 979796258 979796269
    0x1d06010b0c011508010204030c0f0308030a05040201050705010c080609010515090603040609120e01080f01120308250e13020427060b0a0c060e010507020d0c0c030c080609070506040b0906030402 85
    0x9550758200c2c03031490f42030303120b0075218001e40103408116035011a182022515002c00340d00d8400b03c96000724103926543c1d80e80c0c1c19502400b000743c03040b4184101444507900080080c060705030b2003401c0c0d81c2da542c180c0ca00301c0c00f045070050044c3d104500842c0e0181000018161250488501050585034690780c1c0d141d91a040005220b0f003500034001400040f100ea9059900c9201650006000d0340c400f0490b4844005200382401d0a01c2241070f20800290044000780c0144019a8001d070034110a08519182e900380c0324030841560001c50025681082d121340c3c9140100d10301a6810038004114200707800c1190480181742624000e1017038080e041c2859100024903001000540074102d80d064580d0741200024080d2007103a14201c0b1054102210b4094118051280038031800d041e034000d040b805e03034071901030f83d003ca402d05007a522001500004000700b081612030f1001880000300402040c507000c080300e400c02c50b154004500c0780c407003000108080b40940050b282c81000403034007aa40c81c2c03151b200042c1d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 979798758 1250 979797508 979797521
    0x2d0618031b03080712020d0509012f1b1c051e03071a0a0b030c010914150a081e010806010506030903090904060b15120114030a150507031d06010b0c01 66
    0x2c00038100090f000b003c0001701c4140c1020a407054080b121900c01450040d41d040c09202d160350b00003207a60718807103074155813546d60000107840d80f0480e1201c6488115254100217000e0b1442c84104043c4000c4002404d0212a11000c03c82c12510700000f204195105500e503140c48902040036500003c21940f00c51051084660f0a58490342c800f01d039521410254041030400c4a44e94081441c103121b01d909814085682182c0300b20507594080d80c0c90801083c90118040c03401c0c2d107a040020210a26a0010000010682d001040e102d800944c5403d0f00c61800c8080f40940a036004001000100103540b00041d019064a0003203461903141d0b40d8800c2d4261071801401d0120b43e100741801c0a100600103190700600c0400416550711400c0c1034581e401e82d44500c42d44017050b01d840701100041090031107103400310315004002420790311500000d850308030030000031001d40b144840d99282403100b919058030840d14030b4103803403000360000c0210000050b141c0105126070141c1850004140c400e40304291b1111 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 979800008 1250 979798758 979798763
    0xb1812030f281e1e0809030c03041e0b130513091209081212040204110f120105031006030f0b04020a05190e0f0105030d030b04062d0618031b03 63
    0x605501d01e803030384000c20320102104044070b9400001400c2e03084a01c071304100c1d20000d02407042e60901494482040703422120003050310341c0e0f600043c061100d0050741800200024500f10800c6503035a0206404480610300da40d10200310000c00f003003440072070003042d46103d00321502110a0448620084003502c050903004100401150103c4022243c441e00001c055099440c02021980072403010982c0107004e104203800500c00780c0c1580000b400602d0300307400c8540c140c40749000b6682000e09400300305080d5003122085007640404400140031030705041000c0030007040303003980500074a80b440d159000202161100501014019800103080d0746039548241c00502c009812103030140782030078010348108614065040600c0d58600801c2c2c5007041c0c285c00e507050700c00041c00b80c02d58002000c401c2c0c000f490090309403500281c4a040000d13004507030003040c4841d0018041d007685246501c0400c0c0c21046603942000090000f5408801a414500389000007030741d5015599102d11540881010b0b44101c030f07603000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 979801258 1250 979800008 979800067
    0x4050d1b091b0f110a021c0b011211190605030411100c0606050a0f15110709060e1303080105060903070308070302030c07080d050f0307030e070b1812030f 68
    0x660a0b180841c48201200741c00c1c5545000124140e10011200d052412108082a910010107a8054a42098891101200841155804440c3d03903214800044241d1021211201201402d028000d1031044110511011644806c100089400c0c41c4031100701c0b4040c420422078080001070400030000114401c0000c02821040681100c15004080140c1280100c1d01c80d4100880080d40c3d05012080c8402d41d10f01e60b070000c007054206100300b840034030103e020108100621403071801c82031090196002030805100042030345410401079650b080d0014260b0341508203041c10107000b10780d009095a0558208a072501d580300038420009242000541018150020000d150b10800d80c000000f000e5405100c000d85010fa50350380c04d001d1311031880f00031050100704100049402d1103441f81c01194040307014100029562061400540b0300308040c0c016020300707080001d4540080c1d41c80800c0100784401102d03841444041c01c0d5010340c072401412040c1000b40d802040060175511000c08074228559501003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 979802508 1250 979801258 979801271
    0x5090c0307090b0f03010b0f0111032b0c050316050f090a120516120605061c1b080129012102041401030203040302061303210f0b0604050d1b09 63
    0xc0000141101090399102d050882540d01d245c2c181030150300d52110000713240c800c401e0a5040150368510122802d000316010400c9800800d010180d1a00003450b0800c4a144030401840007010440300c111212401707124080c000c10040d80d2a00b01c03c0c1c03410720741c0b92170110745905640069401c3c1d40a208640da502c4a17480c2008980d40074211202c880c0c0c9030196045841c00c0036003101240281d070440c06444070245003102d6080104200d60800d54110101414404c0020030100e00c4900b00e154022007140c03078241484004856050312500c210140c00c070a002006040e075000f0b03d2900c90901520507011280c100021485c4c1a0302130b20302c00d50020161600071140e2442d18038042d00950142c00346007085500c100f40c441c80e9500ca0310079648a80c0d455001401d1544030104200e43d54943c0000803420803625468510130721200c6181440a1400c01c500841c852003104508020ba6001e480702d90700411041c0020051a501d02c0c2d110382c00302d0703080714283c14010200760104088071555044043c41608249 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 979803758 1250 979802508 979802519
    0xf1201020a110d1110020c0a12020f07091a0114040807031505070516061a031c0801050312070312060b07030f08070e0604060509010c05100b03070602011e05090c0307 73
    0x25208001182c100003078628207410524103075406048413003083c940e44e000b4981c00c041d802c026801080d80016550403103200407203503500c0385025148001000010b81000f881420381000420800c409040403041c14800034400410010001a40261031410000380c00e004030760040d60042142c01406c031400503a50281c0c0c032414081c040851469002c03912030b2070680000c52151045060750341c0310a4114220b04c014100307489034030103071885180b060040303c60741c072440066075010440c030103a03c50090304030740d2003014500c8080c200f801c0c140e001500980028482001070020b00c0100c6400e5079050401c02c03549809940030500911840d0020a0b14120000301c1e9014182c012642d51003507141992800e0055407001381c2120b455604015450308440c00344024024907000340080c040a40043c17600102c889583d469041c44c1c030407040d0754a00d031981d45a01020040c1014041e6130054480c9000a0010540c0203188075030300c0081080d42080d450356072003c26049401481603401100d001421210b1858540 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 979805008 1250 979803758 979803767
    0x2010c021e03060a061a180406141e13021b060708011403010903020706140f0706050a06150c0b061314012303070e063d050304110f1201020a 62
    0x101030900c03910480d4000ba54500c458050b04080d1410380280045006200c01c0c000c1e6103807c9100c8004000e80286091039841d02e840c41244000e0030000d01c05400c412992061000300c100b07078090034108541043c00618075888000f44020030107220a001a55a1110707005001e5820300500e08403414010700c01030180c000c2c0d004060905a07045868803104018070401090300721015024010096040160100810343c028107940c00c005064a851a18000c1c0301c0255542561200c1000c4039069518020b000200100d881084c02404440820754034150150740003404080300c00e13000800300c00e01d11001030295101c000d24a000c80b54207201c140540d02c00e05038880010402406a10750004410050114038611a8503002e2242c9019014140b11410a040d4070460702e4014102600030683e0395200c00d4401e8610f500c81d64040512041d00000310000f82580e01c840d1910380b0260420006005100c0454508600052103d80840f51003151040400c0403070300c02c6051000d4200c1e95480400c01c505240d400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 979806258 1250 979805008 979805059
    0x101d1b0412080702130c120c03150617060102010b0a090209040609020316170c1e09060a1d06070c092a0306030b0906010e0f040606090c0f110708031602010c02 70
    0xc558411448412101344070440705021b0300000000c500c400c0780d4044020961069800c031505103004540400034501e00248104554401e4000030b41803103080204060400140d504004244020320802e150000041c003840018001c80011036800240342c0c0099a41e50f110000600c010a0155101d02d4002d00742403840b28002039600200700c3c040640441245840d040711b1055450311215801e02c0d24902c1c50428010070b840103a00400d804000c0c1d244155a114041c040c8c4198590720080c0801800c20030305c1c0e0b46d101c4161110701850083c032000c00010034034941d03407050b907003650400205421001c10403002c601090442d02c82540401180e10031040d03258001206481c02124070406d5905e840002c01c2d0707203030710074801e070320703083d0100c4002c1050444c680b0140c5402c18021640864640e03103c5042da011070305100e0b640c0010070a41505100c500707070403000240ca04000740c806840d12901d841c0000ea01d03840b0f1203240e16560300354002410f086a000d1041d8003182900500700d00a0034001d003c452105001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 979807508 1250 979806258 979806263
    0x4141c030f05060a230415170f031c0c1b08040911030402100309051005010803120718142214130c0e0c041706101d1b04120807 56
    0x9010000d0564142040402c04451550a079001c1100200005c15816000c1040d410b910580758080104a0340400c00104082c00c44105041c0384015000d481c503242140007010000c098205110401800760b0048900c80060918200415501d219000490759070440d42d130120744581e02c07011848140001440070b00261407880d80308106490b901808038095000884000f0351116009000e0441a4402d801071003480c0e00c43c034100d48680f8036281c0c4c001c044d24026040448a0350000c100100d0103c210044650061501e081170001d07280c032060260000c900d14020000c20000458184910b03032101ca1104c0810599500b60010040340d810030100a80261103011089401d100c01260041c07610348040750f2003950140b0b0100030989803000d40d0b200000024091000301c0018000018540d0301c44070741920a09003031001d01542e240c0002210400600c58020940d81b15807140045070318100d8008464208050540b422800c03030540703000300e40b41e204d03a800c60034100350030800083c2004050340103042c0651 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 979808758 1250 979807508 979807511
    0xa03030905010605192102030f0c091e240402040308181c060e0a0c080c0a0e01060219140109030c060b06091804051509030a03050c0f0304141c030f 65
    0x81d0b480d0100840741c2c005207000e400d100d004140400c03140d036010b140f205102942d907921b01d00703416141e0000b90501500d5440074155812203201c0c51020310f45020166405890405503409520358220907a61900008001c0f8100100801706d090301c4e20441d251007100210018001d42d0b95584a142444540c0c1008120349a1081440314420a9241440400d0500c400601034600b4080c3c240d11810003421101284507158007620018102098000354540c020300540c800406403d0381d01402e010051080ba44000710304d103070b0007005000f450f0b03000c54418540310410441c4c50011006041600600e20710020b41c415a61901052908042d04441503e0805003d1541000064002403d11506100c1e03417440311361204003d40c003612800741001031150400e00410450300318450b0620703814505a019100c00c0542c1d072010407490841e540c507009150b403000e40301036007030304060040040e200a400080c1c001080c1c1034202001d43d02601c000c0080c0204003942000006c1b1100300c918019000b003103948401c100c3c0700d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 979810008 1250 979808758 979808771
    0xb0301050705030438181914010911090c0d110c100b030303070e0f0603150901090b0d03030c0513060503090d0c0f0305092d01090e04230a0606090507020120091306080a0303090501 79
    0x40b4041c0705600c11250440030040c9082802f0040100300d15004025002810042c848104014680d00c901180c60f10b4650009964807802c49007907151100c040c5000210301d08140300b01d0f40c0d945000c401e0b02d03003050650500450045507000002e01c8092408040c540083c1c022042068501411a41c40b441c44020b5860301407598a0300030800035a2940ba540c1604440c20b8252040020f102c0c0c1d10a8040f1300407483c0081c10a000c5070008403043d40d031a0300c5180011400700030320405000901c07480034080454200310849410325520a40d0b08451030360080c0034484003240381d01c455200c14103e11103000d41c0560718021004c1361500c41c142a9070070782c0e80e2800580c203240003141c1007a001c4c041c0781c0180d41020343c1115002c81c48007540b50b01000401950b46900500c4014070002d05e0398011500608400e0b880800c080c9400300000b401c40b0390700e00b0304080c28840710004002000c0d650040300e82d0000203813402c4442108030445030f80034040541c8105090310921022400f415850740c04004800e20490090100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 979811258 1250 979810008 979810043
    0x606060305071407230a03030b030c18040f030e09040507030c0b0c0c240a050912120a030209010302090a0e1f0b090d02040b03010507050304381819 65
    0x2000124001c40070300c89030803c28180420b400a082c08582c8603885c0301c00300402d0060034030a05094400000f200400d8032003d40d441070b40303070901002d0f0002006448601005040c0343c04061300c800d0140015081504102001040c0b5105108548152001801c034a5850400303141c142e56070f1000d0300c0141d0f01075007800400309410340c0074021120035054500080c082101210204825040f2001070140e80c1c1d04240f11042a03a00aa4080e08a58100351109500c1e0490310081c4080003075480210161a0001c0c41c03c10f004000300010ba4040360550b00d0011380340c002c9480103030020301c43c0f0203c1581c45045508006040f501c0c5a40300342c03081485901d41620318407000c0c030b00c40340c40034580185540d03003000b4012030302ca40c2800c2c50340c0110140010004904205d80c40c1c040307403c45c2d41c15545040002e900004000501c0300044e4418a850310801108110705160801040131212a071011007074144c42802244500600c3d188090300500014180d640c02e4010741400d803200001718404690001d1402c0c103c600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 979812508 1250 979811258 979811267
    0x5090309060409051005040c020706030608033406050f06130c0f0e0324070207060c020d321f050402031e07091e0b0f1807020703060207060606030507 66
    0x221201034001400c2c1810f101c4110041d1070001c200b00000c0844040004e1241d560340148140c80205401402c200780c10300d08010b0559140740c2000800ba40100308a2007005192015030f50301071085c1001c50813000704200d14880d4450881000340400b402e1100340801c0006007820a4010042161030070300c5071030341c122000143c80220644401182c00000395111190192000d1381c14004010182c1700d0480c401256581080802c00c0d00071884a50300c005c125415804010060251038281400e820540013940000d0005090003001007680c83c00f80c03900c1a0360310242082c4484d10407040601c641507c401034032140c1d51104501020b41140714429409210b20301885880e019540281c00341000194000541c1000c140c0f000a100d12403280000008250140c0d01c520006c07c0600c2220034129501035403800160382050440d64400c6c41d03800ca17a840f59a031038500300d800d448030004200311941d41e907140036410f040781640701404040c000221070b82009440d0307024070140ca0300c6480801003038441c814201e4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 979813758 1250 979812508 979812517
    0x1324090608060901030b090c13060e06030a0c09020f0705031602090a06080307060908070c0e0610030506010c0f06021608030109060e04050312101809061407020d03020915040810050903 81
    0xf90000c1400e00140082a4810040e9901804160072030300005040400303d0620111803403078200301039543d0000c1c070a141d41800c80a0704408101c00030414070505803103010b100e8010b0700c20304070510342c0002c802c281c3e004a030050b142c4854001c0183c82d00c600040c0c0b010303030101c400c5000491143d0b41c100d000946884c2584209d4055440c031200450034104281c0e143c20080040c088180c075482c0c03051182c0d00005540c00002000303442600405a036074100304d000c0c271414040d00c1c00c40c0b8040c1360078038040003d0b60b64800070001046030481c4a010300480b15040200c02841030600c42c0390302c281159141018070107100300440c100c500c59107007001425650310110070304400a41d80108960001c020034029580810086034214806081b484c03d4503945441e003000f1006d00707030440703003020f9217881c030102c02e00c0700c0384c400c0130b50b00c0c0002c0c0d02c404540c1c68800b0340203481e0b0181d028190249640031580d4100c1da16600708078100300c0026002c655550340c0b02c20b42e0035541c5d0900c2c00c214500e50704000000e1043d800c0801500c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 979815008 1250 979813758 979813771
    0x10e120a0225050409260a1d0103140a2306060702360402040c030b06030c070c090c021609090f020402091c060510140a0b1324090608 59
    0xe1103205858811101e40202e007045140100000d0704000c202c90307a6902c40d03a000548030b144240c40701d0094042820130040c00c5400714506c90b006210758a4100c0d040307848651070312803030010f070803580840c03000613230091114079124041c00030043c04020451032a54000201c8420f440d016080d801c0504d440d244501d00100d070002e400450600400006062034600113640c0d40740d80035411000d0102c01500d40f0580d00e03d1548543c0404010148401d45c1032510a17095942c4061034240aa03034a210086040c0d880050f0601805920000b400418050b101c40910081c1030f01078070503c01294001c070025034561444c640c0400c0798450100c00036070354002c0d103d0880d0b0303541d000b80d82d09010300e03681d02000003c0d004180071035008503200c1444209940324006010300305104080014440c01c03c1c140e40404a0016082000d045d052110380300c00d248e071800d001004560000a00350303a02c440203903045110506c50740c40981500234007a00809503600144055400c509290b450141003991000111080c10701503c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 979816258 1250 979815008 979815013
    0x1c0f1407050c120f0105070c1703070807210e030d14011809150504031218081210050a090501080d05041404150b0d0b0a15050d05100f030302010e120a02 67
    0x20b04681406034683e07030b28012034030645409009984c0c3c500d09440c4106e550800150703802101c0001c00984c00300000d4841d0822a040381180303052a4050074281015001200b4015a072848858100d09400c00c1c201944c4400000d208040410b04021f6803600206c06980380075050a0381600212810400c20341202c0c4401d40080c2d800558422040c0141501c260139101c540c80701c4884403281e905d038082c0c40d02031480f03660346004113605c0d002c1c0e140403283c0320480240d2a001c2c40c1090404141c07008155241120041c40c07602d07964803841581c2c1d01070492030780000c5d0450300c072501c00070340c5540d590b201c44d040307440a01c141c444030150401304503802e1040f8000c280803002401d00042c005d003056030000202104190030301c140a03441d005244021b401001445d090191900d602001d1420304d0b100346001016020640c3e20b041c103040001410030300a801c01543c08075070300c00000b000920f002621000503d480e10805120300e4407820000e001e0300a007440310000744501f054500a2000d81c0e03040360b081c58100d070301 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 979817508 1250 979816258 979816273
    0x4030b0412301b12060504020c0705041104080118050606010201061a0d0f0e01020403290f07020106050d0303050406050906160e04020c1902010f050f0d0b01021c0f140705 75
    0x4007006071141070301010038a942d406190500400c3c0300aa0840410561142040a804048540d050700e20a40005000e1030045c000050540c000044450964404403800300d0180c0e40d1003201c41d041d0046500106c19036007050b46a6540766031035990000c480307001d8025107505695890069007681d840303104030040220141c1d5220300b0300c4403000c00b402c120f80480da80810241c0c0f04103003020540c0c200d8050581e1503503000500f00104081c8030b07000c50b142c290031301500d20f411610201741658080d00420001d400036140300001c400d28070039807104010f8140104500d600c90900d041c001c3c000c1c81c04860458205203840d01246043c42d00169082c4201e20012201c07101c2d43c500704080f2100c000e4000000e8001d902440f00c0368041c00240f0000c440100b00c1a55a112401c041c00010300700d03102d8842c904180301c81002401301c0c2c2d02201089038000400b212000c0344100403500101d01d0100600c84c070708155500304030003ca0182c0c0c4a51402000c210305e82c0ca02c0c00520040e9440099486950801006640082e1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 979818758 1250 979817508 979817567
    0x1009020a0e04020d060908070c0605040504140c0d0b0a0801050114090132040b030a0f051203010f091a120c030c12060a09050309030f0709050a0b01020a0201030f1104030b0412 77
    0x4000318030040c4114860342c141002365480d2065800f041c1c03c0303080400c4010900740b0550030035114020708040040313100760007070406981083c101e00c03440c900f002c40c00391640e01415454544401100003401100b00800142d03a42e02d40382071321084d100c4100d81c494a090f400000300209108400080f0100c200580c140b03850b0301200044000034075100d51600a901e8840d026031941c0d0500180003114061070f5990060600b6113481400c000c400d2007400a00c0105000502411820403440c01c250b500004000825006d03018400780048042200d05502c0400d000b8003101101011030b0200000a041d0110b41001030760004100f80c01c4145da420155940c4084001120021150040500b0f02d01440989250a04a02c00700307007401820146a01c0b80d80c0000c034200308100103482240da000f00c13108003c0001c45007100c0001d44840d10710130b000e81056101d400d02d80c05c0f055158064a004181c095100740d5035030b07403881d00248098044405440700301e03c8074a4410781c540130300500c20304500c100080145202501 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 979820008 1250 979818758 979818761
    0xf060b0a020c09060a051305060a05100206070302070510020a05071502040b070809040204120503030f0c1303060c021c030e15010b07170702060304060b030f010c080106050a050c1009020a0e04020d06 87
    0x415042e8085d08036003001400392a0510050480760101344081703807901e801028096900300c2a4810390060780c1650307500070020b5000c2071a0342c00c55821325026030b41e005982402460030b2a5082c45003120b610000b180e00003d074109004040c4240b168888500305242c00c240700003240254031402c0130203401000b45074001203804006089042005000600f4a40c9a0300784004c1010710360411510b640c40007041c043e400080000c1d5a50245101d05034500e071603c0c0254049200e001c80c0310082525031a1050a900c6034000e00c0340e00070040501014000c00c03010107100030013034011100182c206005501c00407030b900075141c2000d4140d9990318101450810700341d82e4013415810340e0007901203200302804800b0042c0e5a40c4002e41c080e90281c0c40205484c48130b0000c040c140340c030503841000340d80c0c900003103020b10540080540e41114241c0c2040382d1540320260090741c0c2c034824030341e40341c1c818000c01c403803c0515407032540040c40890003580d1031000c850721560302408040041e039010358007010f0303010f082c000540035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 979821258 1250 979820008 979820011
    0x90501121b12150b040e0a0903020d0c050c150406030b04111603050d090501090b06060c0c37081212010308030a020702130509011b0804080a021204090f060b0a020c09 73
    0x76480000c0c2030322030148240c00d044468104c9100e56400042c02c0040c00340e03150000307811049040082045051641d406561090b02030412000c2c00500100607050110030301142141c65409000074040580010148405d94480e02915010910b4400c1000320760910344140700c003082e0b4a255440c640040c4200800b0941d00c0c901044003081000c012070028481c03180524400c8600c00c0c000840d009140340380401c403110000701214040c050504c00b2200700b2000007142c41c000e6509aa42c1e44d00c001c03484100800d00481000d5000c00620001c1490740e0360002c500c8401c0c200c40404066401c0a140c1c144401e00c24440c4c1055580403241020050012454003002103800103d002c000602c0c1c086903502184c6d030740c0d00740240f040901c1d94a104010344000c0a001d02003c0c060742c800d080868500020f0050207000340500054100341c000f0a50401d054001c00481e500d107211a00100e807166984c910910250807914030194400c0d0900c000041c0700d107425000c0d07801d10180d603005040208010320520014060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 979822508 1250 979821258 979821287
    0xf0305011508270a0804150e09060d02120f06090c0d0c1802041d071805100c060b0307080f0c010212121e0a0f060807050105030106051315090501121b 66
    0x3d2441000032400c102c0007050034481e03500581c80754034241c40d091102010f14881c0040c450603c94001c07903552403003070290384200700f125803004465090012464442208181d508207101c1c40c0003420040800040c81d80c8034080200c00c1f9800780390400103204003440c140704000c0400d01003c8052002d600c0c520b00065107a0070308840117041030750702d45003c20095540f10f0344040b00a58941440f40c103e078070194980b4980094403000c4081840e01c000304400c1e5209000362400c104d4811148000c1001c41d4104910004c001001c4400841d02d404183e03842e419800700d00441d503c5451203203c90f950010411f1410942c060701030b9418811241611104140000e21032010180c0740e04400c444018030403400360203044008800503c46039002c4403e011140103030032089090b0301040013040a03a90240407241503612610f003107510f418090f0200710080c19103030803480d4180c09450030164005d0f40309100d401101e0003680e4480381080516020001c5404032101070003010134210361004094016040030710041da = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 979823758 1250 979822508 979822561
    0x209030606100c08070f03021501061e050d02040b1201120b060d080c06010906080c0a0b04030303090227071e08040318080f010f0c0206070c02040f0902100f0305011508 74
    0x91096440d1601d5038000341003107440d20068840a4241f50b810450340c00504500c28440321503504180300a404001020701c10882031110013200011141301e03806460314007104c02020b545450302c0b00381081c129080311210010508208000048003110300f17081c07905107a0055800ba2850f00c660040c04103d0000d84401d0390355240c00c01422014507010890036008000000000440c039041004030703801d04403400700381c0344942c07103418080c05615506011101142c0d80350800042c1c00707000b8400300e944203043c910480494909801d0b00d5054854521607030703120349000d5541c4c20304841010644a40c80c4007511000c1c0003c2d1400000500180c01006080e081840d171700d400101066554007880d00d451010070a542080e5100d04e4001d551015030f01a441101392640094405482d001600500712071484501a01c596200c041030201c481c07071940079103030b40c0790050040d044010b002e0748003074174151211003100c0009281000004440d1601e1060014a01040c1e8401c1015200d83c200c00c0d0a84a03903d03d49040741 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 979825008 1250 979823758 979823777
    0x10030603080304110108060a1d09010b030a0c0302090a0509101109030f011406010507081c0f110a0e1c030c020307081c0207090605151e0310090f020903060610 70
    0x10300700700c040d6124521030200c1480e02400a00010301228000c0c107141e01030101000c1c140b01e42d680084008070711022200300c2c4c80380c0f5a6070205150140081d0840c064142c0607281c60602800703018100704056900946d02d5202945070300301405c0c02c65104583c3c2141d183c1210f60804c0c17032607950f0307000381450603603e10001d814046860000fa0811405c4280c070140e0341c0d5206400343d42002c0c00d01465621642c02d080c03042c1003d20ba51580600c522032121440c0c0015218a02e103940403404d68005d02003241452004c00981004100c03480d41e5510203400c400209100c403049264500c0c050898049410000b04450700c074403040e0340c007030b9680c42c0407020880c3d15000325400880d40e42ea08000660395006100403aa80601048401909200c03068010306052404c00c2418002c07612885a403200280035560701e07980e01ca90315a070304000c0303100c40032100040080010a028401d414803102800b82c42d4070120400c0b02d9014021101c0480c89910441a010380100001038501e24100305d09a814014908042c8140b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 979826258 1250 979825008 979825013
    0x203040303120b0d150f0e010c090303322a1009020f0303280c0519020301020c120406090e0603250b040806220f02060307031d01020711030a03050910030603 69
    0x30040c102417a1640155030f130b603403040c5421a502500d01c0214401c0001c0045480f07921000b01008078600004e428032200d050b4003419940e0003290102e501035072145090149842802d0884070782d1100d508061120100105a8041000484401600c00030107006113100450313502c1c44006011180305c242e82c00354100c0c5010000d901c0038002018940c9003c0303450403440c040090701c100d0b5040302060350030810090741c85d01c0b00081c41c0011100c07100700004420b81e85141952000a001e4800c0328501d400c05e01038854000f040c1d0000340003038800d4985581f11242441e4884c581f07080c0c2d10b03404440a0f94185d00414200081254006490a44020309000c902400d81c4a40303403c0c400d80e1041d88035009541c040d0f400c1004c01740e0400e0500c039040d10f044118280c2d84455441c2c20b2001c00d06640060702c202c100101050760140281e009144904041041243c0c01c0a000d044a0007500400c80a540031b10200028072014a00800d030462016030680b80c19040a2004003030010140403565083c05240c0c2d1364401101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 979827508 1250 979826258 979826273
    0x6150105160b0a0612050a0f02040b030a1202070803070804090209030f0a121b03230c07030f1403250c0f120512030c122d07020606010203040303120b0d 67
    0x2603409203490002d6420103005440c210340c42035021901c02c42e1556003d600203140481c031449090f4020060750300c0c40c452030000900070b03c8600d040f59414403800360508100000c00540c1010340e442502699505907888594035100e208080c8004c0421400308001d100300d005a5001e040740b04000760407070300f009240703403103503851300d400403030180d074031888500145014076882520400400454072944207406015503000e4035888485084481e0040c0e13907114808030f20240340a441d005e04030703d8112424156a03090030005003600007419112091b1500e00440741980c000304444400401203100c0011481100c007203072703481058500803641003d229200140c00b0664161074030150460b443c08000e4900c0a280891610f601c000b0321341401c45042c010003800050794019590000b03806030f491941541d0300ca070300d00b004005040b040e0f10391800045150008480b85041244a0180703602210301640311719005903900d000744d12000300003510707900203038603501c415411240300da00b40545440d01c2070a0f50b90f5040c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 979828758 1250 979827508 979827547
    0x160c0306020a0801090b150d0c03090606171e0606060703120203250915050921010e071e0501030911120d020706031e0506030a0b07050702040b060c06150105 69
    0x280020f1020005118076440c611504e0100d0608403001c0c0349590003c50769543d03900582410003103440e82c421050801c14002d8120741015984024104a6a40c035020203000441141694a460f48584003900c4001e00055402002c0402e00d040202016542c400030050a540070b25821000c0110700e2507200c550307010070300195010366200d0103100750741d90100410a0820780c0c2c0712040030400442e24401c02002909290f88440c003c40740c0740076a0b4400102d004180b40006000d16044601540032803002c0703507403040d4005a100040034040d250907507030b5000309403201401c5c081051043d00c41220104007543c026444081d070540304404034801080500000381c007050041c1d01005198108003944c0c0074040e8144002c4000c1c1590342010003001c1540200305003924400c0300c88103016036079000440c030f9a03030f030400c10000020352000200340b25241c0440b006025402c83c8500728020303410700a040080d0b10344603040e00c07008100c204c003c2c0510781d203940040180c0d4944044050502800700503e1904409445048 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 979830008 1250 979828758 979828777
    0x1e0503070c120b06061905090d1e0204060b0406020318040e0f0a03080109140a110906030c0712050301050d260c010608060106080106020a030c15020c01090b07080705160c030602 78
    0x1400900d03043c0c100758a000e580200b140e4800e1408005000020014600c082180c1890740340c0151220142008140b141280303d80c00b6201c140b0a00d12994440c024883c00d84541e4400ea400380409940d40d0055442805217000d83d20150700244604a031000500b4412800300e0340c0100085903501980c0502814000100b9545c04c039900012445828140c0015140d4010100f02d101001900310880145401c00005005c03511f12580390451500100c0e10300c010b0381c038010401402c0707075030b6030800240c00704030381e031100104a07514500701c151500900d01940580e8100c0d03602611001005a1641e034991942045402680e10900d484081e0081e05007a0006050070141441c000546103042201c074a02d40841644910100850f11005119907940800d1150150ba450f05002454100c18600000110220092420154404210111000d005401480500d0301035260450561507111040701c00220403120344000c031382c04100101100111002c4040041d0081080034810382e1241e4900c41a0b902c409000d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 979831258 1250 979830008 979830029
    0x3070c23060f0a0f02060618040c032f04050c03040303090c081b030618070b0310050306070903020423190209031b19051e03031908160503041e0503070c 67
    0x240f9511508040c00d010030060a00040219162400000307194240100580d044404600c0104080022207241074014503480285c0800eaa0705c2e000300a41c003c2910384081c50b18820340c07000c5600c0d50601c1c0c80380c0350044150318102899a130b0b941c0c80940c040d0551103030440e08416045400658000c0074043c5416401141500c094041ca9007000c00d85400c50281c00f901017407800310107450350a0000106001200d0810142030386030b039580c512080a840c5a940015054020482000b0103540e115924a0a41e4070072103041000d0300340080d02d0380744a090341d400d2031a40740345640402d0101440c1c4105003403107107100f40090b25182031500032030700b0040d8041184030541c02000351511345250142c4124501d80700b80030300125123407420340001d0070304250307040c42452a60340007103243c0700d5101803003158071f01c1030180a501d51b10820184010320b14842144d00319881004004031015075403003402164003e54001481e9a50351900c041c5160038a0a0040c040f54944001c0000c000010040030f860070082000400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 979832508 1250 979831258 979831267
    0x15060809070627030b060f060906070b0402010909090305070606080d0210020f0903030403110a0506190e010908063907080c012403030e01171b090d150b0303070c23060f 74
    0x520000c1c05e4400d01c1f017441120300340700804a42c0c991740f050354070258100740b0352956500e40c0e00060320f47c41c009401c603002041c10052a02d040c9500700e00141042e511a40082105955442c03900351540c00c206410360040e0881c40f60440c0250b000c0d005010380709503d0841c5407820001c00002880c69010b070340708444403100807048000620300003400134000c01c020740e4050314007002e06c500d0907405a43e184c40542030018400007081c191340308070581c4006e00a013008a50a600f0004032a45000743c0840b000140c60000078205e58110380d40088003141a031101054905203907907982c40c15113980281c401d0060a640c0c6418040d40750f0b0141c1069010300c0c801910a1030810f0450038003d2412201d145d2441c140112684014142440c50104917440b420340c600d980070004820705407200c03a02c6110703aa030b588500112240028400500c2c070070380301080c004804000b1502500189500e07401904005080703d10302c80f0782000884064048281e00344003250100e4002017010300000c0c1c907070704061030f403405041c004103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 979833758 1250 979832508 979832521
    0x42403023f1e0a020d151d010303050406031a090112021e01171e19050109140412030f0c0f110f06040b0907050409030801050f04060f0510050d02040303020115060809070627030b 78
    0xa86511f0856900c417842c0401d50704546018040384603d1081c441019030b5903d01c85109110100e01c9482c03100b000f031404031596500d1010190b00c0701d070604180d01c1503145040d020307505500013108442900f030603164a202014802981e030a1031600512201820414044e50701c100c1c81e60900041c42070010084111012081c04405001c41c0c505800c83c101140c07030049000c0c1901c21540003654025848000d00300141084e070300480203010440300142e000b0f1300382b95007100b580f50000800d401e803000541c0d48410320b00c11612902d6a03805500501c0c000d90300008081000b1404591003583e1000c020021126003c1c1e490313001c0f07030840348090340540014041400600652902e0007503410340e064215402d1040d1414405808103040b114469a4030a16502103001000c50082041c0c602002960908545481d564140640644089105842d2010440402080d1140a0b0b109180518040e0000b031074943c0c10501c054601700010948039a00c1590b035103d103030380300c600f201c80c460107503200314045400c40c1040d6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 979835008 1250 979833758 979833779
    0xc120601062a020d111011010b0103140703050711160611031306030b031002041e0501050708090f180a0e060903042403023f1e0a020d15 60
    0xc05030100041d061035070040c80c40c981c03210200c5560100c50300208407142c0c1c90304c0820208843da10540211b100b41d020f519031500051161040c0c480b000c020f02850740508011421144c45d03400d444e03000e40c0400c020816452081c1c4c0a00d034891136504014003010003c001c198a001e40810407080d50009028050006903408611001c5401d01000103505118a0401c6e10720401d600b801900c00305541c44c1d086055690741003000700c1069030100400c55450b9110014119440a10407406d1119140e201000807d94462411030350f800b03030010442c900b4031004204125286c903c1040c40355115544440103000c0420504405000b850039000c0090b402c0c2d00320984908200000304040300c42e030000d1004110007800711888409181d80401c80011414201d40d05500030b000304140c402107002070090406922502c40540c142100700001500391007400452450b01c1a40100c407200703122040b0030b00f221200d02a00c00346540101030160301505000f04e0030503d50448481c1e0004084101c0c0d00c40f0204208000d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 979836258 1250 979835008 979835027
    0x403121701030807020108071b0609170301050d0b1315150b0c0d080c040b0406020708150127092108091b0111070f0b1c0c0207090e0c12060106 63
    0x3605450400307585142c0301c50209004202000e81801512000184800d1007400301c000a5113403040f60043e03c40060400c50000c0000c01021100b80d405d03503500103410312554041d04e048039001003110081c0b4a880d0303100c028015001e0000ea22104a00ca0b4010000310b86032103a600100c4813610004409204601d800f42c0c0c0821540700703241c0040304000050b50114003140070454814203052208540c1c44150b4030000340c4c4207541c1316229228012030045002507020070440b00f107881c813030100c0f19805e040c2400c1c09543c0c0000e200d43c401e142100d00900301e001c0c80d01c0f00500c0c124403030741da0000f40d0b116003501c45400549c0c04a011008038520744512251140d0408043e17500150761200070703d01009140d0180c00328501c0c03e803109040c486050b080c10200700c02044510042c0c01d0440c007a420156032818007200307a401117420340710002d203200a150740400e85072086003e4984c082d8002c0c50701910b083c0c00c0d03100410446000407002d000e407880140207a1501000103200c0040350b0b00410380c0390301d4404018009030341e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 979837508 1250 979836258 979836287
    0xb0c03190506010509100e060d0c0f031107060e0307020a090507030c020f1027060515030f060c090a09060f0302090f1005060f0403141b0a03020a0e06040908040312 72
    0x589010b000403668488103541400b0800e0303603110740c1d8000320901a5120078003a03e545a21020025091074901c010303401084206407140c03030345d170b2412a2514090302a29510014480c0800c0d003171043c50041680c1c1c1e040700d107030000703810242d038a040c1403500885e04a0707a5541014009548079802d00100d1a450b10500315460050310140c0f00800302c0510807030701d03140700e4524203d060f6254041d681f10365a880c80c489408606412000f0160080d1b4508000a003404503041c56190788807454590250902081d4030140035006000340c170099480503a0040950844860036070403510034200401c41116512440024209600014440a145104000b0300800041040c8d241550350014081e14240d04650441683c504880513602c4024841c44d007540c030f000781c0d8400b800803190344d0580c4501c00004102c17009040002d81001e07984507000000d01c090841c6610000790808042002042007100c1107410940140e401040800c2071341c1c0c07d454075040741d007180d0015600000344080704000305421041507090700d03c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 979838758 1250 979837508 979837511
    0x601180b1314060f041a0c0d0c06180206030f220f0b0718150203090901060305040b01270203090708031323010e0f0a0812040924031203090b0c0319 65
    0x566054102004d03000d6407041c0002481800076140003518500d0a0b110009502c0381251081c21b401c0d00300034000626007101b5113a640c07424890289408081c0f01410f16160050b020707601d10b459010040500300310040a00d003150303020721021a40d00c40c030740b61010402401201031880c000841c0c180100d440d8030103000356043c000795030648181d20900910100460300c56405000d0300310303012481a030642c8104c0c1e031865445501d80d000811070385d40580c420b600a078002d40c4001e026a0305c564020400210b007c05d454480500304412800d20f922580003558030920144c1030f56625640e49581918641100502c0c110b05145101c01344150700703084030031581c4508420030b280c030b40d5004c101c0041d0a000c0ca20301d034a400b5040e400c4100d22140c0716600340c0310050540c5402c17170711a8159580c41055582050040b603031002d0238008284c01c40814042009884030218074516201c92556645108403000c03818140c051544800900011424250181d0320409c000005296a8500892012404900151400041c9 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 979840008 1250 979838758 979838767
    0x10f0f05060408070e0403030605180106030507030504031b030903051e061e010905060105091807111b240a0504050a050330070203030412060605030a0503030601180b131406 76
    0x8009610005c603549040c010000d07442d0b030f0508802804494100a0b088030400c542c0340d2070340804100150480f820b942c3d040001d910342040850a031902036070090000b503911104490321038000c03281d44421510900f40341c08075550300c2d510941050850420301c0e01000c0c0a914030209110140300440d071016031002e40440c0b0218512280d602c0b600c044c060300c200f181c0d80300000b41103a4018070840b80c64403001403c0c0544560070070105107000d50200c912200040d003455003200c00040019244009000710304145015202440600c000500e40e0304100800840414680040c0e481000042145a2a60791501d547d14181010f001a109807507101c00d009501501400d00b00050035140c1c01e4014110685a400f20178406042d100b182c010f010020390305000000300040c1e110180701e1030820aa00c80d0005000c4c3e6075030b400426854031004003010304607401c03c000190056100c2d140307400c03020140a41e150401501c80c1c0980040b034000d080902c800d1307280388506100c07000030710030440e1451000322251850b2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 979841258 1250 979840008 979840019
    0x7050913060602010e031303080f0c19020f04060302060f030703090c031b06050a021510080d0203030103060b030303010609090e01060e04030c0516290c01050f0f0f0f0c03040203010b0603010f0f050604 88
    0x800321f54400500240408661813030840003200442c3c41f0b04181204031046203d202d000d55192108000e812403249400e564150100c1c03d0901926003101c0d001401039040c9a0b1f1a41d4602c0154001842d1008050380c4411010020341484204d90185016008404450354415401d14000850b40c02c0241440014808908981e074006682c0c0140c1a41400c010b0583d01c0d403e039a030715601110303009102035000d402c01c0c0e0b0a00e140e001001d0750499004a005000000c01c200601d5140d11003800780b0800100356101c14001003100e50440021060604000a442c556501d04031f89906001d8904030001007084c02d524051080410602c01071800d55400d03001e100740317011001c0380ca14411042c4c0c902e075090341001c00d26490036034100342d039840c900300d800902c041e2611503107048094001300e0300d6288504032480480c034094401643c072885182091050443d90702d840315002d1090f003000340300301e0f030541d2070744c010f009103841d12006140209280000b05a290703042132040d4510346090f2300520700484051004000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 979842508 1250 979841258 979841287
    0x3050f15011b02090c1c020910080403091503020703020606010230070506090c1009180209061603020f010614090103140f0102131d041a07050913060602010e03 70
    0x90100c42402d0080c0c002480c42d000c02c1c0e1400103500040e500002c1340b030410007944822401880d10b5a1041010b0802440b0764070b1520407400b8810060f600b00b4003944240b03240a000307440840c6c100380a0308040c8c0c0b40390360301e440310700c4600682290346000940100e03840c0100342e010044203801080034005040d5003e40e40d08010408241c10002850458011143c0594200058115005280c026081c3c4200d454410480796803410803032442030040d003551000c0f800301841a59000103071111940708030045c0038211a050301035040000010303480801004a0280c1e40480070303040310680d00c40d40103030122242da0039a4030301b10781c090b6002102e0307903440b40658102507484820960640794421412160110a03492051600c8614400c5020541c80003600c001c92441340450181200c039030b4881020051240512070b0a80c0704140c60050013600b040c0005c50040104e200e000364090405c0c5803d0b07007020b0701e80c000a07408020914940040c4ca680b2a401d0140c01d40c20f0041c8000c0d1240f5100a5117400c01084100340c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 979843758 1250 979842508 979842541
    0xc0608012313020714070312210507050c150a06080a020306040b07110703110a271d190c0b070503030a0e07050d0312060e0610030207080403020a0806040303050f 71
    0x188101440c061049a07086140e05841186800a11800c1d04480301740209584e46924041510341c4100d00c240100710a00c03072103007480c810411280381d01540007800c4c1250090100a0902014480140b15031407010070100007481107010740700484007950400c9041d020446600d42c00240040c0c01000c149005070b1000250190065480103902d021070b0b41d610350444501c03031a071100f941503000d40540001031004032024040e000e002294100001031340c481d210141d80280031515a601141d2550241e0b46840070b40c021a1035405442191041c0c591120303c403802e00c4558200c1d2102017259001d2001840554103080d0003400506050781d140101c1078540b9a52400014214002581c882c0407003141c44105101d210700034030300500700115880035450050300761f240c00c1904403051440d0540005000c03070030541442c0280c4c2c01406a001e05031010004801940c07040c4426280700c001084000010389910120300014030032500a81a2820b052074010141c0d10090111408480f0318001d2001e21403001c1501c9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 979845008 1250 979843758 979843829
    0x507020927070602210f121f030f1509080307120e010614090a0b030706030b010206060a0b030106111e07061407080d02091f0302040f0803120c031b070c060801 70
    0x5054417002e00300400b940c8100b000b8462507030404a2500c2c8405880c0030071600444042600b88000c08001c80b884041001038840500b0300c030a1849090042100c4260903011500c0510000c81d001055440307041c0694401d980100001b0707410f500d003910440c00340c400c200c41c0403001402444254070303140b108128240b182541910500205022072181070740340d44a407118500103010b5941090b0f4840c0c1c040c0050841104050250003160300060f1685850070744a030680c1d46481003d0b05507400c00e04211814401d0003d0304540307200f5090100c280300b821514000740c1c00524401810840d00b070080c0100f03110f012043d0f120f0000c0052105000051407a019540014440480183c0f00c003920380001d08181842c40c03101d032100340244542c44035184d1540040081e507456a5010560359500c0100c1b5580f0304ca004460110640b00b4004034600b40545001150017580705000f2202c051100700c0007803003035489150119000b100c444010005c56800a8820303004007854002e6046100381075a03000f1071904641900c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 979846258 1250 979845008 979845043
    0x501050907260c090c0d1802090a140411010507170c0d051213020612100911040506031611061009140606070f0606181505040e030412030507020927070602 68
    0x2125036140509480b00c1b0000d0348000e11852024914183c140e44280605900410440c400207203070303070707140e014420f5080c56002044c44107a4494132030174200d0b9225806103040150800940e008146429411001001030095145e603402410b1106881d0001c0c8101c0c01c0709222007070000d0004061000d840c0c0350702007140d0200480c03d0f20b081c0300060981c42010100c00c1c413201381809210345150003045180a45034003100401c4607403818220071146004a1081d00c1d803000040001910740c40500d0280c00840320f10b81003141001090380042400c020f4103c80c04407041141b642c0070080180c160040c4050841c42c0380d107a400078105200401c1c0e6910641c0005017610031007445603410003040e603001c40010300003001158500c06203a0b681742d0281c990402c4454010545c46404140d070710706841030f045d83d80d100900462501c0d1901407504003040d00e90030f0643c2400f005020110141e201c42011500c64140e028544201c50b040f080e124004103a0342280d80c841d0760080c0018400c00c0e4000607101c0d91140070264 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 979847508 1250 979846258 979846261
    0x209180703080c010b010215092d06040803090106050109261f020a0206010e070e0d0c0e0a272a05040c08010302180408030601080c070501050907260c09 67
    0x126a141200650000b42102c400054403440c250041d4029040c1e03030001da013030303441081040081e42e014510649020001d9001049140314440650040800700710310b04528490b1460900301103810140200c5043d50722460010401004035820312030440a00381c242010084141861810102504a4110b503583c100c842c03e4018542801044210401100400c41800078807001d10054041d40144013003c0140c455480007080d204d22240b6911b106606035924040d102070024104000c03142d1654054880c07244000300800c00464100001c0e2140700541004070f028811400c10140007410441d661b104003400c0c0c071031140003ca5482e4507074108114020003101c1e45404070b2203c88015074070341c010750f442351a01c0c24201c0c0254005041034103c03402199080207a00b280c0b001914040f0040318010600032080002030b030740c3e40c02511075540041c140c0017094107200e20f942e03400b0f00310b40080c1c03007405095102c03203010807106064101e00506d0f84038201140c5504040120095641d120039503644d44512064030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 979848758 1250 979847508 979847551
    0x308060f010507020306072003030112060c0909050112021f140306031f090c1e05040f020d09060608010b01141603170a0501141002190602040b0a05090f030a0209 71
    0x2c06496800b40c005041d190340f400d00c81e401a01c0c200410300c00f0f00036038118050307124110b0408000c1d40e0403158125208410b41c11240c4ea00c40c010480340203608280207028801050f40322031845541d000c0c01a03140070015104440c01081100fa0304007000c01c01940e001c00c0c10b41d003a581e01c000d5184d000c0031444a21038a94807001d001030308050241e0b000000d00942d0680e500802c141c96000001010b0103401806202d81d110f56110b540340d10312202c15100c80041c080200840c1c1469800030615040d80c0c10010308015032043d002e000d41d4200302d400d403030944d00e8803010f1206000a105180b110300782420b000300c1e4054207820a071a68000c0e013000c5600110300141c01402c1c58011205c00900500c52880002c45147c80413152000386028041c440c03141340c040003600c0c11414640401ca20808080e0001c101007d600e0314545950440752a0484490303030241310002d480c211220282c0401d420790344480780c03204e04d01d100f4800070b5510401c07910310a40c000d00100300940c540307600315034000001c0090000341c0f48100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 979850008 1250 979848758 979848767
    0x403090509011d042102060f01080c150706151d0601030b01120e010912050706050105220e1f0b1507020a03030c110310060510020f030a0c03020705120a0215070308060f01 75
    0x81d00075200d1030585c5280031403542d01091103403148041504c4151a41d0b2601d5899554054000c010f9400524107440500e005441d14060800c2c0d80c030441c03010618111500c242c02880c1e60070350240342140e0b9049042410000c03c443e01d90781c8040c0a06c0d081000500e2500002d001c8588031900c1c440c041d944100000400d1f00039005900c026404c200c0c080c0c4210380340c0e14001c100d42c0c091402a540b051401c000400c0c1850420a1451205a000f144a81560148a003d8010300f0042e00050040c8142014942c1c100c0240c91581c0c44100060b41c000f400d4000c42050001512000c0c115002c6c0060400400d001643e4085410060366010303d0503910240c000d2500e01d46080140040a40c10300c644448010801010340000d020f40340181d801254104950b03400342e942d0307240030480302e6a903001030100c82545407149216400082c02481100d04081c1d65001249200042c600c20f42010b030000860b10080d403d0040040724208010010b01c6d02d0072000c0e84004002c454050300d01d80c850805121900720680c480c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 979851258 1250 979850008 979850033
    0x515091906120e0c0f0411040f05090901090215091c0302061e0c070303020c030409020d050615090307150c0c0b030a0e0706050a1b02090f090f010b01080c0a180603050403090509011d04 81
    0x5103d403042d2388a8840586034022512440b44a2040900b000000d1403070303006020703030820194047c084280c1d0102d801325104032070700022440c0e80c0100400c00c640c44c1c4044085900160a80242c010b80220304101540d0651000e406000c2c2c020304203400140720320303107400c90210b4100781e4040c500161110b00010a0508622a9606c03400e0100e0020581d40762008890303004502401003200c08101c80700101b0350050013802810200b43e45900140b00401001c1001e801c0a842030340a40303000607940c140b40e40c5034a40b038002900030806514001c0304101d5405240e2050028090a00c07004200580c03030124014443d1145100701b00400c80072034102e080014480f00e01e0142240c2c02400c0b41841d1410b152440251042165160f81300c0c41440644205240184280d0304180740c107039175800c0c0c543d640c6030052100758042000c20041042d000d074084c164003280a104000b811941d07030b01007450304060400404250941e0015071040c11240010170580c0203800c400380030350707481d050000420390b01d40c10a005940300 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 979852508 1250 979851258 979851281
    0xe1c030e030a021b010c32030a0c050f0f030a0e01090f06050c1b031b0d0203030c0a0309090203012102030f030a021f0c090515091906120e0c0f04 64
    0x46100a00140c0118184221414aa041c0c10b1321840c3c0100444012200312000b41480b130744285548000e018803500c3c0a40c03045003e1081c61300c1c0c050314aa0b41c0c40e5900454200c1c000903d40590f69003005010310500e4081c00513607008000c010001410240c032482180040e00030b1018601d44030003564005e44044004000618441c01044e9845001504c40e074014001201c9a000d0200b41c0e115407200010780811010f4003070020901134204a0494004110280003141c1c8075442c0b040d1400180c1e01040145060900580034000200751454081c0c1504865001100d0542c0144014481ca80d4800034400007002c807841d41c07030107084c003600201e0b0405079000104c4202c2e00001407140e440c15000a89601c107021501014900140c03185204801c88107254a00b40009000d02c1302000b86140c030710440860201c04003c1c96142c143d00c000011005e50217506400e11194940038100f1606c0d81100d401801440300304c03018842510202140c0d5162480c40d0f100300c0c4544c0020b56072603125200c0741e001040161 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 979853758 1250 979852508 979852513
    0xe010806191e0e0c0108040c15030f11120c0f1222110a051e011404090e071d04030c32030c010e15070c0618110a0501030e1c030e 57
    0xb5803a8001d5000750000b400f90441c039103e2903140301c0c1d665204500d454451078010680810303640c141a8840e40841c500d8000c8130070180c84880500840005100c2c942c01c20303518210302070f40c45484190f8862440c800501c403246030b13003080c01000c104420240850f5011441d000200b0307950fa450003100f004001d0032801001d00b0070802c100703400401c00c2440d848031140c001250b4071201c035a9501c1c10040820702510b40001c5000b40f0b8406181194040d6001da412a0340c5d520b80142031540303c103c907074112200958280e00c0c1c0d5200039010007086511327280f4610070120f94294811b05103440d85016100d4102410028110b41d9542010190b0445840c058481d0200a42c0c0000c1d0b5000140d0310152781c1e4000d4240307117050f5440c0040340c0406860000d00e1809509440c90307001c01c0c981d66402c0a07180500004000d88806840300110364100b000502c0d4440c541d4031680c100185049240240888107000e608101e060504e0031703540010507c400581e003241c0703c86060100c0c0540b000030900320054464403078014400e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 979855008 1250 979853758 979853801
    0x120b01140604180c230706020c0304170303070306050f0f010f14131e03050607112e060f0f180f1419140408071106041403070e01080619 60
    0x70389190708400c4246031541c5e200010a0091100c80c1c0741e4401000054001400c02c02a803000501c2580140c58100216002ea0b1300b03041da6030042161048010400000d070744c000104020255405104520260401b03035803003207001e0080000300307a41c0070045074054107000d504088164002e05c518401c080c0e143c0d082c42510b440380020a50f1001c40c07007184c041c0305c00406a80803540c000d00d0528040d142182c0d00040244510381f500700d000d640080b500fa0318062035000307072200d5141180301a140005554141441b0304202840042080100c2d0200c0e000728800d81c02203041081407003203814152055a0000101c0c40c444680b6403e030300001d2a400a8081e0043c1c10704442408081031030307580b1842007002d11000b09101149004240495406a20b03240a61000074041004a00e8540141544c1440344818501300301d01c54002951035001640720b41d10100805509000509042c0300e8035004221039040442e075541801c2002e07403210030040015a00d8009550651440c1005401240d40313820000b4405000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 979856115 1107 979855008 979855049
    0xf0305011b2304081f0b041104051912080403120507030c030507020301020d2909040506040204020702150f030609090a02010c1b0816030606120b01140604 68
    0xb09035810310012640200400c0420051000310340c11340b5100083c0e0302181d056440802c2603600541c20490701c5040f221900301038400381c5d0800c50706d5120000d41c50b903e2074000d11380340c0d00010804201c41802e0382808200300040060340e00881c4081219410620292098070841d48014002681d4608290100e446440038011180c80107001500e084014801c0e80b0517140311039840781e50544603c10b00660030300d00d04244c040c0c41c88246c5045c0c41f1450203446089d180c50008001a0007030303400286100442d5121805400d5880d580240b00e62610680c0c0020b250907002202e40074024070010021800380303003002440035000d035816948c11640802c1943c544400c0c140501c003103990100e001c00086030381d81040c8880c000b80803903800e50101103851410000c0540c3c01c2640b090205034150385046022444100c002c505441107199104031845030a00416810702c076a43c8090400080401004c91 = true := by decide +kernel

theorem cover : BRFrame.Cov 979676258 979856115 := by
  have h0 := BRFrame.cov_init 979676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 979676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 979676258 ≤ n) (h2 : n < 979856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
