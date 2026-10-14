-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:25:31.435978+00:00
-- url     : https://prove2.me/submissions/fe663c76-8897-4a29-8c31-746010240ca3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 543165467 ≤ n < 543345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 543166717 1250 543165467 543165517
    0x11100f06150810140d2001140c030a0305091c0e041404020f010305040c0e04080405041d07031103030c1002120606030708040303051503030d0c030605190b030903 71
    0x1603011100858500005040481c000303940b507040c11500c54006407030704003080202144020545082d1940602081c0300680c9644800d007110784140c0004180750203108009081c1d5a002a901c07a01688044440303080c5502586002d4aa10070350555200b015103039404200f0054040c00040c501013690308480c8085101c900020780720340113588651707108500d80115606024000340c1528403440c3d006001a808151100041d0002d100250095481c02040c0300c1c081000000d500c0f40d14001c60040300c0c0180c03640e10700380c100411b440340703210580e004802d002c070044401600011002d096981c481e541c504003441d102d02091442c0186411450305100d00081088965513a9008054441401c1d420502e40c1e95400c1c01d211261100b0b442030400600343c0c00001c2c000c40c0c8030b64803058214007184044402030300c1c80400a49175411a120724980c2c81c2d56444000c1c001341e014460310004080540703c207504103420210911302d2505910400c0c5841a0001c00034a03040741c140121036125405174200c81000310104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 543167967 1250 543166717 543166721
    0xc053703170c151003530405060415170403020f010f0b1c0303020d020f091801080a0312021209010203150316032604080f12090d021908060924040f0311100f 69
    0x3c2c0090303260542080180c106c000b0031004a0701aa000540042c1c40d00f840c162003071030920068070f1f108e0304000300c804d0884c003208005070302d2038042c034001c0d80242042030a01c0c0510b401c40300000d416581071843e0071704401c034a8682011003a6000c4e450061440240580c0c10268013034491215517030042840000e84251046c01c13007000d8040d100050724903d0700362203a43d00040e140d9400380603160a55000b07029520003c0e2080182001d83c8814180140c14641d800400c1c07040468180c45000080c0d4010040007030070001092031003440801100208280c2c200381540903004901804040c001c403200000c03020042013402002100c4060300602c1c1a9180c0da5580d031103898031844291000780740107a2080040540301c9005641c14090001c04400c00c0c54429030800014240100c0001011001d44070002043d1900b400700d20710030034046000e081c80703c020031f41030b902c81d040700050361010380901d4042c4030100c1d0264100007040399040c2803004514114600003071500f10307201000b00d043c5040c5006d10308464055 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 543169217 1250 543167967 543168083
    0x20c030d090f1505032d0a02040314150105041a0d080a120c1d01030e0105070e0a08190201030c1404060c0c053703170c151003 56
    0x30700804001c10b41c54083c00b0b050240c603030041c50000380040c0007051003051000c0e8956244481e0072004030084503188040c1d00d0320300044810146699000c141003040c4400ca038224440100c101c809440221410785080400e06c0f410302800340555a150400e01c0d0260300c58000708880302d40205940c8602c07000385016a013991244100400180c4181007101c1410900e0207010b00344001e0303440349640700340c0c1041c070358004103060000e00307041684071140c009030b04000713210b240d0080005a03503003061207844e00e007481050354460f800840958040e8440e103580c0d1010042a070360141c0e0910300403801c071480c0300c0c04803586403c01d805001050000a40001c046070803070a600b001d14414aa2807009076960001c00c00040758149400d031901d200e008402c1c0341201d030b040038198083c10101c02c4000c407a440e521741240303030f40ba60a05002210030004000ca00c0c80c00800c48400c001d50981042201752038416809401d50300248001821030038181615108030100e103000c4448a50701206030004100305005640c0c1142070 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 543170467 1250 543169217 543169229
    0x708062202130b0d05031308151302090703090b2e050d06020702030102070c0e06010915050d0f0f06060509040608030405011b0302010204051f090501081b09120a0b07090e01050a0504090201020c030d09 88
    0x503001d039440700c0d650541d276014400d8080891241610f44e1307540034840109002404901003580e201084000600d036000032600401034099103501211040c00c03004035041d8045c0d0103003a0440c40035010810b580d115a03440d2042c0e0351058015031201005d1020902900669a0090901c0005117004c1941207202c444c4030300c102026a500b08070555540030851041c2c070b10640c2c00000920801008401020a03000445400c0c1e0740c0d8400101803080140d01003c4580d640c02c07640015500048181c1c051606c0d0080e900070b0314600d0055031406150030000390440e80c1c40a407003100c2004401c480024107000b0760646004140103400e080d2000782da9030f01041c501001390041300202d4035940002c2400e5121300c501611514000040e0f02c0407c042c0a540811908050322065014240303801c440c000039000e10424018920415914096013040c14002d080550305405c00109455610010072007a035401881604503401910f00040a464500040b400c1500355484142c0620403141e02c8401c90b40d100d003c2d6411184 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 543171717 1250 543170467 543170473
    0x905010209060a21090b01060e19060e040e1b1e0d0c031a1b0c1603050303190506060904051f0810110304020307061b050708062202130b0d05031308 65
    0x902d4001070b008032176504002900d010104001440b000e80140032414807518024001d4110821846a08800e020306400950010791480440001d6040c580106200f110107640503068800c002084000301c540c00a400703038403d942d440041c25880540c50250408181c01030880748000307180d8200445070741140c3c4411111448096400d9903c003000d40d00e8240503040c80c03e10141510003071040800c1d107030850380c0780310b100c3d00a1540000001004054034002184250043c0d41c82c1d2400745c98000e9030540f10440703a001c950030003003003001e0303941c50310219040c680040700e0010b481e49868004d0a00b6401d401229091129400ba010450b0800081c11100303003a99030200b4401c80c00401c521402a00043e00c0094166000800c00d01001340960085100c040405040d288285082c0c0c131303198a85042d560204203550003e00c203001d64802c0350072800c0075011402d420f0b21503d40081c0e000c2603441e0300d49086003091580c0d036143e64172290760f040c1035140960303041021603440303850701001e002494040f4403a91910788 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 543172967 1250 543171717 543171767
    0x3040614071208091912020d02070806010b1c0914010c03060f0b03060301090b04060c020610150810091a031e0d0e0301290f01110c01030905010209060a 67
    0x440c4504440a280c1d00a402e4001e40520b032006882e22200034064041e5402042141c5074001c4a03400c2c1d40500394082c45c40d101e103242c0c0c1c00301c0203810642441e4800c07086400c0082e05206281001840904407601070081e1030381c03560803c0304100801800c2c20700d105014105200b28050180e40c0c0001d80c50500d02c040200f09013410003406400f103d00368856540303280c004101c100101c00c00400070319805030f409800884c0d019116510701c201103104940c21116296542e00703c1c40d07182e0341000002e6000344c00210301042c0c541000e0149140070030b081b401034204218280090400088010780d040185051002841050403c900707560900c0c1c0c1101186000b07104190000007600e80807030408011400c00c0010341810a00ea000031111200ca80c0740c0d8075010341d200d1401204c4840d6907d0030391002c144541e08002000700040c1000494110380c04034a040003003894602007240750114141d480d54a003400c0c0080e902005141c184d002e4000c81203c594010b01c040784030b001151b00101c1c004030104100001740c03104 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 543174217 1250 543172967 543172997
    0x30a0546031a010e0301020c060c0c010c03020f070f020415060917030a0906050307180909060507020105090303160c05010203070302040e011e0302040903110109060f0c230915040602030406 83
    0x110b00c0000d00c034904041da0400450554010907041e405124094000f51401c4400c3c1c01441c50701e002030340c201281450020f0010540e003401c0c41a00700b1007603545010b51400307c1c3d106c5408130078050300d080900050355110b810811591240d1109008900d141c00c003030083c40c1d450038050040c07907591084280702913410039004206a000b004451504440d0b03243c841144e41842d03c00c880581008140c00c0030321100940b505622084103004200820354000c011035618030034a000016100041c240c0e80c11f580c100014010311400c0070056942c4100420120200700301640c608035003401c40d41d14090110351000090021083e4503030010820b03a00c0411058075141d0741c4280009134401440c507105195840941c05100601d450b81100c0c2c1901e00030314040111030410344401c2c4c21509034402c22a03c955460b440c22440c000140105282c1694a00703010302130424461024482c4244030651800300710740061030303c955503603403420740d0030351042000b165444d981c440c1d001030f50320351180c043c402c086031500e1002030302 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 543175467 1250 543174217 543174221
    0xe0a1401080307030c05190c0504060b070c03021017131e03021f0b060a020f0c0d11091e01031a16020d0e040216061d01060602030a054603 61
    0x4990441c0000c52070014540c4040f50302240c030107404c0f074841c0120403842c100c004901c1080c0c90300714000d13500340c4e100301d18100c02c00c0101c3d4015402440c04000501070800814040d03095941207980544d2440c030b1030850312000f141d5242e00516082e122504840038441024000e004c0140c035070344215051000454680a440c0b040702250314004c00590200362001514100c818400100100301c840c0450b00c02c00045c0000d4154115000b103030010b92010030140c0e4010410442850840380503515129440c101d601c0b88903900300d10390203071806050300d140416001c922b8040c80140420f000028020103585924111540c0d410010000d28042c201038041402003408030301d10840c00c0b40b13030740082251101180094400d40c111201041e030065003403151402040800440200300c0e407040d00e00040d590062101414010a4542078a079560701d80203050100c46d0300001103804107041403c0003504d408070340c3c50010050b1a0b640e000481c2017000754198140c424901515403a0a0745404202080320712007170100c007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 543176717 1250 543175467 543175469
    0x14010b0604051309110901080f070b0a0516110604030c030c1a07060b0d020a2d3f030309060506180105060c0a081303020a090908070b06030114010e0a1401 68
    0x1a000009208001c00c0003a0f0b80d00c01d80d01c0c03902c250800c2c0413600700e541c0024800c1d0802d82c8000c6c07154100804658401605200c0300e0064101806010f00304014682d00074880d000d03100707920240c0301e801340141c401e1182440800d4981c00e0028030440e07407551079281000c01120329200484000000010101e0042441d000c3d000031980101071031818403105468010145c1000c0940340e400100d6a4034510258464420071006050040c20080d2032031548080188101d1660119498202541c002841518850324100c012400d152100d030420001041c401d8600000001501c5d40028810781c0c132204140d0990001846c0a002e000200420b035640c10900c103017140c01810003403070140280c006200030310300032000d810b6a00e128012a201c0c1240307555000c220364003c0c00c5041000500090410861610400b000050881048184500306880d6110700c0b1601500c1d4000b030400369888000760b07080c4c81c2544408105000c60a41c001c20b56035030301e102e44c480c80f810f0750020001820400c4a0be50000030780c503098 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 543177967 1250 543176717 543176719
    0x2071e0c032d02041d0f06010f0e0f011412010f09030806040203060a0306020c2a03160602060106030c0e030a030801030303060b0a09031b0806010b04090507141803010609060314010b060405 83
    0x711030000b00b40e0030800202404004818a0610640194060742080004214441d040001000c155040c2076284540e2001c036803081c451210708104003c10317130503840c01490440301c0c4000d0b02e0303071400c8140d000034514494250325003400d0342c0f03811000c810a20a40d00044001402901d50000ca80c8802007444140e01c401c56095800c0946800700300009400c0340e00030440d080c5202c0507240018400007a60581e40745168810311869500807440785989000d10407410b038500852410f003500c601d0003030041c1d101e5005228440a00d5986d22802c00c400f0f000369000c0c5403600c8010180ca18108551502a1941c0d4080c0030035400a490441c0c0420001484422138803c9015a11a0b19400b4503640e594820240003d2111030385005120b40000d040104018890207054420303040c9440e0fa04020300701003190b1008044004000e05003890001c442d001c20101d4000c2c6480c003640c12481d400d0b0101007405000f02d41d07c035507120f0740382603800001e000c0004101d002c1c003032034403000380148d1b0040410841103014038042c0c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 543179217 1250 543177967 543178043
    0x906090602150901230402090a1e1503020a1518050f0910080604030c031413030f03030603080a2303010803041e0504020a0507030221030a02071e0c03 66
    0x20704a0400740074240ba41c86410f0701e0000c242e114000020502c804030310b4150030804108030003030108610b80141c103944e009100e17410400105070040f028110ad510310f85c14071007203540d44444001c50001221500030265401801c4052400d0360b8540e50f6003150803003514000000c007148107402254090b441078204031036004205900128800b010000f00c4034000e00301a190030b8910350b0001c0d004800344030480c869030298440380060a17450a0140541143d81d00d0f242da01d95040110342d00b06007440112801742c0b500300c1c0e0110007000300e82c82e00341c0c000c003540d0700050031961021a03819440343e4840b01c04840300c41074051404000c0944030f00d180c0c10780020702a1103010703001844107010b90388402515080032136001441d14440da0781c0702c0124040741d000046c1c49002540004d145030515404008402c4100c00d802000916022034501000f00da00002d0100444560009490070a024068803414410703241144001030030b01542c0b03070103506219288012210541c44d00008400c0c40d07c0d6400b1000c3e4070a0300e1a0b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 543180467 1250 543179217 543179233
    0x1050109170c030d0f091409040803091005090120040b090411070804060305010f0518040209092d0609030316230d1a04060b091207240906090602 64
    0x25040a01c00010196126841000e441c0b1403036940800915411400680b01d0306103100d40800000e20b02440e503008002e03a4002402200d40c640c88005205078059080050191207440c0c00701a40e003400b640c94040001503007010140044441c06503c80b18111486040d0403e13980c101c000c0f004900e010394451445060307c01c0c482080b0508194002c0b0b4911000002c1c07240c907040c0c1a542c1d0a1781c0b90082d410000c0029a07a03001400940c41c913640c01c0000d0a0b0451384000441c414090b064904580284024001c1d43c0d4000171403a0340e1001c01c41096801119200b00b20880042d61400403c2c000e250a900b805200760340100d0507001c404804c42c1c2c0101c40748421070041480c5600141c5010911036000002d60b5a40b20b03039010900600009043d00c03166040020592694407921408000f080b00b800c0da2003541b03803d00800004002201301d0f0407030348040d02c03ca01c005003103082403070904c48903902544c410000fa2400f01181c8100d00b0420944403101c1e200d0148150b19480c0440c0c03020072501038100580c0c00104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 543181717 1250 543180467 543180479
    0xc0308060f0114030c09010305010b0906030a0c3005060d030c170d020a020a051203090a0201030f0e07031514071215051908010614010e130605030114040308060901050109 75
    0x5150040107040c10702a140382e20030600e512855204035402c454402011031400c550390380c180105401003141000c20380c00d0410720800100c0903c00034146030250b5541c0c0106c0c0780c4803030080080b2035039640c0756100301c030005030304000b40c60040780c0c0f030149004290728000009015150114610070403a805560f405104c4416540321040b004944030080101740040c040286292035a00040040f0b200726400391022a440b841c00500d0420024609080e60000b48100200090009400340340c55809180219006800841c404018404d8140c0c042c414020060302205000e403070388940c0b006408400d010840d40c00e40c03a003400a03c0d502981e03030740c000810050200618002a41090315441c44055103040c40541c4e410000c1d00d940d80101c0b20760203245800ca81008424801e100342c8000709800e4031801d012400c0840000e000507003440f245031003050000613551252145174030074005048060002c110100142454100c2030303608032030840026418400064180c10100c400034120f640684a0107510340c1859 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 543182967 1250 543181717 543181729
    0x180b0a08031e0d0f061d0c0901030f060905040812130206090d02010e1e1201050606030720030315090a0b03150a0e0304170c10052b150f060c030806 65
    0x2d40307006400c002c240181c00111140d0310441040030041d11002481074908250b42e07000c800c41c0300c01181d1243e80e5404210307150000d00101ca0079040c0902c2c0006081000d100494001c201d150402c4000520701010402000301c1c480c0140300100c25858103610701c1d51040100300d003000c000c41c2c0007034100606004400c5281000419001a2031050400d918085003180c003240c189800800204d0b6848581d2402940b40c0c00c0a04181e445c4088150003030103a40340243c00b040d01c61001414240802c44240c070344d01d5480782c0345081c0e5920103000c0000d81e6034038240300300c0800c1281c0c44650741300e2003002d07400040f5452050714030030f0300302105019000e02038072040c030360058007251801804030070081e0315280d001070344a20a00040016004c0411200d02205120104030303e8002215003290040590040703a41c0b03199009010f8030851003000c0c1e07411066070204c10403041d0b006400c0c6c81001e201d60400e8201d8105900200080c0d040d01c01c1100c482c1442075950f0b2045805801c030345030140200d4031307200100e21700f42040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 543184217 1250 543182967 543183007
    0x15031b0f2306070f050a0f0b0a0905071a0c030309070303030b060702010f08091603060f0609151a0f0a051803012f1911010c082e03060204180b0a0803 66
    0xd6100b80803c40551320b4403410502040760803030360101280550010000e1642301140c1025001390b0410420800d6a5202d5446005020301214078000f44014040544100100c450406200060300e0301c074140100442e83e541c11a010442c0480e0070301002c00e40e030b420705800740d80440303030142d455801440c00290207442201c40605a4461402040c40c46c00400c0710802c41440194802c2800141c425408070454040390400d410004090341031505400610349001e10660903200c0b4000c0601c040d20044c840d240292240580d10082074401207640c080f80c0c0c1e001400703000d145034082404c40b031120100040600f00ea280441d4200d5603264814500c58007403006814100d58030402c504c03030345030481c42e40d007503260341d03500c2a021030000d01d0300c080c020f03801c10082c0920244d0118609040105040c081520220722100700d2400c10307034810700a840c00303499000d034000000450300060304642d1180c0302c401c80c11a1001104204880506200c2480e44500300258500f007100e0500c0091800c10500d00810304400083c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 543185467 1250 543184217 543184223
    0x180102030c30090d030b0d11120705312a05090a090912050a120902031e03190509030c101218021206061315031b0f230607 54
    0x101c1d1541516100b00081c955000d421400001c04d122981004000c0c01e60f82140c1800b0301500310000100c00240039414042044042259000908041b06050317518003d0750f0b80c4200d91000f20b80c0d0301c0103080d0361014000100941946e03035009400080c0c04031203040ea000f00180d01412140b24020900d0403075968507440c3c0d414041d1610324034140c910310000744405419000361107419540d07030341403040204075001c4044610741401c0c03082c2084185400502003042030b540103ca42c68654100700c0440d64140028249624550031560345030121040c010359a03041642d80c20742404a4002c0040e0756402101a603525120040007006c1040c040e1090140700041d00483e001032151103103844969540c14003c8802081c042048e402800d0000d00410086401c0c2c8101c800858001806024941d02d840f04103200860380408082010344584109030442e0310143e00162440309291a144c0c0c603146043c1100045071100400010000d07281c120500380298011181280c10032208004490381c241000a0429180 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 543186717 1250 543185467 543185527
    0x5030f190f1104060320030109321602070e010b0a0e130b030c0d021819140f0705030105090f0a0605150915090f0d060b030102070b180102030c 63
    0x1050140d001610782c0076a10001040700814148540c9901d8440d4658a54840d08581005403d810000300c06200600411680648442c0c1100900d0300040480311a208440104c40e0703010359030a0303040941481a50b8040030079042c00d001030601303403000610405079549200d640b8031a074070f890707100e44050b40042d18030014403030424000c280c02d94a010700c883c00005842e001144c54040c6d02c08050401e200000c0492158001d00200c03000350301d030400212aa40c0408030032681a031600b12410f08090340c45591280c610303081c003220b068800781c0c040040e401080011120745407501d4225065270726010901505410018410000d060000c2a0f00c040b074005005110025165860744c0100c0e02440a0942c6075003144400a240d08860034080d1184101c064501c078a541051114000600800d100708121440f60098800c0b05091080031350015403500340c0240210b5a91901c2e03d009080c07100e040384e07010212420714020716216007040c021a841030030b08080c00c62801e00340070802002e40c901d00508a805007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 543187967 1250 543186717 543186731
    0x5101205151207030b011505091e0915040e060c0702060a110706030e06061012020d0212180708011a09090c0d03020f010e030711040203070507060c0e1005030f19 71
    0x38a6a21250725640c5450b8040e040301030071401d0007035071703800c3c180e0003802901d111102483c03110b81d0000c10b80e880e0307001c00c030340704800010300350f074651100c001e200400c95020554500b400290080001c5440700b07541c044e141802130001100c03505031181d808503082d0350350f184100000720040c6001c40c0140000c00385800c1900080722100c118a1800029400030030100782e0703404d45a080302c44200032481d8024070891b40c10b2411460064018142000e10032113080c19600401d81660800311a01618914800c0240b034002510f00300b0140c056091b8400c0b08494a80250302002c01d5607035040c011010b45c1e4010b41a40180c041d00d41d801c1c41109c0000401d15643d9004ea00a11b18140e55500c500c400c0d0b260195006016200f921074440382128410580c20280d544100030300c4000442408941d000003108460040e22942c49280a075154821544010030084c5030142c3d5111441c0c112060301800305040e180f202498460708020382d150f12040d078110501c80c2c3c0c601e001505100c644c2001c50b0741804207000100303003c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 543189217 1250 543187967 543187969
    0xc041e09090605040c05030d0f0503150306100302400b0301020c07140105040e190213080114010609180b2d1c0b0c030c040b04080109020405010510120515 68
    0x101d0403208100e40311501e800511050080604520010705021000703058869510107018007407409002620091000200000d4815401e65850343c40001011341603c6c2c0518100344501c0500c61180002c03841407010300c0424042c501030f08a682c003581011400340c550f44c0a02406c150031600c18440540f00c0c941c850303000402c50788007800a44104030180000b000584d0909100710015111440300130304001061004101246842c4801a000035504082914038540c44030220007911401034154081680ca45002400e21015800344405070681031080d240ba980381d1000711070089036032145003900c0c90080c00d03da4502d4000d0f40200d003944002440040c0e101528501c42284449007484200318000e64840c03010039091414840e02001c004d0039880b200342040d9601c417100418090203e883d00c10000c000180c0c00c07000d41c5c04440c00361041000c4a912641d46441a80c00f800309040101c0c025800c00c0700015807030078500745e14089000c00791950072120340c010760000020b04004026106070005000c14100c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 543190467 1250 543189217 543189221
    0x8070c051005031801050603100b04060e04050307032c0616171305150417030d0f0605040c0f0f05070204090c031406071b080703230d140c041e09 64
    0x841e1562a80d603102e250040201da040e00766451040400e906000810100d55070101d420020141180d00008a00d1010000300e00184102e4101000c2e1480e01e0082c0000c0c030100001801071107100e07903981d00501c00d420000344407500000c15801060400350365900007d00c3d100c070246c51240940c1c0081501e2018607121552096809191444403003000242105900c0061034200064802901c0f110b0303001c5d50b000d0200403d4840c0d4800c4d44000321270300c0e56100d4410f4007881143c01100e08a80140000070112100d6001410381d481031911a40c034000e8221b2415000c0c2140c409040c1c40350b22865804141c01e0340c251407550040700226882540c0312a98400200030319401405180501d00307003e00480100900b138507105e0090300a205002d411040b050107404203842c00e21354942e0104265031142070500e02034480704a5400a49407450090b4420f01c2480304004c058a09030400b803038148a600400c4081c0600050180d034007440b401020071003070194194050858036200c100c08401c50216555036441d0007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 543191717 1250 543190467 543190489
    0x10f0e030a0c090b331c0507030c020a020907050a0c0f06060306060e010f0b3609010b04031a0601020a12020a020f09061f0519080412090f0308070c05 66
    0x250881c0b21001441500820310500340d840905030f41c143c400d00000ba1503600d0b01850500084113540f800200c2a100c816900300303554850888200c04c403044400c502910015203400c45856001030300d4100c803155411300c000307034603686280c001c0c182038210b0701d13040411983c43e403003807501c501030004c07410000001075001500043c0c1580900340c0011045d041d4604035040d070f1344030750010300c1c1c01100d0301c011301c1849441c50301d540841d031104640742d50302c1000703000304420700c125480c82d20f0034520a4000c0b00800505418080001401260104ca2917070301c4049070301440c050340c00003070035015007007903110302c81ea8581c40501d4001c007050045a402440301d5444282c1481c1c281d8480d00182c1118604001b1420b001580b10950f400840c2c0001e051301c0d011010038410034030080b90165001661401ca0003072401601142c10032009550400803015020b2005480b4820585044508040f425900d058080c400e45885003600d80c52140c200d050303865a1100380c075a0304040810781c0e191008200c0000c0e184d03200c1d11074603 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 543192967 1250 543191717 543191723
    0xb030d02060412022404020f040212070905040213060c0f0c06050d1506050a0507170d0605280b1c021306030c08010819050c06030a02030f180c010f0e030a 68
    0x3146018a0801482d0311444a003070195840507501d20703038481d402c5c040014001020b0001030b04030350b21400000e1000c40d0f040b192580085c8002000700101d40c8a058080c807130813154079400c9995a5480503c0200d00c181044010a5010a002404894171818040c0000c50003002d002001d1401c50b154508014010342c005004180d0001d081c480c458110701a08044204403031800d00a94588500900a0300c10006a10100480040e8002c2003140018844d40c1032580000000d881c1c05010b402c1600914244c05090320414000804840040d03c04194903076110341240c54100b0f4501e0150310171017a400c40703030300410714410382a20000848900c0c80039041d022860a005000b5074504030b8042d080392030b410702c0802042641e4005008181c000140300d038107400e5102c1200c00c9041c490802508200001d5078590b030014001090110748000c81c3c000d9809600340d1501400d03682c50700c00f1074180c0b2141100400e1450741081c0f0840f1015805104581000105424107040c100701c900c0020b8148440f1410807 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 543194217 1250 543192967 543192973
    0x70c0b0a0305011d011208280e150c0705040203042118060507121b0803010308030f100f0603020901050c0f0f010f0216020f0117010311090f0c09130b030d02 69
    0x100242d13079041c2140c030104000f03501c000c03840b0750406005548124403601d000e0403050001031010820341d242c40341d1810781c1e45043e410000800d00072500030304405003042407511803c441e48134620801002002c8868801904005200d00792034401400040e400003801941c0108000000400d414030035000303140040c0d01030381e44c05503507000f407281d01d000100a030304200100041480485c00084018414498980140c14003000103403400e184011a4078401400401d000000f00c00081008032142c0a507000d500001c054223000d95641c130380000010010310620300d0200080e4020030500380a540204911030042c90024584410008003610b401c00e18298810705a005101c001040070f800e01c100b9801900c80076084d07251030405000888600c840c0000130b403085828601107044bc1c0c0c001c5068840200020311454000c0d84d481c1801c8500012170b009032801040c20500280031f0782c0c15008130f90311986025801d5401d1200c04070501441000800c841b503602c0303a0700c401c034003826030b07041040301842c03107a560007 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 543195467 1250 543194217 543194219
    0x603080f1306030504110d050c0d08041403210d02040506040314010c021b01120e1603060c140406080603010e120c0f0a0b1b1303150e15060402070c0b0a030501 70
    0x844540c1d08541e48014100b6107440b0500000680250074883c4c1c0e20f200312001e440c815010f007007440c1056605201541d0008000c0c034041d04005080005d00200d0341e40300052070040d0527440a045d1603e4003640c2c000c0780c2090540c0440c40340c107200b9014140d800101040141003c2d202c2d80840d503294070a400944080c1d840112643d140c9000340168200303060b0390720291540c1502c4e003c05140802c9031080e51070501c503214482c0f5200484560007000c1d080d0281c4200d44c00b80c22240181d00050981e40401e0310403a0400f241d40340820b000d40d0f80124000d0320004214a820303d04002101d200401a00040d4035548504001440389402c22490100c2410031400641d20021508010b2911400030a01d0703002e40c1003030b0001030102d4101c801c01580014501d40540e030071000070b444003003d031041d074000380c600481809010042c44492103141e804902c030103004001020500f8180c41d950074541c2090507131440c402c2c000030a1400c140c1c01a011940c440c008586c80a070f161001c04809401c58088440000d0f80e40d00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 543196717 1250 543195467 543195487
    0x50705100b1e1c0f0f120909090c051005130e01260606120f0109050d17150111240a1803270302090f090f070503100509010603080f 58
    0xd4034103200341590380c80041c810440740115a9400c600fa025015002c0d0b075045075001e108400108100c4140d0152812420140901d00f249980f001d40c0081c030300107000c2c8100400d10f940f140c882c0a140640040c251480306140104020000784409415001c0150500c030361007204401000c5d002c0078090a404401c6158100101d141e84409400c080c1e10814000803160041d406000c01c005400c14410703542081e02d001c4800d0101e282c1038001110203000d618100c81e0000303025000c10000090b03e4a80c0d00d4554407014031000d070b00c140c501a0341442001d029040c58519a6000c0c0200940400b450f000b1b0f0b03407103480b1186104030080c800f40c005160041c8071604103d0080c0240c4a000801d43c0018080c2c8806c0d005514001c1034003c0f6100c0140310210600307a0071105010340d4100c0801550300401c01e030441d1804201ca99562042550701481520401c500358502240101c1e4000c252540540207000d900c84002045000c0d10307018041851555a031400480855040c4008020321003413500200c2d0747d500001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 543197967 1250 543196717 543196729
    0x110c2b030f0216051804060204030c03080c011503120809100c050c0d0906021510210507080106080d1808030f0a020d0804030c06050402041e090c1403030406050307050705100b 77
    0x49041c0c0b90300300d1083c1082c070041c1e03240c401c008503050100708410f1540e600c40c6030038402407080c2e40001d04604213065002081008420040c00b000e15034100a004600364607043c0c4140048030300000b44901a42e2020715010b91107400d110382d0040144084415410310025414219414030310400c5c0050f00000e18401901c208101c0315094171118500818a1441c180300251221a21855106032008032000710702608456040c08000c0c14180c62260282409141c644290440401c07080300c103409030040004541d101807040c48121008407014225104140130129480640081b1040d05c100741c2140218880e0b404001a050701500c0074240d07a44c0d8405044081d00d0400c06c5d011450070050080c04000010b83d1221005c52012f0388240702290315147d5100040c09000b24029840110034240c4035504c031154290861020750b4025504101040d03181c0501401d81e4900310100f03134040d84100010491903110340015580104146041400d003035560f9506410301200850181d01d0a40301c00e00071a00385011 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 543199217 1250 543197967 543197983
    0x2010606020c1020010b0316030b0f061003020a03090c03030f1d0d030c0807020d0c151b020108071403070909060b0313020f0301061d090d110c2b030f02 67
    0x220381045183c154507030b00800c00020b803040c0501c0748900c01c03100645080c0941010b107083c0401000c0e0703000000703100c41071280204184016540d842d032590101c1c0015101805650080030060f0098151024030b03c400e40103540442c400d5010103648020f9000404c8548401c080a940f0a0b540d410f8101d2040704010009801c2c1c10381405005401200e072007141d60f4803500805d895030f040c00c01d084210500d041c11159802456000b0b500203003098081401c0000721050101960141c800d100015249030030100d808242200f06224140001010400035601038402654010124900b90a4a089070005015645c00544001c070110b0710511050002d0a40c50180502038502100f1660079071038141400300b05401c041c01c02038000c404911102a0949080d003002016208001003244000440d908241071440b04032115581409044900d21041d803088511101e01d0b22918010107074081510100b0600309000f81e008004100450304407800c5a40030b803a4507025500a45681e01c0091104402034245021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 543200467 1250 543199217 543199219
    0x90905010e0616090501140c06070206010609120f0b040203010b030f0109020a1a090918120706180206220e07080a1d0a11041d0a030f09050603040201030207030e06030702010606020c 80
    0x8070604143d0b40c2940300d01020200d52003480d05010380e440242c0354007410300c00c500c0005200d008000c00c00ca540c40d000540d8904852480e52911000c03a511103804588811802c401084440788440e5903020071030384c607492170b00180000c1c00040d040c900314000a00d80300741c1542d6074035141d46411111080d881c3c8a400d03a001000711100341d42030a03504000b0b009140c4074407250782d845100038401117401d070003a207030380a18511076840868044a0a0aa40005503045914200c1e42c06062420808814a5040600358041d80c00b90019040a190701c1c0c4101c1c420900110700080d80b46e10781000a2601703c030018460081d806616103003100d05103400d0703250075121007040d541c07a44400d00c40386e02c0402d00d0004100100c0c4d40c100100c00c0c01c0076040000100a899543e8a00e81645a400c08044d0307a464085407160742180700381c9540340032000b820000d0b10340719290301c00d59500480900014000d54003e030000c055081c8289804031011001c400041c0c40e940054a054005039503440702803010540400a50f0f010700c0e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 543201717 1250 543200467 543200491
    0x270b0901030b0414160b07020a1a030c0c16030c181407110c030d030501180b031002030a090c261504020f0a0924090b090a0b0a090905010e06 62
    0xc10754030380924060000d80018000d50609010614443c0e090104c100f200751101905280180d80c0c198800c210340043d4816445080410b0000900090740d82c020300d00704038007c0169045940d080d03144211904504030700d41060142c110081b0004a01c43d40100c00340d4070a40e0b044006501b0140301d0b5141e991164006020340b8a019081d00144688000741a4040c8241c80c1c03618120141500325403c240e0584410f40c5c041c4158016004201d030150403640c180c1d180716826000a00001074141c1c1a981295402d42e01500070110340580c646440d0015580042003170fa022a00c6107203995107018004945d132154580b0036003401d0048010142543d1640e0400d640e00040c0101c0b40c0c4607090300b00d503002c0540000d205103404e8080a00544505440354020107616400b00003003035411010040000100c4034010b5031045500340896a11241d108031780b2400c02c081c0203224680e941c041d200c03005000c00c12040364044411600040c0c030b82c1d8a80540c040c1188100300210f80402441041172030b1803809010148480 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 543202967 1250 543201717 543201719
    0xc06030e0703080c070906121406010303050d0c03060e04060e060601090b09060304030212031f0e13060b1507061a01031e050a180b100501030c12090c270b0901 70
    0x140041d50406494100c01c083c1e80d00e1341c0c000300c01464102c0c1d41d40702d03503011414020005138001318401556100380c00784030080c40b40c800300700c1400c1e02c410742400003d0203d00140111403d041d881e52010700054144d003000140340e900c0b0300c44043d6481085500300e174001d880340ca03441582c7c0414860940c00030780038200500c419040003204421030154913002409050040001414140b08100044c8660744103681c41d0780d42c2c03c0c0103030340039155652561022010050102c00054541080240394030643d459201301051981c0c2da95035002419400003503aa118510b509014504580c040c02006401d204640004504400c20040300c0042404070407541458641001e1825056582140040c4003607240d2001469999040c41c120050170200b510002080240600a04010500e42018000c02410741c5000e9034503a90801181991030340d0942d840010704c02c031440c060358030441c0c1100c102103104114003000789407a800e164840000310294107115031040440d00c90340310341902c41e0221460069604030095 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 543204217 1250 543202967 543202991
    0xa050717030a1202220f061d0405090a05120d0e0706020c010c05120f03071d0f04110708030903040f0609050114160c0e06030f0a0b041101020f01060906030c0603 71
    0x1d0242d00350075400d00004012480c05140250304503010009648200c46580f04042c00c141c0e441c07000350040a0041107144800303d84580243c0c41000c52880d411502c1c03d10259410600c40079010140c074050031489014131030400513805006510210300303007006840d1103641c000703104c2c1d06681480f0200456900060360920240b980803e10b00b940540c03c0c01c1c56400d0ba0041d15000e072030302800c400c104d5007503180810b448000980720340c000d50050b5540d40e614801c8507903400001c4803002030400020ba2144241d0088800b50601c0d804c03076020380030b5007140c1380c1c184081c3c0d848170307801540200e4200305c59400009d410700003290380c801c5500192a0910303040f6049410701c40064a500580c8001021501001c103643c0444505682803c221551001c10320200756030720b013407404074000140c446074401c0c0900d1009017000500010401c80280c3c00c08440f41c01911a62118070582200c185200c0c110b020344000640013100c01d0045000a2007660000140c00e86141481103400c1855003101c8205820030202483c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 543205467 1250 543204217 543204223
    0x12090c230a050a0b0319060308040504060e06130e1f0b012304180204120506011a12010e090a0506041a0612030901030e011d1e1f0203060103060e090a050717 69
    0x95401040c131890380c0342c550f159070321034100b103040340c3d50050703400d2440c040208003084019000715001034805000d11030b11040c031103c0301c0c0021105d103070b00aa80c0c031a204a00c800325801103140040c0540980d4440300d402c03026039503080b15a255507040170361201c54030341c00c0f56480701c0d48201d24415440b00031444880d292440c02c2a1143e4865a030349540d02560909c01c403d4107504036401410301c0405001c0075000b518005031520002d20034604d515000e80c6c4200802c043c980200c0701d0507101c010100200d61b00300b4500c4250300310041c0141c403042c400c0c80d448400040b400c202083c082c034099030715042840d2140c40c2d4140910401081035010384070030000a4003401000040c0c0b1000030342406c020608455002000703005014658018604150418540507007003004240342480740c101002d80b071141080c620103650380701e0f0030428210311038104a084ad03000400640c059a00080d0503d008100d0300e984600090080600307603850041500301c09244010000e00b0009000244400b42c44400e400b0841303a2001c3d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 543206717 1250 543205467 543205469
    0x30206070303050a1e09060c0809030d0e1002030c1902010b060414010c02060d060602120408251203120506030f060114010c080a08061003090f0312090c230a050a 71
    0x2c0c15100e00c0812119001070700f02c5840c281038004d102e56801d540b04c081201800e0741c1c040a40700c041c40c10603601e6802d0720a890b6244140704400041d0f240101c5440020020080d40003040704038002d950504540e494580021400ba2031100500d030340719010170760b015006114209031039066a1410300080e005071038079000d40301101c010f10341300312502e01c1000060300d01d042c007140001e41c403650014008040040701e6100c03600f0b07101b5684c00c5030000c60601d40c01003094840c80c00b40c01242e03805080c80070310700c9001c0c1d410305128601e0b00c2000c00c00965641e500c04030340411124100d0209034a240208800c9102c0d104907540844102c00501e11410305c640340c7c0e0b4403088180240c5000300200c3c0040c0406074002d0603e452055446041d0380e0766141c0288004200f500140e41a510503424007600c840c4e221700c24000c1d4000c842d0486007042020f0b05981d01907903101c00b2090041c20441c3c03142e41480114140c8200d640003804004481207041d41c5050540c900d0440144034944250500b4409001c02d85607240c0d144 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 543207967 1250 543206717 543206723
    0x130b100c0b18030c06070233041211030406120c081515070b010906060801060c0302030906030a06050409060c08090102040602031e1e13090209012c0d030806030c03060103020607 78
    0x5030601442c00c010706610902d01111040c0c8a4041444021a40042d00e6500101e1294001c05181c030408840ca6501c041500c1d05580c0e108803070080750100720b40a50000c59011b80742068000400840c40c01400c680181d030011021a040c01c190120103412802a40c0001500c0d2800b8446440d04900708951081c451030814021208490b8002d10303c0d04900c21a45c4030754002340000c081d036a4880c0110060141401161b000554550001810502071480e11040a9241d000b0354100030035601808600d070070090080b80c4054030f409000840d0303201d521404840c3d034011540490400e03078200020b0040c000103012007007c0c2c1c2c81000100101540403040d00da000c0701e22100d80f0b0942148130104210b03409090b2030030101c8a0307107494203040c0040d020024a00752481041d01142c00c2d641c0d0381107804a00811010381d0100716850160051035282b0640091918a0340e02c900e410039142802003155a2a0300c50100c1c0415a0302c400e0084a1404000c1d10741441400c400429440d030550740820b41500501d9001 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 543209217 1250 543207967 543207991
    0x120902060d0c0306090f06140906010906080709050a0e180d09030f0f1b030b0619050d020a030507180e0111161a150108060904030206130809130b100c0b 67
    0x4082c0c40f8030940240f0028440020148000c0e002c403114040101803a1140c1400e10034103d00072100c80c105456280d104000507100c0d00a02450010292100361b401403950040102d0f208001c81c03660342e6403076544050310b80624070100031b1074502c41c614020b002c0d00043c602c90390300005240304640d500010a0b016a82c0c81190140461081d103400d07000c0d500040002858215905166403940c2d403480103500840b070007829010307402c0c0c40c3c2109001c2400c2440841040380444618148118144248202e140d20b1000d001503484035074a498041c180100c07504400030615410140d112a180036008441c10549007000803c034524203018070030514071421003074070180d1401d4401d040c144000906061455070399001130000c54949880356003000d502c146100380c0826103078070210300e02c2c0c101001ca03107214075031607001080c00740c40f07002d0441018841305404842e490700402c0b001000f078460b0704c9207402c00d01074920080b0758892050300f0010300d02c0b8603606a5081103200c240480100720300c0150703d0f8102e406d00482c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 543210467 1250 543209217 543209231
    0x3111515090f0703151d100b1e0711042d02191103040902040807060314070818010906142d060409030e0405240109052b0b07030507120902060d 63
    0x1036024007440560100718100150181e61b0181030480801600c030314003001c04103071120303101e08072910300f070268040729804c4030300c040b0461418121803c02003046130300883e0886141e000350000034080c3c86040030008035440c2c0aa44425400e0011408540c2d0000042001c0d1f0130101c206041651000340307951a001003140d00513000109100c00c3c000c4601070300d0003c206654460716100c110b80c0d540e0551040d00300103032825400302c0c00039001b0300c01c441c0200c400c0c2d40c5801d0310361540398075a001020a503801c0e00700c655032649a080000c0b01c61081002ca00c170b01594040c420310301003405e201c080c20030075044400c500c943c054203001e0b2007104d1440c80d488101100d0004a20702c06040440f802c0c070101c0720340ca070420b28005c1840000440082d800c00004010b880203101c0510341e4004403000740070351240c9604038180018031501e43e05440c7c80510505c01c405912510343c1900c4d1034440c0344034010313a03c0b100400c2e9030b00b045c011020780c098a4021a40409602481208203980c003141c003c0c800c0014151130907550344a = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 543211717 1250 543210467 543210491
    0x513022d0403080d0213170309151c0e0c09010e0c030c190309150e07030b15040c08090609161509080106080f06060414040206030403111515090f0703 66
    0x825100a15003003280070f0384445080f50100c00035804138003071184000320b288000941c07000342c0001c03840a0010402640c20309270382e40140f117040c100c030042104802c501800026038144c1e04180420720400c404201040e11008c0541c0c1500f810f1150202c0e034001c62204005115180b800701c401c0d034120407103038030030303980c030b56800301d030040a401045141c8440f05607541c031348607a660303064200309030042c0034404291a19503c080c11000710341c890f482a43c42d940045108001054880c189190f00074158560505ca8000c0b4000140c110b031001000302000c03454a1091004000c010820319902108000081420b0050b1800581142240c0d02c104d03410a06602d844400491041d81e031a801400d8940080c404203844081d002e072200b4442040d4201807058000241552034180140b40325204032002c000000e03101d5400788040c5520052081d0103115102d10495880c1808101050144982040303484940c208440680a030011031100f81d4481d00005041c0f145130000f1340c0d80250010b0300c41c200040c000c4a044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 543212967 1250 543211717 543211807
    0x5100608040f0c090902100215010603020a09030507090c080130110301050c0d0c1b03052206172401080a0605030a0507060f0203070f02011b020904050106051302 71
    0x212000740351000c0c1840c0040e130500300b50441c0c595139108407000c9110f10f078494800c99580c003035418402022954100108030380e80c000d60091008070b200b481d00e2032209403282c640620b44100d40d40700e03640b10341d6203481c2016030540c0410b507140907120000007004480041429000000180c2844007031000c40000302070100710524104546004000d002400306250410000c00c040e040041010402c0341011322010400b441024135000b2043c01c034030480f00700b09141c1c41c22a4980c01c0088528048420b0134002c420310903880e1034010040101d5a03911681168807110018400d1018044141c001c542d0b10701c00320354502c1052290702d0f503042841c0c494200d54645072034070b004c0e1590b58040ea426000d0ba100341d02c24020042666000e54445444400004060042c100d950384a240b9018050034084060040150300c0364401d48620200700b100c40413004c0380c580004402507001c4d60b08840e02d03035403034000300541d0802d00c0006c4c240d203000503021418440120b15400c12814010345440c05000700002c0c04d00001400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 543214217 1250 543212967 543212993
    0xe0604082503140105011505280311040f0303020d031e0515040e06060a050f09070c0303020d02160501050109050c0711060403050d092907030e150c01020a09090510060804 75
    0x306043c4140c000b1240b25070003800300b0300940745000685034094500c0ea000e0f00840304200b04100000810980007407002c107a1402e110b080c01d04142c4c80e13207452040d4800b06005000a00302850803001c43c1461454040c0c42c0c68500540d10703007410f040141020488000406040c41c80c0c50100010170070b07940300c0704805204c800c0703c6070703c60740b040c079050b43c0051030640000d10501c91601a600c000c5a07546036010801360203450302d440782c1d2000710800001e4060f40300b003414112b2a88242005810504900303200da0903a0420419240817907103400e080c0c024090240190317401006c584600b00400c0c104044580071903c80c5650240c0801c1485901c2e503d035481d01001c0750000e68010082d21641103058000403c209020f2041c0c1f46068521609070710451480c4d00000d440e00d802c000050300e002c0d42c80c1d8058130380c0040342c440c19910103203540f4001c8081301c1c214000c2030b48070805000166202c01220b406040810300d900101030b054038000401c002e4484030102d50303050703801d2410324403100d84e80d1313260040c100100 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 543215467 1250 543214217 543214223
    0xe060d02010e0a26060c07171608031f0608010620070f0503150601020307062d0e0d030501030c06032c0114010605180f0a05030303010b0a0e0604082503 67
    0x1c40c40f000442a000c40b0400c8240070345040308200e20548040429650320702542e111a800100304007d00000700d03060826080f40f0408040030f03083c40d00440c4001c0c46000b42070000c1c1c42e4480c00004020990010309641d031051031594a0306128503082c000d00904485050045c0302c24812014030001c1d40300800e003002c02440840301c0407035132029200e0705010680c44082c850300d80280b0a02500c00030403000401480e01c6900180d0007141816000d0301c0d10320141035103000644600e254107042155521441d02240703408032000101060384140d01220320701d170000412454007014038000c0103200040d00c40100b04200c03a464540414210100b18000809a06959002101c0a201c10740003001c0074040d08426600c101642d804802d680c2d1350032055645100c0c1030341030f45810510303102554075458040400d880c207882c00381c00116003d0b1110b01080c0765602c2070708581c260920100d00507902c03e5100c581c0412002d010303650141818a080312299840c50344500b0130441c1010109042c1c0f82c035110903041300055070 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 543216717 1250 543215467 543215479
    0x10e01110a02070807060516020a080d0c110d0209040f080f0301090912140d2f04080c12060a0507051603050702010e0a18020304050a0c030309060207050108010e060d02010e 76
    0x114240100d80c00d501c20203400025000c1c902c000960802c1c0410f0a508540468840d1841c00000e1030001d08041140841260f01450384407010416050801800d40c0440941c5c035601d03c0c10f040e03410300c100020220600d1070b10076555031000fa401a00e4089940d0b07081688014034003081070440c0341c858168010f16007101c400c00000700000900749000d4108001e154094111000342e080304c2001229501e601842e64420320000f041052074513003140d40500d076800080c2d0260303581d94405040c58000100003140800d910304000ca818401d601e4144803d03104500d040f21302c1c400c2068801c40080d1110780003050440704a50720310000314294003a2089070050b40441c0d0450801c00382d2450060450b401c80354040c1e0000e829543c42910303504040f88014207540f050301c91428400c1d1000b1003103001e5400240121214029243d0000002d0760180343c0300d001e0341c46600c07600c1010f0704042000740381c000349520032030400498200401030350810a00d140c1e0402816505507802901a00042ea1b4060b190044a50401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 543217967 1250 543216717 543216731
    0x1e0a0c0f0614040b0a1407140a090816331d0607031106060328030e0d051e0102090906010f05120f070905030a120305040312050403050a17040c0b0a02010e01 69
    0x790f0320082078443c00c924502006480289054003d0004049555002046c000810150721810780000341c14110344c00d00d062b40c5043c5e15080d445041000714040c070034035540348107002d100d02c0c0640f02c0c14500320910011480710804200118520015109003100103008a040c0c40c4006414013601d2604000b80c0901125640e0016180080c0202100c0019004501855021515518000c00c407810140c2514890415080840103049120320800ca021000d01c100305005108030307151410300780d41c118091000380142d0103c100c2c0c00320b010245420100416407040000072103682e035104010307820403002c0c6031840810681c040f007a1782501c00c50b80d40c0c144006441c800c00c41c0c603000c0d0b56000d030b00caa0299a02c409105656005065440100304802889041c2e0010340e95840c034425806194800d02038039000c0002480000d02004031201030b00c01784c1c0054000220710f2002030b000001d0408280c030880704003603e89842e448d090010b110f40e00038021140800076840301400c0c400d4005000c401c3c0711000801283c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 543219217 1250 543217967 543217973
    0x1b0f1303050307030f0c0506041403040909080403140a0309090f1e0b040e0304080a14011d0109030f0806030c090402010e0a081f050c0a051e0f1e0a0c0f061404 70
    0x180d00310642c201d00080c1c03081d6110f500c292044010f900c0c0d180e4440008c11168645980d440040514280c1880f8540320038030ac006451012402664001c80c01050b115035118107508000030710080c070032801940d0f9848048000006503002001000b1a00300d10000070381c406001c01c403c0040d1030b2200481e0141c511114a640000c1040d9100c0e8035104006c8400300141e070381c1c071740c901a102e008600c240d0490b0341114003818080346100c50045500f650406c000124012010b0299a00b03802a280c555860b0395035002d5001019040668005a070700d460502c4440b0f4580240043c1d9240c00196600d405050444045021a401020314401c000c3d801484825016203072000c1c4c0380c0c0e035540190b0048081070040981003002c082d40c032469000b8910004298503200d446081038440b40c1c0040c0c00d0310201407900d0070040c070b01840d500180803403800c004d29581e0741d00030b14070184c1c84540380300440c4552040100800c1d8007541c0c01140c2e106506600010102c006059401d000008210000f800b04019490508002c10 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 543220467 1250 543219217 543219223
    0x60609141f170708060f0904061103040f0b360a1416090b0a2102040203010e011401110c100e10050406020607020304270213180609051b0f130305 64
    0x300d0100c40a4482564403440c044821303d02c2503c02c503802201a000c041c14600304a20001c0c3d00c00d01584d00810400c43c000001003041d44200d034207481d544ca001c4600ca0400c0b0400049541140054509200d2070403170344860449501c19083e010b42d85100b40b9220080c91038140420b040c0b05421641601e14a2070701a40c0c1600e603c1710780d03540040c94100d004c001c2003d5041c1d05c10850b01c410040c0c00610040c0c00c20741900017000301140c20829071450f2410b00302c0140d03513030700055002e03080900c00044154034000c440e840b507043c0c0e500942d05101a401c00004200e8000654640c4000d00300c80c0750080b00703455502543c01c04181c99080f900500d0702e81303c3e240c806810900500c210341d01503081321015a07071481f04036201c1c015802074019012150750340322500741c1007a4001c3d889400c0083c0061401c041030490420303100581c1d000c07482140900c80c1030150786c10700303124510041140510501480c0361400b40c1c060040d001d081c41d040703110f40c003141d401004400b0b03209441c202c41c0c28110011542d83ca9062080d9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 543221717 1250 543220467 543220487
    0x8010c020708013b01110901030e0a170f0c0109060b03120408030a050708090d11100c260f0403080301030219030308060f04150b03010e0703060609141f 67
    0x2610444070002001d4005204046280c084000e5024000030801c944803001c20f40041c000021907100819a248401c3c00e00c10300840d4600d103481aa540d032001d03030000d0140d03040b13140c01400c1380c0c02c0450700d0030106018074050800d00d1074121400f903a600205004142c0d83c00b4402051050307600c0d21040808000e0640d0107805007840071400c03101c1241c3c0c840396850322032250f0300a842c05600140500d00b000c03401034000d000500c1c070a44045080c45480070105c0d411081c03140003a100c4030036444910944e410b12400d40b621407031282c0303003c05030742d01c2c02d072a0202204c112003101080454803080400060f007007030090340d0031808402c9000d47e9650b5a414403107440d0b0400c2c00180c4c4100940c80c808250720703921499840c01c4aa064881d010107948040030020700c0d0150f19111900203848010030658880d42d50004000b80c4482401e107034495040810621040350020400020725152072000d201e01b0b0b4101602604407116214900400540030020960280700030300d0301c0c180414101c0000c0405500700203199 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 543222967 1250 543221717 543221741
    0x3120e0706031401050312220302040e0a1502160209060d02030d021b0a03030903020616020907030207050f0c030c10020703060c090326040b0c0102040305030f03061c030e040c0e04060801 82
    0x10383c081c0d88070000c0540303880002e40305000d0720790104250501486001d0300b01c0c0e0901c041c070000300d40c1903a40f500443d05442c2c40382c0c45030a1036003003200704201700051403881e201c02001c074800450901c2e821981c410006280e1000181c407070422400007410599170035407601101030b80901981c1640c42c0004000e95600306544000c0000034030003010302d00e607091003c2e4030001c49401d03a540c00b2800d446c6800b401390350ba2102a03030303e10000300f00d040800503071903062003075015902c2503500603034803601d41c24602c3c1800305111b4000b038580c120381103a0034582d800058400d2018401c0780c001c807030f40e241c4907816450019540d2000342a03d007010001c8000c660401e4032242100d0040c04000b0030800e01360415a5035612070100c2441e08501403000340316481505024003103031460000018602a102d071075591664221840c01c0180d0080082040310700e04042c0301c1c90780e140006489a5200c0081c80c4e4010784540c441c2c11501c1d00855880c0c00a0302c8140c0b0481d12201d10410151040045c00d4841100394060610008070f4 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 543224217 1250 543222967 543223001
    0x1f0b041b0503040308130210081521151006080621160501210f0b0a0909020a1d040204020304020a090c0c05071a07121701060c230a03120e070603 64
    0x1402c0c90781c06d1300d40901040d802031000040c503040c000c0995104902502c3c10f100010940c81092031a11a003040409115100344207210054128005510300703075070340a401c00140032000a0004210074411600e09541481c200400b099039143d01040440c01d910b10a8220300b0310b024540b010a10020450881c8a0146061404026100c1005440410fa007291180400d051484030410300205a0f004a1421980b0301d804500048a0700000360050310381d4209802280c0d461006c0800c44c580034480b02e00070169021268003041c0c40000c00010000e0040c0040d00075900000014110740d40c1540b00c202800d820101000031501805008021103a0312500320f03040e00c916000401c2584994041014034822001da2601e002300710380c0e0380b488a5000c510048140282484001e0849010b021058041e00c41c0c1c0e0b581035500800c0b8141204010302c002904075200a400c1c1d40712010b5103012a196903420b030141001c1d0b0032205001d44180c001d248003540c4004038002c1e0100442c800b0f5040d0840e05181c40c46070a4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 543225467 1250 543224217 543224221
    0xd0c05040c080601050d09080f04091416050711150408030a0e03010b1c060e0105010b03100618050402070c0902041706150105120a0605031207060e1f0b041b0503040308 74
    0x410390350302c031080c1c0745580840d006010325036007401d20740c12000d006440b07980e06c42c1c2441013413807040c405a04a500300500b815150908803030040d28480c0b803280e1000200e5a1003440c54101e0001070213a100381d80010300200181404404643c0329401c58000d55030b50f500c0e090790307100d5585862030307200e4001c140f12800280348606580b103d446c0500601101080081c64500304010a150244d03014072040e10031a1041e440c1c1c0b10424801a00f84074081c000d245240c000c3e0f50301d00d40280044140740795a0819824030154841c00060440160000700641348180c500690b61800f070304041001c004c0d26070010044170f0001034080f40d42c0740b1580100800020142c100c482945501c107035032421004107100180051020f005240c910040f42d400150400d0040000050403601d41c004603081c00c26194002c1030640c40050700300300b00441ca2082c0c41407a850741000e0203003c11900c238071791038880a80d409900300646071985580d06507500e038041c0b00200e60b00e8912c50801c640185010340305404c112410f4000c2424040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 543226717 1250 543225467 543225491
    0x8010608070e0906040207051014010f080a12050d0f15050a091a040c170405030a080a051303050c0124050306070f05030a020a1e0306080d09030302070b180d0c0504 72
    0x30b2050110014050703103c03980c9040c20f00000750001e02060340e0b24894040c24104216441c80742483c0f603600c0341419041d03981003c45022101c00c8950244085501441c0840c001c42c510307900c402e12101841ca8415070343d008442c0d0003030241c1414140005004d2070120b0001411080224040443e070060f503000701400c2e030300c401e10421200100b40482c4203070303041c1c020b00748580303002e50100d214609079007003481441d00b8100c0121030f00c0074202c1c0e00325034681c00010010041a002001141c1c48030200b08140228030f0404440070200c555000c008003401400314809525040a41010100b515410140c0211008403181d06600301064450b5a01034000c00340400c0440e03204500c4c0b8007070b1a075240c03126803554580c0259600254070440038841080b007954004004800c0c030b800380600050003030703601107000c509054580b070410400f950b0080900122080804c002600815500101c41460081d1500e03100840114034100c0c0c8424001d50f40225540140b0040000a1061005455041d1010014020012 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 543227967 1250 543226717 543226727
    0x18010905060c1f14070c0303050c1602090c041d100503070b03011403030d020c0109060f061a0d0615020a0501321b0a0c0203011b09030813150801060807 67
    0x52010401e420500300403c4404104886100c1140010340001e0809580303c84002c1100040d02c03c200042c0d540314169040c160b050203090340145060b42024a8882c8514030381840880c1044024010444000000c444c022480d098600410440103100ca81180340c0c480100ca160003200c603c201c08000ca00c000c07030f00e130070300007000c101b500c0f6030800e0b21b031445e428524541c1c01c03407050ba44a80c0d0b01d0721041004d03421246107400600020b000c050004118540c251405001780d424841a004403186007000400c00c400d2650003004e600500d01c0300d0280d03500f010304411400b1380140d40000750b60b03504803442d8414143c3d0005105030002c1c01500200a0100300e01344543e03124030b007045104401078010742180c180075490880710360460b680030454006032030070503581180d0741c1000b4031b250081140010003c0a6090038024409440e00821040d0340152a00d00301600c0c018190101030403001c1d02142202c4c150641d40c0505e000b90101200d0080d000ca0728050080001c4006d004440c005a0b1076804100c14034020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 543229217 1250 543227967 543227977
    0x15100e120f0a020a0e48090f0d11010f05041205070f0e060105030610020109050a0b060f010201060b03162001270c1e03020a0b040311060a0e01231801090506 69
    0xf81581c1d20a020303103d031b05040041610341d17900e8400c0720310040c1d20220340f0380c0c0250140400b07074480400381c44034584400c001c03803018a0940e1500079030301c0417180000903003499003a061034503003400c02c180d5940c0901c074110b0362030203690440c0e0460b1026070803d4082c0400014050100c0d071072480a2a071554540303103801d1801ca410f9908070f0200c1c10510219980f40b030004c284d0724200100307200005100c0c61a0b100c06141844280064403207038104428410642403040c1d000c07a084030207000a0040910300ba140b90250f02c001401c1700d0888800700304001815100d55000d100104d803c00004e05da10040c51001802032107061641e41402c00a0352400d42d002900c4400e604503941c121500410341881c2c40000217042801c07589401d2501482c040100040e5a812846006880c40b60308260b10380b1b0841c5001128900c05d0844076114810502400340d02a50108001c007603480c003841c4c104084481000321031040304000039401c01808010800920408180c410841d100209a80c0daa4060340e44006200c031512134 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 543230467 1250 543229217 543229231
    0xa0905091e150414030a030606030b01170402091e0406050a2a0f050423100302040b0301031707060c0e0f060405010c0633080615100e120f0a020a0e 65
    0x2142c0c0800402099150500381e219000c2d040075a04008807150250455100703007101004a5600d403800d2240e241c1c5442815411003013805d200c100d01c0c1004800018116000b08000e11804050000a6070f1110000b450f140361031900241d0240e0381440e14018020f003404a42d02c41a03580b5003502e81401c002c00c40b0052a040c40404418030038450303684011030b9020001c00c80340c1c05020040000181140390540302101f03151120320303440b9a030300c089800c110141e00004030304400c00d070050000741308036102c1c2c2042f82d04423540104980d0154511002000550040c500301604051038400c10011a60f084030507204080411075509100201300780810846001e680106800503c1c0b140c2c0d1040051566408625064041c1408900121180400c040c0034409442805140b5495520810022004001007500660782035035484100380010042804c0c030481c00034000401840c03440b620000d80b2912201e446c11a40d500035642c00015003503041c1e1791a0321611089008010b18480003a41c481100513017805821 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 543231717 1250 543230467 543230473
    0xa1703130201030c090305070b0a140c1207110307060909050907030b071101060e180709061a220306020c1029061201061d0102150601050a09050a0905091e 68
    0x1d8004500070113100c0da0303103020b1002c4550088040380c07041110800a040a03204a031342c2c0c80341588001e10344048130035001201c140c10321403240442e101156a10601c0300007540c890300d549940c100400313200c0324410180d80602801d080441d4140e03001c01d4070030988031094028443c80e120400520741c0d0710b010780300c0500240c1d029000304400b144200380c28080d0140b01c0d000400c0320340c0c86e03035141900700c1c00c1030b20f400154424103c4200c00c141d1080c892600104140441000b405103000b581c50b0110011010301d03400080d000034494141c100c2c40135928040c1240703c1c0e410415603182d00d007000095108030300c0a0b009110b1059089500c6c501c0e4011610a1405040490300018402116109000e440c649145c0d00500a1054500640150700c0003802403c8980e544c20f10007071140b18200058844040c07260454200c1000e040725000041c6402c3d4100350207281907030340e50381c8003c011600070056400c2951300c603010442c0020310303250942005000300702d4041038455003c1614a4541680231060000150390 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 543232967 1250 543231717 543231751
    0x90703062306010503060d1a1608010b040e100e1e0c09010527130219080606190e030a261204060216020a060f0f030203270f030a020a1703 61
    0x548107002460308244050314074611f00c2d6060751500c00c0c00750500010480028a102040303050000550307a841c01c5845420b120350194103015243d0350920483c002c04c0720800c0c111000c9002c035010b194500e00248220081c040450616448240c95141134001002d06100c44002241f0124611f0003100e069150503122546440318410f460405070200d42c5401ca40003e0380c074408c102d591101501c0078015400040011f0395039548070a55140c01040a1050082010036020022030791903000c111854103130301e910441ca030840c0c1d0172400c4440c803144044894060084d204120108048a604011003040c0d8849154413448080e407a140c19015540620300c00e0302e00100030501083c0c1541c000c110120000c59503171102d0000340c0200300390b21560752041001810007111a4007140e0b1000505840c038070985000c3d4a54208813088904034400010300004410300d006001d1a120810491900c5000744042600c0e150314081c00003a4542e410b09509540d42e2901d0000c01c083c15200c40110313071040c00d030550f400c440c00f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 543234217 1250 543232967 543232969
    0xe040b07020114150d02030c0301090308090d051602280f08010501150e060a020a1a0601030e0d08151309060605100f080a0c0c050609010b0301240501050c0312090703062306 76
    0xd03045d030f0441603800d8011106a0b0180b62003c0c0074408289000380c07501d40850030038141c81d51510b01e1840b05042000810b000e00c10f030a82e0a07141d079520464048403041c14848440c842010707641c001d560614040c02c03c054002825007041c078400802c403082c1d40700800942ea60ba520062a8031940d41d00d1100050600c4040000d515100003d031000d50b419204a49240c246a13035a03c0001d081034111100c0c82c014039042083e9581d140c0142014104003001506070504951b0007d8400d0f407000e0030300d100f0716002420f00b03109900d45c100540d40011031000203101c54041c0b801c109005200c9801054050300c5c41c0c004030041280034182500130001c03103655030300032580c07210700950052a0318500c041c100710f442c4844c000458010460035010300103801c00002c40b0780c04031007050300b1981c814001200702da001c002036000c0140901400340c03c0351303002e09002d80c1d1808107442150840c401c84d204180752800d44401c2c4004c1a400040702c4040d02d116002c1081075000c1040b0302c0d1003070031042d0200044024800300003035171 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 543235467 1250 543234217 543234229
    0x303030c0307110118140a03081603090209040803060109061e0f0c080d0e0106050406030c180207120201090209060402030c09010e01180605070b100e0103080f040e040b0702011415 79
    0x40902c90303280003501000364091190a584491200c150010b4212583e0760074003208254180c00303950741c03030000e0184040d1542c3c06494042c0c000d200d03002c1461450072490b1200e01a410404049600401004070742c0340038680081d89400c10384525001503441d00700410824000c0c40051201c3c250a0071002807110101e0341210700c250440211410064480070000005170488081d0580c0c0543e280041101c202c8411481d0858000340e028a04c904d05040042002c02d10040c2d4032000d40712021020740c82201c0100701e0341c01902c44e5841c014250710000c114540c1407541036110a14031031085400143c541c407107100700001c1c3c0c041560200242c04040109405560140300401c0340c031603040c1400d603940042941e0019800e00150701c814042000010076008001c2c070741c00300c00ea2020245240c00c0005041a0a15030080c20500000303201d070000140f02c4007030012420503100200070003075542c0c015140c00d180403140b824013583c1d02c1e4055802c250103100c0450000c01c14a1141910800702c2400461030300812075 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 543236717 1250 543235467 543235471
    0xb0c03190b03010603020612041214250b010e07080112120f11010c020c030606100e1e04050106030605040c02070e070e0d0b0c09100309080708031e0403022503020303030c03 76
    0x2e070665a600c4008010784071203001d003c080c040c070940f00080c2d00d001c0c04d0a002c094a01c030900b07010006841c0c1400b811030203034010307078a0000007005545910382081071159140c00814030702402c03c00d408800000c1e10680b4a000784e1040b8072035500d1001c9642d0701c3d141d00b2581203072180002c0c090244407400198070f501c50481820381c1030301858003010700c01d20740340c0c804e085501d034a88850041e08403501741e81c80c50804010158201c01d0907542428a1501e03000d00401610000384800c0c800d500151190400d98040c1c9841c11621500030000c000d5035a4404c40503009204511035940038509014820581600120300401102c0545c006074411f0b03030b0b40040c129034080142c00c2c9568800d0110704081c011400c1003449621500d115402c481d603230040c101c03c00c01c200c000940d440c0c007058100000070001480341000c1e1502c0d10b5010090b6504c2e51202440340d06001d00c0103410521100e0303280100414182d00186190611440c06a00030441e182104040340e580d00a000c0a50035034020804510b07040c81e0800216 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 543237967 1250 543236717 543236719
    0xc030403020a0f05060106030e0606060f03072318010804120807030e030d1d07290f160c05030c010e060a02070f0308040501090b030919030e03010f090b0c03190b 71
    0xa07140703822a6444003500104040203844a034003070401400125018828800207191030802010945000c100050951080c1a4100c007900b0b0040081003c5500400d43110001611b110080180b180e10b151140703c043c0c20004800024004a00b00e8900300d500441010380030340e81040702c0080100d840e20040e40c0b000030103440001010742e1200344a02c0d008062002e042e200b20038510201c2d00065a4030302c2101040c1c4001030040ca0303002003000304850f00c044440454090355144108440d11f10008000e0110300940308003020580c030000d9010140341200c03412050062003080511007940d21607040c99500c0f100040c040340071480c1c150160300146015801b81441c4582841195402d5440d041084402800c9501c100c0b01c010f0007040074442076812101000103807140d8001e050441c42c0801850f55903c4036014401511400246040d040c140b254100c0c1409071030160083c05620322144107500117000c030f0705003034035070001c6100461100b92041085074090104074a001000200c03050410009120710b100c21 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 543239217 1250 543237967 543237973
    0xc030e0f06041d101502030a0804030e060403151b02030d0b13020712030c020a031e03060b04081e0d02033004030305090d08010806011e0506072103050f0c03040302 72
    0x2582c001c00010011500300602d03c19012814000000c0a400312107030405640c603400c11036290406a4000185c845000c038030324003404030380c07541c2c01c0a58001c3c8442813025080000010b0200600c0700c500000805c41c0d856410400c424a45000d0a20183d4000d200d001e00680007000700d06840c0d180c0e038204045241004292445842d40d900300030b000c82e80101c4040b2032910760642d400c2c00b260f41601c80c452400f8614009001440b0413030350b0043c421054402030a00c0e50b07841d81440c0e4041842540510080c1c00034200d00d5940e5920744050503039603a82c05040d001034078010540300b0044800400e2186080015800031401c100d460565040b140b565010040100f407a0210030b161a20360042e40f560080740603031030019450500c3c09006050900c00b803c81c005110481c0c0040110341c8c0001105411100d81060389280d050801c801a0807a10960380156408040868660180321a00d080300d071a1003001c5103005000c0d0f86495064040d00c900725070405030500c201001414800a0400540d0310910901c15 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 543240467 1250 543239217 543239219
    0x7030e0f010905010506031908041a090409050f16080d050f0d0f020403020a1e030209060616080910090b030a0c11032802030c0a080a030b1c060b010c030e0f0604 71
    0x200e00d0840b840c902c820b8405a4407030f0300f40a04c5e802c1c2803210180a40652015a13410300c0c3c1c03621035884601c41c520031340304d803d0f0300c03030009050082018098400c0450028810300000e005030502a5840e60061295aa03a0244424581c50413045184d144129040c40300540380620710401c0603109500900380004607484200303c1f181d007200c03142c407486089000a030700050711103041d4011b01521740003580216900c0005100c054100d120b110880c02c084030b504171038070416540d0300e40100b191401101607013050f010200a41c40300304205c40300076125140f0152000c3c008607458030011905090f05100b042e070104420004100d034650301c1d801900302241c0500340300b20404030b4a40040c0c51580850000c136850b10500c0b005400d42a10b9650020003200380d4030045061880e50301c46144c64049241000306108400035440525501079001050f07020001407221001c044104038003440c0400310482168204d140101190742507024110840d889501543e40203480c0f00030380c0c2031004c0c9419080080d9400401804 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 543241717 1250 543240467 543240493
    0x903090510050a09050a120f030302130f050306060414040f05070b0307110705040506031b030705040e1b010206070e01200609010605040e010b0d0f1e06020c2407030e 73
    0x50506460107295521a5581c104203002800906250411449043e88030401c000003440211031551003034010540b0b081d1954980303001c0d4020700ca041c100700043e010001001490b0480c005241c803c80c0c40540542c1d200b0394408042000b10313003480912010240f5030402040102e00c0303446484840e20b00c900d0480c1c00c1a40c03120442c4005400448100000907d81c82100d03001d400300340f0603003001b030006071400e0200781400c0d8000703501e9909017540000d8071040041903070101c0d50204100402080d0283c4204020b20400e0685615003540e4030f841901c0c900d15415003c4103510009840d441003606a0f500c4080c524403500440703140305001104c50518008640220003204144003d0f8090b0300c0a07400025018030708000c1c4015288801940e0030541d15007440c44100f521805102e8031180d40c80380300f9071188a1030b0320701400030b0f202c1d03400c040602508920084080160340d900400550305600c08407542145441c8594003030622062208001c8488107000c524418025000044115540030030b40d030464a03c10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 543242967 1250 543241717 543241729
    0xc1203010819032a02120f07140d060c0f11120f0304030e10020d030c110a0303110d0203400318030b090102070b010608091903031103360a0609030905 66
    0x401613902c201e40c811900c600b1480c1000d02041510340c210003500070110a5454140c83c3c0c2d429214800541090070402440e03036480a134140201e5034040340401c5882801d202c0144800d12204d100c2007c90040c90340c040711082c00081846100c4140c8030b40780d05d840852400c11001ea000504105c023481200e82001200d5070364600d08041d04444c6600901a60392030501c000c050b03802140c0048188401c2c2072110380c01a6003c0360140c0d41d9030f050b04000c030b61071551f80c0d08110184110000101003e2020061002d80141c0d480120305108504590f62005801c648990212108540c0c01e40d11034001c0e0a06000000c0c01812201105a40c080c00240110b903651a0515440030880751442980d50006640701085465182540540120b00e01003249141202456a80d5520010042e24070104e80e18080d003054801d4000c900051501c980c020703164100458201c0c036801060000103030400303000c561011039500c0140c41c42c000311201c00007418000c550b0b40310303100100001e0b80240c08012a50001190b01e450750 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 543244217 1250 543242967 543243017
    0xa031112040b06010507050a080c07170714010504060e0909190803101205030307050d20090a080c0604170102040803030903211603050703200c120301081903 69
    0x106010a52403605242104444a0040500b4180031046c0409404500d00103040960240e100d0b040982d0350954541e454940512a4818800554000e0002844400c0030800004440d000507030480059038440054810f4040d500403880040c50a412414840c13030442d420a400c482c074402030b0740f02e29022a45001c58419141c0c0c0030303104101e0004c2031050500020b60717680c008108106094811400507540c1301c0e00d0b44800342c40c00d800c01030003007441111101036511030040000c00c10f000150300305e50700c411440d440c0c00c081c03010342c85022868800500300601003601c005400d001031940e4509070501840000c0030f038098030340004544d42404081108081000190300541c07225000b540c03291460400303201c00074150140300648400300b40900a010b040e80c11040c000090354100460f91703642e02c030f40880c0100050303241e200c1215150361010b10310183c140020300c420b000c0030060b03d408900c2ca0140e0066407000b07101d0341d840c075071000181004981d02c0f1030704101d0303052280c40d20650b621002e030000030b56101c507 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 543245467 1250 543244217 543244237
    0x13050703061406070c03080c0f060106090513052203050c0d0305060a0602031206040b0f190906080105011404112b0b031c110f010509030d2703050a0311 67
    0xe5680148400400700c0380c0040d407044103d0f009440d00d2015a6500c040c100c56110040080c1408600100022014090141c1c920510700c200c411a40e9180740013000e2452034424540a441d481a8858082406002e2503105066410503602c80c40c040782829507013088450402c0c2c007007202c1441000c000401c2408030611482507560049014284102001070502c19a0711036000d641c070070080720344424140200c00da8007500403180000e40c0030303520b004035410740d148022155201c0c0102e10301c403150629800c0e0300001e68010305010400c46444010342c80c2214403c1c09407104044200815032164900b503003046a1290200c002c5d603080c803075400f01301d800403019510704408480c60b10410000403000791040c0319980c03070110300500090136280d212822003d03d0b8900801000005a078042440a040003280c0c1d451048000070000d501e01840c2440d265000a2100d002540c14556000e40b1501009009101c9092004007030074400d51569003900c4560003580c0c42014151140c550566861102d006003607003680d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 543246717 1250 543245467 543245471
    0xf03060b0408100e070f0506031005040c020a051902060304021e060703020109021905011e09120804030209010b0c030a0e011814010e0a0b0711030307060e0d0801050901060f0e13050703 81
    0x10802c00c50050354100751350303a4000d52000380c0070000705548803940c0086032005c2d03840700e56030740728500501e148a54070782002d60460f00380440c41d400755031300143c2c119000d4020001e9820858580e0800902c600503094041e42c07012051020a000d450440004003000441218404031103083c0130100e0820380003000b081d40580d55561500d070550030700382c170001254a02d00081d24149401c10002034100d50703200c2c18901040c6500c080d040a82402001008003500c0201c109288a81103480c002901d58410f0008a0083d80080000142d8a10340ea05450f04103072680095820080c14240803a80d11300c04554040c100b003501d0740c075075540c800340700b112001400140786606242c004a8001501541d110501c0b10302980d0710040402000c0450001c3c0d49555510181030062003105100080c5076003d08000a0700f2070340741c40d0a9100103040060000440203040d101c80e030442c0c0e43c440402508403801d102c0da60114195a110146980c4a00b058284940d401024003251200804030f010890340101c8041c40480c0e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 543247967 1250 543246717 543246733
    0x60f02060a020a0518040b040f09020f0a03051207210503090c0906130f060e100509011a030601030c120914190507061808030d05010302090a09120f03060b0408 70
    0x554184802035001402250640c42c26141c91401042da20518060004208000e085203066540c2d85d0002d403d4150000c0c4180308140301c00350860010501114201d12842181e50300c24100d041481c5030b00300300c075041000b620000c00c2044178009030768071030101180d00813100ca10784e061405145c030344230002c55240d540c0e083c0c41e807510503090b038540040030741d07400d21400805042101d81c1e40c944400c40c0c040002144e01180342c4580003203c00242c0125048a036050803440f0030000d0105502c01940e00325242201c07007000ca0790780c1d4078034541c1003030402ca404210407608000080c0c0c07035400b0760400e80010840c0d14081015075448101442280e0304020220361400703600c81d0040710b400080002c210220043c0030072440c910004e43e03640c3c1d610140d5110721018060b400529055404407c2d10482c020807814041e00e40c0c90074040c0902d001408240030032072140f03c881e00400c1d26035045209100311154004248c00d17120f00c0700c540036600d010113015040c00700b50300e403a00030603080d0320900038000618107000101a81 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 543249217 1250 543247967 543247997
    0x2303040308040806220222020f030901020903010612080301090c0918060501090807260c0316080105070e0603281a03190314032502060403090807060f1103070c06 71
    0xc3c014010502201204940d000340580e96845103903c0c01f90031807446051038400781c034200019000e81d0306c800214000c04410820868010340041074130503422402000385940714001083c03101d0954a01a010880a10050100c010b0702e52241902880c3c6040c140c4115541f09541c1078000c0c40020844400c5803241d40410807540c11540c16070140440401a00c007060800300284c6180c2c0c2020100c3d0180c88000e1000301c0700c3c03841803024415402010b000d07106281c0e402040712041c04614441c2c18140c0d07107004000303041e840c40707020102c2030101d004001034903640f51451500b401d00050450170684540c141e0346850040020f00c260102c2d0f40c1c046403510f100700080307801c15042c00143c60341400f00c6c00c0c0c030b40c91b02800030313500003500209412115007141d201c1c1c0f1440d25110101903028000200c200907505c0304076546400040f203602c0f451295940c11406925410040d4449005214460102d0300c610030005400303001c0e43d280d03042c1e0481201202e0405089403944282c2c882698045c0d0f000c500b1b40b426080320 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 543250467 1250 543249217 543249241
    0xc170706060f0501020c01051308030708030702100c050f070c0b0d0e010516050427140a0f0624050906070b0912090d121206090203060a050d2303040308040806 70
    0x74041c928101202e98a0000040e445001c00841d00703040000c00514001d24171080f842d040b001c1c020540071030b0384a05a83ca072941050340107a48072809440381403440a00903120703011351030401c5010343e2880c2c00c1440604003004250404070342141c08180c00800131806540c8007001e000c8011480d03c000c104a580b0015850840307201504141500121361403102d1000e81003c1120700b01e41c418203580348130b246415410703c05c2c0e50003544181242801d0060000641810284007401a4081201000101082600b00b812034015220740c0201092104e40702c0320170500c60b4140e00d04c080c049e0510524080b4240c001900c10391020700d08035101c040c48000c4c8070001c4000c2000300381b44001c0741c540601d84030780400000c1c00c1c022074040081480c0380b483c1c1820000e030310442e009040422525014002c240d01c80310204007940003100c4050095425100024151605540344e000003a0890b01010007108010a20700c81141e02d003c2d00002e40c40708000c0040003800d42d03c01031006108039006010281840625030b02 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 543251717 1250 543250467 543250469
    0x19050702101104050904080a0507080a09052e030c030908041706070c15090816050d0e0103060e0c090301020715051b09310e0601031529010c17070606 66
    0x41c01203042c0f205014036140e180d0a6a0801e412107103550300d400411a0882c1c3c184140d50004002502c0810781041454114099009450302190b18000d035110051060310f07044000600348180c0c80a4218540d4024002e40c402405c12a462402207a00130380e43e142d42c1c501e035100754000c06084980c031211065881e07050028a4201c0818034100100d20b005454010100c444e81140d00c200da96a1040981000520003c8821825686000510f80f060718101191582c489d142420301160981017a01100e602c20b03c5518192590310450066945811109036100e800800c03c45030950340c2000301101003aa00c44040307104400450703000c106843c0c110004280381c007070240c4104101c901031111041d00d5680d00892030401c2d280f4141007a1001c140380c11030702020141120600500d143c06491840c943c00415682d050b00d024644080c0c03108034400020f000c50710201401004090061140c00d8005048000072540d18014504036080181c00d803204102c400400b03990340320401c800200d1100700805802404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 543252967 1250 543251717 543251741
    0x1e070e01090504080414010e12011e051306052706011701020f1204030e1c03030e0d080103030f030e03030123040902030c01030e03071e02010908011a091905070210 72
    0x40201e0a003541c401c2120b02175805071240e9200520340003021640f1030010180ca28000030140281c045040d140c0e1070003492402d0b540c0180d200b03c85080142c02c1c03050b0040074000c1d1400081e01d40c0c4148030752102d030000d09014220551b240e11804000c00c4000b0300e412041c05c0e0040c1c002c0035210a5140c0203806200e914070442022071a401808200180c0721000700356924608409110001944c86240c2115101038a100d00381e40b046104c41c2c08100c042d000e61300b2120071071007a00e0400c0321183c05541203540c0c0d88145000700c0005c2c140c80051000a124844601e01190350b0305000ca07640121100c3c040c1103800980040040700c5600300405070314490000d080c14109010f840801060b1110b030046519541000c0e030380d03030525844101c1e01000d60740c01c0044a006c1d50b0000814403041c28180c003091002032000c541603000401c0341c14040748040061181006c281101e100d04103200c900042441812500140135803118075076220140402e10303ca01502c1e101c3c6a45074054004c18800500751001c98a5030181c80c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 543254217 1250 543252967 543252971
    0x50a180806010905092e0609090b0103080f161209090e0c0f0a0b0d151e090906022206120209011407050705030316060b0f060304141e070e0109 63
    0x10050404041071090542d552841d003c1078940d03503040c03504d00d0b1890001503511580c41803ca001141000d119034040650080e0f0404c1c896159a0b2064000740c0f0600700d00501083c401d5001000000c0d0044001c043c01c01d003502c42d4505105810845130290384845105a0701e0514120341811610782c4002101c02900d00d0381c50030403114885009107603030341646524050046802c0e0340558440d6032060710107401071003c02031495986508803002405000e01200700c5003110410340c404100c2c1d100c0311240006048a40585e05501131805180b0400303480701410940344c00e50300300040b0100205085072105044240709052440320b20381800103046078151180b04900c0792040c000034125a078000c040c0d121103c00115036035102c400d0b504000c0d0503c0c00c1a804181e1600c000220003c8494003442c084102034004e82041110381440805d000251851041d59540410100000f170b0024908200c040c88100c5410704480101c030440004003202d4002950180c19035001c02d000304980c0c001d0300c504a000d004004c4c1c3c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 543255467 1250 543254217 543254219
    0x80606030c0703030c02030c03040b04080105091504061e06030302011406092202040e070f0914011401180302041a120d05120405150103061d12032a0a050a18 69
    0x400d078500030102c00a003059150328460030210302c05c20640364482011000e495841c5d984030b43d401010b40c041c1c866980f055080400080100e40c02149001c2000283e40b9414001c2d40c1c3d59442d00001e11000304980c0310b0088556010003600401e00c5268081c5200fa000061078001c414282c102c11000100301c144203110203400c011500c501c901b003003c2080d0600401101e0380d11144001009804000035025003480781400014000c3c43c103924502c111844403030700300031481c0280340790300d040030003402401000b01d104011070b200d651243da000d901d1642c9955050044984030b50000b010b58240c0401480000c02c5900740000714541021080824400c078002071000004017500600540100c10410420610081c0000d0920a0038840f044800066000306251583c5a2504d0320041c207000d2403411100c1501115000c01c540c0020341c4248420008041f10f007596a8000d020034418200c100040d402d00c10304041c40508034400001d040f400702c082d11925101d0708216402400d24907042d00740300300c0e00100c40b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 543256717 1250 543255467 543255481
    0x150915050d1d031c090501050405060708010602030a09050114120708150a050a05010804050f0d080f0f10050f042012060105030c180d12020a03030b03030a0917071a0304020108060603 80
    0x8126185001340c0f4542104800c28644080700401c0200800740c40b65007010f0400041100201300148149500c0e21103a5407a40c036048120703501c2c050700350708002040481105201c158011001d4440c509000b400d12440c182081794445400d2b030050358000d0110740c1c56824410200e01101c1c911004000960318110071600d49000120081003a00c17400f418040720310082030912200780840980551481c1c1101d5000c0400040100115070032281c1c000c01100e584040345031004140e21042c0250700b0700180799811030a1a0421a000318403244182e4010303518041004132014001032150245c8901d40420349a003048041740e01441c3c0001c0216042107c100200045140580b007644c0d080155000c05020315000720003c50140011000040c281884001048418650020383c1c1c0c107007103109581c10300030003500805140c1c0c1c80c020b04005802041c843c4005110004445031018a006240c1c0d0844249039510224050b03445900807400003000340000401083d13503040741000d42c020609036081d61440c40c0c00c80b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 543257967 1250 543256717 543256723
    0xf150206060405060111060103051f0c1d031006290a0909020d11030f090115063504050d09080a02010e0402090f060a02030702030114070207150915050d1d 68
    0x38500d074400d50b0f0300c01c08224564420620144c011812100f12980342d40c50341003850ba1a03150310451440104002c2e80c01d114a0781c03074003c005003040c3ca40c03030308540b080e881034a401c484214100b64903014424a242213050001e1802144003c00030041c1c255940090b22196882d10705548281402e088130412a03070f2219a4070a910341c00300c0ea04c2d4040180c5552188a01382c01a080040d2050b1075070f80041b090101001441240c1d078000c00ca030500801c00c422021200e075104004500c40d20b0041400140d4400c280901c0a41c58052546031000c204c0080784d440800800048040c4ea0603551a8030160080800039000188580501210710080100314110303400240280a2040341c5070180360007241480032611140d029207502031004000d26281d0403440390081d6690040c5005a00c250300300080614050040031026000c4d0349564041d1002c00d04040022618070b0b41e0a80c01810004484000542954140300c1004a0300599449a54aa40301e110000a032121981d8100201c18044d1400802443c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 543259217 1250 543257967 543257971
    0xe04030203030f07030f02030411040516050a0c0602090901030804052b0201030c05070b0711010f0513030507052b0e191703120903040303030c020d05090f0a0b130f150206 75
    0x1100e202d1139030312440c08401a04180143c10351150000c0706000c100202d58616000207401950200801d41d1500015005e442c4180710b5000891400c01802220034400c102952034140030300d80c05440c0150242c04100c0003202648190396984d00880d0500c070b40d1502c80b040065015000c0322901130252900d010800e5020949002030505503165513911515004106071510241c01103000803280c503140a014190f204001103c40681d46400c071501d20b00c84151107914015201f0f001384600d120182e6406580561101030281c4032441010714114411741d003010941e13541710000601217100700e26017401a003204c0b0f1101070b5510516508280e121850402c6c41040212a100003c00000650300003005003540300300c04000e000f2003034103020004801d00010052003124420383e82040003d01c1c0d1242282c0f0740c0c0f02c814042000640c00c00c003100051270030f50441940800020450040d05949998604240c0c1c0200c1e66001c01c00103c01e410881d484684a03000001d02c00000c605a844181d164002c0d1a0940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 543260467 1250 543259217 543259231
    0x306110c06160903061a0a050d150209061308011413111306050415030506130305340b060108091c0813020a0623090604091a130905070e0403020303 65
    0x1d031207940c0710345209440700c400940c5c110720200000e580d4601090450b0011007141401a11041000580c1d8109114510011500000004207150b4600c03003000195100500301d84c0c0c4801d042c40010706103143c0c010b44800901401d4000034030035030a10705200107254000d00e150304001c0040e07008004079007d10005c100050044615490208004c1c11000042946400a60b045460051340319010f403030700850141601c0c0620100c41c07169540d195940030404030b01e48000c1c0001c4d818800503c1183c7c10606082c0030049240340031240960303203090003070100d0041405441c400010414010b0658200c861550040d0800018280c460040ca01850400350ba84822a041012050000300201922515000025401041031201a03030300c0c02c1c0280b240c105d10a4800c01c145171105140b0300a10f140c0112a04101c014040f6410185001c101ca1700500c41d603004d050344014803820401c610b955450143c40c40f91020340c00000e1030801070804601d00b5009030416418800e05000340f01c003203a00002520303406a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 543261717 1250 543260467 543260491
    0x15040506031c0e012a02060a050c01020d060302100e060a0f0216080303010f0b090a12060b0d240902030a0b04032c3c0f0603010f0306110c06 62
    0xc0e004003081c034144803040c0074100580c0c2d02d00403480c503a42c00201240c09680036a5880090140620b81114510300c51050804e2080c8200b110001410480040c01440da013500f00103041c00444120242aa030180c05e448442a41d20001801145400c2007200340000140c40c3c4156140000d901190107841050028005c0c00f459040240c2c0103482004921403084a0a1581c15010342d134007210742e608e41080c080e86620001182c1d01281080c0b40b4016680d103443c0090000d00c9442c07a1401c20f12214184c4001a5061a12a0000704050711441c1c9500807407485009a4858143d991444881001740980048065800d054542002d6500012011002c0760410719a803141d4489150a44000712007461f100c40510700c0d61025240744102841184050800b03070b500c200e19410700c1340c00c409140c008a850642c68680f548d8103142e40d8403400c0c0d886080b000003608101c6160303d0340d000100650000d034405103004100020600c1040b4550040c242c110b000500c02600342210401103507140d0b40010700c20f2540003 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 543262967 1250 543261717 543261721
    0x1020309070b1b0703140705010809070306110903061009050c0a0c02210d05071709010f03200403080304061103010e0117010902040212070f0801181509061206050f150405 75
    0x2070440f032040c0a00f4822049941c01680c80c03400031001040030304035200502540c0c000003000c1d40620700251180f20400041c1508608540d103000c014105082800c80d5403c0c180b2203010561010068140608416805c5100d100d00c0d10143d0720507284000c200d103082b0501400500d107910342001c2d024030b00c203a04036400802c802900c0340ca01c110180d0342c540d040031840303241c900309010307a000401000c100d07010f03001c3c400600468001c00301140c401c01c001540000c0000c110204036520a500180300c200c01019000c02c801000b900b00450b680107500282e442000000502c001c1090a20824886114084015056601d0700203080e8100805110300041100c050705600c000200c20b60001b103c40380c0c014811904c45010800782d0500d90812101a03012980c00c1141c1c4104a008000142c12140d2070b161030031090700ca9020135000350800600a80c00071040300404940040c0c5805644060005010440d04541850038150140d45019201c214040001c000344402494500c0c14a80d14040a0341c000ca819 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 543264217 1250 543262967 543262987
    0xa090504021804110714061915030b090312010f050607030f141809070c0c0515070c080d0f03090209130f051c120e0a0f0c090608010f0e01020309070b 66
    0xa4014611010b910a01d002d013030400c04001c0402908003603004c0d0441c210080590240141d03100c07401c0d162424410890707425407881e507801340c1014001d000c0f10b81c1c0c0c3c80c01c95652503440710080c440a90340c50f03107035800c04580b010764000c4c5180c45900525121614002144c64403000c0fa05501ca030401c06020040402500c4030018000c018480300740304200190381d545e41c0d0345c0a03060101444003c101d8420380c168800b144100d8801c00080e03050f41c4c5c001ca0161462843c08080101400b2401000181c1340410b000c0c08000ca140300714280001e200700b10140502642d151801404010050324220616240507850740141e03c4000540b40d02c8000d000780c088601d80c1506009404055441e0003c0c0b480c4500e0001640c215181980c4944504168445050720208188100180e81f00503c01c400c5552012a901011610411031104658040c03541c3c01c02503900c031891042a100d0300d8100d510036079110b074884000c0c04071500c200480080c1060085045081c03452030583c480b0302a101d0404103035804902d41e079103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 543265467 1250 543264217 543264247
    0xb0a02130806070905100f0909050907121101020106050d0c031518050d1b08030609131a090d050c030d0e010b060c010f150b030c0c0a020d05060f0106050a09050402 72
    0x250140303908582c1c00b4605014014400c0113140281d50184944414a48400c0d004801c01e0800c2d01107500c0b200388207411310354408028007000303013110982d2041440000f00011499443e440550003600e240071000c1c1508000b90946110754483d0b40204100a6100040360a0034090300541742d0046100080e9811002400003030010703d03101601403101c400c0034030100900003517401144405502c400d501c401c01200c2d51041d960220390080c1c00050b0800000e1018a0603040c5a50310050361000d00d00b40740626240d00b40704150f142803c0c401e00c0c0c1d0203028450b15140411520014914501d04945081850041701b0340340d00540c2c420225032900c3d98466907a151003034100010a14021344007030741b200e28401070540a01070708003a4408140c42c158110707001e1140081a1025503d001700b2442c9561140240b2140b00d0f406030007a00c00900400d100100142d90301e01d012001c1d140500c0080605003012100c06080f550180c1c0624180901040301d445050740200e41042110400c81d0016141c900e207040d0490 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 543266717 1250 543265467 543265469
    0x1031e0213020a0314090109150608030a0804051203091506060a1704020d05062806050f191a0702031e060714070515040c151416050d020f0c0d0b0a0213 67
    0x10441120801b08029400c055005031920380c02400c2d2002d5580f041c2220300e040b10181d00401886070010410380c178000d4000c40c2c05980081c45031003190081c02d0700c41680c03907998006035658481c642280412800e4540d850b42d809800c0381086411501d08504500b014007403002c4d4107500030101c004140040c0940d9180040d00104507002000d8030258540240c02c191000d42144d0621841c00550000300300c07581c4148600d505031903001d441d9103200741d014420064012041c00801203c40445480818070302d10240c0a00c50f4102607001c180c1d142c041c5403040500b08075550b040700c100d065200402d004d001b4000908140c0110302420b001401c0443c0d4452500c031485492009005440341e02404c2210b8400000380505c154041d1800a40c040d440c2d2000644046100800400255880b4031032440d0340510002807107192040100300701c504203541e49150500004008800244c0c000f01c0100e44400300a001c44035000d40f04668807410a9001c0c1d581034402000076007603c200a90108403201740325120a1440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 543267967 1250 543266717 543266741
    0x1b0105100602060a1a0915100e0a06080c0304111201020406020120030f1b0c06010e010303090f03110f06040915030b0109091707030207051903060c090b07030f12020d0501031e0213020a03 82
    0x5031f040c010623005424a801004090700400040300e001030176034821104540942494880d091541d22591189114090004002e641c0240030782c0d0340300c081e403c00344003d000038071300d540000c12000071002100c020b0001c103c00c8020150010000c0260304541c0c50b03900c96005031101001c03041104519003486843c041c110640c5054410000017041c891408003d440c102c0348650b441d451442d071640d24191b02900140300003401c00d04549c60310340c0c013403400140e03859003850701414075801c0641d82c06000b03059494140c560072421600140c1481404515084540907101c2d00f13506200344112581c035481071400180352142401e402080b6042014404e001c00c100038a40146042094410b403001c3c83c3e96100da603c402c40e912842c022813a098580102c4140c402c4900c0c207400c0034181515a107040d65a01e0020500303404108e1000c00400e1590f1a92014060190294100140e01d6040d444d1014405070400352508858000044e181c0060b40c5510168000341401c1c2c00150f1035054000c0e044d8080c14200e1403070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 543269217 1250 543267967 543267979
    0xd0e160b0904231b0904050403050c06091b010315030b04080a081501080c22120c14030d1202070506180c04060e0c1b0105100602060a1a0915 62
    0x1540a01440503151060301142c04201c000e5001c40c0228442003c190b41510041030f080000e0301101c6000c1181c00b240620081c8a480c00c0540c100050440744112000c901082000c0758000b0108800c10180d94405c103030500a00c040710000d03603006500121001681c1c1055191040061002007910383c05009517807007009010203007814038081a0384d41204142800280c2c2c2a00050481c00450042010050041e110b56449845070a411800d950121040d10303c8040c03203a603d040214001d1449800600c21401100a40c415900e00746102807941d0703010a044182d09a030781c3c802507801040c0c0c503031002c54600b050080b00383c1c072039103900c0a4055000050b00a010707282c108001b812210400e00801140e03c8103031120300082e038007000201e50150240010f51445000080c1090302c5800c020404812041443d81d55464040a19400e40348200c2d8003910800108a0801559404209164000e1143c480a10209602246d58001100715404240c80f038250b4202241074106a0280c0e900c4501000d804 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 543270467 1250 543269217 543269219
    0xb03100908040602151b0a0c0b010f1d090312040c08030c0705150307080103060b030106030501112d0d09030915030e07120b0a0b1504380d0e16 63
    0x10600854200f4031a00016004650355600c001d2040c9004905c513018508020304154500d20014a017a00702c0440107007480410304800300824400943d050081004401041005040100c032061410800c2441350711502d10b001844245c1c1d9001c81a9002803050751500c00b17180c1d41e01c0c00d000e40201f0a507403020b96503000004090032441d1010401105598047d00d82400075428a00c0e0580144002c0b1003490009100500600005020f9009070148400081c00801c11545036190542107403500c0c807142c520624000b84080500e446100308040c629011191f103488840c400d51201081c1c0b164a100b00c2400e9520503c220030035000710b2181d0041c20076014003a103d0866500c014005003d00740c1c00c42801d1248000000d40d00c1c0e160300414107030581c400c070b4a2240d51501c0042c200a0510a0b42550344820f801c00c01d12000038400d4050001041c5a00440070f45500b1220814202180c0ca80e021981c00100a0701c42c40c21000e4200301c40c0000000b100005078400d09081c80c604005820388243d40d40c181c0c0f048 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 543271717 1250 543270467 543270473
    0xa0902010c020a0305030415050702032a060d09050f060f041b0b0309010c111b0d050a0f0302060a061d04080310091e0e0304031110030209131a030d02100b031009 71
    0x9001900c0d034803240c2c5103010022003016591230044ad10025855071081070b82203d1240098186018184a81c17582c004a0000c0760003c0d060340c01c0041c1c481c9a890752900a081401020401d8500b0440020f020303010605002140820703120300140080d010f80700c4017001c2204a034070302c401d2400405004082d10344078245040c4050180c8201070700c038400690b0650000900e420081602c01f1015a0b0f044480922000d000905c5078400c00180240e8080c09001d5000d0003141000900321245232103603016201c00c0c546142c10204941c0d440d0441090400c91007115890f104070440b4a0382c000307800404894803603850031110001c0069a03089040c120f400c16689080c0600d4200700d0140340c540b181d0b001e001007071a024026035039009900c00030745854a001084507181c1803210b50010207110a10303001d4600140329011555070002f070840d0b4001c19a90300060201c0d801e0003100c2c3d8030044011400350404481d20080255210340e002016040301b5901c03a51402c80b40e41c1004404411680707030000380034804140c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 543272967 1250 543271717 543271723
    0xc11030109030309030e1e130e01021602120a030c0803040f05160501020d1e0302070807170d0501050103091104022508190f020d1d060304140111120a0902010c020a0305 74
    0x7a0480214484440c120030a151552414001003c1034030000300c06c041f040100f113180c04803004020300d0345546040070000c0396000e0000b400d40c03840344400302080b64014414000810a20010100280c01403503a01c00045c0e80048501c1c4655041807816440e510345040217400c0c6084100700524038420b801503080c40103480069442214000d80949110490300d02c0d05841c0c1143d0f10702001280e88070000b01c10f0149000c1d5000d013641900802c1002d081c9013555503881045550b1041f02145206d0115040344807002c00c0c000e26014000a203014800b420b030590304d27044440344080a0511132500411502120b034070240000b83c0f420000255000510168188120181e1151403504607828485142c1c4035207901a140d000f0b05100d1301da0080000810708032048a8180c034070404500381d0100042081c40301d54030f00020314042c5004c2d08000418240710031b0b520382100c400c0c4c441010b5500c410700c90010386242c02c5400550001d010700700402c80001c240f0049450b11601070b0b0003503008162000c0030047c00000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 543274217 1250 543272967 543272981
    0x9040f0603060c03020901170a0608030c030301080c0a050303120912040314071509031b0f14030601290c0705040510090e0a080f18150901140c0d0c110301090303 71
    0x2d00b030070403a000310034104030141d104206009001c00c0b00c03050101c0399040403921503540800050400101c00d034803090081e0441d88684503100280d4400300051051110600030450031403821140034030901d1401010a0b00c0340140300105c1d0100c4040b00010301c075050203000c41824203400d515007030765898407403401c6920b101000c1c81c42c0ca124131403440089800d000d84416808589416155585032521b1561644a03d030645d652404200c2d0170b004000441d0b0400f03e040c08054000d00c07031400280030300b0105162510350140e104024040c0010300700d0026050b614000080f02c0c035060311955851040c0c070216440c00c00980c1c01150000e21740b40400611900902051081d104d0b601800c0c0040c0398a415001d586460480000d032080c1d2003001089003e4038440020040c4003e50201c0c00b60440c0c091000500480f180303010100180b1b00095070071540d47e88003d512816070802d055880c00c007003240600d02c0e5a4416401c0800510442c030b08020280592640298201c500040090021212030b26000b800340002d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 543275467 1250 543274217 543274223
    0xc03090e070e09090327060405060f131401030c0f050307050a0207031203140702030325030e0a0311070b0429040e040c0608060f0306040209070903020405100f0605180f010509040f0603 81
    0x201e946c03c0c8100009414060289070b1000300803900f05400c000c208069507000421041c44407104012049840d40301c80c159000404d001910000740b6101e0100150a0312024481c88041040c4035440410b01c43d080300035a90032048a1038490303100c6190180980c6412155080604070841075002014400d500d03030001460b030503031004105103907201c58009a82d44d010680b050581042d03400b03066808511180105019440b0f01d103408502c6a00483c60b45080820421003540015810034441103100340401c1038500504004000711300d090311b40903c0501d00c00182804004840c80440405402c20202c0305607000303003143e03450101441c01c00380751a2a402d440f6110340b40210b044040081c1092a2044200500ca80060058000c0b50b441d0b81c200000d40600030009010b00820380c00100150703c9610803075101d20501c8906044250030545c43c7d10f5070903210b502c0311003040300070404400c02e034407222000e940e0312106850490b0400020741c0140c2c0e0074000c0c200b40039000707441c080c3c1918400f10b00343c000c4d90481780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 543276717 1250 543275467 543275497
    0x8031b0c0303061203160305252a0303090b0c0c031c02060105151b070801390203041403010207020d05150a06080307030e1521070c03090e070e090903 66
    0x4c80c4000181c40340501d400540060f061940c1060209005100501c500300700720442c1c0d03100465503890700d5401c036010300c41583c1c14420226403200e00700e44181d240340544140e0b01003900a80c50742e503008001d000180541050302c0c102207503020083c0c03020803624003c0b4900a0079034002e203103208411110707111509081c00061265100000701420400440a014086003003080d00c1d05140780c510078582070011071031407060310581c44c000440a03002c1c86102c0303074178600007442c1401511b502000303400402024032101c01d410109110481d080d40000c1250200d4400000740041c03014800c00080c020f00604101941245a016040c02000701c00701c1c02034030b486154041c00820f40c9a8107841d104a400901403100c90394402c008000c007184c050240400c03421001080c0065400200700308a0f425008008009100c6420340c01c442210520110320345d900c80781c2440d015400003181e8030300420400c6240f041c0d440083c401000700f0b001d039206d03010b03504800102804803401804c20350311183d603a80c00004031050580c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 543277967 1250 543276717 543276739
    0x91506090605100318050d0908071a031303030b180a140603070b070f08070f1a0f151c1101030b03010209060a0311160b0604050a020703090308031b0c030306 69
    0xa5440c400e0000b5034502a01c61110401d092800381c00034007801c540300208101076100700000aa04210b840d80a484a03640c02e01124503000c3c1e2580b40c030225800c100ba03909052460131100c222403800b039a50040d48040003401c035203520308056000b00314441206070000c078071080381000d01c011342c01c2590040c402c01408026400e5081908100e444050301e046505412110301040480700840160108a0041c3c1c2c0010307024403103940d034083c02c0d80209001c0724a4003051414806200d0384404044440b800d001e5051140d10f0440801e4004840c028119540140c2000d041c0300d142e10b5003071040c208507203400348800a621039410840c29036469030005500280c02c1000342585424180260b0701034490241c8054100301221100341c01410641c0b00380c06610009100801682d440020440181c0d409841c00840740e007480302c20b110950700c1c01052198454010440800047c0c1d000304c0c940102c03030300029400e8a1303454001c4508800c80d0580f03244041150b020030b8540024038088000d40c01904200c032191051 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 543279217 1250 543277967 543277979
    0x90b09070f020c01030e070e011205010b090c2a0f0606030f0f030f09030f03040909050c010306030b131509051c1e030f091212060801110a030b0d0501091506 69
    0x710401c400441c01604511079890303041d40a504060380030802c50302502e00d65511042107220b860780c01d80c050701610800d4942c601c00c2c010280704da07201080d010795412113149442d01c11340e4001e100700b8504040ca558000401d2244224408c1419002c409450984001807241c41141350b1300d4034251030f000d1190240e510381084120000a107130341d43d40b0450700038509064500910b0040c980001e4500f6806000309015060400b40a1008101034492650000f50300600e1b82481481c000380300e1211414180f038040d0900c0400d01c03c040f41c03075201408510241c2c1802d068a040401d0104001c4000855800c00c84028204400460204a600282c040601413000030070b001b2940c54001040301d84540103094040b10b80c49100c1d4001d0301c809065100b020914030382961b20250030b081c13804004c90019043d0041e240e032140b1300703024803001450749600a01920802d1040441c4c00d21a210281080c15520869441da9840b02d602041c44503810200820440003241000c410b85102e10b220104511301e13222012030a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 543280467 1250 543279217 543279227
    0x9010509070812030a140f09060f041e060f020d0623060313050a020619021009151e0f050402090a050907050d1a0a0b01030606030b03210f04090b0907 66
    0x1c44442c6001410204000c0003030700550350000c0c00d84203c60f510b03030700c140040c20340000703c035400342d50300c807000c0c803070701e192030000a800c0140103003030910302c0b444100a02004c80c2ca00c0e00f141010036000e200d4600c8241e0b1901c0d00c0d1009108040d428480e940c00801c80d034443d41140e51004040f140c51280070f040a002001a10020341752412099911074028408684141c07914a8004500392003081119101507480d00098204d030032401020140444d48510110003d505004080e8007100c5120248820b95540e9542090b12645c440d64401090f0340703126400e40d42c01e4142c80004032624803501002128200c0031310307901420040310280d0040121501040310820703184103a521a1403400301510030f040c1005d08000303a80201027410f440e405c4100d507442d00085c0401c9240c0e405000b00210018601004400140c00c4d038405034008002e140c83c184410343d250300c010826440080131120007094003104801815954024a40e0101080a0202c0c01250704602c591021441d8401200d140701250780713401d4100c907 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 543281717 1250 543280467 543280469
    0x210103050c0102191e140f06070e0303090d1103010207021903030212071505072006010303230f09040e03040f053d0905030f1f050601080403110102041802030901050907 74
    0xc07030a602c80740129081c10185c079a1000d814801c00c070404e620314454404910b0000c13034800c0380780c05030041404c0c880e01a4000300d54440d20142030b1301031802c201d41040020129114200068206404010007410565080d0b04440e40c647d8010300262007605610a0024803142600084025215980348080c07402001d400f035603c0c80d54082640c69180403900c0c1004042d00000d8810010712007450000c03040c1f40c0764405100d41441d405001803d8079803550034010300c0b240c10701c50080a40051024a10f0f03214081100f103c00e9040c44006030313542d40d6a10760210f80200341c9a495000342c0e00012802244d901c0307441c003007081201c10407200b14241025222004400922003140c113154044040c502380785502c40d010780045000d6060400d80d14069030b0303602181c01c04603041981c16480d00640d16200f4003220007098507035041104801000b44d40f5241c00064040d60300035002500b8040400e4640303528000035011134014040c0a5200000b815000124034080e4100341d400c2c18440d400c1c0310029030841400070f442c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 543282967 1250 543281717 543281723
    0x1707051905090406090e0c0a09180215040e0f090d18050d030e0a06050c010509060f0c072609010e090c160c0e0403021c0309030212210103050c010219 66
    0x201444420316001d07107a907444228401c0c0c0050301c90310b00080c8013046200e4507041c80540e034080c1c10391540f84001c015900718250000313100546480600000003a04082d124003041d4182c403e0201d04101c800800954091a400510b0404c0200c04000e40804a082094090010b07042128100c4801a8060b40c0d21102001708450780c0c12600b00404c03452030300205030140c040c00b80c103201d1307440300400c070101d000340e03003250000808030f42c00043c66405140e0034450300b1b510411020152145050010078a0300b92840076021034120303100403841070144050700070b40581546140b6051031b40800803200108407074000500d0035000c2021044222200e0400d04403503845003d943e400c0c0d614000c000700c9802d05142041d00706030354441c0a1880807403110043e28101e030242e8041d80040441720604100c04015200b102118000c00d410a140907000030380019101c1082440482c0b0a0f0b103481070301c482228000c48105042d0480c6078284000428030a000c41c181d40700b008280c1c20340d14101c008000f00160f401510380d0003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 543284217 1250 543282967 543282997
    0x1030b09250f14030a1e231905061203030a0c080702060907150c02061215030d05071e050d0e04050901020c0703080f0403021806030c01030506031e011b170705 70
    0x300300540a403d00035948507210b81400248244100f02038220101c401d008903081e07581e24a04802e0160100442030490784124861020500d07080e90406100403110120910094072032001c9601c075a600180700c44000031003000c49480749441c0d40c81340003078500301c400280480c3c00c40c404115101d1000c5500c510402000d0000c0c150189007aa52580302c1034001e007071000b005041c1100c071006a440c00028492240c42c0c0624060303605040040594000754911502d10943c405420040380a80120a0300c40080e009135940304040101c109081c11080c507440010709030b0040e0508507050580100110340c2046003500d04000315510190110300303d100b0030b40e01c42c1244e40014410030011340f40c60002c0280700030281d01d10342001e0b601d071301043d000d04850b103051881030020010440d06003401c210340300c41d095007440d05100fa03040543c0420b0b03d8180301c5817145010312041815005954007500701125405105035060105e9051030002468406000020b003180c1d0309680102c1d5211344240182c036117580c1c081c041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 543285467 1250 543284217 543284237
    0x4020f33070341040f12020328060204080604060b0a0807140a0906060203190c0803130c030203190204050f010f05010c0501180c03020f0102010606140901030b09250f 73
    0x42c02d0b00c40c261070300d04816010b554200c80118024800300e0341401c8007400400c00e45032410101917409441880d00030103080d0301c0c5c058401c00076940c0010188a606882034050a0081e800d05040880003c1c0c42e0000d84031070300004000a100700000340f8a80720b54000c4408000c64031040b003c01c07540d50301c58851020540c1c00f07460240031034030040e003000741b00700401070440c1c82c0c070340d681d100c0701050f58000c0c0d0098002d6040401c0c0d1140070070300c5010400c0703130324150700d01350f5000c920a503a981d04900026010380c4804841d080f03a90100881d4446040c0a50380003805c071205550b0320b112040394481248070490290f418800440e0810808000c15030507540060032801c821070a02004403038154072001c06954940d01d039602e05014100071fa02c0b07001c1550251a1482e461411801441261140749682c81d045a24104040081d15402040c01a000c8411b2103242d9035100d1207001280507040701e1b070f2600d43c04034a80c4140f03c010b4004030003000c1c0c0380c0d03164840c01840600311301007920140f220100420128401d002 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 543286717 1250 543285467 543285497
    0x3160302060f1612320409020f0705060405071706041a041b03030e0411030712181703011a1905130b03041b150509060304020f330703 59
    0x19001d00d05a480f081c5104401d00d0710348164000d40980d0300d60102d851034001c0b080200e404c003140255480805143e4201d01428244141c05202d01d214401480340e000c00c1d07210306e06440e00c003241c0c0c0903a00030303045803120304150401a0315131169103d04203185c13800f80c643c03c03520f00020490500c156081403490700210b21030400d44660441c0107108031250782c5228103181c100002c00d82d00001942c0281e40d0315030300245d0403090004940c0c0403807d40850000501c200060300340d010014001c6080c00e0000440c40e26042c00c0740d10b0a5a0550b0741c0146010008051001040000c1000c2c50482d003000c00000380c046251400c03c44503100d0701c609025034555109039000110702070380c0101080000c03640784502250f640c04c001d550b01e400507101103070a046070412410181840d40c0e100c2c400b500142c05107403d91103001c02d01070400d115258986000f040b01000240c25580c8000f1001c04011010344040b018843c480050013480300041c4032000c5807680d049000e402500c40809803001c00c0e5040e107912a440360040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 543287967 1250 543286717 543286747
    0xf0a0602250806070207060201050a0536070b07020f0f03030a1d060301231e010804060b03030a09060206150120070302100c033c02070518060316030206 67
    0x41061445079201e00001120709080100b42e10401d100e80c0a0044c550502c44000d0070b54001402100e11141060280800c00880301c64001b400c45002581070810b05a61a00e02e0010050381d807041510f002e20b210009842d03010700001e05001d0b01c00c0b64080c45d031010503800c10100b21062050243c2542c810701071010407070301075020100c281114030110b80702c0d584410000340a5034000d80040381940f0f000a03002e1603030000e4651141c983c140c100c80c5900400010000080303032803401203070340e410440c0e900046003c1c00000c0c2e0005404000180c01c0e240d45a801c8840901031303803030720b00c81d0a005204007400503a880001404500710000140e66491081064409503882103200c404400018040c10a00000581e10345e01c041c240900b198a0b0f1480d078460f81c1c01c001d80b45010843e06070283d09940c00c0301c51100c03480d00f10426501100e48400c0582145210f030304a142c10056002580c00580325044e80c2040300301c10a44900c9050200e0440e10011040d030500b1900c9220b40c40000d401407010711107201c00c59011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 543289217 1250 543287967 543288013
    0x708031308070204020a091d060f010c030e0307031209080102090f15130905100b041404020c0a0c240c030e0907030f091103010c051201050f0f060c0c0f0a0602 70
    0x2404403281015600d0f0005800c030381c024051100450702c0d840c0d0410491041c00441404200c1c981c1039a806c07844c04602081021031501ca4031344c108503680b6070032000c05026002c20074008102a0407214880d48a2500b49000c4104c16840d00c00b00385c03415400a4404e00500032541020409084801d0351401d560510842c0070050000d58904001804040c0c0f01c41c00c58590300300140350743c0e00003040030700b41a218085401c4080d00800807407142004140a28a90f070160120701d594159001030303403144007100c3c07542000720a440080080c04c00307070320001d070317102d0300481003c8800200210000003000e004c50036152141c4211f030040100e00013162200540ca0590801c2e40c3c4428282004903100c0c01c100c4114045442d204000c80741242012594505410240301d117807104485814910700c2e000108440b00030302c100500c5124410144402210700c0b68803202044203008501030f2900383c4070210700031456210b072a407242950061a080b102c48107035242c40011101194460740190090111a000300a01da8240b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 543290467 1250 543289217 543289223
    0x507060c0f12080a1a030303130620180f302a0103200f2a0d05040b04030605060301020c070305100c050724110a111207080313 56
    0x41e0740303010106004080c007a0940d0300c81e0740c0d00c140610309100598101d40845190003c098101c00014000f500c0000840350020161240c402d0080002e1621402030b021079515106102c01d403400d17187c42c40c11a000545250003803001c407000d90755452400d0201a005a001c0a0303804a002000c00c2220300c4905280301e04850b41d03003e01e2900022641940f0716008484801507c820141102d0480d440c03252528914481001d01c0c0c00d2065000c00348120741250164010322000b0400080d81d40300b0204520115481824070511111445105c0749060030406540440c80a09000742d201c0d80389403c0c418400c450a984001d000c4504003800d688030b800c0100030013004180c05d50341c01c001c8401045001c11418000314480c81c01032031040401090101a104807a050405000c000d00074040011003900c60740001c08903100b81810004018003402001d00420500006010800a800211541d01c80c0701c2404202099040f1391410100d80081c442901c1341c040b0240071ba190500200703066103c204031000441d40 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 543291717 1250 543290467 543290483
    0x27090c09050a1404030c052e11040e01030318080a030c05010507020a05030d0c0905092e0b0915090d05030309010606020a0b042901080c090112020d081b07080c0405090303040507060c 80
    0x14420103480b0050407203d051640c04120a45088c003510080e00908003440d5512075014203080c034103040851a000180801030501540ba11904d004008010780702d401821810110b40c03000099050241103440d60f010306894035401c1100050801d400012852a120f81c000300542c070f4038100d0b0030801d00070320200d11800108200c2080028407552201606401500824050580109000201240880d0f1100001640580e0400c20400221110140c4503440401c0e9008130300d180d00c61014403c00c2c8203c8404035448200d070100381e02400340001c0618441c0c076a2500800c1101e8941005036550300b50008010300d40e40300400000c0c0091043c0f2a40343c1e1352121b1201e800c4465010b0388407041d48901c241c00004299120340c2410340b140c5030034000c1600501c010131040340e2003c4560041174444030f0f60b2502030301040300081e4880799051110112420354070240161034605403181c00c0240c96008202c0301611417428503000c43c01c80000030040703d00640c0d100004022084c58800142c031346112664041d50200 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 543292967 1250 543291717 543291733
    0x6010f11010e0a050f0c09090a02041d061f1a030105061602060f13060e01050a0e0105090307090b3f03070804060c140d050427090c09050a1404030c05 66
    0x40030400c41e0300b040c3c1301d40013500d8200c031503100c03c0c0c0c6031100202c10184030307240c032100780f1a1100b00443c00100d441d8040d074000c07442044041d100b02451120003e40c0c0168810350b01002840503000e85105250b04d8140300344180c0d00d9882d0402c0c01ca004142e802c0c2080c400003000100440d00d41500100044070703120411030f803c80d401c2d030000b0300c66411107100038689a6002480c080e500c0d00041c1c512028100b01e0601d01c04120311000000d1450141c2150341c4184016403a00d00b40c280c0c080c3c0107591607820020102c0d98110f8640038580d001c1e06a0000c0c0c1401200080e550628a010341d183c82821000040350440480204900da2401c5880c841c04140940c0802c01c2543d0200b0100e800070000b43c505910381d451107050700d20745441032184c0c80c010b500e81c0c1d800c8196172440c01c5501008403021504e0302c03c0240c1c40c0c001030301c850380c0750711140c00103d403122441c0001b04000c02c9101100790f0300310703042500200325035030b1800003c000b6181d01c100700b100c1c05a100310000340021700541680c120b440c0604d00700c540403 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 543294217 1250 543292967 543292991
    0x1213090218041d010c030c050a0302130302091305010b040c050a0804290103020906120c0f0303160b180d020c0103051f03031e0c0f08070215040b030118020306010f1101 74
    0x303800c400304811209410054000200e6400d0040948990703946c40c0800c05080399240052a84c000c00c40140205a0005102000904103800071006540c0081203881d8600700442d40301c015142c03903442110103500300001c0310401c2c5407510842c000d0404903120b40d45024580c2ca070071030301d40070000c008984014002501c04440407400c25006c1d10011034030301d0b45c95a941107004100c04440c00404591090a5401d8001d40c02c4001107503800104d04c050315901e0710940c2d5080000d00790b000c0e214000c0c44804d012100f440a03c0141040305001c0c02003150b4000d540880e000c071745a20345140f81c41407005644072041c070310a554030941c41181c1c80289103003030910040c004190303012200481e5105400040c11000702c241920300409200840d0070450070a03481840140d51070102c040d000c002c002d04010b0f000300d640419074481240c102004008071007820340d11511040c5003046034000703002d5002a07052803021443d941400d4800c0303e001c1c0d1816100d440003008552011600804280034070149075403100120511 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 543295467 1250 543294217 543294221
    0x623010c170d150503010902150a02030904020f120603060c180a15020d0201180f080c01021201170d0914091f0905060f0a3c0303080702121309021804 66
    0x2c4004004a42460350120052114005800c018801e9240c031014100503622500c1100420b01c02c3c02005440b087d80200c1a41540182d1584923002400001c00c1d01013401c075100103105040540e800040c3c2d81e140c54041c19500c0303108a54070841130004000710030920480c8004801500f0000b00b06883d403985680c0700c142c0e000140d50312036001d644840701880d2095021f00a05421101c60003c803400100c46445109400740d04074005400f00b0780004103070050890030b4045420030f10f046011156103594880c1c130441c0c26644c8520202940c002d000f40021428403420680c41140c00407000c41c0010441282080365401000c0c2c0f141100b80c5c0040350684006020302040c00c02011985c0000816240c10818404883c0076444454803401c0ea200c0e0611249054480014a0a00c1010b100280d150352180104011110700190461081e60220020415a1014000340f0038030069003550300d40304140170440750794000e8107411460065040c009019509842c0d02519040402a1011842502802c04581 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 543296717 1250 543295467 543295477
    0x1407060912052a070608040f0204050c030a0c050708040504180209010b18040605100804060e03030f18010501080c0d1a090c19030b01140d050f010f0623010c17 70
    0x4188003182210f50f050420f01144141492842240d4282080d540480c0e15071007540108800c0c01400c802241c00e1180b0043c00700074803a4083c00400c21030500b101f1801240e0803c80b1602c84460500d0700f0040190701c900245c40c0e990b941711150a08107820a41040060020440d01043c0306450013055000f590324201d189000303014401590390703206008503a202002045202581c051404c00c80100400d4172000c0c40180011520324104d10280c66505d4100f000d04130f0f4514090643c8000310501c01c0d0780807070440c250302491044980c0d00c2e480e800c1ca12005d0a9175824840d100d0f06802015092240b41454284d040350240314068a5100210343c0f101b105585c00d080d01ca440203070303011111407541400d0074503004800000506108000da132559a5400c0500014050040907110b032030b00c0084a500c03403458545425510005640800002c0c54000f0300034101a1715800c034042c00d00c23000017002c484040001600115003140718034071440740001036a907451401c0003120741c250b0b2103c402c0702c0180c280001d8a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 543297967 1250 543296717 543296753
    0x5040c030f110c1b0901090c02100c0f0e12100b01021624022a0f090a09021918050601110a030203040e01090c020a020d060e1509190314070609 63
    0x66200c042c1500c202d4502420f001144014540c101c422004a60301c0c5c2020038110b940c03046010402003064902282094820241150100d04006100007440d8000820b0101074807280d442c02c41000c01c00040207940040404130b141c041d008041c07105800307200e1360441c0440103c1801105c0071010414110281480c060740075079141c4034410070703010a00c9000038040d0f40c40032192002b003c0252000301480201d120381000400000f4004400c03203a10b486800c2910407069004040344110714180399204042d000c4610100e1252044002c281200305203081242c0643ea030360072140c141d5518010410000306400361941d03061203c10111914000002c01c4203000041c42540903548862800c54408840345040c1c001150711414440c841a04035400104695204e8046070945265049170401c000100944400f4081c0d0f806800352100351b400d48008440e00400381d080448519880008150311003440000b0020300054540071014100c0c80040c02601859004400c0050805100c0e40d850680c90301e405588 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 543299217 1250 543297967 543298001
    0x20f0408060f07020f15130b15010807090819060f0603140115120803061203032802090108060108100509010314060f07020706031509060609170c090105040c030f 71
    0x144604400c0241d075040f80f0380340010503d4400402105403942d40004d05c0e5901501c2400001e00c40c640c0e40e0180003090f5070410421242070400320741403000c3c1c0440e0460382d40455505d038041441c441c401c81d003010032030365070764040c01001d40d081c80d0607515860101400d4590f552108180d8408419901c25440294070038150181800d408980c1d00d82520034402a0044c2a02e410a080102015407040303c003a4a502c80c00d240d540b540c407a00010500320103400251513901c03000c020403006005054209003518440109084480903011003042644150030031240000e0407040480d243d540a040841d8004a1020758120b1040e15070000c1884c0c15000d034000e50751401a10700328a00035009000c2241c1000300343c4200006880d001402235541d0b0100c1c800c1c1c100309955000264021034962400202504541206029403903613044020701c081424020594024010f03082e0310590000000c0107252108c0151201880b40e00e440c1c01c010090141c08284011b260301c99142d400c0503012845600c2051172a5896 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 543300467 1250 543299217 543299221
    0x30f0f07050f01060302130209060307030b220b01270b09030f0109060911030a2004060f0f0302101e1d0303070c03170a02030d09060905120a03180f02010e0301020f040806 75
    0x10045002c00d00c407c130100c07603841081944015115003003201ea108980e410041020034002001c503018145201c07200220102c640c0940b40f14107003a40010b004054241e8901082409500404c510301101645c400920701c2e10804c10003940740c2a4001d002604802025100203083d0a0152805d440c1545401c13a0815651085d40c0c5c00c1000d507622a6014100c10340c0200686034050b13856801a00d600c014124039140003c104a02542e529000f0501a158244403481044c1c2d1f03800c2c0030648480d403800304130b04c40c0f00d4062142080354820030100c0c40305003140d80010105480000d00f5a001c00503240d4a00b02c41e421711500003810b444c10001480a103208100401600c0c1c075504041d0b0101c1c034010180e10181008001c108202c0387d0020507200c068203210000610b070003075442c01000600b030b41c0c1401070260040c1f0f480a0f104001c04000b0701041010b0751002d00128030081902d20102800080040100c8802c81c0c3d0240076520500c032078140d00c14081c000603c1c0001c80710752565150071a07482114281d1191003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 543301717 1250 543300467 543300469
    0x3091014030f101d151c110405060402031e07030213140a0503011803032f0c0c03070308030103150f0513020312070b010330030203070809060108030f0f07050f01060302 74
    0x4828010b014101c200745944d00c400042d01a40740c0041d081220038156071007048001e1b80c0760a41220080e54029400760800c0140c135110383c1c441490000e5510841c94080014000d05080c0200c92048041002807050340509074455204004060036040400d40e0912a000921072400302c240050290070f0f00031102e59a20008000c284103164110381d0080e4141030b00d40c4076400e500700d401e003204d0307515043c040340210008103084403907211415000e503942030001010038840204001440a13101e0bc20039950802e200a040c1560348a09110080000004200405c04241880450080524040d0001c00c45124140d0b61805403403003a5018a01d01d5030a8101804600c1c04202c0344c0440c040017042e80d4140b83c020385a04141800502c0080d100a417240c4442408200900003202c819100e40081441203e0480d002402508120f82d040045512140810080440012070310f04032202c0000862504000480300700b090340155400b440d84500900c16079000400a001840855407030000000300030349580 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 543302967 1250 543301717 543301741
    0xf05100e06030f062404061e0801020c03040315090b0f0601260a090c0f060309110f0d060b030708102307020705190915031104020c03091014030f 64
    0x5406103100758820f5245a0281d0000700350345500540e03032a1920a801e02d90543c0b92060700c1121445503001d4a010b41c08100c0341a86403c40565051403428440e0550320b0315091801c170b1003080c176481490b61060200700000389061031009400940900082a0000346540e01007035410b050f0780c2c0550043c402d00c1008181c3d40d120f1208220407401041c0e01c4504104d0a0142d40f1000c030140c4a1000c49440303164810030702600c403c242000741402000041e41a640e01401030041400c900f0840b0002061911500b49240c000344031307001001f00810000c0d03103031044e41d1104020300030580b0058160040040010310240c2c20300000c51080b805210104d4a003100e00d43c41c005911551056420141e801020300800d242d001030607206948007566104410003131240c0c2041030180c59880304d0400e600f07000f811414540f0401c041011684641803407480074800e00d00b004160b0054020070103d9a10912005601b40f406005603065000d035070400440c0358a030641c0e91051544111444490054460240403400c2061 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 543304217 1250 543302967 543302971
    0xf0e010c03092f0609060f0f04050a0906051320070503090a09090804030b250c0c0b0301060507021314090703031706060d0e0717151e07050d0f05100e 66
    0x30900911a034602031003034540071500a90483d004a03004102c80e0b0440d01c4070300441c2d0540c5440d51415031148c0c6e0b1481010f100340d10a0040900401c81e0ba20000754010040c040c0c2d00170b841d03004060300441c0c9621014000106101120107440d141c0c00c69244400c0416600102074690080c0c02560742d40e1110400e21416072143d0303202e54281880d10300b01002240765542501c0c1036903071000c0e1002041d100e01212080c0108440d0110040d0f4032442c0b8414002a0090901d00c942c5226134800e8208036034502c9801d02c9800300f40300e080041078080101030010319280c0e0b5800b1203905458000185ea550007052000501002c407100c050640c0300c05014024950003ca458042000201c003c0d0900d03d00040421000e0040103450851251680c0602c07048120a104010140103015500810f035100120b580f540c0b041c80c00fa590388203c10840c0030480100e0700d54410421803030001c400c0340d2940c40e0f1250480d43c1b40c1c03114030645039860340d9240074441e4021b07500403035000300c6854049929250034400d207280c6200c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 543305467 1250 543304217 543304253
    0x103060e0907121a130302010507020706080c070206072a152f1002040f060302070503180604030b09030301091413021e09180111070309090f0e010c0309 67
    0x28a04000c0c0d1210000381c4031081d1001e640f00418264000c4c644150701d00a400210200510381c0300c108503c0310f1034402c2c0003081900a500a10154645103816a250361560051b13100160003000098214080d2800030007040d8406072015142c0b030101e8130b030340c4400045e002035107070400320b9005441c5a800d50013400300301802074929040018103c0540142c80d140189102c603c408040c2c56003c0c030b04002c002c01e00c0425031052001d540b4008488003410009500c640a954080000c901010071294868803d41e040c05900c50011464040000c01d02c1008280d0245d81c6644000100000f000140302c2003142401514100e00440d100c0d4107001085054460a043c18061424904c0030070114030044d58071402d06540665541c0b4160700d800e0604c400e248400e0718090303000f400c008180300343c0c250a01d100321308000c84100200000c02d0301c40790300b050714458681c0260004142490030302c0a2411a070120009054154000541513600b5160600b9201c40d2071800000c241c0d280703920700501080201550740c41075 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 543306717 1250 543305467 543305489
    0x5120f10050616021521180705030a06240f0303021b0117071e05070224030c0d090f060c08010b0f040323031329030c090415090605010306 61
    0x3e081c1201c0715120314003840c064410303502d030000b03103209455610848424000800201c8450f5810f420310002c0108280c1e04030746078100c050200d1410000c0421030310f0070f5807802009410b40814035284c400c080c0044503400040011a500241d050004022401c002000f110f03203008901d40c91402d001e070905581c18608220168000001c0c0c4940c0e90211404555840c0b004480949441d015011901124240c0040070b0f075541002c5411070040d040303000345c00d20602c00c0710b04098641e001c080100010b5103d504201d60b03800300b400071404c100c440340c010b80304280441c036001904158a4070340c0404180003000513a03206607202c040d0180d00e40e1080c01030380507014414625240c0501510007207224800ca10018000c0b811840f0405000b8004640030540c40000c03100322070322a040e228481211080314401c0750256800c0030010417161012820f03009032102003006150840e0f50700f08403801658044205c0607441686c0c0d0321190300c8480319081e1040a842003d0300003030500c2c1440d0014003100e0b400d40056035405 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 543307967 1250 543306717 543306727
    0x1404120e09061c0804060e120c0303250210091806080d050c03040f03061b030912081503060c0306120106051309020d080703020c101112030705120f100506 68
    0x80c0303800841c03940042094a0300c01c3c3e07030040c88421040003040114001d000f400002800a9034541c01503042d080c0020880d4000050719000c1030440d901c100c0b113216107400d6041030240c520402d440080c1d802c01c855406920b0035004c0310030b500042c0b12108201d407201c0401e40301c610602054180024201055402c03a41c208105403c080d0040e5070742c505c0c041d0034070402400080c6030662a60520035103004081d103a5000b46c9c0562240740103005428070b41507c1c094a060940c09600b010712900942c504140c2200541c40d0038080c81d40c040b100c91100030702a43d82c40107050244822a28100183c034800c0d041d85032100d032607040407c10040d85840c0c480c0c010110b6130500105001d02d65502000c3c8900030f0103210000307040003c51000c100010810007014190441c08103940090680110361a802d005e070880d00ca01e03807048071400a840585058245003c00d81c0070701031024000c16007000464026105003003841c1410300440d8401c46520041350140382c0300300e0300d20622a1006040c0211405850101d600c24100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 543309217 1250 543307967 543307969
    0x24050a0c021515091603052a0d0b030d02070321080109270602040306050f010b0a0e0402091201090b100b0a21060b03060f060313020f0609041404120e 66
    0x15203121000003100041001c041000f01d520b01000240f0044080c190020501e40348145203000d0b8540da100d8400329040c10b00080b8010072000306c0c3d0503502d08011b0002406d02c0d040c3c0e88918140c01074001d9078a42951050b54460f150340c06c1280c500c0000c8541e0003803801500718a0080300300380500340e1902080429043c0c070403a16800c01d400905407601d07440001050048966030880221641460840700b4920780000420700c04250010720a80c2d029101c240300135141e910342e041800200b4890200c86280a000c43d24000d4403030541c00450000c021b00c09810310031140005800348072090303d01d4445a54407082202040100110181e00c59010000340c405d491804151070a107200c1c003441501000b11103030000c01c001609040500c54402c1c1d180041110700c0d110105080706520640d03c06105280c2c0e65a205418500705040741d104156600341800c403070015500348140c0c62112204180d0052040c010540ba40e01c46102d2a0148010f08007450446d00382800e1500070402c048101c0c00030851802914511 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 543310467 1250 543309217 543309223
    0xc01030204260a0209040812010b0a050702060a02011e0b040f1a01110f030a120b0409050d0c03090b0c0606120f061611010606030617030c070b0c03040324050a0c02 72
    0x40c078055202c040d0b52000d064080b810100f55420007075006a4440c280828051003d019024007a02c0780800116641c03101c0d1990305d80d0044626620000350b00300f08800c01420302078017608060020f800042915128444416150035584130042021641d615044000785051300500c003014040300020010700c0b0403500780c00d070806100c44031b060500c09440701003010150100700d5042114006002e40381c44008050300107090003030480307003050b07503d0422106841c14941403040c14241070307103c3d0003000080b24100b402e8074803016546041c0c090008010380010b1412410380100940079484000d000145040c0c0c003000105400707802003443c15403004500e82c1c0080360004d501c0b90401c000760002004520006400c584424035010056025403c1c1500000da140e0181c00010955224202c0c0355030060009130859582d005280c0e299404c0d50000c40c007009000046d2004024104428003502d1400e178880d10f51000005001c1226a0b040034000c4c81d25409260780d1140d82c1c4c00c042000c0c07043c00700e44a10200295 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 543311717 1250 543310467 543310499
    0xb0904020901092304110111030901081602031b010b01170127020c0115030507090e100209010905150d05010e01060f0809190b090f0303010b0f1c1a030c01030204 71
    0x55540e441050201e1400c01048007080084c0c0c80105511910f4546002c02c000501d50401030702064084480c1da514607070210503a1101041079444c40020f5a80e01403c001418110080b502940020070152000345102c54018400034001000420086007210004044194070041d81840507000d50050200b24400c580384108440c120b68840c0408501485c200024480d8141c203105942c40d1940020f0007140c440710300d000b1130340280d098422041d0340d0b01d10b0704240c4404032000102604401800c40701e46070329501034404000185003904003182c6410114841040201c0e00702700c00c0c203000c03480c000d20f08418091140580302500c41011035500d00813024160b0714001610314240f1900c0000030b15142c00c00c1080760040a00c1c10706902602120742026903800c3c90540b20240180203441c1c0108040c44000100d03812145d0f00e00c007891030030302c083d50228407540040425600440304441e0500010303105009002214154062000e441c0365400c1c2014507003600b004c90035050500502003080348200c04c1c030705aa = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 543312967 1250 543311717 543311729
    0x220f06200609070603021e07060902010e010513091d1e0106140609130b130204060e06040f181506030f0e0d0e0409020303070c09020a090614041a0d09080d0b0904020901 74
    0xd0380740d00a01861141e0030700c000c1c0001d00c448001088000c00d0020981010580340e000337880b108002d8494200445051207280204e01c5668024801003116014551100c400700842503401204152240e44544c104003840c2006005400c2c01c201d8508520030030702c2410014501d009035189041080c4007c02c403540140200e40c0e1096009180080c0e40710f4240e0043d00541c4001000000841c40c203a070b4103402900140280300000b280e81c0c0350b2403a5424814200e800340d80c414540c11203124502320681c100203117042503030307000283c030f034a80e055600b44c074400c501000c0c00c45600d001c20f000344407524010456000004029499000d203081c00c48998000c50b0420900200b55800b06085503a400401d2039480b030000300034010913030f607200020701c1c1d1080e501801070081c071a03640e00c15003580e030703042129101c118111000e030307544c42000204040c0b44803407140c060250094412a00f45081c1ea44144111105d24100b0b881502002aa5480450302c0303104032407d546080701c3c085903074203094002c0b6141d044d05021b10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 543314217 1250 543312967 543312971
    0x30103030c170c0d02010203150f03100504031106040f1e11060309070f030803041406010e010b13260706020f060a1104030206030406020c120f220f06200609070603 72
    0x4882c00150000700d40703490622804a5000301d03103814009000354030440340403404003041032049030681380200340c03004d030300341c005005104900440c4110001084050300032014020b1401181092490501c24288198003800210941f0406030414058040c0803040c40b540c1039141c601c400c030008403450918400c00c207081c3c032299202d80d038401140d490841d103a00b140a42980e1400008100609980210302c08d51241c40101e202c494090070140e61102c007070160000040c0c4060052180440360000307890070506100550346029a1114014900c00c90800c0301c0303c4c8640f120480200220b000c004010040c00c4501c000c080210340e0101082e1a00c03000b070314140c80d0342d859040310401d44c0011400e4902540d00200150781e207040ca890030000a500c000c202007400d01600c0c8e40f05d5440d00303050040e200e00303080e440c1900d4502030240901c00481040d01385405411801c94502003035406544000f20054800341e1240a0700d50040c851001404400340e4060166034804010002c0d500008540141121514100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 543315467 1250 543314217 543314243
    0x7050a060e0309130b031006120f0f020a1508101d0903190c12080c0906070204090618020f0901060903020603100509042901030206160212010e1c05030103030c 70
    0xc0e40d8110f11030b115440c2d42c4184204480c4100c281c6a92181307407a16422412144080146001041519080d124000e1803120150100000c60300081c103400c90309120351002c0c0d40141c0550b00103040710400380c1040c0d8003602c005004840d030365000180b1541101c04030902c500300303610f232495030040441c0f42c500c4080321000e81400f2404d03640e420000c6d44c03c032040c8803155025001d04840c00509401900c3c001b614120807405080c9034050141600a018090500c484d618241d482424885641e001034070403070300280c0c0c80e4400c031b02150f21845064520303802600c4c4041031039400e004215202d881d812080f0301c54204a80100101074103c012001207950503079445840e0394400d85056500401340d40000d820403031803c1003004104d002240c07143c00c1c0454000c104050014912104040356003400000d402c40300802215034100b2280030550b04043c0f0003045080078001d10241103094a20b15400c468999006001541c031034151104940c0d4090000d00e4002c1c05c1d9851914010a2500001005443c1e1110802 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 543316717 1250 543315467 543315491
    0x2040c030e0309040f0b0a12210815010507020d05062409060409030908120306011706130e0f010f020c060106050a0c0209130827030706050d0b0301091709011407050a06 74
    0x103405031b441c0080201140540c3c4003c8501605410401201ca19002141c100f020340e60281c6900c0d8030891595070400c0f25034800c0821001006200b6815062003020310250340140e841c0444404110f00c9071002d03007a542496109421090001c0d1190b08030350004001c881a60b8460900031540200d040f80c1c04a00003143e070034155043d02a60700a500540510400443c07181e600d03200a6002d1300080e645c481e14610711244029070904107071250380d0b000300c01c50801021214950010442d490401c0300b03490840709007021860031980c0c000c0071203100a401040c10484040144041401000182003981c90400710803c028688180d4090080c8500507804c00b14100058035010480b0715944008000e545104000310101090015801c200e0001c018031018035090501080400845855840c0e20b410b010b815014400034010014080d0f80540d695203641002c00e500c09642c44409500c407014981c1c50300410700040c00704024011441302c1c20400c00c4080c00160000400c040c00a402c00310014290f00420 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 543317967 1250 543316717 543316721
    0x60f04020a0308210f01061b03050408010606081506030c1615060e090105010f060c03030e010b0a1d0106030618180501050a1406030c030307240c0c02040c030e0309040f 74
    0x1030400380c01040e010601001d016142c00c0c40e0030130150b502183c070b01a0707558410701c0040340409006080c00150f0909011101c10424140502030a105c2c2c1072003400c2c251502c0c0000e0844a0950006000038412424000c68800c041c4a6041004043c0e48052031890410345030342141c41034007000c80d8503241e0841070b90b0034800080e403400404010b40505005081ea80d4031050070140c0144c030107034255440d00e000054050195411101100c41c1c5440d04010380c1480e4406034010070700345203200d0a039520b400944010740d480242e158060440c050800004603e4030b0b503c3c50714074005810480505280140501104e171005040781402a43c91303c02080541c034280b5008121180b40c0720080143d82080c00b48a016003154004202940c8040341080603943c1c1e10003019078070880d80d95000c3e05908100b218001007011044800c5500448080701c2501c02d202107000c2c0111418a400c0000203600514400e00314035241c0038004d0118124a4180034841c601c201403a120301c2525480391180340d4541c05064407030459 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 543319217 1250 543317967 543317969
    0x603020a09053907020102030d050c03010602060f0c070f05190c080d02120901180e0103050703030e0d0314030703110f03011d07080a1107081801090b0c060f04020a 72
    0x684110000303a910184480a408141c032015211841078200e078914000d00c01030600c0c50644405900308000c0c1210003405540d010641c1a07045010400c51114494103502601e8003400717000e0100c0f07940358075015000303040c104094440c440e2084084148a498034028064520040e04029001917076000e0f407401c5440e01e4940181caa80b14564910130100344144051b002088804640a8454440550070101e88444641003450789180c8144070900540d482405030f001c41c4080d1341c6490085985848608107614000d80c001c42d00340e80070305418020550f00842d406e0030300c00103490030414a0a256030107040300c40c207103200780c8001d180440015000c9100c0c1d0003a00400d001005003c3ea02c000240060700d040c0d2090103207a0f4006041b9000014106007450f07030900c1010b1a9407491459219107410001070900150b440f451100240041d074046850007000380003106503004030b0122120303803c0001d41001e11690001365010810b02840902c0d80000c14203e600110030348444200342e680d480018400615 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 543320467 1250 543319217 543319219
    0x204031b0801060504090c0b090a0e04120f0e0d03121503050f0c06090612040213050a0207030201050106090810050a020f0a020a0c0b04051c210f080916150201060302 73
    0x214981006403554010030310030707110344200070701c010750f214820b201c1903034840f0360014401c640f8031100f0001d9907900009040000300c01000e000e0704036514001c03a910300205a8080d1042d035541d070780120180d40c02440c5520010350780e041010401c440c0c0030000d200103000882c081e0600071901c82c841c28038201503112401d41001021503020307007a107d05145070346440c00755a8142c00c2c030512084613030740c2ca01013050340e08202c0018482403401c45e4405400505400140040fa0022a0a26202c64008550061a101e800c3c0110010303216000740c02c009081d5a01a80003070240a100da1041c84464404a1440c040809404000c00d00e030300c171300502d039000703100341407042c6848040850018112580031500d802c0540c020120446030540b9001c481d00b0601c42c0d0b11845500c0500000d410003501900000250303414003400341000c1c10520640015507075255111218002800c100701c2c051150382006415030400d070b04000070803107131003a0000c180115405010707208081d1780001680340014400d4111101860b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 543321717 1250 543320467 543320483
    0x10c02040e0105160801080f12160203030d0203152209021807032a051902031e0a030e0604020607030c0516081005060d0b01050112090209090d020f030a02071503020403 74
    0x30b4a080900c0040c3c04d40b0b859a4000f0361400d000044002c00000c0312881150400c0150540c41d200c441c0f54041a84801003c1042e505403518070000f5076020300107460350302080c070805030f5245042000d5102c07450131160424400c1e80901c203c0351240c0a802c8011540350000c000024130100c80b03000003105480000c0c2d0b039406042040d0104003427594550001d8240386120308840c11074070405030f40c00c0d448035081241c1c03a0024034148101c441000410816100c4a0045c4c01a2403520241e8100800311000c00047e0304003600000440c3c0c0e480ca541032203001b41c041d41401c05010b0340e04003640004c0c411707c82c016002c0c0812064481900900c0402d2004140d6907042098180c00702ea131320a042510366107202800034a20b4a8080042c04a08010b40f00d4801c10354085200c00313441e07081a00640c1c1059180c3d140e0050103544121a01c01621042c103450b00030f0004100a21041400c2c070300003445d0550100c03403541039070000e000d83c48040b0740008907001640e01064685004000303859046000b805641c0c0040e000c44 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 543322967 1250 543321717 543321721
    0xa02040603050d110d0804020d0819020c09070f1706010215090d1701030b07080c0f0d050f100302060a0e150d050414070f12020d060908180411030105010c02040e0105 73
    0x410300103000400001c060301c0783c50308211136281254841c0450102180424403500c00100140b47c00c40290a007544180c9406050503100010078481c00b240d01c142e0b8000d0391169101300d500385009000b142e40194586040e404410228900822620f4006e501210002040300800c01c1c2d0ba0003403150031820644a601c035115441e00d06030040d80c5402c40c1c03450101103018540f100c0075840c0300302010b0b0306132500000018460780b076201044078180c00007400203001203003d00502c2e4840138044001c0c28890080300010409051110208184c1b10f4044e09100003c64000c40800041c0c49a10a03104480340720304002c00400d4001001c24511069940c0c9183c010000190381014020107500140c00381d40a5541c10000760601e01d4140c0d82c1c0d004900401007004030f0400104140300b01c00121002403440540700303608518240d0740b001c003692410314085a2094000c90700460100381d402521a0b1080200c0f010701c04404403104d501080e10041c05041d04004103a1001d10940d280d03508003075140e800d600000c205074 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 543324217 1250 543322967 543322973
    0x1b0516020301060e0f0a11040b0a120e030c030a020c1e15090402070609060c0315090c0507020901080601060f0e090103080d0216030509030d0903110f03070e0a0f060501020f060c09030a02040603 85
    0x40400321b40454203249403840700c6c1c2c0040341ca502a42c00703a80f501010b040c0380c080840d000742c0d85050b42040074071380251189682500c069081c80034008400c883c10080d51100c4c010b403c0a420030001107a00c6000301d800d85090070360100c0f241a80c40300d5000c180c60340d8001e8228050801140e200b5201380e145c1090000813800200002a480124610b000d0070302040300d082c0300b0b141101a1070513100060565448120b05214141440d03104242ea038280c1e003025845d060b01580801c1711100241c2c000703180c94102074010040c40c0d070805400306162120341b505250880c5038400240c603a00301800702610705440413421105003066981101c6003951003a0b809028800b0703919005080ba07004140050007809403481c1844030501030580c070425a41d00c5200746204040380310a0054100007070071025814070540b0b00c00210b030b1f40240c0899008064000c0081000c0500a07041020350f501e40e0300581c119401f0700c0c0176040b984000300b255a0401080e911327403a135900d80303600040d2800d8401c0901a5029103405400810 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 543325467 1250 543324217 543324241
    0x4021f050417280b04060507020312040809030f0609151506180a0504200a17010602010902010e060a021f06090e0304091107050d052208060601031b0516020301060e 72
    0x3041e500d1003403409020000f10a001401415005150416001c0800e000511540040380d00414a01c11a400c1c14402e800c00f20708410143c2d42034948010005003541039007410301142c0c2050040c040200468100017020a90740c8002e00850090b2000e078401007406040d810b0348091749220001c110a868507400d106c2c1100541c1680c540364032880340c24030005140e0030140070300d980f000c59581c107080012407030802c0c02c229580581e007000e003003110140d18040c14180f0740d240c05010386542d500000e540004d510024190070380c8015154420301052104009aa41c00160107880440c80c808150150310080d418401600058100c0700509041140684001e540040a0011a41d500101f0701c188a941001c40a561042c944003401a0b0420399622003840e02540044c600341c208182c001d560000340303080000265243ea00801f1850b0800800c0c0300e042c0da030501810350464400b140c1e641080492189c0900300c1e215210b9441c2d64071051004e42c0c170565900b035211400030b001106020b0b126140070604c1000e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 543326717 1250 543325467 543325483
    0x1b070305031e1009020c0c06030f0702010e0105130f14010f0c0905120312040c0504050a050a0e0c030d121b02010b0109120507031401092f0904021f050417 68
    0x50009000009060780074082d030081c0e4068100c520310080210300745240080a9881050150705501ca02440c2c1401e90300d03018000c610801c046040c2da4040d080400c4020f0954078512407103441c2c0d030305107403c2c40306180030401c0c6a05103941c8240d1060f00e902031850040401e050120100000b03500e86201080c0314140d40c1c11107903280e0b19075a95140300796190010044440301501a00816500911101c0f07411206a4009a00103004000e0411060b86c3c8200040643e02c0c21102c86c0090b40c1c4980511210b21518040e01029140c0350303014007900000000403a41c6c1d084101f21030010400d1504422403802c00d107a01030021280c011305206001c2c1c010750f038081d01901080440c00d00007130f07032810001801c0581d014a0103220341e210000d0601c103031442d101c0c10280040901116015540ea0b580000025101080c0d0040418043c0450b0074065001200903c00a00030380f19a0140c03407554200001650b4404400c0c00b2501c603110380d26104445c1410031109402244c000703060002d900c981c1001c4c00400050209 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 543327967 1250 543326717 543326731
    0x1b0307060302030c0906071103330c03010303210204061d0616150f0e1507050708041203140a030b12031c1d06010f050307060e012115030b0a0507020a12081b07030503 73
    0x180c143c24070007151b0780c0b08a00c20bc03403014080a0030f000600000740f007510820301c810240c55007111010303140c07110042280d22682c442000f08011191940014072000000d103011142106d4890400496918241e000050440020300c00038010300481c407415003d6100010100301e01d01e0401030381030300010155451748110100b9600d8500440000c4005210350100d40d05183e10542060400380341450160185004420132010b02c402680c076030540400950103415003414542c5d0110720541080103000c590449604038002d540c000f0031005c00155070fa01d8180e1011110398400050102c2c04550400020148050131a2039014000001868032802005042905c07000c0b815181c240e6920b42c001d80d00742d13040c02c1c41c85000c17984584100701840c10113100610010021f24020509590300d034030080b1040c095800403101a1080c206112884603103100e100e90104444c0020026001c25071030b802e0880c0c880c0305401080020130702c005130502090450034034000d00c41455880d10b4642a19010f0040d0300111004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 543329217 1250 543327967 543328033
    0x201020a060b0a0f0e180c030d0f020703080d0b09160c03140f030c041508040222091205130b0a0e15040506040b0d0e010b010e0607060e1b0307060302030c0906071103 73
    0x1003299040c0c08100d4032072442d802401800c2781440d2100541e004980d81d1080d400f980105100080402c03100720090120b041011030001e02c0095120400400000280010080d6400c0600c0c55601541080c40101f40542600305241c0200c14900c8102c614801c8044041850602000340418181014050300c01d84059020300c0c07a4007061400201c446a50840d40030750300c1500130641403520540040d0715400301002c5100403440c160700d074542220044040c10640e0001c0c000040c8101c1d250340418400000e003e41103002850000e4900c030080c14418852003491007040c0110b0820100c41540c011280104005401c00751079541e50055030401e43c000e0030002010350b051a003081c4ca0508188100084184140c40359080d00c5840c01c1401a95045254111815075445212140500f420402c01c510305107654603813003420344180c0500d41031084941c400b0060600500a0020758903040c1c00344ca40001054600c1500c0b407003241080c5400f02c24004070260180a4171140c80d0301c60f5540324045001d02902264 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 543330467 1250 543329217 543329251
    0xe0f1c030f0c02030304120317040308011e081506060c010606031505100906030f060515030405251203271e06020c04020310030c0f210201020a060b0a0f0e 68
    0x2d44865a00020081d0315800400040c440002001894080c0c0c601910b003410f0140c411100401c80c00301c040d1820340110340e8050041011100040b002400c11911962410803145085c941c55a0348076444001c0c00c441c2c04040004050740c440d030056030101e540510080c05440d6507210054020240f80400001d59012004041050b0600301e03200c4003044529501d0814051074507000310000e0003600b28800704d503a190140012a603660f0021002140762450701c203031ba6400c26240c641d19204941304094001c50700300b05800035040110103420110f0700402c40003100d0750190724048400391418461101c8e13400e42a00c6200700b0884e109131810070b0f54048400b01c1e581c0305462032107011701c8901d8442d20300181d2010b417060040d404c058019503001610100203c14494590b9a90420907607103400055591010110030850440d20f2001c190045503040c001c5500c8841d80e80000f074a66004030805000551204c01c49151a1241d51188009041010100401320307100c480328903920a040e19680203030510022 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 543331717 1250 543330467 543330497
    0x105060103060803090f150408011a010c050703030c0f080d020307020d05090a031421360d05150106020a020108010b040b1902190609120c02030d0e0f1c03 68
    0x420311050f108010000c1d411711000340c042040180d5040c0007a07400c02030600c60003c4400050003d8806040c4a0340046484061215100012b0740c51188090400084485803001715901050f40d50640b5010701d008044040542003100052800805c020114040060341903c080026130165000e0b5400740d0a855605040f003404940e0741c000c0c101d015500c808010b50820000f48840d0540a940101c503040c0c07103040017240580b105514144203142840d01c000a04100c2080460040c0b0314030342100715a405026485202c0380400a410382080c81c00307044190341200508c401003126514506c205081c0c40c0c080d684030360000391a0b0340000400c9005c10b20110000ca0069001d20694013511800c0030301c02e0034182c0310b01d884d102c8d08002c40e007804194014400860f0398003050b41d9499520fa13006d10000f04500046d85460345103284115180c004200b0f00d40b03601e00045e6400f040446140035a41340c2103501d03a50b224001070041c1d0390707825116030020300c60b1400307031056201d0046461028001d441d50000c0c0ca4a1070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 543332967 1250 543331717 543331721
    0x40b090321090f011a1009081b0a080d080f040201050c01050103081c0b06090f13020708031803070b060906030118060c090609060c02100e0415170c0303161e03110105060103 76
    0x580e10b4100400303480c0317000780f260901c4030315112244118a02a40666900c141c02c5080024403001c0704a403440e80e072101091402c0403101c0f60000c005a40c0140030b1004002070080003240b024091038580c1c01c0b00d10108082d68410019105003140e01c000070042035035640f03012007031680091200e4440d0713000c100d141c01a0340b00520030a81d4410780a03007201c3c0352100d154100304114500d100d01c90b9110140d8007011403081540c0c80035105680c41203402c1a9203040a40e40c5121104c21241500c403da03008005c810006045031400540200c400d94800404d516810006030250003100203603466854600108000d0000c940c0002c1d5042c155600d540c81a151920030464081c9000e0140c107010520400401c001800e11108043c00c03040b66141407803811801301d00042c103481d600902c3e600e80300e10070a024011000d6500d2943d4003180320100618021942501007501d83c090150b14034046590b8407904028004000e0002c0255000841060000480c2d8a0040d240e202200313000e02d1a5881d007030014409500034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 543334217 1250 543332967 543332981
    0x2d031e1a0d050a0807210503090709020c0a030c050708010f02030604060e011d0702030d050c120a020a0c060e0a06020a0f030e0303070914010c1b08190209040b090321090f01 76
    0x4405083e6214071034462501d0340d40980021500d44201080d02200d0030200040300d681d41300141c0e1100da0741e040095241d803410495800000c8114070411020407840c10011303000d40d16a0b85401e00307400d544078900344141016201d031f200100c0c80d400d0980000c4041d503d90300840c4035110882d401c00401e07495040c04441071809000705c4000c100c03031a829070f07801c03102010706c203070b1140c4203104503803074075045491a1050380c40c04d0700c65034200b11010414401d442070b207690040e4800d40f0400110700341100940c0003081e04100d410060f0100d0382d140e10130300360b4900c01c0c0184042c26802c1b641c15540c805a50070001c042c0c5d803101d5500c0340024503142c030403400d009003c021240600d0a59552000c01c505080300701c55100c82d613102c00c90500480e01e0080d40040d02e08405138003644460700410010925044c2e810307041101c00310070f612401d407110740b0340c00060b0b84858559820540040700800d0075a01e460499185100c0d50b034408101c0345001144052001030b02c0040d0344100820005c0d100000c070f02c220114203035844 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 543335467 1250 543334217 543334223
    0x60911090105032d040b0f0f0a0e0a050303130b0117062e060207090b010201061d0702031b011508010213060f141b0d2d031e1a0d 57
    0x204010100301580300794065500303c0840c1100c0807442e40f010540c1400c90b5a000e40d221102c1102d00b0422081c400040e80d181c1d40584000020046807034000e0840303000040080c204146903a4035401c1e03201592080152030300081e8010700300c2c2e6890a00b104140f903040304580c401c68070807015900100d4072110703041e001c85404811000501460f1205494880142490a200728500300c2a03c80c0b81036041d0609010b40013482c181e00904061030404100c1425284200131190540e0b04100c400c00c02e1648141c4a80004803080c120b1b000b107503d841c00104e09502c03542c1c0c075016100d031341181c5050b00d144040d804001d03994171850100e031001c0d50b00c01c8142e0070303401904640c0060600d07018081180c940241c4440201c6005403500f003202902203000708285400036803d0000042004100024501c010082504201c016050200d2000803c110001e00d5281820703194200018030010315203031034041e07040ba648039002019a0301103103000b0042c0ca401004942001c1d04541c00b604015582c80c2095200010a40d070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 543336717 1250 543335467 543335501
    0x70b0403120c050a02010e150703030c02010501080a050c040e03040b070614010f06120b0307090c030f200d020d0626070e090a030c17041710020a0813030c080301180609 74
    0x4d26400540d60070302420902a08105c10285c0501010341120040145501c1790b1000070f40290007590003400c54105800070035440c0e2185290230049400001d141c030705418100c401140c60b0f8a1318803d1400c40c041c40d4452503031804003141f440c04024190304090045000341c03241e2139140e80d9070780c5001c416030307405e04c55540816001c1440250b4000c194028110078880030302264071440e80c90342440b049801c400000000207581e41140000d0303020340d000e038650706403040d440750380450802c0e01c1f00e15003441080e01c0217a21550006542c2c5000310b99402640c02041d802000d04008a20018580079010b104c040740d01c0c86000da4440400c0d18a9111641805551083c000f013103010099034040c0c80d080380801c0283c8240608240c01107500340740c2c0d40184060138289659006038500007203850714001300383c80d942d8062801030207910754255000c0c1005a00c01074620091220488a06050700e504032180809032806000000100d000d00c42a040000a17160701501089616584c08140088807008426110343c16 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 543337967 1250 543336717 543336733
    0x160b04060516020618040b06070b0f040f05070b0d0e010c02190203070f0902090109080d0f0f0c060f0b0a05040605150927010905160e10050c070b0403120c05 69
    0x3522641c0030b4580c001c49800ca040c611a01c9400003486a000703646060440d03c40c0504024085c1801d01444e80800750170764019080207941d641c0d0001c40e41000b0546c0c0e11301c092950000d814445810300f407101198012045d130381107a07140c00b0b503402d01d070707101c92407859003141010086500c0000c144168120f64040e45d01416a61b00d0350841004500105030b400e0307030706104d4604049a100300d4019041d0081c800210010f130f40d03a8034280094903209603035226548a410081129078503540006201040504924103642071b0010400151819003103588081c00721031911420103c41040750303005c0394102404990307400b1655a2441008142c0b400d50281030380010103010b4a040821130079000c0c01c00280018003802d0101e40540f10300c1c845128006842c05861142030041202d003d0074425580c0002c0c1c2003ea554018200881c054000881108030901450003c00440545d03485a0281c5107818002c0003950041c0350358000c00001030700076002c16607802c00e8846808500d1030003111004440d41e4404040c1c1564 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 543339217 1250 543337967 543337979
    0x20f06040215121617150607060920010921080d180506061008040f150b0301020a0819050106080106030c090e07030c030e030c0a0209060406030b0103030f02160b04 72
    0x420404000d000364031091000741060118001924498200f2088000903141d1004c4020161000313030640c600d1485015041c41814040d5544a11035294103554466070f5074458078101000b411449805440418100080a5040042002c1c016250b5090380d442c03007003d890b02000521062803000b0200184109034000c000920000007074226001c0c04240081c45461040505258110044046405400c000308000451a0040d5811400d100600d88074002d07103083d55440e030403980c140b500038100802a0105403a0034000c3e40180c020680090029925408032030409071042d4803d0321708801890201960b1a40550b0b140b0405049817108d0740c0350041c1e640790400c160000d0145207180780410400c080007080130250009034034051803955400103054803480c130004045900481c0845c141c2d4204000001421000044010000b0f404480c0203007940c55150000c0c00812541d40010051203034a0300010034140c010b1180d410341c629035000c0c4e40c0103c10480320340c03d200b5020f000f44442c85800388014050 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 543340467 1250 543339217 543339229
    0x3050702031602120601080a03020d02010b0a05010503100f09020a030f090803180f06070f18030c090213080d020109020306070801030c0608060102010f1104230f061e07080d05010501020f060402 85
    0xc03d002501089036003040f54141828040c00741c1002d02a030780016150420582e04012218a00c5003502c020400c100e000c00c00130301540014460f1504002d80400030842054291001e0f60081102e0702e4006601380d60307800d05030040d4110084000110b8a072954029506030035000b00d0040680c0030840d44d01c1d558403110299008200034030043d94900c103011600b4407031002080028090329040d214a164000c0021004007990182c01e45007a050380c201504000203031408a107c0207440744a0000361310b8023a01a18059228580e5200100070f01c111740e0107881068066000c42d0b4594001c0d8140c61542d1340c1d584050794212800e20000b003007108555010444680705540d4140c0040301440007280d600f03107009075481a28854807160540410004040100c0451941e00c0100c040342e00700c2c0b040080e071120f0001100714003041d48032030091000003900068500c0b03151364003503680c00210105444192a04101a507034001d10300b1100050703c1d000000c906903000051889041d5503d01c0101155075440d130a00032 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 543341717 1250 543340467 543340507
    0x30803041403030c120105010f0804110301020c0a210c0b04030f1209060b1f051207020705030a030804031d0306060d02042304050625030902060d06030f120305070203 73
    0x103810201041c1003200580d00344011401440f0003250341d40c88481c0c412410b4002401a48190305208104115010150304402c1d81603000d40c1000c0c02c100d125a8400200f80607120369185103c04d401100d00c000100281241e8505007164030307851340c00d48c0c841c002c0c106075581c803214000503140841c0c040c0001d0001c0d114144240100d1814a0040581a80303924101e00703540700d00604440b21500c81f528100300b810a8480c10615198080003090005140c0401906a10800100d80400c0580c0300c00151300074001c00010f002480085c048030600381c91400c00414000050309c0c01c40000d0b04042007110004079a03402d414000e000200503110503110442040540c48500c2c0c8100d130010344403c203840340722403e041c403203247c1c1c03114170040e82c0d40703280a161150901c4402400c22082855008040ba52178848103007038080c10074103040c0010a41020700000b00c80f400b600d05030000f01c60410401100300040800c10402d91445010300d130003407030300c080b4041c0e0a95004031a010300503402480000400502c60605007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 543342967 1250 543341717 543341723
    0xe0906270c040603050619051e0606041203081801061401031d070f1a07050a030c260a030b030a02060d02070f051c0f11030d27201903080304 62
    0x78100e03441c08000716060b14140d5009a56a03040700c400c019400d0722034010904c840054482c200306620b412103410045010107110b5440764614103000070503079210b0032b04803070140280b2000400b6103500b03458010240304c0220f4030b8510350040d8551207080405c05014620640c0d00d20300310305013804540001140200380364007605000e003201d0b03006074103107200030f014400241a1305648012564100194170b1107114044407200030296003004171501164010071290099a0700d45007105005905050200704024803c0c0c1c0600c402c0c0e261000c6c800d142081100030a0410070544040c0213103280b4104160b02c031a01800080e4002e082009000032800240d030040c42801e10492618619007101d4581500c0d0008240c0400140781e50444810901a00035030500d000e0701040c60704200030011019096224011014845422521400408140c1642d940b000044032284442d62421040500381403a19501c86d1031b0b084400b0240219540d11420554000030341d072040d40000100301869952000f01c5940014415 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 543344217 1250 543342967 543342973
    0x201030209030627032b0921020c0d0804050d0311012a0c03080109050604090b010b07060605030304030c05010e0105070b04050705011d1c050c031614040b221d070e090627 75
    0x3100020042010201903451048c492502c44801540107440c0030702512600c3e100c2c1000b140640c0004081e2000c40f8103945060340c802c05007030b82525007030312789040c0075903024802c0d403c003180c241450040b11202c01d40e41c880d8111a0481d0840b248081d50f4140c5501405000100c491005000488954001c59003002003e80300180404407074880c9240b8407000c0c0c010000400300007480906105c440d02644000c3c02044000d98a17017451507442149142c43c511505050040545403001c0780d038000da050b9208942c0106920106151601c0c0c595114840d03401018041810780b070078400c260082c0e2007046c0f03e00348060501c1e200c0642c01000398584e00e00b1580111074a100b02003070515140c4041c0f2000e4014131041c1250354900c0d0420f0302d0b18180048180001d80203624150701c01c0d0507540c45070700c0407a004654604812110648006c11000384c80d84c0e400c80000c0e540c4600380880326040004040c3c040f41c50908244100346c89a00c40b268940c542a0f940e0401c024140c0c0b195442c1e841035038a28000500b00e1070072 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 543345323 1106 543344217 543344231
    0x12010b0720060d0e01150b04050a06030f0612081215011b210c06060515040605090a09020a0e120d050f0f1903060914220201030209030627032b 63
    0xd0380c40cc154681c07550f4002007800c1d52000c006040305a1003e100c6003001d00f0300343c02a5000584c0c41ea0071310200000221813890502c0810100315050b52012000030500c10304d00d40d040b03818001070350400425590046800143e44000e60128900d44944005541e5410000d040300d15542c01207029620031045005404c00d488201e07400e403106400c1041d1a03004d140e010440d4406660030500ca0070b072002440c00300040d00070444030080b007411107802c503048200c4041c050b100c1030b65010290100b84c05106070034501a52401500c140700600c2601800c00400340002010007924002c802e001c03a686400030300c5411a980200003c0703c2d080d00b121100b41c01d220408075040a070b000c0b01c050400701c940141d0300841e031294044900c2641c008088800606106900305000304110740043c410202071880a950b0003808010340313200040c06080c0505c080060450002450100504080b881d652482 = true := by decide +kernel

theorem cover : BRFrame.Cov 543165467 543345323 := by
  have h0 := BRFrame.cov_init 543165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 543165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 543165467 ≤ n) (h2 : n < 543345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
