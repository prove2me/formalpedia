-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5359
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:36:22.514271+00:00
-- url     : https://prove2.me/submissions/117e2b6b-093a-45b6-99cf-7d21b3226eab

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 963669064 ≤ n < 963848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 963670314 1250 963669064 963669067
    0x609162f060907140d08120a0906151d040506060d05120301090609050709050303041206061502010b1206130b19052404110403080c0316060f0605010f020c09090c06 72
    0x85100d640e00c070342d07191044d0000c401ca401251215420042a45014690002015424006100d403044c640110060007009001d5445000e400012043d208804c1104807400d404107a180c28981500009100c020f07105920301050800c00000641c00201d40e98070401c03c0c2c841c080100350620f0664501081380e524071114840102c00851882c0007a8804c000305d07401d8050600843e1107550090324402d159024468158108200500c0004482c4091030a481c0c40f076000044c50310f13514081020a1401d02e8a4600140d45aa081c0c0c00303145820b99090246041c07141c00340120341410b1190b004070f0070008500074030203c1950005214400000c002c1c00902218040c01d102a141c5103645240240448100a125003035030109107070503090a200b008d03600070b1031013080c528080c00c68031203480030b4000000f440305910041101c40031080c070760810903954620444000c6000b002d841c80364403e486082e0022410410b00100c0f5031800c41c3c0c00520b030214144140d42840060312020103507401c22826940c1075170030010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 963671564 1250 963670314 963670321
    0x50622080a03050711090403091403031b0312310303141f090c142203080711040e0607031a0a0611010608070608160302040f0e0609162f06 61
    0x3007200c014044c1c0c1e132089103644003565251040044040094501800044403c182407112528066006c503103464000c4c112418100c600a840c0e43c0c84181c0092a00705400105050016000d12142642c03c48003a49030718140d42c90380d010040c5c40d215560030111400148c0c4a141084c10701039800341c6520480c01c16900918601300c9801800303105a081c1e00500302c03205000000310f0810b10700c2840d100e0303a01e80d9120214626000f00300d1005400140c400010001e400c84003041c6080e540d041c80c3c004601c01d00c42c454940040c1d040c101c0c194203000b41041d0180703040c805850317010304006c100160b00c684281000201c001602142c0c803101d10b940526160451041000030a1041d04a40a200c481403950001d00805071100000741c1c4968070707482541301150601c00440c01030b070341d044d803220b42d0080545030041c01c0640da0b0f113444041050607071142c070344206a10240152800d000040661080310403000c54800030032a600200030208400783c05000c1c5921702414410355046582c1c02050724100f0049800c2c1c1c3c103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 963672814 1250 963671564 963671567
    0x12070816061a01180e2e180605060703030903030b030f010917040806010b070510050f0108100b030712021f08061f08040b1f06180e01050622080a03 65
    0x900c48110b101940c2c9031805002e0943c07240007030114118040001001c014139001490303101c440043c20340c5070701050240e16140007101c104030240617941d5002403000610f1034007040403410700c4884010800c19040c0f00d000e00180d100c24007218070f0142e041c0340000d42540d07581422802064020540c0d5414040d40f4000345448505401c01a840d500680005521b05480301c8449140c0c070491250712211380107180100b01da02c0030381000c0d00440d40141d0030f0302d4906880401e804120341c002c0350780b81c1c00005c00100500550b081040801c03010320740303004200110820440003a03520382442c0300717282e54482c00030581811921144c80401c2654041c04640400c04c000c0c440103049d582e01100c425000341d00211070070101d03a003032502c1150b5950490707c1d02801c5480b140c0740c0958060008081c131b14003503210b4011200c0221600e01035401410240c1c4c07114510f0040c0500301004a40740d03449640c1d00c4558400600c825503c210403500040004070b9080645108000c80300c0c6400395980c000c0586001d01c1e0381900906 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 963674064 1250 963672814 963672821
    0xe04020c0f1f05010e06040c1701081b04050f0a0b030106090f0501051903110910051002070503100c091415040e10060c0807140f0712050f03040501021207081606 71
    0x1c0310b40c40d95141d030300740311100d00c008444091003240400c01028000c00c4c59410560b2110b0060343c1c0a103410700c00c0c1c15607018402c100b070500303034003d0b0044c1e4850540710311061220001d281d00101d04590901c11410840c040b0271081c1c03400383c5500c822503611556074881c0d0341e007580030800520124405005183d0305858020041c04244100c0f07000310700000f100c0a001c507448640700705407035100d9082004181950203100c0f11140083c03034040510f08261010606984051450051003440c0d130007400020b00b820145810108441c4603004011308085034801c42c0c44e0803610b00c40541e51450486881c3d0080080001d04084001c00b000c21680c00011340400e000c080118030070b128080000c040815a40e84040443e0203c0c041300019150800074401540024044001950103c0e03500f402c64151900e80c00c1c2d12410203c55074805010210000100c804000301400001c1c2142c0021014504007803030000003075100c8900c0c0004200b00c01e80041e0b0704041150900541e107006203000d0405407030031010318042004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 963675314 1250 963674064 963674083
    0x519120905071712030408090112050a0203091605010c02121e07081c05120a0f1a03010b040621080409051302121b04020c0c120a0210140a0e04020c0f 66
    0x4485401c02000415031001071300c01c903043c00054003a841c6690307944400010380c003c40c0c14541000000c0c0900d040400c5030b40520740c040e07c1200d10050b900c0c28101806440e00c480f00042d5064070045080401443e0380004100020980564035030044a841c000414184081007030b031131000144e04c0e40720300c42140000800800f0303240c3c0d40c800c4883d01c40300c0c40f50702c40504024140c0600013a80411921b41000b0b034140c600b540001490401141c091016414441a100407a107c20035190000040a80c0c1d40350074018400c000720103031810000542003080d88120035588040c401c948000361041c2404001150f41103d0042100210802c00d60900825040320042d8195007644184040400d03031888020126202d000c181c01c1a440200c82d0000d2400d00010b5085003541c958a0f000300c1d1461030064032242c4a4071012030540300600045121441041007444a0710183d0041104a65921007070f0500c03c02240c05d140e2003810580c045552100c001400f07485640f024030054050003a42020120002070403030342c1d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 963676564 1250 963675314 963675329
    0x6030f02070204020d1b18060309111f03150509070c0503071202070306050916031502090402070b09070b070f02011b020d060c081b040b13050918060c070201051912090507 75
    0x2c140851541c1247d42a0541021814400d402c0104010080c020b601c4004003510030200c0d4100f80300180005240034a6407066010840101450242150703414414a031031841c0800791242542e06010101c0c81d1500014510801d000d0701c0c60039031091010410550321034640c00041d2042c211704008000352127440d00d100403143c071800c2001242c5007880c0070034036170320341880e507201c0081c8546191107071103410507944c44c502c0d2903981c200811040d9803507900080c00e40e58040d12240c041418a45911441d101d5164004140701001307010350782c00554884000118244c0902e0303d03040d12040109102c0f04181400300003940318654440100800c005604010161603940d100d80f92140c0d98501500c411720b9209003c144c0301c54003088103004500c5100f019202c1500292414091141c85001007202a04141c4103c1c1386250f04034030540c641902009200d40c0f0003a03004201e1f09040985d4000791841c06116041001304552610704083d5600c101088224848007200c01c3c0007844490070135a854481d180503858 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 963677814 1250 963676564 963676601
    0x30e030a020a031d090412141303120f0f031113090905010b01032706020d180c050d20030c03010f06080c1002030307080c090307090c08060d0c06030f02070204020d 72
    0x550411380c0c800c145080714040d02c00d2400f5521583d4050901d090004600203201c0c5402c1c034404c0118814029141445000d551441038604501b4800b500724050742d1560108150200001c4206034000b075181485071440c02c5c0441e14203103401800f602406442040790154000c8000011014165004800c206005070005c0020b05014001182554195041c0340044c00d2021502d126449001041c2300000780103a5006090240210041d01901d614103151210600e10041c41e900780140801c218004050868051001a60a0740c46440039004207040c11100008100403039805d4409202010710340000800802c038280c801c001c0040100385501a0740480d03c54000024101c0c102174222003201c0c1d0f030030f800840c02c658400710202d032084ac0c001c194040c0c0100600c094142c60f2002c0003001d02400b00d211010616204a80000f010550700078102d81c894442c042c0b606c03000ca0f060940210030b40c1c00903d4040b07404040b2a010030003a2280e0500290414400a016103841a5903481010b5102120b140030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 963679064 1250 963677814 963677837
    0x2a0f15050a0902150d060801090819020f1009020402070501090b10050a030f02040b0a0305030d051e240414130302010617070e13080a02011b14030c0a030e030a020a03 73
    0x340212030480c0d80094104807542078605100c800c4d1005804914661100807910a440c0e2403440e003910421582110350700404030700342d00810382c0c54425512001540c401002041441c180710307503450590381c20140003517580c0e030303c42e80544d101c1d0340445520365007200003030088035418500004800e20854801c500e0310b0418201050780e00e00011520202c9800002400c04000141c00b048002e2000382916a0b020381c00d4000080002c600384081e29280083c803100040700d150504420250345000c480306441d1004010401200341c951106100d09454041c14545901c0306080c0424000d0030030010b03a6203504400d900b04560401880544120684079900a105003507481c0340c5c80303041400d51500d0102503000040d0a100726400701d90885d80c06000880845044000707500c4030102036001418600c0180d4440c00c0d0000d01c91015062500c80e45001c3c42c140f00c08c5501901c040c9001d000150001c0e81e2203c0024801c40585e03c40d410850805280506882e40d98666800180d641e02540700700301c0118005400b038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 963680314 1250 963679064 963679081
    0x140c07060f030e07050405060a1d0405060601082203052b0c020c0a030f020102011b080901060510092702120106081e07052209091707032a0f1505 64
    0xf0030302900c4520700100001e5062208000c0038150091809401840c003040026080c844180e04000d00011407003148440c0c14a0300f8581d003004401004241402070b86018403074401e445488051202843c3c581060070801c0702e150072500c91090b4140602d00c1d50034225404070320241109840401c00d09000208101c2c4a0254140d8031014244030040c4c0c44410100204041401d003e40050303560710507c00062074040010106018840d10708180e030016900d20f0400032415400d200b20707400f418049400030180c0b10503400091400703071203000d080e428031203a1481101d2810704620714100003401c88001d648409a500c0d001200391824490300000a040300d0200c1e1524000c007511a41c0c884d40307844d52a42580d01c0c4c69046d183d070342c0102d5040114000102607029050340d24203008001d814070080100714208203041011609100d1016061004000c0010000298004010064403541c04030041c2c00c2554011000d107008414000181c8009070881d030700c00402c0a1100c000800d00d440c00b42c200510b8448020 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 963681564 1250 963680314 963680321
    0x607120e010e0c010c03090e040f15060311061803070b28020c10021f050106021b0a2105010207050102030f0705072a05060f0a030c081015140c07060f03 67
    0x960b1076190465010480360b54403595440d13030114000c0c10501e800c641c0d115000c40c5890000c9a041e205030a0070b0005604202c10691130b1980104989400c0c4066810b68880d4614500c070300303001c50320440000525101c80c142d0b50614191001e0000c041d240b1403661040c00017010b81c0000d1105c0d0030308542140003000c130041100000d0200159074000c1980036020414004201c01c03000c0c5040542c03164403003091441d00c80c00e0404025018071036000c80d40f03515000002c3d103458000910341c80460440e404221040c0c0b076011140f01120b0742e48200055a03c1c0205400c2c803020034185c0e01070190350000a45d0b40a026054004600039005100e44540310755500504030740b40c0c0100030000301031651031861811059034809089030f4944076030382d11800c410307916000180a688a01c034883c111f15030201e68101c0f016014482c4d003030001c1585c1454145451301c0e040034103240140c0e008440d030344445030401d03070004c034172801101058403141d07025141d031000103102183d5100c44500c01c16000500c90750060400920900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 963682814 1250 963681564 963681581
    0xd1d121528020706060e180c03030a27120f110d05030a11070902070309030c061e141306020114010603060807120f080f0d06050409080904090c05030607120e01 70
    0x20881a1071000702420003039407242c907040d80c2640e100c0b80080340c0c03003042403005401120710002020f100c084281c10142046504001c81b4030035013060000807441600052559a0800e0503840141000e903413250350703074003000c07a0f0b00940040d03d000040354007080030307007a144004640110400030800d0706070020000801c601c41001409034000b840b0609005024995401d0080340e081e084c1c46d001500c4410040403038012500981c00588000390401c148800c0d01c0c0094042e00d040d00c0d00685a42a110707000200c0c581d4181010100310006240c00c00011010040c1d419036072444003020b4680e641c03801c0090190040040414004091200000704607000e40b20395400c03101c0c08005010782501e04038000d01540b00211017610400101210003000409000041c810881804001500c80c885454078004072a210380051740542c0c0f41071f40300e0740420800d00a40740103420450340410b400c1090328003450091b00d240c4c080744c2c0611800c82440036250b00300400c400074540040b401c21000d14945a95826186c901 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 963684064 1250 963682814 963682861
    0x3050c0303030c27120d090e100302060703050d020f04050f040507021c020f010e0f12040602060402040c03020d06030c0614070c3c05011b03020d1d1215 67
    0x4020596065a0051444900030b001c42c05a845240813080410400058400b10031925040060044200350b008507024001e811100000d103220300d004030b070005003003d9502000e84502d0780401e142c81051301c154125034030b04011038015512540385010060f41ea4002d03000e41340c4a000142122106030a003440b03504e1050080354004d104d5038003000c20740e07582c0004800a040031800b070820862031002c402d0042c20300c048950001040e44e0351081c1c100505012000c0055019404100f10400c405680000e42940280d01220002400d40c010301064000703102d1030b0701e100884d50400400200340444400760f01d08848540c0ca80310f10b401003064100c4107500c241c0b4801007548850749028410504081005c4184900924110010b44503018130182c0842c0000110540c43c03444401c18051541d001d50344440c501d0f03240024140032405543d0107034895030b020005008012030800e1310310040004060300c0303507810301c013400b4600300782c1048600c41d071a8032142105072600c0c404980400c2c07440045101041c4081002d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 963685314 1250 963684064 963684067
    0x9120815061602090c0d0c02061e0c0403060c0815012c010c0b01120c0f0e07031a04061e0806240307210b07030204050d06020d0609090c03050c0303030c 67
    0x11031080141940001080102c0507281e000c82200580310044042d0244825081c01a145c500420302d40f000d8070200300795441190800e009000c0070341d60b8007190310f00c281e0b441b046200c403650b2801c1448000d8022548040c00a43c00e104009070351030f800046640c050718101d0790382c1a4129514005440203283c1c8592801044403420303480f6010030101c0b9000c90310328014506a9a00d9a071a2504030080100fa0400d4031040561000d043c10860007074840c1b0020941440070044061810503040c45040004004c0390604d511010b980001c407113000d5200000e400001d00030082ca40d2524600100d46941d0125120988240b4201040700500050103502c02d048900c078130f403d100081d00070050070350b20709044260180700b150760200391100703075442202c51410036034050520f07010795080202e6070b1703003005d0208401d0505c1000f05200a03110a40140c450766008000541e03252156030a40e4000c00241e844144594649a406000c1142d059240422030707000314226102c56040074109500c070310043e1036420301c6640 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 963686564 1250 963685314 963685351
    0x170601140f09030a0f050d111218030a0606150206010f0302220f06030b220507060507080708031807060e0a06030504021206070816110c01180f09091208 67
    0x2941c00c0209603801c000b0b019145400d01a984010b0046142a0100c800d600b062104522181c2d200c8105298032441c071005000f020400c00c3c03a41094454440c0454081610f21110300f603948003002000c0c04154001010050241d5904107503041503d100f01040060164030000100e00d015460300e0015280c00814400025441001184000c9504010041d000c2e45410101c7c5115109110b4100110b00491107101180381034902d5054403130142d11400c500b413900b02c1c46800860400110176050b64043e0070312680e142404d042000f841c0c041d04000510700c4500008000741400c1c0d0a00c1242e80521000c204d418090703c0d614259966800e00780d41642002034030390b081201d036101b80c020a400a0003c2c1400c5030105141c61180d0810340211420310108482e00b040c0028954a0340002140c01c07070380c0c640703030121004207180d0649070300c402060b13a41040b0340c400481d07180156140b0207200a01c9084e074960b074001c1e51601490040d00e40600203407001d01524805040550281440301d12640d151040d0740c08031807 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 963687814 1250 963686564 963686587
    0x1d060103120e010c170703260f1305060a090308010b0307020c060702010e04090c03210509040b0a1211010311030105010c020d05030c1009020f0619270617060114 71
    0x1c018010782030411206980d40e03004900e1007001002c00e01700e6607298a94030601800e01808011900804d0720140902c1151800c407800900000d5400260a290003040354650f00c550004601c0c0c0c00e50050464050501404403490250344140d402520a4403404d1300e5a0380c0d21044241c0380002c540c0c950160f0072821501507a4600300d002030034403910505015074403800e02c0001c50b04a482c0c130f00040f02c0850340001c0502c107102004044001c82d40c05c024500203d0081840010424004c20008a0181c0d031038012074800340c0d88000000001d810900c04042100041d418419010145024002d020038074040c2c1140c101c0b0032a4046034140c44040e168402c0d01540c40e400d100407241c060a0944880c00280038200121109001078414070812501c0030500d94001e004100500020780341480c030803542000f82d140010784290500ca1001001e05084005091600d45090800711141540c8203000300c43c54082101d070703000070004506134441d640c9000141e685400640710940c0c031711841d8034035a01c140000318644 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 963689064 1250 963687814 963687827
    0xd06080a02030a1101140a020d02120c0a06090f05010e071e0f05090702070305030f0c011a010212130e162c06071a090307030f0c0c09050c1c1d06010312 67
    0x403010f01d0405008890510011b00c240c000f851a0340043c0c018654102d0181d40c1040400d0200e0302c2d015280785080394031400a9541c90b01030030001c4c181604d40c0815400c0c094440803c01000381c01c00001e0041070040c1d5225a100c40380c50003070303040d42000c241402c11414000c44003001034a00126141c11010304200412486c100003c003400e00310b100e8140080000740c4140042c2c11050005511b0342c0d1100007411fa11400c1d40c000a403e0728081000022002844ea80041c0d241074560072449650740d200c0c11082902422205034100d0f0340c402c064202800f81d194840e410144200038590340da2099035070422421150190b02c41010005401000a401900d251000003030102d64450341c000340c002c2d08448155024408121985a51600b0211340384003416000088000c18001618206c1403210190391440846034450141e4800190b460001a0307038100314000303c614014100300d81005250100541ca8050704600000030308421075072407400049100015183d0680f540140744071404042504101c031314 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 963690314 1250 963689064 963689093
    0x5010503060f131d01231e010e150306070804020603100e01140312040f140109180e0c01031e0504050c060a031a010c051c020c1201020d06080a02030a 66
    0x4804a0704402c902907903403069552081e02002c002107030b5400340b02642d15003c421000f0740601c030b90409843d12044d03810b081c094040c40443d4071081c10b0603114a40ca445150842940c8034000000c07420002c683d008034194060f210751070100f0590080144502415181c0400381c50b0030010409a001240041c0307000d00103560b1100c4401c0c0d84010559842c028020024820791026010b00400081c1a841d41814022a031540d21818079403440d287c5440340301c0003010070038801c10b0020b50b0340070703803e0400e40c1c496446c1e0f20003080d10340c1902007505541e00710400207181e8403410103028800c06524040300d5002e406600d0350120352110700c400d98000414440301a0100070411a09401080030031151551400c000c2c2c0310a25082d81c0008102c00c20320300309011810080c000a061205000200300041c400207280e62000ea012007000f20352301c840c0c14003a0f28040c4840741d000e52000340c2030150759000c60158041c02c054601440140021235440d02555160721440d00080c0d05078100d56030f080301080792030030b07507002 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 963691564 1250 963690314 963690319
    0x10f060e0d0f081e03040b0907080d050c100501090218150703031508060106020f06011e03060c121b14130b0307110a060c0809070f092f0309060a150501050306 70
    0xb5110046484009003030b001c13503440c1e40722000481803005224440760029070204c3c00ca802850400c0c204524155074404020500d0100b10001070219407034071082c00141055220104e041c400d650f100c2c203082000c0d40141e41f02901d4155038640e444400e02c0c2c400c080000d48407809080300c0c6043c8054600302c0192010040c000000d5040b100e0004c5c104800b085007a00a0480b40c0c0070308081180c1e410450b0400c0010b07441782c050304000c81151624042d01007400701c12203502420014180c4403c03001550490300105440b14658a046031800306030303450741160014480e050751803010b944243c9041010b0b80c01180c0d060288401600410720094204500a5812031a0b50a2100c200d624822451789042120182102e080b038941c9403080da055080a04103410000100107800e4450904e02d10b003040002601c07604600d84d071030b07071210400351540780c440201c849046150104081983e20400300305500940e1340c80e4080c8910000184940c10600c07070340301c1412000d0100c209192414004441d0703a00003505895 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 963692814 1250 963691564 963691567
    0x41403030408070e010e011706010e04030309020904050c0a1707050402130b0a09050406050108043c0f0b070c0f12052715070b061c02060f03010f060e0d0f08 69
    0x50b4414041150703000030100c188280f0303120f41c10400c000d000e0003410b0f0700004001c01000c045d1145030301e0108215056810180d01c0d070101d681c503402c3c101c2c042e0504910185d000044003040c00180a804511100b48107801d441402155030340c0c240f00d01204116490038192030700a01d10030300291406800808443c1041180700c140c4030748400c0001201d601040c100e0001c142c41801c201300e40c1c101409410000e14007403c2402183c5055100c5140e10201c01c2615003200400900020b031101e05185000042e580b001288404110286401a290b132540b5500350380144800001810140c400c440c01c00c07003940c2c0090102c207210345503600c00c40140000010341c0700784001400003140b05000510016070080c03854841c1d0150184800502c5540d103070f0a2050b0810a8080041d5008646e0951085800c10f5081d90201491a0800c6e0005074050000800039802080000c415043c100b642e070185d8103940c0d20b03100031402d65903911400c1c0c4d501c14201607040c0c2c021841c0c6414801255074441c10284150190a00c1d9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 963694064 1250 963692814 963692819
    0x7031514070c0314040303170a020f071506090e120c100f02091002070b07080903030702040203070c03030b03160b0a2115051203120702030f040e0f1b0414030304 71
    0x640c8550210740d48000140031004100c24164424080410030961000040c5000d007591401062050895007215140318503402203035840006504607441c18070704901d00d548500e0640303800301c2030000c00c0b4401c1d07070090708088c00400d04000500c00c920011911100814940403520005c45150b0800c2904002d030340990500c1c91610074075070155010b03000000274010783e45d05201041140c91546410782c4030440d0b2201f44140800c8081e00d003101c0c0040d82101515850320042c400082c6503104805000350400c1c004010700c22980c3d080120803550754440d032410b0202d0b605200038150f0b1100451280d4428005181c7c003001210700800003003e5403000c42c46d1a03d95134036220700400303021000e40300030a00243e54020a80702001c00020341006018103c820f02600c01d0001141503503405007c10541000002d9400302e90700ca40200b080300d1880c91160399103903c0302d6640441c209085011105000f00b0611240015241c100ca40441d0071002c3d50702d005c031424181043e04440c00d20400300140351b058802044003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 963695314 1250 963694064 963694091
    0x6051b0f0607050301030605150a140d120903050708060c0319090c0b0a0f030b030318010507200a060f0f0e03030708040905090c030304030c0303050f09210d0c05070315 74
    0x200c521601a0f5158a44e50b03501d1840c000089032402030450350480000ca5412510ba40d643c1a070038102c81d901790318011f0500807a4005080c488005900900d018541c05020403059005100031085034003e105942c0c000d035036800c141c1d440741e9003229683d03004501000041c0c51082608241080181d01480019440c901542e640c074500da22a00030262094002ca040c82d00c00b980708045240090051a040c0700d68084d503004241c0e64051800c04440d22800558502c0541e44030740d007520021500720f42d40d1044040c00020f81c400c4080e0071161503004085110020886c2f030700503809051022a96500d001540c241c50804440f080c3c8440c140c2d07541030108210f0381c40841c0b1404040c0000d8500d07180005038608002801d43d2900742c2400e00c0e140290030078002080450610006001100d403d82060f50342c0d101c0c00401a1094410403101c0e51740140c0a19800460b40f854a1502c6c0d19041d0f50012541d070580c05601c20b41ea050a40b08006119501c0303001c06000180d441c211f100085100e605010450000f00c081 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 963696564 1250 963695314 963695323
    0x31306060e04200a0608270a0c090f050105010c0b04020a1703090a080a020d111f03020c07230423070809061317031512030a1806051b0f 60
    0x4041d036040c1840c2039803a0f61080c0c02140c9010464040350440521483c0c070001400d000001410310b00e40051146120b0080075070031a00340c4103900715405880c04a001c500c0c09810040140c020a0001803905207910000c0e030040c800d09060390710586540d03e038812141e84008a4402c004c10890300411840350000c0c0440640c100061210034400140d0b803602180c80a02c024102d043c0d101d000b0322307400280400c1c00f41e141c4840300f03000241c1280c450705c009481c0d41c020503a914002d00038460055038001608800075810b501034a41e081030001900c0070b00f0ba680d80d140600040c0c00040000c070b94602d04000315540307410b0740048481208800084106007150248c0106104202ca64202003052002003103003855090020a42c000302114240c211090140c0b1019030b0110310390f0904c19070500000215144510210130400c500500908203950440804001c98998004031394a0000c1440001d2003e6402c0842903d00241c8020b655800c0c103203400e04041c05c101d10141d034917100990044501e051b103051030a10 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 963697814 1250 963696564 963696571
    0x12090c05090705070b06090114210303130302010b030601180c0210020d0b1305070f0806060702090103030e040f09020f090c12042001030c140c01020408100905150c031306060e 77
    0x1103da58843c495070600c403107450720003080705100f10740b2040144400000056064070401050b074003001310840c480400c2c015410030161805207880040204450000d00591000040e84254002e2040d10015003c3c50f1b6910400e01400c42e42c0050305d5100c010040d800e9101503100c2d08144111120002103801c0c07041203074008210005031170381700c807180c030300c60308000e102e1000111041c241008146081c0303900600600c0c0c0c1442c1001006400c1c008190641e8503a0162040590000c00590103944c0d00d180140080d4941d03181580602d080001041604856105010000d900a081400040743d81d10421280071001014240c0070f00c41401002322002241004901c40d51244a010024002c030480980907a9104500740e41018100701c00148840e51080c0a819011200d20056031501070001e501406806150000141c038030490450148070b450b1500719003480c82c0602c003502c00300149409490840c11003210305e4141d8140401c04100384901c100d810100346409901e000032155120314440e4600b4070b0a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 963699064 1250 963697814 963697817
    0x8040230031e04031e0c030203060f241810080f01020a030501050a0302130905010e0d0c150507080114060702060403050d11012c0307020d3012090c050907 68
    0x3084854411600c0b110700300d222680d1148042c1090325682c1e400210350948000c211100303910919190400500303003070407005164002c003500c031640b400609180061504940b41c171044503100d444035102e0f000d503510550507c0005030100100d881003605007880014041c0c41e10a034001c5070352002170025401c0c080039031001100b000150352030b00c00c07240080a86006802c51881401040c0c0c0400060350b84040b42c005100c07440c80f0114000c02542401401403044501019007801007034001c1c0412507010f004940064468001001074540c80540c0c03000b242c2d4200c690b0f0012400f0140140940040c4d012840e110040040441d403519800307a021441c00c1c0c1065208403090782c002829016040d0700a40460440f50389940200070040c03c039070110451021002010406001d5901501c0d0041c1081c001ca074007480c2c0107026002003130003501d801c606178141d040c078070780541e84c8104a500e04043e11001500d8200507650384c803103003124650680e10041c075030700408030f600c6400c20030006507a07100c0300d540f42d200300b43d02d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 963700314 1250 963699064 963699067
    0x30504060207050a05101809151a0703171302130f05150306011203140a0e090906040507030b0711070b031f050303040b1317100e06070804023003 64
    0x60550103490502c1c0c1c3d8020b03a21071483e21300107000585403881900d910442a20b45496208600725102c00308100030b0300054145c504000d041c8004481c00146d62040700e200b024500034080c12500300c41818000c0b100020001245440c5004280305c0c078545245d040446c1e081c070340c0301c004420384c0040d528003404104481c0454440380c075054a00c01900c583e5a003c0555070581444089280000780c4407041405103081d504048140c1505262091144608088210070580d42d58040900c002d800020002c80c07842c0704031643c10002d110000049000d901031f9620000400103941555110308281000030904420060001602c044941081010030000c02c0c0084036aa541d051028141010708400e2501c0000010881c0e000c200a4030000225001c036129990034540b2201c0502814691741c0d1540e010a907151181d4081c0d07020f2203c04202484504002c440801403103082500340c80d10352100310f410700c001c21840b02c0042c004d4180b4003100c20001944009041000024000c020040d01c035440710354807035620 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 963701564 1250 963700314 963700319
    0x61614010203190b0d05120a020316060b031e210d1401081903090902030c04030c0f051305040b06040c050904110301170606030d0e03070902040603091b0602030703050c1207030504 79
    0x540b19131401980140e41c14465455607484040d614020f403000b200c03007000c3c00100130000910030f200385c0d11981c94079a030044400c0b481d03040c198050400010b0403072180c010031440241800300f100000b000d0490f80d00c00b40038004044100030741507030350611801c10548000c00c4003191540fa00d2103680d420001e0078458007020750420708150314000814038240c854405031034081c004a0f17081020041103c02d144400359503661a460070740c07018043c07644020060101800046022445104c0780d0040d56001d4958040003083c012144042e0b030f100791400751810b512103002c1022420141c014004000e40350601d1881c10a51300040760441740000540f00340e010010005100003020b010101500d24103c0c8000c10250030310f000002d8075200c130010000103002c0840d0f10041c0d50384003803054000900a00b2001c64031035640b0640a8081c00340074070700300e03144a14203481040414902c04044143e0703510f6801903080820665003603071103078401004091130b88a800700075418509100c008244051003a40c500b42c5030351 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 963702814 1250 963701564 963701611
    0x21040f08031305120f120c040e01032d08090607031806051c020307020705011206031e05010c0207030b07140903060112020a17031c02090a09060503070b09061614010203 74
    0x20002040003400f1108108030f0801c98032110071b4030b205800b1407089074081e494400324401d9901c56a4002e19004080400001c103004c01d0880f05c92001d450100c50820448400e6000700d1600140e80c0c009213005c8041c44941894148203000c2c1851511900b800402d00113840c100000c0d424040e80040c0002e800040c14184102d41c40003004640700d9114000e40c1941404840a5154913031405034030304000c0d20001661428216801c1480256004443e0a010105480340510102c288220644256007070030b400000542c800144082260740005094480b40c13103c0c1001c0b00c0003d04248400e403100e506020b0f20000382e90900905000b020304090b541244403a03481440541c0740c107640041c00440300d40b181805c0c01c1c030001c4200c54009124401d10200d20303910505080c001e00809080380c2d040280c022011600216641c07014054407000c40031100c281ea602c110152942c450176460030b4002009001c40004484041c0400240340d2043c40d800d45546801100c081c00ca0b0030442309443d144207008071841204 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 963704064 1250 963702814 963702823
    0x305160504060e0606030c0d0e061501170a0e010e102703050406030203071b110111010606140702040b0d0f02100806030604020f01030b1207080d0521040f08031305 72
    0x108401d40e001c2c084039181240324110382d4801025280541c00000024025070f0401d421211448142d98041000b501400269a60f480c001c840a140c1203001e410039003019070003164203005a00441104002959910040d40c004d0710340c0303210b800a59901c075111403c080c4c500f8003680c0880d4001e000e0010350943c00240c90011aa0440101c10000c5d80e50006100403a5200d801c81d0191307a03007810056501e031200c0700100c1c0c0c2061103900e0100380f80b0803c4174600401c9001d00540e5692070007661440450303024402c0041c01c0310380c2e901c101c602040920000c600000e0808000c0c0c807070f4500041000800916080c04103550500400046860340500c00d000406c626002202081e401c50034601300d0344502e00000131a035115005000648210710140c200c0d401c981c8030b1340000352081c10183c42d0080403801180c0d05992030f950b50281c0b0503d80501d61580e4416441801070799922001d085120f1022003402620992465020344107680745c5201c00800400300b840c11009601135520403003015486a00c034140107050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 963705314 1250 963704064 963704069
    0x90507120b15040e062208030a0b03010f0e07031502040f0e0a0c0806150c0f030406020a0c080c0a05190801020a0e01030c1701051210140609130305040924030516 71
    0x160f260656400b51104c0014015034070a042c2c0092500b042c8140200020480b10300e01c009103549800810894942001d400921601070158002d124841107548500103440402050680c503500150042001c514030701c10308000810300c260018603041d1501800840401c2640110402400b620140711840c0310900c80c031503d68401c2d141000c903604041c2d000034081c030b00e01d01c032480c013801c0040355941c0e04030000d11813000881910011a561182d5031100a5140c0142c00c030180e86a841c0c0e81e4001940080109003d048910010b03e2444c0c50781c184001c00c5806100340d20300c4d0000d5211b5903808541c0e501d0900c014184cc4119481d1480950410030004003a15410a0f2900070400c040301ca085090107460b0005d81904c03011107a01c4800c207518400503160009171000340040508081000d0380d9180014100c40c06207806032100d402039076036055951074020041500400041f001c00c400c100e40c2a6550100003410b140a440c0030030540c03a0745400f820344100b5001640c81d50050000c484141ca40701903000d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 963706564 1250 963705314 963705319
    0xd0e010e07080105013204050403020d0905060304110402030933070e010c140c0418170406020a030c0f0210020f19150e0c150405090601030b0310090507120b15 70
    0x1303503605250300304414041c2608900c1c0510781d014003040000b042003412031303a2040060810401c52506040081d90341170720118480104601c2d0394042214204681140c0c403c940002031180011110020310000790310040c1118102d00071512552002000c090305610707010717821101c460610100115039002c41c0b00240480e01030007980c0c050415540d0f001300d08441026000202d04030b69200311001c642c2010518180194400d150002454103007140700d403440c401c02e00507800003100d0344807440311264038401c0d13021b200c0240c2c7c0243c90b030388000781c441c02c3c641c8181403044069051541c42a800f24a9500c007030a580405604005420000d200702001060040d1000131502c00703060300213407500340307460651a280221a50702e41c800c401003400204100c103c810000307848807020205e40c00b418203a0342c11a0260034890350041c4086070541d88640242d0f04140c1004000e801582146021940109602034044555014041d070005038428025000300212780100d015010615014802c40c2d8900c050803038252 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 963707814 1250 963706564 963706571
    0x10020a0210090f0311010219030207060b06040e0c030c1303050307141902061305030d11010b04021201090b040b0907050c010509060103030507030f02011119180506030604020d020d0e010e070801 85
    0x90103c0c03001d04048072202d4243c05c0240c02050390702c02c668060b20580d503140d9002e146900103c140641d15034001d00b929401074a08000040e807400c10400c03180306a02c42c0030341c1c80c094000460294640f044c01560454201d046451a05e00801440a0104607030341c02a6190307000070071540180460404803130390210018000e80190004060f011900d01c2c1002c20280c0030b4a0b010440300c2c0650000c10b5144080c00300107007200c010000d5050000c1c0140e074081a40ca449500f880880105400e150013500c0640b504142c41149603828100440020a03004646951040c1c2341c46203402c4940740c0342595802005a80ea40d80e41d00d0003d6091203003924800341c07009170076500c40c0e00100040380d4441c0545c0c04580c1d161400703204110602e10101e014007030003080081d11401c005440c0603829810681072030907604507203c5825842912880d0200c6c04164800c4d1500720f0010800590140b034980e000b024003110b001401400c2c2100902e589044400018401040b60b54070344201140400402502004010003070090 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 963709064 1250 963707814 963707831
    0x30209040c0314090c1f03090b040b01030311030a0c0f030203090d0b090106050604180c02210a0327080306130e070305150709030320160905060a0305071e050310020a0210 75
    0x346c0030221340c04000e00c1d0f81c42031485040940b40309420000940750441c030311012a00f4a410301005014081c072045001c0f1f404207098110b4880080291403c451180d2201e40b01c000d95604c803080003410101c0200d04602003044a4289582c03044480030310940200d8000c880d9143c28200c230b9003190340c1500f00b80d00c103803002d02080055150f803c10070103c44007100402318200400c0c400c1030345001c4610120303090105250b25120079035041d4030007504020001d66402d12095041c80444030b11000112402c807810b0304107140308808038822500564004601404401a00761107103481c200304c4010710350b094140d0b04104010010300c0303801c02815825440e4400e0511490900d0800a001c8042d244001420304c901c00c62403042c800c01c240c2800d07840d4407070f00c400d480310b00514420001c5c0100c480e00501092600d0000032507014100300301d00e0004e0300d5024005000c00b13401e02641d4103600c41d0b18043c0501402c481000403890380c406101d03070100141070b60b001584400039034401030f08107640660a44031540c68100c04 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 963710314 1250 963709064 963709069
    0x70501020c0a09090f0209190b0906100c0302030d0603050703020f180406150317030a0c0e31060e010f05150304031b0605070c0b010b0f1207030209040c0314090c 71
    0x4001c00c8804143e00060400c4881c0380030015030480701030181d40503041c00c3c20820301c01100700900501542c021404c0142c078401a0402004901c10f40d51076802c0640751030260003803801079810034a51402401100c1c24001e0710030101c801c1d1102da80080302c079600400020011420002c2d0705040a0b10110752150001188420341c54580000a001900b01912840c4d1942c40c030b465441424050f5401403080c00f0300760444a840c440c69441036034005941c5160110700785c00107200d024001c0300030b40010290300c02261070791300100030030503403030041905414550900c951005481c4521001400380f20380c41003007507150003080380b462403c0d684114000d0b20002103072441d6544072800c91354010741c1030900e5051050100f0440d010346e552000c0c0105210714000c140900603801101b4844914814215010a82e0303c0d0790a02c0518080e0510401060005000156481c90703c800306940c0003003a4600141810390210014003a2084008082d012945d25001c1d0a14620b10004407503128170310100a015804400c0003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 963711564 1250 963710314 963710329
    0x6011a0712050c070303090518010501120f060e0103052a13020a030906360b0403301e09120e060702030f0c0108100e0705091302120405070501020c 65
    0x14000c108940400c0d0403881d1501903400c0d11261030643d01202c850035120310b400342150b02e483c042d9612500c814214001d0400a040801e03040c0c840c181d540203d4a21944410000780160b0910661802d03103412011500007602c00d5600d00a5000e0801810045144800641061044808441040209007180100e9201d6011900c0391040b09140140e540441d81002c400230540124010109800c120002c0c0011010003003040130884001d1050036160341c00c21805038800e01c4194002d181411a40005c3c1c0400e00807041d240c050407001e94004004460f40548046006034010154012980e81030340c50009800107a1a4400b8010100f081000100e152118050301448407068401c100e502940205561101000e80b000d00b540901100c00c040f281c0c4984603150000c015100f40003030350410004010922403100741d03080300c5820400e90800e4599160895070356211010a0340c200c0e6448481220b00150b0b0f200400410600c1c004004131810703d807410508000c0360368003c604542c480c2146500035540e409 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 963712814 1250 963711564 963711577
    0x70305070b07080903030c010f0501150c0b04030309151b0e030a061508010f0f18080f0a05130e0702060702071805090c031606121505011b1b03030206011a 68
    0x2980c03511a46240340c085071a204c0c3c002c002d60103000100d50304031751f01c40540225100c0d440c110410312042c1e0322010b0520340d080c00c0c27400c14000511190241c1002c1021407001603002800b03450086040fa2143e1030b604035015141c101e12031b906a98421141c110320720152501554185407034203a903184282800a541c0e400a00303400740415a5030041d1060b14030850340100010000c51000380074403040f46202c2001410103905c00340d0340f2801c1c102e02c0445a442d10740c0c034104c010b40c45003401d41000303210381007a066504140c10f5001030000802844001035048504140200070440d450a51440c1900e002400c0c400060440e405652240401344880d0003802c4241c10400e04000c4001600c2e43d61045680c9444209120940c05d402400f102c02c14813080c030220300d8252072594554560403146035408000300c601440700780700c03d81d018540610a540c4603550301c0f00554580d40c60340c0f0a220b020741300c032641c40302602d0500e000e400300c40d034040007019018003000d030040203c0010a4102c40181d2140385840c414007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 963714064 1250 963712814 963712829
    0xa18080d08180f191502030c04030807031b1112010504020603060d111005031012030507031202070209090303010911070b0c09010903120306091b0e19240f0207030507 73
    0x501c0c542c20000c0d0704120600c611800300f011140195140d407030250140035070b21001d41e4010003400d80a04041c0d00c0340200c6c0c1c001c0c82c0b852507051510746140c03075241907a0005001241005540b9840412510382408842074203070041400b4544407042804000c08c0781501c2e05810f80c0b6906010811015a0f00c58080e40ea0001c0d00342d0390646581c48034035240b2500b09110566170ba120b0521900031102e26800000341d446204000325035070b21a034580104422403941c441000700011820400c0707800281c03048a40c2082406000409410254903a000815001041700d0305400c0c0d900c0403004210307003503281c001e59000f5003c0351030f02c078a0500300c1e88a003421840010500341540100040031140760b403040061030002c40e00092090324502038031000501800040c400c10b444141440c3d07011151300d102d1550340d594070f401519040401e00b608020b014045214642da07410204804500040e50500e0b0203070480c0700320243e42041c00006042001400402425080004640c0203450500004500040001c181c6045 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 963715314 1250 963714064 963714091
    0x1c08091002040305010c081f050411091503040b0c030c1e16120201050a02040b040b030405031b01140105040e1b120a1109280e100c050909010e091b030a0501020a18080d08 75
    0x20f505d03403020f1031041c400b0b05908803781b90b80003640e205c42500075502980c8a07800044507a01c2d4422050024002541c0c4400d0440c0100080942910786418007d552024409420f050018001c0110151448460140d54001500032100011a428414240e0000350400b046050500b0485064041e004a0142c11030b4200000045000d0101c00c0040e102c4006580c210507035881e04206095010f4107a404030030540c1e001103400414140b40c00d00809105086c5280241449541c401424101c641c06480c0c0e1030304100940342e406503005081c030002405074000c1500300003643c00c9205128984100400c1c962112031800e031007141d00804681d0b60051014121808900000c184034481d0425859194940005207000c43d041070303098101001d00004142141e400d0f48686c1c0e5034132040842c1c0021030318103542e83c0040001c0d041d10190841d0902081c20080c0455242010781e5586c2400c986c4900c50300000700382c80c84c04011811040441c5400605101d402400300102a028094800840a0311045d0301101 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 963716564 1250 963715314 963715331
    0xc0608010f0522020c0d030605150306040b220b01020705060c060708181603050d080603061f26071202010f0522061e021c08091002040305010c081f0504 67
    0x400294500640808011503031464244012662400816009401f01e82010800134035407070211300401d1a0b0300303081d07105850342c2c2e5600e0401004102450b6481c1e4801000b400d1000d01c00820300301e22007010000640003862071544400a407410410390300107403242004100d0502415004106d00380c0140d02070521101c0c68444407191076035081c444a102107a031048a440002c2c80241078020310880c0d00505c01da5801c001c079040115043c0108650042c0c0642c080c0003c10740c01424409a0840d030117044003141c01d0304d81ca078080286130f4a00d40400003451040201085075a4406015020040410310340501c072450f52640060401c0000e19501c400380080403c2013008000e034611078844032503003900101c002c640c03114406810310f0070011000c94201c50120343d0127441400020002c0c00107896804002020759918011030340008028041581d501840001e50350403d070500241015610400010984a5206400078400e03480100600041004031081411151900030800c0c1a55400e0307070046400764 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 963717814 1250 963716564 963716599
    0xc050a0b1903020a051621030504170307031e050403020f071a070606050d0b1503210c0a1205030610080c0a120e1609180b070c1106040806040c0608010f05 68
    0x306540b01b030706242115000c204200300d10800045d6009403220036200540c8140045003128005c0320018001c2ca00c01e00c0b8681340ca07400d4400b03582e20039041e1502064000b1f204d80041811265008290043c984a809001c1059018880b01803107541e84001003820f689440c1c440b03042c44103981099840000005071000038817540350010000b400014144220314001498180c0c01e1410845001082e000b0f007510b009030300d2401140400851100c0d511040d03a590001d10140100e40c0300c4d4541100300e124a201c3c40000500b1002c04000510309611455164504903050041c8001160010010130040e5000c20a04080c49000d40710840c0f00303860410b41e00d00b40c2c40c142c60020710940d0f07440400c1703104000c41100780c00d80c60b42ca440180c0d21901400e0180303050031010030901503035041000f0704e034400c2c910000302158403a010b21a146800361100d2070300e041000c0041030aa0740117030000101900010104014000c0e4039403850020425031621034265850004030383c10300441317401440d12a000100300f8580c0361 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 963719064 1250 963717814 963717817
    0xe0c0d0b041e050c030f0d0522030501060e15041416090905010801091b052103120c030412090501140f0d020f0a02160e0402040b0d0f0c050a0b1903020a05 68
    0xc42e10070101c09a0702e81500785140d0781c0f5140c0260612038850200c43c520081408240071008040c1d5482d2103051801940c000d050354041c40d100345204059842001010480c01d01843c801071030340c0d40c0702d1800e504000340d08031034409017040c005001d80e0400c488c0310135180121004c984c4c0403062010b0b00701316081d281d00c1190701c07049550001032220709001c00800c8201041d0712000c01e0030710980030203d110803c10001c803403c01c11031042d03682c0700d02c65000041c4d070312030b00c0c840040b582e03424001600e26200d44007400546015060324007141e003400c04000c20003000301540309a01c581d80e50742020b6060314941400282040d2000a4000420102054403540382d5507100075105c004260b003400707544600c2c410181c04101d030092441c0e10014420505e12050404d20317502c0c030200b600c01c600b80306001681c403502404080c09492958603000300035100284080b03443c0507046d0a4451160103103c0e010342c580401c10950f00b00c075800a844010f802c000e83c0d00d0700b0046100c903802404580c00c004d0b031200411a800d8429 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 963720314 1250 963719064 963719093
    0x140a062a11030607270803030112020607080a020c120105100504020a2f0607110a081803060a0f0501210615180204090f02070f0f051e0f010e0c0d0b04 66
    0x94801e900074000203a421140401d0503140840c1150030b428480c9017011602e82051282000e035800800060100e21890311101010f0750000d0861441c0002d9036403030703c0c00d9600c016803600058005501445041c54541131081c00f100440009010b6801c1407058081507601c2c1d4400c0301d00c143c2d40014401c1c002402140c6003840b03d003c58181404c00c01644040d06c610070035074030000b0414014080024070050182c00342ca540e07040618000c0440c079815079a40403860b44451074042d1821607034011404d183e0360422105204040c03950003c80d0b00400480c241c1c00b41c0d001078103d9522a00c10364403510034442803503007004441e6004040460308074081c1c0c24060b0380b2102c98000712103130b19009031200c001d00c40c2d940046c812119101c00c10070140c1c0742404581d04a003ea01401081c41c4542109000031178180010420340350b00800c2512400d07002d048942e104005000c03010615508054543c0e106000280700d02403030132300020701802002c41a200059003210301c292005100100200c089010300005000c218107 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 963721564 1250 963720314 963720319
    0x71a03060f0112020f0301050f0108090a031101020d020a030e1c0c0b0a0609020721020109080d05071403161715061c020a0c05060601020d050a12090c140a062a11 71
    0x117071828030194080c0694000d0041d280105041560703114594481e20350035110f01064000790030004042c0c1d500b01c070000803181c0d00c80b0b00c0e99001d124000071303c0384902c01000002107a4600040400e1003480340350803d040081c4d2401c210030300300300f5940170745d812000010035507600c4107047c1001d6440840d0b01004250540080501601c0482c0e0403041003039030142c1c102c0d03400c5000d028001041e0304400880c26510400402050010140f02c045103004aa0b041035400c9005401e1014002449100155280d041100c1640c02226000030300d00002e40c10041401480464155240461420002200b40030403441040b40c000d40000034282d2201c0f0604402d012850b0454005554410880710010034400f00f00707000381c1c0c45001d07031400700b0785560000540c010908010f031141c5042000300c000595418100c5500c1e60b913007688171810300c3c00203482040b089003c0c01c0c030817030032148034001c25051100c6c40300c00b0340041e42440100c496103001c1943d21242a840600c4004102034110103924107c80c84150b000585034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 963722814 1250 963721564 963721567
    0x1807120f020c0703050610080715030c021903120f050f01030f02010c05010f060f080f0c1215090a1e0c090f180501050f0c1602040c1e0305060102071a03060f011202 72
    0x4005c8003043c9a4003030403039103294440d02901c4040554071440d06114100040d0348070152182c0090103900103803251411801aa82d01039801008010706c1d64800030200e00080a2103001d41255506215202c4100d160340d800f0009482c2012406610800601010b40009001441c00085a21650007c2c498690081c000d11249000f0003102028040d1400380c800c86462400d40443d0042000441032030301d20f040300042100300d8444e418010564030300e1800d9020b0303008071940d00a81707075280000b02d4083c6503518020012810700d4102a4440c000d5a01518500a44012000081491420031406072144200009243c07042d610a0200a112480b040a060ba08109840041c00b4040d4070142c45140a218201155920440a80c180d03108881c803410203203080e80c4612015040a0380708129648507803c0c124104c0c800044080380b840c000030401e60010b51202c04100595a051001c0c800408200d910100618840881c03400304d0301009008500400d81034000503c140c1c4607030326124aa401c08242107 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 963724064 1250 963722814 963722819
    0x20f040b03100b03133503150906211c0f020601080712060902060405031f0e0607090605090a0506180a1d070c031403151807120f020c07 60
    0xc629800c21a259404440303100740014404601d1003c8034410701981c0a5034600038007aa803120704007140e140024600c6100300540d00c9464442020a1803281400640c0b95120718101c100b8240d00e00001301018040c08890092101d07648034000f0102c42c0745e81da185459840e0000c0d0f03103402e192815405001038602d440540c40e8a02130f4014564a030611115400d55200382c1c0ca42404541d20840c91161104608458450b880400c05640c4088905840107018500e81661200003a16001490080460261107100b48544500b000c0c0b044400700c00081000d80028a0515000342910f9041d214090030b01400080300c54207070307560401001c0a083e00800c02610f460403000c280e90100344010301030b402483c062501080020380d40310020f41c90f0f007942442140b03503554000d0494030b00c205441c08500340012948958070b540d814902551050700c124504005816550081041401d100144400d50501c1107041c44043c41d8086803a04c0e0048034000c02264070744170709c8041d00092041140d240030381d014a0002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 963725314 1250 963724064 963724079
    0xd0b0915031e160b042607060c05010e0a0605011e0311040b0d0b010e0106020f0303090c0d0c0f08010f24051c0804080304090b0118050103050411040c0c12090324020f04 74
    0x1400a4855009030315418605011700030b6600c1d06e420604100300d510420040200520440781000941d01c10000482c17040d80201c0340c9480c110f242e410803510076841d98014005640e00c103002041c0d1001c010307144140c0c0d901c0c6440308100c5502d60171815014507140c10900e0181e8a9040320b0074081036100301020607643c0d549100e0204e002080c01900c0044c000c01c031034150880e0000050720b01400c950005414040f204004001c4076452542d802c40345140102c40004051000c0c0505c4402460200000300c0d00144086e00301d03084460348181c4900200b060007401d0150790702c4c44824002d44a051341c0c80400310314500c0994400b00984d100060680100250201e03082c00d000c4060001c40e00c90100c00d00406403070b0b00056403201c01e00403254401c4c044102c410040c0398801e41125822034011840c40482c0303413010300410300342c0e01071503c0d440103d00300009020800c01121b1070b03008010f21500d4806007242c1155282c50035040300611503505006400e10324051a036880e8121102013483d2040d03281d80e182e49286 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 963726564 1250 963725314 963725317
    0x2090a0504020a060c030e040c2307020307060503280b3d120c1206061d010503010803040b0309190309030b0627040c03080d0b0915031e160b 62
    0x41c100d0041c800c070b40b0000b90281c0240b03132018140c0e034541c50301e08000001c441800000c10b101c5501ca000c1122000b01c526554000c0341f90840c800d44502c90b166600d0020f03005042c44c00031564040750400c030081040000107042c01d400d8a841585d82c003800d03210241c0704541e1a01511311a0324071980a000b01d22010304d482c481c0c022200c10b41450100c1c08681d540000074243c2c1e0244500540004900d800600318280354107075002140d84030341814240304003485040c1900c21211660000c8010400e0a401e001d01454001c210704280c42091070030619560500c119561240100d100720308030b01102001040c0701c036206000c0c81001c0e0744c000720708840c0701049041c01091050700e48410391343c60030100003150741c0c0d050200459078081601c5a54640d401d865403d00d920030400200b0607203401c130f0303070050210018503500014501c201c01134101203400b030340030002c0020454010700051074804018500c0e042c1078402007417054052596074158202c0d40220300784182892040b1100e411058020740010843e00065030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 963727814 1250 963726564 963726571
    0x504090f0b0a0f090f1406060703021609091401050907140607080c010618111b031e04050a0605071a071e03140c0928080318040c14160f02090a05 64
    0x39030a002509903d51008221280046c41c0f084884a80c800510076040c44801010003610a1048450030041a11040c0030b003982900300a4040752241070a1080c000031000c0745460b160450020061820b1002d400341e40d408032445107161907202d050354503e0710760795403060715030f001d401004041d81c6640f02c1e84c01c035009000380e000701481c0001c0310b28803c4900d002c81c42140d00c8515201030562914041c1035410498285400900e2200d21042061812000c2c0e1070004400340c00b00ba02e44a61103d08100c02c01410001681005081007424010b66001c158244004050040140103110490b180d66608480244031403a14480302c22440c0b40d2070070060340c16132003a522010401c1900b8035984681d40d04004601c944a034459200c424142282603030300c8040700300c11206070f401c03044040e50341d03480b08200c0c19608000020502c030007040c07064a0040c01e080c09150b0501070a860303d040000c02ca50065a1507016084e01c1d05882d03428545617804121041001900c91a0000d208941c0ba18000003180003406044 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 963729064 1250 963727814 963727829
    0x1d1225090516050904150801020a1124010b0c010b2d15180118080106050a081516030b04020c0c01031b05091504120305030406060f060504090f0b0a0f 66
    0x141020b990341ca0080c02d2025140e80380c61401c48140208000f81c030340303071096164000c0e1111002928400c00d100620b40b25040303441e0607512035a01c0300803600b0319010300e40030f15000060010202c4140000b803025815100302d003480b01c2d269141815a2801811201d06207030308001b521141c0c00c0e60b580049502c80080300b4a06100d0300b50340c00c903424000200320007040c4405403802031080032002c6500759007402069206240904002280c81e4901104030440c1d0321080040e50758040511490410701418809031480800410080090500c0582d0400d0018080364003100075a0403110018403a030082c0d51140f1004000b5515102400368840d22012443c1480e40401c0c40c0c20125803c09168000600d0308520f035454590030503010a05104e81180a0111600d01140030080801ca82c0d403003002e190f181500a503550f544a160918000c005c0300c01c1038111554030041d0460410086912100b02c80a540281a0200ea500f80b01c0000038090b2881c503040070b502500d03050700400d00e501c54018010468020 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 963730314 1250 963729064 963729071
    0x10e0a05061602010b060a0516150c0311030c1e0903030406030b09090c03060a0f0905060405010204051305220201020f01060602010c1803150504020604090504030c02101d122509 78
    0x401c90140d00301e03860701c00c4007600720900b4400201f025019501600b4003810740c8440d801458069541c50500400d4400001c1d010341d0340740d03201d0100541c10712840034031820039500d1514500300907407152010700800a142c0d0306152504440600e00900c00d00b0389510000c0501101c0c0c44584400014020300701c041034560058445100040c0781100c0000c522283c82d80240250582c3d4688031112006886110f198000c4540c0301d5060b840000e008004040c4243e003e10001030b06c80c0d0914082000c50040f66070300b0110395090200f440f00700c1c101c1030703190000b100148084500d070500610050b0304058404644412a500c0d14034001001501900920203c024607940c030744201040f54402d441e482014003018102c0b4403899202d0030a401c02da8047d0b41c21500040145050598030010761050f528106c2d41200002c8480d0061021810445c900c4468640c03176041051217a81c0d21003c840f1070340718200700306108246010f0300d8004e1003418401d00c164501c07151040c0d00f10450b051180d2002e10100e110f0844800d25 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 963731564 1250 963730314 963730351
    0xe130c080a111509011e2304051c050c01030b040f020705011e0207170a0302040506160c1203080708070e0414040506011d0a0c0216090b0f1c14010e0a0506 68
    0x414001c650380396030161034a040242d003503680f01c141920240b241b04144101050301d00c0244040300d60214500c05000010760380c4608207010b210b100c00280c00c0d11820b013454895800e00041c0f01140c4984400d400f0b10700041e150340d040d40061b02410710746070112082880011080103000064020704000c9624910100c00030b617288285204a20440d10003030b00c030801340ca0200602e250441d00070400e840c0a4035026007003640750000a0059401401602d441481a0f102c1c8810440b002070554001d203106105480200299140a0070364440200881c2c1040f08910001d030107203006050302a4400d2001c2e100b04201c01000c19402e0340d540e170a850507101752103442e000140280300d40303d407283c418940601031006511107008070f1010f81802a48941540100118200d080c15084d221000510202101003180b06000042c0110101082a054001d00e500d0641e0302c0030b81100304101c6603465020500c1e180314010000c440303004050301c0750361a120780140d8141d9802c1c014001900c074020080e02070800b84065 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 963732814 1250 963731564 963731599
    0xe011406090601090e06130c05040806070f050706050703140702031b07120f05100203100311010f021207151d2401050d060b040c030e070504060e130c080a11 69
    0x840b40640001e10480003031120359040459283c009002600c458910880d1012030000e541e20380304014000340c804a0b003003020072070401640390010781c40c0c00c05905124175040001c22511542d04050302c000e817150049203296100c0e030720046a00c0c800c46015065410009002034681d4044840a91441666118500798120100f40c2d04100c801c98040c040604100c3c1c1d40d454142c518a0400fa5801d0007440c6050f8203008050006501c242e00c0c29429105050851800c0c40c10815103000c0e880c10088100072000d1016000141801e04000d1815001c0c0c4803000c9280014070070f2209403216001a0815400302c4120a981c1203080c803041c580070580c5c020340500b0701c2d5444001c1c50320a441d03114a17840c00041080341406507a42e103c09020f80000b06e102d5200e18045800d840c0160369040002c0da0310659950318072001d1103500e015003811642400018901203031242149130180200c1d45590160640c101004640001c001c010107410b07041e1800007015060520380b500c0b0038480f260103003000031030f040300c2103 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 963734064 1250 963732814 963732829
    0x9020414010305160f18031109010803030403080c13030503070b0708011212360302100905090606090103090b1008120a0c0318080703060f0606030504080a03020c0a02040e011406 78
    0xc0e80c03d00d041280102800b031007120001d82404105c400d00603614400c1e455111080c5081d4040e40c0030301c2003421000c09078024000481c105a0084050760001e0040c0400242d01c02d51158202c881d5481c1c154658040051480d000b081561005000703210000b507000410401400c098424205070319140c8460b80c0c1d03950550300768180c00d10002c080b410540241e40810740203026446480e4102828928500101e004556944101440012051400501c10000c52416042c81e0000307078120300d0b2410000340780c00702146c40d500c03011300b180e44590300c04038261071242d01c640e00050140703030003400607a402d00f0209000e440d07400260040e408035010300ca5203115107924842c00c5851001403640d8010754041c2079241160207514102800119010070100090704403c20490000618001c9400050749114810b0384030440e961684200e0615003414104004248018241c13401c51449090243e89ca00e82c4080180c108110220002e42c02854424400e40d4900c0540c00070100302c6000ea0044020b0311940e0800aa0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 963735314 1250 963734064 963734071
    0x8190b01080c0f1204050303150102030a022d0106150f030204061b0f05031809060f210c0301050106050703080f010f1701022814030606040e091609020414010305 71
    0xc65401c00100e08606510402481200b41592200e4100700e0708512945482e44155803e481c15400441402100410740403110b416290900081d0314100711000007948a030407960200744160040e00c1c9082010403042d42c14251491088000c100450719100d4400407850214921800a65101d0103d0403050081c8200c5094440f29190720a250b90790f13105070544032078416021030f00108800d1300000000e20400c064a0a040e0080f00103010000c2d040501c00c000800a00051060360b988030242c903240c94801a601c048240c50b52041c920300c4164500c81c4c9010042c00e4503d42641c030700310000a540390f020000e012068440e82d07400e030307a40e2201d11800040355003e0045c0040012031030010000010403a0001c007120038a00000350604000c1c004540000c1048084000c4403020a214944940c3d4005003990480c1040d54007103042d0b00b000c10200304140901e024800303030861480d01041c40030300c0030082d43c100940c460728441032081d182e28160000c1d4200f481034030052000420294950340c06130042a11 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 963736564 1250 963735314 963735317
    0x1602060c031501111f0b0f0607110325030c0603140a0b010207030602030f060a06210c03090f031d0a05031009080702180601020d08130b07180608190b01 67
    0xc50b02e0303514803005812500d07906541846151030b185040c00d80203011038400541e50b180d0480d0204040c0c14601c0a5610a0443e00c0c40740600f0403450302d860f540c590036140240e40100d9500d88502030303900070038905412034903441090180c141302c844c20032107016200d00a403803040400c1e00300107948401c25401e46046003242c0014001d444005036801c01c4a0b0300c4240d150304144125044103540381c86403012640305541c41001000c40508000a07820122380c0c4100408040c0f400c0c0d03d40010042040452045140f010030081c0c0c1c0355140d046d00d4034402d0304040c0c40c140e04095240c40d540600d290180c011044014484e100d01501400d1000901d803031031781102240c8000d0040d0800701a28039090740145140c000403240e03400184402c0d0007603210048240e00040c00100250251705040001a2a14203070350010303010003030124100104c08a0b0030501e03030b00d03459100c1d8102610380c5a02109998a800000c01065100d8274500d0005210394401c1e160b0b8010b4036010840700310304100100c90340684220038940c50 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 963737814 1250 963736564 963736567
    0xf0402030906060d06021308030403060b0a0f0306091a01060f021b030d0c1511041419030b060414150f030a05123a050a052205160603051602060c 64
    0xa58604003811022500c82c4170f140010b140100d00d059608190407103030490f2070180d202013000d100708000d80c80380000c10041100c1c4102100c5c50601c0140240600740402000b03203855014001c2000f0038107404d042c0700d158054803d105903071035090040080d40554084801480b81084216107006003400400580c1c1028000e850304900303204040e200503c014000300c5e404014201c242074505294440c2c072484c0800c10744407941e41c0d03142018501d00e020f02d840b0001e205d10300e2010640d425010103011a02169400603900100d5512540064010314102042e903051010070003c002481c0c4075401e851494503c1100e5200f0600741040c00c1c903a641c05090001005a81b260301425225544035000d800741c2c1d074a1038039694004540d041404020885514088510700079100c41898880d214040d869021071500c0f01040701d460614066002d0070b90398104403c40d1041c125407581404400e2112200544601240c40322180d5214030040041c00c048903840300d101c08048603000d00f14800710385240540d44078003825 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 963739064 1250 963737814 963737821
    0x20f0d080a0513171c0903020a030f030e100b1216080f070812131215111e030604060b0c060610051617070b090706030501050103020a0824031203060f0402030906 71
    0x1410340b85c0c440810b02020515032544001000c03038901078010254829809010203204528018064800058003103040c10305040da0382050550020704e0418161030100049800d4080f10003241c0c031040c02d01082d050078000c81811445d0a40512020001c0b07600183c101c500032a003200109443d01c4560054035140d400406101208000e510040c1400d01422406913403040d617680103003603131101c0109080307032118807810352620010b01a10545050280240c11207117820f03c0081c2030341d403240d400c0450f000c00c6100403000ca440c07038076254402c0c0302404004410664840c607102d076480d030b9040c044400c41e218106100c00126981c1c0b040c82070704da071801d050b002503080c40c60720383da2101003103034541c0105440d00e0188500c2003c61201000c5c02d00520820003d17010700b03803c0000050170390380140c20036411706004000401d500c0b640141105ea10000b44a4200449811511001c204580c0c922446500d4490444080c5003802c0c03150086d8001c007004c951a0342c906104000b4001a40021201c1a21542101000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 963740314 1250 963739064 963739103
    0x3020102120909060d06110d090b0a0e15090f010905030d0507020a0201080a1109060a0f11161404020d090c1503060f0e1302040f140c07170a020f0d080a0513 69
    0x10b10700040c803c035000b06003031001f110b0010190700851000800c00340c885c0c4002003400041000e09402801c40003081c020031443ca1300585d90b8036a801214001c26007040001080304605202034408210100003d000e51040c1d4285243d690300951220542a443c000200d40520b00000b05060309075810786400100780d0315901040000d0003890302c20304c800e2804022259540d0f4a10300240501c1c0c1840d00c95658001c4004030080c4548060440541654041e0604d610480422f900e0003080350001e02008501442c103c1c00b10f00640101d194011701d040c28103010801704203440d5900c0c420f98282d00000c4280c040041c4040f01621000d200f0b004552000307600620070361040d94080380c0d01008076145026120240c5d4086821100550704d111189070f41c0e112042800d010010095800030755015446042043d65255540d80c89804078621440c12400a025010345001b40500506071100c2410f403585140a107401800d10b440842d90009964580000520440500880e000d41103801042054080e0403902c0ca = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 963741564 1250 963740314 963740329
    0x2040f0302010f090e13150b06030a090c0e0a021c05130f060237030911092508070f0f020c01050a05040b19020c0d17310302010212090906 61
    0xf02c40040003c06800440c0d040d080880320b5004584900c8a40d040c0d07601800d100e844049440c0c000c800e028100003904049641d44016650880c090420000307004056241103481c030401c3e58411140344048000300040c0c8401607010701501044010355200c503054190145088400c1161002495080e0b41d44036400f198040c00001c44044c441c1d0030051412a404074035240304c0d041004035404000180503252800340f0482c0002912100c00d0078244a404031650300d240030205050841e6000314000c0e400a9140c018040c000c0b034181120342c1806408640a2000910100382110460003040c0284940e01c4514403454034202c4141c3c03d9409080a03100340c4004491551203210310404100d0180804203806042c6001030030103184030b286040001c4240c2d00c0181c10108242143da00c1400c402045401094034000d1020280c0b0714080300c1903035000c00c0015442c881520b03100c0014803030800c80701c1c041d00329194607040c01070301d000342c08451201101002d591074a20a00b801e480e0005860004900d542c1001503 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 963742814 1250 963741564 963741587
    0x10090309090203090d0906020c0109120f0b0901090b01051512060103021b0102180607050607081e1e010503060c12090109081903050c0307050f160c0f03050f0102040f030201 76
    0x1030800344140e510076180e0305a0b00150f80c419011740107104a006030035040310f02e07800101000c0c00604132301c555034400649184400d20840b680c58160b05100e40c20840d2404840910300e034031a0510f2004d04084186500800c0c0c2030000b261100d0f02c280020400340307001c007a000411130b410002140340a003900419602004080d220906041c0c003408513000e401c4084030403041c070ba8440d50006032200585072194241d52251090640a8582002004003050001c10115441030030750500d841540c031416030300806040c2440c100101540c51105208401034900600790f55000302c9000d484d4107903281c904068840c501524034012041080146869411070444850742c0f00082100002c1c002d10036880300c09030b540c80124a0f4103000001c00407102e03400e81500c2401e421040400342c0714110300e0513001c050072900c51894901001240800d44045c0c0e081502120b443d80d540c00071100000e1540c40003c0700803000c0a01046809000d02601071800180500c00c0e034045400c8224680200b910307580054a0402604c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 963744064 1250 963742814 963742817
    0xb0c090f010f2d090906032a0315020a1229030703021504150912060b0f040903030519140403050a020f0303071e021603150603020a0e0a060611100903 66
    0x140ca904043e02024007006405480520800030108014100030006596500142a01481c2c05002d002240c05004d001a2440300c00c0450340100d84400881c3d090564540e000820f00040c107144c0d480c40d18900c0e0081c3c00b4201c40c6da2203c006150800f001070302641e9014019085420160b0000030300e0395860000e0ba40b1045018003a12020b0303460360045000503000440940c180d0300001001c000c60b580c3c2c031b08610407428452900561031403e111100c5405450303514050066902c03800c1401e4541c1ea000c0c0d580c269401e009000b000350101a09c0c028028082c1151000141c040c43e40800c501c11004c1c1c042e130300078000000b02d07a4030145d4460340d041d40c15030840036440046200f405a03000308080c007000218001c60b0107071200417003181c13080c01d10030b03881051051200442d0003081c0000c6d14410011820000c2d203622106e002007081c29030b001c09006114503800a540140d608800080c6420000412130048000c03001c140086529000161285803c01d14010881c0d0301c26501105000c07102e5201c0006541303c0e = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 963745314 1250 963744064 963744077
    0x5130312150506031f06050f0a08070908030705010603050d030204050f09090c0d0c050f220e010b0604030c09050c030c070807020402070209010605210709090914030304030c0b0c090f010f 82
    0x40c1d0b00460001d070000c881030b0389030620702d04c44500018019034000c002040c80d464014605404104180b0b400e000b812118414003604101044180380078140d010080c050030f40c00c5940b500700380e0a000703028203420f11043d100c500411907104500d9100c1c0c0202c501b80c0300003030b0610441d07544d14014410300c203400902c203000304d004003580c0718510b0743c48840d4080d600d070040c18242c80d010b040c4000c201c03000304170010142c411701c5012212000130b484049403410b1080340302c00c00140480c08008190140c0555200d03140e02c18030001d40842002581c03002103003517403400700c01080150b50342c9661081900c0700703448007541c8060500541c000034001c4001010010320290025091103043d60100e55120400e03040880810408603c074074444040340090550101c0b04000189030b400c2205014228070028040e0800c1181c6071081e00d41408610007107031030707445103402c1101e583e8a8107003030050564003c03400480344c1c00498008140b00000d00000c0d80d0129100900240003500340600641744d540c0600f102c6d0003130086 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 963746564 1250 963745314 963745319
    0x318040608152a0304060f1a01030c120e0f070f030317130209010b09030c0406060e1314070810060801030825020901030b090d1403040b0403120608100513031215 71
    0x142c0003c3d8075078018161100c5031241007034a04181591400030107000303404c0c42c00c5036206800100e0a956004a002820700040d400c44400b42140c40c000d04030b509524180c02c1030005c646850000510010107c031103406d17542100c1d2190416049042d203484058002a841d4903884018007102c01a035070044084200714103895901d45c0400d9070303200700f42c0c07003105026000700d410151070030f003848412140d036001c0f80c041099a042580280112071804040c50181881c00d122918043c0740307610003414413820a6400b1214500580002d10781c0034221103e100408103410001003a5000b1140103068940c0698018140b407901600c80d5a42041e10308802e100101012404015031140e51000d40070314003030240312016181850f900d528200581d090f15041140e00320350180b8505800c015650050351125585a0603180d5090440c1d44d4005214102205403030301d0030005000741c00164544420700340401c2400b01d43c0c6c0352041c50030007007481103024004c141904800c185800c0154440130151f122460a40411034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 963747814 1250 963746564 963746611
    0x307170d0e010204060e120a03080a1107060501031b032604150e1906200c0a06020c0102010f1e0902150403060b0913030f0e04060e09031804060815 65
    0x1800d50000c1d20240c0d60001d0240702042c0c1c8050790290091040d038581044900f425041d0b60380d0018040042e00300f0100502251525019070000c2d00044890802c0d6a2070b800517050a00060000703200445000c034000c0c160034210340030541c0d802d00302c07508056940c00011402c0034200441880c0c11041910300b0b07041001240ba0703281000c0110071403000d0b41d140d4580300000d8007072001044400150300c2001c0c80301042001000d0348200c6d28146940b006041c00400d0070607410081c6003040075251030380d20030014900420f4440d130004080c2200c0f14244c0c024019070a9041710711084802c2c016401403109001500d0b00c10244141e00710750011440a80301036031840e410080482d5580058004844082c1c4400c107002d49072500e80001500000d0700b4000119880e020395010f004ac1904003120018007000381e05c1d1404941c0c41c2c0e0301060080c440b00e807121450386004019152030758420503400c82e208001c141300010b2742c00c10b0b1090a0560300d0388002000c080060010304000c085005060318a41c3c0c019074158100203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 963749064 1250 963747814 963747821
    0x605010306020d0b01031122170a0615030b0403081e090f010b0a0503060402150403020307060c02244302090106030c0e09040f2316080307170d 63
    0x290302a040058983c401d40702450b0076a03598498940c1014109800e605d0003034000811a0703d20408400044403080c0c454101240c2c01d51150300140005203806d1344803c2c00500800c00c4404c05110b4001040120304000f103403520309006000c00f600180d0b2b2540040d00190080440c9500584000c1003e00d803890740000c00e45d5800710803280c41300142c1207514410b58184003402440500142124440911410400030961b6680002e0010348100c6414107a40c410b440c0c80e90480d0701030340d000340503900101c1c2c4581015001c1003c12508a00500043c1814199807140c0f038981400032005109040c0383c0200d2254516180503140c0501c1128047e0b850214040c40c05410403030205481c44070002294405801004242d0005a0054040c94148400da1781596401a020b00c1e00d62400c40b811702c466195401c1080c414140740c0c1006250b101400031400c01c0b0034002400c1050418034104032041680440c10b11030800f0348a00c122000e40d4818040c10000558107600c081145954445150800084074850702c00c1c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 963750314 1250 963749064 963749069
    0x10501030309140d120c0206040e07050405090f0403120f020903150106080906090601120309081506040c020106121203091e1a090d0f0e04090b090601090903170403020a060501 77
    0xc12030740e0804101d540150141640e20010451340640300d815103403680d80312020081658010403094400c60402c5682c0c0c03005031030180c013144141504030300d810503015065a10034003420f4464284000001d4074032984000da18426070341941c400a901c41800100c0004e440c110059100c10360b002e001d400c0c12500c08110314403130b00c400080d9064941d49044406044200040c3c0380c1030990708403d082016a11000a84c1ca0440c1c1945151b40c071004000c0c2400c4034005a183c0002e0b80c0740c001d850981d81d404100f001c400303000342c4003150304024030111810240d080703543c0c61084d44410214030104a020a084414601c41d40c501c50070040f504021f0b0b50341d0044800c010b07407a04903c0d003503e12800c07000c1c0403440500d01001c4036144c442a2243c14155044e42d03032030040e000d10b5001c203c01041c80216092142c00b801d200081d0140090020701c0d04e915080c0e0980c0700c125001241481500000100c800d0f44d030241c000c0d46034241d01e80407070140354500d0752138549030300800540039881601000030010302ca5100700c900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 963751564 1250 963750314 963750317
    0x3070c03021309120c050709050106030c091401210b041803090801091e17130e090601030b040b15152503020d030b03210c071d01180207050105010303 66
    0x211030451042141080d80045038155003031900c20b280000500750800442d500341a41404489110700c1d151051400c01d5541282542c01c0c01c00300000307050768054101c92000001c80d10b94001c00ba446445101c54100c1010410b03002640c4202c0c00020b140342841a00404100d2031b5002c21004010b02c0400c040e01d20045070381800c407001c40d114800b8550321007680400790020400911000c0c0164503414002b01c00b139010600582518802041040507000c6d05c3c503001d502040005481c2d49450040160191a511607000a0356010000800800c0c001c160141030b01d134040500c11060700c070368581c2c005a00e0024901d01000f802c16181c2646507039000c825000c503010440000d41e0f00c00c40040011600d040f40060a00410081828075000980101e09002d1042d00c5181c0011504544d40019143c00e101c0d02100c1c0e030b03405540f800c0551a280c600b000307084000403c0300320350a155440064592260512981001c2c5080040060003480d909034251090395401000140c107050058031158211802a8011030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 963752814 1250 963751564 963751583
    0xf0c050106031a0c04030521400503280611041a0306030a020103050a09020603040515070c15091502130509090d021504020a08030703020c09060607030e0d02120307 72
    0x1211000c3c0108003a901c82c4100c1c04160030980385584095850410f00d0a00c003101c0303c403101401647c0803c00a9030b0140d01220614822140c45c0074420b00c042009645501c2821201004e040c02130b0711000e029000c403000500140303202d1025101c5501c2c000f054514050302809003c5021002ca0424012066498401c1290a070b072280f91441003c0c41038584001601401014810490250781c00705043c50195028240800c00b07a42d41c0e00c880340201041440258000c030080240003c0c841c0000d014170844e1404a007031041500c540704103072120a440b48000b860024410098050351945030810741079107220744507050007503d513410010180e1300101c00c82000001d44c06c00c100200d14050b89255000742000c80542054000010000d4654101d031200c0c05034000280045001c644500000c4001440d8040980703407105e110340790080d00c0c0c140c40c10f11a4486c0f0304d014003150f010b2410604482259078141c60b02c0484a02d400180224400c40d440d083e80e0261000492003400c41003800141150351003030702e040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 963754064 1250 963752814 963752843
    0x8040b0f090a17030a141c05042307030318050909010b0405060f1e0604240f1e08090a170702030106170606131104030b090c041104060f0c05010603 65
    0xa24094140c1c801044000c41e9414030f8100b90001c405c40c0c0c00940c2071314100000e08000094060030b8801c0c9030b0740110181526034103910f2010309902c258081c5d80709440414000303090392000010410032040b84040354010b40c408000180c068141095001914009080d01d959150001807049408032080760040e51a030020718440c0c070b0244507080d8013890454800c1c110b40c0164000c02c003180f1084d40440d036868940c1204025582e034480c280d4001300341c611003100891176540c0c0030000016a0300324003070201c1c82c815482006240103080307040d0385081000d03111802d90b46a00b402c071000c4401502e400564096800e8080114816919200ca40c40a480c049d55450700180305160071039a59034801c0c0c03c403000481104c3c410301e0307010503241e4001100f111451850103d02e18050014504000301a80d1040009800402c00034640e40300d911804c0c8001c10381d100d152180c01400140e4000280c442030300d05040009202c01c501541030b840e1031404a10b41a00b4100d102d64600c0c1c01c442c01900305503040c1ca800c4054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 963755314 1250 963754064 963754069
    0x1121e030f11010e0c0607050c04020f0702120609030a0507060e0604030930080f0d02031609050d03200a0c030602030a050105030316200310050714090109030f08040b0f09 75
    0x540c003035104402c00030007164884804968584144803010b921a0000240d01f0302442030411480c40011001001190740d090082c580301447c0e841070344202e0161800c00d00d9070045d00d90102d046032007a04040007071494803416000407100740c0e0101c10212441c9a03030340c51000301c00e40d040002c81d00c9640b00351240e900340c0342440860110102d028550301c8504414100d40c945042c40d041d03500d02c0b1603500200841d00c07a44031046a03412406603001114616101108000669a04103002d000c00c81c900d0300e504410580750b106011070006540001307004101402103407118a0121040e00d610b60107818280c0d040c11006a865406a02c501d5001755003144d008014000f05110f58815140100401c41c0210b10704604003800d18071034503890780c019284201d1458040305000b500c0c1001c40c12140024295085c0c5400e11402900815040d918400002c110303000c0302c0c4845022008071407449105031a500e000b9031031a034a0440e00060b14000b100c0d8900706000018400b0f19200240c01001d000510180c0c0b5210050b00303 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 963756564 1250 963755314 963755327
    0x105070c03030605030c06041206020c0a033b0f0406080f060a05010e390406050c0105060f0a1205030f0703020706020c0303030423120f0403140d0801121e030f 70
    0x4c1803003500101e480340c1e01d50791901c0846046981051554019035002d00b0640001d014403c1c02d030115015207050f0744101035010b401c0a0404100c040c0802c0c2d0301c0e07001d800344446c0060070800014907a142d1489000d10b454076010b5620100c000400100e5140d0300d89008500300003140c215420140e105030f0510000c0540c0d405024050700080c600042c0381d140220036103044070402e0342440c09d000ca800c11240b10511007181180e04440d03801591179503803a43c902c801081c0c1c0d4081004c2900302c0d46030401146c05460303c02030342c00c0201d41c020048008641003002d800c01c0344c402e800003103035144001c000d4484141034a1001d040c20a000e90080d000d04c03407801c1e00103400e102c42d40c100d00d03100760820010030001072056182100360850400ba003441040ba011034180c50031110072420200c207500452004820b000300e000420030750307201b03401480c80084140702095440341c3c248202400324031748000510641200c4003c5c2c1e00018041c0803001d000c80c0006d04801c1c00400001c02c02d44c001900066840302c03a540000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 963757814 1250 963756564 963756569
    0x20f0d0632070f0809160b0703030f09020a15090f0b03040312090201080406050601020313170c15091009090e0c09460f0e12040f0b09040e0105070c030306 68
    0x104141000d20707281600918202c8031811040900881c200845d994400030001c03c504140c5000c0301001444d21542050259041400118006814500010a140311a0055000707451340941044e0004e0b05060603284000074a031400400c02c40c076044005004c1c0c40c2401420014101c10008039541e00b01810002d02d8100c06115507140281005140300041c0d88c4918500d0b0320a0b0015000100b0382c5a10340102e0851049040c940c0301d0001c0800b010400c04000b20041d01e6030401e1000b2920808415001c1c45189210300c2c143c0c00c5207241c18804800c0509100149180d00b62592400140c3d0b0b0381c40d041001c04403099010b031041180d2002c1c1924207141881c0d12282d4100c4401c02503240300d5180742d0a6031402c41c0d2075806200b10803144280501042100002c000004401d4440c01d20010605111038001005403408c0b140d890710840302441c101c500003508843c10b940f60f50700069603040c10020030b500c4991049407c10340199071404810071200c3c0c2886583e00238080ea540307501c804006418002c054407850b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 963759064 1250 963757814 963757901
    0x2d013209010f141e0909100927060209010302090d11040f0603051f0b03012a090f06030203071205040b0417040b180402090a1d07020d0c020f0d06 64
    0x11501400700c0e01480540b84040d004013000160003e4900c040c400070f00607407030b880d608281c0c0301082c001302e540320516007020346645504c00c0054440f102d40d02c1c000744007041c0780c0070941603c40c61000042401c94004124040b010304002d1300c3e0451500101c0d85450b031066007668007070b2203a486a5102d14060160114000350f155082c400117040d40c03200ca444808104004c01c5000c01074288204086468004a03401c01000b03000300320302071106202c00307200c08155004000d08803045420072812400749095806031410b454404640c1401c055055000358406030049040c0700b045001921a00540d000b140e114501c40c10b04c4100e01e041505e403524650303480d6203604525050610051007101010000d0701c5401e1f28a000d0b20000d5003840c00810000d03c80c4440103600000c07a40300109408078000c80500c6914003801c5030103140c0e40d07031040881c5c03190701d407403000000110903281460161412400445403d50001c18242c00800705ea9a240c044a030381303440d00b0480c003205201907042c460b6200030302c1c09048040b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 963760314 1250 963759064 963759077
    0x81b040b070312020f120a0906020d0e0c0405151203190e12010e1c030905030415110106080d050a271415070605101a07022d013209010f 60
    0x6400010a14090100001002206d480004002c000250449000c41e60802d40840d95040e008100c48060484802c20b40700c0384c462103c0b00d002c12b0805114141c0b003030f1a080f84541440d848401000030700c0500c1004490680700500180c4040e0403481c21703110224855417910703600048540148006045109a90007040c0d152070b131010603110000c0703101c02401068580020a0000117442a03008000120b806003c0e4480410b000c1010882d1139200000d100e203948500c9002e5904415441c00d0b1042c1c1d016200058100b0b1080904030781c0a030000d4460380c443c80c24862001c1d41120314014049140700100500403407509820010204440980b400c42481650500050154040b000c0c1340751103a800010f01155644001584200000c0080320180540300b100e11000c80c4042021102074101d40d9003a486070901400300c0c3c0401e00c0301d010084508910131701c5074a5080901006450400c1b419160703052440e665501200c82642003a1006602420007003038a84410400f0b0006051918610340d44083c480c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 963761564 1250 963760314 963760327
    0x515100506160b070908150103052107020607080913050103020108010803120f09011401060206040209060a060c1103011b020f1605010c15141806070207060e01081b040b07031202 78
    0x1901210a103264000e00ea01c12291558a0100c98652246d400340324036002e000c000d85200103941341e0250483e80644200d400c04004140618880c610030708040c1d00c00281000100014101200a000e495024078000c0d8185a825000320311140110f5184165031540c0c1c0740144210742e0040d0342035001d0107144008500f4525005c0c00c1080c041c401520081c0d030a50407074001841d040e025004041c50081510b003020342969506d10103540e80c0c1040d03600700c0c400d40000c4002111420b02990650445025540d0003544140549400982c000314400150300b65480c1d20b0300d41d10842034a088052009280c0c0d0050207446015913855060443e050003071032200c010034100f042960707880480407030300d290000716040f6514192484900200003000140050f030080c0010094030700d1803600d401c08844804ca003a02d051340d49540080ba00d460f642d00842d401701c0c803032000851041d480349905a9016103003048034001e80c1d075240d8400740e064209501c89200c002d00000c0d4007041503400400b00d62000e10180040d0306000c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 963762814 1250 963761564 963761587
    0x4150c110c01110c040204080f07140109150e120a031d01080c0c071806080f060c0a050f0d0504050c120a020d030804230313050306010308030a0203130515100506 71
    0x1d41012140b410000c030034040c841c2541080c481141e0061004004561352941ca40c1c900d5151b800403907503101c0d140541300002806042035285000803210580d281041b444c28070f6041c0d4980420059000200481d54442140302d480d0a0b00055044080100a24901d5403c0c5401000813180300182c0896250030f80b8510810307600b0402140e0010001c0b08000d81707c00d8a00c50300380c5485803541c0259010100710520701300c890740660140056441500c15114568004250300d580d81100340c2e000d41c0182410021000f0f0300e84a074024000001e4a0b0010600c0e169081014a041d0b4100f51070a5401d5004064664400e241150b46030f03000300403040140c42d4a055540014001d01c0c04c451029044c00b0040c0002010021031585440e00781582c030b054540481c400303061199803130300154070201e40b41a52420105a1b4030780001d402d412254440c100a141d60756480ca070070003a401c090700c24803801c4c2500c10001c00007841481001845000b000c4011058500701c01030b40d0820402d94070040c02000c04225001d1502c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 963764064 1250 963762814 963762823
    0x10204050a0923062b0b09210a09090f1508160909140615100908100c0e060430050a020d021504061106150604060f0c0b04150c11 57
    0x84045410540a94a400108240440070a20303045c00c1c10174003096071521200b200c1c68507a003a01501603101c0c5a03841492807035440c1d1f4520018081d030351018040c001e2502c1250010300c0301404d139240c0422416a581c046806070b403074404a44981c180c4a284000c0b402d240d082104000300071007401440d00ca00c079038074a503c15800c580211306407640c07618010307010b0280041c10303150b4020325042121801c2c60010045401020314816142c03140c0c2d82c024405402e03c0c4140c1d140e100740c0701110f018100007000300400100038408101c401c010b2040c0000c500e412561203901030700042c50040301401d90f8045140c1074003003c06c00d004104004c1c0d064504544042030000940c40811581624a40b1107000a0300014002c8080711700094080d0b0320000c0c1c0031440983c4400b560840d080010304961580d1580300d403d5500c0c3c0c030004e0307180d80c200d58207000402142d84246211402c0c40d0203400d0031450301c11b0341d0f1665941d1120444056420303d20700301010f03801071158480c20303032102031600d030030601707500d43d03034111030b02d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 963765314 1250 963764064 963764111
    0x301090513030512070c1e210207050d1a07020304170a0f030516080a120b1c080d020c2407020607141308010e0708070b03010602030732010204050a09 66
    0xe1120130b000040586000305001185250020041c6800410340d100600c0098002c41c01201c0b07005941c0b0080003921441c0c54a808110303e1500030b050341f0360828013841443c6501080c1940c07005644410420401c7c00000150b0003004c0c50341c09582d40d542400074a144249280c001540c0306d609c4102c4003408660404031a02c100c0e0741c1442d180d5595280c00544030320307030049204060040e0750001500c41000c0c1d000364a000b01c1420004080c020286418100225107006004645119012051000014004000800350b0a003581e1005081001d060315441c07038052070702c01c0f002a17404070100c00c4c0f0302032451610589c0c2c448110320045c035451611180c01070188910b10b0b5840c9640f04041503013201c48643d0700c6d482003d0003000d00200548485000c00c07a40d00d5042d80701d0040c59005014012030744010120840307050302d881e500218548503460303a0340c90952140b1380a0200b0085000102c000b02c5000b1200c80314513800c408005a16642400c0c02c01c07801110070f40c007212040e440c0c4500301c5081c00c4121212040b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 963766564 1250 963765314 963765337
    0x112050d0c02011e1d040902060301140307080d09050108010e06030a11060f0d200304032f03120f07031e0c02070b0d05010603060b0c210d0204080303010905130305 72
    0x80c81c00d200580d00c4c04982090302c0e0044010341c60000600307030b0190361a440685005080303154400c0000502c07044541681d40039400500410061140c151a80c01c19403030882c02800b00c92207103588400e882d0600149610040008000300b00412880d03900c41e20580c09085608000d00032030410400090ba25404031100a00c044104000b24102c1c1c3da40c1001d540e4450082000789a035000d20000038030040c018288008407500c210b22000070b200b19101d06483c821079060329500c0c07a100810002000910100000c11000c00030181340869004050018000001110003118868200a0301000c0894401010381e0304062816008080b5030a500ba01c24000d100c049400003812401820124181041a00240500030300000d11401307891031540214101e969982e000c0003000c0d00c69801d100c840c070030485041c5032940070803616403d0b000000c25100c160220802710502e0711a02a036000d040ea00b00da070107020280c001000410815202c2d00a00780d000158800d021040542e90740c1c06401802462303480b07403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 963767814 1250 963766564 963766577
    0x40f08071a060316140d052d07060e1e030a020a030f02010305150105041e0b0318010b0906061b1c0203040609080f0607120b0312032205030306120309040e010606080112050d 76
    0x7130038041f050000901d07517503414200141a901c103810494100c07981d81a02c0d6030307038030406000041251042c0d51800e64203c1c01021400320050481e00404032040d0380c28600ea05005525403400141c0d1811030340c1008501c10311138451400014000902103a000503e030030311511407001050000c0c0e07448000c80d8150351080700040c50035000044443c1e11072055030020b8040100002c240401172918403425030200742c86000910100b201c0209100303080d01d00759007150b00001d0510125100c030000c1054010480140c004894003100c584c4160f000f01000a01e60502503000000e09201981d84030f0300d443c01514400000302150401000c50a50380c4078000c1c00c0324108401c40c140e6902c031040a800405403c8030082c11a01201074034451600c0691080c0d03505e4100000c60002c0c0300802c01010316403007202c1e81090140d811941d405040c024440c02900c100782050100304141d80d0780c0e6590740b180d00e55071101c0c140002003080c01e00784054a03402040c0c0200d610180211502c8001075800a201c0003103007814038100e03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 963769064 1250 963767814 963767839
    0x4032717010b030f030403050f071a220f0510020102030f04030807021c09090522020618090405070510110c040c1e03141e040f08071a06031614 63
    0x803801858542e8040c2d506001c3e20740c491044110000180058078002c0e01a00c40c4103000091450741c408a502c2041d0030f145040c400589800c005030081e0800d500651042d0340600380300700c1ca90540170320170703000a401040b07a0a0288800d08002d481c030410070400340000c528600b481090103585800c001c200a040080960020b201d240c070074071a142c02710602d8203030302c2d100b4150407002400c0500c1d00d002e150320541c504400504ca9505c20504038a501d5000c6c2a030312294052502031040d030794003040c000405407401e0720b07190440d81c4480031030760712503800344025141060420307041151411400910208000c8000c04614811902060b034040d001c3d41144d002a480c10040c00c1900c404900d00304040302045001101d000064140d002501601c0e100382c20041240c4d9807a528618021f40c082d00103200b484000d00003000100c4802030740c0e40031070040c1249410003580d0358031100c4000b81032440211954102041c4910381c20104501d6518481c0c02c40c15550f4a4100304541c44280a04c051040c0b0500084410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 963770314 1250 963769064 963769109
    0x30e0f06090907050a020606151b070b070c080c0301110301142209030315290c0d1206061707030515031006080709050103030e0904051c08040327 64
    0x1210a070007070260034850545850b07800a4032642081c456071015011b100005561403520001041c0c000300c03840000fa0070082e84503940f10619008100744043c034070a0040108955524001034000c042c413602ea11a4800d0800800078100214240c00c2170281c4e041c506001071300d100b50f0003668150380d80040090042500c0900149040742c407504e500f40c0c03003250710b10041507030031042d000031005a010313032401d1000c8829071140c02d407808224030652040801c203031402603001101c00b501c25032503da0b13050028141801145500d0801003400f0039034011801030080c400e900c5280b40103030720041109050524410210500320300011b00010203120400d5580e10001e01c519000c0d0551400302140501220040d2021a801c40000c102600802011b4807982000060303030b0760903018541c1600e50541d28480c0860020003404412103010b00200d0b80c40c01800400c043d401660321481a0201300c0350364400baa400d141c1809001105111010082e00070114094203810903040300a0703048031100c400803880c2c110801d11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 963771564 1250 963770314 963770317
    0x70512074703010311010f1202070f05031914130302010c03120603080d1103190903143f01061211040305030301150504060e311a01050403030e0f06 65
    0x240101500c0381c4450703124030341101d0805036069a1045201c50002034586005561142e0b501e2a04400070300c40c004a5a60f156283c1c01418903030707202d00c1d08250008065903c441c03c0d5002003803001a001191507040c0e205c294020003040d85c442d05910307020314240c0703442d603540d10089180c000079040c1328030784001c1010140700340058411140034403030803c013454580ca8a80b1305580442409010981400c0d074440440d002d600c02c90b405800004a00420429609080c0d00541405001030b02445100b030b281702d00011203100100048410414045910303414880080c0e080740000d2010380c2079910a10784810030f03808000d10181550542d04281b030202080c24490400380008400c000840a80410000100312002000e54166030080b400310b441509441000c8880780154840c5c00700051030802e880304903041a143c101c04440c400000300d521403591a9190380c2e1101d0040103003004559902c0340f001907449000c0040d50404003481d04030b2900d0315544006000d018a0742202d88603080896000c507503540c4110 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 963772814 1250 963771564 963771659
    0xd030509061b0303090c101809090206070803040602030a060e13260f041503020c06040b09100504030e010f09060f1b0c120b1e0117070f0807051207 65
    0xb070440366130f49820310040c0c5e16821401c01c014080d804074a400341165015800c14400c80303041005629180385015011030240201c00c3e020b0f41c201e0000c100712808100c1060013940300c1c40c000c07080540d580c21320003040e0007201d0040d408140150701c0e00b01480303002c051001e8036001c020740210f0303c100243c1c04503a00e49043d4100c10b0308210030034000143d0402d059803610107002100c81020440070f102501c40d1055003030b4807a1240f050456002080000c0000c0d0001c0303030b065000706181d0112400321450104030000c5407800d40f0250302050000308500010b6a100c3c0ba8610380c00110316010700036a25002026040800300060002482454442c0c03180c1c03843c0240e10001d4054000e81c0d5180101d41e580b0703850043c0048072400b80c3d040010720000032030743c19108489980303151003914030604580c81c086d002112290700c0f00404404d0302440318001521509082c414020703041e00005080b4841c504810400c007900b898540e29001d1300f140301e080084c0c07280c449006400d05004101c3c0d41e803d0001d210883e002d049001c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 963774064 1250 963772814 963772867
    0x20409060b0304052b081f0810050105040c051603050f0f030114150306040c022a10090308070f060b04050c1c060510050a02070b0a0801060314090a030e220b0405060d03050906 77
    0x4030800078208e40002070048000c5c0716040d04102030b98071081400b090311080d0700c1c041d010070420050301c00ca103044104d00303000c07843c020f1424034107200da5030500101590004051401c101c902200511545d0300000000e5a030346130448010300e100070300100000060000a200503c40c0c0e41c2c030302e128049140203000c52000c0286039a00c0212142040034025102d50720101c20382d011b0812804050801da003d64005401d9a07085980f49080189581c0c440301c0f80f201841c0c044560b540c90f0a0158a144c8079806100d004055a25003561034225105901e0441360f6542040408142007900c208001d40320780b8a020101c03004c1c1e01e40780b07070781d000500800e07490700200e80c2c44020810310000b8007943c400d6000044c10b0680341d0a81d0180180444250401ca05000070780340040300d5008986c2c00e50002e80100e980500302103000d002d00304510785500d19a44010002280c1c1c08001c1c1c3c885202d69200c2c5000d21819500010845421107111048c1e200108a030140c440c286000e184e0008002c040030104289000428196 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 963775314 1250 963774064 963774121
    0x20a0803040c0303080619150e04020703020619090c0e07030207020603010806191a0d0203120c1b220209040f05011418061012020409060b0304052b08 66
    0x151030000c2c00e2007520721041d4009142c03040071501a1030a40158002d45100a40400c2c185c2c0c100010740c591190301d100b0b141c05100d21070824112a8407540050000d9034007a4004d0310441ca048400b2a0420070013000070396080d45070540341c1f00000e05070390240080d1504640c100c1020755684106a0091040000c06035121304080000100102c000a89034402e100c65100e41003e0307a4050100c2c5c085d56260420100c024246600c0012503081c0684182da600340001d08656042140f10059905a0b04c051007400b075503044000a51031000350481240070b4920140c81241214049078401c00084e40c4081545402d141c000440f101c0b290b51b2500034406071040c0a404005650355081e9040c98103181661f80d6004840040009580c0d04102e03003031600c074130400f0b802c0100084800c10b0481d510912604c51314243d039404d1101041e100590300c6180d028004400301c166480c2081e0400506d44024408031903e942e8020000d0301d019a61440003044400c0a0f08110100303481e44403950441045440300b40c03040d03041 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 963776564 1250 963775314 963775321
    0x30605010b0c0c0906010f0e22020d0608030c19030e040203150306061e060d020403060e06010314030f04050f0f030f0309010e09100b031f180506100c060c020a0803 72
    0x1d40c8020300e600d449441c1181e0600c0c00b2401480000c41046415034081806510042c110703902404224003040c1004001c0d03081c0c500c09104208098482032a0180000d6000c2288942031600d4820380015050000c02107003409140c05800c0e43e6015001c01741041c80c8480300001e410940a041074010011000780103640740d00d404aa102d22801c04546000e21910900c2c0c0030031031500f131041c0154031403030391000340c00324a40070b54041c0541c540c800403051924503420040000400c205116078480131510074054a403a5247d414499a0180545e94100254004214500501c050381c01210308072201580c4084000f0802000504c0304103081d841c0729014011341080c21031926010000b85072020003621410703002c112031003e00c0f5401c2400c0701c48d060441105074090242e103c9503c05140d10000201750815001c15549100d5001d8610358046004034054161419118070640140d980c01401692240000013101000808003202c806010749002d41d501a80e4254030300c248205108107401011150796401c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 963777814 1250 963776564 963776579
    0x30121080a0f09170a06020f090d12081e15011e02060117011103190b120303070201050717180f1e0106050603061e010e0a12050c01050a09030303020d0603060501 71
    0x10300002c10100240884501042e103486480c0b580380b03100164402880f020400d580c400000398003040d503a080000c000d2200c1c40c055515041c00f00e010078400c201c200310b42c80030684090194080a404420582c2c00c0121000480841400701940400f0500c020022590510010780f40400307035000d010505501a1228013901c1d40025050341203480010001980e003c180155508032060180c01d1510034a080001c03a10041d0040070040c0c3d0700007212000650803503588005001c1c0c0f150041028640d41000c0b0030020f05640a00c21168000301900700301c144022090f0b812a102e0340010558105449041c51103003803081c1c00c00004020400d828212581c0620340c0b149401422a404403b000641c00c3c000080b0b5103082103820f0ba8055100030348200c0074840a4641000042100c803849410480480510310f40ea90314070007080c00400d03c020600c4005202402d08504007108140035906211040002c0e468250380050002c00303e81e0149070060302c0784071000070003000d800503506c0940041d050500103d6030700b = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 963779064 1250 963777814 963777827
    0xb0d02030d030b0a092c0f10110d0203090601060206070224070c05120c07050f031203130b07170a0605010f2607171f030b13060e010209011d0303030121080a 69
    0x8070305000c1c5900b0151b0144505560b4440010340d9000341c1c00c2003031081250805070b0801c022503400000344030b007000c00c0102032004a0300300b1101c14009503c42c0b8010800c481c2c040c821660400c0051018155001541e405020b0506441c40080d110550540015100904c99001c1118590707211007a900b445103111071003c01d40d002041909464011300c080040e1a00c4c1100000c0c00540c2c0c09000340032605044885907440d900010034049000050721688030020301d40e080c62600c10001510340a0303149403081001150380c0002001113890b81e16008082c082c503a0084c0707a40d5007400f220f2510740000140502d40810507019045103081401800341802806a000005101034020381c04250030969a204420280d00c01d48842d20340d0070400503041840456040c0b820141d10130007001e25480c0c080e4682e41e554045552110828159941c0419410078940e0f201c0e05648010040e401428a40075500001a0f1648810700c10388a84aa1408158071030459442e090401c1070341044000307455031404407019040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 963780314 1250 963779064 963779111
    0xe0907050702010318290906010e07090e0a061d15060c031e191803080702061c060e340201110729130f050c0d080403060b0d02030d030b0a09 62
    0x100c1c2c07015041b40742540c103041c10007889610050001c10859180c10348285142001810074801c001c0640800b041880310190032500035079034004000b50301458114141e100c02c0c0c1801051650601040c14003684031981400f000449508860300f650b986410140f20740780d4071130f4180b0014112484c411103101902600f02806031421019030006020300171031000c0b40e121140da4180040c44801510a00200320800f000d04510391014140d14503001e4003002c000151003054151820103903e03800144005201c1c42121031700510703001400703c4890103126080010040c0c0c0b260350200c010b8102038032501180700750486c4038501100400e042d51085541043c188052400030041a18010040e42102040d0340c034410314030902201c0000305002c1c280e696403440c5411051000e807124400c0c2410300030079940d0840e611406c00d204541c000d64517465880c12006546040301e80380d200f02c002c10907050150310085041110f14407035182c0007988181040000301d6088043e00510300f8a450704036010301050740424004035 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 963781564 1250 963780314 963780353
    0x1116140f0c0901060c05280606050102121204020301020d0608150105011b030c05010e1038090702251e0b0a110703062301060e0907050702010318 64
    0x100940e10380141540e8001d100c00700341d000300e1000010411548101181a0301c60302c0380341a1200c08070702c0701560780e07001c100d4040c0c90044031041c030842d4204403c4d4030500c1d000782750a0000c3c2c100c100d000c2803080700d1030241086500120300c003400040c0c1196029412034003405a01d0178108000d07500c03084aa81e0310b440c20561044c9030041400042041d6002d52126842c44100c3d005505007142c2591341210102e08000040301c096494030f54140c071205041c041004200381c0c12500154821a40800f20402c487e0540d291050404010503c014a94400660101444103480d8010300c1e03256000d04902d4003071a101c010142c461141c042c1c0b0b146441c0030311501c0803074181080b410034465a00410b00c2c1e8001d00e9100d4001d000e081000904282401549000480480ba9042e03814060f41d035140c6409846154810b50810742c41d0160f11550000c08080b06030242c4420b00d0304900c100081c101250444101400344414010080744001c110382c032035000003082114144038491000391501c3c0c01041ca9403034011129 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 963782814 1250 963781564 963781573
    0x1306060f1404151116031101030c0504080c060f0403050d0305060a050f010804060f11071a0f0c04090902042c0607021203040b061503240a050d0204111614 68
    0x4125900c01c0003920700340c6521200e4040c6100c1540404d881d103400401d00540b46003c0d4a2424040c941121442c20003140281071142c2d00c0f10041000504480f10f4100c4101445002e02041c41039080000d00c04001400c143c903601e6070340000000384405030146900c000c02510403082c4510880e5070580203240540010303038001c541302e07840d02c0411480030141907076640010b400e11300041c040748103904110740c2d1001c10303034001a01c012800d03035500580c2d01002050300c0d1500c9281c8010000d0b6120003003158466001d43c116200e0f070130302036403001c0948114810891070607103500044065580c1e40e800750608004040c01880300c0c514205280c02c13800301d40c1554401031b00854001502090004c20386e11800150681158510340c1c95036242c0094100140016400003031036aa8906a411a88001c6001d10b03003251000c3c00014907440101e4061000d82c454074002c9840000070421070301c0d102c0c0e40201160f030450340825410000004a40e25028925048490104100d590828851028001003440c6400300649 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 963784064 1250 963782814 963782837
    0x7050102100c0c15020c071d1506040e04080d021c0e0d0e0603040c050d0323120106030e1002040605070203010506040b0a06140d02040f080d080f0c091306060f 70
    0x107003202c1c216000d039408681158000780c00a9624801049681c80480006082012525006203011180c0e0400780c00e05400106c0d0f08031040444444650040ea884180001130a080c00403641a000d0f512601c0b020300c000030082000c00c2814401e5404130304a901d17085441d143d0314038070581e0004110450800503403030022031401001c07000c5500c0c0149080d50f1035a070704203244081442500ea0008106035045d605030000411241d032880d440c586c00d2800707940c600c05800345400110b0081c00c40c0820070680203104209400310502c001c0005411070b1910308000034107252912240e401d00f0509402082954400200810f942c3e40003409804c4590003a0020000c50342c41c0d005020881d01000142075103c11501010001c00e40710b0b4503200b0014994912480c107240005540e14181c0c1c200f80c02030802c8e200300c820207200b8134008002c0a1405c2c90300d4a09010142004190306400810240008000b1030340050380c0f801c5601d43c0d0f400010412200d4004010b0290380b103200501302011982c40704001120384044 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 963785314 1250 963784064 963784093
    0x1107060c020d081f0b0301090e120a1b0f050f060118050613020901020709020d0504021002010203040209220507080102120702030a021018060203040f031101180f020a03050d0207050102 81
    0x798140c041035a00c44215035203139080c0d0b040544084400c58a44003a00c0c85000c900d080808014500030080c1034004102c0203180c031003450910311a4464071081c0403090080411041d800140b604011568503c0c02941e6401410170b10b400004640c009402c40c810072490030f80b00d1000055050484860190290301015401d8251382070710010b4860542c011031080242d08240401e07401450000303014011a003140f07030342d0b0200348260b81100c04815821039450b02017206504100940d0045216244021455454142d001501444d40038150110700c065490f25011880815400c0f0040507400000b113440942d520401d0701c1c0030750b1013040e4041c0352030307030090115010900003c1a1180741e00360360041d1400b4080241c00070000c10340005040f84401e003021252000c00d82a2005501545c058400488200540c1c1405005200c0786484002141c1c5000a03241440750703103116585540ba44184546c0707115049000080d0300c0340302600044e11074048d03070000d03400d4260005050002c80f80c085c5c090310018041d5094 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 963786564 1250 963785314 963785323
    0xf0c012a031a0402031005030604030507050111040506030f0411060f03011401230d0204030609050c01021b030c01080402040f0608160504150b030a1407020309190b040e07030f1107060c02 82
    0x600309115910b500182c4824603041d0040c50b0b1294500d00c01c440a646c0c0d40f0002880e040003518240c011400024403901885820300a984034400c0107848680f40924080216001e0720008144800422103003020408009000c40700f050340e01001840070380c0707078400d155514904d40d1083c412015140000c12000c40154010000070092455080a80f44c0d00400c0303c424648550280070203010306942048084006081445100d00e654020001401c60140c0b0800181c030300f084503481d0b101e03622008000d031881c2e80d9002890603005007081c40e042000352030358130100c0d020704921900b200415040040200f80701c0d900113000f01d0b082d500381c0c00c0309041c15501c2003403004480307260800085064070340b50240300347c10100d002980c1082004900280403101d0003c001d034215800d079030800050300001076282003860701203402e125600352a0002e4008510b00701d00801644941d02c5030640e02c00111002a41c60390095210079010201c00c04280b082d0307481300242d280d80340e00903801280d01c0c40c034001156104910005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 963787814 1250 963786564 963786581
    0x2a05090a050f06030c0d09150f0b0a0503190c180b031b01050a0c020f130203010f1703040504090311010203070f170403020d121e020a1b0c0501050f0c012a03 69
    0x10724203442c4d6219046440841e41c424a03900c4038030340c4c581d164880020030510001e90728900e41080000d115411038501029141c001e6038403827181c0000034040c4903650b400300b65114042d0f0426a80081240c0c00d08d032202c042d18040d03228030054011840d41180d0300b07006410105220b0812416551030680310101c59008141c0d210195000481c144102c0441501030384c80c80700180c1c001400381c44883d09800006141e07004203010094025004030041140c0c1002e205000080d10040465070b485c103420000180d034074012031191500c141d403201c1c21041458006c001d00c0030075050360b10082d03580f0f1402980c080c240801c802444000034000718200f01c14124841c0b20b0f54011541540508200c13000314408a80401140310366141203a40d50030f204a040042e100103001403013003284050707110780100c02c02a140702d07082d280381800c440003c1e0602c00003464150101080d90b0007401c090f6212020303440c520301c0b40d014245da8143d82d0362801d038400060108010640b4080d01100b510881e0045e81c811044041c2e48048 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 963789064 1250 963787814 963787819
    0x9010f080601120317040c080f1e0a020303180a0308040909030f11030904090303020906040e090f0303040506070c06020d02040e190605010903030c020f2116182a05090a050f 76
    0x514090800300d2881748465001401040c00b1903040351140040e44c181501d2500d0782220f6070003031080d01c0600c41e0600c802c4080c8000c440c0900002402170300800d842e842440c80c1d0a0125a07509421071907680da0b042c564000e5608403a140d034841d620717020b409000300001c26080c1d001c80d42c07201c0c420001e58454108280410b03103ca002e10b080c4024201808050a031088045060540a222001181c0c4642c00544000c1c0712440749091541040600b640c108154007030710340000e03001001000046480010320a4000116262500e001c6030700b42051030080c050b481c2c0c0d146c42a4000200044c1c203910055240b40103c0e40740f03159242c1c0031028022002183c50034402c1a0104000490401c0440c0c091140c0d03205190003e0042c031400c658040006844501c651500f4124010301d540b142d14249040014120320f0700d4001c2c15003080f0f030800020b00a0141c10300f0031803070600c3c4c030740706085010400a020f141c059800e910043c0003e00400c5c2014105400c800b000070f00404080b0b100250500d0031030032282554801 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 963790314 1250 963789064 963789077
    0x2406041a130902040f0b0a050d0302031210050d1101030c1d010e0619090e090f0705060a030e0715110c090106050f07080408161d0a0f0b09010f0806011203 68
    0x100034032046555846526079620740e01d00031000541c44030b008202400405500c00502410a4030410032410700036040360740501007030408034000076000011200c0c81100301030304003010f6507a80d003122469546d9070071107500212094101001c11529101c103420307840003620148001039002004480e1410b000e205484400e108104058040d400340101d002c04946c0680064501480c80781607000d0468000c045400203020410200b00c00c1c01c3c008802600701c0704680150481102030603015542c0e4083d8021144129400145d102905e80203910040c12070003101c06840006599800f643e9503110a00041d0000c0380342e036042800d4407113020500fa840964001e01401459081030310031111034004808001c2c00e0141084420301065000025100034006440140b2401090a80c1d0074045070b4240e11103000d48810005c068400e0502e030559a61080c100d400000b1042034191609024003480810250420959000418030803800c004c04016a82c4000c103e55081e40d0361825040210560900035001611 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 963791564 1250 963790314 963790361
    0x21040507090c030906140f180703030503070c02130b0325140102030f220506030601020303150a12030801030c1a07060902060d14060906010207080d0e030a05240604 72
    0x503503038003120a20031107107000240c003207007a61010204d07206d089060903162a0a010407504c0d4011101c141d5111007024407500761a100914030030369401c1180002024098080001a9072600c039440d0414010380090061819280000030b201c000d20f0746400d82402409085100c9210700c0c030400301c00f00e69411000004d0405840d107045d00b1900c810790048a03045000030443c1d10b00aa081401030b190600c100c54000100c4401803400543c0144107502050069000b801003119503a008000d482e80140c42c3c420100007452000005003e54a41c0e400c48014444940e51480c241944040d8a83c140c030f1290510741481c1d40c4804121040300e000c200e002c07411000c204401c0300098007903040f00540f5131000c0c21490a10b9a035088080960741104503056005030000100304451514441c003641000080c0041d19600741880c0c012610b44066003441c009001034103107103031000d460400500340100c1e000410349100200d001c8032035514090441d0f50f0034926801d00040340540c1391900c1149034104000041584684 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 963792814 1250 963791564 963791579
    0xe030705010e0d02090106090905070e060304110d02120307170304050a0f03050d0501091b14030a02070f050d0206042006030f071106090c1008041e05030f0c010221040507 75
    0x10b441409820282c103520860043c0c482c402528041c01e81500d84100050801a00d141100c40c0103018108000310004041056221030301241d400980000391b04003941c003000003248074601030f80c0000b5003042d1240000303501044040041c14070b4a01c98021800c1c842c50702480071409000513180905543c10841040b800a034016002d0071503a842400e0040c145140800404110361090780301055013030f02d45c80c1b402c12000300b00f04285212030003414030072075030308040181c2c1c03629000041c84c13240120360024581003444401c503801c1c4952a4050100c0d030700100d680724029202c0720107580031682e000300e0600c8804e9039010754811104148021b007900d0700390758072215400680031010300004140604060b4151042c007081c80f45070720402c3c81e00f008007003500c0fa10040c0100e903200340507808100017500c41403200041345418113224100348040515204071060409600b14403a0f00da124030003d00c005044a20304106402524400b0600e074260b01d0340c581281d00e50541d50a04a50007843c9801c0101c0a01811 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 963794064 1250 963792814 963792827
    0x60e03060a0e10060f060905040213060e0409020d05030a0801150c06091e0c0e090c06030109021e03180c010c030e040c02120a020a0b09240604020d051e01060e03070501 74
    0x18080c10b02200c2aa211507120082103819940010304454510041402400e801c82d2030344000303000a407011494608024910403590b0b401d030180204000b0204102d40c825600d135080020f03810340080074130240740502d00e040381d6a41e1007021342d01d0218003503600010b80e40a81410b1145c100c2035584803100034006565a143c000e14014030219006101845543c12518450307500c0d01d20799101e20394460105040041c5030303241044c020a01c0b000359203c03124445603916400107480c11114010b5025803101d101c0011800040f00d0b072110030014000110030030803015501c192003d41004180181d90812440c00c0044a03940302c034080c0500452000010030825080540c05410700120510542e840300703505d001c01e100d05501074844000140c0c043c004c04414000852038098015100388010282e451424030741008016500c0361104120001a0001d080f6442d07a0b0111505e01d40700c1c500402032494040c0c05d0700f580c00b44411002807101503060000c2281c82c002c80d4030140a1000400800c0f002c0e15040044802 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 963795314 1250 963794064 963794081
    0xe0c03060a020f04030c06050720010c14031b03210609010e190203010b0a081e070f0908070f080f0a020906040c030e0d0507050d08040831080102030709060e03060a 72
    0x101c40820000000c5003040c44000d01807c038654501d50340710700074181500c0d01041d82c0c01008442d51004e0028580741e0300711a000c1c12640d404012040c01002c1c801c1503c1c1940078000c1120039141048902041060022000b000c0f070030078a0760150801d002c015000c41d2034a108580464014010740c0050144038400f0410945c0510003400c145030444401d54800c05a800aa00c007010070b1801083c48544107030418800b0380d1006a10304000c0d9075101c41842031020240240c9008180030505141c0080d00b841a41c90602030300e070300b00498130f003c0d99625004000d8009886501003d001d8624440038400020490b03040d6583c0040c10410651507882c00c20000345503d11f540d201349540e0300403484041c00b052080049420b055142c03e03454201508103d402d0070311306140b040030800c01e01d0070440043da1a4042c0c2c2d1002141d466501c0310001e109800301ca151040c5201c09a5048020760009800c0d08150000c5224030055503c00f052a030703460009a6011641d6045554903810030030000b4241e24083e8400c0d0304 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 963796564 1250 963795314 963795337
    0x30c05012007180e0f0601092405091906080d1e09051c171e03071b0c0b0318120c070515040b07080d140f0414030d1e0e0c03060a02 58
    0x5100d0312510301c2174038020100c1c08542282c2c00000040011003428440c452842c04001d0400084811005a543c017901c0b1500401b031294641c00007040e941404410020400811a00c040040684400c0d01994510b40c00754164002040d03045242c159181144140040c52016114410b10710300740402c100c450b1003540c40d40901c00c0c10500d150750104401c2004000341c0c101c800001d42d40c403140c0c0b4009117001403100e04411400030b030400038840d4156101c0404200301d1058168001341140e1490207809402065210250543c0d001c0103103c54a021142002c07004c80f1082c040b00c000303038541e295074003050182e1180a44241c010700e008010030704058803401c00941442e100c103480e082d143e888081c0c0315000840107071580d89000c540c641c41080f1503c9a00d005e440384008808091901c405060300c2e0500003000100110b007140c26402c00400d04000f980c0003040c2401c0e050040ca000080b065140a50202103131800354200f0812142c40f035008114268410b5010b00a4440340d5124080000030b503000445140 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 963797814 1250 963796564 963796571
    0x1032c01021c0203160903020d140c06040923011503020309030c0d0f020c221802041a0f090106050304082d03160914100c0606030c0501200718 63
    0x2100c41d00c41404000032082c0e4180016204d04120030341d0311584258021101c04d001e464030301400540c2c0c4036240f04400640c80090515441c00f541c00c0300b824114600704040e00304902040c086503250054203d0b0360441c0001490984018a41240c1880300c04e003031040c843e94081514829046034840e03001181e11201031822a840d001d04d440c3c1e46d40c034103001404150005041e04c0c01d034000e40b513818449000c0c242c0f0304a03400c00a0f00c290317054200e4031401d904440340806903120803001c075074180c2011442007240c00502c10811410300141c1480701c3e0844d0a210f074403c00900d040303d2111f00d080d042c41c9060b90550f94400d42551742c1d81d40c0b0300b0519401441640e80b944414200d001a240c03403401c50000032040c41055646034109541c2d011a00107000c0d00120511007501c5041c040080001840404c4640440d0003080340300c0c81000a5a2190f68404090400b5040034004414080ea5811120403503034213aa0700070b8071110310024120f4205a000007030040d40c00c540b500f08a44e892070700924080100828001 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 963799064 1250 963797814 963797827
    0x2100c06150b0405090a1a130e0106091e0203130209040f080309011505060c100f0213031101020601060f2c0d060501050111030a0e0402160516031101032c0102 70
    0x1580403400036440050002c0e00080d05002c0782c2800c801aa4100c01012000e2107261150510303860301a440001c0540180041c1d003400644070500e41000450329400402040f41a0325040d180c1c014108081103241030241301800b644400303000e072003100d00c58150b00e00d440e8a001c04540c00c00c0090000604261582c410340d03e5480041040c510007540580c1942000062120002d080103e03046000d5000c14072444041c86031003034103040802c02060174041110b000424500402e0700c00020b016805080c03440810041002c020407a0864540341502026003c4403200ea0340d4030401c403445600080d0000000c1c5d40e45807402e038403400000c00420002d1084030007403500904000820240c0b00100c505a0310142c40f04010000e5503000303030701c601900c03405c0c4000c1c524080545d41c0113130488079980e0140d030050780e0000e9140d182d12001c48070088040c2c1c3c0300054030f008486a404102d24001a40800d8800ca0f84c1107116201c158005d208061810380c401c007842d1072402c09100f0608036202c1c0c4016000d41035400300442c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 963800314 1250 963799064 963799091
    0x4110402041805060a090c0e1009080102180306060603191116030503060a1e1e0b0a050d0b1c080702120d0903150603031b0807240b0d02100c06 63
    0x150300e1000000b0b000103000d00d000c8042012003209948207104407071404070841d00540c0c1c481458a21201c095406003604c580b490300880d010b8155900c613500c0d03944003150356025001d54014120380b0081c01c500712001d54681c0b1003001853703c4291400800d02c0c90908800312500c203144c00040402ca010344495003041450280311402c1c0d0700301e5100300e00186c000070802210780761a20300360020b408442509192a40070381d00001c0249240c2c054644016200070803040c101315542140c802414003040e61540f1043c18004c05089034000c0f1401c1d180d003904040049106091003805802000c00d683c04501e098280313a110f04440e40d0001c02d003a078000c510727440d850040c1c8000b002240e000d5103140c0c2d902246c031490760030004042c0740d18146040715103003454000c00c00b0990004100800c61603210b82c462426600d45050310342c0e403041d0000103003149403141e02003d000d6800c11071845a0004640103018400f0745c0d000b080b00440c1204070003940b010a01b0600f2203103500c11300c90b461045102c0c1c2c60024413080040f02 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 963801564 1250 963800314 963800339
    0x1003150609051e13091b060503240120031b030c0c04090f0b090f0a08040f0b190518030f06011d0f04030e06070b160e060901080411040204 61
    0x2140c04100807607020052428401c540003403080024031109003408005000a185603003d0003c003141a840703040c0d803418403106948078900d80c0100c801d80005c055a0307010113441a0003c032140c00b80c1d44000c1c040c81c0e20900300e81d018502507213416500ea01d40700f0f80c040007120b0220b52440b000e0030184414090980000309010340f2403010000c1c400195203401c070402d17001d46084040c2c04103900881c1031217001d81c00640a8a20154020707441012a081c070f42d40c0e464414641407400d1424400c5100340350702c241c1803000c1c00b0010015130708071080600e18a603d802101c3c2c0d0038803458038050440075200b410162440d01c036030060f140388000d1405511300c0c000c88000103440c02210a076081c205030401001003000100e15048030090302098000c031490380ca821880c2c52407030750703006201070284004280d0202c11550740e8011074109a5020764520139a050000e0075444030b0318000d08010100710191910070092034142d00707407480f4041c165a90354081d619950b507042c6c0c00c02c00306545a0840d40074032010401c5280e43c0d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 963802814 1250 963801564 963801569
    0x60e0610050307080714040903020a0f0809011d010f030b030106091d010f050103020a17010207020d12231c02131503110901050d0507020a0209280209030309100315 72
    0x6100c4080e41e04220405080070120782c448451540b00031070410030f0031070f0714000314142d120440f000101100b15081c1070b41008010b0900030042c3c9150f143d1102040f4500000e03041181007030384c03900140c5104480c01c141e2b0700c103480b400034081410401c3d500807803486600010350600c0094004500c0c3c99440c28618281c1d108052002141e166440116101e20401d129060300803d44e0031050201d545140c01140c602c2c40c181c040c0c2d200749494062480c1d0512001d404a43d40154003900100b102c010b43d080000b48210810840c0c3c0c0082c0b13118840f41c540d205c1c0360031001039203194400d000e4a8408035030f5500700546181d01400d03001e00c0e0240000001030f01d14013100d60040c180704d0402940001032807401811500315617864003500000313200210090741c0c84001c0d60451181d040000505440b4190180c0c6803001c50140254003481344420414030203940840100d90741c240b680d035100d9244100e89280b007a409003c0f4429059401400b518590707243c0300a55640041482c01d0000e580f0241c449003003e104141d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 963804064 1250 963802814 963802831
    0x1311040b10090303120b0d0201110106030c24020606030712031b03022d0606010c0303021303031101150305060708070c05011a130b010206010302190e1312210207060e06 74
    0x8410000d00d03401400c0b43c40c5d412010304081125100c0100020420885000007a04120354942c0c120007601782507001c0c10195800501d07513041982c1da448500302c403007860840c00c40303143e8840b4506403042e4000a4002c0c041e00c001409000c07034a003490100c00c1643c1c40620f05804001e110464641c4141120b01c80301042c90196000c0d0400305404422041e14480301038a15400a10000c841c4000c0c03000803418503000102460f20600c82605400d040b00039000d5415400091042c41000004040d0032503040a0000c1c1070343c00034043d0030300030051b940018495110181c155008400040e0000e4450400c040e07000f92a81003008400e0030070744406007140c17900c28003030010b82021410b01459180500da10b60102c1c00110040c048601c01400003501d41206120003070040d410030081c0c10480b20f05aa120018009550f003100041c036105d001000c0d04014030707206a403510560b5148a09a6101c0c1c0070741000851840c900d800c501c2d100340d050307030001d6004840c03d403081641c90a80030381080c003d00a0b1030003800d40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 963805314 1250 963804064 963804077
    0x140c090f0405010c08070c08030c1909030606060c05070506091809070f121109220c14040c0c03080603010f06061808030309100b0a0e07050705010e01051311040b10 72
    0x90b141c650b0840c1e031454100c00500c40a101008417480c0e00020b49041950701c000007689a855501c440f81c90341c0502c032a401d64000404109055403603200c03000000b01c1c3e01500302841407554588060f6030500c280031010342640c00c1703a07006000c24200840108840c0e5005015119001403031720340342c01d540f0346c2a9003001460300248401c008000e4814004005403108501c0c1c0400c4507043e40d10554078081e0001054090700c1c0f01000200784a2842c81402d030a040410801009207800e46059012424030b4050080e03294809031120349242420301c80c01d1074040c03240d01c80b0040b14003151000c0d42c2c18140203000d207030b141d0b484960140510f845809014010305154494841c40c008121140344d407070415800c000d2650b4028401c01c101d10031b0015840741164880c5c100040c400c86e944010aa9001310380c0c0142600038088000d001706c6a921070700600c0c3c803d02400081241c00006913049083e2081601d8000d08151f8101e0070030042062846071541c032326001000090449101804960b4441d8034941c0040460395 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 963806564 1250 963805314 963805321
    0x190807062705040c020a05010e0f07090606080f0c2215081006120905010e03040f0b0903030703110a060903030c030c093c09020d2304140c090f 63
    0x41103590034609901c480c120a50500c50302840380121152032107aa441030340c50780b031811410703802440041c440c260080028825203001c40304441c3d0300c03045a04800460f108139000022014510b02c900030584103207554940c12500ca512080802540103092020049410000007a00801c23000385510000880c030104d0340788078074100c03403420400d000d1840c038418480041c00b000046c0d0707022001e103000d0319800d007031058589030703002401001841c0e04000100190300e40b0080d1409480b00101800c1115000400b910b4000c3d221100301c0c44038000c0e402e1694060b4400e1003001e000a0241510060b100310580031034a4001c0b0750384172a005c2c0c40001d04140d010907500d4100080056040c02140c480c40f01e81d003002d41d2a80c0c86d10820044007031640e0301c5441501c000b1418110320007007083c003101011032442c3e48080a107880e00b0006000754416402801450720f0110908030003000c1d03482003441c0103119030100c08903940d05c0c0c91b041c44541e10242c2c8201d480c000d01c10264069035400c0c0e00030b03001c0e801804000c4201d14 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 963807814 1250 963806564 963806567
    0x2701050c0f0c1806150f16061505010f020d0503061f0905011b0807080307020a12080f0a0605030a03120f1401080f0f1c09120b0403080c0301060905090619080706 71
    0x103d118460180a54070000c11185032104050504c604001e101055a5107840a07842c0000d80189032840303800e5004008407905102d00d98220349044d03c407520780444682d590b00010b41d40481841e0080b40940c00c4144565605800342021f1540683c002c1c0904600c0714060745182d140101c00501100821401c610a10603035034442d40348440c2c802c04031684641082203403030315071944c0140d1a004021600002c00504c200b403080c456580b0065000b00136640c3c0c000a803c0c0078000300d500302c500b200b01c103c6100004418100364011902112005005448603038801d0b2001c946501c0c807165406080c41c0c6941c10238502c0c0549106400f2444220f06a00300035504140b0a5410440e6520441c1c07941e0f8800401594444408290000120122a14070020703450607030080e82c40881d1640015603c01c5585292014131010072041e512a83c841d07070354002d0590303030002510100c2c0401c3c0254000501100340a2205081502c2c00300d4000000502d0501c00b0241904a100c3c4010260040420350300040d50400055 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 963809064 1250 963807814 963807829
    0xa090201020c0916020c060408120f0c061009050f10060e01090308030106030902030c030601030c12150c080a1503030813060209090c1308010c0c020603151302030601090b2701050c0f0c 81
    0x900301f158414a450702e0801e8041d500d00c0d03450100ca0401c000010b42c4443c421aa03c100c4041c005ca00c426603902e454810070f009a0094688964140d5a080900040007141c290f100d0300d03c1800d09d4461084070700c0c2054400ca64054105039041c7c1030005950010001c1081c0001860080500343d9001c5001c06031441490f0404800c241d046001350b02490042c40000c440110324000d07100d810400480703da406040c8442c1c0d0100c40c01d9041c2c1d401303240003100e0683c02d40c030603e12031107040441b030240030780b1050014011541e0650700c8050001559640404c3d00410709105444405000f84805820b05594000003112082c05460250109200059554050116020850003010100001c101012030386402501064850100a200312000030014203c5c0f07a000c0a40c035070406001c0c00c0c203110024030319024002980141d89032400700e20303081d43c00a1004625021145c05d07100036035203a040002104611152402400050f82c1400024805102d00500400201c107200c0c450f8001000452120f0003400741c503 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 963810314 1250 963809064 963809083
    0x109120e06120609040816121d03150c04270e030c032d03040f06050604020f0d0c090806070201090b0a020903210f0c0606090105040e060a090201020c091602 69
    0x80c0760034001400c480c04181a4075038010010759044207650340f0741c600310f00a4400d884401d105041c0d80380e038071014010303140d1042da244251500e501c041c03084180c0907018a00f98000300190326030300c1040c01a50703149141d84841c0e08800d01401c428249074841130390b07441144000d58040140c124a00c02c44100503106d00610184c0300d07108000e03520341920b80c45041d48900c9840c001000c2e61a030400404400304c10210860b40401c04480050f0300c0e4101858010060101590300341d03400b504003808251240b8140c03003102e4000601d0700c10310345001080c0c7c10b0f01c0e01512140c86080103021842c01c00080e200d200703000180c0700b43e08550001561200034903005031040400703404c074004144140401380007928005603007144c822500220419141904400c031480d4424135041104c0b620010600c00c1300c00c200018242e009420881d2809056a02d40061204550a0a040078032950110008c82d80c00440c40e480389004d14010f105640815040e0303c08a03070880010780701c03000800000d1241d18810342e07050204850 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 963811564 1250 963810314 963810319
    0x40c200f10051e06131a030c01030c0207090504020d0609030507050106081b0103020d0e010606020c01090510090302191e0819021e041d01151212050a020f0109120e 72
    0x3680c2008141009408004800d180f0080d180d000410502d03654404c1140742e06503008004e11501002c0300340c641c910340651940c14040c1c070400c82c1d0a0034940c024080e1403040022640200340e0b9602d0000c84c48040c20f8040d0007607030808081d0311180f004c03885500075840f010b40a81c58265440741d903440c100d030841e1030941c01107200b500400d540302e040d5404400c1d11f0a100c00246005a100c0c10480c040b4002440c460650340859807130319900090090700819400c0440000f62200c50340c055441040c0007042808610321000201c0c1c00406000518141c4180c1d182007100c44043d03114981c80b030611601c9080510107405014080030b030208054903042104d600d5840203454000150070700e90340810300c0d03413002c090030034000c0d42001d0280419841d581d20032282520040111000103464210a900a00c41d00c0185000503808450202d02c8000000351204000e074400e4061403918050750040321941c12243c480004c6000f694400200c0b00f109010741c0a4080c011020500405141d50024200101c420719150 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 963812814 1250 963811564 963811571
    0x6050f0c040b30010f0602120f07170708040f0905010b0a141803030f18120d080a060b0c07050f010c050712020312120a0b061602040c200f10 62
    0x101d0075050105a92422038249001140b00f09003a42d020795449814590a40c42010350000080a500103640d10080314416000c2d150680c1002c45900114490400a10704162041102000041c030340c0d56010380c01451401c00c0b5080c003c199890400580c000e50080145500301c05050100300c00340e2007007500400c0c00c0c0c03c82e185000c400b04406000003456040d0580d102e1404074180c082342e60640c143c0d40b40b50400800740c96a80d11010050715907500003a21212007002050b40100450038000050b02240c460680140884200200e0403146107400404080e2140e44981d0009003c640e008050803c000700c40f00541921820181030000c0300b05541d400e40c2c100403985821501050340403401e0400d450250b112184080c0c03540c00401d1030314901c2c1d90031078912840003da84d40705c00e140319007041c003c800b15017091050058820800507640100c01280c03805400c20703406900185000e07444603002254901385502c62240b048a5101c649100503410903540e0059045101d04100c103110501440450a0301003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 963814064 1250 963812814 963812819
    0x315061508060f011d12160501020109020d0f061401030807120807120905010207080f0c010b0a1d091204120b0a11030c0a1e170a05070f0e0109030b0406050f0c04 71
    0x500e9a070f44038651141130000081c94001c2e41c900390000d180c0e800101510441d082400e64080c19a13841d006000031040e06282c0c40081555071042c014407103001c0d0000c00c40400e9600d103450700881e041110000702c41d59582d880c441d248102c030445203980258021482243c4540190030700039400c401c0207081004020401c804c0018407900700707405c001c1842d01180c001402c03800b1450b01c540240f05000024140003c0031400400761030810004010038414030300244404c80ca48018040d201c60140941820481d0b2070614102080020352a01c3c0e0111801e000c5030014030030031080400c00c0d4419048050034034640000e400a1080184009400070280c0000300944429140c408146002c0500381c01c811040c00105018198810b0704444941c07440e55004501004001001501aa42000c080302c90f598070400090204007943c45070304e1003a55152522424811811011240f00d0303107240300300f810f2100c02c13080440480c0450112901c907c0c422080014103040004504d03100e00c10080040c3d02e007003000c200a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 963815314 1250 963814064 963814069
    0x9060f0c1801020a0204020403080306150a1d03150703061502030c03040302010e0604171c02031801030b030f0708060f010f0815181b040c03090b0f060604031506150806 74
    0x1192030490385404103110800507400101c3c00c2020341c00700a544280003040101c14040000000d500400049601e18501c0801e102a4135003805440314140c007003500c514608000703940c400d0381840d0000004054803644a5010608216000160340020001c3d60303070070341402041030030141d8188400141c0015030400c03850141080d0b8921960200030b04204101c884489580c503054191009445aa510504e80c050326000c0143c0c3c540c0d141301600c2c0d17021480541444c17070a0011003121002c1e140203540c6040400743d0001580901184501141c16206203081c00010a10600480c800740c590000544411f0400282c0320702c41000c10b8201000340c503620401000400300003c0c0f03803192070302100c002402680d00c1b90072050072108040366800450103240100301c4219903010070040504003c50301009103801e00b090031000c440d04100014030341c0d00e80801040b0720307d110509050344000014503c614142e101e6640f4071480043c1041401c44980302c0320f050014032281003400700310a02c0c0340342c0540c0b0781ca8181700 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 963816564 1250 963815314 963815317
    0x80d03050f0a0e060624070302010e0d0e091b0d1e060602030301080304060e040902060a080621071811160b06030a0309050d021306300308010b030702010b1809060f0c 73
    0x1200313100d421646d0410a141840c20703000700714121701024060700c0b480703a4103000c0c0c0a04044151036525015a01c600540c035402980b00d0300054001916415203691009500c1202c0c280c4000d0b485e0111000f80034001c04d00c1d009000f1800c040070350180300e5001000c040001c606407000d6030040310541d0005d0005000e20980002901c040b80d085140503c1d544040c64042001407580510194000741c0000d840c40083e90020103450003201c00741c1da4124980c1051070a4501d4030740c00c1d82460050380003030a00304102e20700722046000441003990000350740e40c075001e260b2595902c40d43c840002e80201c07401c42c006010208540c3d0341e0040003039010302140034055400a05082085c0038803072213645404000419521203030103519050b0038401040042d2078440d81c031400e1241420460341e85c000b26200c21001c8406414203136901c1d0036030580301c1441c16402c10079803501c00e400007080b01c2d046640c0d13449500032990342d00c1c51301c458601c90181000c4050404200141c20190010070041c8994075100a1011a02e507400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 963817814 1250 963816564 963816571
    0x60504030606141f110303070543050111040e04030815060301151806020c03070f080c0d1a1306050609041a0a091a01090b0307150e0a080d03050f0a0e06 67
    0x13001d03461a00b41d01e0b075090f07440d01c6018116404038407001c020002e00b01d402c40c008111011041000e61146103c0c08819075514010742d542c244034401b64910020032600c080b480041c1e1501c0380c0000320318508602d5080481d83c200e50b00c03038500c0500307580c01d020034181c101d448507800048030300e0529181030340800405d50790320062081d48600440c43d085012040d01c90000c50060441040300b50108655800c402540c40004d00741c00c91103130181c1c007000907020342c602000c2d00c101d9038032102030301e940c00002c8100b10405a00410a44904003404003440d52440d00106140c807900b4001100300480d442402d1442c105e070401020f840c02078128805100100b000c410408421006444c0d028180707a448101c90b10291200a40080401d80300410718a5406c0302c1c9004076040c7c1d10328a5003000086403035010181c0c2c0b04554444c110350700c83c80110141e080740c81154040d01414000c3d1020302d000d42c1d80d00815103011428852040040d84e544144598002d03d41c90107500044050f0080c80035a4400310134a071a000042c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 963819064 1250 963817814 963817849
    0xb04151a0f0909070306030203011b0c0b0c040b0409060806071419050d0905010905061f0b07020a0f0b09040b0f130e21030115031802040b0a080102030106050403060614 74
    0x420000480d916407000c0300d00345540580200c6450400d000c2c040d000d840940000c078403a50038011b1010b24a034842d00d00c0c10200c0c0596803040c801100c1900d4015600303c1c080c0034104000c100300004903048000c0c01c0100300505810f0000602140380659103401e201c0702030310610410036019105e00d0003001d120140e80c02c405090070b54401c1b4004107030050380c141c401c1e100481440c1d410100032800384241980320140842c05041a9401135495000c5495204921600681000d80b0040103000c40035000e009000a14400351231000016140c800c81200400554002600040b000406130114102409280e410f4901070f42c40c1107030300601400013850100268096040256100c5182c54000303400c001d002c00d040401003240c422004103500d440000d038024001c1c480d901d810702c203000860718440e1040410300d4080e04e11014030b9805660811019001391412a03500c5122800c0c045442d080a01c01503000b08421b0b1546a52a442c51a100082c3e0350b01d5032040540191650000899441c0e8202410501255 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 963820314 1250 963819064 963819067
    0x312080403351602070b0f0a110709020706020c191212020f180907090509041e0507080f0705010513050d0f05060726071211040803030405010b04151a 66
    0x440c01030440c034205802040b11601080000e11001000000b11114211420341c241e41200b40c1b40e1004540034443e42c59800c880983c10004548101c1c80741d2680c01c00740d00c990b41540c52060341d8803052000c0c0c0e0030030b44003903410a078001151034114208015191081140805400c0301011a0311940303590200c80c1d410106111700280204841c4684d6070407100780000d205c151130f40310042c0c1000c004284920309000d5024003a0100442d40c0700c0d0044d41904216100141041d0303455440c1ea903070780ca0b501702182c20644405d2491004000180e018000f900103000003070b00411220703419003200ca242c0300082d400300d81480000c00046a0001804850343e06a0700c00f5a200f4058a0582c6440a142d002e6900007601d0360050f08244002a50f01103c0c1200e1000020420380d82440a11541c464510065030000d022880454141303004c3e003400d401c2216452010700496040035540c40f0090304603441194100d400380d5585200d200c0c240703014811041d03070b002454050440c103800c20a0504c1005004880d40b0b585820 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 963821564 1250 963820314 963820367
    0x4060c08060d26070f0501021e07080915070203010c0e01120c0818120307170c04120b06040e16081b150f07021c0b09060903070f0c050307030b010312080403 69
    0x15041c0403030343c1d203680c4100341c1860a0b9060071b00038000d400c0703d9221103180300554030309080c41481905490310160000400d5103000c1128041200e180724260081d0000c43c0280000000b60b41e00303104400c00020749454100050064034001007090300c00f0130038960340c0c0d45040c0c41041840d0f8000b4400741d0224410780b001344000880708446213000042010b07a0050707207001003048807207584011266040c400b030483c0704c1060346138222010b5841c055802030304050a4034a400c44042060400200d80140001d003001590315104030003d41000c404442c00344002c455034408020700c0303000700322610034182c107482d001c190310101c2c9000607112150000107452104005c01c6c1652809000c408859a080e070003041040780b0b040c070404d40e04459016040503100004102c1c0021500301011a02c507104201001c05149401202d40d25040c4641c076411085d2887c03d440304010841340c40c02c0043c030740558051442e02d4250f42c994505090300f01000340d086010841854248030001e508044103100211032142480c01881 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 963822814 1250 963821564 963821633
    0x9160f0c1e1406011d0a0207020d02090a0c0e0d0b1906180914010c0e010c05100e01090210030608030307030e0c04060314070503070b120c0c0604060c08060d 69
    0x141005001d982000545081d41c08000451070140342c0c14000e10706540c16a03036120800e03008407103140c0c40c070181d000c031203800260310100590040070258030080860a0118442d008140401800c49020000980e218500005690864091081e800049944518240595542a1001001400b584010220980c1001c0c0304070441d041070300680f04041f41445552620440c0c400500b2442d401940c440110710303030000c900c1074180608038a601e01c580300e00d04048807400044482180b160400c0e50030707003c1c03500c8298003480300b8003490f400080070000219050a1a00400c003240b03a120304804141403510908102c0d8500100940e81d00490904000980000e8007104609000311180b42a5010b40b810728084108000004c5043d4004101e00449600310340301c0040c11760313074902800f400800c0f8605000000e03e604801d45d140e94848040190141000d208107200361400405440c12255951100080821190311000041e4040012101d03088400c986442e004030000301c0300740c03020300103403c5803400a10303d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 963824064 1250 963822814 963822833
    0x5030c0106051c0209061507110108060d0c0b0c0a080c10060b03011d070302071a01060909060810020904090507030c0504140c0d050414161a13090213090f050609160f0c 74
    0x20461f01c014107540322082c0c540b00c94a040480041c5010501c400040346050a1040c440c0c02c0469001a80f69006410160400b01540021260105610070840740d03c000420f001c2c003501124029100900010070701954080035500650000e07842c64105200410940340c50031010b02c010414030301c800c0200d460321001100603100300d060190050034a00c0034a04460400207060b412121324bd0b403441c0403e912462180d0a4407228407440b080c0e50f024a001c400221003560041110700350007000091044441c0d901c0d81e00f01515540184c54502612901708440d00745801040340203443ca41c0c00d49814544501d4042c0c0902480c0219180c0130340c0d900000c1d04100c041c400440310144110101c070a084548103030380301c90a20a02071000081da40d0034183c0070341c940030000d59440000340e001c100400d81c18403c3d010300030340120f85400a1060030b20310005442c1c81e14459404081604400452280740c040107102c136422005e01205204050b60380540c41041d4054148440301a00c0d1030012040b04803400c081880 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 963825314 1250 963824064 963824089
    0x30f030207060221070305150105030a09140307110409080a0813020a09230403090b030a110d09051c0801050607170a08100803040303080a0f02130305030c0106051c020906 75
    0x80d140700041128a0b690071102d1350100b00d00e0003503498465980c80904400340c42d07040e00c464240211400042c8010345c00342024644c06454040c1c006090407140c1c40710540400510003400d1145c0000481c1c4040c08103094010401c00e4040e1014405a0b8007079651800300e02c20b080030a801c10130020041000180590504c5070110f40040000c6042d60b00d84440030020555078046c08401d80260303840100d00c940001ca820702c9a0707007640f141d5569614100c0420380301d03840140710781c05c12955640c20f1403040304040080c1140003600703100001c5180003440c04600e410195820808106034103005d201d0ba1641c0010000e0554800340c4400751144401c0c0380c03c55000004040240b03c800e030220f0703210f09059114004600c1507944281a281e019a1400504e88a21441c08050300003080000000e00060107600f10382c82030380d01300360010f00c2c0c5080950b080442d000d4542048031035801c0082c9481c14a642401800081e002c210341f14248d4490103640004107034101200280200000b0b0001191a610f0b0500340300d0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 963826564 1250 963825314 963825323
    0x906070801120206070b01180b040603081b070e090c1008190c1101050c0c070b031303031a060a031505011d0409050c0d080d0c0327112101050604020f0403030f030207 73
    0x22961100c5000c0a100b5081d140d441d011231808105409900d40307030040bd02140d802001942c034102034000c0c3c400d01d0b200c42040c11412441100700028182d80d049000314451001900600911082c80c400c2003036880c0b0782d102841c100315800c0144940301e06002992394490546220005800e030b10000d0a0350740d03034500903880103194600030800140340704030001880c0c1c1c1018081518219500c031035a4030076601040d2404180b0004020150000138082e0740b2020403189910f0140005003038000010f44250300424071400065161100354041000a5001c40f01620090030221ba0001034511042200005018000c4c4207517192038060080c00420301054900c0103001d80b81c0851040f0900f0240b60942c41600e04400c403a15006101849030320030701c5208428031000c000750079010318100070710302a4000300c5400d9a0340c8481c031071050459a0341c403041c05441c510307444080a5403060b0b41c03400c40c215000142618016030041107003010100e0660100c8040d0307581800c02a46100901c20b08030024081c1100080 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 963827814 1250 963826564 963826583
    0x2190507170c0a09180602090402130801020d0c030e0a2622150915021c020a0615081c0e031009332a03050f090607080112020607 57
    0x241100801d01c0d88003082c094940c140a00d507200340640071074012040c96807882a10003100c50000e04643c00900200b60010005410109039858180b00c0b900ba80c0d103c41c540d44c7d030000705040601814001c41802c8005402c04011080c8025511a22001d034040001c1c4850204a80120040320f401042c941019004010903100c0e818008010081e50036003058000c0f0321913510002400e50359000018020325072039568106c035107180c1031000c60f958482542100035402000c114031001881c040580c2440300a941c02488510001d003400b908641425040d0740c4a0b801501041c895202c1c0000c41300c01161070f4840c0c00e100c0003401ba5044902069142640350b05010303040b0444040c4c4010b400840613a80a800a25144000c01c4911141508800ea07400c000071f580c6036035240c0b800c040390b100c44041c8411401002841c04000303810001e03500c01c0d00c011404a0b5499050115503000c1619542e4009410801040706042880300a400700d42d0503c48c0440c81e003541400c48085441705d10503a610301d40d010700080b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 963829064 1250 963827814 963827849
    0xf1801030b0601090b0c1c030207060504030305190908070b100b0a0903060b0108090c040509160f0608130c030f0c0909111504050604030f11130e0d08010602190507 72
    0x103681c2402036400740c0c0056080c0c2c20102c0c1c3c41841408888960101c8801042682411110f2807182e5131100b0301c0d88103040d42481782d00b000c603005008444c801d51181c2c0d0001441d1402d0004d44a01a43c00010100c145240c4000342d80064811811666025000200011181c4d120741001901144542084001d903102013603883c8602d4020b4090f5050344e206440c00d10181e24440011180d0050072103003241590b1020301c0041103405e080e40115040040407007a41c200c04481e01030744420034131551181150708003568081010f290311945254010756084407a100d01c20385500c60030001c0c1c0040c00054001c00f80d4003103090821442001960081801c1442031011501ca810020404940c1c0c1900c02d02854281e40c0c400b900600e4501100c040d680b00518242c1001d0079911350203242c500381d10701102c03840b2501c00c6000135aa9642c0c55440072810200c00407900895400500303042006003020807003800510401442625004a0011408000b0961110f4030b080b03039003006071034110141d003c050300d40c0300741000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 963830314 1250 963829064 963829073
    0x11e0b0316120302011b080a2a051209030a05070b0a0b0409050f01060501050324061b0a031d090708040f020a0801060509060d0506070f020f120703030e0109110f180103 74
    0x760400303240640c008000400c4119031046002c0030140c8500000740c18640015230310002c66000305502c0004180364009e50014800e880e1461200607810000300d039011640700f40b42100600c00d01c0d441200880594142110004040d082d8022040d0081c4004e42c0d0303c0018805030aa0f6004201c803070380080040c891585036007441d94032010a64075034060342d401c100700811a54082c5085034050706082e0030b4480803040c0300e0801e00060302d105101d41c2c1c2c400c40400c2001e60100a0300d190454040000307020703051051003850003070800310b481a1021a03000c80079140091543d00e41710542c0d4041c4050601044564031881d180005100c03083c40203601800424002c2a190015484207081d039906580c500d4558440c102005030f0b18109040081140c3d0040c00003d1020344540350300144040c1d01e00448000824407004603003000707500c80801c3c401c00c1000c031b040d0060582c503008540b8000c0c0000002c0007560620f896030a04000b40c0d42d00680103c84a90b906c94894480008448070400300d00100001c2c0c0d612483c1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 963831564 1250 963830314 963830339
    0x7031218030606170c090c0a02070302090c0301060207090605060717070f050105010906090b330427090209010905060a1703040518010807031524030311011e0b0316 72
    0x1d1904010614800000b00c10000100005c42c2e40e0010302d407420940d106003811001e50b0041043d071085025501000006072541c1c180700c4e001e003118025035902d139818090020310f400542e902c242c0400341070400c200501e071101c000703c07040310b5084400c14481c0304030040302010030f1140800082548840125440034080194002c9050b51120f4030b040c4a1340765520f41070810348058444041d400140441c809040078031051040001061540c010b42c054072041c2e0030011560416401500314007015007290b139400c0c4922012100c04503440768204113629150b000304811440500a94808070381d20f402080141c0d80311a007903001840c54100b94034044072641c09050712900540b24060042042c0c60403006031f0011030720351078181c0c1e46c1742d8000d201c8140b854031680320079502014043c16503a035592285041300111600040310320401900122094610b1030700520320002079407075045c02d92400055011001100d00301807a4042e030213501003102d2030094000f90601d22880d410701000700050100060000b103070b48 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 963832814 1250 963831564 963831569
    0x50a0507083723091f0f032a032c070f0f0302090703020304020609041d210a05090f03030705071802040f12060f06060509150c07031218030606 63
    0x12038514071070b4103a40c415100e2151003400c181c0040307240c200c101e03801140c1070003510300035200402100c83d8050920030f954103040003102580000b0300008142182d19010700990021501000c4200f440030882c0481c144c120760940c950404060310703096190450f000300101620320454640c46412a510107042c0982e44d00080d1248500103080c1c1d034000501550045840e4084a0b00940458402d9480c900110001c0d031005100720792104003400602c01d291039a1160000f065a001c0f4642c6010000900c03c82c40c002c00c03000340075a80385440c40c0d03000142c0002400d0398400b407007508203d500c1d9200500001c04040440c00007942610020508006000002501804032a203060005903030b2016000c2910a07417081e405002070440c000302c009c121208051400b02c84030b134040c407800205012002a8101a42c1159000200007240413415942d0303450000e040c55040c03040903a84620f03000d08010700b2901c810742444042c002000180d000c034049800b0f0b210702c0f00302010003110b080c0315903145d16260b030003401c590 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 963834064 1250 963832814 963832897
    0x3090c090b0616050313030f1e080412080c01090309060f020d090302090411030a0305041e03020d0209040201020f03030115031a0d0b090a060204030503031509010303050a050708 78
    0x182000a100320862040c99020700015103460302d00015a800c4146400c968182154580701c20001c0d400d0b524080c1841c1005588280b042c43d02d070790f0780d5080c2010300c00100000d0700d648507242100b400006243c0d000710340c1210b00e019440307440c1c0c141c241003500141c002e88510310480d500340140141055445a11002601ca040c2c49a40b4450405002240d49603504070f007001c08920100000d001500d022010282c3c043c2c0720307102110318240c40c0760111b8101030708a6001c80100d08003090500800d02c004081c4204030f40d00860010929180d50001810140303508000b074003880a040c04642903900c01e02c060038211440e0300c1183e0b517a5a4445c107a9100482c1c44103c1c1001910300701c200d01c0e58401d40041d01c5041c8200400d403103a29555134a451050202c007610511480c4078026060000941c1400035000070744c0247c2c0035589074508541c0c8810002006541c29102d02010001407000076088003e1300c520030094079125813100c3c0c0515219840344100d40000b0842405503511203449070b41c1c9900c1e280141c061 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 963835314 1250 963834064 963834083
    0x405040b160203070302100b0a03081306030605040b0604090e010b030d110606040504110f0604081f0e0a05060c0d020403021804120518010c1a0c180306040b0c07050703120309 77
    0xc601c0480c2c80b40641d0030010016080680b0400d904503c03508001c1c4070050003094101c419580380d60381240c03580102149020003214901c00c010054052240900402c5c06031001e1018118610000f566446580a204050b6984400200850001754040d602001001c1c1c1102c4104d4030218001d070001002d0041350b0141c0c03148100146071030a087c01040d01a5a0004298000840d204100901c018100d60701d40d40240e400e002c00100010200040040c4080f034600045030641c0d04e45000003030326400b201c1c1d0815980103018107000103100061a96000d44070a200c0e9803036404038a0703d1000b0748202d0f400070b5444100c82c0303050b9050f450071003000f5006a10455580300d4120b90004140d8141c011031041540050f81c00d03403031817481d500484861215034412441000042080382e065195103609443c080c0c8510408500e0030002c8690540d4401000800c80040899150907550700303a4103c001004802c100d5004200c3e0410041c0410502001d1540300035886103084180e000203008061144003036400040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 963836564 1250 963835314 963835351
    0xb04121707030504050405070c150c0305060d03080106051606020409021b0c1e031507051309153b06030705120a0b04051e070504060e071e020c0405040b 67
    0x3803088035109545030311401d062a24003c104002824000c110700e052203880505080001c6400d00845400d4030303003010000305480c00317030001411110010030507405502802030010200307400c070542904450861408135558042c602044e000800c4100c401801c4a0000c01d000c1070079803498011b020b84aa880000409003111510015078403001242c3c0e15070030280c2d8000e2404d0580c1119450140b425020313048900e11702050141041c01101280d00c000050f0b0f010030314003c1000d04402010060242580038008207407401c40b02121086184105142c0c10a0400e44080740e40038480031001c88540d82410030701f0a64080818642220111140e0b4420700032640085124580445114181180e0200410400d142ca5550506a480c084c00617501482241e50184000c0312903500c0622143d8014080c0c0f440524040600080d1602a00700100c020301e05401c1028280d88142c40400c004a10109400030b454201c8090b418142132064080d0094280f00410043c80f07100d5080d1400354141801c01c240c02d65 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 963837814 1250 963836564 963836603
    0x22103070f08300105100c0c0f0311150a050310050603090606040f020c060a0c020a0c0b120f06100c02040b2e0f140d0b120109140105060a0504020c01060b0412 70
    0x30003142e00700f4110a000c200501c002c0c1412801c140c003001017401d21030342201e210303203070000510440c0d0f110b04201c0e0200352040c400c12949191a9a0b038074400d0b00d0b802e00d60030020700c081e401c03030165000007007c00c407011000030041904d0512076070040002401d02507580c24480c42c0c282d100d030002c5410901071401c0840f4000a40301604c200e613800304160002d04115154201440064840543c43c1d8045202c0d554104000c0383d81c07078441760010182c0500440e90f4440b41c1810349061140100441b08080104d0100403450b02d8003621f5102e00310003481e0001e91002d01c1d1000500401c0500811900452003181030001c40c4078610401c0080d100c01d143d041034010350250211500c0c122040440700140a440341c0c0b0f040418401d000e030060003244480810100301c4a800704d8101040600380c094141c1d102c01d0fa110074484010b880010029082d00280079610f800070104180b00310300c1c42441e0107142d0004000c44035260a45c000c44c080c107003801440d42d94175075a41684c0000041410180d0f031107070380140c01040c0c40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 963839064 1250 963837814 963837877
    0x20a0b0a020c1c0207060e120f151f0521070603020901120e0c09220b0a0b04060b030610030b0406080102071e1502090303090405100611030304022103070f08 69
    0x11405a80100100390404101f120a4a1450929500310300901c1142c1001c10080c401400700c0001702e0010000c1441c4203429004a01014085800c03903218070000000c440509207101d030541314151121403a4541d4518452503901c0c0100c090302c514061074002184465042c1c00a094808090b0b954800350b0000305000c030111900888010229440340b0000800d03410318104081d40031042843c00c2002c800b001e000050b48421005c811121a01d0450400880240382e01c1408110036040d5001c01031141021607004680c0b1018202e1840b078150010b000c40304a00c03e801c01c604c5610003801c20702080c1d80e00c004045c043c6d00107040071200701a60078620b89100961288401006811442100c0301105200d07000000754004081c05801d4001044200e0341601c0754054070340500401e000d500d040130310700701005148615010514015400800921024be501c600702a00c00b181c4110070340c0d040040b0b03803001910703511540d4001802c19a074994003030300703001d6000301910904028400a4080d88030110021901 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 963840314 1250 963839064 963839113
    0xe0c06040e0105040e100f0605120f0703020910051806031c0807030f0f05040311070605041a0c190308190c120504081c05040507060e061603020a0b0a020c 68
    0x103148180004204602e081c0d0040702c205c04054040e605080c10191034501a10b0a40720342c4072045e910f0b0b007020061420696070768501c1044002c05080f0381c034164084152144900c0c88041e10a0821801051209841100c0000142001405003010303100c00d405404192400f100c0b113900c43e0054002061007100111101140290749903990400d03a945e00700250000c0541015640b003c035a80c8200c0c94180d2028031445001d98041d0721480c2003851184521442e12109401280410805200c10401d92128449000e902c180540403144c540c20f00d0080a40b1b0540e10405c1e4a041c1e0300480c1029080c5a000361815014611407040308140c541122941e400740d4186a0071080080d600504241f0880c25640c0010340080c4100805490004081d031034400040400d082480e44983d920288400c0040400980c0000c1009040140f80140d8080004450317002e0711381000c114100c840300030401c041c0b082c425a01c00b91f9200c41d000c0310f503050100150009400140040c860352080d8011107804000318014002c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 963841564 1250 963840314 963840329
    0x914040201080f0a022104050d03020c0d08041103241e0a090624060801090504031709070305033621010e011a031204030c0308070201120603060e0c0604 67
    0x4154903407460a80078501c004150040b12a030901c98415000d8014800e003e000540380b042481608007030030230604012140311003109162041100e068502c00110700d201c11a0a10306224101e691181011640c1d030303c40c010440ea060081101041d41c05542e02c0c04903201851110b0b9070041580c800d40d0f2803901a136000200702c3d400410100041c02c89100390045951140b00740b001040185071079203125030410016803400d51b800b080c1e1400703020156000780024010240e41600740868207054134050318180d000c02c04c610010150000054880604000ca68000e6501c4800c680d607404254480f80e0410020301c00100e004c6481c84904142c104003031580c8820b8020007480071094600b0800691040c0741010300349007040d52255030f1400140c0c02031103101e42e0303c0117601e03410072094088000c0506002d80032504041000c0701f8030003480400c0c2c100e1600420340354026600740d81c4083d240010781c1d0040342c00b943e1900140c2001804810040b140c1c2101ea0030040c000110341900105008000c010701480c080c500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 963842814 1250 963841564 963841577
    0x40b0c03091207080c1605100311070f0f0507091d01020a080a0c032d0e0601030c090510120c0f0b1c090206041a0a0e04060305060412180f0914040201 66
    0x30350040b1440200380041c410071840d4a4154214500c07810403038140000f80030020100780c01c0000c0c0c03e01040007031002c1880d1404100780320b141646401203000d100070103080b11402e03d00a104002c4502c5032110b001303410408440441c1e81e80c021110180011881600403a5036a1500c5a04d2000500a4400458460b00c0d802000d58079003c0d0b25005002174114a01096125079440381a101154464000d400000f90b804071047c00484d0400144d0b0364a4841d51030035800349004102252a44410006940b81590301048945900d0506c82c4507041980003800c3c010200c0318450104661280704a003141d44200d18010130640e1080c054200703016170b5008485c1c00d1103040d0f800c0c43c00360466008118241c8020106070419880b01c0850004094a08040360902e000165020303069400c00105801201e044805110082c110b03a01c95440300ac01034802000c54016100c402410741c010300150307107103103a140c04181c8413603a00c002013014164588181c0c032545140600144420004600300f80c420b580684524 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 963844064 1250 963842814 963842833
    0xe090c0a080d081b0708030907150801030303050403020709020c0f070b1833120c04030f080d1b05040e010b040f032a0320041515020102040803030f040b0c0309 70
    0x3550003c500400f8441d1080341503a420005500785805400c0103806070310050b403a45850b0190341c1c60800340740c00c28108406801e47c1400c01d107602000241c1980d905107008100c90701c6a282c1a0301d40f440c56000012414004599013180c843c0008240d1112801102125007807a0f075112400711912842c03510046401a0740c010b1902414070705000c4180d00010050300141800f08081c1070750103405c945403100001c00c005654020083e0010100760403110b2040c08a1038107107103a0303600c803004c0c2400c44020314500022402540c00c010541c882c4109000d51040e00c5c82101480304001d2030b5074894010114410304c8000081160210380013030320182e40b6600c0e0100c0001e82151194506000c040745010900306c001ea94031201e0082d69443c41008520604202d03d414a100e20352400724030161000d0341c09985880381c60251070501da1018021540100b17078141c04251041000c1740680324582040b00d99120000034400c941094103000c61065008501d812016182e13210150498841500c8100b0b40341d0081225 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 963845314 1250 963844064 963844067
    0xb0c070623012309130506071b0201080603011e020a0216031a06062205090702030a02150907170f0d1409040b0402091c211b02011106010e090c0a080d 66
    0x4107050f1030850403020351081180c000203588400212a14000c00a030141c2200401004002007070300146242002003114540c0d080c13501040c0f16003d40a410041150042980b0b0b80b0298031402c02c3c43c200e10380b8003900c002c0001c103c4019500c4031a04200521400028494100c0f0031961102902d0340111144c60200d007000b400b51907000050905503021700200840d80e24140308042400350482041014040c2d10b19000804c05000c500900c40301c01c1d90810049140c820340e000c5035100c0141a08003c5285a480d00d01e2164500700280e0003014480340054074a8002600004030300003024440000c0f241031603074208048880b40c1c2c040008085400b414030550440d86469048200d807820058401800d00d698400000c0810035a80e581e01c0742d80008182c584113000300100f940e4515040b41440d0720000090140083c400e41000d0001c0010341d50f01900001103a100708100050340d0b8403042103515958403003040d00e840c0b8006442c04200c52198904522103418017604000440d100340018086009017440c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 963846564 1250 963845314 963845339
    0x604050904030215010311032416030f1103100605040609031e021302121b0d0f110a090602160609051c0c1202120303011419030b0c07062301 62
    0xb1000d5000b4266100244812a800e180c000e41c00388000c80107203240c3c281450305110400002c2a1410b01001035008039990f8601c0c119000303400151030140b1138210940071401004065490300d226810a00c1c030302c2248501c03030061801541c845029041c000c1c0d6a40040c0d031144598803c500100c0c0c407040c4100701081c017000200000c038400c02300242030010701c0da0025049151a0b0020f4100a0380404c2268001c4003400750690301c00c404480081c3d03c02c242030455441c83c05500602d103215030721110b0110341c29900360003a100c44003164011684600f9000805020746a40d13010342c400501c5050010200482500b0000342145c0b002d80381c0c41e03059810401402900095106d40700d0460b0702140301c41d40014140d100180007003944030f011900301b50152041103080001803452000660061005000b140410f804110700e0241c2100e881c4003102107252500207040da180d102800c0c000840040104482c512001032101522611007000407840c1f0501c184544058101c00d03100c009006030040c4003c2c0441e48 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 963847814 1250 963846564 963846571
    0xd14010e07060c030206060a08100903020a0204090b09060a0c080a0515030706030c03060914070503101701050601140a21020d1d0c011b020f12190b0109060506040509 73
    0x20030400c031228801454000315602680c0000d018000f290f0505605204040d04072104030f900e006024a4448040c1d80d41d0028107107580c110b40d450603240d04050081025142499016100b80000d006d6030401006c0d8240441d03520030240940000115820190b1040c40c40f1046180c80d60501500c641151a0080a006220b00c109080454440440d50360422001c1d0003003c00d41d801103502c0c0300124004054645c680d0044011341e040c2989804498803412810f07620644601d84a6101d03030740c010720720380070f2285540900050032044400c0312001c03006400180c403c1e4804c0e2944d41c0c006520026100380d611800d8400400130341e801c3ca01e072020b04107080e0720039404c4030301c001c02500748005810440c00300c030b03000840d0507500318642c50044d484041c28480da40640e07001342041d40140c2d840fa60010001d0811400c000c0c81082c1901e2121060380c0d60007500e041288400d01101c110321149988100e84120000c0c0599030000c1082c00043c020030b55000710b106a80001c1c1c062410301d890042803000884028 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 963848920 1106 963847814 963847853
    0xb0a0b1c0c03080a200a0506010501050702060a080604021909030510060f06030207030309151d070b040b09040b09040b01090c05130501050901020727050a020403020d 73
    0x71140700202ca4200300102c2d95080501c100712800c60603030624000c2c040c404074006040b000d0015050750740314030900485d0942d07601c440c010b440703501501c00000d62084042100e101628445c403c10740d000030020b400541080e030b50072101c0a00349081c0b040d00002070143c2c40d0410034418200903603082081640c40421611b03041440606503581c03d030080340103054000664404141c03290344105c1c16190807003131841062040c0051400030744448202c1500d03040345185510343c0b0a1012880328125184070b0101460300749840c00401c025042001840c1d0320941c2d802052805458080b1132034810b0b031242c2d0f1620b4841d81000d03105022510076207109010040c051001c2c1e52100150f01c4054140c41c07007428510340b900c03102c80040b0716201c200e4100304000a000d401946448980c880344c543d010402c00f10138001b0307a03190f8000c0d00032030145100c041d50008030a41c0040104103041914007180005 = true := by decide +kernel

theorem cover : BRFrame.Cov 963669064 963848920 := by
  have h0 := BRFrame.cov_init 963669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 963669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 963669064 ≤ n) (h2 : n < 963848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
