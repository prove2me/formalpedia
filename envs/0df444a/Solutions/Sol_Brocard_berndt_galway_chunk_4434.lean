-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4434
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:36:05.465667+00:00
-- url     : https://prove2.me/submissions/74228d9a-d471-4cf0-90f2-829c6c3549e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 797302158 ≤ n < 797482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 797303408 1250 797302158 797302171
    0x606150901091403031314040b0d0b0a1d071d06030d020c1315090207030e0d0c09051801020309060708060a030b0a022b02031501081512010f06080c09 66
    0x9510300303095480000c008941910880d54408a90707014141155400e005841001304412400d14000d40c0e90500c1c400c1040315401c502d0f02603850720000e0102424410155013400d5045890051543c17204401d680c000c10349014407282c600345000c0e080d12a140c09000321001802c1020484011102c640641c144004016003004d220f54004c0d0f100016250f00030465480200044a03901a81c001402c0140041c1c645440d000c6d64072070b2100b2007c43c2c03600280e4042d225840c06a6220291080048140500341039040c40242030000d11000c20418040b0b9a0440c81c0e0000440260001d036121315100c007801d81e0000d44100b5025080401000b00c042d91010700b0781d6100f00100e40f0041404c0c619114200d8510020301440300161b000039a640c88110b035500c1c800c9100c9810700d480035006040c121410025002600c0801200444400740940c540c458003006008a05041071401664511010440100d950000c00100795407111001c00b01e0300034030701c00c0900130b10858005e4403058040104018030080300810f00c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 797304658 1250 797303408 797303449
    0x9050901053109050a140601050904120203041a090907020105130b0a091a071b0201050a030c090504060b12060402180111101d0d020a020907050a03020c0307050606 72
    0x40009686000361452400000c00d00b8507401081d010300d80c0c07008041e1000140109040034144000c0100004c2d00c00e01306809044014030000c0c0c00840551182d100f2320030f5503031120044000c503010402d030382c10b031401d003001500440345803550300c80c08611241708417003c951001034045002109400d00c8a0071070391082d002d10003000640b50070181c40ba90160322440c054840c0c440100045e007007040951042d14000e03080b909400007980b042e105071442410407600f000002d5102d5042074141d6100c0784410302203503416181c1908220340a001180141500702401d010040c00740000216520f0314803505014000301801295a817031a9014500030707400c0505a240514410403443e01c2040840e8104c9060030001d02c1c0107170044000380710151400d1184400000024584103440225109829581d00741d0800f201c1079850785000000c00340d85036551440040e40001d1000006845980309600904915400e41401420f0801d104090740c910303001008202c80079800002030100d5494105122001c0e2841c0080 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 797305908 1250 797304658 797304661
    0x81911010906081b070605180d020a08120405010b04060824010f12022701090b010c020a063501080c0603091903140c0705130e1b03031c020703090509 66
    0x20002d1050340010072054030248813182038040c140070750007250005030300304200b40003904110000c1c0b2080301690101403091f10076031014900490002c02d500c150550040341141c10b040340d0b441755080040d2f000704100c1d465540c5440030705069840e445041c001e8000d00c1e00070002850300c00300403140c484e89031492040c004281d10041145c0d6000c10860000e80e504100c090b2515481880450502c240606182500c0002060408405452010100e04071070103d0010b10466035581e0040d6443c0030f045802035000100c0c0c9000f0b103c1c8500484402300400b401c0c2c8800001266842e2001d400801d64100610700c031002d90b401044a810100204102c000d000c40c1c50500c0c50030200309007550f80c170f0710400d0130705010024000f420030316014540005012042e481191350715078080b50b685031074100f540156485145171030b0501040b20382500c034031030001c000c1c00020160f00207103000103519640c4280ba41035052104004070310302050544440512244044c40142e1103100c80c2c90040c0006400741c0107640100d44c00310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 797307158 1250 797305908 797305919
    0x4091805010e030c060a0e010b0a030b040b150108040201030e0708070f0306050622090201020307060f0516020d021519020c031804020f0901050325020a111905190819110109 76
    0x117900707820100320b800c0001c0d00440004802c5c050010070944c1c65003c00c540b0800018400b0f80020b09220305c0c0301e0b141085da640e480c03034601d20903804da00c0e00d010b00152a4800240055001c0c1e440154014428412940d41d19a41c001d00340c54101580c001c3c10211030084420000c22600d0300031107030001c0c2c0448416103001960112030080c01149403062410b141c68484030300559000340101c1d072407a034200d0b40900100140c512040c0c05840207852869050f4540064500580c1c03011860304218215603018082c1204034906915044802520481c0c0d41304840350416032040d820702c01081190064000b0f9a00e540c204141c0c031545050354540710b800f49004010280e440807085c1c08845416900b4204207131207031214207294003202900303a52102c2c40504c000248440540004144400c2031061807a131181c1c0d4800c50520070b0000440e10789c42c105501410061002c6e1910f0b400040d0b841044010b20560307950340710b407090715003170404003c0061000000d662601340f00e04080c00c0d102144e803c0c20552105e03803809 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 797308408 1250 797307158 797307163
    0x506090c0313030909050705120912160320010504140c060403080309030c0129040e060c030402061215010e01021b090604060e040818030f0304090b0604091805010e030c 74
    0x40c8080d000c010382d000c05104142c021101440601003010b0104803520700104050040e510000319046540b240c0000100c1e421000554000c1034024030790b80c941010350201900c502829480800c40c1231115044000344040005200030303050355030810000c1020308150a040f41806c412034100040703038002c3c0101031666181c21045808595000040c16038a98540540712b04500440341d00d0130322035080000e110070340001602d44620003036074281c800c0784c00c01410f01004119543c418a5407a56006000000c1e0b220400501440c1d2007030001c1d10161401c0d116103040c2440c0d0404540090000060351401c1310f0035680003104c840704449c01e0004100152007000c800301e004060030002c1784135210290000f14a80c030b40750400c4009000030842d04130075003410f20b040c000680258a844c00c9585000f1007050742d81c540018030b03103d840d070400080c51400b07007000c0780000a402640061030700030004100000704034911f4810b81c1000350030607000c0d01201c111071804900f07403810900c5615865209000c0b000c4204c002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 797309658 1250 797308408 797308411
    0x8040b0412030b0d140115061b0c051305071b082a011409010b060906070602090d120e1509150c0a0501050c0309010609060e22020307090209040506090c03 68
    0x4041c00c5450744a41d04100d019050012001da00032403000b18640400c8802a1404200c1d20726000074030100281d62038040448541d8442e80317000415600b01c12a81ea000740a031401410b014100d8104050740380c0010482001501d0181a66142c0c0c50082004030f540c0004210400c0f2071203080021000d10544884129000b501c401e000038070b218140c021117204090241544400d0140001d0100001d65121ba000426045404911399420444923042a190202c122103640000071310550600b18a9210301009412440e15039400c03200c02502840810034148894500c846140d0301e00f2540500030080c002c0c00004000100c0070b0007824440b5100e10f544000959603041c02165509407170b080c0f54688185070220200028215520f490300381b1800d4007480008600c914101c200038082d01e41d0b2040044129469407040b14002d581d4003000c40d03450152000c119104210066802034100c1e09500024141100e42d8040b05001d0750020344110305040ca8001c1c50340c06076048440011521300040c400441c0d210 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 797310908 1250 797309658 797309663
    0xc0b16080c07150e0f0307080a0803070e03031602012615041506030b0114040e070c140609030918010f0e0c040e040c0504051f1806080322050108040b04 67
    0x70408444028042040c14010101d442005030443c02d89070b0044c154624000299000b041507007510001c40c10002865021a5602001841d007941a600e400405030000307040341c130821801801d80728640e41c3c10400f51803440b040312041081e44840c2e01c0054481d881401400d402810800035900c2e5000340900311942c40046401442000c548000004009010410300040350015207240896120361690200c0c1c0c0803202a01d8840480440c0ea40000c8140218850314841044010005d02514401d61004401c0c6201e00702c845c0700c3c5040d420780a814404d0440710101c0a52003c07441e41103500e012002d0050003241c0a04078511541080c003020883c001e03500800d07211142c000c010a61032400141103500904641600171700300c0c04e00340f402080d200600c0c89120710407418030001c61034642c0491280a8484a1000212007542c6400344042400508982a03880c99555800000b15400144010041c418001d22202850304004081080c11070075600058100b003d0042088005141d1304481d64201d80c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 797312158 1250 797310908 797310923
    0x40f12051c03020d050903030106080f0c18011431030b010509070e0d08090114210703020409020c070302030f0102033102060403030c0c1401050d1e15030c0b16 70
    0x1407550400d41c003912406130601c1520b40b41c5010032107032107070100185059822990300d0344404e403101c04d05080750050940c0c640b50303410380800c001c2c2804040d0302c031500b0b070303044040c141103140f410740d10840c2d6071b03c0d00700d001002d40070008145070700341030001081034103000c010000c4044196425a207850700381c60014001c1c0d81c0a1089080413803822402100a41c846580050008440030004e1030503000c55001564818085000c0614035480b000b200c10a8801103881c4004000000002002241610002400c203409140d8200800f10b030014050006092140100e401008110310314070606103800d042c1c042b504081d91040c4141b200310030743c2c3c0c0910200090289060715003030b80c0d0210094011540d860f4002d500003000280007003095080384000c0202801136004940e80c688d6020078845c014400e41d01c55001440c1040480a10403080d0700c00e02a509084a20400107400403103618102d6000b042c0d81d06d03003800107180c10001c200001000c0b0014000f0804004d080c01480d0241502c8150007400041514 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 797313408 1250 797312158 797312203
    0x8070603020904110f1305010c08031306110307091a0307140307020c06070b0105090f0f1906211511030c09010c061d01060504060509061002070803030c040f1205 71
    0x10341daa82c01c00c40e01d105104d0100d681d01e0700b144400e60b1680e4004055000424000c54002031207601507050350010540044003903155644d4040e0405811000c0b00c41110302e0399035011102c4103000384002651003451280c58103c18141030a4014003509640004c00304140d90400130450200c2d0b011043e143d01d00b42c0700c1c071820740300e4641440c00c0e030034079110895643c0c11400120f100402e04c541c202c3c2c0d8904a480c159201009074aa880421140ca902202e582001c60414004900c1004030b1145006640d5044040010130b507403a0445400c80c00c0c1508244002e140c03464080406025103007011904001c21840c0c100078111010512840a000c000d145148402c40411005c815034081c1101e6010b680d44513a003004020003082c1070305074445550034844400e41ca4100d01140c070342040e1003071000340ca03401040b50001e1350300e01c4200040e42d80703400e081e50214001d9010014040000304081c0d070184002c40c003269152410300d148a00010310540c0800c0c40000201c1d0002c1c04a40041030202e0300d8076001c843c4a82c07c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 797314658 1250 797313408 797313427
    0xf040620060705040e0105011b170f0706020c010e0601080a0b04030c060203090601170d0e041a13050405010b090c03070807020712050109060515090112150903050306030706090807060302 82
    0x5044040d92510580141010400e0a070303401801402540c00c41344424400d40d889100442e0810000c1c0410000900c003607110002040c0c800307019004a5003080c8605251070600692690550400308044503041d80104010204030400e0181c5c00c4000340d994014200c542c9021006943d4100c004d0010f80078034691004a0705042c4074500c1c001d44550448019540ea042c91042150307107500902c2030000450300085542c15074403011419100d040c21941c0c0b81c404000e524400c0100a00003481c0f2000c01e12045000301040c2d032a5810920300c6c0300110303c4001040d00e4282011825526511015445850710340d04000019585806494020544d40703040209581d40040903468000e494000c1c007400701455108000f0010150421880244558010301c480e031981803a44024103044810310340e12001940c010322010b2081039a400d085030007134000b04065600100d0300801c440383c05005900150000007048a541810043d42c0d0080c0910319081403864989001c0640b6003c950003800201600082e98021 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 797315908 1250 797314658 797314697
    0x1503010905062403120a030f14060a05040c02030901030e070f030f060605030105042001030f050c071a0105030c0111030706050c0403120c020609040c020c0909010c1e0203160f0b01090e010b03030f0406 88
    0x1161101e03c1048074039400b83c0044c0c9d0020b002c4404601c6007400d000301007140d080070300600d422407105070015400e00e1034010041d00a4003100c84400058841c0f100c0006610303007140c407110015405048003c0800b64039050a02c203481854003e10300980c101030038040060140006003007401c0d114106001c0d00300e800300c0120041d201c6c814014915500703000511110400d194024848284120300000e205002c2c101b2035024120244526070b811780203c2038884041d40113080f5808210f0400c0d040d00d00c2c01c0680c6d5901c404950050324020b00d8010085401e04c100000550030400003a12400c14021244513039000440303e01c0390010550180792941c02d00200c1c280200900b0951000051000e078503441c000440030f0090072402c0202001030409880d40440e44007025942c200740c8403a030f01031441d1140541e1280e5903002c1081e4100c51444080315540c0103d00c2521490b4003910704020080303030050118800909440b602d281c240e10980007049100c1c045580d04013210211448d50800c1c4114484a004e001da = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 797317158 1250 797315908 797315921
    0xc020102070b091305040b15010c17090d0501020d0614030a051b030c060403060b0306071b0b0408160c0509100b16060e03030f0405011a13051503010905062403120a03 73
    0x101c4c82c070b081c80e05001c1005980c0b4071441c0308076034006030a142510b2401c01120350250780840038000c9034406210b02450302000f0300a0120110140c444d000da9840c03640c0e4507003203a0041c24251001a80c41900f4001402ea0107850030642c0811401450500b50b15203803651115440355020000164101c4506042d07181070004030785c0481c0c020b1203203840700d030349040c00d60182001070b15371072003802000b00107451103000340c4c0d0542485202955241d07141c1103e035590b1480e4a006802520840810f06c801620380e5160000c4803c003078458803d52800915250503c0744062010b4406a03580742944c40901002c540c0205684042481e9030340c001501200c0d09148008110300030f41915203000000030401101550950a401940b0913002080300e945d642c0249a0340d92a90302c003055000d48840c0442c6140703c4076401680d00001060340c00d0070401d10800001c1d08580c09084200c41039040b20040150540050300040488003003041048240a00c0d50002501c6150710380d40892412400715010200c544a0b90210 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 797318408 1250 797317158 797317189
    0x1206031207050109060f141f0f0303170702070b09010e0609030328050901200c030607110712030903022b080c01230105041e090b160c020102070b09 65
    0x220781d0741c1d1040c24498041d0003200000c1d12030314244481c030604900c003881000000101c0c0501400552282c0341c21504418a400300c00c90590441c1202103261604459084000c5102e03454005a0607642e840d00403a5010040c101710a542100c40100a10340701402101c0c0c04e240d0900c1c0100300101c412000507864051100b0741a098440403e9085125115140c0200e1018011042072078068080c3d00840d010f02c1039001d540e000403202d03000480c00c03c1542046041d500f1040b0309030340e11002581c010a203420b004482c1c5400140c07003100f00103041c500920540001d0b11403c58213240107942902d010b4036103122480001d020326940680349641b400740c0d01d64a02d0b81080300d042c0781c2c10300722541404c07e82d90b00b0145051440707501c1c3c8078980300c0354030a01840e08108100045007161607803800c401c00c4010004000740d4a50008558101c40440c00c061040e0380d2114400c0203c480d107400c00300b02c04400300320005c0c00300c0d0910040a0704240503070380000d12281101d00000b4116600c140d50b4001c02d0381080b491900 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 797319658 1250 797318408 797318443
    0x305010e01020a021002030c040501120f0911011205091e12040807050112090c180f0e06070314010303053a090b0a0207080d0e150115090515120603 65
    0x20300d8600041d001040d509100d5401c950500b20340061400491105491201894400304820455940520091024400e90400008007006a03204201c01e1711140c60049540c9505500c0c0400e256800c568004032039110501c1c00c20030784c0703000d034515a95020800a821905c0c500303408160080d410402150b00c40301002200c40780c9481d901c03c100c0c0da462540f0b014140c0461b8260358001d81003011441745002013608410071b48071441c9400c1c4d4446407940c401c03496020664480724405150812030044c0d407800c0310200c00030281454403981c010200d4030b0741c41e407140000c0040c2c0010404203078060155030404000440000301c0c40440442c88a03000f4540b041c0c80c42c0e040305941e0b60228605c1d1360f44400300c624081e890b222211b60780d201c0820200d2080c1354000740000018085c2c65070014440d803004001e403488404444c070030304101101c001c0044003648010349451100010082c00750f40304a06100522041e1004114501a400da08415000d000100f01c40b807030a0100048481d902000852540c0414594 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 797320908 1250 797319658 797319671
    0x3050a081207170604150f0b04170c0102120c150702030307090806100623070f06140403090312090b1305120a020904080a030e030301090c080a06032a030501 69
    0x404041940100700c182000556641c0040e5207680540a41c0d00381c000d04010300c0303030169101c00400005107140850072000c140f80040202d0b48907400b0a6810144c5002048503846524003c11049010021101030720345421812885240e40d030005038260070b1040d8410308984940da82d05110349403a10461901400801d000d05001c04150080011070055100c1c1d0341350034095448583c0caa0f80d4100c180e940320000c1000100030016203110b10b030b6000d110340c001d1541801c0070211144042294110800030740d9245180845c3c4003c00010348940c50381d02c00417021a0f195481d06413000342c081c2d60b651001410f940d880481c0f0080603442415a040500075480d1420f0703c400390116034281800b046c0c003516001d900700040c00544c003c0000fa030300e9100e40c5e00400709003040d5519600d0790b017240c11402421003810b898000c1502400d10500c081d6020f45100c40c07001803c01c29074a0000c08002c07000d80203d034124546141400030074403950940741d40056050100070300410201c819400c075800380d480030b4415444d040 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 797322158 1250 797320908 797320913
    0xc1206180819030b13020a09050904060623060301140102010905060a1b0c080f0f19031a06031e1513060608162109050d0e0a0801020403030503040206031003050a 71
    0xc003400c0c464602d925102005401c0744010b404480390945036561042c3c424019141c04100c6800400c022241c0b481d140111686c0c0328040717038000800707079401c46000b51101020710000d590521644004c200c00046801760401d1500452118070042c019010300c800201c800c0c848990007508490f512560140c112642446e0016406000b040340000d03e0328501d50341c00203150312a11810f11281c2d01504210042d01d0a60081203440c0703d5480703030351310000312070003801002c1c420f0301d46542c2c0d1192400c0c01d840222380004aa078014281d410468802d9100b010284140f158001d81d55201c0380884000360740c001d07010345800c5034066003088404c003000e80c840c0302c981d100068482160810807c4442a4031100000e403101d510b0002c580c02e0100380000010290030700100014000c0384083c44c0e0700a980c100003100107142c3c0740c0c0d0b4103000107100790310f0205480c1000c5220600300400c8043c01010303444021801d00341556001001488042d00281c4514008404540c10a4540d01d59000070340d031040486800701c8003172 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 797323408 1250 797322158 797322173
    0xd020a150c0b0c040506180a0b0301060518150d111b0c09070807050712200c1914010309022b110d02010804031b0813090e07030c120618 60
    0x400c200d0700203080380003207140401c0e030f9800c1e42d05070f8400415140c241813030702280324200c0744503611160f8004c0401000041c2812242e00031750280941d0b5444941d140b0303034284007940000910406030300030005811442c05000240081d1039180c00d6240000c900989000175030305c01809100700c48101c010340c6180404c607611000800460300c0e0002d5aa11200f542c481314190303056a011210b05010038410442c0c0400a40004480401c100d10350800400001c400740c4201d00b02269640596410750040044103001c0c070302070a034144104620301402c00f282d42030501520f8140c0402c0c4100e03044c9925129814110750783d00c40548200300103502c094061000060035003003142281101560100c0140414540030304101d045110101e4068403100180d451300c0da811108601d40d411110240c2044000c0700c0d000945482c010040c541100000120703940c141400141100ca03268007002284c0d01c00c4408000041d044074611084801c508408440901c60f41018400f0f4200702d0306d24540000111944410000d40 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 797324658 1250 797323408 797323427
    0x7090312181e0504060605070b070c05100203041103070b1e0f0a02010506010921030e120709060f0e041e08040902040f1809050c061803070e0604050c0a0e0d020a15 72
    0xc0c0d10340b180034180c0c0c400510080700c00380d0003800c00041c020000340c00032680700b040ca0750b0805031500c0c1c224900d40e0152111030822040028024a0540000600c0140700da041c1c15910001801c9018022052034601204050b1048106a081209650810700701d0410280b0986810341316190000e55140b035540c100038020042240c4e40b6002ca619040041035251104103d520b500b000700d0603004417140c582d00e054410b8080c54400941c0010680d01d00d00f46000e0502034400100f0700d004000c907029040c08001c5038401074a0b008200d02d56004010030000c100d508440380050540c02c02c41e89400d2465041500300352003550403004045000140010fa80d95049144508aa07a00c010010340214003120010580350310101c080e0250388240e5500d04507290003001402512501804495a0503005000c01d0a00d01c0b81e52080042092910800c1000d040c18015154081c042c5e5001c18540059000302521076201850f031140564068030811045441d18610b14004e809c0321002c0c0ea40d480c203410360040c10540c9 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 797325908 1250 797324658 797324699
    0x140c0d0305090a0f02010c0c0504020705010c030b0f180603030403050604050601060f0e1f0905130902031c020a030f1701141e01020a06021c090503120f0709031218 72
    0x10700700000710507002c0031481c05462503104140c40c0d03058a081d001150034898644d01039030b02018028001440d80c3d22031004180caa88540c00100340320f0b0200d1405821242d030402d0b458082e121a00c02680300d03649802c0c82160766041d18000000c540c0398000441c0ca14003541e040205948036880500040c000001825412580a65aa04951070521030200c44420b4a0600550050301c4501e00c100100e0100305841000c04280c503020072500ea496000644010b140104602401d560314100400d50900340045030301200454102d601d00060303100020762b1841140b0000c0c0412841001090015102c0e10403186440015071501c00b0710758446508005180c0c494441911490607403a000d03103560100f0703c2c1d012001e40e058024184034922912250081d502c4144a40d4101180904440c11b0114a206600344c1c1401040150303190702c181c458004401d04042c00300700324410103204000e2440d0740880c00c0c0017500d03481644194241034a82e0281d4440d581003009081300c1c45100c2e00401e4104286041101040 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 797327158 1250 797325908 797325911
    0x106090905041406092b052b0606030902130209030304030f080c070905060f192c0702071d01050303090409050a0f0b070f030510062d1e02010c0c030807140c0d03 71
    0x8410700b1908580b1514036190002268003489651140032821382c45840d00b2344a0031980a1301c0c495204810100c9a03103410000102c2e59604006040d8203211551180c0000081021882c08810a000940d07030b000e540b0000340310b40c551301102c0c420816407600352039070b82c00c25070100c48500d40c484044102818080340c04501803110032116850300d02e021f803100b0000d219201a2400e2140c2001040c0091070001d0252545406241c8203411000606c000c2481c4101c0255014140007810003001504441c200026a405a40601c005110540d0007100700e0f160900c044900046400f500d00e412400c0c402c50100150410b08050b05034030a2154450038107104414079629100001d9003504190f04440e801c0c2ca02c40c0602a10707034814450315008035101c44440c0e03e04105000600e100780080d12131143d10321011000112032841c40d0421540c41240201d42658900003440380c49021000140185c4c1020b80c050100010b440104506a00510801d1442004c00182035900c214030080c00d90303a11868500c410000b03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 797328408 1250 797327158 797327203
    0x61703033705040f17030402100e03070807180b0105070308010608190f0915020c0a0f02041d010b0a060f0206361605090105060301090c0e04020c24010609090504140609 74
    0x200c1c11702d0850744140e43c028085510080200011204201c006103a650580704102c008950500100803c400801e07211140fa007945084120100c10740d0020603010781440000d012480002e90011411410b603442441c01030065543c103d003000311001c60080015616140404084c1400080c1c0c1241c0b640c103000e0300510b100000462611412071043c03282800603500560449000550004120b000340c1d030004101003210041c6071021591141d02440f0381e40548c0d036070b102210450038880f000000501c12401d01c0e80042608240c080d480300c100400c007600e4120501000d01058122400f865840b07c40c0492150345198030444859a4004180c15400500706645c0c001405150850020381030310005070085085910b01210040941001c0280c2d5050068158204000303485034400307001c10f01140d000501025a01c407503000d030322002042c0e044502d043c2400041c4001a04000da4030125a2a034000080700c0d0340e2801d00d0a8016100304c5007051501882051144a000c00a00f40010b130030400d2001600 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 797329658 1250 797328408 797328443
    0x3030f020d0623060309070513111b0c0612010e060d08030a150b0a0c0b0403030603050607080105090717010b0c1006031a0c03010311060a0e0a09061703033705040f 72
    0x35404101d50b1043c0547c0300c0d000c01e000a0910081c404444d40c0380d00e402081d01d144549401805030402d00340350841700812148441c00b20030421005000c020b0607a021071500134000503607030780c5d400c050140401130307640c48012480580310052020001a00b20403242d480e800c040a08001502800159480c100e5003428080791a8925004a403070340c0145480d039200010711a65040c000c001c0042054040c16079804000000c1041402024032802003542c032450250b042904110341248040c100008111301c0003e122900084e8041ea01c2c15104241e085a80b01d0f415000024a0320b0101e103c078012260800600001304840c2c251182080301401c4d20801440c0d8602c1c1400605000c244000b5104456a441a6005c0d04140c0024001316115241c151307168090280441c250a41c650700a140fa1035543c8410058280c0c40250782c1d074070100600140d4a50308004082c082000c4180d40313000c0303000d510300841c02c2d401d13009542189100200480b00380182c0c078017030410f41c0e400401100243d4540c203900688001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 797330908 1250 797329658 797329669
    0x10501270b0d061d0a05030316110c09060a080708030901171e0a11070b04030e01030c090b031509041115041d0703020405060d06170d0c03030f020d0623 67
    0x14140d50107048481c51242a403180c0010340700a50481551421107103101c400c105084c0411085c2d80c1c01071004550b80c0c2802d00c54000c0c4a40f81005400c200003000e07003400c820010101d640c0502c040c0c111104240303a1501e00008041e1503680c0e10210b190701c124600010b85410120140501800c241c0300d0000d080d040540f8414804011601c000c1500030040d20741c4520a0070000c056040401d00c04000b60f08103400b1541c0e24079501080e419140074032341c14104010903521001c804003808081c0f806010710459a6000744c04810580502c030106640440000d129021126581d048520b00404024450501d0b0601c00642140440c0b094003411040d13030300d104505e144900f00c070100da401000381e1011002031f4a003096828005800c98082680800000440c1e03610100941641008640d00080443c90320080c1d902c500211344ca554055003103240e584881c04d070408142c3c4112038150501140c03040da1800c0c1c90b00244078031001075016514250780424810701141c082c0d10300c01449400c2c4c100c0215078404028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 797332158 1250 797330908 797330921
    0x40f0903020721050607050d150803130803180f040b22061a040603020702011e0e04050609040803131a0106110d090302130b06040b0304081312020a03060903020f01050127 75
    0x14511751121011801040c8910010100040d09440014100201002c0180210100c4d406220107030700200b01da03850384102c2c01441c80104031210045281c4828030050030941807441d01070318410000c8030b84110050710745400003258008018403150301d00307000c0c0781141c1c03517250a14110b080a40c41c00f03001003003602d601c0015a017400350b03215040c0e04061a10808601950220a080f4100412158111038800c4102102101c040c0192201466102441c0c2800f00702c1d00001c0a603032051031100c041c040421400021241c000c0e845200e1080744400c1410001d0302000c403141540c9000c1c100e1800060741e140c0c0600c0c141210402e00e42a24005101114102c40c160200d00011b03500030a0b41c02c00f03000401c81d0ba0f001814104010b40290f041039543d08051802e900215010380300d80d1000030344050200040b0301c01c1c0c03019003080301c05241c242102e5000318030100710600004000d1903030b0340901010b050080020450391210325001344010b684074040408009007400101e0036010100c50040c08a42d014040c09 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 797333408 1250 797332158 797332163
    0x503132d03020f01021e0f010f02070c05040b06072108090609151f0306020d05070203030723120412081b0f090f030703030302040614040803090f040f0903020721 71
    0x403044181141c0800c010b507007802c1c4034103041d4031420882180c220400307a4601c1c08a400c50b4043c241d1900c1c0018074500b034aa0303c46c00101141d10410007100000c0240e4074040950f1001d41e0000307040155a004580b81d4070a480f13018104145c45c4455040c1c002c42c43d94007420b8180e65950380c110a450b21102e45d1f960b0581031310045c10703035000801e00c2c03e60700d41d048179140e42c0280084131000781e200a040c05408514016001610b205400059100c25140c1c1c41c01050b41001141c40194a9440c2c20740e001411708145040c4002605020f0071948900c0f201802625840c001d81303c1c0c803444609040c03401c0541c0a10003402140071440840018060700200d0100e241c4200040401a10b080c1c1c0b42260041c16070300010000350301c01c456003042400c0e80ca081002a01030361107a2001682e5906100025140c054224207000d1006400c01082c071913a0004429100c00a44c1a508510b0700c61080f40042d0103000c5420741c41c0c650500d4a49040149036000440f01c0c100c8006001c00400c01c0c3c504010b4000b10464410007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 797334658 1250 797333408 797333489
    0x112050f0f04151409150613090303060f06030f050907081905120729010506040b16080c010b040b0d0305040e0403051e04060e011d011b050313 63
    0x2000d190200240ca0b80c0148185807141003000c030140f1100895070510400d0b90f41420f04d03810806042c00401c1803659020f811803030100c00d0700d866000200c0c00200c0a003070303909542c0c0318803d20b0105402904403a0107400c03220b01c1a958543c0b2001c2c01401424100704008095051038003080d0002c07000700340d40c002d4503410030151480d02142c907003039603042d0444081102c03144142020080240d4210f0042d000c800e101d241c023086005500d100d08108c4401d0010041091070b019001000f03196600c001f15000c45602e0340c6000e8482d03400c62419001e161100100ad401c6044c001494048060198440c0300140b10440e020018109001c0900c0110382980c00010041403040105100c41c2250a4629621070f10915000e840c1c02d6580314046a40d01c64000f880d4044100814107000d1260440d298568841d02803030440090132060498000c504181410281840100c555044c054113507010800300d06508001100c2d81d03490030903c034020660b018440c900840c0c907006840c20300035203007200284050150000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 797335908 1250 797334658 797334661
    0x150219020609040b150c010b28090c031401031112070302060d02030c0408190c120b070e0f041e05060d050601091a04090c060905100504090c0512010e060112050f 71
    0x1071000400c000b82403903510401a142d10301c2001d200100901c0380710f0340c1d8000820403059023807e20115410140400f00d00302014065209914440100c80048a4082c580491000b10a0400b07a0007010580c0e0242e9048075a10004402c0c402c1e0361416001da0b80c03064a03002c509801c840030668407082c06000080d4401c008200c0c11940100c80e070051608103d85d400320302d01c0d03d07907221112454480c1e40985000100a0303a030203c0305010002e2184402040303540c250171070460080d51030164250b0000c00031b0042c0500c0001c02907179070b121030f04411080d08014000700b010b080306d1a582c0c002d080b00304c10724003540c5051000192103820010007030a205540000140f19503405c144804018184c0303090350b03002d028507c180304401aa03803070069841c40c0b8060a001100795040c60401000c000082d000700c0e004141840010030b04030f50103000c4030b08440340424001407140c0c00300e204036483c3c4254080c80f401e5402800000c00d4901c092130800380205400d0300c641e03a45d426001500230035a9002c0728071003000c00d04d480 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 797337158 1250 797335908 797335927
    0x2a0605070807261f1d01031a07020c12010605030f060f070f020a03030506040207020d0b06010e0102060c04140303040f062d0909090201030b06032703030f0c1b03041502190206 77
    0x40b10b480302c2c1c2506103082104c180c8441c103030030610070041c00c03070203070300f5180d13401003060114440e81d103103410032000c42202181c501800060f6850340300e40c8415001d0103410201c1c80b4088800c2d84450003801c030040030f40703800c040481c0050303940c0c107800e40700b501c4507080328400b15584c1c1c0d00a064061160ba03054016184200c142e803415401844010543d40c1c05c076401300006001a038880c00040740d201d100c1e44070f10546d0b007020b01c00102588480d0a04034159800348080c4410300105100341c2d0300710741183c048500c9504020021906500550f8890240c1402811001c9106604404136031210090300c8142c8002c80600c0c140304030240143c2591501096611106108070030050f0005a82c550044c14082415100760000c9075565004840e9011140c03003034002100030f0540e8000207003001507034034029821400d01001001a04401401c1140212030000e500b0600094250f0100440c80303008007503944490741c03009900f401948068a1800600880758129907428101002030300d100e030046d00080c100501315 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 797338408 1250 797337158 797337181
    0x605010c080c0330070f2007030503070f021c0f03030b19080106150504050f220c17070206090c04150e01030609060605102a060507080726 61
    0x32a121409010810011106441c001050440d02c41d60455180844d07640f4402401c46980160141040250701c1300e190031400d5110741607803540968810052410325000c0402880c0c100340c0c3c1d1004106000104190b0144035036000384848070380c000e98908452403858481c6a103210301590380145002140c01074440030a02c030790311445e051140503102035070340000c1d1404542c0d01300041d4400a5aa0346810062102c00c510f4100c401c1c1084403801c01030700341400d2100143d541c0c984104014020a080c40c03203211621784070515011040200c420800c9084120b1000502e9484000b001c1c104030138140e40440c509a200003143e9214a100b44060001424000104000745c480c1760701c4c1d20320400031940041a20a1510000e41c004d5114900000d4464410b207841c0381078030419884148105603c2c0402040e0f81d0308100022210a0040106842580c01c02c900a9800602c0080540b00354a010100401d482c0c11007403040c010f045d55220724640f41ca0b60042ea01c00c450019000f84030202064000c21800d4510 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 797339658 1250 797338408 797338417
    0x6140117061603092f0409020d1101030b060c16060f320c0f0c040207351206120102031e041a0f070e06040506070b040c03060501080a14010605010c08 66
    0x500d0040fa00030b140317880c0d20608000b0705100c80c0c1d44c42d450030080c0072400e1302c0070080004400142c605001c2ea05158001034219110071102800c0006440d01d0311195030711170f0b80031064076400280b00c6600c4804405165684a40c0d07450400d1394440340480c0450050300604c000b40d0508007e50b2840c0800a49485000491004212030040098441c4042c0c070302b00c030040c025200116905009100e858600003080d403900d5140d070b46e054003031403040140707901094a004104069868002800600c86100117503040c011420f00101a1820701c0810540314403660021880e002c0c56044980d401d0070102d040d9401d080b0300c0141e50400042150341d40302c8200d00c001d8121158028010140031100d00301001e00a000002c0444405c104071684100b04400c0b50f400003600b055503841503d409090900340380102d400c1c1c2c41841d10213002c02103000002001c01c01406074400203103900039806d100e596520814681e80d002011800c0300c1e51209003909030503085c41449924210b0340141e44840c8449a41d44800b24143d01 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 797340908 1250 797339658 797339701
    0xd020a0b180c100509030c0a0303081b07080d0605040f2702030a02060c0114091612050c0301090302070f05092a0409051512010b2202160614011706 65
    0x501280e800c090f039a110840c41c90345103d840c0d03281d55680309010542801105e0099900ca445800c0c1c0030300200c0c0e805201c0c42d0f40408034402e850341d059104580d101e0140030302100181030400000701e0489081c13007900300208660081d9000d100c41500c50390800e0945d0402500d141c0527400c0800411f000322032035002d602e100d900280031382d00b04480540100391039034041c81c2c0c100800c1e0f44a4520b03541c1c090b8100043d95110081c03002801208025549041b140030711b910800424240d06410441130150500c00480d0307001d8028001c0094141c986006904d03001c7c14845c03031001000039a0002058204206030a2203400d216940c00e040f811008081d130141020344000c9064480d05020210381280b00e44150b9002d1051421001d0f0390f1040c3c08100b102501e0300d504880140d904001900510b502d072916a8101061907a5004004640d0a00b4180007400740e000030482481941e0319003000e12295911125402a1010403c920b6230b803035808440115030340c6200895250300c00750000f444861450254140c521 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 797342158 1250 797340908 797340913
    0x8030604021b0601080613030c030e12010f060602101a09100e01030605010e0c040e070f0513091b0807050a050d0f110901170c12191b020d020a0b18 65
    0x348812030144600000b00003020560101006000c6500c0420210382c2c848540c2c900c00c100305526a800038042550b10400a0500c40740c4801200141c2d60090f0382000408504000c1066800356488400038160610076034026000c0d06d19801400102d501543c500c01210108005000480783c00313000495100800104c1c0c01c4584000102c0c0032800750071600e008602841e4040781c10350602e8100000820042c0003000141000c01040101d4230101c10111b078004006c2c00c01c4440d02200c1e00055031948202c519000c44140940404165501d4942c0440c50031015540e00c10340f0301c45040c009540c1840300351084408a40241300f80c0c0c0b42948610000c0401c20315644001c2145080000f00800b13641c20b600c000000d0354404560f804595a000c21070780844c0303d505500c9000f5040511046146104079040c4818054801001038003103507a00d4401e040f42c440003181004504405000d551800382d0710152140180621104820400d100003402201107401c460740020640300c0c1049003068080e112040f20607030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 797343408 1250 797342158 797342167
    0xc220f17010e150708010b070f02040504050114011205120c1e0c03160e0f0415110909161706060901121e020405101409013006091b0c0803060402 64
    0x2801c2c0f00314081ca07070b40d0701e4180c8090304202d540a0030f4418140c2000b011100203100e00c40100722070610401c45d441d01a24009120780b210300308140500700b01000604541e80c10400083c062408a100e0211503000b0001e45074004120016040e00344035204404020741d100084103200c555503081e0000e2500041c3d030840306204200310119051401c100500f00c411186075004120710110b0480656100c140c01c1004202407406644031403170203022083d0f6082543c1e40d068031240c221400d00440d00e4080f4014030383c04c8103140c404e044000304250b000142d030016200c4610b0701c842c3c0c90152030903800741800510042c20001d80360300445071004400c504c0311400342c03107030510903800155290315882204204400742c0d03203504082c2806080d584a021580401c01c4048184440080c0b003000d81d80420b00c2481c150f0700000711400c000800396014201030000b440b04034500e01e074100e0aa440401120309952007445030315140c1100350802d8518112400100d4001c420b0580042c84240046610480060005090 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 797344658 1250 797343408 797343431
    0x15060c07060306050f0d0201020d210203040803011706090d050708041707030c060c0b0402040906021207050d0501060c030e0d03140f07150b1f050702090c220f1701 72
    0x20009150710000109644800c1405242008500c0c8400114240c488400582041c2e00007907860b60b8a020b001c0c06c01514808500700d00d081644080aa081e0028040d503c0c1d081900b0441d483c0e82c002c1c46848022003140c080e40c8035541021415034401d0350000080c0c5100f500c2400e0a4809900c502070494040400700008198284d44c109018681040c2e20003c00d012401c41c0740008000501e41c114500303101c803000980e00020304003090150301a038182d902080e0754084e40340c1003019000f00c411a000c620000010401c3e19940100640300d034403000e00050142ea40e885605840001c1c207c0009800030b180310011081c0c5060031582280710301d22078903098000242188030a84140c00c22640c00c901c2140c001158818440c00700c104000c0601848030400c104203103c0005104484c20498038045450102102c1c2c110600903010b4510f10340e000707400d295243c584548400050750000021100030700da03d1882601074245118030341d064540d58000348140c0c1c0d003004174509001c1e01910750307140c9030340d211566401d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 797345908 1250 797344658 797344663
    0xb06220501230c1c0f02061810020c0705120312100b03070e1212070302070807060813050c0603070302030618010506031807031b0602070b070c0b070501091416061715060c 75
    0x5159a645c8150604014a030028141240030701821002c070b0b00d00e00f16030351b550320105a518825080c500c006a070f0300700038810241495025440140c1c0704044000d2041c4030040403004106015400c0303040c0314135654003000c11407280c0c075900810f126107600b400007034800350140440702d041000091588050141d80090313070b45043c410360851a05910003198180c1090340401400010302201d00291588074105000101040c0c0d0051403506060044c00c550428013405000a90140d0400b41405541b4600004041d010b940f083d100c0c14003030041d0386200002e480e000711180b0b05890004003001d00d152070701c500c450100760b039042001c0000d0181101c00000103e40550301c4a07160b10341c0d2440804546009401385c01c24419030701164140c07504100180005509294050549003c0909545c03201143d0900c1401400d4100000b0b00d900341d003800d0b0203260000000c1da0000d5180c4200483d1440e034940f134049990a03080032075801707203980780c401054441c4420030081e4461180902014180b030311138104e692 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 797347158 1250 797345908 797345953
    0x110a0303021f0b09070e011806020c011e02060a231828030c080c0d03060f150c112403010603060b2b0b06220501230c 52
    0x280503922000c82c1c0602c424000041294000301e40c0700402c83c842c006404038410344001410b40041002c10305d0540c10f01d0b801b403072194285d0010b45617000300e4940c880c0c90103581c1e003c202d200c442c081500c143c20201e000f00c8001400700d05001c3c1d40d01902c0e1a8480b020031401401040300710403840909603601041900344441110f2180d2150070440d040c814405109a09080b03a0407040050074510140744c004285001c030300c1c0c0e8513139035062070a510350f203241d81012101406022203603e03e40c054400c4208142d64160458820b40f003c042c4206081c039503030034101100c65042010755012505001880e0041a80f03110001d1039910082d1004240c0005a4054400c801e85041044400b1310044014000d881d858800c0c03202604d2100d040c14544604100341c40e04215405a0742000c41c006e940c07a01c180c84080703400c240420f542c09070045846280c1c003a441207407046108020803801e114600002010f602c200020340c550203003080e9400c106924054640f410390712402c400c100c1881020407111005441c491505c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 797348408 1250 797347158 797347163
    0x306162c0d1a09010902010503010b0708090a081e160603022203150c020c0f0609120610030303182303040e0c1801020105070f0318020907090608010f21110a03 70
    0xb940314240703440c98200d1500002e0416482da81c5400c80200040c3d0300a0308407810369003008038241e01d501c80340c90000341034483c08403205c0d04840d42c507800054040001440344440802d1b1520321910714110521a6940c603510340e0000c462184480040104500950080c90503814030515040d801440d0180c2e6800b00045031b000701c4500c40780c0004010550481d1041014285580c4080c0c9582d20500c8001203c07100c3c0500c281d8440c04000407050015507541e2400d49013284404280c800c1481c00d92071a90450b0340600c81a40401d003030501c51180c82c034209442c101082d03030042240058490861001050b40c0d42410064940c1c40104004034802d0304034640280b18011048200ea0f42da0300340210010389806032049503040d60305010601286d0b0b03800ca03824250840540c41e0029050341e040c03015981e40300000714041c2d0010000814030104d55801004038040d144251145213042c0d0781c0d03180041007212a486224441640c6561010000c1841c0214808a074000c912600192a007600011180ca07101e0f4005c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 797349658 1250 797348408 797348423
    0x1021209070608010e04060b0f04330b0403030c15020c010f0c030b18090703061107020f151812100605190305070312020a050d0801050306162c0d 64
    0xc0142a020030000072000d000e0524022040b94500b501081c0800360280c4020181174485860510340d8803000d04c1c039103521ba00184240207003240741c12030291007505040d40300012414809019948440581e040b8225200c0d081058600352858070100c4000344c00c400111040154001c11240650690010308100b41020b80001481c03070301c165105080305c040004c604d083c1800c00c250745859985100c10100103040c164060021643c03400310f0030b818000607170801403065207085103028607440349801805507d4400d40e0040710b2880c00400300031a05191a0300c0600c03144082003161600e40070024120003081004e0300300d100101501d80413504003210710001100903507440808001d18680701d00d00d14615a04855040c02142c11034481e1520780c1c0660201030b00982454821041540c0700300950040150005c0079988240d902c1e040c010a202c90078803441d4403a22940002c02c0200012192079002c0c07454a80360114501c0342c200050421511750f000d100d044407070352130070f591b055241d075140d1000d5144203001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 797350908 1250 797349658 797349661
    0xa05030d060e010b1c060b0f09180105060d09020a030c17060115020a0b090c060304150e0303130209100b040f081c171909030909050603010917070212010212 69
    0x2110044458692002203004003450041000d000840b0403540318405901c80080d18117040c8402c407024150941c0701440035540020b216250400c600003600030002c08035200580b82410358404070312000213020740c541c00340007004041c15406203035211101d024405032910083d180e59803030780914001d0b0b035408040404000c8030a404055001d1001c940981003500c9920005105204001d41d03548082c0401044420030a0114a85210820145031001c50084c801039482c6024035119406072020b0001c080d440e41000b40204d00080b010069911400c846c2c1c43c00030320407005800b04500714a02034120303000120b4041011802041c00c0000340003070030711100aa070340649070a1a2501d8003e00300000c00f0001828244c520b110340d48809141107211508050075100d071942203200080075280000e00f1020382c9019492000c25401c10026000c85000e0041041203a542c17205060907584000c0300140500340380380e00e460304045101c3c080e181060014084515102950a070a8226132000e00c080414600d00030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 797352158 1250 797350908 797350927
    0x510050403030b09160207060f030f020304030c02010206070305042f0312031006092d120b06151603050a020316060b0a120b0106140906160b0a0b011e02010e0a0503 72
    0x905a0400300b10840106612510340700203445440600424040001010451032030038400c0c0c00c1004119081101103558ec1054030b0003500c1483d0a04049015000340702c006200c240c0244581841540c003c80d1240798558603034002c9208540c001c3c075140c04452280003440458030b0030840b07000c020185200080d640e040c40307107110140e814240d020700100030300d48000307010103003481d00c646698900e070000841c45d40d400b0017500d40640b0511303000a949500d20481000038455100f003000e000d8101a0344c17007d0f403200400c140c0403541c4580303a084449210185207000000788200000e0241a206106690401842180d0700c03420142078002520501c0d1968510b46a40c540728078608010300d501c1401600f24400c652320074803614414030a000c07c0c40000700d02e13402061070601c12908500f0004002680c3c0382121070440000300301846058075412407080c00140348500620403031030031100c16100c5004003400242044902c840f401803138002c6549641d400ca0100030100658002240721340083c54942c803200707 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 797353408 1250 797352158 797352169
    0x5010e1305100807080c180406090210021c110a0f02010210060305030c060f0601080a0911120102120a0b03071802040308040b0a0806010801061407020a03080a03060306061706130510050403030b 85
    0x10b403c5100a90400400c05445a8580ca40110050a19040c7e115541e07518100b0400400d03010300065003104d4088080004664081040210821003004081c09407148a4040760780e80294011501145d001d60004004208200c0c0d05451040c4144102d40d844a1861b003024160785c190791003264903074008641c8106442c410b01c80d4aa00124a1140030386600cbc20100003003503940d028140d03404040c2c0c0c8188140c1800081c1c03841c04899807016003004165002c42c5100340c001c0d4800109410704002c40004100100040e014503c8015030040040014604001c500e40c2c07400340300d844000000b81e00308000030001d040d40c00500000d00048100944901d60701c003010b030131450028031260407c00355000501c4110b401110520603451207003195030302d8210303e10201e0003c8844d600080d150b80c8011918090701641900030307070141d1784200414011142d558440d090b0212000c0c1071001160000d6000036042250703c0c0d00703440c005024130100c0b803119000130707200740c2154070540301900000c0e201c00201c1841c3c1010f = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 797354658 1250 797353408 797353423
    0xc060e0f0f07140603060904030306050303130510141c0f0f0207020907030204150507020105070f060e0c01030203090c01051608030f0402120a0c090b06040509010f0f150905010e13051008 82
    0x3c403410119600015000900c003448020000d900c60641c1c04049002d2622030303071040024102c080c7c2100e5694034a403121304590502031142c648206c0c80031070031404441c4160900007860a030f40b000c43d400c100c0d0300407208050b41008044130251503030b80d64a8001860050103660074228821100595070000340c01071103002d2400030a0300f01450b004000401c050702c19010004040380c001e1410544a450520040b50300380701c0c051000d4403010702d0b520340c98107106696001138801d00751641100e17805044030005605070300045405800039000450f840c1030b25401100141403c20b5220305440c642d02c00b59482c00340d1034106446910349011014104421800c1c00780c3c031801c561004000600042c0c01d03540c0c0340305283c9003d010b5146c5c1070b070b02c07031a80c044143c4a410941d00038140061084005685560781c0e100700101c0d91250007415a00c3e0140041d250400c0c01540c100c24901e80d56a15030107092100540d911008100c1141e08002d0754510a1904003551040a0203503000310300e0503c003a85800c51441c9000300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 797355908 1250 797354658 797354669
    0x42090607050f04120f06051006020f010e19110909060a112b0b0a081c0c0b18070b03090307020a0501050405030a02010305041a160f031505010c060e0f0f07 68
    0x701003195994071415503050781d044820301d81010021100d00c2c5040300200c0010003004040314200004d00900c100c1d9504a0300590f001603003107603402d030310b4140d4550a072585d090700c49a650b000450301443ca013001b500308603a000d000d81e00098250b1290800306105040440715884241c2219040c0481c100d014041d05100d24021000d42d070500d060341d07414040c603008000c002002800079400c11510f003070641e00140361643d0002d259204071503407115032607100d10703400c08501000d000008a45071868055040d410300282c00c000d00c1421599402040b070f8000c0161407845166110369070300043c1e40011103000b075115402035030140d51900f44510600c103055140340c000b03e061000030306c0107001d5074900141e004201602485c0104141d200c6082c21410981002140400299120100003003030258440840345c01210b42e403a00e03842d4404c54001c40489501c809007003c0100e460204105547c411100b05032080e0143e400003412006405801e0301c0c0c202032284030081500221000f6005140034001c0000901d03 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 797357158 1250 797355908 797355917
    0x120c0f0617160309140a0614011a03090102070204020d1a12120f090312091305010b040b07082701030f180201140f120402101142090607 60
    0x1400c05904600076440180385906548102c810001014400d070804194544c121710140300c6028070b810140d4548507032500036240c69080c4400130780001c004440480c100c03084515502c00c0d0f6840f40280e650f13a80d0001d071168001d507400740180000f40e52940f00400110302c2e140c4000440c0e01e9a1400a00c60381c220360543c034440c8452030004540b820300460303620100664450020303a1403202009880c264026003e42c1c6400d44181c8508003480c07c0000300030209540111084071402d451413584009584090090038070b400428041013000a41000142103c244a8000c1030706010080000c4030705002140c590f81d0003803645800d801150750f01482a0504c12003400001e101c0038101a00c0400c2c0200c54450007810403003151103109150b0800d006803000c00c1c0f0501101517481007900c40c0c035281d1b80c109481c140d00c65070810b02c0c240340480c0644030203104600e8240c042c0031040000e281c0e83d10005031000003d98020108000031481c40b2919201c58501d000060380301c802d505040030120b240c248003c10540c10b02 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 797358408 1250 797357158 797357177
    0xe010206070c020103180c1d060d050a120509040212010311190312090b0c07060228030c240504060e0a0b0109020309070b0304060f0b090c07060213120c0f06 69
    0x154000c440362080c507020b00b80842c40c030701512403000e40c664002c84050003051700054042200d2034180203002c25180341c003e03c8c4840380c035408100489540c000da4000e00e6940404e2841001a0601a09070341c11030440c20300c107023044140c4000c14242d9003c40701184421f54000018010460340512070992100e003640d9407442800d0800b0703c1c1031150300c107000c080c0c203a400e07145101c02014890f05042c0040c07c13041d0344507904e681c2078131066903031180540208400b5000d4042215442d0f50000310286882c0f8030600c03000c3c109450b40c0c5094a00800c0d000b03050391804550542c09102d60304140300780081010384240000c547c5410b040800444031080328550352508408841d40208805081c014103541c00036800581d05d0710388040052401145900c0881d000c00088204820b00c48581d01400044400607801d0042d100c0c00c004204002c2000c4840c00241d40c001c0c40303d42e012415941c007800b0361500303c401d011800d0341c40e800d85440d00d0f2803601c03080300c161007409010700c682c40d100040200100780600382000780 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 797359658 1250 797358408 797358421
    0x9110a0f1404020c010209330a090603022a0321100509130f080a020f010c2a1502090a09090201080a020a020c15041a030c1204150e0606010e010206 65
    0x2949080c0010b200e1030b00070880b00c01e1250203604550401a00800180c2c54800c0300c06800c4031240030044203050411403404008594030b00c03008458103c0368a50341c01c0d0382a803c00760158001d4000f8480c00e404141940c58010700b0046403110032401c143e082000355100c0005000070180c2030100844070f14040d603241d06100400c0f9901402c2000d0b40c1c005ca0b04404156125001c0381d000d19800d81018012000d8185064288a0500c006042d404099070907904030b10000c1c20128242c840400c140c0000541015030250b4988050000401c07682c0240e002c14a1040503840d0360404241a0004204890703001130710407120301e4100003640013004440c90038015940c9580000e8504200140389101d1f55400150390340180d4402e0203201000003008010764440d60484688140f29041800f903004000c0081ca8074400162a6400741e0380300f110700505c0c042c54200101c44004c604000644100c800e4481c076440003001482d1402036089442a01008000ad03207080800104000da0500229040d500000c3c140300e00d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 797360908 1250 797359658 797359679
    0x30c15021609091b0b04060e09040c050906040f050a0b0a0e010e0123040c02010b030c1219140d0201090b0a0b09041b091104030b0108070803041e0909110a0f 69
    0x11203540b914001007120f00d6003402c0206a250100324510500e003e1800b003640042c40010340142c40c4156105000303420103006000801c282a42e01070900202c480d01009145082408143c1c460300240003c070761400700b07880050580d5020764900c1c015607103992600355207092a8800e0b400500c6580d29501c2154503100c6550f0320050103020701d0000800f5405000c40444051000300046100644200400741400300000d00a06410380c86510901524107d4141c6d4602030680e180c502801c14081c00000d82c11840e12038152585540482e0342000c1d01c0650342210b0010701021074180250740020502840620703000500500c000c0c1214109880c0c0030a0003c2911241d81541d4800d07481070103900c0000343e441410600000c0c542c0800d03001d50602c139001c3c00741310f803080c060400c607445511651500d0340c0341d0a07076588502060045c005654004d0004001e050002422501c95072660710380d0810858507032007000d090f1000280709480340f00507030131101300c903040201d42000200280c450b482c4a007810545401d1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 797362158 1250 797360908 797360953
    0x20a050f0f07150902130b01091e0302120a060c08070c060911101101051b090105030703380405091b010e060712090608060d060c050c0601030c1502 65
    0x558000c40414a210340040d01c1040301c1840740c2200e81e06462015100088002e0035001804a01603101c24005007804445805011b160b854161104408242821001c0a0b4403c604040c2c080fa002582c4c000070250301c2c0c0090021042001102802000c00b980c03c01c00250380b10400d1403070400406100708601c055015a55000703041d0b1080002c1110b5559082400005c00302c0d090302c66011403444802010b036500018580400d070500b034000e1049a0f104000030204298005480c6e038501010402c0030f2030340d84204005c542c040d4032400d00107001c3d0446154501e00010000210400c488400d1031460003080c0100b400b0b890030000c9030b041c0624941056045c4c0c841e000c5c0000440d10803024000d017103890380140b40074440603801809180d101c0d101d80c241400c41080075074100d030108003100000705085d48181260781c030600004d851040203811b0341e40c0e1240103207424200e040c104038003400003010301e640901055008500541c0d9401c58a4101400980350301d0100704004199072102d000116403004844203030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 797363408 1250 797362158 797362177
    0x3031602071406090310050106080106021b0618130905160e100510030b0301110a1106070912060b030a0f020a0f03150b0a0305122109030d050411100e090a020a05 71
    0x85445850b91804a4501b00e00c0c0620215043e04107800810380b01e0780710544074100c410304d5003180c005503013500348018165055483c00341c00078400c010342c0300c403075020071008400c400c0d0141c00046120725003100c040459041207070031900b5400c02c12034652014100c00240020381030080010080d41010411140d2448062240300c0c014408400d40b0340503140294000c1c02c503804060024401c5003542214428280d014000e0f001c00700d00c2151310020041000241a485880c3c0b07038039900e185504042c01c651103040620300480d003168031144083c0543d20107101c14006540b00e1000d0b944010100c2c4100030840c044c42c1c01c26004c181d07103031004101095555054140b0700c03410030300000c0c01c007001c02d0229440701e00a0b00080d15522820800041102e120384c000c00e42d205450a801c140032080c0c280b88502201d05440c14032956006200303040d9040c06a51003590420b10540e9810080010140824428078004004402094205100f411282848000a076004255200851500c03c480001400e0ba020347c1c0300d00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 797364658 1250 797363408 797363419
    0x7050f04141902210912030702101104090606030f06080c010f1d120d02010f05060607021012110408190c15050c060408091003110901030908120405030316020714 71
    0xa860381c03842c440c0c1c100c43c41c040c50003203049145010103054040203d015150281c2c10310a8600c410f030910080e000766805045a54060f03d900301c8083c5014004e4070040500e507804e034004200001b21b4081a100f5017004054a0f100810b80f190320013212400ca0300503a01083c0c039a003100c810120323903a074009030402c00c4900c2c03810007901c2034201444d8410540c0c0c00d4128150000951101c3c044c1d5960300040b4100004519802404251402305e82c55050b01d40544696410107002c7c4122801441c04491070f0401960a203032602c0e020092580c5d820586044034850100000005800c0c40025002e02c8000550116441030041507015a606c2c00c52500c00381c456120f1055541d25005582031003803085600e90f000b801c0403a2031504203410000d071a0790041c22f000c0d21806045400f40c06040c0a406110341034001c032451181080c501f000150050000d0f1441190564820449181c1c41540c40d540140135902600041d40c80346010351707102c1034007004100500159802103004220303111201e150301c24040020780c2c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 797365908 1250 797364658 797364691
    0x31a0307050a06141333021c182306120103110111010203070f0906080f07120617250e0403050702040f0216020f060f0f03040c03080c07050f0414 64
    0x4413880c00c1c0503107110010303542e59070800081c01b4030040d600d01e80708031441303035000c00c020061341c1c44a411950240041400740c1c114042c280840c803e203240704550744015051851400c61080d0f00c03512003100303641003211100708110060408143d1241100d05002080d10300741c0c50905031515030916175405100c0206488000460b0170100d034825400c41d81c09402c0500295200e081540e0060000000c00307841c0340c00101c842c1c2c00042c580344100b000d80d0003240c0c2d00040c2e81054441d06030403030720001a5080c000c5803a032501000524000e0849030742ca01c10321560041c1c0b8a000310000b41440c81580010381051a990091060144040098041d608107506042c4145da500951001c9409040201070100d0354620210394000404801c41c00c2010f50b5208489075a2601d2401c01080490b001e03145d0480b007051000d10240d4481c982007030045820034090307403c0e10700003552030b55014015030190f007103182190401d02007000581810350341202040c0c03044a01344035a5008541503a44d143d0000c01340c2604104190 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 797367158 1250 797365908 797365937
    0x10606120e0102130303050c0c04020405180a0e1501030b060409150c021608030c070b16030c0c17150108070302011403151e0f100804080a030e030406031a0307050a06 73
    0x50441e01341e040e540004442c403d40e01d08010304560000c40d81c40c0e24a0280c0020900a0301c0d203403003120181e55004044c010b240c80080464590504010300001925690f801c400381001002c0150302c60001c0706aa00c0329180d819403030409d10521000c2d1040c3e014500b0401c00c400054801d00400700104101c0c807001032903000211f0100c1c030300030116890313411144500a000c191128040024085c100c81041100c00c075075500e56082c0c4c41441000d107900d000c15000c942910001e880b07403500b02c1c40325014035031100d0056140c880c200c0c0c050210301198000c95012103000c0c004c001d5101c4030180100302c00c101a203601403440e000a8070785548009004e200c0000000040e40301c1c4810605407018130300281402c904a4001010342500c1caa0b40311080384070f82084103096078145403028880c81070645e2070341c40709041d484540d258240c503040040982d050580b00d45000c4003100042019000810190790007040b41d000c5c0140740b4003194a801c1c0501d000380c024580030f0105443d0403111100321085481e140c84401d1514 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 797368408 1250 797367158 797367161
    0xe0f01121b090603050c100912062003040b15030a230a0b0108160305120903100e06340503060102031c0212010f030c05040c0509120604050609010606120e01 69
    0xd000d0704542016207201246140c155400041542d2082003110380c0724040700c042007601100c103049000007a00418040c00800f0441014946140c4141d1010038051041c0c8128140d0750105c90041402e8580402000140a801302105410501c124102c0392500c1400e001b20fa11098501d0000d004800c0303401180c0c02003c0d00d55a61003c18a950087d640b2042c0c143ca0100e2902e0020710803a015440b030606455900801c61054100700e9900800401182c0403c001d401002c2d00000d124035803502800c0b141204607181c43c02070082c0581c681001c0e090740d2405142c6081401e4081a40101c0b0400d41c1c0c900719001440107445400812003802e00a80701d40e50000100c0c9184034040310228560b130b40c2c211080450ba920340140046800070119545240c0e04c8680c29513000c0b425100107010384d4800b040c00c01213407c2c954041084040340f85486458990a00f010030f20f922080c1c698103415a00560400003481000d0101c0d0380c0100102c002400018542140249441e00b00c0c0c1070030340c159950741d12401c0c03145400d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 797369658 1250 797368408 797368433
    0xf070903140a05010e0309281e091d0307020d140307061505040e061303090906060c032c220e030a02010c02070f0306090c0503030d0b0a0e0f0112 64
    0x14292544085000c00c01d03510345405180803141582040807044058030044143d80130110007030a00c03440d0301400c0a1607120100c200696070140030b19103102141ca4121400c512019070b110104000d41350f8a8481010111803c80050b058400c2099071a84c032400c002204660311150100c1c1c100d100345030541032003824101d00c200030f40010310001840c84100074042e0080604c040c804201c0a619a83e6202030005540081e10083c0c425004800001c2c0c1c20b510001090803a00d00928065494035111851041102d01c030350803800224000d519140c0c101503101d041c0130100307002c101c01a2641104000c41813040d0030040c0000b4070a060760300d00d200c115950190360821401003000c080c401011546621501ca900040d030140055003005210941c4a0000490400326a8040303821107086145803141e0004150750002221010000f0304005029038040000d000300b010602030009031103044400700840680558810311400d00b45004100403e074403500c006044031344103c0c81c101020342d00e24280100500 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 797370908 1250 797369658 797369663
    0x90c07060b210d0305090a0807150207080a0c0219030803060609180114120f030901080a0b0a0305060621030a08090304150806040e01020903070510020f07120210050408060f070903 79
    0x41c00300080c034000d000003ea00c034682e400340d20100302580360420842e13101c41c1c84000c041d1480c4000c1040d01c0010f60f08031515403a49000f4140142020341c1a61205003035802944048005429030b007001065180580014009426900320075801510b90b540b081201e0000810072845514041070701402d0340c41e03a21881170300320090381d480c0701c0a60b15416490094090000c4443c040e01c80310030190030300c1c807002629031801007a6400950400300c960780111060300c801003400031266114a0078130307802c0c0c0740c40ca5040c3c080c502c2140a4800c0f40340101c01c0c05543c1c1d071000d42c5040c900245004c414403150000c012030b0224101403600c541c0c19615198014a035106070340c0100100c1c00416000c40750158000c0109019007000c0301c0c2407020f4811440e00c0c500742d009071050194150054201004549440d03000040d4900c2d0600540b02d80b200c62444450420314aa0700a000501034060750a04624110900c49000c03101d5042ca1810103003480446d0ba503546004201d452509490008141510701426040000350b9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 797372158 1250 797370908 797370949
    0x240307170304030b0106052115120f19080301031e0203190b13020f0d03020f12130806040c1719061a1014132c0105090c07060b 56
    0x104440100e640c80c1d000e0710094079a01d100c000089002c500c20012541c204904594004400d40004030f05076010342c000e0f05162225081c0003400b86c00d80c5441c42c21144030940e000140203040ca0107101d09042903039000c10561581203031303c8000001f5050600b42c0341520303081007400c00500a4403940201d062007420002c0d5041c8558200d52031198202e03202554007603c1034820000c5a190945904210f08254600a41c80780544152031000c1c1800b071108100c1078041c0c4100c5540c80715810400b41420000c00c02d51461040c005030f920804500d44102c00020042c031001004186810b480f6086009a0350060b00075481c958460220701c03007000c2111111201c0309a400ca01c0d40c1c0741030701d8000000c0000b1220a04826440c02071740c0101d1600c45c0c3d05d0a181780703681d00c9881c40444180312030400ca43c0403640e4a10000645007011801d00034250644082140c404c11a440c2912404115291681d0503845684218040c00c2007000c2038040c40c0039505565445100452001e6003a000600c2850050342c84803400f9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 797373408 1250 797372158 797372189
    0x8100308161a060d15110a091a03040b1614040e07110111090f190e07110607020c0f1f0513090203090d0f020a080c0106060306050603240307 62
    0xc20a08454810482c80b94900e02060340800c01c403002c035182e04481982e07002405058600215541c0d005942030b000a01c000042c3d450b1302c41e140c4075100d40003040898001012a2028072601e45401a441c2c0e031981c283d00c031107003140340544d1141d454803030081000c0001602003401c0d244242c0030341e038422840a04a03016981721502c401d298854000115070180c0003400d040c101c401c1041042c412701e40c410101009052401e0100d10600100d540302c4900c540c0c0115082071080e40c280c0441480304042e1151404c6071202d800e0010000741040a80d0b90a2a200d03080b0205200f04c1940002c1c3c0c4840c00d580c19503440605250140002e14407482444619412a4602c0c1c2d200070380b1340e402802807802c0502c0d50910f46110f42c452000344200c1c00100da0700e10049e4040e0800d84030300c0f8052403400403500d520f44115500300890365550f5071942c00c4810000351503910341d201400000c1c0c0500881025103000d48555003140747c40006014244840038a030300b49544000310303440c15600e00780f006102410030280000d812 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 797374658 1250 797373408 797373427
    0xf0a05030a050c0c0a080f090a090203071707081306020d020c28050a08090a080a030327210e191a070c090b010c1505090105150109030308100308 64
    0x203900485a108640b841c120000e28502896026140300d80c850000400030f0740110703954451241c0c1b212280c8451700b00b0511445110f0faa404115102410641c000580c484c14800c2010b000c01e034040c0900200d51000001f001501d55201c13052a9116680c07443c2e03202503200d6030400c01d0092241181450529000103124030940c800081d1900400805080d40b01030240540e610300601c2c0c0211030010131640000c03010310041038088001d0150381d03d0081c00c103428156218003c0385404d4035440c0c00c40c0440d0712050110f0341449150300c1c100410f0080d4101c004c803181c2656803c49180d0301d1a14500c543ca0740c2c00314802c0d45074820480f8100412024000340c6501c1c00d0340014001208042c85414070620154240c81020400305e0b0545a21a51010f1911503031401c2071f6900b00a00212200c0798100179107001d901c000300f5840300c20400078281d401000140360608022a0f401d4550080c202501603111241840b00360340e1000c2c3c0e90003100c1c0c05181c8440c003525003000703000030112035074005007500c0780101d0300c800c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 797375908 1250 797374658 797374667
    0x9110306330a0e19140105030603070f1806050a0608010608090703051e250302120a0f060204050f010f0f030207061508010c0f0e010f0e01020109020a0306021c0b1f050f0a 75
    0xc00590848024402c0c081c0c20304d031041d0741c0901c3e02821600203920714040710303a540104041d6821840c020183d583d81c81d1608aa85030f440040e5119290195810044091403000d030f101c0c0e000070f002d096030310300c0041e4200700c17002d007058030103228050401100000050100f04c0510507080078550040030f036144001c0d1540c034813902e9084400c002c01640500e525500b400b111000481c001000c100900c1180303940340d6001c03c6145951078604048600800a01d41d001803420001d40200c940310f40030051f211070500050050408002102d241804652004a0344640e0000c40c1c45c80c92040038070380569104154500a8041d000d94105009c10035000c46010950315010341000300d40e403006a80c1c00001016140b0300311b440c4040c40c407005000c9890080300b1600c1d03c3c40781c51844554001800042080304107a40030a91241d226031007aa5059400706904460510000c0e00e040c552101d80820b015001030800002c41c2c4901da242580e00c0c880d9821811003070720b4000d40070780b03414070560185541c8941e4220000791 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 797377158 1250 797375908 797375927
    0x31e0f01062d0e010207030c061d030604021318081c0b01170f1005030610030519021503060d141b0d1211010e030f0409110306330a 58
    0x1008212007800c020882c0002040007a07281c0c1010102da01440210507095551070154031299046004144000c40801d12408044000f05001d0340c13201650a50514a84000300807003250758800d411100a100160360364021215120761a04000902501e1108600e0085803460f1401042d554000c508014000070081300480003041c246070601c600700303502c001122045480481000e840303007100c0c007042040302120020b5038806c55400304690060f480f8030009282030022503c0314080c0400040a00402000703208031a800707601c148813400c00800c145c0c00200c04068010031400f01d4207000c00007c4065440c48515a04072703400c841d401c1d038055108001c1070340f0780d011641d401c0004008540c4003560b0303003459503520030b000c0d03001042442c2000c5403c000311600e098014034000740c1c0d9251035810107501810f10003014841200b0381031640d11458401032310103403004c6c000c8a0b03070445028000c00c005516804110514020800c6400b84040030f6180e4400f01c040d10a036064051403408a00840602d411001c40c1 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 797378408 1250 797377158 797377169
    0x1050402040509011103070c021c080304050f070f0b2206080f2206020306031507020a061116021507081603083306040e0406021309020c030301030305031e0f01 70
    0x92040c0c3d650649261300740d8413941e150032004282000003801d0076210344022171081e8402031100b80e00f4078140b05000340d00c15202c9070030340f40c030a00041440b04100081002e0000510ba6201402c0f85034944000e0784200245403080400200000410341e004100503c0c117031401d0317a8110311064081c2e8235140c00030940202120082020303000754000c1920107007210307030344105003541000f150020345241d0b641001942014000d107801d031280540c040c1200481c216454810080c980c02811420840c2c14540180c3c0c040080201c0c2c501c104008400190b02c4c1c440d4200e001640607501c00307281640c04040c407200c82c410910083c11020000c601207596010000b0ac84154501030303950001d658549031920b00651104032403c030344036a580d100314090348150000b40d10782010000e040d90304255070b4140d0400a030004a80c01c5984550004003141d5592086101c8400381860f10000c6042110707031050b0a40d02c3c441800041d090040101c00144014010105c81c160302c014010b401805007010b02085e01b10441c2070041c6c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 797379658 1250 797378408 797378411
    0x403350109020301061b0210200f010e010c0c0809010309030203190e1003021606050603010b030307060b011e1218021309150b03031207171e0f09060610021c020105040204 75
    0x1b20340d04501c13800c6980325403517001440c44020002c0090f080d6188491100d011019240040c41c003080010180009140403000c0300000c07510b240c49540d07003800c4400005420051148943d140c03000f054202068409106c400e0130009011b04071820103910b58003d02c100e2041c41e000d03504040c03415562205000e8840003081c1c070808039a004821040d01680030301d254015015400c0035103400481d00a0704003a4000303501a000051211400b0040b07811948083c600341d550940b10155213100d5603003d6030341540718400c080296180d60764a800241f4550b51b50000340102a00c86000c42d48905c805110300c04000d178010300418072003080c007821030007404000800769441916040c8010000c0f8184c0144200408006d014500d0701d448803001b070b850387d003014101c0c0003044ce03c1d00c10030f8400c07842c0c0071589000301c2004808843c48070f0340c000d001a600800504c0100161011414840c04840000c0c2c0d07183c0003402160403010250310240e0480c41c005404d40c154801041482891100c5038040d0f02582c0101d00a0b9030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 797380908 1250 797379658 797379677
    0x90203191401053103350c0c12030402030c090106030504050601081609150e040b04060e010218041a0402040612110702150a050d02040e0105040c0305040335010902030106 75
    0x207620072020b040203540440c0362104c000c85260405081c03600c56040d0300c20b0509200740310011b00340201c1c40c035011005402200f08007506280c80c3d2603407052264000c0c1d038660070518000800304010b407142c800703200d194030255021002c82c08642e0284104502601d01820800ca07540e96443d006010304015a0706032818020b2900100d90b079040402c6801d07041001141400110345481d8a440040c1101145501e0111400c0c2002c22006484c3c0581c1c1c2c0210300542d9004881d08080c20210101e03002c0c01c1c0080207a80c07040015841500544007054461001268002400c8205500c0280348054046405902034800240407030315503003241c0e401321204101c1c0c00410054820300d0341400c480c4075400340031f1760010a100314404810150f900600c0094440d10340300382454120031603202079030050340040c500c1c21000300061043e810b1921815103e00c00705c0c5400c0c48107081545014207012181100c0408108017607085901000340d40101140c80784490300303141120344e034802000d80250070030b002d00c4000420704203 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 797382158 1250 797380908 797380921
    0x120f0203041a070903052a0a06030209030f07050109030602030a0905010e0601080c120a08160c0306020403120c23031b011a0a0e010b03060a030f050703111005090409020319140105 79
    0x200c500085c2c0c0d500400402c420b021100b076092134044074001c916191542180d680d215512203010540062103140c8001d40c548096030201410000301c1d40710506990b00001d0b0800c070b90faa0001401e01103179081070f00103070340740c907a20544c002801001c0c4001d4160741c01e0024032440c90350300251007412030300c0100540c0c8400805c0c004024440c50100c501c060310744d119440341404103421000070b100107501d0042401c80b003c000d54400c84a04d403075a10a4424560214007042400003040b50350a5040310740c0350414980da11a03403003c903030002001114101030380c44112421104410401c41c1d400100c29610311152480c82c800341c2d4003a01092403501483e100310748142d1501d0518410000c161765018088402d10703030901348044a40e1300020001c1c2c1d44840321245c0040811241c2c4013001c10030340644083c2000034118100701c9804000c0031602c50180c80401040401c40d030b0b1090681c0c20283c0d04641c08650f4102ca030000900d4102d02040300c07580024400403070300420402110f400c0810651600900c00c90b40c509 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 797383408 1250 797382158 797382167
    0x2160b1509090114150406030b100305070b0304080d0f2013050906030a0b06010509220e0f10020f13080f0d0804170c010f050705090f0906060703120f0203041a07 71
    0x101c41350209014074501041120081d00082c44210380b0280000031030681d2501c80410002095601c101080c82a5405006004092151101506051000a145003072a940d081315170b2003121008002a565142d101c1084c03180d9400c2031100303a8448840141c40e0811644c81c034120b41c0301da01800c90711907100c2c030001110301b0890791562103410024040d042448481d250301105080c01081d00703040150400c1501c00726628130f400803540c0200e03580154003842d100000c2004903410507074001c840b0344c003902d641c0d105a5400544144154100b5102584540f00c0c4d916510080c0600090138040b11240b1b2000f00340752400090460b41c000c15070003150703400102d444c8155100070051307074094443d41012540440c400e0304100200030749280d0a0001540e100082c66000881c5c40984a410004000259000071880c0c6928040c44110301154014000d090031000101070340320b50240102840010900000500c0d80d43d807154074489600a010b65803440c0030f14102c8961140c1d40d0b030214581e001c0074041001c2c648178 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 797384658 1250 797383408 797383421
    0x1c0e0906040b0d1506150504031a040c09150308040305012403020603070e120109140f030c1b13050106021e030309060f090a06180c06170a02160b15090901 68
    0x94080201e01020707481d0480d1140911110644d00780d15480300040c08004062849038103040341d540c2d0f41d15181140b51a803511610a100060218a08010702000c9030131518402c0c02c03256070030000640c402200c8102d442c40c8083c2c0e480600303600000321703000003404810b410000c0d410070907514124060341c04035400d03001400c2900000e50800020300018040c0d81c000d11040386007800003403201c3c440b5403070024510b094480640c0c0c101c0d090342c649140840c2c0070408010340030030104404003460174000308402c440d0759a0383d0b0a0b007098403049814030f2124283c5912903501950392540005000568407004044d58404070b90100d2115981c8814005e511801c0100c25640500160700140560361070742c3d880c52801d004041c00803021400340b052800300140003445030b0442e84480315581d00401c1020304105103e40c0840d80047e0511070b4104c07c47da102c21080c08001e507c0049100016101c100310f1448042d0b00101550040c542808002801500e180b07a44c01241d944604481040d603640c1c82944860a8440 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 797385908 1250 797384658 797384681
    0xc0d0b0901080703020f0105090d060e010c0c02030a0b07170703050906100e16050c010c0914060c070e0712050a0b1306140f03100204032307050a090c021c0e090604 72
    0x8059400c0c8011b141080c400842880b0526040c0c0c10451040001826154400302c21140540d4511003d69020001e00034200e5184950610142c5000d003600400c5d00d0ba604800010143c591141c00908101d005096810003d041c0302c80f505600e03c0c0150024004110035110706070301d480b90f1000107070f819031041c0c190003d88998000301740307881d12a601405002d04040f010303502440024040145650001d100e1080c0024850b59600c0c00e551500035200016100f40700c08074081d040030400300d070014600240803001c403400c540040845507503000c012070301700341c020600642103402d14003031006141c06500302209043c002c075031640d0040c0b12048400200c661a115600e041c0301190309008942c5046c0c0e0518003000e50107801e80c2c8601c0484620700f0100ea115030000c0399541c05250038406609265100e5100e409120741c0100780700d500380300014441c0311080c81a00f0a0680b69089181aa4401c2c0072611441910180c01c81c5903000400c4060900780c0b40410150083c0c03006c0001030043c4ca031034090300740d0426 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 797387158 1250 797385908 797385913
    0x60303031b0318011104050a050a12021005090a060c1211190c03050d02030a080c0403021c0203010f1b1214040303181e110d0b2a030c0d0b090108 64
    0x41a4000d8001904018904503c0e1081209203c2a10000713025502445032159516561a4180740c2080390480841d00700900840e0b41000c2484042c21540010220036011281c295000c007074045c00701c900e440fa13031a078181c0140c111000096072030b42005604020b103100d05100c41023112400c1e4100c8014842151500e034030380c441000022210014100804024080d07220400e0848d00c03501e40b02d1030900503825510060340b00003071100c07803a5030010060740c1040c00c2d20300342e92a09195030000348a2881c24001c1c0800b03414a81120030440d6800d61001d07140300c052020a1103200c400781541110342841070580d2000c10070108511312865410310984812400c250030010458070380e0388085004200c12032084a1070258110000080740c072446007140d01004181c0350341d1300014545440100b90a8400225000b640f20b2b941440000c1c03440c1c13040eaa400440014408203a115410752a043d04000760501c44440c0800002d00668000500040130024841034041c4071550b161002d020200e182485490010f8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 797388408 1250 797387158 797387191
    0x30c020c090403081905010b040602071512022a01050a1b1b020409080f130b270a180b1c15090c1703091f0e040e01020c01020309060f06030303 63
    0x10703000e00b4281d6000300091a04100c4003c0b00a0030200302c075000e230080158035002081c200b14242d0704101c090044e2100c403440303640f403c0280d00050024442c0040b11030040d070300072403a01004040780c1d00c84e05803802ea0040d60200d110940c02268001c241c03c0e100c65030003600740b015942ca51081103170484403c00f00c4d6a208a038480b182c943c1c1a01d404103a820490b40242c0f900402ea02148421029200c1034104442141e0390b2000c03c80d2800c100803080c0e226160320a410b00c41803101e00000343c074002c4c40e80d00c92480701003004280c0000814051050700b14441c0424100b16104450f0241d41c801c02c0640c0d42a104440d00c81d1007600e41c0c104903111044000c22440020f40d0914070452143c02c001c4034a44501c101c1c506641e00ea40982001140c3c0c2030340c5441c107520106003545149840004480e14510820110007460240c0070000c20203a14040424019601c2c3d609106020340c00754100c80c002d0000000854803400c21891554441e601620154121460711012032034625010044034003e140301c91200300710 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 797389658 1250 797388408 797388413
    0x140d0b210d1d011214040b010f0806070e0904060e06010602070501090503070f06050d090b04031205150105090d0f062c010216020906010c020a0e07030e010504050c1516060c030c020c0904 82
    0x2594004000300e4011601d0302d40c5c00c0c0c40403500668582c090f51040141d40e90341c0d03040c07401c5118611000c1d880007211707034407100130b200340345810000d940002c0c80140c85028030f0355298148080900180103200030b50b441040000075034250b02052100c1980c40990314010982e503940300f055a1451140291034410400700410403425008034014680865a100003091343c0e403a6860310100c0400840b01900803c68841525a0102943c401c3c0ca500c000019503105d0105103200008109019040e4014015040c41080c4018450000c541e510000d612170002e208040385a440c003c84009200a02038003400c048114045101043c001e0340c050604404440030304816540812602850140140e414040d0b0080040d0150b11001c0c4060060510a492040b0074180b190780141220b09041070b07400301e43d00d02001e2000084e008180c10042c404200c82c0c800c0c01d1450018a1042d0744100e280c51a00404400c404030b007004841e1b0000348800803d6101080105542d403800da0311410501c803515030118011000500 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 797390908 1250 797389658 797389667
    0x1090602071401031d0601080706082d0a020408030c0c1801150e040902060d09031d0d0204050403050906130905010608040f0f240f0b03030a140d0b210d1d01 69
    0x220000c0b411170301c0010031842c190f09051400a8020700a00e8010550902400d80c0291200741c011003526000c003200c1803500c4851821101c140180d40056038140d0100c2c20301c0c0150340540d1301178800e08094940e540415800965551070750300c0b00340e00030f003030328810345030401c0d484200300d81201c40095070510b50400c2041e048032210a010a00d0394441d50301c48090f400f5032942406010098000e490001c3d00880794140608880358644d00c020f07a0300e41009013000b59446107003107560100d906480100c3c1940380c501d0300766001d000d180304641d040f82010901005e402c44c00138200c422201a00d10401c540e98031000203c0c0c04c5407007101c1c00f40030280b5140d201400901e140c60340c241e00a000719092801070b0090849040c0b94000070481d10601c940390051402940c2c1c2e01c2c420003d055800310019480c0848001c400f8022018185000d010103a001c1658807100c3c540d41c22203500c160000f0094101c005602680e40d5012440044031b000c2d901c1504a54043c82d4000c0750868410b8005001a1005d51084001101d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 797392158 1250 797390908 797390921
    0xe07030902060f0a0203120a0b13020d18030216080705010e060a1403010909051020070c18021213030e0d060f02190813020915220204050109060207140103 68
    0x7038100200f08580b00c1480c8000c0b01038030403076070700342d01440da43c521101039184003580141001006a02d000c0c1c8260f82542c4000201100a0410b10056161000c44203400010301200e4201d1149803801040d034420182d0201e10b00490080301e144040605896002590751010300d4010303107001c94010040e01009103415000380000c2021480c0071800303e0305045948e4a260020383c0080400e60303d030b802d0401000810701800008a440ca0001c204400d042c0102140c03c1c6415105440d0060001540750140500302c0d8514020380f6074020002440007817110003034001d600500c2407104a02e8200d000c5000748908101000c8034980613524031102e0b8812004104041d455076400302d03a9940e035405c1e0f849103400c00e4000f030000c4040451543c40c00c4000d5400282032a00d000380032501035124500d2500040c1c0d0b0b6145599040f01d000c4400180d403900302070100c1c1e1302c5000b0568203003041c41c40982c61030700500d41d0780003002521020303030f200800c8030f6072180140d9455845d4010000602c0d80583e6480741c03035110740d000320b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 797393408 1250 797392158 797392163
    0xe0901020c0d031e0e0307020405040c030503070b0a05071107030204150806130209070203120114060f070b060406080309010801090203250302030105100c08031305030c0f07170102040e070309 84
    0x1494882940c0c025480c21168050b18008682c440001d45064100d162a803440d03d07540c01014000d18031503501d820b440b84a282c000a103d40e60b07900101c1c1c14060001001d40103154884100d0380c0d2881181010144c03040102c8000b43c4440c102000524424171a4207249484851a0014850301d4250b500700005802d80300403560444415980001e0f5000d07007002018050901c0341130107414146280140714400c0e00c020010303c2994130030000705840d9402c105499045605054078620b0001b22080000c0291180d044200c10034140480d130602404440c2c0c801a001d95030481d010042c155035854225140e004a02038180840d205800400035009039800840d40000c1c00c10003020201041d003070511008100032825400254080018025820101102c26625840b414010101c0309503980c0c01c0080e00c002080e511006800d6141c02c003c0090030420f45180b00d40341c0c400c0c1c41e8904080d42005a0360502ca06c1a86a4016602040345400c0030603c00c9400f0f64010342000e0300e9507990150158090982032004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 797394658 1250 797393408 797393411
    0xd0e0d020d02151308070b0f01091404122610080f030a03090302030f04061d040605220605060418060503161203020c0a08031206040b011e0c080a090e0601111b0a03050604080a080c130e0901 83
    0x28503e41c1614144094203203202c070f03c0300c513681d013000e0fd06200c1c8161540c10240d0150b200f0600045101000819603a03190b00d81c0c900840e01d00705a180490030740c080c1001010b40060042070205046800010701800c0d00302d50324902429240100c10001507402502c903007a0050361070026950103524100010306e0b82000c051700800c05a6548003c00e13a5030740941d0108074000748403011158400568000c01c0d0040408500803c1858442c10111040080c03912481241d8010080031400701802441090700441006003100c00090b42d501056440354072034040038480300115800135515250a01c1520500c0b07406035514541e4060216170f50241800c40e200071014000340c20b00c1d500000d0742c103a005010896180e41c8104a552031f0036043c5403a1200030340850f040c015406019041c82c140000d5a506000681c0a086e05049066000c280d80013a5600301400782d018500c100030034444002c00514082c0415610408207a40e40141204e240c0100d804502c15031000301030420607051900811608074144800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 797395908 1250 797394658 797394677
    0x409020906120c07140a05060a022a162c07120c051b0c1503060a030f06230903030a020f0c01020d0e0d020d02151308070b0f0109140412 60
    0x402c208180101c1c1c2c000c01075900020b01104104404400e00d00c10180000101801d000c1550384a4440780002c201034810b50340401c0315070140444444240321344c07038920130b040c0b0916500b01c40c850301e6298455640f0940b0342d03070000002c0c040120808542502803056040e002c0c079131000c44542580400580442e0401c01081c2d04440e402819102d94051426941c9600c3d40e500d25070b00c609400c0b56001d42c05d1038001d4001203500605902c2d50081c40d01200603c2d48401e980c0d6441c0b82c0000d21354511a0800f42141054039001001c002c516803114011910302c8940c00300754611440c00302401c0d00112a050640c1d04107101048006e0318a0300904a40703821201490b0034038007000f0340c031401ca800c0041050005a00e0b16500d00d840b02040c00300303402e03606d054805030020140d610340195580d01c060101c503510060020010704140e5082040300e045c1c40d4040036660340d0f24102e05260311161800d4a10083e816201c02c000101302c19644101e60020900440341180703903880e5141c41c1c0110070481c0300b04040c0b00d020348 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 797397158 1250 797395908 797395927
    0x19020f030f040503120a050706090203012409050a021e1602060d1e180f151e18030804060504020d0501020318060f0f1305070b120403030f0c050409020906 68
    0x2010300354040d07107002181d4545161404141c90110380300002c0502c24010804c2501c3c507940311003160354098006070003203480d0280c1d00c0841c1c010000405030452402a41c1109020260340924000407039402a4040c003040d11104100d50481c03150100d103851500c1e81e07084003640c0d014108090305083d091242100d505000e19000304800b0740c820b68074042ca031603842e241620f0320080415410b859000515040040b034082c801d480a089080c02005001c2d003210031081c20030445d51f642c400c554054480014015404413140480203081030440d070740304c07041c145490344000c3e401c41684a0b0903140c0640c0c5849441c1c5954035500c0041c170b0043c000b0707600b00401e0794a02e00400c2d000d00040d4090f00c07448500080d080010382c5041d0602d0f6000d0f1008507110210024030850103c103046158000d0030300342d409a110700240c50b0551501203e540015032120001c11070b84107401002032500e00c2207004c3d40b410700800b072489017800200c540c0c11080c00d01184051005100c1d8540c0c0c0e41c043c1c055080c010345558580910714 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 797398408 1250 797397158 797397163
    0x2217010623190b0d0e010f060302090c0d09080c030301030c0b0c07060807020c030a0507080114010803090f01120e060103020f0105120703020c1e0703170c0606040b0d0605090c0a061419020f 83
    0x12500c0a0115258003104400c1d8800344076425603242c0c0700c081000609d0659000541c020f0307029000e580142c4c004a09945d00d00416800101d403607520403006a076800d8482c024030340745e8200348400d41d044c00c0d405c0341c00030303040001400300c83d0702c001120090103119050bc0340540e905180504504c045214130002640540c904220003100140182e0041442c285440051800d42c0c1e00c0300043e4948010800040003526000420f480da940300448440050346051401240c07c03d28210101711240c3c20700041c42e0481402140c064140c0340250751041344040d0800055400f48a0811a42906990400007030181407003a03010781000c003661015100c41707002950b00a482c02e541180080c0068116200820811107618001982c040800350000e0405000140c00ca484440041a45004584982c0ca022035540e9030099102e506078494400c00c6241000d900d07144d501d0118003441401650b243c00b020803031070301a403070901c40c07102640711040c5410380240302e5110240c028108181588102c04009101c030405 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 797399658 1250 797398408 797398417
    0x120605090d0c060923100e0304080c040507051318050708060612150a141c0c03082a010b0f0301060f0303120905010507022404172217010623190b 64
    0x10600240301c06c0741105500800c0350a503010784030702588101300400c031810011400c0c03c8245002c880000301555034200c2034809200d544c001000c1d407088000081080b074190380003194030840c0c0010400107955102025142131038182e5013258841010b02522510f0308011a49a50264076484242044031030000411854004c5801c0100d0b030500282c00001c907400d06118508803410400d03014003980485489425001d0581e0001401c61800001e06001e0310000300c1d1140d90101f52030f9005007034140c40282240c000c226500ba032070b00c605401800c158162130140103110550700da6042007040c0b5131940e6401c1d51400302c00d00080800c40d88550344800811400e02c207092141045802800b00300031420310fa0303400f08100c9210208485035160502020821a00c184c0030023030f4020800660300e0306050000311001d0a82c07a04003a00c01c1502001180700405604682000180d1000a018094580848103031184114400c038811298015407400c03545845070544004070003883c00342c0c0040d900c9151001c1640e11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 797400908 1250 797399658 797399723
    0x60d0b01141305120c0d140c0a030804050316080706030e01140a09030f0c0302030d0e0307050a080a0e040b030309040c181527030206091801120605090d0c0609 70
    0x10242c07401c0000b07040610800412404000142030000d203888000b603201c81d1610006486442c4001c40c0081c0d0400c01c0184684441e0001c00f90300b503440c2c5d240340200e0180c0c45405a14000d01409015484240c649120303007095070313800c0c03000d8900142008030840c02000c140303020701c01707641d01c40000583e0241c8488500d4014841c1d0300002c15003010034103000d060002c0644610341080100c540800c007081d4048180c408004202002244520b0f2560000385503008001c805007041c0a030540903810403e0010003000b000700b039a1a0301e182c040c0054100411507500311001e9402d070300100b00b540300c1c91800e0b501c0f00d1800d00503420500c1c10f007141a43d90b200e030003801c1c1d00400c0d5000c00141c00400003e800019000c094020054015009450594a0690041107100c000e001c0c1c40302140e0790078a6a40c3c400000c000304030050342050550fa41d0f12004001c000301c0e03c0d040c0d410601e4100440c03200640070071410404211b9031a030a1381003600355076600c018510500e098034006280340300d01c9540d101c881c0143d500ea18 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 797402158 1250 797400908 797400937
    0x6090a08060f010e040302071511100f06050f011218050708070602100209030d0c14030f21070c030e060f03010e16080601020a030c05010e120c01060509010302060d0b0114 75
    0x2c1e0450041e494004180c019001c0480d00400b000006640050000c0030745a890358035035400c0324628001c0e18141544100c000070760248080c04020a580d5501140003c5070712003060018541c0c59040c062040d0081c0641350000d020061441c10510440c0c21400c08412419103003071a100f696144c07242441e41c5600200c20b00c0d00050002c000076981040302c1d50402c94038403811894a484500000c2d961a44450801d046c850041605c0c1d050003a40c2c1300b011501c03100c01060300c0c1c2c1c98006450b0f403861a4001c107101403411080e82028110f040c1d646002070b02c14501902c5015100f07115840c29100e90788007954035a4030100400c411460781d20610701940c002c0c20690991152420030740e40700215940c1c44900c0401b00b10303e0030104222603900141c9a0703402c036003505064811290078203185015206d2840100241c0c4540c0c6602210804090003c0c80c0c0d07405040020800c89849004212a00f0004c0c03001035402401407101100301c00244d84001c10408050400d818404108100740110b50801058050401e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 797403408 1250 797402158 797402161
    0xd1407060c1107051804060b0d0204150501021e032a0a150f05070206011a09120a14010c020733082202100c1722090507020c04050606090a0806 63
    0xd0364104030f440d01805007110360042100815003250b8002c4001131014000319101c13010360025441e83e890034098903802074000e10910403001140c0304150414407410380140300d6100002841954000030f000c094880d84040e5140c1058804803e803004074110560154840201d032001c804542000b0306003031288184c2d02000828840e09800c0704440c00c920b10300c6403250418003081b0308954003003050ba0641e26421b0785041c144454543c0001c1758040d0304c660303540080d03440840e980141c10000d20000d019224900c0490709103103140910317007a0b8a4030722801c40941e00c140380600541c11150440c110041034041400d04800c1d1400f0385852000c860f140c45008076000e80c06100b024240101c000f03203640008914003900f010280d0100d00406082d84204080181d82111002080214640485054195000c082c0c503041c14500d0711300041200c040140c2c183e40c5e17910700012140840d008003407181f4104c0d00076004006040c0c0c20300010700001004241e221707504201c0480b0703a41d100f80524001d02406402000705 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 797404658 1250 797403408 797403437
    0x2070b2a010c0e01120f02070b1f030f24020307090602010f020a020a1103070b07030f120c020303040314090a06031401060813260d02030a1a030d1407060c 68
    0x64414203903010026074144866040c200c1d03004a120303140e0560a00e40a803048441840303040007000e50511104199000245034000d2101c0c0c911914024802d094050041401800003c0c0d078811291000030051021980310310702150303217031078490191480030b125070701400301c002c0d461001c03a4070813100c850104200b1034090110550900ca44010320084080071450000d107188040c0d038030050504020880381c3c1c030032000038094800b03101e0700b001898241402da85615041c54042c00003082203001c20000344a40c101541001001d01914000c007169030051072458849842c1181d4522000c4c1071f018010000f00a060100d81315080b00d00014103847d580015804207441c0c00304100041a8460780412010500f40126640079031001b6054a60001660b0a440e091700072038824001c4412803e4022503000c44c6000c20b501e11703a001544a83c400c0c0404000280d01c1c400d080d1100112480300d141c260303100c400d8021740c1c58001d012403141d140304e8802d07440c20081541c0c3c42c0e005813035011640200158462404020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 797405908 1250 797404658 797404717
    0xa090b01090501180b1215010e0901020307090302120c03060108030d05150325030f080301080f070b09060705010608030307211811131401050f03010504050705040c02070b 75
    0x98070031410305018039450011280e00d502021100c0b80ca8455944004010390b5403585507808258149030240c40c90410b0380440b0802180e802d21840100a03008000a010303988103100320b0340301d0401d41c0c0700c561045040d502403000504d006880c1c12014410b1203040c0b544c0381e800300600b9000b0f0032000f00460b540c0d40c0c0c040340700341030380c0c005481030610320b807202c4443e40c21740c0d004511005044580c43e03030341010810b800510202c6240790b91000d0501d400f4102070340180042d64006505032444181102c500d0b925a841c03541d13846043d4414480e504030244444041403910100621500e4003a000204010303448014140c2958416104540411040b10081c0366020006522902003402c006013081700000c035520075244400a00b00003860110b500381091040d1380c80f420701828030a20340d5002c00c200200c0c0141d034082e00c4400e001d860300c0f410310034071101c40d103150501071144611380c800040c04141d480c0006000241180403200c00540c05988408540008120043c207a0014603c10031500070100000c0400d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 797407158 1250 797405908 797405911
    0x60f13050106260f060607060e0a0303110a0807080903130803071202150a050c040e04150b03071d06031e06060405070f0c0b07140d0504020f190b1806030a090b 70
    0xc15095001d0f143d032903110101d60f2141d611100318005428181d4400d070008a1500c19003400500103071405100b116074510004051708954800c0e201005021000441f60456010b0401c040b00003c6004c40018400b85c400c00c840c907001400c0d007048900700320030005a0a051100d82d04447e03110789c004280c0d1410310400703c00b0840c91112030b002a1500c040740b0840801616002030000c101c040e1580042100c0c00031031011200104480c0fa82030003942424504102c000c041e0880c0400701500300005400f0350b00e40820030340100c0744221803801004c8031010410541c581d0003805180c3c14080e01160050a180c50034032a5103c0700c81d4400b0389030501e0302100304412103c0103014502003041420b1001d01c3c10b50071183c0190b40d9078100d18103140702c2d960300904880b0700c400342c00107000c00b880101c0c10485d105901d4004038040c0c0d201301c03180700a03105440c0a00000060448070019207043c0164100040c0c00303000020107540103440d6940b0300d03488254001c14032660040e508818141e41d5010310506120911201d84d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 797408408 1250 797407158 797407187
    0x6090a020301030b010b0a05040509010825050604030f02060d1107050105090109080d0207060b0a09022d0403080a0942050406032a0512151503060f13050106 69
    0xc40c1154155200c22038a80030501030a03104140018408102a0040e07040c0c500518004000469540e1240d11070f03a1115441d90981328118031182048401400d00c5a08209640c0b01602c0c06052034034648800300b034110411001d0b178000270100402c00688800303001e079070045a0118400c5a54031100e140560231214014940000307039140c10f54290025038404103c82d24509105005a00c500301410580001e04c407814103580d002400c080e0000e401007240e009000300060580420901e061560740d460a241c5034417110b2228210202b1040c0001071355200a00f1500609180620285440304800c40c2c4120480c615140382000083d81d041039000b03204140071000740480c85000c4030803520342000e000c1e4003e83c002d81d418162102c0c5c004030641e46000c09113000e5000c901d2822208440360708040c0071544200d04c000100c40e8440700080c03802c940705400d90716402c4042c041603900c1c4020302c51030317032560030180c000743d8840c04c1801c0740303400340d521360110041c01c4da140d500c001035651405001400d650030b1030060 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 797409658 1250 797408408 797408411
    0x1104091e060803030a0b030f0f01050907140607081c1a040c020d320d0902010905091009020a0c200f041a04021608070506011d010e0a1512060506090a 66
    0x1845000c1c0040141c4e6080b21542401090002c02880040d042402e05915185a807158000c028407003101500810b001d041010245d400450b200c1507400b40381340024003100e4005408120314000036442e64020041b1006031400b4006458803040144142d03680f1111003880780c28000354016591503d84504220011709000603c2d007215500c1002c0d210390620851103c50102e11907880007005544c421500700c042032035040b16a80c80227172600742c000b06080780d800d0340051f08a00c0045618105910014010383c180c44950f412103250414800c0650301c103002c01000c02c9030008412002502d030004406410b49141e0303000f05132052413800c0c44104280074007071a01c241c0c10050040303081200380710020820b141c00d840240e030303512240c00340f8005040301c281c000300716280006000c81400000f1840c90b0590784116911150510042c082e524041c0c42801072201400d802d070082001d804160380001c844c0080040340c41c50a83d0b0741d0710007012807a01c0c4142501c040c0e807203508000c511320b4080c03100d591000c0403c60 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 797410908 1250 797409658 797409671
    0xe25032108071d040903050c0a0813150c060221010e1e010f050409080702150304050606010c0308060d210906020f0304060c02060d0906060f14010e030d121104091e 72
    0x10084141800f100d150b000310358a00c03102c0249032144003103400103c0c1800403a01c0d407c1e181c4c904502e007540000c4600d00e00d01590b1001151012010208001d408807a503030703001e0000c0304c1d512044029800304440154004602d00740c84000d50071514000d008040c103c615040501d840c0b6010000a89411f0508601d080c0b02d00040c01880140c100c0780d019507100f0b403000103040c0707080d15024003c2d22138071034081e60002802d103800848070700410085206511401c00c2c5c950f6078131040c005680c542c00405000f03001c1400e17170002035120300f00007010b81203240c0500841200000044256500500c1c9120303007000048040909100e2150100602c44440b480c08005501d0b00e8a041e80040c01075900040082c0301e0440002c0c1500a034805420201d043c07038000350100480c0c0d42c0c0e025208034503135a9100d9205400c02c101d81020007907000c3c000301e103008031001d405056040d010f0361040b504c2ca007030802959540c5903584003001d546007810f0701400103403840d510b00007540b0f51101c03546c01c28444801420f100007800e14a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 797412158 1250 797410908 797410937
    0x203150402150c0c06030109020403020a091401050409080712120e0606031c09080f0105070e040e07051315080c0f100f0c110d0c0302130e2503210807 66
    0x2d05880052484240780d00e59030809907440c24007104140c0e00e83d00000110002c0303042c0300a40d0042041324421200100d80a80e10522082074508e000050240c02c0c803200010000e50415402480e01c40c0e100b00c0da0300340f80005581c0c0b40c2c07040c0018a5403003400181100d102250f011420320409400303a00060052860b45020b900007039840300018030b400640390144140c1103100740101c0c0450b001d441054240c5504902c803183d0340e0b00805c0c00319030846c001080842050a641417038800c40c41c1e900700f208041d113503440c2400e00740321081151130500704d04139598803103140d204542011858043c00086000e0091880b42c80104200c41d001c000d9030740d2107500440e0000301c42541080d180304c0ca0300ca071810311070400e1500c0e041250400c3c40e5012100c0d003010a0b1032108040041c14414601624400c4800110318400404614115281ca14011140340c1c8204420782c03503408002001444148d130f0035010b08543d501c4e81d40340111441176103944541100031003d600019a003080c8015400010751420907005006031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 797413408 1250 797412158 797412169
    0x403081b18040b04091a09150105030a0308070e06070f05070515160302100c11060109111218030415020d03021608030604110a1d0d03022d12070203150402 68
    0x250610480d0f5840745120140c445800007900d090300200915441070241c99604018601260b08070014040c60718440300d80089214694140c07140900103100403201c5036000d46080703102074101d005004035100c00002030787d42c0100800c2568403482091000c2c8003180340c540d1518a8940245100d14480c440c060385801045041d142d8032841840155031700310445c28140e00784003c00c20000b031043c1c2008d203130030045901b103c14000707450011411241242e0361121403000b114502d2a200d00143c03401c00481444810030400b807500248004c40160040141500e1249964441da000c0312440d2504440c160b5490340500074006c5152040c1003e62a0581d580107c1c0101c83c4610030003030070724101001190840d240c5074010304481804882481c0e9400d4480005801804140300c9400404041e4020b54285e081140c410802c450707244d0020207102184803541c52100d5a514811940d807034440744007550b5007000308000022007420b488115520122070042c1410b21815520307241c0c0d03540f0080e00f0700006032502c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 797414658 1250 797413408 797413447
    0x20111042c010612060b18060313021c050d0c05030a140d020d05011d16080a0216060b120a0b060607032102030105040f0207031d1908100509070e04060b0a030b0403081b 74
    0x3140d008d5560390742ea009070f20a005224002941000c020b41c1c441c1030071220302d100340c080180a07100f19210448144406c94a905980500511507001402804a03190007403091000d001d41812025041800c2e021040c0e0480e044100d4a42003140c89500400c42e031030300c40a145025400e910703150a4189001c0c00c2c5900c8510f05c480325134041122680028403e200305a060380d22400c0000b185807105202410020080e041c2000ca02e41b190b07000002c40c44809800248511050798440b01e240074603943da1003002800c2d00404002c0e018000305070303124076215007003c148400c0091200401a260350401d4144407c079014486141d1644d03204025003030100390001421140c480f0180049615414240c0c003094140405901449100d0444107003c5201d21001c41c00210130301c0c131400200160350360260b00540d40d000c14400c187c0010148000305d40800e0040c0c100507098540039185000f1213540c1d50b603282c0070040c1141c09030001080c640c1442030f0407141350207201502c118107902e071b402c1ca0100451407a800701e4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 797415908 1250 797414658 797414707
    0x70920090904080403020904210c0b0f090a020a031a07052b15090e01140403090612021b0607020d0503091b040906060308120601020111042c010612060b 67
    0x242180041e040243c50b0046801031680078052100505040c94908884001c802d10858103c01016140c0300e0244516451001030380c010014049a403102da0b00742c0aa6000a02501c1035806076a00010150701c403015001c0c01103119040f4440c10880c030171002003e8083c0507198908202c02000303214926814030f46201c0810b10301140000174100c034071000300c00800304904040c40c114bd40c800001180d044c907034050901010500f00034002013858440041d44240121070040c08030301c21074000e02c00944510b05032140720a50340801482c00004000002d0505429070716200d03640c1c00038040000459050001c14021107543c1803250844c20002c042a468403000350b0a5220408031070018011982c80c0e8200e080a030303400000400c9650340b2414640007690120010300e8481014102081e455481403150001380500d9070b140900f80b908082c04124001d1140c0340103200d1074001c4a00c0004c030050004030364020041521040706c900c43c40b0071000700b40c6816074001c07034080d58144804640e10070b0500d1403007031501 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 797417158 1250 797415908 797415919
    0x70207090b1009140a090e0c03160e07080c0d06030b060f1504230d050102040e0c03010f090c031b2312010b0a09080118231002092107092009 62
    0x4d207400400c4640c0e4655116254940c107261010b107144c90003041d038400840b41030307041d1442600e030b144000d1344c0b004075807048103040301341000010569441001c0c1d582c0c1111080d600e1078035200ca201d034420150f134915041a90041210010300015182036052101042c1003a1450860314054000c16803943c000d621421100d0f129901081025032003d25000700908001070000c080300d03800f418034900070340013070084100d841402800300d2505421340064034100c030720706010080c0700f60501c02480041c1c42c2580021040c55221801c0340c0010041e40c15404140906a49400d00d058101070a42620281c1d101e001d18034000c10440035010022610a050540e50400c915551751000207104560f082183d6001310125484d1503012101c218180d602100010b0051501b203c51300c0100441d4801a4406402d03600b50383d00c910140004440d29801510011a0041807580014030f011681656a9103148070841c5a0f004a40c0501010180e441078000c00c040e0901e84c070142041070101c85051b40700d642e50b41485039 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 797418408 1250 797417158 797417189
    0x1e07030506010c0b090d09080a1e0312020a030b01020d05160b041b0b180604060c020f061342080411040c110d020d0504090b06040e070207090b1009 65
    0x10b90280882119541e0300c07000062040c0380144109486180501340840080c524240011b8030b20400900c0e105002d40101051416243d02c401d001da445c48904011400d00c80f030398262071403086461014020300e81c070310b49000c038010007084002070030201c4201640081c403405102d000030445a0340ba12694450303110220304003c0e100d50030b0402517142d4814140c4e540c3c00038481d000c5440002c41e400740842d2941030f4000d1200104d02000c0001d28000d50090300b00140e8043c0d03508001d45480c4280750418103005c0d19062074a4540c2c441c0c12400e00a540112039642070b01d003902d8903c402c0b680d04140070305400b620300d40d21800030721200740d13150840401104200808038011505100315696440001a0003d02c10051680301200260440851000049290007a03d0007c07aa0710300219002d984040981d8a140c541800c0c86125002051804c1c68103401400c18440170525040400c032050080c1641d4001304140d41c50035041000350365140b102c1c14090307041c8204260080f50400090016240c1411000c1c441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 797419658 1250 797418408 797418421
    0x70306050c0d0222061403070c0311120a0e03010c05071b08072705010b031f0528091e050915100609060c0c090e1204031203051e070305 60
    0x28001d560a408010f40b00140c4541c24501044512400e02104c00744a550f80380e5800d416512481000c0031402c54410420006081034814410030b0f9042d072203801c0c90b1008880c06c210851030b08000300541205503c1c006106900175400030080644000110000d12610710350703c0f0f00410324010500c00401140ca994034004c0d000680400c1a005442c80904480300295221000500c41d043d400d0001090b0080c145092020b46482c025941030320580e900c450316613154a182c0290740107014200a40d0f5041035000401c0030f9590a4900b403078030314034601803880031000301c2c41c50f08100216401080002c1c50642520b0303c908040c03480714011400c02c071300000c0560301c8042c0d8a00b025224111481490341c1c04040062561062006009550b0303582d0b00c40f0422510340c40140c0c2c261601200c050002c6104c004100b00b00300558211101100558050341d1800c0d101c85100c042c0b40e0899001210943c003403903043d04090340d051003070396446400c580794013218085410140d00b5480b0003030310310000c042c0c4030310007e0039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 797420908 1250 797419658 797419681
    0x23040506070c081506100203090a350102041403030a0c02040f020c03030a1e09050a08031f06030b03011b0c12020f0d05030117060f150a0302040c03050406060e0907030605 75
    0x5014620a581300c50114421840140700c0885042e03210701421071010070707450710010079100c8070b95014040aa1060400c0110417218a80181c0d1100c84c003800d420f2040c5100c41c41201c102800780000015881c1da00701103140360012000c40c0403e01a42c818002410304c07a80c400c00035080150165000505a0030128043d00a071040700002200c074400001402403410b80f81d44030b41300c0c0702a4010316050900e4000b100d8010303500100340c060120703030001b000500401d140ca4000c2da0410310217407801c40c2070081b452400c02c010b44540e00000110b0781e1184030f1125130a003800740d03004140300c11141501c24400c00101800c82c9000c800b0140207059107410928900340200312800000030101c01315117040e81ca400000303120398002d01500700f4181c1c0c03025071541c800320002042402108560101e80d5079a9403a4100c2e40e42d503200309031a5520003e590b000001603180c602c500c030b0b0701c050a9a40803910f80707040c2c2040e0341501c58681c031448040300c2c291708011a840020038075805803980424003081c2c948078031a803c3d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 797422158 1250 797420908 797420933
    0x1230c0d020406020307021f0203070b060d020306040b01080607082e0e2805010b07021225030318050f0d030210050f070221070210020a0f0b072304050607 68
    0x80c40a480040c010400b0b940000c0a4084ca80c42220f000340c2500503038003c040081110169039026a10500c041f900284940000c15840341c405441c0200700600768000038030780081a07400b03885031021074005200c480c00a00156601241d5420300c80c4940c02c054112092444200c1c03a0319100e010000400d441500f02c132151500200b10b008958101400d00540c00e00340903200004881a0200b0241081d2401c0128056a41216100d440882c1404503036000e11a03801c82030400d82c0040d02442160201d2010f07180d86800241e0511007004203c1400c504d40681b16100095107410704003c02003042040c1d07610015000110001502c52810400981c903060349444041103446d04e1150410040008440c0f0404005100d03921b107500711050040b0502e0740f10395148011080514048003080a540942071510128000c09264812101c0d0f0407401e03155103c22448114003181e0505685052042241d07002004985040c03441400b480c05602a50f1611158802d03441514000c040215100302841288261003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 797423408 1250 797422158 797422177
    0x250e06030a140c0a05041104032307060c030e120c041109030106031406060d030e22020c0114010b040503340e0f240d0204020c030c06090d0201230c 65
    0x1c2e8041040b800e81c1603110410340710494080d82c00c2a074005028031741802841000726042484030300c1c01e401c2da2a08001c50407423800941c100c035a00b51012000b89001c100c2c1000400c519549c540a100c402c1c030340241008070211005100ba001d286140c0e00d201000314400080040c11940000c40c40030301e2070081c0d998010704004903455441d2030300000902c9a43d0100d250404d42d440c041d41c10395a1008200441d40f00d081401400145070041c040c19542880101903050f2541c0e41d1401d0400380d4001411750a07a80201350311140342c0d44a098011000c45201039242c0500b03625a04942014200008a0f07a100b0540f021840d4051011506103240ba051401e5507820741090100b0000e04c5890307a40c07005c540384040c0c0302e110f0f426000b5000941e400c0c4410b522499840d00c060a0a00d001c400701080148018103010141c1c1d00507420400102c003800100018603502030701201600c0f082c40c2881200e420034607040c1c0841e0035a4106006c600318805162054001520450b40c5c010641e120b120b5164107500a8240d40c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 797424658 1250 797423408 797423423
    0x915120a0504020a0807170706020102041208070f0609140f0f0a08161b08060c04030c030204020c15090a02090906060a05011b05060c04051c030e10050c060c0c250e06030a 75
    0xc210300d402c0707500003406806188100d0b01009e569442c00c07402c0703115912070a1007003900e00081c180041c150a0081651a0090680c000010030a031503000440b105960b00311081c8250104040d14408140240448100d500010700004030715410780a860344800c550041c401480001e00e14100500c00a42d4840c0603001a0ba0448602c0405900154072000e0b01841c1c10503c40c1200090080c004002180d069039030100910b07a449103554288406500a600440b442c2e000305910150159000d19905124101d0400101881d03240d03401401044035010306045a19042941046800d0b100c41030b05000f182c40c2840d040c804c0120301810501d82d40502c0b04c0c000c010340942c20502c2045803411018200350b50040b5400c507105020807004014034055820000c0c00320301e8102d0040040d1420170500440c1461600f1f203940b5001c0614142c6040280c1100c0035000d40001140c200d1500200b0003000309041c0c1d0755607101c0c603503e05a1140306100400ba104c0c880f0b900d008140000d0f0181c0381807044484840d400f01a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 797425908 1250 797424658 797424673
    0x601060c0c15080603210a110c030a050d12200306030708150411030d02061b0c15010614160b04020f040212012c0c0304170408030915120a0504020a08 66
    0x1c00500003c3e0a5403024443e00c0303200d0b007401400030202a20181c1148400310140f81c2140d24134103403140440b00509140c50b01a65216030b901362010302180d2204e40c03103800901845194501702800b41500403820074040d81c5413036080701030074205100300301308007503000e500d06d0705da43d24540041e203400482d41054801d8011303254a0358564003c200d40078000c42c81410000340502000782403640d54a00c203d64031005901002c0801c0c041600d090301880c120307560345081450100d48107000d520348180300d010b03000c1405c601e0004005442e0301a0301d03c0d042c0001c0481c03a52800e00d06080d009200c0b00d103000081c0460700789001280856807214140c16106802802c1551900a09410741c0314505c800d120301aa500402c00c81c40001590350140d50403142c41a12094825440d202c03040a49500010030441342c0305030500003001c51000c4000540000c226080040da514412036060162042d0408140e00b2a00f00521403200036407541000345510100500b00010565078038000298440d0281c2d004111038051f84a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 797427158 1250 797425908 797425949
    0x130b040e0f010e060108070e03010b03030f070c061b0b150901090504140102131e0e191107080306060a1701090903030e060103120f090306110a0f0c050601060c0c 71
    0x162072241c000426040c0180c1e0f030700d0300d00b0301030b601d0122074244c0055071242c0010b204c41e000b11603910440e000a40002040105800401d1555101e800600d151102c007043c44800c200e01000d1030000343c40f072071606003018140c0d00e140b24980c000b5120018104000703031340000c100ca001c01d8050f4202e0a17004144030019655074550900510040d0707401c5d600080c1010313001c041d900050003140c00b400e601c2032030031512500e030176811a00c000310416000780740000e8010004a46441d1410503010ba1150134183c0a00340c6080495001c490190341e03240c040c00d800707100d44c0020070032410580341d201d2020f4505503034a85001c401158500c111001ca00880c0884000210716145180d000c0c036040c620039201007004000319040d55030303201424840102001e200e8510075001c00c0c420038008042800d5418401262a01c9981d12415202d06410200d1704040208502c5004c50b44000700d51034440403400c2800369510961112625000b05004001c28407481d42c001c5810400e490303c0000007800600c450046200814 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 797428408 1250 797427158 797427179
    0x32003010507090e1003082b0c02060709170319050904090501020d110306030c0f0d33090c0501030e0f01060801022a0303060409060e010e150709060c08130b04 70
    0x18010809841c050000140c05e091491000030706a0f50003602a07814448164090300e00c4a500c080c0074000980401660300c04110240103d55000500b81c01400b910b25059070020000c900c29030120100c038140d400e01d034440402c040220f6541d1200f103075900f218940c0e00c000a4560b03204420842c2d401c6031505603501c00740720065014000301c001c020424440b80c1c410481110311400305442c1c80d40d05070081c015039600c501c2c0008031504014805003000070070950f644c85000506001d00d00440c81d0740031000340c52400c2e85507400780c1040c1c9101058104081d641030384951000329003500a5038185582d0313940c0c0003007042042080704400c0400c1d2009008240d02c83c035000d4081e4104000c414003408400e20800e0024201040b09e070700c0c1028036001117040d691284200006480003890582d10307541d45d40101003200c3e038280104414201c22900604910010302c110341e5400000800120405c50140c4e028001c0c160b00800c0400b40f9a0451001503c41c152069449103c005550001d401c48500190001da108001d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 797429658 1250 797428408 797428427
    0x1207020d0e010e09040c0b190905061206041a06040603020c0d02070503031c14360a150f1d01060b0301050d020d060b030322050f0307032003010507 65
    0x560954100809900c02500d14540800c542030115040800014882c2000400c0030b0b4081d0041002e041c0d0682d440030780000c42d601c00004400c070b141a001284038403941001e503500042106031a11407078036a040120040c450009824244103548494000c00c414103a40c49680124000403c40c9903500c0e03442201030300940c00070300b00e00340a001e242c0b0ba0921050010a8007021210083e003c0c500d0141c940c445183c2c10704110304034041042e0342e4001c0400500307484174440c0c4503043d0444008038402e4001c44103e29000d4050918803d29004c03041051010000710306005d841d83d0000220200048140101001d019030160f1560b10b03900c1c1000f500c0135000c2054082c0c51418000c40208003894442d1512071007171009000e5150401d91000b581c10060a0844561421902030f120001e10f01100c100044d045a0101c0c04940c0b4891842c201c00e184030101d50b102c01e00402c001c482080c11b180c80c070000b180d110745003448094802c40a80c1c089086864400e0482000781c0300083c0200242c4c5440840901280348 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 797430908 1250 797429658 797429671
    0x3020706050c040b041701200a080a06081f0b0909010c080108120405060a0c02100f12141609150819021e1602030102131d131209030812 60
    0x10480850307200b02601c41202c060303440040c1e0451400d4100baa0a50604110182d01c156030b41d60f90250540301c02298050079180c040780045c040c1d99640b0014000c2c03040d50301400c40d0b420a868140d0408c25103400107440c1e01700a0035201e00d0b1002170f8190018600800c2c00b5080e00c1d803c00c00c54000c104041e001907002049010182d1032b401850b907210a95161f850002950200000c0300801080c08207191550140c4512452403074000a1a00c0550218a44004998425000c5181041c00220840d00480003c11608401000700590000c0e10604001c0f03207070240410025031851420b07011910b226407401c1003c3d02145044808403d80d440009040c02800c6980540510f054110400702c400d01e40220365041d031000083c001d500c03400b640c00e50005d502c6909002d25500030745507140d0041c1c80038009007036000d10b01e66403c0d103603500e0001b014140d00b0b8200c3d8543d11503900f110801254010342045418250f8010304135824104101d0010340390b03c0c950b40c20107030401360b0102c4e03218004281c02440500c00e52 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 797432158 1250 797430908 797430911
    0x90f0501050906040b070c02060d020c0c03010501090c05030103080d0e0a0b09190b0f07091a03010816051509040906090b10090b0f09090312100303080106080f040807050f010c03020706 81
    0x42e1144030075600d804007510000e1075a4185404250f85a1003903426031000c030300062542d8640004441c0840480c1d00c00b004d43d078100d81114a03010464582803240a0040110010500011324a024000c189100500000b020303144041415005001507038002d41e0010754040440d0030071030141c1040c1307441800803241044c0d03512801c040b02254240d800f03a8030758a5540252044400e031100c01d0449a1924028000303002c01613006000601600c0c0440c1241c0a00700d0140c04980e29410102018103051011022004a03805100100810380385c0448101c0381070b10840750551107080840005001d4075401d00d000d8402414599071805002e40241d6030307070240490b11015003007aa40c0354285803d07900e016003855440900c0c0d500d8044942001c0c80e030b40303500115031420750b4500f1902001105e00d4030029955002009503c002c14410550461421805452103080003040c07407401041103140700e40000c0005150340b401198800c01c002c020400700c840f00c1d001c08003d005003807003400300500940204030140c5909 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 797433408 1250 797432158 797432161
    0x403050303160c020a0306020901030f020406030c0e060f0a0804050109020306150117060901092309030705070608090a06090602070222061403060408030402180103030507030305010801020307020a0b070909090f050105 95
    0xf0301484005104940c0603016410b62442c549a140081d041811140e06154503000c40174840d070030520040016090b540c50018440e1303d01d0000400c5d190051800c00c0c0078183c1000071144041003541914048000b5183c000f000da501c43c6042405040704810003034040c0320b98003e00c10100d003008086041640284d80703080342c0d041c0f01d14905d10041c1007619207a0f00a00000c006018102c100d0b0031074032212605000045032050003100140c42440100c1d0040c001c0d070808180e1104120302406104000c0410f460080c0442c14950300007512006002d4004282c0c03540c442e0310f0001c01009070107803800160002d0180034907000030180e00340300c0c8031000143c44c0304138680b043c0801c3d007822207a58442d034036501600802d8107540d01c0c0d030f0340d000c00d80c0041e00999010079a02012020f115407115000d0207180b003642ca49440301501e00c0c5c05000d480d4180c002000a0340148204200303107a001800d0030580d038022000200b5501c1d8140141c0701c40c01ca90300042e02c51030811101d00305010407110f848602c0e40c4100001c000e103 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 797434658 1250 797433408 797433451
    0x1c022103120f132613030609060b010c0b0613060e0901050a061208090607020f0d110415080307120516080c19030512070905210d050a0c061a060403050303 68
    0x10b001d05100003013440a4550b0080c4000b111500c20040e90741440c00301c28541902040e446881c003486034801c880040c0c0f900e409804103c8030f40a104110b000a003004058041d0a40c2d07000c12503900145501d003d21007000c000c5071800002e8010600420301207004030098141144481d001e48800ca83c62004681412000901c1084685034403003c181c001c13011900b040b001000b0000964002c1c1c2c01682d00c50101e04c011005a552000300b90040c51081c0340c5034100d4640d540a004c262805a114103e80c00003d1004200e2441b0120845000d641d000d1501c50200f2240c400588550040e4100071120381038500040d02080048801051100924421200da4a4416a91912807220880010b000030b50500c6070441140b5030740801a0405441d0034040080342d00c8401140e4034500390744000380c04d10b00164070b4050000091040e00c220308498600749150041c1d0b60b074060510311222a009103619541e4200c1c01e40c0240b07144031001c88050042c6055076460b5a07050007a1b4a4100740c612413111a07000230450b03075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 797435908 1250 797434658 797434681
    0x151508090d0212220b0706180b010506090d1e0c08030f04211208040b100608060d03020f0607020105160e0307050609180103060f0b1c022103120f 64
    0x1001e400d41c0104a8010304010307a550540041c40d0071a813a5441d02c4000d0903560794070504401408800d0034503912040e003030074224155802e00300a07202c020441f52025010504160089042d658183c9105685103043c0001c24560300742d8200181800306a410b900c0c50844a45412282441c0100c641e0250141c607105041d40340d1041c076590460410040000300295845245000607005030300303001828048098980fa00c003071041015600c00100d000c3d0421082201c041152500500400c408800442c00c003180074043c07190180500d481824540001300805100b004041583c0b0840016243d040c202a03101a011b810b05032124000100c0c003003000e213034451150340300a40c1003500038001c1028500d002c040c00490f03400503249035005511402000c52402d500401c01c1d000718403c2000160a03000950040c2c00c8a07425604030344a21403007141c40c031115407412207118006804803013520320751114181c41c0c0e90404183d003905c11140008101c3c0b880b04e81480c03c1d050300c681e20038000300794a40d484510051 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 797437158 1250 797435908 797435923
    0x705030c0603060f092e1a030405060103020105161719181a040b07200a031a0c070b04060b210307110a0803070c1418010308070615150809 61
    0xf034100c91503101030b0b407032482d251740b00300d4200800712500d008141081c400d40d402d00458104070056148540410040341c0d58058200390102c80c0c0c80003860860421b03079642900c1e00010301c40a41004004102001c0034981000708030b0500b0b0344a09008031421585000d41070941200403e4032541d0080440003030410b01404108920707a0b2040759101400d806c095000b02e41e051150303001c0e00f1010040c0000306d40221071800800c60140280c0300101104190340324030785040502c9008600402c1144030410000715031707100d800aa54080d2070004da0300d540d0042030040c180142000035000889074401c1c04107200c0c19034010700c0d50b040c00741d82014440000b03090382c0b45c510300c4041080030a603200300401300208440403003c0d5401200100640743c15030740c40400d107146400840c01500d074858441360420060405c4910101140360559425070041001c007001d800304001407101038903102d4002092409c0042c1075125542c200c20a80c4481b803e903488039440020804c2090040011910035000304102c100001080c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 797438408 1250 797437158 797437171
    0x91e120c052e11040312032a02030306030631021305040803040c0f1a1608040603240b1c0f1b1709061b0f03010303020d1808070e040317010303020705030c0603 70
    0x200340a01e08800308900a08510401c0c248440120505011038034083c50008c40540c01a0300664690408504060030440d0182118402c9042c00080b02c025005c0c000c1e01d040444a4220301e10700b5084240041480580103031010342c030140c070b001c041004001001000c1c50145000e00700229100b520b5002c05600342c40c0358010444060700020740244140d00b504020001c14030b22980ac0241828160350300c0342641c000d6001480403d80b100761040c28510721000c900203406210340c50215061402e10b04100314450000342003d4207180341c003064845802c58114040d00300764a0020040c1a41c0c0c0550f664180f450070b80309500007500d0031200380100b024401050300130002480540900d454002003040a03150f110002d1030404c0c41801942140c07414030b07000c2e40c000e5020350050800b581d540d1400920080c00754051641c0d04080303082c107202000000038400e00f51000346005d0280e61711941170548002000020b0020030009460001c001c0640c00704000d030481d07909500f1140f51341441c1e800c00009000441d03e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 797439658 1250 797438408 797438423
    0x302120a05180f0a080304050c030604060c0e040603020a051216060f08060f0f130b06030a0b01080108030307210b10022d0a020d080c06070201091e120c052e110403 72
    0xc60307010405c4800115005071080049071101c2c40c00c84082420900200d8040c1ca0059170303a8040345240780c11400d100d040340340c21a0200411400c5600050306420720707014003030181c661030383c0303014003480100b04401900f685010900a002e0b901c0000a001d40c00f0034041500080003403010850a041040080700000c6004000305070048003001440f01040f10001e145014503105e1401003517a0704e5070700c0254024450f0080c003180f0300c035071100050b29007401a80000901da10800c2001700d03103a803052002103042004007241241c80b069440c554040c01c00c200e109a8006100c090400d0f2050300010b00d43e03100782003601062012a060340c8004140e40c92221212400d03003164120b17100518001d1340013040203209250950078811a000140d01d00728048035940f000d80e6441e500c0005011142c05034038000f101006a0506981d01543d07844028151021048144219900040c0812400b84100c84000d40c00080059406030803420850301420041032010000d032401d407210000490700000c90341a81c3c1c00401 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 797440908 1250 797439658 797439673
    0x1203020a08070f030f090f0b0105010f0503130201020705120607030b2413030b160e030c01050d051314010b01110708251e030b07020c010801060f0302120a05180f 71
    0x400d843e03441000d03601030100f5544054412458920744030700c02201c0d01420071159080d100d031404000700310301030b0411030502050084c0394034025800803c40ea0b101142c2c070944116003240c0d200507071801d0b409030881035200001943e400c0b080c40c000283d07188200c00e550360500039403050358144805610301040c414802c0035a00100c81c4450b003044000c01c0301e13030500300e414510981d407074640110101c01a981c0c0100440c01101c00702c0c01d140d100c8841541620300310083c0041482800c0042e0551051210448540f51a0b10004200368101010180c48940080081c420030011038061402002c04a202074045010035240701205140010b1140c20b45428100504250440c40c0f1036406c9500300c030500d18110350f1320250102e688121104540500d16801c945e6018031800c1d031030004070b880001072503101194800d00e008401680d00454490445241d801e00d01d0403040d42e01da00718082d200300032a208009030b514080c0041c40c02c00e82d0116200d0481200034191103c400c4200c80d13110b000c80e0340190790542c400c0c3c2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 797442158 1250 797440908 797440921
    0xe010e150c030409020706021c2a03020c0604210c1208061909060515160b0c1201080706020d0804110907030905100903031d031c0b1503041203020a08 66
    0x3000745280c000c0002280e00705540e03040c000099900c000c004445070b40e00407600ca09051305400725004120350071300d010f0250544001111989165000003049001c0d2011409800076003c0e60444848001c001c0c01da4250745005d080621044004180005000c01c644015030340081c07080180d440d8066100c0085125656102801c407146000a800e50ba8015062061210301d9071202e0619001000daa41001c2403d40c50441084a09500b0045610810908120140c280011a011000c005074843e9041e60703070ba251000406e00500803e40581b1038040340200110791080000344000860b892075003140d84081440400f101c04000c150f40003408158201d421110718548400601d07480b0410307180004103400161500d80c6400002c5400c40803c3e03648490000c20325915004414104900b246045512843c1080081c0d0781d104e00c0344402d0920242170840903803d54503800c07103c0e800740e00911a0362403000d00149810b091780150340c00c0303402d0b1107603801c0ca1303000902034000e0b00c954180c40e0300c2d10407581d40c800 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 797443408 1250 797442158 797442199
    0xd140d0f021c031e050906010509131209050d080405030d0c03050a08061305191104050f150f0703120b040c0c080a09081609060b03270a0b0112030e010e 67
    0x2100c04a05142e110403104e030942c103070fa00031140c0c01900400040b410f800c240203200c4c24a00180c10050054480d581040001005107144180c0954401c02ca0100c0d0500c14400f220104002c0d000b271940904d04517200c20600c45111301400c02e0b50300032070507900701d2180c0310f07000d6818250508004001c10824040b14002e40d01450000d40e001d40058020f407404140d0703145070005c4480446800d91150212000000fa0307039110f01c130740c81100e04c03140d6a85240c9400e000c005981201509041d900c2a40c0d01c8204500c1d00c2c2c0c0c40b8040d220300d080c4000803a9190181480d0142c184882810400d1115142001f0405140760500074104c03041919161103068003440d840f10384196202c0c009400520020407030000c1e20110802815504d641c0314504150b0250415074450141c1d8590340c040000103070b05000740304000b034901c1000ca404010442c40080700403890340303003a810700003c540d028222074400e02c00000c00c0565004e107108018030076907030f100707106e54403400640308046440001c40e0005283c0c4800400100704 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 797444658 1250 797443408 797443453
    0x9140d170705010207080c0d0c0209010b0a0c0218010305150105060703030c0507140607170c03070f020f061608090f06190f050921030f060105180d140d0f02 69
    0x311a81a8035040090301c4842c2680d001020885003218000784901aa9005121401c4041014030f8420100b100e00e800084102c00c041c05142c00300c14000035910a030310300403440302d01040d80c00380104070420207444182d8500e1000340f205a035540202c03076a548114450070a0300d41a148014503032424400c503500d08034001e1120009060501030f04000003000700c1c160321440124030078564000c003007524100c00020184a82c0710041101104100d05100c100d0f07142600f90382d0b0007641c5251031001c0351070021049203003c07502d1a40c0c00489c01110144a041c0404405580001c8805c0e06c3d01603c0d42ca445810f00d948850700504015960400400300e8210500600500070501c0c0b4202c0104881c01502044011070b06c0a94900b601c651200c0080d600941417603010420120220313078003d045150071000e008050307100404081c10000006049408107606180e208040c070300242c0b01400310042c13031070001d45404001003021018030440e00c5051500744a0400019480300c0c0d80e0240c0300302c00c11103000c03c009400c0c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 797445908 1250 797444658 797444693
    0x120305040b0a0c021801090c0509030a02041a060304120e01051603080c0d0f05150102070602060106051317210c0a020d06060b0a0203120a050c0406120e070b0a09140d 73
    0x910021020150360350036841001c541411718980d0360f0303500d00b10180301154846001c03482800000d00151441d5500424091801501903802142e0705003c0710841c01ca0b4194003c60941c00980403040c841400464040d140100c030303498031060682e405000054429004a00c003001c40b50210b0664072002910a440003034011003850240d504040c0c540110809407400c2c1c52400c0c0c0703110703901c00030400b4403050514052040300080c0040c1c030303005042030300080d204c6c9014002e81017408030019281090b482c503181c210004018150a11a50100104080381c541c030600c2c13100c81202c0c04e604d020102c603405d0780d01110201c0856038002d104d0030001da802c2c400c0d1041c0d02c02c002e5444960710800000c0765000140140030040d01e41d40516030710051101c0d00c00031000082c1031840e10924010070060355180c0c140455040d20064286031150030059034030200500740c00e1030644c07924007514200080005210025007102070094079444801c40d143c8068415148507601416403004400c08580080307801200620303005103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 797447158 1250 797445908 797445917
    0x30516020307090c080c0c060c180306070e09061e040f020702130c080a051501030515030a0507231c02031c0504090b040b21010b13020a0207120305040b0a 68
    0x84540000307090822542c42140341549a0410150003544030580a50120740d00002504042034143c01c0c5d0b0751880c000740162029440001d00c043c01408a507090142c00c0e10040469446180140e4020b00c4115100c10382801200d0640c04a482c1c0d2504408507020420948041e8030710110070303000c10001c2c08080c1340e181c607019801c10454001d0789450031480c00e00d082c14540800c003e0f941030ba0040260030004c0655000900c0c0c001440419080c4805c0c1e0b041d1200309190100c0d01e6200d081c40d5032245140c41c100180c0c10702c150340705c20082007400f0601c20b0031180c0362442c001c0680307800c00c2584540c03d040c00b0301980c420058803010400e00407201000700381030f001900300c0e81c801540e140e000c0c80c210500c48450001c2a0003140410035241d05000d208419201074400b0302035480b141c4080340250080281f44202c0300b9440c0e1074106c20400950003103010034802007003100d4054555003000002d5000030b0041380140105030003c11100e840d10700310000c40d03605680d59442e00749045036240107a041041400d0411 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 797448408 1250 797447158 797447197
    0x6230924100b030f0702161d04080d0903020c030f0703032f060c09210a061d07091409010c0c15060906080d08070201110d0b21100b0303090604030305 66
    0x400803880a148540c04a60900354141030004020b4030305041f44100c122040c0c102c0d101401035800c2c80f8908815801420b800c04015126841c1410b098050b02c10094242e40c81d080b42d03442410f50004400c0c4500c441902070314a4050070703601854441a05001c0a030100b892151600e0100c00304644080e912440003280c003804401d4031244600b03160069276110030b00b000200c2c03860314038500324018420b81d0107404460550404c520301480c1e110b008210010709565500d00d021a0420f240822001480d000d200650344002e40b0703540c03120020491032007141d01065048000030130b518414402c409600f00c898450140b101c0507a99a10113140d00c030202d681800c1e071240300028081c00140100005000040058446c881d5001e40060095200400a508580c1004d5546101224041c215082d910180c900031032010f02100128034144400c4220444080503002c046540d0000402d051440c5418141c0903c00c40100001b0103540c0d0280c90340080d0700550404c0304000290051008204034952410001e100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 797449658 1250 797448408 797448419
    0xd0b06150403051b0d11061309050703200f0708030c070c030b01091b0806010e0312030411101e080720160b03012607030623092410 58
    0xd03030860342c01110707164070090588aa000e0b01c0811141c518000341c8a0150085190311501102c008590043d03004400c00224954040c00c43c4c01140c02a0883c080c00f4011811310f108018000d002c40402c1da40300300d089020f4081d03484510411550080d01c4a0704080c207052650310f40d04616032004d84841c0b100c2c0c1c3c04001290010304941c100721700950090101a82e6589050501c6003540c004403a00d0780280742400034031502c5500054142d07041002841d0030541811404042490702e062890365107400c460100c00c00003001030a078044410b8010a941802040c00910320580d21046a43e17003101d4500000850240340034414110554801464580b6440500c0304280e801000c0300085941c00c165040346011082c03c01016015100804120034814036541c544a500c1e800f1001c3da141c2d500c80818101d000844c0c8100c100802000341d82c001000300500710130520302c0948000081c6415520400f404001000044085240201118a8689210221740540c0d40c00d0361141d0041a060b07100035100400700300d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 797450908 1250 797449658 797449699
    0x131a09040b0d1707020f01170f06040e070f050a0e0f07050f0405100810050d0b0c031510030b01080105150d050601091205010213171b15161a060d0b06 66
    0x105544100f5041d035950710240140f05006401d000345605000140000080c2a000c01134581e0b0322842c0700020003026203d02c4d000602074082245415110b224600001c2071103c0c50903902c0003101d004607079008002d50f031026030a64080701211401e118807800c0f00061440c500a5009091104401d03890502c0d00ea20b84000a181d203030003801544c00588100200403000c0382c5102c40e0400340c60704a442d101202d03201c0d5641521410001c01105d0705d540301201050141d01c0341102c201b11810010010b882c00344455000070b0042503141020f90006040e00000a000d0170400605030410400d64840d031310308846035500d18050040a441e80381000040c0000040d05404a02c224800e14415400903903038030380e04400058200d05580044440038451040d2041c0d010002403d07031074180c0700412503140440a6400102c01841c8104101469540081c113400c040e4940c08107a40600d225500905d0303a00da009041d09046101103e41070f8100402d800e805010441800c0c90540c4400010300052040894014091 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 797452158 1250 797450908 797450933
    0x6180603330626190201050c010b030f030c061f090903120614040609021809040609020a15120606021b030c0409060902120a020d06110706060b131a09040b0d 69
    0x20418820381c0740380640100403943e0403006104200800e03d040700c3d012030210b02032840b20028184500041c001a40140070742256100c290020240d503c01d0074821442501d95101412003003150180200142007443c070740d000500300c2071030b000000354110700700b80b21100280000441901848501559045e1039030043c018a000b40445188000a54000c941840305440c4690028000c80b401805070200407040300700d00c035809000486900d040d9031201d0811000804800c80041e400403200303540032a5543d0001480a03010102e9950320100e64401011030040380c1207405405d006070028022104c041075104201000d541d00141a965060b16401c0003908441c0309d124100d856946504a0304254503102d80f0001e2142404030240214011139400036001103880d483c02040c0a41d140c09409a403070003041610516607220008121003070b02c070100380c05941c00007000c41d42001d418120105194080d102d03c0090383d140c1e2005e140c1041c10210411024000203015680c000c0034113004000401c48601281 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 797453408 1250 797452158 797452169
    0x906080702030c0d05040f05030a0b2208040801150512070303030c020c091003030219031202030c1605154005030a051213050d0804030302160303061806033306 70
    0x25031b985182000d00c0302d1011140c1e108500c690424a409400b051080568507840742190032410501030700162290b156030118400a8240070011901080000055005103801c0c1407030050188010b42c0e13801080031080307100300100443c0d00000c0c000c10002c0e002e03800020b02c0c2d070070314010f455208205c84080382d407401f000c465030b0126031b00381041002415010700420134445d4000c01c6c84a4440d80a0700c001e040b960602c2d04640085a00100080250951900f034030a801d01150600352128994101155246460b00004100b1001303980810364040003940c03040b101c21204d082544d03003035100c4040c200a01c40502903c03055140c1419000000640078001006841c00c40d86035141c90382a590301c5c458140300010301000c0240f25101e1b2040100c0c4001924800d091001e2030500d04a07030721860101d0180c0a402c142c90360b01103030355400904043c5c00d07030004400d441c080080c1c2c40c40b0004640300c08007650703103a101c041d140c0b07400700f80780c85074415801013058070101d8a0500491070008803c11007040786d1041e80035 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 797454658 1250 797453408 797453417
    0x120a030c020f2e02010c0c1203090b0a02120109020301050d03030e0f24091207080d110309010902040509150106080403170106030506101d011d060a0201140f070906080702030c0d 78
    0x411411403960b03100f083c6202032440208010568080d01500680088202070202102011903c045910a4100005c1d2990015800c0e03094100300141001941084400300381c0501ca4a00109980c14a8800c4d03904894005090140b03502c1c080e1010360040840150882d114003a0300440c480c141010020713610604015510444e420241a4680e03503d18406003810085030440d40c0c1301c1200b181307507100703031040f054008071159038810715801c0500003440010b082801081c4044200140b240065011081a078002d40301400b1568034608860340354140340744200d1018201340018030a2511441100398064402c4c1402e10003019226400794041100342d0015002945800070000c00d405c4c0440050203014850074146e045c5402e011401806004c14909030b4100414200000c008144081e9000103c960107440940d80e81c0c00c02400901801c02c206147c407422002c0000708a5070100d61030042d1048820f41c4d924410a410304200b00d4405401404040c111301c0141b02c000000d0364140214401c01c10f191300c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 797455908 1250 797454658 797454709
    0x3052703010504210c02010903080a05130612060b13120510020304050a0c05060924071a060307060815040203041a070e09060a0b03060f0402040e090709050105120a030c020f 76
    0x3c44801000321300c4491010004003403012001030341c00c40850000e4941c40100c46444181031201140c80c1c0c0500f000703001d00c0c2e2040190025920b60420103402054030034440502c14a07407610301c04e240c9c40c850409090070700b8803421300c1004800c10414907128200c0c0300b542034580b0303009103440301c00913030b0070035a02030781c09401804c103944c01c00160381080c1c8004c060548903039062402040004200d0700c44111078405841c0d02c0c0a100080411260486122560244031607480f00000203004030400d2048400074002c1c07050301d10100e40580500c068920132a50070010010007a460b00a00010b9000500704030303400b203002c080c502030701002c08031b45611403d413076680c3c00d540d00281810040180400382c4080d008d540d048500b449800d848a08603940810306640402c1100d100c8404240240b24a40c480b00c15401c0c4030303040c01480b46010410000700d550001050146980700c80030007508444100701003185a004079016000030780039000c407014041c0018010482c41c8075140201d80b41103410700e44c00c03c09450004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 797457158 1250 797455908 797455943
    0x7150b03060c0c15070804030804050f03130305011401121101021608030a0e1c060905071a030f0a060509130204060b0a050702130c271a0901170403052703010504 71
    0x4103d2130806229001001414030f020080e00325034010b800541040000400078061000410802c01c1c82070710f802c1203d545828808001254120a00007101e0650800280d443e0355221800307024141c2d024400d03c5a1200603940e1035030258100c411065040d030103071000321545000e101440030003c051002c040d50b0f6801042c40d009182c8001400d10600c40d170b0900c000708180784160445888034075405403000860f1012820200d01c8d10035998030040400850341080211900ba440166010b441c1115000c000c98880110003000d4402c01d000310354021010100003182c4640c03189440841e0b81c00900005001741e280c0341c4911440d40202560408180001049030450030642101da0054032001410400c40903500001007a0740c1960901051006203031400c440039030100840c5800030620f480486402c8120040d06006a070010410640461322000e204a044020710391010b220300d13419564549000a581512100e0405c08140c03c0d41c03401442080340135a440900c10980900d0003503e010000d1003218 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 797458408 1250 797457158 797457163
    0x7050d0f030e04050c090d150507110601080a030507110126070909020c030a0807110303100515031e15030313090e0d02070e060f041b091a07150b03060c0c 68
    0x405000f4019460801080b40c00444c2c40250742518004a03400705148400307060000c00403000321248407c0710300c1e14042c001102d420020031034000c0c1000054589036a45c501540303407180340001000e00851000c2040c42c0004d030405803644049001410010000d00e00103041400d40616040301500100e1150140001690803601078401040c00c094250303d01244071440640301c0c0503070381100040c00100e0010615081c02144011212080d030b50840f42c603898641c04007a690381182c032031140903d50f104100f09400c0b801a007240e101d600088020300b03c004082d5020200701c0382c01000050100e0301e54486e110147d400781f0090940c400c004a1a00e00c06040c8188001100c000015800f170550001172807559660f008942642100c0f140c41410116644800c086503030340034604e000b16845450071440303040008404407000040e07a5191354507424941c9a0000c610b07054900320707038081e0340d00302440080001000885190843c6000d95404501c2c100f4110210789800e4003901c603001c02c400f01040c0c400503400c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 797459658 1250 797458408 797458427
    0x51e09011d010e030405040905070e0405010b0901060314160207120317010807060c03230403080a0e0406080c2116030302010f050c1c1401140f0306150904030207050d0f03 75
    0xc60008000f11800708514a99a205520a050041791908480401e112062001c1d40c020301d07108941c913103d4589890700500070f010001d40c4070700c103080540000c80c007c0e12a2250031091070b110341e0130300c07580d4440b00302c2c050452100c03072030031400c44c4603140011440107403240340c4005072480b0b510380205104207080507c00e41d41050708885616400b0340c1c02001041c0d44400406901034260a19000c0400300310210946a442032072420f45000001400104000c100e800900c0c00c45919503d91a84840c1c24082005071026842400420380c862028480c0314034140c445013000c2c01180030300c81c003095158144503051085c0ea49940d507290000b0130b010818190203000782166001550410001e0307160440804900780111100000c110b060080742189030040395100043c03d58990380c000c034a942c0d41d90441c4040c549004035690082003000780d20150b509002031072074014842c8281007000c054500f0140041640e00074415002c500c2004000101a2545816801168090520045201401d08001c0c0c0352141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 797460908 1250 797459658 797459711
    0x2150c010b0916050c0f07030c0329010b0a0201020c010c0f1202030709140415090b0411040b0a1803140c21060105060f041d160c0b060103051e0901 65
    0x651400f080000908040710384814001400d090341c44400002d01c0c2c1c2d2800c240e14030014120300c2808004414000c4410004d804c0b241714a215000d0030b4510508901a50b0001c080e0a06090b24030005228502a26001c0c04017001144001403e00c07041d9501103083d00c26446803030000c1006658043e50041d03002640403900c7c04442015072660505400007805400c043c0b1515082000003203c0e161a699035800c0441030340c0b800200c23a402c0340d44910440c030043c10100c28441c801d601d01201d14103800140c00689080341d0b192400203083c5192041c1c00d0b11503082c070001941e0921041100840040e060481c07103404502040002c00b00da0701400d09100b103078a44004040b0394045100c44100c040c1d100001c120b41968000c0d500b0b6606c80e107441041c14441c0c0166001480c0001e144070041d054600c3c10208a0f210b01402c107481800c12003440010784021030001070290000e12a0800903600b9400398100c10b40000301051881528019204418a036080a0f02c510b0850794403201844100c280c0261a562000c2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 797462158 1250 797460908 797460919
    0x2315091e06030f100507052b1803090b0d0e030a0201060801050a06150f030f0c0e210a1e020a0618150203070f14060112061b0c080705010902150c010b 66
    0x28040403441303503500e107200715201c00181c85000240c0141d2041003030381e021215105448181682c003162900400003032024040c01700c0e1401111944c01d405000d0010007254040e1200399041b801c091000c203107648a1040d1a80081d00c405c0307410142c3c0c0c01040200042905540001541c1c0d091001190a603440604022101805e2000c1405040911703104c1c04100581410010500c505550054001c2c01888400700c81481c038140d10441980c1d04480c0700d0030900d60071034410294286c0b01c0a14254400c035840042140d51060850070300003640003032150075000c1d000348c41a1044003240c1c00a58040a0360f00410001403102d201c500c0504154078014000e02907031100060050100c61000f0350741c1c021010040c1851085c030f602a000e0102030100c07820000c014005031030303156844040400d1610140c0c1d2080350b00520b0715145010741050100c800c5c0f00b0480b03036030710103800710303180d4030703042115000f03030a069415540c0c50041c00e0041e0b8540d680310501c501d402c2a115101c440c0c0440050071200080c0090b406603 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 797463408 1250 797462158 797462173
    0x1e05060105220e0109060513020a08060708010608070909020301090614090115030b1305070216060206070c020111010f09032601030f0602160b07030501090b042315091e0603 76
    0x10303038442c1c4042a5042d008440000c9081c00c1e2003100313000d4580e07104090850751030002400301c6050b40d80403d42c0514000e840010884c1d0b40e41169aa82d54801c507070640c0050007140040c008d291144031382e280c01c9000c62404ca1200d648450840c0100da00a03400300101586d12481000803800c044c0c902d150300740b41141c070080c1d15071400e0500c10314151100070010426654841c80d43c025521071010700c4810801c5402002180b070290f40c081c1da1100c8102d40f5200401010800042c49440003400d248035031069601c8102e1400a9801552103081480c26403041e5501c1d0f8140a907024028412552128040d0345c0d400031441d075003000100b0903142070104500415814005101040e500c001e049603490780100c00680d5100000700c1c070344240d00303a11b100400c0010a00140f100695064201605a515141080046540c2e44080101301c6000d040d61110803410b60141d40824041411410ba102140305800c105440810300055840c45040390680340d02904031180300c0001e6210051954031070742c142c000742000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 797464658 1250 797463408 797463439
    0x50601030b011e181502060c0a02073b0103120216030803040512161a070c14030f1611010f12020f0403060c05030f090613031b1e05060105 61
    0x103c000e1404001c80c00d4800e050003000041c0718486031604144905203400301e56494581c0074076401108a003000043c0b103010040f0b80242c0310344003100c0c6035602e02d40082007075501d8443c03415410ba00d081c503440100c42501e40e04008003984c0002844503041d000050389129810751400d00d815a224540304011540030001104908200c8412201a207804c40e25260f22030380c2d0b038030b84a03150600300c3c040c10b101d030b4002007404030080920780010040d1901c100c0481040c1900500e40d65060b01c8112840300014801801480201d07066496800003003032100241c0f4545103810303001c00660b90100d8030098603540100002c60038030408210f02c094080091901c00c041800d81e900003020601c1250564103c03607030003e00084864424802c440045038015410301c0324000030200685960400c5610300840043c4500042c44090041011486800b040100321800c5841d84c408682100f0b20071000180449140c0648001c11010283c100164031116a588000d4105141031400c0103410fa0000b40581d411000b00f130013 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 797465908 1250 797464658 797464667
    0x20c011101051b0f070c030b0f0109091208130c260102090901051002010204050a0e01030605070c2003010b030303040b0103120914040519050901020a030b0f130c022e050601030b01 79
    0xd900b01c1d0122581320300c400c8900f1180c0b40b00b0068001c110041028000080001c40c5001e940301c0c104034045e0401c1d503a41d849004082e2920b48000412104001040c20384072070190100c1034004280d9044000304003030994901d6010011608090705900c0502c070110140c000b1003520314850707002a0000e40c28905c0000200c1d402e1041130188902c15a5200c2d28001128401d5041d10001e24000340030030460f40c3d844e4030b61962110203020070b0f911681007100040b401e5000707103803001000e580203030520180c044942d14010140306240000d50b05548070058828541d50803c003440c0114000c0c00fa403141ca5155143c140c0c4462110a100000d221030b41c1c1c400c1003816562400710b501554242d030b000c1140e070780b5245801000d41071058588540b91411040c000580415400f0f80a200301c076442c1001117101407801c0003007107600850510740c409115400066008035580007404500c40d0342c011143c00c00c0b01801410a00341d100300c100341c94401072010825421805000b00d54000f5000e0130104294818400002c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 797467158 1250 797465908 797465941
    0x120c050919030b1503160e06010906050a080f1929031204090f020f0703031a0a0f090c020a02030a0b092119020c04020d090501060f0e0a051510020c01110105 69
    0x125000740a07440000e136071024480b012420a0a21000031410303100d020000c5101d9065840c41d0003e08a00b07800309440d4001c1d011181c4101d039644580d038082da50f481d00586410001841d10380003041841d0046610306990003a02040c545c81c0d18600d03400300003011302155100070b407001c0d81e204e9400b2640a40b0948054012141582e00004010400000480559001c0e1084441c040030380d401c0080c20800341503240d072100700b44501d164241850082c0400422034621121b0085920040400d1002c010300d8585900c000d1500301c041c01a26640d4109800103800c0c508114415600044010100480c500d02070285152403280c4d451011b10182981101e07015a000d007000c03000004503544030001d02d4134000c20220010100040003555582001d81500001d014802421036156003045008500540781800010503680d41d080744014a580704441c1d0320141102410302d4041e26803080c41c4900d981c40300201041c44c80c0117900108651080880010404c4411103a0003859915080c2800906d03a078650031704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 797468408 1250 797467158 797467171
    0xb040f140f06013507050f0a0309140a0b0103140604151d030a0906020705030c030a020d0305090402030c2512300e070609080d0807120c050919030b 65
    0x55000e40d80d010068030b1000c0801c46100141c02010045131048a070314084c2400c024080101188549601c8003d45050055041002c41079600344040d074480391080d4015078440d8080d00c0031001c080007041c4a0303814001e002c14140e40b14100d250040c4140617480a60803c00c42c3c0407030040c2181d24142e162803541c1030041851301c0215490f00f811200c540b404c4000c07502014008000d0320303940c00342100e001d40403803128440c40004d400394100000d410310300070658940c00307800a000b80c08003801e40c0d820840d06a4480c0411014044188454001612103101641c4503400703da1039956200c00130400288070812a01e0010702d5095012517610001d1403100648554070103505003c24258401c00d91440a9001091101091960200f81c8000f00f41160482c5040f000d100040c1c680040d200c001c1240c03907070388a014440030703640b2020a0121a62280301c05907400001842d269040c5035004c00c81105841391461b0fa10300080002c80c0303404803490300b109050100d07004941d501441d14a550f407000f054001c010f080c0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 797469658 1250 797468408 797468431
    0x60e040203150907020609150c0901052d0d061211060a021f090204060509090703080d0f020c0f0709140f06181323060a05100801060303030b040f14 65
    0x1080b04196450045400d4520041100d83c0d00c2c5400c8500a580e08030443d916074482c412650464020151040c806004111002041c0d00c0c090b000001034510742e0010002c52120414110019208540321501900c1d1403018612240d940c1d0212030030900344c03170b40354024980381d2140c5040c21001403484034402d66200c1040c0e40050b101c03140101300381c5c20800103103031480c5080652441301101c00c4c01035100b008014403c0ba000c2290545460920040940032501ea40d500d9000503070074400b00c0d60702030107002c081400c0000030807502d01017000001640c1082e106000305900050808401d0b5506011410240c029400c04004080071640781e040444000350004005d811040c011444586801d041000010305c4980c4a6280d803e180726510300c0c4400703100c426100c00301403024015510344c41402d028070050b06000106515150402154020a009040c0c0c000c0080d540d080001c2115080c017401000f5070081d04c00203010483c0c001403200b40c5000626843c00c0034500719440c0c103089800c1c00d1403078020a42261 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 797470908 1250 797469658 797469661
    0xb0a0e060d0606090305010f0203010303052502120102070303061502030a080901090c0b13050d0f03261503011a090714120c04082b0e01140a03150807060e040203 71
    0x1003416031003001c60301a040d42c00e0040109009400c00758900c1100e01c150001c1114820008100c4100d000a0100900044081002501119644c81c1c100c009404801094000703140740e41c0003230424014a000020641d401140003418141c040c451000140841626500d0141546400039103034400e40c500b18050016020214039461800d6100305402640b007805076a030f1540300c10091031150000303071000300007403007524000c55142803501c0080f29142d8888401c44141e0955034094500e220030482005c031007440f030b804c02c038034240d9003610550048241510350859010880203140c2581d440a0221030900f0703200b101170b002611500050b035881001890303c0403001a9800b24a15140304900540c042800c4c100248010403c80100900455803424201d03840d45070204400c0c1c1010556000a10803e1003040c07603401c209010724683c0c01c10306414034042c80c118a0490002c5041d820485814000954840001000e0900112440e02400291000780700302441c0800c002c105003845824180030315000700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 797472158 1250 797470908 797470937
    0x907030221030f0706060f0b0f03010b21040606080c0105030402030303071b06020a030212070c0c0501050c010221010614040e01120f0605040f030e0409030c110307030c0e01080d05040b0a 82
    0x340c0c1c1c18000150165a0b1301d43d02810140c019040d940244402c4481d80c100c0050380d80f0200301212400c41200088c5401c603840c1890400c5590000740d1888400b91107101c1e01d1481541c3c100407030344503d00c41c110015905051480d050710341200040720304d06000d410404d010169500000340c0340e1201c41c0c0d1804014081044050020046404000030711450001c285400c400350940c000c1d040122459405414036a9025411a00380c0c0d0810000380c44505806410b21403544224024400c3c0e01e00003001500c0d24005c0721416807090b10011140c0b800c141b0b62001030151396480a004503540c100204041e0406080c10f0303643c0313009a018841c0007104140340001c0700070048a45510301416030444420000c92400342024040d1070110042240018100c81144500d40341901c500c006990f050b42e15880d0600d1240c1e604c80e5101c51410249525100d501d000100281d81c415112002d80782c0116450900d500d01051145000303020401c034424084d0030b000500c0141001800d8512000ba245840d589008024 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 797473408 1250 797472158 797472163
    0x1205100e06060703020703080a020109030e01090308070b07030b060c0109150c050a0c05070b030412030c0f02151b04031a06010e0d02311a040504032c0301050a140907030221 76
    0x7e84c40280f0b0315401190101c64150194810310016010b070f02d8441400130407030011602201540401405000144803000104000303e5685602c00d00e1030500040540c07045001411581003400c00c54080e0b07450301a42410043c00800d05100d113000c20707009101e0f004103418003418038000c0401c0311082241307084500b42802300030814000142440c651042d56070030141130402c00c0210038105c0c100440c3c103142410710010b00c114200b4403402242d501500d02003070110986905400050076560417008400b0750400031440c5c0b9401000150705c07946082440c80c1409040d0580000c0003003146050012a9201c201d05450720022004103640c1200c00e0b4851380790003c110003480c0031640325414401101c6080045e6000c440e8003500482d082d881c2e203500b1140700c04042005440084400500007004c1c51098000141c210551101c5000a2075000c0c40840b02c401c0402d007103030400c56900c3d80c04e944426a45940505519041d508800400301a103055810343c0c01044100606489000c0c0507030040c0d4803c400d11005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 797474658 1250 797473408 797473423
    0x170103031b171201090e060c0d02280908061008060106080a02070b0720120909070c0f0c140315060907020102071a06090705161e020d031205100e0606070302 69
    0x141115140c5404000e180f64003c400240114000145800d1001a02c8a0006100c030310410b10741d0384813490140c0ca403803030714080d4109803081e410744642a6a92000c00b0a0042c7c94119000300b03070b031405c0056141c00c01d8145810f40140084601401d031003001e01082c2ca002c40d00a064803080c1c00c04040310703240d22840030000c2c450348901409035000c1200740010540d100000311030101c20007441601d10084011101d4030307035031004071840c400c250400c0500f10600f09a221254400054100b00c0404000f40d11542a04c2d08450800c81c0c0307c00440f501400140c60800b800b0803401c0068004180c0584a100c0d03890300c401000c1c010714411200e280c0016080783c400d404444d031b038580c408031100d900b0b1018450b040c1e000005880b10b81c0b20711310180000e403009104505540481c4400c0d03200c03822015444d150a50f81405c5404c16100451100c8400e0015840b0440300ea070700a442076940c414000c60141c406021600c01400500a00e007d082c000c0281100b0340c110160016003c4420310303a00d6a02d072078240d250542 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 797475908 1250 797474658 797474693
    0x3070b030f0609091c140d0b030c01170609270304060201060f1226120105042a0f0309120f0906030c090501050c010b2d190b1b0f030406170103031b 65
    0x1030000c1d1f4244507001580182d81c17061000d0f004c0764120503582c0c2c015120b040305140700452101100e00003485500c0e00d400d59030340140030700c81070300482c0c10302188150320b402d14101c000c01c0c660f0002078104003c44d42441120000d140000c0110134090074403240b41040382c4000c1028049a54008a01300c0d000020341c03926505c00400101d1303541c0d40360303681c0c09010904024420b85120b2450b00701401080d500c240c19121000c418400f4082c006100c0f0310701074940017008817840d41015a10350380d143c000340040c42003001001c80782d12200d1429071003000c0100752540c4d0327404c500105814034021008940d0805121000d036803090902d90b4841884d96070a0b40145120f458580d409054441c8104c00002500300b80e82c1049078118041d101050031009100d451101100302c002d5203030083d08200940844280a856440140f1025051004544c0c0e1071510f04000c1042d511380b20b810004007000526004104443e644202103211203441d0302d5500c01601c00c4082d54020b00c9000c40103401041086940b0b61030348500f02 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 797477158 1250 797475908 797475947
    0x30c03010e060a081f3902010e10050412090602030d0207030314070503041403040e0118090204090b18072d12111806130b0f03070b030f0609091c 64
    0x42980070205444102d21031742d9882c2514010900d26005011341d00070110180b1141414940e03041c0066106a010920034400c0071035503140c1030030020341000d224081c40810442c401140d241040e060101c03d16210018031004d00c070010408014003a0044183c54071848606001606c508440c01c05801400041d00c1591000083c01c041200940d000702c091401640a079060f2003007401c11850f0140d49100d80d010341582c01499200412a103001020340c1c2c00c04210f03402011919007503560206066600200301140d060416804018617010303e400340030007a8031140024180c1914240c8110442c5400a8040801d1042a2102405484c4902103a002401240d0313200384070212504010f40207000030552315105100700741000001d603030141c4000c0c1c002d00380102800e100c0010310b0100c400400128843c550003803404020010b0030ba03400d100e03585c01400d8020301070f0f0313a9103400b010512032034034024030481c0309030b4050003400284500041c064074050750344070150049084101e001d841200c1030811103031506 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 797478408 1250 797477158 797477173
    0x412080c0c1005090606030a08040b030601090810090b06010207060e0613031502071a370608011508011b0f1e0c0302060a050121020f030124050105030c03010e060a08 73
    0x180c0355601c228401c0c1084c3e000d4948075200e0208041d100c8a401d20054040d003c00d02081c00244c070704c1c0d002503801400c141010034402d2f6840e402c4a0800d2046a101c1c0f008544e2892140180101040340683c04802440500b020038240b0030b020300600344220004c1e01541010844550032000c000c0a88040c3d6005042802520b0040c40b5290195000321011110584441201007800c0d8020010500403544654881450100c40104040e40010307210418070b100d40050003c40741800511401c4040c2c80e00d0400440c40c1d01103048209070b40015548602040d82c942529100c030500301e00004141e021061070100c0c200068145c084030002e500a145240080e00354841c00f10b5250400b00280b030b514402d800b9100582d403000710460448000340304807450010010803601c0c400079800300b10000c0c00e01c0108100030500450001c41e01312500f00d9031807190342c032201202400c8c406035442c1c203100800003482c1151451502040107017442c081841503500558800e804128140d4580c0c02d441c0c007910002080303c0e400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 797479658 1250 797478408 797478433
    0x10120f02031c02101e0b041e0b1c08040501050d0e060117010e1204090c0504030b0403110f01050402010e062104030918060f03030f270501170412080c0c 67
    0x24196541c004058404e03014409071010340341c00399001310582c1e0076003107104c441d00381d0701c0d800a081a480e82d11b41c4240c0ea00007143c00b90506940d11059100b803650000340f002040f009000305181d00e00e0704068001346164242c0006982d2004803825500203182c155104d480407080349010b807280c1c403041c4e545070203240008610010415210f100e040900303c02400500c4500540d88c1d15a40252a8922202c2d420002804014002d030044134803e2410700e0f11a01c4c0a55035240c050100f0130a0390120001880c0b0b4083ca088d1840c01c021034640c00302031a008000318245640040c2100c568216002c0c0913030804160000003684142c1c445041d048100640980d03480c1524000b40b50070403502072030a54010089440321129401d200e03410035900c207602030103040c60454a09940c18a0300b080050100107148d080401201800b00c07502c801407000300c02019082c2d08000c00501100c00f4424804100c4803e1402c020100e4000c04c441495442c460421900c0c80e11b80001a9109209412886480b40b0400400021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 797480908 1250 797479658 797479693
    0x109080d21020702010f0e01110f030307112e0b0301020d0e0601140127081209100f080a1a1206010302150306061806160501140f10120f0203 62
    0x264011440c011070030340030024441c004a0241c000701a00044407901c1b40d0b006140140181d10b001a81410030340c2d20150841445031034201e8041c40d60b803280d0408001c0c44140381c0c000000c8001d0343c0c240f001030306001d864200c1c0c5109851108090309242c94442c00075100758080e652018000d2000940255610354007044010040c0409203008049072003001c0c000030303800e0303c0c0303021f20070310290141c2d520440a02e04503050940d5400c1c50b00350751807054600e1000980c801c1c08104800400c5007260405884214500410018a00e454150403c0c08006a05030800f0f6500030b034101e030f000300e8445c1c0028142e14102440413031f1492542020f13420035500e4140d1703400303080000350850481e031003110480004c408500259038240019500903070451414448000c41c50451001c00801c654050107041c1013038021a4241c0d8440d480b541c09442c0c6035900c020900ca4000700480a59201d9441e6201c2c2c0520b051000518044980911508540c181000d000408100c40141e00700c0016800404481c100c0a54801c0c00780b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 797482014 1106 797480908 797480927
    0x10509090a03120f0c090e0c120402190308160b010f0b09100e13060e06010c080406030b0a090212070f0c0302061501020a050106060e0f0414150109080d 67
    0x851306001441a81c00301c070300c0740c4c1d54284128036041001d44114006856800402410444405c10170003c1051940081d4140e848188000d03103210305502036081500f000701446070010b00014083c3c2c900c504070140500411460807140d0765500040741d800745520440e8420b58003070100c00703c140350001d50f2401c506c80d1803c05400725200340340000c015203100310a14030322079503808062106148450103590301407000c1c200420442c02c2070703d40c100203008910403032042580740d00a0500d01d4848844000092050038020754a4100788020118410000c860640004000300382e598000d91141e1707035450b99580c2503006815251981c4d880d1202240c02c24100c1e038158420780d511900014024824080201644d83e1204043c0c104407040054410458000340d02c194100080c203179030b08644494041d00031290741c07111002c000c004c00058980c00c500d9440f10341107003e1a90388055058000325901c = true := by decide +kernel

theorem cover : BRFrame.Cov 797302158 797482014 := by
  have h0 := BRFrame.cov_init 797302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 797302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 797302158 ≤ n) (h2 : n < 797482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
