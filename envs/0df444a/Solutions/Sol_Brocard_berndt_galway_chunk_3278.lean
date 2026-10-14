-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3278
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:11:28.545065+00:00
-- url     : https://prove2.me/submissions/f8ab37fe-a8d9-4d55-bfff-507e4f01950c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 589388489 ≤ n < 589568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 589389739 1250 589388489 589388497
    0x60405070e2b0c031a011e141309030509030c040506030703030f0c0c0602060a1409120f07050601080c0405100b030106050715051609060507261b070302030c06 70
    0x1020300200300009084880031600701c0c2420300750768000c040c500380d000868580c000c3c0d00b0145000ba98641240b90304c0041c2c2c03401e0200140e11505030b4a641e45200c1481007244100b001c11141c240c200b00d12201800300c0081d40003602d0008040b4003d1030880d51008164019000d0003a2540403020f459000c0030f110140819180121584c07641074029600600c0024082c20300c00d11803080529145110307403246e56601d200590660000402759002108224000006000e00c180100102c1c480704110306007244403d9031170703108061403000401c012a040800792860300079541c40c01c1c0c00c00201e4856507516a8229110040c540d40703280030300c2c14a00040d0300206858041d030100d44151507002d02d1a8a400e42c21591500902d80849800f90401004080c0b01581d005140c02420091044818401c501e000541290000d521410a109080c0842c20100b0002c2030400300c518050320301c000c0550315000c104111481421038821a6002e00d88450000d54000280441540c0c07003078040b20401030300b0100308030071809 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 589390989 1250 589389739 589389767
    0x10608210409020c010b09041b15051204030e040f09140c10050322050309030d0f0906031e09140f01060506160302070f0603020c011b1b080d09080306040507 69
    0x14200700801c4804a00d500401c45840b83e08000100320a042d00083c176102c40c1964191502c03402c4d01c140c40c40300300e02d00d01307940f00805031443c0e0601007529a100180013409104d48001c030708003801380002c080c18081c0507001044e0070010800c0240c41e10907080f03c801000381e00e0b420344501c040f020740868000300004504d0300b0300c1c4005080c0c0380c2403e03240e0404c9a160748010301d0654a4800700708450a80031005000c0000a440b590140d510341702c551080c0f51070004c3c08480e4000300b01880640000080c0c00c613403088142c031041d1601040161203a0107060109440407100070081d8a041c603002e045c40315000182c9001d00807001034400e84c0c00103064880c2601c03000c0c000c031755101404010365074a9802400d031034034440d4421700581c1d66140d959140204401d00c1a8080c001180c0c0000e228981d0410a100b12412a10b40c00044094011070460090107004003001c0740881d03200c034103941c030140174070031050b1522409543c1c414800030256107840d03003d503042680e64500450402c4003098281c1e01564030800c50603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 589392239 1250 589390989 589391053
    0xd05060a032f0603070309060f0b0a060507030c0c15090b0702180405010f0608100c1b0f0812090a03171315020f0d061a04030f150209060a02010608 65
    0x4440071440000d0718070594492203100300700d200c80b115940c035a440a180304040326100094540103500301070081d2580e5118142c0998a8008007111075503610030b203401910800c0c0b90282c1c8501c000d04e8161081d03240d109001d04601009200020860f01d1101d24240b40600c55560880050b41c40039802c0540c051014001d43c00741d41a01945c04521000c404070781e0190003480042640380309000c500003200d0850b04418034507001034030a00048007460240032902006890010308810244421000d504013400006108070040b66045003440002d030b00b0798914011103d040020342c14681c031281e607506080350f000c9000c074194044240584c0c1d100e06205200d070440300d40c903242010255448801e45800e152150500c1a401d119002c17107185880068140e00d0424040040e120f42810400c1c0040481420000b40800c0104800c0c80000c2503016406002680704c122044040200628000640105216240c005d48082042c880e62a8150010401c91721084162051840303440d42d00b0003d054511810740d03401d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 589393489 1250 589392239 589392263
    0x50114030919080910080103020127030b0406140903040503010c090501020307020f060c01020403084f12032601050a0b0304021302040b030f01080a11091015050d05060a03 75
    0x2d510010304001149101c0c082092410560f00001035110f0303440c0014400241542c1e0040c4110758001000145903404480500024021821910300c001d41500004080c000076501003000c110543e08401d41080030340d03074135001c1840c042584070350f240c010703108281c480e608081c844d990b01c2c2e00981e0880309641040e405076241c0f881e01d800380300c5110003c8110075007114007040507208050007072000d8400756210300302440e900c0c00c0001d080e000c01000150748130084030f1094941d2082400d201c50032084507803016043d1031901c0c0002007030220384e544c1d5484052604c00d68004030b0304040d4010461100c501c01042c10f5010009000c1c0c034400110400d0241640065100e20284000880b560107194000c0c801451100384103030b010407003c00da80281c0d001204c0801e011003071060b881034940c1a0360251489030014162189a41ca40103601aa451a402c1c011804007022a102d0070f17060716000d01606045808000c80c030fa446000070700552040d9203420081c0e10b4203010071a030b481c004083c00105c940040e034a1800d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 589394739 1250 589393489 589393513
    0x408071109010f15020703050303070c170307091211030307060f0f09151d1c1704020607240c020706021b1e010c1203020d27080a1b05070501140309 65
    0x428030740314800313015885241070010004608100652142c403140d50b1b9070b0859503072481c245000c0e50404540c0240c1a105000b080005a40251680c0c1200d44075030f04170200600303c0c00c000301e1040d0030080303140c0c050100007041c8082c4160340c1c01c00108100300c403404201481420702940101c0b08600303001008281d201c00d070b03071000010030b800890030b41a0207070303514a41030102c41045190013070204540c090071122103201d00915410102c0107400ea0350a0901180f64949640050300c0b86c440c2c0b0303000410248500d8541028129008401d88609100e20802c109600c05440007a664800ba03100f90f00061003080b41d5685003201c0c0030308400e05100090000d0002602c0400d8003600b8a890789007080c10002070407100d5010030940e02d01c021504405847c0169038035100300d000003e9481598481042400c032040000b07010075130129494a0031703080040d8035107510401c3c07002c882e101031091804480280c135a2200c0d06110001c40c0a80459000340c880c03e00c04548010a0038081c04202d4440d07040341c0100503062a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 589395989 1250 589394739 589394759
    0x80112020f0603181b21030304061e0203070e03010608070e19140709030b07080108031804060b04080c09070f021c0203191e03060b040612020d050408071109010f 71
    0x10704042d42c007007601c2e03c2410a07031007507140c008181d20980c100301171104030b1162400c1c04d000c102071164860400d010b0907075500b10144e42c5ca20000e440117121a41c1c0e14100f448000e01c16155441101c1044415540c03070501090052080909000840c4603502c0c2030400a110140000d843c0105e5070b22800c0004070750f039440c20580107141400c82782040e01c2e071281020340d440070740c402000b8070408050300c0303d206680c107604222011003401000070041c80b0f040401440411000800d8602200c4207a040444141f4014041806486140e1001d08100004500807900a5020801e29190307001074503042d01c1641d45820490f44d01008407004000741c0c00c0240603552890354075400768403181050049900d0107280ca104c0c04500340c1400604070001c1c2200c19451944103144075070501c00d075a603150a21400f81000a410b41c1407156105580030b110240022094098103034056440d0141d070b4a4042140d440c00e400c02d06216403103060308407950162a030605040c0d16181e4680c605898540e03000f0720b2864100320b4005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 589397239 1250 589395989 589395991
    0xc0a0303030f0219050c07120807060510080106180506040207080405130612140c010c02090106050c010e0f0606030709050c03010302062a16091a0907050f0a02060106080112020f0603 80
    0x81403050f020000c2a4190030483d030f0a1041c240580d07112565100c0c240d501c0c07400d01c21550080340003840e20401c0b030400328403440c2c186c85104ea000383c6e0001d1980c841c2e0101007881407060340308070115400c080e40002c17042c010f41d40e811362071070718100e003440301e580c400b410082244104030004003980300501080c80741d420840130000c085c08c8000c00005072103440341c00a03ea0b10014071811504c40648560359544036006000c2070741c000c3c00a0800003800c0f000759001507190300c814020b4404100020030401c0c1c114009400a02e06a184207054400000e50321349095200c3c042168054000e10640000151000f510704c10740f1b200300210a00f50b802c503401d40d400c0003502d502080801c0d901c2446005075140c00d800c1c44a004801110000082058814005120001c00c090380e02500c005807078618100d5416840141000c040b281c1225014003507600c001e801d403140c2c01100480b40c1855804544580c05c1030300040c04a050310016203500c90f0310703a070350260041140c1d00b4100c02900841c590400a0150800c1c1c0091 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 589398489 1250 589397239 589397261
    0x903030304031b06180c050603040b0406020d20040f0602061308090d080d0c03061d1602160605030603100207080a0806010915050702150307020d0c06110f0c010b030c0a030303 77
    0x1e01c1c010300741615048243c40c0403505d080c9441c00d0210340d000401410541d00001890309070f5504d030561030582c4441c8420000103002030056600066600500310040d4003100398202100c100c4c024200103a600c107082c2d0b4000f405001e400001280c8049078040c0005001c1344102c0c0a000c07401d000356a9961001302540211489541000ca1074003280d00181540000d8240d1606c408800241c203015000014140c0705a6808040c000500c8102e0304003080454005aa20410403081c03001c95144c030302406c901d48081c2100792044111787e01e00115030780d0b41c84401903000d80001c40071512918110300b04101203104480c401003031050104041c41030503005101065100005040203944555034107080f5050082641c004400a60001200c00841c980485040c600c0c9003a000d1550452900c03109c007941d240c00300080301050000f0041c0e41c1c81003180c5031700100d441121007003909440321541c40396510581c010345910703002c6501300380d0b014046040014a8450030303e0006d104a02007403441c3c4081d0020550f0542c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 589399739 1250 589398489 589398527
    0xe060a20030114030714010c0b0405152401020d051c0608100608010f0902061b0c0402130e06090403020c010c05010b1903031407170a030b18100b090303030403 70
    0x20359000111000146008050600c008021105208101410a403c0b034103d1491440c0c0210100182d987c040c01010215a2003901d07d40c01ea2514181286404011240c184544030040708008417180f00c003019014a4019444048020b00c03d24010398072012201c110000082d014002d01e5240b9a035003581c0d40c5002034130b280020300180c44601d02030601800a100c1301c410394540504000003802441002c456000a81c8200b2003142d09a002aaa03440385118641c4090b00a0000c1d9800107802e11010030040c1b001032045585503941c3c1032002400801307100716004c102244001420504040f0110751107142e055010740800303242030006549200314244296030566a84d261160203480b44c3e0900040d110714500c0a401c01803446c03800030f00001ea00d980d01001c40400303000c3c01001610010517082e8007812400c0190b1a5500c1c40012001005201621a800a02c0080704404041d4030f95945000e5200d10704144050f40e03c0b44445011032081d001c0b000d4140d0310420001e4040b074031a81411840d0904c0d118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 589400989 1250 589399739 589399781
    0x40819020d053403080a030c050d09050a030809011a19030203010e1c0215040f0609300906092105100218010807020d0810051002010b090106030e060a 66
    0x40b80391a00501010303070f0ba100c080e41c4100c1880408540e0801d400700b007445440403511030955a174405140a105240b006054445040000582c001c5d4107489000c110450b0401401015007405030703407061440419030119060303002168030080180244114402103521103030700c0b4000c0700103100c90b00c0703140d40b00840302107005240440140e8080c0030b040b00609242004081506003078054030154036010503184107561081007020207064141492950040c0c0206070340e0a14415401d01d4005010069401460a08036403042c03001c00d50300f0641103050114a90800d138130603075000800d440710380c8180107100c0483d0590f10708100701200e2406140301e0070b05103145080113103010364480b49042c41d00c60b00701404940100d10140e102c240c000706140b91003000d00e000805400c03c001c0103912000d0551f01c1d01d041003d2080094081c1209059000062101600303114042d41e011000900a02160b404c01d07106003041c2d1b00019105100b0b02034281a503150350003501403600d4107a20003000380603007100102c02c046114 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 589402239 1250 589400989 589400993
    0x1608150a083307080a0e1011120f060a030f1506060f020d0203041508040f0c230607030e0111100c0504030b0916141c0606030b010b040819020d 63
    0x100c40c02d030344100102030340c004014032a89440c0c0003450728180e544100c0c11280411104a42c020000c50f044040f034a00001d074445001486c50520304d8060010b00040d003010343e84003804040400420505104407d4552036890300c0a43c102c500c2800c1d00d441d030b44000b02607024000326032000d2018150503c5100c0c01e24103038081200300c00c00d4a41d9984100007158420701c588010540510480611102c0c610145190500701035020b88114000702c0190100101040010204140c108a9040458022814911851762484c58054046e150010020b003050340c0c607228803135030034000162009190b054a51100094118004550f5030085003051945441040740403000c10a80748a101032240443e41d0b513070761f11811410039401d4414040c0520780c05030700c03142120038968003a040c1c40b003d40e014404c0c64800c800301d0900203141d600070704040c0140716003100e410700c0c00c1105a900c1003007241e201d0509058039a0361448104424004c41c46490131a0700071100f201c4901c858094940d500780c2c8020401c8420302056 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 589403489 1250 589402239 589402243
    0x40b0d050601050a060c0c140111010f020903070602010204050a030b0601170106020d0e10140d230109060f0f12140105190e010e03090d05010612050c0103051608150a08 74
    0x200800d45641d0801001400203080c5070285201030003403400d25080060035503684000e00c1c0c00740e01c0354503503400020780392110b41ea20036000c05624203140d0b0001d11a2110303c141d110001e5220305000380c801e20130380300001500360040c000d550031a6402460a0802480c1da100d0030368a80e8000c16141c10400740080c2e00d481d940000b90315601a1034190b0080140e0f0b6401003000e8107600d12000031034400d4240c2c0070b01442d01c0761b100e14518030000f244070180b6190a04151648050106100400c1c2591900c545418a281700d41410b41c0c12960a60014400580d07103403643d14815900c0c1c091080ca4851140702070120003030616903803030018441c1a4850074014850004c5003110016140820315804c1d003034003803c40c2c42c03007401030b56164030040008200c6000050710366941c038810400800d0003a44620000d07002c0c07100a503c02e10007800d2602c00801c0b9010f091411546070361b07000c0e650b9408a07240c02c01080c0d005104c41045651811075071a9005c0a8641c0c14403c00c40130940e5100c0341d40b00c80d00150110340c844003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 589404739 1250 589403489 589403509
    0xa0915030509060708061c110307090506030c0405010e07180b0a020d03062102010804020315010b04030308070504050904060f090c0f051509031203130803012309010b0a0e040b 77
    0x11039500044600b0002a01401c140c00035202c4003c0000702e4050009a9440311011114140761000001400c1c5207031030040740301d404041c50719501d4001c0d00703400510200e50303401c414401c7c5011400d8a01d048003913030400c01210420301807000e000903800c0000e062640070b40c4040c00810104002181c40f19900c41402d00c19910000b60302005070002c909001000b5018000c1e81d0181805484d056800f0040d010b007445900003030003000e410800118046402d40d1070900521304d10040c00c4c030b00c444841d07840f441410485d034000e00c41200000d06001c00550f0451007082a1400d4440080805000d41c41c0d9440340b074050040c0c06414011180e90300401000a1403500f010002403007046508070307595140c14100f11021013100400c2403030004c2000340140907a008160038039007095070888503403207440f0b800c1001103061500c8401000380c00004004220f04d1100020584204501e241401c0007440003000c1c002007290a03c240048a4002c0c400402c0c0c080c00f905400340c403000060400119440e84800003075503004 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 589405989 1250 589404739 589404779
    0x6190515041401020703050c010f090305100603051513030c02180f240603010504020c030c240121080f13030f020103061208090402070309081605010818120a09 70
    0x5000101004042c0d411051011045024006002500d00d07540b03d182d1610024203409042002d81e249460350a4000c0d6401c50266422070119039204814001c024002d01050209984611401d5000740000f10340130111031050008002443c1c03203008a41d0155445030255608a0340303d40d400203095003061842c0081880385d80340f890049030364105101e204200c000c44800240c00c1808030405c5540700e40b940400c5038116003082d035005030317100410f0b05418150b014511100b2558081d085403080da14071a805083c100c0c0341180c2003100a0790b620710509201c5a01c005940c140034011400f4031002c42e4040c000f41482e034901030302039880d0400ca03011038142c407107940e0412108030001c6d22051040d968180305000c060400342c5c103c46030010a17902e80024a019081045102c1d940004051041511800c6603200800e82c0c441144e030032801110030714201c65504d00030140050b400d0740c00140589029070200e03903009400e8000c0c0050b06911062324100ba4000c00f600014411200400034038825119112001a2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 589407239 1250 589405989 589406029
    0x1c03050307110d030915060303021f0b030703060b090604060305060a050405030c0f0f0715211509091101020102090f040f06171006120c290f0c07081203061905 70
    0x40c004e20300f01c8446d640c101043e800c0a0715004041c80002d03000101030301000c1c0441080780048070107001c41c030041c11a26020139058050743d2000020020107810403246021f0031107072060659601014001252407d00c03000e0304c90390214020404c1d5850551060b50407034081c005030b03860319004941d141d1030160301400d03894548d40040e4141c62504001e01154000c1c050f0407031510014a81e026000380301140c90a44404440340003104000380e07a0381980000d420700302c8022000c2409a0b1203584400408807103500f0788010600c40c034028603c0d807040c800c45801503002802084a030010106200062503000070765a80c0c1a546c8102007403001008220701140b070081802001c0c40101c01800c0170598410343d00c4015640040003061000070814150801a280d01c4490710090b00700d00d00c4410000110801100201900081c40509581940b4000c0101c4c85440040b90289030707035400300f83da0710081064907c60100040c40420020325203801e40b101d80842c900c0c540000991200009124120f098200503141 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 589408489 1250 589407239 589407251
    0x2060d090b1e15030a150f06060f030e070e1b0d020313020a12110402030403031503060608010b03061302040b03030d050c04030605160c11061c050103020901051c03050307110d03 78
    0x250314242526030204426050102c03100040c1c003c40d940b04d8000e00011b2080c107160600120400c8180d0014000d914402c605101450340ca500103400c41c00403c0c60007000904280c05074001c1c00001903090100d480105900720300d5580c1c059050481180040000b43c0c0f83c0c010000145240020700103580900c3d00140c00e081082014410040c000c94103510400040b400c2d22841d0020078038a50102012110513a0056500c1d07070356240c202e00500705d0003048010015080c00c041300b8007402d030b480401600c10302e038003c000511810382003542c0c0b03050490310000d080c41d07031180110050070190888001101c003d13040b2401c100c43d050402003551011a000d00c9002404501003040c0300a90041940040b50b0142405c96288900d000034204150024003809500360440e40d040942c80b01c0341142e15841c2d05100c844486c850010707003d0b0242c10280f2090f13116031040d000210f1203280043c0d0000d10074038003100d03941078441030350303400c0e205a0801007022007401100349154a0302c0f0703c01d12000c1c10086241c1d60020361 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 589409739 1250 589408489 589408531
    0x1306080303040c0e060306010605030a0209131b080901020c19290415090809190803130312020c06041206021b010b090a02190c080405100815010f05030402060d090b 72
    0x1100d13001801305100750f004c03400410480e03420500f200c1d00454001000b581e41c0b18a6804960481c0c0b40c040024a41403038414210303d83c100402021104405560b601c402a496051034107082c0d002e51888844075401c8000480d00200580c00480d401d20320820800e40b05200ca6040c42c0ca17213085004482d41454482e1040104001c0e05c0713090014002c1500074100842c1410380c503a1103050060310300b080d00541201a43d040200c040100c0c900c0144811000c403541d50300c084000441000131403004913446800b241590b4081c5002040d0f042916001408050905281c0020100710100103103050b607016a01700200c41c020f16006d6806403401d5851070001c620380b1308a50920090f000000c00541200d0310603c001e0314100201c00036411007200354648034280c41010f04010100d07104580c400c581c010901c00320310000c0703900180c0152140a02c242040a454484001518001044413100c40080d40c100f0000700140392010141c24800c001d0340c0c000520015559503600010b005403445895040d0481c80902 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 589410989 1250 589409739 589409759
    0x60310091b0f1701140315090102070309050306010b0919080d03020712090b0d0f060503241008070b25051b040908090402030415092009090c1306080303040c 69
    0x2140a000e0300d403002010741240f150b0309a02106000d80341040c100001750b8021507600300701c412080700d0001010042d9041c0900c005000f5400038004401040c0348290000e264603011039801c4c100d580c59408185440c0b00c2d4410081550302c1c44010b0564a40300076804104c100301000300c000010b4040d21300590300c00107410080343c6000e40828800400401c0d520900c00341c90001d055802c481e07071200001c00c110180d14604030162404d81c010300d07058030609400740d01140c00003004683c0000c4915034403016456484d000485040c180c081c0001951000c10100a0256504002e16500c500020f2265207200b02c082d201c0141585080191001c0e07001d08102c101c4203854603e1302c81515000c036000c101b12002a5034070758141c01030b207081a00c00c55000c00064148010655034011004000c4070030401e02d203d52a040203002650380503501090725511003101281440c5507210701850f8003200415030703c1590307010003a03e44444110a040a41c40380d8000441c0303034082001e180074600c0b54111403100e904101d0584 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 589412239 1250 589410989 589411007
    0x10081c1101020c0d030e1009060203100501090b220e0702010f150503070504090f1703150409080304240f0605090903070f08030601090f0b071208070e060310091b 71
    0x800325900c1080030180c0d03800700050000c0e014400c1d00340403507100032043c1c01c9814000051803411001b07060104800400a00d40c1c01144229004482c0c103940c183c69100450344115540207070764840c6010005070745494442e03015034421390000d858815640d5150087d004000e07000341c503201d0140c2c1d101d41180c40e900d4483c2c00368499000f48480103000d640d1400c00041d80c1d9900602c51940200d59540101080c03045c03218900034036541211640603022460206c4980c540c0c012a4078107080c6201204059a034500303406540543c6410071440d50468503680c442c40090302001200301141c5820400520550240340100c0907a18400840000c009160200340000d80b44001d1410322150030401080000510902042c4409074002c00e68075100c0e601c032070041c1c40182d696001000c0c1048003450005066041c01d005100c5184240c5108000840307800c42602d40c00170540e01000400c100c1d519800650401c0c5010b0350388088441c481541da680d581080d4000c40d00c44160b50083c0703b615801400304250003002c06 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 589413489 1250 589412239 589412267
    0x4030516170a0c061d0304060c060e070f060801050d03080c030a060905090a0314030106090627090c0f0e030c1c02040905010c081e0a05060f0405011e09020309070e10081c 75
    0x2440c20100d0110141c41f8072075405160140120345035140180300711070b80704003044200d4004403107200744c480c0700000f18038102e40b203201c00040d04a400410941090700380309a03001e5040c2c441090b9600d80b4150b02e850350b0001803440b00704a6940300d0002e469080342c014280101e680d10003a2900da503203400c00914a001b100000d06040808000402506a0103140b90044402c02c0c5400e002340001c03032007160400c103d0041200c02c5403490b01c20102d40c2c201240d214100440c01903d0b0030041d4040880c00380c039036100d106816a8150000d01d14007030700d07050401c0d500b440140100700e988001d0150b980014103c94200c10705542036035541ca03001034450b401c440c0e29074100b40d410b000c20175201011034a502e0070440082c01d0308903103901c400102c3c01c02c0e1030304c10441c864424000c3c0103001542c0c54094000381d00e00c018a031800d03c003441d0600040c4040c454800c985c068114180a44242800c0c404046440c0030081c04420540780191800140008140810101c1203801500b8408010310050000c140c886401c1c82 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 589414739 1250 589413489 589413521
    0x50708011e0e0703050405070e010b03070909150509090a08190813050a031b0807030809010c09080c04020a0516060c0f0512042612091504030516170a0c06 68
    0x700307102d580c0c0001825940140c041c0341c04202980c4a19007281000151360145a1101d018000401c800c07080301d000d148603e08541d01c3c46206582c9030070f0441640c007900c3c14043ca480b40401c0c2409103050030700800e030707020072150115041d142039640c603203005a0120340041c200d040059100880305901084051304120300d00032540080c0125144c85481e081d16600045c10b005004501c0b1040316000d0003071a101a82040c540d1352903d001d41030142508008840781c6646518100c0b4016090f80903803072140c1912020382c020140304101d5400c0c00002e5208240040500500348200b07000c2141101d410f4401c076201d800701058240312138001511340c2c80140001014080c0c14014101c641e4211003100703030f01c0398014810f07242e048a1a10720000380d030400c40b03400645510000f035201c820000c0d08a0140680103910480b20300d28811480d000080c002920014000341040160702c5401800305262000d02d401501c514400e00361620740300a8030b52044d100d59021501d44015681844281d20030588042c9000c60 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 589415989 1250 589414739 589414799
    0x31d120102180334150210060e100e0c070602360f0618120109030e09070207051e0a09061d0402150c010f060303020a0210110705100509030105070801 66
    0x8001035003480410604e15140456000051200040c00340a8020710841140c041c880501250081d26000c9103c600c4070014105030001405210504c1a03034859038044000d201307104d051440210000a014101c919010402d0001f03a0101d45244028400115042c0e02690b40c4e5007003c2407140c500300104488034000085444403c030f00c0d203e44040d040041800c81c0c80d182d40728211030f442d04103100f41c04181900201c903124036504150055000f090650b0103500c2d21420b1000b514208180c904c03007140d06a0050300500010850b0782007503030700b240c52440c54105d6088500022004103039507000b5940400200f64035481c1c2040400c4054200c800b5003000f81e1018050741c98250007080b0040c3c400b600b800790700b000c0000e410344c2c000c4080d840b28000c4181000284039555503402c00230b548440e0b09005030312072030079101c01d011654016600c8240711001d0002501d100e0345003504101d213030b0b4200040501403007020011102556028407030746200c0d45054807880c40c1d55041640e04942c298200b52564100440c4031 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 589417239 1250 589415989 589416013
    0xa06031d030702060f030a0f09050c12011505040e1e06011a0a021c03020d0501030506040b0603030a0804020d15020a0206012306071707150f0b09010e04031d1201021803 74
    0xd04442e0000c1c0c285010981d61f80310084042c000702906064500c0281c0341000b40b00410801140c000d0100504442100f91302c0b144440789422541544517507583c000414000300110305141c0c2200f0141e808400c161111445c00c8000710708101e84110000c40160041030050000c03034480800d5184096103490130b20306000245030003a40d500d40542c500028880f00320b0950540900c2030701159200c641501c000d00c12541e4929100355207002c280c1d000c4a03a84608000120742d070600006a075003c50aa07500c0c41861b884540a1000500c20000705860b59002e804131b013085111203000074413540056900500c030562424425120940d10000f070588032a002c1c4419070469620602980c0038141c1100010a036900d114120f520171340b10b040802010b030441c1c1045e2035000d2034658006041610101d80a0085807109010000c1400c024000c40c0c000c02d54282c04500400c0c4168060050300b4802c40207502810000c43c0002d00045100900c0b002c242e40006030040d40f00244041441003410030f82c010404031201e2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 589418489 1250 589417239 589417249
    0xf080403030e072705180604080d0213030f110307060509090a0f1401060e030a020a1509032324071d0618120d051b0c0a06031d030702 59
    0x2520280405455416001d110a418010781d80208003600e1500312596104021100f50298107001103940b5140000243c0010703d0498040d68155007a4080c0c01203541d141d0b22405c0f41d0700107a010a08103039080c4405007100600102401c040c50003051952004002c07450711801d202d4010320141d00a070401001040b4940c1c01c0f00640d01c2800c4225191145a6680c1c020240140305040340e1000c0035062512401020f60300d00740b5907060350300715035030784410801e40c0c1c0501d0b070740d00000c0c103000390001c840410401c1961540c501c0024174071160301c0c1528049a4030f807074010013643c0d4141c0300c0c0c0303070240030f8501c85000c02c2c010840310034201c001a100c05004114100d000307403600002002c0c141848642c01e80f207610108803042c034070802d9500900042d107a04044e40d040c1d04c1d090701200d00074001c9a040242c0ba035401e80000e55442d40300041e503640351801c1c02502080842402441007003020b0300c601070092020f0350700d171070001c1e002d44110341d40040c20300a8031207170241c02400210f400607590000c00c809400741c0c2310 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 589419739 1250 589418489 589418491
    0x40501022221080a1d06041d010614030a05040816110f030f0a0f0c180207060605190501031a060c01050906070f0210110c030307031d15061203040803070c05010207060f08 75
    0x32410002c500d0840e0b00f01100304031605c1900c069000000181c0403031180f5503400d00700001c850b00401071019a0b250360040d40c41030f12081c05008180c10900005031900800d400c0142c3c014800c95240303052007002a60a001d0b52007043c0119040c01280301c0b454100c0c18841170240b0721000440041c02054074614200d52203000080b40a803804190a5030081880a60307141c1034001d101d00308211580001c280c03500340081d00480012909036003881c0e00003a1501e0b2400400400b0085070141c010424a014015030081070007244400001c6041d410740700302540c0d2070001e000850b000c00000702e0245000e501c10340c14050010014420b01083c0d0f0340500e0020341c0000c00450718007030668001400041d415401d00f0174041c040c948031241c4800000c20030081d82c190403c01515903c0000b0551004404284c2c81e1035103107411010400b05a41c00008507036117425510021450840b505403131134a40c07550b501d281194089103059a8906001d0010000c550b41080440300900e46460406103451303411000800041d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 589420989 1250 589419739 589419757
    0x50907050915030403020c0909010504050c0612060f1309030806131e1107060612030906020718110705160312020712060902150a0215061f0804050102222108 69
    0x2d07011000804142c000c11081d1800c510003810040580b070194107050203000101d404030342500032007442000d075007080310507186d11000c1ca90308010717942e0b00d0780240940c8149003110f8031390040ca1001080002091489900001c50107540ca00d405e07440c000b406d012903c6071941d000c2002c0b514000300d0407403a9119803c03440e0400458240402c0000600d40d40741d5403070040d2003000d00050f10f07210000407029012490401c1141c0301e41c4171295082e580c0d04050382c440407184580c0450a07020b0304e48812040c0c05a0010050344048440760b0305188031070f02c0341403507e02d41484184031001d4045040c0207019034030b940c070303404010300344000d00b0722600f8030716001030b0403510200c0103011503200c640980866840d110442204c5524449298403855402402540c1c0c14030103050340402a42900400e91904246480481344c1090030310300c00200515000880b00501d005009a60b00d5500307100d0107020f48501d1034190b20100d20b448410100d203080c483c207504e098603541502e003400c000044070b80d0000f5541c0c9041c0d6541070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 589422239 1250 589420989 589421029
    0xf0f0b0703081003120507060c080405070b0a0c053702010c0305030606091509011209080304142802121504060b0a080303040f050d0c2a1503060509070509 68
    0x203100e04443c0001e0b454503402c01001592117200303040d0f9143e80180944155400ba08040c00100e2403104241c4a000703003a58081d11980081d00c0501c5400e0541000b0240e4440c80d143c03090400c1d1050b00d800b0b00707080d141d00981e05d140034410320301c00c0c80c0415050f4410401180d164207103404a080e90021301102c2a21000400b0310201100255442d0b80c0d00040d110325140c0606860054000c1c00540c40096100b03180842c04500740c00c1301010b5003041c5200d105c41d5240d200c01080e140d915640c907540307514010400120414403070f00c0c801a040b035850104840e6820340740c00505294403405c0c4100490135506a40b4807000f81e0140c03204130151110325a0f0981c2042d000000010211400e402156010585401080c60751000005202c01c0284c000c1069801ca13000b4000d0311090300607400202e402220b0903402800410124544e000044014100004004d001c0d6881b148510354503804100b100ca0082d011401003951030100300f025003003e07111968405680c2c50400d1030440d01ca030004400f82800d00c0d40407a84 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 589423489 1250 589422239 589422241
    0xc020a1520060f1518060a080703050c1201090f08040e0a0c122004030c031103120708090103140703020c060105010203040614070602090a080a03020f060f010303030519050702070f0f0b070308 84
    0x44c100c44138141c4410402178a1072951a40b01458420800c00c19624280034000e070940c0010021070100c0c41100746ea42c0603000c3c0014548800c10080b4440c0c40c101400215540c48403c2c40010f0026081d440d5024810501140c81d20301d03190814522400013072029203124140308102d02704d607912582d07981402034024800074418028028000c00d140e20b00c17503414042c4000240c04018408028105000c50b40300c0c0c1071200c600c580c60b500341503c07a52001c140801024050106038001034021018060442061600042d90b0f90307004100294880c042d0356020219034009140451007000b880002d0250100703000079850189003080c01421550404814100c00c1c0001ca0761030100302440d0121202400000c1041201d16220008141c4940e010b007c110f000d48200c2c03a0010361300401041040c890031500f942c0c8051a8656202500500001041031501180400702d20318410304600c03549000d101160b0092103094103140310902118400c1d0040e000782c0812400c104001c0d90740c07000f01ca2907141c1c035141400403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 589424739 1250 589423489 589423501
    0x1060e040b161b0f061109131b0c05011116032003030a1505130605130501180e03070b0c0a0908191707050304080102070309120f06020a0c020a1520060f 67
    0x101101c43d1001172581d8204244c000811103000080c00034504115524000d420703842d031860040700c900800c090342a01004064000140c050060000c845010f000003040000d00a110340109a00010542000c003d0788200d0105255004401c0495006800070382503045141c4c1e1401c1c3e590b400024418815a92104606203045544410000003404058180901c1e8124196441e0241102d401024092004402c1046000d540d501525040300d000f030b8060100d0741000c10003080078000048000009210410007100000c0031551a43e1180c0d45012802d61038203001c403801800c600d01c03603101c1d00f5198090245080902c8030440d0821103e03a100c1c0f21015402e5102407414524042c241c030103400350201150001d01c481044d00285240c078031960b070707030a0550303112200310303151081702d40010304025211082e410000d41150b0040c541c2c24040d003488000c260755980050b407521211f410102c8002101800c107074907250080b00d0300e140382c0c00c503000f00030720448a4510290303201d1000700032a407a200100c0114207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 589425989 1250 589424739 589424753
    0xc0609010203160803010602061f030303020703030e0a0f0b0a0608120702190602010507031b0e010c081605070305070515031b13060e12120f070206040801060e040b161b 74
    0x102e0951500f441c2c1c5203655040c0890550001d2203208050f00500f0006640303107024070001240391ba014103095000c0c6080d030301c08a000f90030804044080c10769030310812003000400c00c0000320f43c07032095020140810040c03420391000c0c07001a02e11f5071002d00300700d001c2c000c508010a014000c9030b9058011030301d403155800098022001104280400100c00e60041103083e4113401080c42041c9035141032091481100c412983c0600e180030490010b0134400701c0361015031007a04c21342d01040c0101256810014a01c04004c0f110b00c40803000c94403540180001c10402ca024401c00000b4602141c0038002002140d110084910004000c1040c00300d03802c480c05401031107101525020500760000c00c0c1602d40765000a408404141003441c403540503d66603a038440305c0008d801c0342c01403d10711050305284038a20041550740010000701d038000b00c14000030075141e80c24881c1d10010076204150384039500781030030880071040d00134205000f0200c009000070800c5410482c1e685285000c10b00301c4079904d10781e0909030303 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 589427239 1250 589425989 589425997
    0xa050414030106090e160f030c090e1c030917042409030501020a030f0b030c03071401021906091502031308070201110610180e1c050d140406060b0a020c0609010203 72
    0x84213041c174003444d544100c1c1001442000c071120728101c038040e080c3c44d03d03801d0720703451000e20009001522880003071003686015000212484016001c840c1005088000e180c2040d034460717076030702c0003d90785d15181080c0070085101c603070440e646845861905003403003541542c050000304405c2d411110005d424104520404541008680101c006c6480c2c80560b84018050002c0043c0118010b042008040407071030042120141c0d00c80080080c451203280c1190058400402580e4a0640c02035003d07682c0080d503040c2000400c82c6c81a4800101240140707415070301c0b407848001100490348148100f00310801c4950034a0300c1c1e0368000343d01c40d80314005071004a503400340c0c105207a80e04e80180d406010030341000c0602c0c2c0d019201c010048201030070b0158142001c60314042c40069181d0301ca005445000d48043d035a14616041624001d842c01103a0510740707003914648500040f0783c40ca48810031091043d40c1c81200d000c2c0881030720042c136091043d80002c0da582003017800346100300c20004442b40241c1c000c00c11a = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 589428489 1250 589427239 589427249
    0x130e0135030301090911120d0e0315040c292d0720060f030f100305030c0f010b041b140c010c111005070c080d020d06290a050414030106 60
    0x682c1d6030b60b141d9002c00040c141200e000c48400904a81090082c50f04d2060000b0050004005003044001c030b44c01103801210700741c282e640501591018181d1019000381d00e92299004100c08200b11740b900040e000d0001c060b0389440b0b903c407401c0d42c082c0040c1c40540300b11041008c800d0901011300c0c114100d0003013074040500c020051a2070009230340c0b040203130440400000d8210324000a000d0301003a802e0121074800c0609156407281c0c10400102000405603150f90040d6103540f010100c6510707559510714503031000d81c1100c03550b404010100c203406001d008161200005980c1403203090710390f186840440e0300c6040c502c1c09000070507201010740b50f800c000f92203002e000180240300060788190003412800c0b007001000060300540034940e0343d40c0c0c064042d00d80590401d6656028074030307190319601519007018074a83c080a408021265030702d00d5a020302409400740079a000e4000e0700641002c01d180c50800900c1d1400ca0f024000c45240c6a00081610101c070b0100d02ca40c28812034110001c0c2c010100d035002 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 589429739 1250 589428489 589428493
    0x90c0212041415030118021803060415050105030309010507081b010f0e070b0c070333141e0711010b040504080403021c05060105060a18060203130e0135 67
    0x203201d50118000c118020003075a00d10041d000c0d076503d61406120900642c2100d00c01c4404282e03260b41180d004102145800c0c0a5156440d00d92000a0400300b080e20b0503242840041407131001c114162081c0f5004110890045240c03841d02d2001804c1805255800781902501152a1010700301d114001901c080040000f00081c480041c20100205002d41b0780c1c016a00c180300010035800d101000300c80002c0c503028020614249196141000c0a0b060816416092100041020b46101c160801b400441c0d03400b0002c03c000c2e5030180c1100e01148014812a8442c840c00406683c210525505940164251810402001c0c0e40c40215025042c13614405420a14000030801440b6044024100356403086490f200200c182d01411010620b00740d5002c1e003540c1100004002514001c00240142d110030306041341614100503130040200b0541e0700800140c0c000007445000600d0700d03040078019101d1901c9042240d4140309a14007287d0110224080c0912000e2014812810b414100001a144002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 589430989 1250 589429739 589429747
    0xc0e011b0209010f090c02010506031903091d0403140a090509090c030a050105070207061404051e0405040f030212250303060f060c05070501030b0622050a0905240a090c0212 76
    0x10300e2070b181c0c2c4e215129588549290a0300103c0b1311f4418050a800391400400501d8140a41e040341c02e41c10020030030880901410120024200941c40c0e00310160244200700240c05140504001c0c09602c044501c1d180c1441e82007200d8000290003458580903110103482ca50b080d940c402803001e251160300340700c15605100f0449982c00b0002c054100a00c10710f00340c1e003660405540d440d400e941d8200720140c0c004420005000c18403040c1841c0b20310303103940c002c8070518580b900c0450300410204d8000351000d40c0c240501104031002c0c10f03010000c090b0415001002146421709000352845040a240e030903000803107071110303100d003418402d0f080800500782d400f17000c600b000e0756040003526140140408894a0050401c0012a58000d10802c190300300081d0243c0e01d04805984603030104006044007c00750300c00d410000c105515070403101c40c06000110b000252a0a01003e04d46607945035124446c5007031400c04408155482c1c0c400c00d1070459007904000b10b00064408000e07804d00021060490580ba0045 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 589432239 1250 589430989 589430999
    0x2130b0a12060e1b0a06030b01020a120e04050705130b0705160f06122c0f1f06080a0201020c0910030204090f15050f0712060b1602030f010c0e011b020901 68
    0x81d0000c05101410001c99420700300d45a060a54040031001c4c195005484003400c014203806500000e130324040520550b00040381d0b0f43d40b1552001180303c04800001c503407611407009400c15108140d00910b01d030030001e042c004105008a01c201140c0150803100c14085000010080100504104528800904200361b03446041840845a0703500c54540020049000392282c040300340304040c00310038200700b062030056020b9621640a01c0d050340f26040361007070381500ca9059400307000d020354900740340311040341c0a401c10b0b00720000c2c0c0718280c000003c0341c2c1010040d040143e0300001c400c070f251502621101c003581d84550341500b40212546c000b9400c10305009802081218840300d0307861852146220801ca140010203200440c0d90854034040d1140d1810081100c150142c4203500316410b83e2036001c100c1a44aa803190400c1e00081412207d14011821444c2140703818007074206030304c2403074bc001c106041c51580010450060a8941414811168010407801040600205000d80c000c1d114944e296591 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 589433489 1250 589432239 589432241
    0x90506040312140306060720211209030703030c14010e0312090109020a1e0306020d0203090d050c06070810120f03020c0a0e0a023601081302130b0a1206 67
    0x3a082e440007806804022415401c42030680340143e00103031081d4180f00003039a90746207096036214400280310b1001c000c0c04071644d40303950031840c4400c400d0305101581000141135142101d01152046050b000340b2113825030740c9000440804407a0503251990004815040003620980804800243e035400c2984040c1c00ba00000000c10004990220681013581c03034813201c90880e249244003d61098107502c0400695000280e80202888500700e461a107503565540d03d412a84280c0104034956004001c111100c4418090300d0110400d50901c00d18050040d40c00f47d407140c5004241310244000d24010815840402050074054500580400240603040c24003201e01e0040400840052085900c2c41082d41030990054044074803001e4207242c0c60304c0e2601d020000e500011075100744d030010240c1065550080d13400c4000301c92030b0070541c0c203d20442d0b0000103010706001000101c140050b106501d0040e00c41c1001030701560060f02d03001032174030100c10004aa5070f11680c401c20726410442d156406000e15 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 589434739 1250 589433489 589433513
    0x80d05040305120415121d01090c0503070807060c0317070203070c2304090236090105010f0b07031101020a111605030a230313060219170a0905060403 66
    0xb890407541c10014400e010300d001d102d0b5020b10742c011584004500c2001e4082d9000302c0e00d81020311000714080f00560800042c098145040c00310703ea440c1e45042041c0074022400601400302580502512414080f1041e42e0720710074031501c0300704a80143c2041c01e040c440d6003c0d20504c10b81502c100c8850030568402540e940140313100b90f452100c07140e40014100c480c080e544a8010703004008111507000841040000c020303207071007a80c020000190540d9031400d96100c0508081100713075844e60880c0c0114405202540042410405a14220041c080c6940e25407400044550124020307503241c400741381c00c4814145d540181d025540c004105a50401d0300228050801c080301002c17594400c0300000d550380c14049612419070160841c90340e0101040701c01005101401d21252040344071061070902031f1455001848400860f41c03200700900660b40e050011010b01c0398a94580f41d95040f4603100c0c4458000c00342007070b0855880c009445100b45000c0c00800005010051982da19142d480c108210301c520 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 589435989 1250 589434739 589434743
    0x170d320a030b09060d020f01050f121e07020a0c05150c06090f010b1f1103040315022a06010e15030111090406050901031a100803131415030a0f0204080d050403 70
    0x3190f0300090000d060200144200c103030024408080d00b48208010b41b2151b01421075035204420801500f0401c002c0b001c82d0f44d0003842400041c0c6454000094040e0900720081c000100310f410002c0040041000d41c268101914012035000103018400a015100c1d80301c0d40020240d680505401c20a0241000c1f0303624a170b0000c00c00082c000b4142c1441006241f051055810140603103142c113500d03541d4890030025041c1030340002140e1134142c5a440c3e1000030501c2e6000d04480a800140c5065103142102c1c1030f107514180608004000c4450499141e00c0d14414000c1c405010710340c000258510501f00c0d08168111800740007003010201e181103800300d544c0000011401607040440000340f9047c2241400d040f01e4001505001d041102030300400b01ca54090068842c20300c030f04e24041a030010074030007400120603100743e4007150391a05c0000c07031030181440306081c45800340c1005050760510302002c40e0381c8042c01c2d000c006042d194044403807000780955004480144100c1e0301405656801c00024000d8174 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 589437239 1250 589435989 589435999
    0x6032318060c072001050c1203011d04030f08091e07031b180b0301090605010620070b09060d0617030406092304020c0a02040510170d320a030b 63
    0x740d185220401144103d02004143c2c3d0b070245075082e441c41e140d0200d0441a04149441c92600c045444402d107040c429190601200c0710020040100c3c8107480d5210708070402ea4446803841745008d44024024902000da8882440700b00800100260401d100100203480f8072071111405075246010f07140c3c0c40c0018002149c60240541304a070116980142c2c0004840e071012043c0c800c05080c205503030250a42a915541640d02c2d03a4a1000192150280b280070700310030307624100d0200034911000216509050762001c1504180803e010a072031520458521a80c00e4600d0355441c010885071340020180790b441b200c4081480310b03150f00040740110040c003c1300c1c9142d450004490301e900b1101001340303d24038510801c0708024800d80aa003007507009008000440c2054515103052070300800e0a070744080780d940001e44030840781840203000444007490318900f41002460071604c011006842042c01178005020081e0300042035041c9030030035540480503214414079545580c0024030140c094901c40e10818425 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 589438489 1250 589437239 589437241
    0x40f05010e030303010509060d05010e0d0c030f030b030d0c0c080303040f0b09060c0d0905010b03010608070f0e130f0804030503120f060102060412050f070804170105060a0f0603231806 81
    0x9240010a0701d046e0742005007400802e854440810544a078000003c84407552950f000c0740f0701c84400d2200b4511801551682001c001c018030300109410741d5a078202c0185860445070410030780300050103120034111814100b000c40310300e0429807194222940f00e01100e100000401082010320184210200e12511255103a80ca032080d0300b5071203030012218950003610501c0192400600e50f0440000c4a00442c00010903560860202c1e00f0b480243e0041021a071020304c5c2001440c9080c01140000c0414003a2204207080c010201c1d4800d03c050440a01540c09000502c0705020780ca40854001b940e121085aa4819209aa45001400855030340c0594080100012015400481c0c41032103107130701281a01d8040c118000581c0d20350801101254448014002d000010341c0200c01480030340391080110807411109511142512002420140101b650340010044d503000108682e007a00c002e0f0034003092607280110464103030101c00700002c80300000841484035041c0070900b80c102311000b2505071400d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 589439739 1250 589438489 589438517
    0xe10050403020d0c090b090103082502190509070207080307080f040b2217150411060d051b04030c03060b062a010507020c18060d020402072001090b070b130602040f0501 74
    0x140940900c07003d02950f0081080380b4103140d01c0d051002f18086900118008243c054002c02c56000006a9070802c4140c0d000080c8842c1c41c1005890340d10905510082001a0801421320341340d003d00403000700943c0012550400c2d1000000585024106502009456841c240003d003a01045413508070100e201003030000c2410404c03540303151390400e0210009c00715040c000140714941c0100803c1543c14004000c000c80380c682e16103008241000c03000703001182a0800813014034048202036036090720220200310410014010a2000040701c1d0001d10003e0485008004950a40b1441c0c8240c400c140403280d801207071044100c0c0700c07032114111000820850b510f04400303903650200c10805a501079403c0611141000350380342c1065100501234013200420120b82d0114060f6004144c1c100d8071500c8c0414140d001403500c8111690009007480e14040591604603804658402c06001030100100071000030201407440c2c1c00b8420a0382d20080c00c559455640c044a92181003500589000030a4180301b912 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 589440989 1250 589439739 589439749
    0xc02030a0c0f0c05060c0d020601090b010f0c0510061221050405042c0d081509040303111303050d021002030402130e0f0d020c1201020a0e10050403020d0c090b 70
    0x150214054a4a4181d03802a45600c40b510380b2061044442001c0c0e0031002c901902c0c0c450203020034500d540e00404070702c004030034082d091040582002004502d000741754206a03074440045601c61105092402e4800c0707150620f103090004610550030203c2c00d020000801c0e0080f401e48014140c02900301100040200560f046114017000c6800c0020348240020302071380c80e250b407000300755600f140c41d814502190191800a91001c807900c812040d04115031140e14241c002e040607502414485004085004050000e00b0402026001408041c2d50710700d0010f4411401c41110344100746c00784c0e4010350568a00d0700302c0c0d5805a00d0b40010060140d001d1110b880b0340d0900980740581d40c020306044440c80c0c01c1000c800102034075007510a040c858082c3c3d4502141080c8152203501003258040d118480c104400e010021003001c0b815981a8030400414000590205c40b07114060b00445003501d10b40e06540c0125a6802903420181d1311035103620003017080103400c0a6410440f480ba0300d0500c507820b00841041 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 589442239 1250 589440989 589440997
    0x60c050315040f0e0106170d020607080c0310080f07061407170903030f0706020901030516020a030c0305090301020c0304080601120803040f03030f090b040314093d020304090c0203 79
    0x1011210a05140d41c1c014689034100c41070203404128005140e040c4100d0b0a0b0a41d8896403000c03e4102421540782e6181c1c1c0c040c0a00e1010294500042c00a400c006400600d51030004142c1e040c00b04000c4080340300709098a16881c020490074044513505010400200e440340d000e803040c04080340040b080100700030580707410745030415082150885c110404402700780f59a44031214441d810b000801c420090f9400b0039000d0081103000340c01c010780740d0000b000050704540c8040c040c10704451000401c507409075400640c040001e680361902400444003850161018050009038aa1650000c54031074440c802c0040070700100c0d4940c5003203075502e90307807003506890120500d8006010001e0400000e00802c01508940e41613034428a000260549841d00c69000c407412000100c1d140700d46d507024031050503807080054800700440b001d400d182501c0c1d5000500408462860403444500300e503900084507180140010705070394242c000000d00e542d40310b4000d40703a41c02405980303606490031000000e0544008195 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 589443489 1250 589442239 589442251
    0xe0310230901110a03050405100603210201090b061c020402031f14010c03080c162405010e010603090501090606062d0206060f0f040606031509140705090102100c0c060c0503 76
    0x40c1c5001104c40c000c80141100802c107441134840c00c101e004494500b07204403402140110301e02e107006007900c044207007038212494410085a040000b00703004202c1c2e002e104d40e000b04088848884035841e6016844400e004104041d510a101008002076506080040c80f07400260066070a00180c4a0b440c0805426001c0940d60004001c0303026000000c0c0200216a009a44004443d0a150b41074100000c0700142c240100c84030142403422080c0103200750401c0d0342d180d041d000305100075810201c01440c110130510402c1c0030191129030142c10701c1805c1d4407802001d80c01c0001400455158030b0017409041e0702c1c41a00c82e0000048080c0d11241c5048a403802030f8000076405820a61202400c002d040344015004d150f1004a89075803201c555528071841008006a880101e4413450543c404008002c15a0050308001d0502d4685440c034502041003a84c80a00e50800986403010701004038a0444249029001d107407a00c00c8901c13480780c20070040d101d014456081070207600c0c54288110381a000503502 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 589444739 1250 589443489 589443521
    0x60902032512050c0415180f1406130f150f050306010b12131403030411010f0504060203161127062e1e0c0606090603120e0310230901 59
    0x10110b0903e17064001c03100f09a02507602c0e440407615101640e01d04075088081d1403519644003000d00504005004080e01f21151103d880e60038540000410001e102c100721103001c0aa54003134141c500035045c1d100c1c0001d54440c0501144003600e45003034110703504490103414401d12890000042c0c545854040301c044090703144010ba4543c0320001811961032800408a40750b61510700b40c1d241441c0200061403080c1d0007144c406103c181014009801c1801e9044901d040280c20041400150340000c1200d0304c206826019400000941c05d04800303042c260041c2079840245201054101525801d842e11603080700403c050f06511988100450802038000c43c07281401c01c84100690365044444d5099500c00303e05101030303c80703903061425280f002d503090060085540d40030b1980c14370200e03205040241811080030030205080d512411440c030035100c072903820442c2000314001300d62130520405a000c510f1074002d02c081c00c2c429984880304020700f0140c0103660061000a1030b030071814014130385141c9a17501c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 589445989 1250 589444739 589444753
    0xd020c0f06090d1d010c080d0b100503010f0315060302040212071805100c050c100f1814060f090307030b0105090a0b0a091107021f020f0c0604090906090203251205 72
    0x1c1410003004e0a101941442020708941012071201c1e402028411014200042c01d201c500307080001400440d4400e4080010a10041c401580c600c40900d0a030f9401c034040900582c1d070302c80c81c034003d006950030094100e4001300d4441d10340c40c0c1400c0c200380150619150064a803120760b42d00340b83c0021502c540d55000c3c2c55a64124401c0703001e54041d0210b9401803003070758030307006071840442c010b180c04c10034440010b0644503111050a6006845568840401d80a401c2e00d41c0340c10400204a150800094800c07880000c1c00340d00c1e1008103088518020015098078091030352420f200c0c3c1071040c01d204681c0210410000141440c04911840d01600303002049202c07032174101080c00c80102082d180005130240c00308461009030341c3c1c6410986280504609181c161011103130000d0602d08880c1841e003040d449101c840340c136952060141e40c1541d1607050002003001481c01d00d1000b82042c2c42000e50035008032a010300b01c015141c0b840001103904814611880c513070390a003507010b55080341c101401c0741d04941 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 589447239 1250 589445989 589446017
    0xd0c030e010e04060b13061b060c020a060507020706080903120c090f15190f0e0609060403061a0a0f05060d0203060a05030f0c0301050f01060f03050406020d020c0f06090d 75
    0xe181200000d506140654480e01c001001c202241d28039006074140c0c00b0040340440c1c2e02c03501d158507034001d840149000e48904c0c00701584202c40750400740005003103945420100314498800c100c4030a030303140c00813404d03c550304007000041c0d00c4032104e0040c100000c20300e00004144500020031608624600c281d0000c4540c0c440110046039080060f0465100c5150742d11044030380c0d15410b00c1940349a6060009907074031140703803c60702a40c1000314006c0c140282d028005000c1c40c0c00268004a01310142e41081c1c0d11f000c07240001c0d0306403007582c00080895103402c40101c1d444180b50803800340c122041e604941841c0c1c6038400d03520309528600c40c0940c4207000b0044400200140d80244d60003c0c4d01409000c00d840d201c80000c2d0802e0042d070740310b100591284500501e03524003406100d801015081128400c2d5041c0300c0010000c04070320001806060f10b607400700e0101300c060780c1224080d10907100219154400d2210340c1e6101d107028908a52a80f0440b804505c140c440071031f02d01c078807803e543c54040d5078000c01 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 589448489 1250 589447239 589447247
    0x7050604060f080a0b060a020102090906011704140c0604060c0c0801020324030c060328050705070201030c09080d0c021302190c031206060302070203010c0906082a04060c0b090d0c03 80
    0x180032034005901c981d442c00590b151b000240019801580002d0b0721400540144241108001c4c6524100445041e122955607258040150455000341010f115041020403091810001e003400c180c010741d0000300000c226034003c2501030054800c02e0b110312110b90700c81000707090780020303111880ca110724950003120054003503581514441c000340c1036541c00907031781001505130b030812a0303001500c1084a07c4103d005030b40e9145004140c1c0c0c064410051070900c607500500c01e003d00c51000b414556203a5012006500509d104d02c0140464001c81e821940ca11030014506203100504a01581354a4900440c0310300d00d0080d100e180b040c0d841c5803221410f80a604441ca803000300340540034007480d88107a41c07000910307000300c402170f000e44d8030003580e00c410300d02c103042c01c445011700c2100c108026000280909540030040340e0300070000c101401e054121401c6039609908060715031110040f000100098603e0304803203900c1445005121441090ba600f6650325102c03141202403130300154908092000207402 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 589449739 1250 589448489 589448491
    0x40e0606013006060206070f050a0806130908090f060705120f0f030f1801050403020c190503010207121704030203091908010e160603021224090703020c07050604060f08 74
    0x901207820340380c00b20707201c1c000032072840d000c0c00042d941d88901c014042c203030b01048099000340503440d06001c41e0841c0c010003040d6004070620101000a00d0b800706680b680c40490204040f40b0030101080159074900d000f984960041d11b18901a0000c0840840603103044415a40d9017500700e00540380e44103514200340c42ca40d02810401d42d0a20003800080c8a542112020310b00c5102804141090b6040094080038008254064408a60f04100400c00020703400300c1d80b0701c4c0440c800e94610b05811582d1401c1d040c001d482d50845034140d8400301782c4d1000d0029904590145d4980f9866036001910184481e040c010011240035002d030340704010b021002d00740b4a841d00c40c41c00e02021840b110b00e0716001d9281c25144104040c003119403140700d0210442000c45141d20062000781002c500c5c244409074101e50300f5600130300b82c0086200440740c0e10300ba207600b41d5200f00b00c0700008020b030780c0500d01040041c009410140100309203100e911070101b4282000d00c2150160b0f0410340760600c07a40064031041350700001c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 589450989 1250 589449739 589449767
    0xa0e0a122303130303030915060311010c050f12121e010b0f04030b070807021e07030807020a050616050c0d080906160512070311010b0f060703180e0a0b040e060601 72
    0x801002a1403c2d140b0b41800c240146120f5503010038042c00c0750400b0300a1494034030060803c00d183c040200001a1840c682c80c0b06d0440a09060113403071700f107050070340c18003219424082c0d250164070b10700c2c0b20b64001c01d001080700070034074510712442c3e03216414041d241042001444070220003800c0140210420040540541038042800c10310b000d4690b55088440034050b40c1c4480440e014105100c0000e40500c4444071426108941c41410312032946c50a03030b23940003844040c000800019810342952190b101c2100903010140c9a03c2d41c560110551100d5200034503000e03603e80c002c000010005180036885a1003a5403c5a500c60030004c00400b000403c0d07200c41328050b100c032883c41a040002d24113004510031000070000c0320b41c80e220305060103031070752a01603c290b0741c69240c20368030451941d480125001c3d446e81034030b41644039003003458107841d4440502c44990005140503c0003501e00701d00701030b8520401c5158800e100d901c0c2c441c414001500c03a01c114180700ca40089000030407952182e0b04100c0300c02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 589452239 1250 589450989 589450993
    0x906050d031d03070b04080118050606011112130302190315050c09030601090b0f1206010b130f08010617060411040c0201020904050a0204091404050d05130b0a0e0a1223 74
    0xd00b100041e103010740940c401c4c010f4580c00f1a0400c44400c0c28070940e4036440700d4664103c01c4510580c1c2c2e860311482c00505c100e050101458074844a00d0341048100038030f00000954659843c48001ca80321800400c2c4004c84c0710301070b800001119000c480080d0800c503948554664825050929520040d2800030b00440f50b21405010000d81640c0403c003541c001c1c18030660000b9141d089400744407140f504d41d12181c0c015001d4008031440403500160f000c0c1180c20f0803280c2c0c1e40303071554200f51340030203601c0e036220901c0342c03141c200b01058000c410750001c0c04a425850a030044401c02c8800740f5200d0b501118003822000040c030502c0000e090a030000d092003101d0380700051603c80c22000141c1202e1040c1c6262980a074045024041c13403c4601c115900c0c60400c1d60061020b02c1c066a5203503031052580038080400c01c000c22a282034801030122322000c0d01081d4009501d42d000440e0042c0910320148180b84031700390f520030000d4024499100d503910320350002d4034076000000c81d58800b1903807540c1c2e0038440094 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 589453489 1250 589452239 589452287
    0x90702120d1a04090b06040b0a03080417031308101d1f0f021206151c2301031209090605060d0504050703020a0e0a0506090c070f150e01060f0906050d03 67
    0x10fa48030302c600c04c1031500c9080c00780110b0426034240400c46407220260b5005260011050002c980e490040c0c0301114542c2140104030b10054030828154000c000207100d0f1849000e2002c29480030104d09400a410802c030f0421044070b0501030340d032a400c16080c0000c41d68003c41c0058042d40501600c1101d010380303843c4003060f058411454441282d01609007030741c81c030a40e13106010642c50445031002c0d43c4102c0700032160030000200351001030411205102c6035150b640305070003000e0030740074200d5800b61120112040c110750780da81003034080c1103041c50804000a0400401007484d5203a80b25100940d01c0280005041440000c880002000050000d403410f1107280d20010041c2d60f2954220080c01c810021050700303052041c603243c1031f1440540164419840602000070000052040c2c4520781d800010701c52000c0d80c1c50802c20b00381548080c3d504809820030034580d407d407005402400403114044413140786a507980e0900011500f45014066100102d8011403021034420845440b00421a80d501041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 589454739 1250 589453489 589453541
    0x30204061421070f1107060e060c0f0303040809130539070c08120f0702150c0a0b092107111306030b10050d050703060c020f03070f02090702120d 64
    0x280a2089035104000744d8410070316407a09910564811a0a021100034044641003920240c0b009103503035542405020f01280848440e0001c002d1036007107114120031703642d0302d00301400c2452540e48080d42c0c0d18003440302c10b8101c06d01d480881c4185841281c1d031041001180d0f40001d20762080510f49540007144890f200c6800403140766120083c00594403490444207442e241140581c1010400d08994549140a1003c000f201c0703024012940e08650446098001142c1002e19100798020400c801c40144035010f0414100040c920056018518080c120b4054100c20000860001d42d443c3c084040b401b000d200c140700080114404008030180144030000709215210142e0403284258400e030f03004440761051018041c1880750103400360006485800a019591f1a0640e443c4003900c0010000c580d101c01c03002445100303006c0c245105042c141941e58806490800001c41750059100ba8402d55020f07002c01d102600003e1030148210000030030390706100f031500325030340105042ca08840007074420b00d0350504 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 589455989 1250 589454739 589454797
    0x1020a02120304031703070c021c08210a06031a0a06050907020106030b07030e0a02010e1507080d0c0810030b0601090f034202090a08030301030311010b010302040614 73
    0x121031501c01004545492640c2804100500c43d040074189041081040c40422036104410388061601981c140501400300c5c07510700001960304401420841c0045243c02840c6104c0009a5942004d0003d52442d516542e14140c11125140300050802c4181701e28261800d010080306540102c2c2c41c5000500da03a940ea020400611003150000e0043c1d654440910410508038215500600c880c5800c100030484001075030340c0c4cc1c0d040c07503020b0f06002c0c0c2620844a5659058036000038440c0c92442c40f44c40c5e03034407803600d0350007034021448070300c070b424282050f91130b016100b811040c1c411103680e4080c010042c42e60711910b0010700b0141509042050900d0b02290030300300b1400b01001188540d030203017030f0b90504202c00c9160f50241417425002d1032921001d201080484222039020342d80da003070b00503592003400300020f050384600d40c0308001034000400000103041e0003011207502c0035000c500038032800b4210001101284502d00076180800e4085203201c02070091003004d01a206404401d007240351001c158018 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 589457239 1250 589455989 589456009
    0xc0a0303121803021e12030a0f331a04030803182d0705061b0a0f030503070210060e0f0703020904140114090408090d2d021f0804030e01020a02 63
    0x283c0540d0006892201c00c810720031010070f11250b030320b02418518004a0f6960072911018120404c400d0b02c640b81d80034000340c1a44220782a020014254003842000e040c4a04e004100140240c10300300025000500c92201501410340c41c0e000000c003900d040c4c116510740130650005441303040c20315110801c02c00c60507020005000e0f083c070f90a0704a00d172200c440d401c079609442d044043e106c45801c00c502c200f1841d29803005a503440c048801806020702c00015900380f40c8408680c0192542c0d14100140040c190064006d40c0108140c0d0b09440c01c200e982040c00381070b0b40c0c8502c12503007411002d5001038501101c45603005c4d003007005031030050b2030070010800080c142c0743c07030800d80303454108418010070103c144c804140b0700192054550640c986819112011240503020034640101c0044d601841000b4803141030386d41005a44c5840284a013011103098400050888102d000310241c082c0890340c80c28192511030500c40d9540c81442a558950b8129580c1d108003076458198411113480000580d02c4601007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 589458489 1250 589457239 589457243
    0x250c0308040f09180b092b02070b0c0c012307050c01020c2209020f060a08100b25110a0608060301051e0f2502010203180c0a03031218 59
    0x75215400c0c0840b5260800c0380794066080503291203010780000c6911201d680034140c200b6111102a501c2402503410320144405c2507010744c2d0700e003814503a24541c0c1201540500090f6085500a60b241c4401100c0c9105040c5810026840420084810341c4603d4218003502248201d07050315413400000b549075504540340444081e00b066007083c0c09035030b0410600000b101c4c112180f1008030701950b80d030121244007681d2030300c10036110b0085209540301c1d900011412100a13000543e0b45413256401082c2e080c06888010701c207980c44c00002070070819541500c405003000c1d45420490b61a500e1141012103030b44c0011542140c09000090f910344d12a0079481c01400c032502e03485014985201007508461004100182c1e90b003246060000360604d004140d1b9011a0900108000d43c8520180f420001c00116212401142d980059900c4a5064000d50f014500e01405611824807981e000354582250040d1680c2100c40c0c5002000440d10540718044c032003482d600700042d140c0200501440e010041901 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 589459739 1250 589458489 589458503
    0x6180c06071103011103060d060e070503030310141f12090c080a050c1503041202012403110301110d0b010c06050103030e090903040b0a030207060e0a05100e030906250c03 75
    0x210700000c3c2400e00900007042e0b01e040070286180740c400000798418105400150841c0e80e50301c94040300680400402d0701809005046a480b403802281c4440b030380f02036001c1c015040c017070400100c019003032050340902150028844c1d0000f8881188048600540e00181300d422aa200d44c0b504001c516226100009001070340080c10705120142001460100b01100560141100c1e002001d10098001c6c00e8a4110380e00c40002a04201c448004034050003c809608119800400017610742403000c400d020100d0b88106c542c0421800103408160072112065076403403060784100840e40c06610150710100003540141020400c4000e1504ca1204540c402d0b001140812054901d583c0b40d464504001980290000c000710b1800307041403c500310740d0140da00d40c0414950003182d80410032640360007400d0100c90320421101c034641981009a903072940303142000e02c802c0c50051800d84292000c01100c00c4040040c14080c60700310120024a186180310340f10b90700811405042400140c000e2524034000e5020301e01c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 589460989 1250 589459739 589459763
    0xf1302040609170d031104030b0c120601030903020d21050405060f0c040f03030309020d0609030806190509061201141305070e071d06091003050a06060c020306180c0607 74
    0x80c01405800d0b0b80e410059030344104900070b101820002030109080811468003080d46c0990705000c0e01c1500403a080100481054030030800742c80741400107048074400e41820707500d26403100c80040d004c0729141c50f0083c006803ca4018542c1442c0124035900001c0390510030b244d18428a08440401c8417400e6a040342e0540181c000e016000170703110a0690011882c4400c82e2a0a10304038480414241c144802024540c907411242c06541e50211a490216007114003801012400e1900800690003122014402c0c3c804010210540e1119640300f0b0039618081c1203011552a48410004030310400301448034170750340303501141c0208030501c05010b002d910499841c00c48102c880c505507041c40c07403e401894010444000f0490490313880003000710841c0c1e041140c044401c0458003c04c0243c416407091907000545e0641c98407080b80c0c50360001d481040b60b07040400103161680700403181c0340d0082d20069850352084001c550035101d110b0b408080e6007803242c200c8441200d070f5008580f041c0c00c000016038016a90304 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 589462239 1250 589460989 589460999
    0x1012030c02032104090b150703120f0e030409021803010e15130b0f060f040c090306060e070903031b050a030801051f14070212151617040b04020f130204 67
    0x403800c02c0200341c2609071040d078000c0603d0302c280100d00c01c4820b2143c1750f12440c419502e41a10340e202000300207900c80d41d907085900b00640b0b500c0d8605121a2003d10f0004010482c040d03d206540801d241000070b5484c0501c0d000000001e900b042e00c09086060800145000a039024802c4143e042200c40c003401100b0303030b100c0c04006455401400c0f09a220f00002d00c4c0400900e45040036548120318050006594440070003043d900d60b050b880854106241c030f0700381300d410754000701014200c80c8213480512181c5c1d01c81018071608170007901c0038004258010030500001740a03842e040f090301011002080e080f51a501c905151440840080d4007081030b13440123005500305121302401558440e0208222801025401000200d48140c0e4201c4d040001c14032a04666650100242000741d80d811a444e90b980090383c242c1100007a12080d03149032100900e115058050034003801d4a00d400040c00d8045e944549904c0d0075003900500c00ca0780201030321755400c3d039070360b4031940554007090880b0010b80740c6040c9 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 589463489 1250 589462239 589462243
    0x110901090c0207080a02010f08090309040507020615010207360203040606030b060d0203070b130806010e150102150402090604020712020d09080c09010b070302030f160318050d0b1012030c0203 84
    0x903013210b40785401c02581040543d0300040c090f51742040c1454651040d644064220781580030302c0703400661050404040c0040980e0025000340603082c2c000102c5411a1208016a902c10192040c0180c080c0c00d152100d0602c1528086a13071034221496543c0c400000c640003010880e80110340031078905954000500034008510041036201c40240c54051040c0040e8002a0b0788040b54892231040020000b02c0c8008003108060b02c100800a22084507170550b114424041580700407a400c0251058002550341150310000c3e24002000d403006c00c03104191282e809020090340c0c020319442c0c00079000c000c0c10300051066100308106020550181500000035100240403c1e0340d40d1044036030703a001903600b0000f41d03030f001c1d5910304403015010580da032481c040c681641180281008a1080c80000c15038282014121410b000e246110f9a102c4444440000058825420902900d5004642619118002540c27440e00c82e802c166a51303005541ca90780d03980c5481c000980a00120006080c1a102e01d04500301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 589464739 1250 589463489 589463503
    0x507170c041e0f0b04061d0603010c080a0b01021e010c08062d0f09040f050d0f0509010e0d0b190e010902030a030f2a0b150f040207110901090c02 64
    0x2084406000381c640c500300c03003040c004035050800c081c6683e0f5001064030094581c800034002ca00504180149640d03445051410613001c65041c800511180000e400c1e49030612034004840e035180c840c07550070b89a0b46001002040e000c2506410352082e204440c40c11000c010200c03220300200000811032403200f24000702040d1024140078018942d54058480e404030b98411090050440e020f6104000604000185d416400c6a411a04613103d50b0500050090700d000056070f030f500880480e031440014800840c3c01c00280103009000920030f000040c0b0641c4074202e01466484024000d003200c0d2600d0f01c1c2d00102c80002c0c0e4201980c0240004070011a034058000e40895039605c1000f0818000f082e00425216141d002e8024100001c17a003400f440f0a0042003c81c000d4208000f00c1400c2c6095100325040e141d20404098a00c401440c00054918610f609000d10440028264051f03c04d0700c202484080d410519045034405100d0b0806071281e200c04101a0082c40010808180100450f0010f400c0c144 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 589465989 1250 589464739 589464763
    0x1b020918193008130f020d0507050102150f0106080406090512180901030c0b0f0c0303010914090d020c1509062a160e042406050108070507031202090d050717 69
    0x180c0d0b601c000c0b0103034100c81101d91240c0c1460010022803c0e5240061241d1200d54000b540502c030707640d030003041c0000000d020381650307401e8007160007900300c2c114081806901143c8030103440c4080030042c021300d403142000940140c8a124003040032841035907080c1c100240c0030302c14003001c90003040120a0034082f80c41c081200300d090b50f80200c0d55055468444070200070780181c0c840424005100410304141204403500d52a101007666200d58584401d007029050707140003816401c00001c003055a4003408642c05a9550207500206106074500c8180400300621200c1681c56a9080c000c648850b1509030040980c07242483c1c141024000781d0440f50480200d0540711201c40d44450900c01074541403800032010f5440403201c50000d507545142508a41e07420000d6590a985a00c071641f116420320340107c4150b45090300c1d0400940d5440c00200c07528002c9490140004010007810a09249a607009240f5020013400750800700035503440311303490200f480d0700181161414821180c91440d05220000003c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 589467239 1250 589465989 589466063
    0x110d1211060c1206060307110607020102041802041401120b0a0824070c031101110708071101020606030c040b0d02120615040204060509010806030a060509030a1b02091819 75
    0xf400e07241022911150043c00c207809800008040358009003c2d42c4034140d02e94844c0c0488126281c9114024040d410500c2a8001c0c03800f01142401c0c4180540255819a0808140088d0860b6158011215100f4100d03401e18070b507550f4030084c0700c1920f0f501309000207020090001e04041c85800c600011140c022681e4059250071002402040303940a070040c44041e0b010714000c6501804a08482d00610981c550f101c4600030025000d820003841074042c248440c0110340d150b6019a44100590300d40340d0499070350380c0c0b5400001a41201e07140542c0b142030030820152041c5140a081c0e800304e40b044220b500e0021491b07002d4810440d22140c0c2644524225070162000e5041c5440c12002910b18080c07160001d040c00b82c2000051525142001460075294121900307220b281080307004240c0300d60105a1541c0000e04c0031803c11324115030b08680503110303075000d0a07046056540f051102101c01c066034502c5068024841c004001c10b007078039003141049016810300c080180d10304500f03114016035000308041d48 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 589468489 1250 589467239 589467247
    0x310020403030c020d0c15030b01020c100806061e0403050a152d0e010603061505010804020a0b0703051b06060f0d0c26070b0a02010621110d1211060c 66
    0xc0e911510603003d156050b58404800030243c80d10343c40e0704295401c10b00c030a0f04d68010100855500d908840290321080e001d81e00000c911302c0030b12120448206514010544078400700302c0609102c00204103a07110100c06c0220080c456956500c00c1e0b2040e841500d6581c0042007131400e02c00340400590540e807140700d041000c0100302a8405000e5100c030581e01000130011022031615106070003e10700c401084008004568982c90041c005007070b101c0c003d400c1c2c1c2c0301c44680410154020807406000340c2e001401200100d140070002a0b8a50114030220700f048000c3c011081c640c030902c041040303004401300190915283c0f00052021100215441314800e44e4800129030225500a01040c183d50181c4409441c0c42d00102c00c4210820080c0ca0b49040c030300ca05c41c00018001070b1040a003400c1c060a50081c0034190381c5059030440004400c3d01024002040d41640b00011070290309075008220103802000343e07402c20748401c0c2504004c0307070480c40400c0c0d00c600795050f900000d1100592001c0c09440761814 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 589469739 1250 589468489 589468493
    0x1103070305010821030c22030b010602070f0306020717040e061e0d0f0204060b07030503011703030705300103060906062c2a0a0206160e0405330310020403 68
    0x129410340714000f04503002000c901c01e003010380200c400742450506034905402d407e000018a9000038401a05d60038282400403c400d40302182c0c0e0b008071000d046010390b0749030858035064001c0d03124003c01ca80d0568540a40c240b02d0641c580134000504041d07074907201d00d00e081802d012406a0020344050425024108a2055601c40281800a42d08070003c0c0c9110107451010a000301314940001100400101d01e800401d43e11100450690b1071058500443c0140040703010f80ea0b000c240c0f96180418018040d1a170400e460312031038071091030080740000c00c02550801c2c502d1220000c0c0c2041c0c0d8940e850301450800d0101c80e0140b00001c21216200781290008011240014400d000e042c031442122032010403e42018a01c050340380196030789040d6403034012181c80d0800c80c3e0243e040307140507010381c00010700507014008244c8600b107115140c1d22680c0d41803608010042600030507240805c0035a1850507211004000320144c9001404002c0b014481c26108051409066101000c480750040100b440 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 589470989 1250 589469739 589469773
    0x2103060a06050c0c120d021018020d03090e070504140a180c0519051b03030601050315130f05101707030210170f1603050f01140103060911030703050108 67
    0x30441e249032520688401c03861500b10700b05000c0c00342c825403044000d1518124140c01042400d030540c0203400b16000311210601c0c941c1030300c80200b1600c4944c42c40a0115025080114040c540607200c0c0c5000e0001036120a0b4020404a00303030b80708400030b440424140542030107000002810340d402c43d4552030036880d0981070035001c000c4a5010030705584900d04078a0b06030050090f903954840c4041d03d011002e401c020002c000341c0281140141c09401d280400b18080b0b004011a4064030040e919035156036241c03403203c1b428001c29000c854000d0010048404950564841d1100080901c40081b550b07051000380b96800c1d40d40c9403c00600a01c4500100300310741400119041286c1c0e045c2d0f055481640001415200d082c000d140700d007121200740b0200000036002d03201c0c040c4a03240c8084020726070400300070101c048400072101c5459080c0c03013000500c02c01c8485006000c02d034005150100303a254881480c034060b0b8034910450580c1080200a04c41c4c001d406004490140c1111030007020501c1508980704 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 589472239 1250 589470989 589471009
    0x807030b2a090a0f1d06060c06070e1c030815030c0d0609050703020901090501032006070b060a080706020303010f120b070503070513080a06051807031403120108210306 74
    0x758400c1c4000608a0b0750352a4a1441d00c01880500450040c1c560746440c00309000550148110600c46014002507140c03804900b622031483c003400c002c180311f40c0e40040c280d902484c2d00e511240d1284542d14840300d1403010200032241240b203039131000341030b050005100d40c50084240707240b4030a400c14055181d075526010600c074101c81e044040450140003c2c01c00600b080c038981c20280d0880400b1002140d1805150400c9040700c0c8105a03c0c0c0c2100c00d4481154000581ca42c0d42560084013080480013081c80c41454a40090000300203509503981c0f480e510786801103030783c405c2001da08080010810b42c80f030000104000c01c00e0710707003c0304040f03055a280160510002d294100303000001c40401c1645100710141d51280099401207c1243c0e19401043d5454040803001c4803803505080c00500040103005407950080e00300700c01006440c1c01d5588404001d07c04c0c51900c0100d10081c4148810307a5403664800340203051080203130100441c494081070350070101200ba0307a8400790803c00d04c402611100d20203 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 589473489 1250 589472239 589472311
    0x705130f060c062c030703080c030f0a090302070b0310030b0903030618070309020a03030e13110f090f03030d09140703030504090b01110703060507320a0c0c0807030b 73
    0xa8040f0310007181044907032a42003401030b40e2513040385070040c64000001442d0081c0a81c5495040740d441c441114210b2000300d40420341c0018080210324003d0580d084650228828019100e01d0381c1c4a245011254008a454030f038041c190850030000e105106441c240c10004c006c002c1d500e1454120085034075002e002c03d079039001c600e007880080e1295209030300181e0a25801099541131036524100103040300d03640001180b00303441c0c2e400d200585c10f03040d118000000901d40d44984c1404c03090000b1260503040542c006030400d0100031810f000c2d41c2c05200504410780e1440c00050f4981c014184036080c50401a03486d9184c1d489101c050010a802070250380c2100c4444030003060b401c00700f0004031101e0340c429400303840b50300c16210701100704030590304000d204401c1c56a031844c50700d414510f0b0b6450b018030b803012061014812408001180c1c0984000e00d401c28903130030f081031052200d81d00c0740c001170104d9011780d1083d00070030014000c0054040009400c0b1041c2c40e901c0e0028040803d0b40d42444001d2121 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 589474739 1250 589473489 589473491
    0xb181014010302091807170a0f050906070c03080a090f050105041109090303060f12031c0c0e0a0b0d0204030f0809010e011d09060102070b0d1b170703020906040e0705130f060c06 78
    0xf4006c2e5120f02e844440c800d0700c0c0b082c030301d80030300380441510064403603482c1c201c1203a401c0900040106100148052141d011a5244046000552815641c002d4040c021440c66600d803011840420a6848138541d2244070328000121841c1a01309a0314220001c882140300c3c004680c02d1081e040c90010a03250400c0742128241c8029400c440040c0542503483c0c02050107000205008504d00c0c07100d040c62603052510001480004100c2a08171529100c03c000907910052080040c170410598901815143e02c1c18040107291a40f261961000c002d441501180c3c1c0d103c0004500f002543d02044c410780f003101c00c1c02c04100e00c95001c640e503504242c01128090040a0740030006044d607100300b2144005150007250240c6c1d40340c051140901401e1280b403107070080c500d9292080161842002d0b1100c40f80301c0c0482404003900c03020011000382d840042e20550041003030102207400d1442040303c9014007001c3d111990703144110402c034201440c3c0d9500c1b641c03100c2200c14042000b070390003516049500d58031003c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 589475989 1250 589474739 589474741
    0x1050904120302070f05010f2007080c1905060a060506030112080c10051303020c03150c130510050406200607052101030c050a0918060b1810140103020918 68
    0xc07080340203000f131010280807a45900996400e02c1810350200c1c11469030078809114000b802030156007031081e81500700e072003080b04002d21004076402030081c10922030307081c082e2110807884001400440e07502c03900503581c42c1c21003030070701c90f000c2401e2080200a0105841540c115031408001d8140c002c1406c4016103040d10010703000d00381c0c41301404150b41c503861002d0308202d281000020780d48241c0c4e21110487c0940300341084840303540b4000a80c901c54010003078001c039083c4d58555408001c0d03000280b0800400c40210740110f01342d51407410200340c1a032035980d602c0c0c99514002c0010f02d606000c400a950011003602e0501c2c940304040b4180c4c0e88400e448c1040b42d52a001400800d00e280c040084120500031804d0002c402c11540741d0951084581c116294427101c0c3e100d82d0403d00311008503112104401080c5517080c0001d035250041c80d042c00d0020300c545007500d030111030303440050403c6406007612104800103101010703e01080d01c614840a183c11420b2018090110340054516000c000c1ca50f40000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 589477239 1250 589475989 589476023
    0x504080a050906090415090c080405071509030b0412030f0b030615010e03060c0a0e0604081c1106160207060f08130c030f0326160804140a0f0b010e01050904 69
    0x1070403140f140300d003d0410000d480c0941c1000d07003040c050b1f005000c04681484401c29049204516060240740c001000c0d10010340b500108100003045541d07524207001c100c40000001c00c0b201001c141c450b50040c028001d03281980240101101c1d803044a02210618012050015272000111160303c04944204144038604210050382c80c1c0c200d88108a6143c0b01d04400c1002003140400604041c00c4075488540307043c0698010400c06000d140a80d80c00d5601584080d01c11981401180300050703081d082c0340d04d42448911116082007000c45811000c0d41d8580602c41106504121610092025143c0006150509000141a4500036254903490800c1104038000c1c0090a4181402154002ca8802c1070741810700e40904150f00354400c0d440c6624064909000355520300c540300344280316090034443c044649000503503100e1805402034a001c1440603802d59042810407440c8440b90007604004003800051a00b8911400141c00024061b81807400401c83ca84801c01d180b50440e60100507101025200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 589478489 1250 589477239 589477249
    0x11060408010204181104080d03020d14090c10081b070507080718060b09090c1b07080723090c0d020d0504080c0f07210f052e0504080a0509 61
    0x240d0841459548005000a2003c800c24041c8520088456040c1308120201c20b080c84240600e1046001c01d80208240c1800c0c04c2c402d13801054034500316800000c010b4400729180d00b070102d00f146e4180a550181c80801468500740030420060900ca00c3d1010440c903156070441410700f900405000c1201000c10040100101031021b100070f030a0f40821105042d9484844800044c0d03c1540e81d04001d26008021801035803a000700d131440031024040344602d845002c46481d0a600c441c80100b0540354003404e8180050b028000c030ba0080c049500204801c1d4181000003183d42c2a41e03a1301c206444039174040d110355403500182c05620802d815003064581400c150840007911a422a40a201c3e10300820007081004103c0a13290340c80d001c8003115022010464016552003103030041d01d10b411302c281412032380d40d0750701610400914031441045000c1a000e41d150740c9400c01041c03968481d02e4110507551102034064000d50801c040820b41030101d8200b50311800714904c540280e00081210015020380f0175210 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 589479739 1250 589478489 589478497
    0xb01050d0e0717060709080705030d080c1e04080115151b1209090609051e150d05010203150a06050a050f0912010905010f110d050604091203061514071106 68
    0x2280003420702c003a1030340c2e901c4d8903040301c003d004030303904080120341010002190800d5400280080555901451003030322600b000900c4002408000c000c2c0d00003c0713514907010080c12400929241d150307414016141d0950300c041d00302110120f07680a08200181c11400305070a8012542044044c41070301000d010180e041040020788002440409520400c0e0b2100c0040308070340e08540d0801040382c0320210001036950548011034080c07203a920b00700e0342c1000383c2040b80d04a54900e0900503c4440309011403030441c02c01c9002c0c0c80995020040014143c803460120045c00400c9416400c0f0900f002c00142c468064800c80c0001c0000110342d643c1120303805c070202c50803c44014600c20a00301b4194229002e803940342400c40d074a50800d4a20820100640038440b500d10a80a41c1d50404441c403c10400600000380030b180e009031201400d90204038802ca107118440b5059402044103810401c4600f14100715800c03031001c200e03500308110f040b110303604150b400966000286101341d40e02c1f400010b4aa000e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 589480989 1250 589479739 589479749
    0x7051213063201090c020d0e040b030f0102070b090309030714010306031707030306060206060f010e0f09040c170303010b0706050a060e09070306060e04110d150203100501080a0b01050d0e07 83
    0x1103600b03850028119140c095041c0360040d8001081c581e00d90410f0400e8545854002000da1f2246407000700c203a00464502400c0c081c094030020704d0400c08800280b034004034541800080c2d600094560500c402400255800f948000c0110b21f00f6010b0800710350354908611400091100480d040303400fa80c4640c005600464012004820760300030301d194400503a00c641d038124003203841c09000140e80c6d4004100a1f10400d0003c02000c00702810030019101c0d900c405000c03603803012103004c19100655444914901072030007035031595001801c005401c811940c40201d0340f00c030750380144010002d1700d000b00120750a403607000c0000f00d51600c4022121004e80810740040000440040401450f0100042c01c0d8007141d008000501450b0390714480c5600425044d603014050060f01c03150408a41000304a00e01742c20b115a000d82c451a00100141040f60400e0380c24011121041e041048190780c48090250007601c03200b0708200d0300c14039000203007441c482d11070380f260110b44901d80000014003d002c2103000300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 589482239 1250 589480989 589481021
    0x703051b01020d060501020d030614010e01120507080603100905030301050d0f1227081207140d0509040c020102310503060406020705071a0409110c0115030501050705121306 76
    0x41c0d143c1c80d04002506450007282e005104001c1c143c003846109010354000c59042c204e000d84603102c03d00045490000c0c03810807906000c0d8a084070180000c00d032040c14860340066131948802e00b40041018186010061601030b1903040501d84800b00d000401101d045505c12510103d140d04140b80c81240390a03a5840a080d65541c00d400c00259904142e240034140d109004503440c1519030140305410071401e0186240b0717640010300c50b110340c003103203030040a038103020344c40108601e01c44244181c5401d640400020008070045009041410f01d406140308408482c00250305020341100300c0b51b0f280c4038000600c0c4198115502d80d01c180b03200003622001501001d810384e445440c050030700f04040d62200c1e130105c0e06440f0711034000407080455084002a2240e10000901d018506140400909849440300c0c141300d500b00041d01681c0400d10070480f4800020031404a41131540c1003090071940000d009030306002d8100074150384102441c2c1d20940c0488501448186103a01381400002401940c8401e0104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 589483489 1250 589482239 589482247
    0xa0908180f010203193b0a0906030812060f09040302100507110a030c02010e030d03060e010b1c05343011120103080d0e1603031b0206030c0d061a0703051b0102 70
    0x74032801440c1e0b41619401f65120050a5030300e40d85a0102c0d5a584006484150203110142000c2403049080e0b0300100300070310300d4002c083c4013400618049415501240503900040460380005c00600440d5400600b5091590000d80c050501c25203400c0e05500007000c00803081515000c42e8007400180e40d9418000d0b04542c0c200d1200440070300241600d008540700d841d010030000466921180444031078088082c9012041d081c0214020301610703001d4502140071502c03c0a500903490f101d1222000c594a043e2001640241d003072003c0c01c7d00c4010400c0d00f0b10104101a005c406100f00c1c03082d1005070020b1440000c2a42c0c14262841241c01068200424016800700000134002003002500740881107403020800c54003d001c0b0300340d951041d1035420441c10b55880080020a01500050612804003c41c03038950b60400d9001400d154004c540d000c0d040c68002c038030251401c00b03d00c58040900211003440d030700c0311120094003c43d8010068001d0401c000080c00c080041c0c0b000c00003210400680e8025525 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 589484739 1250 589483489 589483577
    0xd0f270e0907050f0f10080a02070f08190201060e13060605030d0306150201020a0e0418120f0e0f18130f08071223030a0908180f01020319 61
    0x1e954003881010311a039a506031070021032804c40715488a05e0700003803200c48482c03403511058420903c014500c11030b240e0b081c03000fa40070071000d03020042514800d81c0107564490000c1c00b00042c00000712054402c580c50220144070700401030400c0b0b0380001501041c0240c200303031803400c40044d04054001a41502406000426568250f0041011744004049054055081c11412800c0340615084400000c0c03050603030a040f4107150f841003042442000080c0701381700440d100c91084101d00c0c41020006107440c00340d2088607030700c110228101e18084070343e1005600c01c00000740322600b040ca14045150703d884041407441c000500000192039100d4480f038150600b50808061540033444241c0b0603200b04102c00107480d00c1402c81c01100d009159601b0042190103040910582000304440000c5564003510801b240507079002c1c00740500303414840c4220044840c14421010f14220415065500c240402d11305100d0103099500f052243c0d00e04482002900b80910704a000355500e80d94210720090643c1e00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 589485989 1250 589484739 589484743
    0xc1303110111030a211107140d0c0f020f010e0910090b010e0303071b0b0c010f0e06090a240f020a0e0f010e04050a09061104080d0f270e09 61
    0x2890382400d8032000109890107124988034400c851007100050000c1485a50281c5c0408409100b1070001c0b038002041040752265000b294001001130f1041810302c2007600c0c4441040045440a081c80c1c0350a8403490090303070382c9085045000f50024800ca500c1c0000441c141d1141d20100c0c1d15050040c0090002d0814844410602046008001d80b540c1404402d203217030b5000e03000075040801c015008500c0c10503507869000080510304155405079540a500242c245416009095949907110000814180b11a181004c540941230710300003c1e00305400b04404441c021401100464011400c40d103003d590200d541c4010009286024505262856808204449502400c00c991150321170080e1205642c0c100094116010704140c00603121861b00c11440c28142c1016400c141001d0380490341c0190f51392a02e058503a00400c00c0c030340403004141000b80c1842002820f4010002c0d00741102c55900680000300f800030240e0703004100590480c5584c800070702410000c002420075220041e11405c0450001d9 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 589487239 1250 589485989 589486013
    0x11271b040e090c031b1011010f060e01140f060d0b060a030903020c091b0d020f0a03141e221b0f051f110f0609010f14090c090c1303 58
    0x1115115040040f005400c0000d6000440c2074100f200210785860030b0704002080545400c8281000000311601707480800c00d0007448034502c050342c0c001c1001c0c1e0500b01c42c45505001640000b00000000301c0f0108240c07102d05801c0d00007e402e54403c1c1c1c0c1d843d0306040640141244c001042d82000300000d01c032620903407603480303001801d11903401e458040548008102134013605849114806050f0200d44802e40c00c504000c00110999003030260800c140d01c004004030783c11082c8001e005c251582e0303a04008960f20510340b54040854202071101311661081400d00c66402002c0c02c8800a0000d2120201c0030100000a825688082032100c82c03140041b49c6510030445205000044942d054003144a10b03040c20b000400c100403045956034ac48100d1421a6502180440700216019500310000e80300e005100700340c0304840e02030000c01d2410312659407034116061003042c001103401600c00d00800b8400460f072034410305002c8486c4504c0d0b8503101221011846800c44c441e40144011500004111200401c1 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 589488489 1250 589487239 589487251
    0x61e12040f150c1205070212120f0105010c030c0305070c0902160303051803070f080708030702071509080d0f0905130506130603050613060603150911271b040e 70
    0x1c2200c88440c03020480645501284180200c4c03003442e06564043c80940c0304030341c0b01074980b0440f29000d50900b00d0885a41c441540001c05600e014200308144c400f400130b0600404003803814489201643e10300074040e030741401000701049000203c64052205000c0e111015101110303085640300c410700e0006850342031468084001ca82004006180c0031001c3c1003030344101c4440c1024500d403408030364540802d6101c581044170418003d000300d0011a513028003440c41028590010309071282090004207034401040420401c00240700c4040c40280d10100d08038a419000f402d21441c2824131940540c2c083c0c440e0381241ea0440b40302c5451f03d61080c81c0d5044076000f80c20544d5102c9900205240f40700956615001c00350140d44182e002c500c000300c0038140c58040350b02401c800905942c407584c0d804a150000d00900300200e0311004148148099aa460142c0110860344400c400240146008000f000190010403404800c000102d84205201038040851940c0e24029501c50311038181c008800001d85003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 589489739 1250 589488489 589488503
    0x60f07090b0715060b0c010c0305100b131508040c2903130501180b1e0112050f060f01080606101209020105070506040303020406120203060913051e0c03100b061e12040f 74
    0x65100c23503406485500e005008045801d408030b0b0410a5000c41a407014207551916011000009040080038444001585540d0303501c242d00c2c18076007011503042c05039400070203105140c01a02c0b0804a5852a540ea40205192149849569001b0b01c4289d003106a80301800d29402c4c42c4219030600c14a40b81c8030121b6105800070803640d2a40000300d030082c9544040c0000100180c80144280d000780c3c4202140c0610070340880702940d100f1541d0324240b00382600c0c614070704490000103000c0c48034140000d0344d10007415102c041c2c00c64604034004040c01441504e414490b86d0360b140050659100c0c9044400c1aa080700498840b41490300d4001c0c000d41c0039218807400554505800c0402d010f041c02242d000d46401808413959448020300d00704c00c403131400340441e2944a0182e00308078404280b610410700359030a101074200d1141180c141814a000d0f00d2444c03278800d1130701d0f103080f5041d6070b030720155031001860403062071b0700c0c0c0d1025492a080b80b003045060700460820104210800a1980056140c1440303280 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 589490989 1250 589489739 589489751
    0x3031101110306030a060b03070f08060403111b0108070504051f08091c030506010302090d06061403240601021212010609050d02060913180311060f07090b0715060b0c01 74
    0x44040c08501082e03a903c2c0d403503084600f16a002c5032294001684c548401420380301050340c1c8072500c001e41d0000e54400c0b081c0d074000a003007100740342d005080c0103a0821105c024242400c0a400e0a441700312001804a041c050542d02149a4a1103541039501410b40603210001c46810a140100381b4070701000794100003038114000544001c80411925251549001203075800c441e0004107030302811000304001d041603400c0c0422001a607603400c0042c01c070390103000006a06c03030410b010041c04c0c1c181150124029444a000c0f01315144242c20900301110100a204059443d0000101d0800458102400e580100420124200c01c90529541e04a500b6a04c136441c00350740c0c2d0030070302c820651607043c065485401409017000364201a840c4c40c050280e811000901d4488400b450400354910940c107400142010380c1c85408081c080164a0f04400c2d070100884491a2a42000380012164000c90511400200d4584200550758001928410207200140012619401c0105040c0c111050720440303582841 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 589492239 1250 589490989 589491011
    0xe0a05030310062c0402310605032206090c0303080106260a050714040b1c0207050c1203040302041d01140601120e03040b031e01080114060906031603031101 69
    0xd03000d0460256040548110403407003c500d441c5000c1e018a41c9900645c08009844e1400440c28510841d010520071500141528a0030382c40c511a840c0c122005103c0d04206000b0bc8481012070051811101240a2800340a82c0b40807800b60052041c01070001c02e072011301008250b0030946003410780310320f903031003540301648418040d80b100300c00415041e003101118007040c404810b54010b03991068090800700410201c81030311580b140c1c4541d106140d8660085000310704420291041c07039a20800c00f4003541080c1407a21060780b0f85007040c00340d512a00d500307904c000b8080810300588004540052042005500708007036190500b291a03d4010194078240c1481900280a940680220410395806106208240c02a8000c040c400485a82c03440709000008008400400440c8220307c003003603200c680c0320b401c40c00341303051030041c3c01039019641803c036142c550310166000142e108001700c420310903a40755003010a00703002030140484500e6400b81070110505421001c00c84203c3c01100080000303c80308 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 589493489 1250 589492239 589492247
    0x32004170105040b0103060b030a0b07032c030d021c020f120c2d070605010f03020315130308060d0b1e071d0d031106040302010b130605010c150e0a0503031006 70
    0xf110000e00e00d005020051002c00c03500c2c3d001d6421680c01400301c038100b80e00c580700e00a40c403104031940320000c0d444000841118140012403071104c05403440300b0a88070340f91114192280101c54040d2001c2e51b0126440303050380a51400000c00125a080441d5a8400d1060078091a48a01c00b6406d010401c20086000e01c88250100c4c6c2c034031920310001c240140c12170342d180c2490400200310100344140c20301a44000c91040e2080600801c48010314000d103920710310500d030401c060429059038008000342000101034401810342c6489500d0f141018140c6c3c1c54100188900d0003140001d880308148a0070003242e02d4900d4640880500d01c08200d2400340d89000342101c4001400c0d00050080840e891084190308102040c481071910a041240840700d840540314a880d5048400f0742c0180e46952181000b0304180c1d030010f14848440c3d0060010505000c00030782940b10300b03800140400303407143d0011424490ba500808980c404a03065456020031410020740d6600241c420102c041e20081000800c5401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 589494739 1250 589493489 589493491
    0xe180105090a09030e1903051507020304120302030403120206060a0806130212074704030222060b0702041103090c09360f01150b0901032004170105 65
    0x401005241c1d20ba44a404403006082005403c50074031002000da10401e80d9003101400c0980c1c00c42d043d03100da051071070510601d03041c14400d0241c0d4235031004043c0410194007104482c04d5400c1c406e015040160307149422841e61080d6440907000c1c80b015403500d00c00795030104425020304000c9880700d034800d843e4143c1544450050780d41d0030343c3c01281c1690000504004510240c10701c01003041c0d0301d80301d0340c1e0018a00358403081042244a42000d220040800c951560341002d5140c2c401c039044881070144200c90100e101300d0002a214003100f0381840082d5020440c10840c2c140b000c181032015035070300d00f50440d0503004088101c0c4941c1c00c1c03294402c40311801c44203a0340b043c480311000380000344c80c0006106071034401901030500070340700c0012044142580740031001103a03144903107040700f01c00d200b4500f410121901070b0210181d041c8081c044000100750b024005640032034642503590814440140c00603c840c107840c02d5880082681c0c04000615903029000304d0742402001800001d80c055058201d802c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 589495989 1250 589494739 589494749
    0x1503060106121413140d092d0f06110a0b131b080d0906030b030c040e030d060f0f06020706091a070213050a0b030705010c20060a0e1801 60
    0x2010200412000748540418119074000ca040000c103210f00340c910840c0070204403454074002e0003c2880d0002c20002c080641055a9042c01900d001044480010103501885c0f060365013003940351031402d2000c1620003024038000c00c0540200c1d0899900d500c1200005201c0c845c64000c40c080342d02c0914031100100741c1c038160560041c02e001e6644d40d008039240c1c9003005000b040e2005c51010103400f60840d0316104d042c0260104500800403000100380c010051881c80e00284109810f01c280703280b00d40c600081d00311580300c08480110368440740c4090325280d400360071a4010b0b0682000700000c0c0000d04c000d0b8640030b8481c030111041100f6158038050303039640d4940c400d013000a00101001c022200310030070309481104100c6843c82c40d0100300c5e00040e85072036880c24074a1701c455441c414003150030a24480d404080205070043d010551410001070540440c420015004c4948603100c1d0340c1c40c00c00b1040c903d54542c001000140c85080d103d00041808001548407401102d65040c41441d0040102145049038 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 589497239 1250 589495989 589495993
    0x60a0603030813030e150d0f0c050d090212010c051e130909020411030414071415090406080601061805010212070303020a0c02330703051605100c05040501081503 71
    0xb480392150f11455401143c0c00780c003048511000f80c80c03d5a64000140b42951040a101d40c030b816003e2101021111a643d165410619001e000b110064106040d18080030441c0c40004040340b035030010900803003002d0043e80c8a0b500c0c0c00072400074290410050425a112844001000b0b9401e05200c4a00c0c0f00740800c12207001400201041284101e40184032100e102030004200a45040c1c0c5480c290b403c1501d00311100c031002c3d0001178040408100b00750040500e540c4a040860301c1c1800300f120206003884050701d118000400d03030000e48841d00554001e02e204001c5030000c0d80d4610005040300350300009a64114005400040c0c01d610000c1d5800f000d100403010a0324082031a6030540081d800b2540d407a06000030306180d0300141c1e80c0c0020324004036110070440c0c10740b44904c00185010350040e03500018015414403482c07010030b034040c05803a40488e9018218000010b103007800d906c1c0401c4944031701420703402c03d83c4000c4c00c1175220000d0800c80c0c0007a00c8503c582c1d125500d1a09080b0700701100c0c50b40507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 589498489 1250 589497239 589497241
    0xa0201021806070b1b04081c02151014040608030a111b150705011b180b030f182e050115140f04081e28080a1101020304110102060a06030308 62
    0x9011254105d2280da8244a1038919055440ca4040c0c28525004410042083c41c00403100c0c155405001c50000b007640307104407204624040c6c40905108140d802900c0f0300e180d040b00840f00c01c0c0c4039540504051301808040366118a140c90008111b03102c02c05180b00c4078041e0080e0707401083c00400135007039030746802003074000400c1c086910180075030441b0301d00b41d03400c0d0340342e00b9182c1024865440740c1d1440821503440f045000c51075504508014290b0b40291144a0200304101071950004105500f0031503001018000b14440d000e4a0b01e0040200e41c0415902c9504002c6842007070a48400e44403001c0b00c070400c0c01107a1ba83c18601d11a404000c0300c1c03e020072001005400841483c00091001ca6940c148032030406850301061460026441840c9007454051941d0034170440341081201c01000c00d1407140296400010004503011550040007400c40c07002150f17640d150350096035605080480e20000b1502ea2030241803084282c01500e8005015000d940d01058110210340a00000d030794060f240c0240e6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 589499739 1250 589498489 589498501
    0x4110a080a06150e0915070504050303092103040e0406060501080c0d051b040807030515010b040e0c071e060c02010e0c09090c030109050607030f1a040903030902060a0201021806070b 80
    0x50911005100f885040002010680c01c1c0114800c1e4054000300c402000c50b801d0404e001320110401a1400e07083c007109020401995400104544540b401607034111803ca480b4124000040c11062204681c2d00020030013240600c0d591086510a500842041c85001d0341c5000554917580140ca000500d448200140384100c441034000980203000396003601c98000c405010311003240c0049d046030300981c0003618104140320341040010002c4411103606a00d42d45020005d06041c0309902c02ca1070384004100000e20003a41c80d8060310612074100444c0348142456a1007180c20740382c0300c0e0089030701d02d15101e81c1024840c4148a00407559404130020102541058204102001c000341980720780c2c4103040500c0003585003030090b8411288580f00818080c141090081c0a17645e131000d503291643d02c0d102001050310a890900f041e0201e00b6030b0000780300011420704a001c0d261b20711004c2c5d008440001e40681c60b42e81540246061082c0407080c0d092440c1c0c03281040080d22034102c0c0640010000d0000c01c0b5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 589500989 1250 589499739 589499741
    0x307030b1804033e1005012d121101020d170604020c0a122307020a0311042301060e01030b090a051f090c1e020607030506040f0204080604110a080a06 66
    0x181c24900a032441d081c03030031200601e00d0280c902c444011107000d2207138003400e88940100400f0218040f42d110901c881c0d0f0403d4240583c2c0b912000161200c207089928001401c41c2c1150f40e8405800840112140407026041800701301041001083c01442002a9005098403d10100700c1c0c96500b0040b40300907444603402c010203034200d0024240c42d07009102d0a100003070a101000c030f065803050f031540d8032040c488410508403001c404400400e0164104242e0700140d80f105c140742e00340c9603c012055041902600410300038a50300a05400d0342000c020701405034a903046c2d405040741c0c4181d5a842079066a00d004505550240040c0798011200c0341c0400c0c03050940d0b4009544c401030042100c10041c000e840d43c02d0703018886a03c0203036025668542441e10f244e004100780150139605030100400121098008e646040041205081595550100b0110381e660f40150f500701d1108007080d9241ca4540c15051385868068908494030b68035145031a045041103240c48003140c480e03d000c0d100c003c40d1502c60300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 589502239 1250 589500989 589501007
    0x12030a0f050903070801150e1e0f04060e0a03020601031203020414060304060207020a0f14010f0f1119060e0c0d0503042d0303030e1002041401121b050307030b180403 73
    0x83d418000d240010400003001d10038a5003031154400400d0080707290151a10000c140503200c26068003564109903c40c48040c640180c2045082c042c401c8150b5407400c1ca00d0040c030405070142080d000740f040b24028076a001422034103aa004081d101c0116078003a600350100d21403440b032584c06118441c100340e400d1400c940910351050090101514224140d40043c041c1102a040040b10624080041c810340d8041140420808000c0c00d104168820070070340078003803070300c070f1000c1200b0009005070080c0384110130700424602801c25901c0340e600046614007140039012614180261b4858441e0050781c500d080c500101075150000f02031480c003820a2524040c80c0080600d131100b00c81c0720030001e07003035a1003d02280000c60284e03400240b0540107054060030403030040c64005c81503005000a100c0c010350b0b814012800b6800b424595450480400c0c06c00241000406000b2000310010900c0c41e0329270408015440307100555020040140b92000300001c40441c1d001140500140d8000500021300508a503 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 589503489 1250 589502239 589502257
    0x312060306060a050405090f01060b0c0706090e0a020325030b0102060f010b0406080a0603020d0602070b070306141c080d05060315040c0608040501022206091409070503060d140c12030a0f05 83
    0x95402c801c1c8d450320303540c08d440300d80d880070801240010301d02d600c0c1c0d1000d202c82c001800701841c00c11a01c40c036024030503180c0c0310054807448106a001021030014200520408041001300e078550000302c1081b00702500070242c0c2408103025005034800201a001c01e940746038140c4090310708031800d003820104202ea1500d4010a6140702c0c0c1d0740c0351004405a9200800b080c551445080b0261b9105280c2ca4030a00e0010050324540030305042c0a8107101c03201c0451518658503506580000c01c030700e0340c11500030b500902004041c18072400001c1d140c110040360341115108100503400c5903211000c8080b40c46403039404540c0546812520f110502000703214041e0320760080e000c3c03000507080040d150200180820b81e620006100c1c1e103160000c00c00c0507000020030008200b41c24500b4032242c003500204544400052250301003160000000e102a918121120181c50f0812001064040301c03800c419a03a42c8004d4650f8440c1d40f11080d82c007075507580002161417001e425a101c61548c1d00030b080540f05908044c0c61 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 589504739 1250 589503489 589503493
    0x303080109062c100b19030b030a03020709020d02070c0b12091b0121020d05010e011a03060616050706020c0108060609012001110c07050a0f052101020f0c0312060306060a05040509 79
    0x4c00107103c00080003a01040c8518040007900010844010381143c091843c0180039030000e00c0483d010940100d40c03e012500900301c09039540c140d0704909002072007072a400600c3c030150f20101242d48034800010388020082c08000014079100c02d10b1a540d900d01070521900001c04c03680c41d09000e94842c14403c104640035241e050000c42124081b00f0681e04500204081c240d90380004001120414000d01c1c01400800390142550320801621800da100060400e401010005908604001400d0490003000c0c3c120007507170f150355110340e40292503425903d6042d00286a45010460f2483c2802c01c071180318005849001c5401010908410720094101400485560710301d01000c0d001980da002f001e203e0b14802c05420700c41d040c64100041c00007141c0100014103403000e4140f00ca0b4640d504000d10610341c1c2e0707561151000f004c034030940c060320400304510b04448012404540c81803002003c1c1c80302680042c880762650340c6080c2450380d10714040b00d110f9071000b2640f004000d6401c040c1e21541d000406501 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 589505989 1250 589504739 589504771
    0x602070303200904050c0f072a0602030a021204051309050a06050a0902011206030b1f031b0501030e0d0203041401021608071a03090705010e0402070c0303080109062c 73
    0x690702c101622aa030900d00250340050030b4050f5182030b101e5107601c01c0c0c881803441d04041060500300701c1d9000362030000700300c3d035901d0815100420f01c0303414044e030114840448088117900c61a00944a400c038240c024050b05c1003940e10342c80314801000f604c05480014144034051443c03d000300f0043d000c01c4105581d9405202ca1050102d4240c0c0202e07486005128000310fa506043d100040c0b0003482107406d04030852a03c441840080c41c026203c41d00720001842034030f040d40f241300d442030000d40c50b070788002c000302290304680b105455160048412100709032802c210001e5258001c54a031085800c41d000141c00802c003d100b1600101d41113902200188112200c1503890340c0916031405240e007200c0803d44c8000070420666509002c46c005240c1c3c01c00889086007000c02926030341e900603003c2c06044c40030401d80c1c4000c6895a90644203020f07006043c0f647c0c1280c0da4140500014130a01039005003d08199020400304100000d8110721428145001610445407010000c4400080d00900031101280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 589507239 1250 589505989 589506011
    0x609011704140c0405042003030c060a0f05011e030b19360c05010503041419030f0203070b060927012301080309040e07081b040b090c070602070303 65
    0xd40344034492031150305510780301c041e296a041e1510f809028618072940c1020704010003e140c15210424002c0e00038014806056003400081c00d6004d0040c10005030321440c401c0208807030460308440d01c00c500c119410049640c948959044500342c1d2030703031480500c0501c1801c10014070f081d0b40141e030040315100341400c0418018100b0040c5c481c10750402010540c2881030480b100c28160542c8404498942c0901203c0380310fa50344907011005200e401d041c050044002030508c100444c3d500701b031100c1101a42c4003010042c102c20000d0007003038802d6001070146d94600354081c0c000402c589290350845a142015610802045010140141618082c100c251058138001c07400000c041c1c072040b403050002c11b0113844404584030900c50021b02120302e83c2d02c840101700c000000300444441c40403e50340843c00074510b0905a16040035540250802d10820b107840041c400e200c00e00312001c8500311000d103c07048a040821480700420348070309007030b00c60030404100080c115a005101c00780c407a003004031360384800d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 589508489 1250 589507239 589507277
    0x3070806030715110114040f11031c110609070f0b0d020c0607170c04060507030c03020109380928020a0b07050f060c03070509040603120c030f020714060901 69
    0x2241521002c02c0350000551661302081c010b091020070b010101250a00e01a110500c00c2c409030203002e45088030441c1c0a82c21500c0a01500d0070f141c400100b0b4003c905070701c610080c000c0184070f48108060140c1004600c1446012884500b201c0d11451228203040c10601c002080e0750203441002d140d241c0c00c203c2c034441c440c01444070350300c41e06050300c401026428801c4941c0786000b00070469104407804000a20890390400103440c54503800d072500c0004003400e4a0305173300611161101805c07401c00d01403441e038921510b003000340ca0011030b10b003031001484412a110809420a03101c2c0030721a0000200713514203e09280072008071159001e10b01c20300c4105030700858148142500001c0502500094100070702104205100e0048100d90007040c0724039001ea205d00c060300028007003108100f0000385d644400e41d6503800c4000071b180c010000ca05900010072000e050701c84812002c4000c150040518030460f8000b01300c1400f100d00d02d0110b0000d01100c1410028254031181400d41445661002c40c030f1100c0314 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 589509739 1250 589508489 589508519
    0x20307050106062a0b04080306060903060c0a140313140a15091a060a092c010926030103030c0320070f080c0a0b03060f0d0f020405070c0503030708060307 68
    0x10350b0b00d801c9482c0c5a8940c880f500d80d844210304001c1d0f0728484d40000006602d07404542d0340035070001402500c07919001c0005003a48150507031070b50305200b0301042c401c8900d20700000303140120355512001061030060078540840d0104030307000781d13100c0c802c2191840840e502694030040410300d0425200000c810b5907502441002c60403850b0469507680e01d0810420068650700700807240491200103a51910740d00055410402e07000e0f805c07480b621480a0190002c07640340649810030b051a1083e01801c3e030300c5d42c050080a400006407401c550800d01c07520b05101c40010000301c42c00035110036245a0840e10143d40300401c920080b402c00c10b41003410101c006482c800b0700b0b40d22138290040c0103101c0c90513080728503100a80c2c00c641c0b219002000e0305109651038003550000c480108441680701d40d20702c0001510314100c2c2031800e0b0401c90f0301c1c00042c10400300d8110421201e108980820203516006007c803a40301c5404c2c1e000309564400c00110707055a004a1007103074000d1009088408960f240c00343c852400700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 589510989 1250 589509739 589509749
    0x4060b06073509040c0536040902090403030e0309150c060705090f0f060d0617121204020f040603021f030501050906010212160b011814090616020307050106 69
    0x40750442c2c40c1c6010094404041c4440c140e42c0054009092900200e5800d2003545070981c801c680d504021250b039400781007030f14004c4001c429410041800059055400302c81510b10b0340102e50b071003400c244c1d2451305110710032060350007920326007141c1d403640e40a07001001c244103410140e110a1110062a58421030080b000b0300c040d00501d80c5504618450500d06503014000d041406400d2003000340e640c86c2c0d09a40a2040021a10000b10780a1240401c80510071042222421811700744081a00f14101c11400c071021000001c951002d0311a000ca020b41d030050700549481c4242030000f15016280000b82c0b0840a5001040000c81c540d5030b41c005100061401781521100d8521081603c465406201c0e943c0100b0082d03c1c200c40501c1c1c5080000c0d10b441c01d183c40b2054a0310049034084a8800e040c55045510383e0000032183e080d615000784100010325508613090050411400070311803001c1c040c0d000d00a80725000101260317101c611030b449201410804200c01c5120034404840440d4090091304000d00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 589512239 1250 589510989 589511003
    0x509060304140c01020a030f120f020a03020a0207060906050403230f0d03180203070909031710050406050301090c090c2f0f070b0a031a040906050108010f200304060b0607 75
    0x2c0c1080e800c040c1080f60381d602e040d05640150601c01c0c040703a0480b900c0040366099107480c1d403003000440364640051009104c1c40ea0030038030220706504100e070150300a10642d003180c1c086172019599044101c0305c113103182c003405001580c02c3c403040001950410340c0c120251a06242c5903c1200101e250500d44041d6000c00c0185500c01007000100d43d401d8410060241c0a000170000c0c101190380204c9e50707602280c8200300515503150107500c00d1500c181c900e54540340312012002c6840c101841c400d10715080c1c0c0e000e6607200d14a40302c4000764900c5c0501c5000c0c0455172001f15105501e10302110200103014529080c1d09002c0c0c071041d0014843c420004008120f620925038160b1509401c90080ca042d014010f4923a441c0d000a40900440c0d010030143c2c1d4103c038981c9004118211032100d01c1000200c80001c1507001401d0204c1503007040010b821023810389170300d08000c0081c1c0748045402c40a85884a00e07c0001300044c2c429108a94030403001998818050003020848070503001c08244694030880041d036000c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 589513489 1250 589512239 589512263
    0x902090609030d091404111e040f030813141e03030c07030c0f09050c071e21030f0c0e0f030102070b04050609010b01030b060307211d0606150a0c030509060304 70
    0x1400d541014a000c100c8281c40421101c00c1c180030380c80c41031240c0310400707003d00da17801c02001d0300c8c002d5007003100c000d4032451412840c400c0c0e40345000c01e03680d003004a611140d0380d0000300105410b10040201c0c02074020040c43c94a215520040d08500d1601c0c502c9169014001040b000b414198100190b0001310301c25040c0c441e00d280350800340822141660005500c00f81020240801249130030161040150021500c000c0f251900d01407007030710040801c0040028988030703880e01c80d8150b219120a1900e005031014040c41c84243c0b005021108560300c0d080210b40d09400c14400c07401c01042080e1a80806000149040850385401514070401c4504442ea640041e007001801c6400b8044c400e4120300a003024861480c060001032400c0c00010f00c1102084408852034104550080d491524110001000c00c858040e80d498440812050101e1141c1440b17404040703401d908080a480780d9600a0040d12404e103600c100c81143c04c214084802e404022003405092102d640701c200640c01180309400e0403800b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 589514739 1250 589513489 589513499
    0x90c0908010e010b090414070f0b0a020105090c1f03060f090c021b01050706050915040302031305010c0b04060e0a080a0503010603060e0609042409050d0206010e09070902090609030d09 81
    0x2500c1c00c070110060b250f4108480810070b40c507100403081d0010303405004801e20001100499203448410742c00707098051540140000c0344c00c0c03600001c0c0100b0350680c0c000d120715616003040ca65501140e150664001e1031800c103000100c2d01644c4d40784610303100d518012505070f94034041c1041c042080e421102d4120381d10403602075101d40400144d80f4001740c84203003100d0030102600107403481c0181c00e4041c1c015903c44000800d1920b05100f008000c0304500c2c03080c061414541402075072a003001c0300200d1007048070400480d407580142204040d882c2e00c00001c0e08190380d90b0391010058608040b10141602c6001540c0c2c0000344440041c22042c542c0d076607a00c0c4c6a42c54500004c003590100d612030344020150a09100d000d8131141c0310264400e03001100c1056a080e080c13082070510740d00300024042c0500d062202c0e42004408500340e10000b0305542215000e0b6200c500d4a42c407038109442065190f40100c804010000454020304203580b4001d002d1400d2408070b101103401c0554180881c40025210300082c02 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 589515989 1250 589514739 589514741
    0x50105041218060203160204110a1809021c0e0c0603010b070309050607050a120509040212010e061c0303181403030601090f1a0906041d090d020105070c02010e0a090c090801 76
    0x480d03042c102115030005454150040d481c0d102c3c084258090701082d001a006648868000c2c0750f0f0452031680382552a64500e10040074010500c500307101c400c19000340002d15900ba80260703005603250050f0b1020000d446c0c0c950704020300c5820300b1440c680c0070300d150010080d51010013039802480c100c1c20040d071340c1c0500e2500401d12000350300300c18071030b000c148403240c0420310008024508a034000d04a0001c8680c04809035175500401c0c00c801c1e4054000038102424505403180c4504860010b40b9504160711420b0400c402060306410713841d02601d28094500c04240b00380c008105014070b4000b082c465080b5612003020310208000040d04540c000000c0c81410b50f4400348e8500107140e006100001541002c2c0703140c40c90301144045000c0d2400224807100155140030071a001002102501100c1c489402035001d6a80022102c03005580140d5014038290340c0180540d504c034000c169206015090540c0c0195007044002c40116080303064950003054401441c41a08944a01903c03240003d504d0300132014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 589517239 1250 589515989 589516007
    0x604080615030a110628030207060b030c1f110a03090e130203060a0b06130909020a0f0b09101205090f0c0612011202011e090302090c160204020f070501050412 70
    0x6002c1d0380704684a070b01158002c2d07291242c505044070050380c1c48400898401400c00440c482500c1034081c00552149980c040d8010309a03540700b10824090180e1200405850341800905c4075044a503104951941108103421115190510700f080c1c810000c3e6040d45c6441e0403c0d8020071070200708a14000e1201803c003132003641d40458200203070612480e02e94046521840b001d4940030106440d9140ea1040ea03564000f501c9046082040c20603140d96503000344000750147c003606a0003050076034000b050010585181c1c8080d43c1030210907915081c610030610110101400c001c4042011103900100c41813024040c003030161001c18001c101807988104268101044601c1c6030340b00b108104044420b08050b410360a044440e90810f05418001c540010785c1c889100c090016103240e1707200e0808035042e4004c0d200700d060324025140003505640c0e5001ca02c04031720600905001c0c01228605a00051519400404150759200c1003a070034070b80344e6078805007950010303202221414001c0c2d41300320020b43c0c011007103 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 589518489 1250 589517239 589517281
    0x7020c040e19171e1e160201050a02190506160212040e06040b1e0f10080a0509250806130206030a0b0109050a1404141b03070201060e0a0f0e030307050a180506040806 73
    0x1072034400d11b1b0880740082e001c5000000c5c1440408a1500b00182c02404480341145404e003021403258610714106032034800c01ca030096030f00c120076100b00380d80030700c00a24001e2403010315600c5071605081c4204c02c0c0b0854802000b0941c0f1170340b01ca6010815842c0c0e042842d03103860002c114800c43c00c04600420201104144609010380c08804a50302d295620000650304503101810000d803503241ca039087c604020712156694030081840e8012000034800c0510b05080300d2561040e030740151a20100d401d100c0d507030714074080d5000c0c800340040340051800d88d2191a05100c14103020030290794540101e031070540306a00032040c030b400340c44542843d420729010321040c94030800a25807191422042c2c042094a0790b5001c1400c0c40360110005094a000350b00000103000740384218040b074541444080c00ad1302483c00750032052400c080481009813400001e0fa405801203072501c904000300e407502101d8045043d5400e180d16988800000340580300e0f80f00920160020002412080c50031220210205c0c40740a50 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 589519739 1250 589518489 589518547
    0xd1101020f0403020409060207020d08040608010518070e0f030f0a0506130506070f03021c05161d0d06021e0403200f130e0607020c040e19171e 63
    0xd15204500700e48111020b40c2c4c0d04030340004040c015403d20784024062400c00a401040c3c0d04504824000030300c0c01352003210901d0750340b0843e907030301e80081c4201006950100c98680c0804400304002c0da000703120303445c0060700242c1000300460308a40000d00d0195011401c08094110810902c203010050210b07541c4001e9208941e400c042040e88c4141e45e44100400410800040c4400303880c00621075011a10600e1000c403910201c44245040c0c1c40050009907030341507003100680010391105001c0c2e003411510044604c91102c00c0e0507901c09001e401c804d03030310048480300c1e420003422090a10068a03420802d50070a0300320b48581c110701d808940e004085200448500b200290a200350b42d407443d401400300720075580702c3c1d120005411810017409100e41401340700c0c001c0008004480f980020125043c8004407001d0044101c0d40c9100d5484640d0080a00d9100394031041d02c10201c4c0c0e007050b807030000c1342c020046c81e480d02c9210700000f0b039402d8034080545000f440000341c6580c3c444010340810205050084 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 589520989 1250 589519739 589519747
    0xf16091808040b0702190b03060a0e07020a1209030203010f05060103110403080313061b0c02090c07020906190f080102070c0608070206190b0301020406030e070f151d0607050d110102 80
    0x3980001400b81e03101d0b161141d90009003020454880e031075000102d4403a94080783c1c038a520743c0300e6042d05420031505607001d4606807500003a0090b110310094001ca000b500a0002040c40c0e0300c1d541074000c841c58003001807169425002005031424803d800c140e6021a20015003400c041000406540e98546c0d180100d0a040c002800401c81f500112a0410150176425400382140d10740032024100040341455140aa20380000440f40c00c00707900d03002c507407084030802c81940c1d40f103e040c0d03810f00a400f4042c0d0000f00e4180080c1181c14003204d100050f4000c100c4004c2c401350b4624030035240560075000000700b0307500800c3c00b0301008000411b40004c1e04050400921b00c0c07070a088000e507203030001440c1388940b0794082c00700200100c041e4000241c620001d00295903840d11808042c014041d0340345c03014098420240002144112000c024090f124000701008032800296001c0f203504141244c8480490920345450160740d6a40e4000e0108030b100b6005080b404290760000341c4411204840240c260740100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 589522239 1250 589520989 589520993
    0x321091807120c0c0618060b090115080606071b0e0f04031d15040b1c09030c020909070906031110020724020a02030703030504081b01140c0f160918 65
    0x203412070104820600000900107401c14013111300c2410040040c240b940340281c1211100d5a0b070f20000c01d407500504042c4820504c0304240644240709102c4c1054032500e1003a00e0f04058130407400c094110000503c0d0324142035041c0c031580101c0c810300410110f081ca62950800c002c86450b400d0652121040c031b0800882d02d0700351000780a010307029a4981005403403465102c05659420341c2c03c0d4003800c40c0c080d030a4a903078596428401d10340c070104000302090a84017415102202c2401500a5945c0c55540c4006844080d801d11810003006050301d402c0307018102d400301c2c20060520481c0c2c0110302502000c81c40c501c00710144600d00120030403210440d0003109090040081e48101c0480d401e8500d900e80040d400d8454080f0b08101d5031300802903042c069074500000380b5600c00054010b0394030030425107100c4244a82240b604810f08211036020070035a00100741c16507002000303444800526426209a11110507074581413403103000d121382080440d08000d1103000d140c0c0c811072101c80103074050118045095 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 589523489 1250 589522239 589522247
    0x82101080f0721060e010204060315050f01080705120a02041502010c02061f0803131401082a120f0f060a1a0a020c10020114150d020409020321091807 66
    0x75000e4503100b410702c15a218a48000e00b2050500e0f5904803004119a1500f500f03507501070342c4688180303400a806e084006c1f003d14600b102120403103070000c050007050845800103450380341e0b00070810f2003031003828481c03640c0c0c8411401807244506041900181d4071402e0540035503116482e00b010344116031400c0d400c25500e5070001407558100d4032a882450410003804c04003040601a40c1050f0001d02000c612540b48010414002c4d0a482e0210400c81c1103400361f400440d020705088680940030311402d201c130004070041009445241b950010040d24021403460301c40144a0243d56110609c2400420400340d1001c0e184250341008040b9010241e45291444010420320500d5000c1c103403090020f940542d07103000b000055481040a8500360b07003e82e150720702900a000083c450000c0324542c1e000034429041580d03212000c3c030801482101e03000e800b5000d10008003000c090881e054031030701e6550500701c940682c43c07038079080a451300107541d50801030034440d0b040403001a0400c21008582444189504 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 589524739 1250 589523489 589523503
    0x51014040b0916030501060e0117060f0907090501080a0c0f06270f06051c0b010801091802030102040b091c0807031b080d020d05060109031104090501020403082101080f 74
    0x3a00701e00407600e504030b42c1c504003240d1038084607080e144502d0000c10040190490001c48580142e015800c0c1c1e62044034a86200d1560641285038208400040f44920480e0300715401c03a401c40d080707485042c1c44440c5102207840a811129aa41c0901c08200c208091400d0000142800c00343c07100c0038a107040e801801e01080301c440318071701b2802010b8220342040b20103144030040c070321440900c058075a120300c040d1280e44100c1904041d050501092640c02105001c3e401d01200181c1d90091103070f2a2540e0f0100600445807800210038030720410b0b01c0540d80034006800540b42e00b070249987c0700d559004001d60407000210401c8581001c10150340030400000c20341d00c1e010340501345198003042411b1f4202608143d503400030900a8007084001c2c0c1100b040e80584003d600c2c4040400c110b865100055410100c10f1000400b4104101d030305102d10306040e00f015428501c500c001500703140e1079989140a80e0000c4010000d860b6110304961220485203520500502c2968090500d010708041210b4840c44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 589525989 1250 589524739 589524743
    0x909061807050702041503030c1e0f150e010e0f010b0405010e060120060106122a1107170c04060b1e1b0f060421081501030605120a05101404 62
    0x10000c6206400d540317036504042c05407440d1144c0c481c9450386900e4080c048076802c060a4a0a0b000c00e588a45129401940d4001030360700010354164040a40c0e49040200181680341075020b40c9a0000c81b414003802d00071031100b806800003034511300418491490071914080003840c810783c00e01004010780540304440075007090b030130b2078010800166a80044620700b101c8001814a00c6002c00004c1c07180ea000350740880384058490181300c9581400070b04000440f401d00c9410084c0c00303e8092201c902d000314084a61031104005441c055595000d240c014482c908080751010381084200000c0c03071409204e0013010740300c89288a17040104050342901135480345031109002c454001483e8491452200344008006582400c950a24005a4003585c03254410396003141d4030011103245048214032110b000e060140c4969602c0c0e4207035a03051508a01c0a1072000b01c5045c103a44010102d0030362074800ea244d03041e2701c42d20002c1010002c01c5c42c0492034018061110090145860030350199007a00240da20382040d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 589527239 1250 589525989 589525997
    0x603011a24030901060e0a0c020303161115040501050a020f0403140304050a12050f060c0a03180b18070b0a050412060f020d09050c060310050d0312020d020909061807 73
    0x142207403001c1c44103605041488608000b004002400405420200580721718441403186074480d0040141912440d200c8a00541c006100089880709080074091000c1c0d000d20703003294003180c112540c50504c2c0d66610060380d0512100208402c0c030400340159074000c1c5208104602d4441d41640084950007a400014112109012540c06142041060700d01800d0020300034615982d94030a50107241c003200b036080790f503800359040c444410080419003900c10107841f88054a0010f080c1c03000c40091003200944211915844451808110f0700140d051190700184140c105041d1414050791602d1030070360040011200400c4035001c140c0e84101a103003103608a80b01c2484103081c034541800034148241c6042085440400c405020200c19005611814005c02c144e03600a8240002e021017480100d810a198040d50b060400150070231100141115020303190081d9a80000f0060f10203907400343c0c0e00e4240c9240c01280940c81460300114698115008545201900444007040c41c0c802000905041c144 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 589528489 1250 589527239 589527259
    0x30c0d0309060c060e01050a0203090d0306140f0a031712150627031c090602030708190507060c02010209040b01020f150709080a0510110c10050a140f0f0603011a 71
    0x10704d6811045c40d810700c0000a01c80d52504046800081d00125840a4a84601d03030003e444030b03010b40300311000d0392400a0703030080040407041401078204ea0205d40301d8110070012000004250000c40440c0e90000308000266101c62107402141082800381c05180b0012064015009540d2501c0c02c4a80b02840001510320841001241d01144a040800d094050044400424800040105204081c0400e4440c560b45903250b032002c030307070f2809041002090140b04000c80000c481440d5010038004449203880c0e8640030706541c0704820f445c1d0340c08801000d80e4011919158515090240780510700c0284024019180700c1c40c5110783e01c0751b200410380182030350718022405461041301e0b80400b5042c0c0c0070403110004801e04d0010b039034113005900112030a1504c000304d0541c0241c84100c0b800621084001e026407150412550020203010b492140e5403a910040c0560440000704028031030101c804000c3d03ca031510010843d000080180104e00c264900600c0001c0440340d41112200c50300141c9015240c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 589529739 1250 589528489 589528493
    0xb030d0c12200c010810050a170c060a050711060715091103071206060f080a06020f090d0b1e07020d1b0b010b130b0a090e07090e0a0b030c0d0309060c 66
    0x504980742650421034801040b0a01c0c40c10000030316020f10140a907998115035880b02d6132011844014000e25900110ba080104038943c0c41c507200d40c0c80c13144250140c1d01e00d00a24000500320f40c0c000322260010480c04101030f000d10000c6d08192441100680349546000c060307503904050401d80c0c0400300c1090303984240b40014080401009401c030706010b011030385625150607401300d5100003043c048070001e0030501d000ca07000c035090101c1c908032851803008007003e6015954140194008000c00c05100c02c003842180300f00c0da1005c0344806041c4c003401c1c490710103080c5884010215141032072489440308960044c4071070190b0020741d030261041140f0b41000c0c0711062000d0314038500034207132015045c10020000419842c01c5070000b08626030300b1460fa8012565205481d03800c44c00340701380b1580400c00c03125040200150000030313140c0c8030f00c00d80780501c425521000489040401503030f080c4019503585400c0311b1281402c0000b420203010031600300c50007a0b940c4c1d400500c0e650540c0201d0741085510181941 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 589530989 1250 589529739 589529747
    0xf020904050f030d0b04060807030503091201020f1903050a050f06040f0908120f01080708060c0a110109141006080304090c02120d140a09151d01050411040b030d0c12 73
    0x54048800c4183e07980c0d10030042c1c0f408050224100450321941c82c002c070000e07001e2000101201241e900030081c50400c6d48403800c0000101c50b0910a860380d5408026405401c60400003e1211280864040c8000840d000c0d0080807918010040d8030440c1c40c0c2014080c0d040d010130616540200215400f0600d216201d280c00040e02c0c6215009140c56004228400b146500c91044c034818421819825580d0b83d8030881150307940c50703912900296400c02d60101e4404081d110081032241c0d483d05007500312070b143e82412421103910840c196a07111540074899840002480003501e01180c40c942409810b051040c070075202e00c118030464802c00d54804444e138403140280201c3d8003002e6111400381e03e40406444039005010260410040c40f00d5000c0060b1000920344149003244c0d40005850728402c0130091280001e003882e00848515007100108445161024011244220704c10b00791406000000018041580d80d48106a88243c020041c0712212540c40844040c7e41e907013002140d4412819410292 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 589532239 1250 589530989 589531003
    0x1e0109020d020d020430030f1b020907020f0d090302061b1f05010603050130110303070302030d110702060d02030a0603021003020918061804060f052508040f02090405 73
    0x16140c004607000400d03190041c20b04070a03250f00159011b0b07054104c10134442c54a04420020301095250484a1309140314884541029035000e40c008428031544e000181324240440ea0307400183c0c00702c291000c0907082400035142240140c20704001030781c2503500080d000d009001b8181110b084480007448284000c10a1a044403185580003441c480107840d00c1010b4a4240202d80110342090f0000031030f60001110407902e200d804205101c0c07507030f00000c45003104140810683c2ca406101c110460b8036a418001040210710030380003150f4690b450f41f4924140e4400c03c8031048040418009240581c8a21080f505a1a5028001642e07996251080e900406890300040c1d003040d8002c560000d4640c00d0b42c02042c0d4540216408040c80d10100d0140d1101c1c00304481c01900301090403032034014600140710301c0780c1240c8201400308410042d5804c08040700d1003124a2209d4400e200e003055010044072528500402541c0740182561815465814081040810090003442c0041c002024004280108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 589533489 1250 589532239 589532257
    0x304090513050606010219080702150c070e370e070603050103052a06090d050a03181a09011b05010504080d240b03060307120b0a051e0109020d02 64
    0x400290030304500c680350761041603038211014414030012442943c000200003400c0c0301d43c160300150902455951035610740208108a8000c04000500000365040303001400f2100d140318028640340b0300c2d05002006090303000c1e001000700325540600d00300640c170400d042040221f5070841c0c10f54019a00d189200207001507448a4124050400003150341c03903154004504032030081003140e003003480e008140c10b5520704400303100d41081a030284642c2907040080c0581100100280500d01030f12581c1c940c5800d0541c141421000a401c0f0f0b400c1d405030140603040c0703a0192603092004900c0302d110f80604201da20940c0c040740d048c03004290902d0b122401800800c4205648540240801c3c1014a0804140d42000502006a60400b1241c0315140e04140345125168524006c1e503042c18585012041c1030f034400b8001c01d4050003a00004a04200c0301803282040d584518560070040c9081142c030070403500c015041c2c0c41010f0719040074005140d00c08402c2815515034407030059840320b10110b088001c0c4600040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 589534739 1250 589533489 589533491
    0x71e080606091924080a1b11031c02040f241d040e10060603020901120902010e09072309211c0c050f010204050108041104150312030e0606030a0201030e030409 70
    0x8a19050358011301c60002601040d15600080d031501c03805401503e6502d0080d01e44038000007440c3d0b061910800c0004000e2185c0420b603464041c0c1100070b00c1102c5090380c4012881c03500020300700a01400304e11aa0010070010395903404802d505555451001d03220090710b010040388104c4d040c011040c40f400443c0074080107004200c0c046940007480d403213045010191004c0b070b00c3d00c0030000e140c0b03010780202c41e1340d100160b50302c424580132440712900805c0400403e90410410303000c4030405441c0c0c24403403809510651209104208040c9100862180288032100d80c01d1081c00000803030345070016007025400071400201a18894442950b250072402d5000b580c148185003e13402e811900b00344002c00720380c019820313249491400c680301802c1c0d00c5648101400640b4040000340480c0c90080320308d003030700300060001c0340c401010a0b0362480c154464000740d9011090f512120080c43d00752041050108040000d0031540c0360120001c0c1c0c8561001e40c003c0c4c145520b5800c001251841801100e01905003004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 589535989 1250 589534739 589534769
    0x30309040f0e010e07081f180305070b07170106050c0a0203061815090c010c05070503010c2a050d050a09051503060a06090b1c0f05071e0806060919 65
    0x5071907809088030811524643d441c0004c500c20203200480c0e21720a0300c41e0b070b8006010b403e070301d240b013624524100d03004803607a540d6402d4054030341841c1605c100100760199550381d485035418201800d00501c0500000140030400800c00104000323640b41a04461050034001d4998074181082800c1407880c610081d8103016072000c025040c88202d102150138001a0704490100c44488444400884240e800820a900c0b06004810541c0710780883c0356403922680950708110780e100c2c0480c1c25615960840004a6400350120000762800d000020490900c5245c607203c0c48050345886480d50001c140a808100c00003d01040250223404198000d040c098041c4050101e1602c0641c00707500107441452050140395000624a0322840d00601940c0007030030541d24141e05c185121200b4410907258900c0c1540f00d19182103004118070441d4402d00c225102d070707061ba0603810b041c0303401904c602018506001115090000d19214842a540c940c0001d480c03080d03040304240e10b00c01040451364001071000318044 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 589537239 1250 589535989 589536011
    0x30602160213061a030408090d050709020403060c11241b030a06080f070e01050d030c1e031b0321091707031b0809090403090807080c0906010e1e03030904 68
    0x54028800c44108880c800340d04130403030700a410b091000b91405001c12406020800181c40c0407000740d100684540c00319400b15503503903400810790304103a00c26940941e6030a5653b8145410100740014141c031140509034502030342a21030030142821011490f0600ba10000600e00150741094a20403010304d02c0180d01c0303144c00002840a0501d5001d44c0b1828001c0c06840c1a071054009803450584140340440c0d41560b00302010300900c2c2c4035028041e010402d40341010342c0070030341621007400b0040d0203040183c00c00f0510f040280110100e10750b0030f0314100d001525480800c0e070101200e80c01031601340c400780c624551113494002500c1c1c4010042e00420045d61840c2a2800c10340040508074840d84804110045008004404407020f002c0980240300801c00b01150740342c0000780301c1e4054440d04244044944a40c01a807070001190080d05541e030102903901d8441c60700c85515a4088424a80b003405c1d00c01c44008240d4003c40c288500f2264030340711224038401c0d41d050003030b603200c10b40191003080325554107 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 589538489 1250 589537239 589537241
    0x11162a080a230715121b110f100f09080f0409060504020a05090f04060312050c0f07050105070215210a1d340914070e0a030602160213 59
    0x604944114200700c009140c60050040280d20b0315001015012041c94440740380a80c40490b0301c0c1c03804002403c43c022070321281c50b100341102500e2445080034004103560380a060045452a40f401a17440010f02048007180007130ba82e14031070800c000200305030200c600c80c6405070602070402051100003003a00080c00401d40060000c90300942d10900426a0b40c1d0f00380f0040344a0402003000041003004041c0c01414810314443d0340340f03006000080d20955a40300d00003000014203042c0002100050f9003e25090200422001c1003a454007424840c0d2078880003a2080c460280000d00848076034032540b81c00280501651044400c4403c18102c000c071854803264842001c0721814003080c5010380c11100200300703400152804190700300a0842c04040042c0e0a40001c07003087c2e01c0480320a030b070300e18402c0785603c20b18600203100082c400314031040000414107a8030300080c442010408803d0010010340d4070003852004076034001100690324807041d032204041110b03017000650407001c03076101c140c026201 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 589539739 1250 589538489 589538503
    0x1020f1e1504111011030a143c04050d0b0601050d050907230f01050d060b0f090301230c130b0a020c0a0603020a1e031e090611162a08 59
    0x1003102c4010f10750241301029107440785040840000c031707407051002038480da001d0000b03c00c204c15000300003420b14400001c1c000c10388022003800c8800c000c90b008036030140340c844041c1110740020010042d08003420b007030106c1c1c116102050050142031686d80401c0480c1d002d80c04030341e500c444100c4140041d00c1c0038080240c1c0d50505110369215600113603680d440425030005203200c1c1e03240040402e14110040c0004640b183c024a00270840340b41d0710b0400050201caa80700401d820307140c0c1e081f116118500c0404042c210350313418013990f00d038030310419000c0b1017049a0035101c0c1d030200007421403540718070b40081d0704448030a864020550341c20000030b0504440c1e0b0009200c0000c0c1d6400c5a135004101d40b100400c4059015943c80b10006c5094180b41102948000c9a1f24046080c540360009240c0303840c0c1c00007250002c9c14190781440307940d02c140d250244000c1d07005003400601c081d070344113241400b45001800d4003044024054907800c01c01802200c2050550701000007180030035080d240942d240e403041e03912855 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 589540989 1250 589539739 589539773
    0x14120c0f0f120f1203070210050c0c030403050106180c09030602070507031a10080f0d11210304210806120c06030115080a15030201120906090c060e01020f1e1504 71
    0x8944c1c6003140304010003908982c03042c02154050721a921807403008001411004d820031101c4c000030700c0811105041000900000e500510007c940e00d07152000ca10307200c21000b20411010b80c1085025881c5a8000c90008112684107400581d0b490003814054180119600020003400ca107280c0da8014508880302e480c00f40c90651a5a800c440c0d440b0701c0c080d80c8401580308450103030029142142d00601803e01d8402e262041d5084d40c1d50000102241c40482c0c40440f043c07481c41d800032041c082806800000140c0c0f6603847c1e680300041c0402020007400d50304004120358070401403445a207a200d44144000e050004010f802d071a22561610b5440100d1550494000c0001d0b00786030014480c150503009140041142e48045944580ec42e00110360050b43e030501403158548403905000002c00c284140000c5500406094080900384a8018001c401d4440140d04542c040503a00036407040115004604030b00c800720b010380d21280100c0ca282820310b241c0c040c2007030740300388810401400041b03401d00b00d04803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 589542239 1250 589540989 589540993
    0x120501090c033801090e16020709060608011205030d0606050903280209070203040b040b04061403042109030227010807030b0703050c0412050714120c0f0f120f 70
    0xb00140c0c52000e440032000005040012660051084080f20110ba050060040c074128100c1da0b104c1340001c08030002503599031304c0d8036002065009101d90501c00003020309100001400080e151140040403005d040c0180403c0d0b8800c46030140400000b0800c0300c92129009000707204d683c0d80c0d00005059a046408510f010380030340300038508040b20845035001c0400702c041552180c820150207021780d0940084c10350381544810080401c0c0c8104da20064030003020351080450b595420070130018510a01b1100c1c00341111005d1040c040080d8151440000c00604201610868601786501320303120109684041c7d00580c0c14030040806034003081c907410f581d015561004050f641c0c0c8ac00d980780c0e0f42c0d11921019000300c0c401004078000c0c44c401d400c455000300070f0312103042c2443d40700d42c001401d004039180201c58545c014201000010060460b0354407005040702c440064a581c108030544071800c040f50346105a94240200f44581c0d80c00003030b0300380e480010f0034090402580300718640d52132107038a180c001e0f14 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 589543489 1250 589542239 589542251
    0xf060503030f0d021812070602011506020c0d020406050607062a08040b130b07020102070b010f12022403040c0305060f060f0d0f0209090d0305101203050307120501090c03 75
    0x5810000210b50001d45808095803030b0103100400c0000a41201240501c501c0030020044043c0e615450344450101004005e007000502d400406402c450505401c184841c0800002300300c04d5401280b4030720904000d64180602c03807003503c009802040f0700d4024950000e4003250f1901400182e90100040d01d0140c030201500d0036214035406c0018040124603000a003260b00010b00007035240ca101a00400e800300e00700406180c88c3e5486030710b020110b496000503903004ca100810b003c030760070106005001d101207140d90070f8105000c004015168010182c0100140c242d504407900181626603540d03800320001944900f0185842650710505100949040c800d42d0040f9026120b0008903038098035004140b02c010b0034412052000014107100d0649450300c0c49014800541c4406050920501c81240034180490414101804071072010308211903c2003190000e005503080b041e04800d20681604000d0317100e0780d589200300c0c2c0401201011840700e904007000001c5910154000100b01d0410b51014440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 589544739 1250 589543489 589543499
    0x9020c0a050714061b030d061d07090602030415050405030601150206070e011211090409111206131b08010c1d09040b01050f0103020f070c03030e0a061425060f06 71
    0xf071551498009500c55020008424a01c28880c05503c60030390b18800d40e41007104020f500d1040310915030140c1540c00c00380700741000655913110f110380d0080c0d940c1403140382d65041c03420007950781c0160700650708030340d0084c6105010580038000b07560050400a040314a59a16059941b84c0502c12903032150143c440e00c008100111b0244022150350340c0103035528401203122600c03440190907042c0c80d400c0864020400103401e60cc40380543e40280e40190655103050302c01c4802d0200da51041c581c0501c00c0c2c4c00490030b000b580018070220b40b07186904092500c805040c080c881c80c0100d04550320005466103895504000e25402a0b1103040000d501407c6074003520324030701449100350048400404184d041e200510080c41d18803100707100340d2010314005007080080700500119a1141c1d0003568440c0c030b031080c04c108140c3d002e050080b03106800d9804441c01c40c900480039190603070500154501103404501503075070500d0000010b29410b84c0000440d5001420708210300241410748050a0342400c290300821 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 589545989 1250 589544739 589544759
    0x192402070e0c09010c020d121107050d0b15010908030a020f123a09080d0c02010908030a091502070b0619060f03020904020d060f08010c0e010e010f0909020c0a0507 72
    0x2110b854442d503864074164416004454209680e03108a07031003d58580f000c001706440007600340300d0002a407030300d0520303c0440b004180b0b0801a58412442991041884070019141d14919500040c050142c03c1d040d5035004016107010446402030041380c800814400d43e444c1d40082c1c0d00262031005801e0322140740107410b29400341d04c45e18400c0c5049020002400d000035404070585191111a014080c00d248800ca1a0b40251888000c05031070720701c00030620207880325030b034402c00010b210980000c1201c4401755039601124040101001c018950341d168540603c03500090b00d84030504064021581c600d070314505110569015a40c182c007514400380a00c07406003801c04520305460060302d0340240c5141200e800ca000c1e5108681542c0c00035001d10180f00e954896001f8003020b40a50484401018103005081e400c451200303030f8000401c1020781c00010180d800a0f8110703400a820310300010030b5a201d03182960030064680c4481c00c5240300103001e901200002c1245044584605c2c29101c545541e240205 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 589547239 1250 589545989 589545991
    0x307080603010b01300606020703031e140307023307020d090b0d0609021602131506030e0a05060f0702070e040b01050402071a041514090705192402070e 67
    0x28081840003445402035000003034081780c09045011049551507400521506480b040c1c1d202102580c0500750510030147c0080303000321400c0c0e043c066100044e8890a004102240001c1d03054000304001001c1040c031482845a0401e4020500803030801c20001038200010940164031200c0b0381503000081441c95202083c0d40000c0f41d13040d41c0f00d050044c1000103214003a03102802407114640c0d60400080c001c419070001d4120b241d001001c08c2e90049460060001c640300501c01c81e0102c604d801100300c1c1a40860502005503111444c00040b900d4180c0406880c2c0a60000081c0140c8640810030094030740c01648107220712015400c6d41c1c1903d81d119000200ca41040c2ea00501d0003280f4030061100e82444d90107050680d009008585501c2c5c0202c550010071801910300391145140140c50b0000441180248488200d03002c0c02c2c01c0e4646042003000b901c94409000d858450429001200c0f5003030790034034012018091402a0078002c4060031a490090409124600094003554100040481800c8030031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 589548489 1250 589547239 589547261
    0x13210b0105010e011706011b0f0c050108010b0703050f0f0d06050f01031512050a0c06020705090c09060d1d0d090e090d020a0308070212040b0702030c120d080c070206030c030708060301 81
    0x1170b42400c80f681c2d509a000880c002c2a2604208415914100618104902003446402208591054125820031148090941c1c016074180103400e0700403c0103034022000c89d03400c10741500d805a11880150200c9220f80b02c0c141e0441110000800e003507080c0361487e8020401c5a90450f803074042211000019000d0310f03081180c0b0040c900b070302c580810284049184a80459219009a40301034502d543c175440700c00781a400c8000140e10100c000e01550030014950350304aa102c2c9102c5080c440100006500c030f124070b521409215031240d004400601d01082c00000300000340c0d06440559242e0b290080501c0e1032446150700ea6025100031840c01140801d00d2040560343d43e0281100c0140703030300e0a40f400240602130504611400d00043d00188090f8050805000201503071703641c0b41401d0042526007001003041600c40c004102c443c4149500010740d52441d140c1604001e541c0b5920841180081d00541002039000400002080320098030580118403900c0c4a49074042c1584881c020300d404c840b200092 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 589549739 1250 589548489 589548497
    0x1140f0406120f05010e030a02030c15011511010605130c4d07090603020f09150d170307090612050402062703070e0703060e0f010501030213210b0105010e01 69
    0x7805020504400116880fa40540004600c0050034500149568440440c110050f0404101360601e140144220210500350214501065060000011600c0b01c41c0e60304a042c000113103540107480a0a40024000300f00c01400c84854440019507100507200c00c000c018000754601341e048199040700f800405020a0700f05414280040b00e40ba855100c44009a211145007104201001441c80c104141006028100c2010401c5851403040c01103c0c00c4042c20240714042c143c0c1007000700c404032000d0300c948400480740d42c80c008415052141d03040a628464040340c0c0800010003075100d400c42c40b10f03c00c07501c136680c03420b4030120b5102615049071410b40300254004030400c18080d20390600702012000140c0b100500c1c15184025002914001080e80079084003000c1c5410001c800e60944a6440201502c0540000070b18003070b000b101c0c401c20b05014039814564003083d00307191030a0285461300038010304103074003041038030001c1e0080d00314859290444110441c6130000c1050b51140380a05031040301078503 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 589550989 1250 589549739 589549769
    0x90b030714011119050705042702090c0c07230102070f0e070e03060a05010801050903040324090c140f1e04052203110d090503030f0319020301140f0406 67
    0x44814203d24000004140709a00b1041014240784030350414580c03207080100304603445d00007031000361500b020111140c5c03044541c9001d003c2c204c110b010000564110b50030a4199522207003200389005182c03d000092081c44008500c100d9124132188003452080003c51103015400300490b40c80c005802004501002c0450030003030380381c00b000100d80204150400005640380d00380802d10708402183c02d04042c41e01d5000410140c1030070710400b504541c80c1c9025602d0d05056480d6007070341800c4041440c4400107000e111108140407540840d02c52688881040c50340b82d56070085910100805501c20f1040c58110056252840c1100b140f400300d02030740100c4001d0300402c070100002800003c0c410141c1e598610707450b90095424540305030800b4440c1d181c070000a107143e96110b2410227070500250500942d18414042640e000080d00c1d0700102c910560765580d902d003966200e2041030303a44000c1907240040300203d906520880303005440c50f410390701c4401040310b03030003000141c50043c880d4420900c10340c0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 589552239 1250 589550989 589551029
    0x23060303091e030703021201020703120b061b100e1609090b01051003110a020718020a080f040609210f1701090b030309060a0c0203060a0608030a080405011506020106090b0307 77
    0x4082c00d021a001002c0d9585643d4a80100301c1c003e5070003401f22080d0b50300003510000c06421804180207058001000c110045290020690a1007413030755690081860f250b2007080703910100050714107c02103410038000c01005520095480307400c042d4041c002d070a0320002240c08880c0e4801c40c504d80360002c504000d264644407d014041c5040b980c004109a141c081006100c01c00400802d8010b07160380c014400d807480d000d05400120001444100804d00412445200690080240360003901d4202d0a208945461034004010422a40700078140c0040c61510041d03454103040340d010301441912115000c1d05c400c03e003150b40ca81c00c2a5002c4500c540c42e401880429150f42c0a150441400383c1164500902880002c00396080020344900140040300d10000710305080c00340f241c004800f00d0701881214140382c0711300e890740202040306003004642c8000030240a02501b18945903001c03400b038801d15907141d110003030180c015401041246820b24240c00750504002030180c0845240003411081c0f02421 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 589553489 1250 589552239 589552279
    0x3190b0a0603051317090f2403060d060903020619050421030e01020d0b040c020f030403020d0c09020d0b120a0b0f10050603190b0a03081206040f2306030309 69
    0x503000400c0706880e01c25000004200a60417007070791a009100079103407125401004519550040c0490040d04100c0d26921100c4c58129528010381110202c035490f6034a20300401c03007a520205c0040c0c4082c0c18a0030f00c801381600072969502079456065020203010a0505020645900b5240100140e16007562121000e0028195446a00003450041a80d00c0c1d2580d1050076a0050100000031655a02403600c251400744543d5401c06951b00103032150b0a0007034039058903806030b0711010340968905002c000030081c81d00d9000c00a802010304c2107445103083c000c2c20000384080600a4001c1e24681044003c443c00042c1c0240d40d140c4c403410301c15907603030340000d5081e543d44042e095005c40b06070100003151b146e40e002c01541c403526019000c03071004804e17600700390b05480842c496503000b40000041400480c081c0403c0301d142c0109000807030415141d40340800c00801c504642c1035241c42c602800c1c81111013a0500c281224504040404403d032500d0003055102d10a040500d640080e540c521911400380e8 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 589554739 1250 589553489 589553491
    0xc05160201030c0e060c0c090702070e0703020a0c020901080a0303060803030114040e0c0a170d1701031b031e0516120b100308042402120f090604091103190b0a060305 73
    0x28610389018030406000c00700b04176802071200d12400350801c10f0010035900b0203184c2540d00001510040c0380d0a441e15030031155180014040004064000030070050583c05072012169040e400b038010f043d55039403558002d0300c0321980c51040300000c0c100000051461000015281030b641c140c0d17070040c001c140384020040207003110307900d043d079a014070101c5800c41d46d18082c08200070a0001d450010304802c4000b11401d000c40b260395032040c003045558100c4050f2581c00c40c2815240e01c404514a5821080581220400c1c1c41d40018030340d04188011343d1030030200382407081c00a48150f080f03500401c03603038680d00300d40741440c02101800800440460702154168001079000005070350b40030152a1241c81d5450070741e02c80d400c580700c000c488140848003600200503010401c40988094111552032019904584c0310340305d0025a00351021610143c0340c0e84500c00c0f24003c00200c0c0e4100b0070b0099031400c030071043c0c01c00c8520715469454064842401c011038001c10319144c9000f803042079050f08000042d001814 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 589555989 1250 589554739 589554761
    0x2070204060302030a0c18060e04141005100f0b030405030a0c14060903070309061e0807030b04050112020906100c0b040804030b0703090506010815010b0a0e06041403010c0516020103 80
    0x1c1c89000010160b14103000c03866615000e003d40c12412428800001142c200c2c08054420041c80c12108008040b204002180c010350b01520f00040418800c42c802e280031080081e52030b0040c9814188800040b05222150850709040c11203d1126501c540c0c02055000803540a04960420094804458421300d00d088600784a5448840c98805c40d44010307282c0301d8100ca2014040e40005005400d260704a20843e00070301c081e00d0000804e0350750f2840510082c4c5502014400d001c10f8002140c40303140250411620000d002d04100801d603034800c10843c0201c10b2040030307030003001c1c94000304149040403920018190741c2c80d100ca00e443d50480d95103402c0c0c000000c1064801d001c06120200c0000c41817020280912030139076001c181241d4a003405820070806902c25903440d40714400900d5481c0c4000202c0e0b044544403150745403202003258050751f0701c20000302142e50251001601040f000c0c0068081c441c1050143c0080003844604181601d90b40300c0c0740144400440c0003001440103600c0782d00600c0c1120317 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 589557239 1250 589555989 589555991
    0x108010c1d0a0f080106060806090402030d1d0d0506060405011d0c0d090f152901050705072402070801060609090203072a17030708070f09030b0114100207030308060402070204 77
    0x15940c3c003499400c00500e0b0404405030351546010011698405041078220b101110703910240d0070690300103596500080186405d00c14450400c41c0016a090034603820010060092820503a103480c00e543c0b00e42c003ca42c11071056181000208016501e04840740c080c1803110b02105154444100034038250308152031146450340c8800c80700d800111400003490344284162150441d001102400c0e03425941610300d804581c68000441e1000c0101241075082e000c8001e08001b599501d0a0800e0f50a004603504903070114003800c80610440188400d189440d05616130940318038549521041e405d8030076501c40c030700015902c0b20060000344855801560442c1c40c6040007011290804090401469110340820a6a5601c0c1840050046024409074502c420b0b5074a03a140d49814803000d000035001401e0701042148400b100c0007220b02600080002c4c540001a14119694400070b0010000404010703070700413a0780200c841100d5000154801c01d0341d13810740703072030201d9501d100501000b50401030059900c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 589558489 1250 589557239 589557259
    0x2010206071b080a05030433020906120f1602060115031a030a0804050f0402040b160314220605031021060906050f0705030103200402090402180102060108010c1d 71
    0x141e00c0f0005105008103600c801d070712440c050800350064136240c0d44852121081c0c0d14112801c1c242203400c0100701c0d01103200140c071840340a000c2100c4d8020318501d41803420540d0207001c4070f03400d4208500e10800e00c1407000e488140d644036003261035000038811405022800d07520400c5840c0650001130b106050012014646034949000918002440c6000d5800a100040900c25400d00140c0e0914188080e50103520345403804903601c800e88114800d003400b48136404d070340d00101441824984584191140c066885010042c0c2c90220700e00860401840d078082000c0003d40315018005691064410f08559514940b400e184200b14148031002020072100300f0002d100060200c5c8292301040d17000c1c407030014080ca4148071110854002034034040a02a00f4801000000c0d808001c0e003482c0c0c00e8034880d0070707000300142010501034000c038010180d005001203289900802041584100c1c031009030f08545590342d85010503400c071100d40c500c0400084001a010102a1840c2441158044090f02220700 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 589559739 1250 589558489 589558493
    0x2208031207031404033203040f03030204030f0803010518090d031d1203090706210905121902060105060f0717070506010b0408060c190e01270303120902010206071b 72
    0x11440d0f08507030840120704501074020368002c0c5040d4005480341071030034080721154102141052400014001070802204c01091820507120341c059174000c0d507000d8203405290300c0a00c1c0009280d0024000c00340580d100403408280401d103101e0190142c04d90320301521f09428900703002c401074040444910f20381c0458a400c0211020204014000c0b2069080016201d007040001d490801c42c083d84200304120f144814481ca903485801460b00c0110416000600902540340290412010304410303101910041140c09454550700e400007103c0c0525420f80e001c9a0300c4404000c0d1070f005205503140541c8060010700001000c00c080c07428610310b42000b8504003603d40e5580c92500c0c00c241c000800c030010100d000c1050036801c1001507000b04c41d0103030203400d1101c0b640d4154031180d280c50a160804c00410107881040c0d0040d581c00d04520610b621415500e925944900c0300c0022900c0100c001034407006030240c40c0c1915108200d00687c2c164007030312041d12490070440d281e01820ba1100020981c0e0707591600 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 589560989 1250 589559739 589559771
    0x60f060507030305060d0b270601241d0607050c030105040c051c03021506010e03100c23040b070510020d0903090b1c0f0b15220803120703 61
    0x205255526103644454602d001800e64202078025402210344601d640d00180001c0f03500c0d580719202003423031150840d403500c0160120200c40d4510150f8001c01c40041441186100b01d1050088650385000102c2c92030042280c0036031000381c4840729a80d80c60101549480c2c900d00800a80c0d018034100c032400d42d20500080c1c21151b0554040b00e400042e06001c10032820040b03140c8015104c0080341e0341d6980110b031006502c84420703010481d07212510340300003440e9a004600380d550801c8080e00310392501790305020300801800004d020380c0124440c076070700c00c44103404144a48483e083c4840018107161501109a255400c0303104122200d00401c0403d4904450718405000c01c0714203440041683c40043c00c014004021139000049448400c00051030042010b080400c0c2d55400803200261f6a080299000014005000350300d900100100003a1051510540a0505264545031b1503981e081122284601c415082c031816455820034030001040950340311134503a01520a081c04240d0401c409203801c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 589562239 1250 589560989 589561019
    0xb070e09010b0f12010e04020f030d05030601030c140a030905010506040b060f0c2a0f0105071a07050c0a140c040c08010603050613021b010f0204060c08070813080714060f04170106 79
    0x20001081b10100b10961400b40218070705440254090040d04c591f841e4000d15601c0014000e80c107243d10b41c10b03282e801c2072140010068007440010025101d0260000041c060503211106030344560805002c50300707905c0c00d4401e108100b5001004e03035140016003850a002608540e818903a03600032035003d05c035811800d1a080d81b500c46e0349424581d22580d88030030095054540d4002d141000010320038000001e4100c042c84c0c08921495040e8030b25581c0d1580116524400c100030307040b1300d0180205420030410000829001e00d110602660060003016003813200f12020140d203000000d014900401c1000d010340d00c86500f0500141c080c2034055410228482039a000c10f2100c402503001e84491601d2040038402c8015629407840700b546410b02d00b540087c003070085120080e06048000400c001000000b0044941c2044407800c112804c1d80e9428559803a00028410064501503081003043c4528008040b81c14044443c011941440c0c00e0168410085003c058041101e6680340000b0078040d1500800c0d03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 589563489 1250 589562239 589562249
    0x21060103051c03051027020a05070605130b0c030709091407080f01080304051537021204090e0307051515040504120e0105070c030507030b070e09010b0f1201 69
    0x40005440e40a07812042c00d41e0705226000305407500d0140010442c0001070300d000c445201110644401c1180e11500f00500481c020103a590702c00218819046d07040009800c242e070041904021075602e040d10307054130b01060a0f00818542c0c07044005003a000060018581000091170b140d40342588922440007201e90040c840c4c90308541c012304100007182e00400055111100d5100c0d15041d5251003003142e0340f4095809030030b00c9510b0440100038003014400a40e400341e0707690202c2c00d440b000e4408202240030300c980201a2221401c00303021010030300001d05c24a100c1c000c500110302d09850803030b0510041a4032001407445020402860b40802c0c1e080150030140100c241d1204454100090703560301842e070207007035280a6810602000b020441c4074000030b078040842e0421050003418a40125203034420f030f54004005444101c0c0c08020b0000018840042d00d03c10341c000040c503100d00740140d82c5000c084074a00d50144060005201d02c083c0240039007108444e01040c40c0c1007218034041e40c1c5404409801c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 589564739 1250 589563489 589563493
    0x3180105070c0807181a01090e2a0a020c01050a1713050a061b1d09070302070203030f120c071211010e030a2703230a020607080a1707020a022106010305 67
    0x109001c240c05c0d510070b20441d00c003070b0243c01c0e42610350b480010301501214824403001500c03400008184101d80315094040c1c03205003254070148029074101010380d4224558180041c800c40d2440d1042d54050301c1218a030145070340742c5000c24600c1018203442040e00a00c5130101d602c03034007890000203c0400c454442c1c2882400301050f000f4038007910b0b03d44086a024820308101040108940d14003848001d02d58001c020344402d0a01e41e201c4c00c0c02c1d07019100d054402034041c4400204a400b54a1041c080d01c0715581590a0380480d46a034040c40441780642140a070070020404060344440e40214111080d40c1640030022400d202000100c0b800d581003a035003040404c900e440b10307501002d8040800002d018075501da2108807415602c913407105081e514051a4031040215003498103000c100302c045070f46540141407598641041c500303d0440c0c0c01400054020801040141c0140000f002542e40708082c40d500820454515808204902c81c0c1c40f074815200c40100f004d01101414188200b0b4061801b447c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 589565989 1250 589564739 589564769
    0x30f05030d0506220e0f240a0504081b1c030614040903171b0f0a08090d1b0f0203250e060105090402180406061d010203180105070c0807 60
    0x25101055540080299100b60601e40304d03190003460b034140f0740e040450303001c40015040001c2e07a00340d4941404034802118500c910f0810310004042554200d03e0203130241713182d500540b145170101013941c0d01070320014090001803041c46043d26445440740400401c510482d0002c4031003d010000d510300046010000035282c15050141e41003214070300e03800b604e0a5900700003040040c0ca0041402c841d1a2201c2144909c0d080450140d803c0c0401584a4030716144000b550341418104008132503202c00c20117004641b080c0001135268a000c94105083d00d01c0c0e85400688000c60f08640c7d01440b0071400440b0000040c941440150701c00300301c01c103110704c80e0b92103039111782c0e0b4506c203800104006680000807980c00369042000c240d0f4072006540900d00142d4000d42c07102072111110f10089400015250040d00d0100c00003005a030003501210000d0711006131034030155041d40120b07161700c50700100b065031540b01d555020341544144001d241e140e00030101c00d45602d444420041c10190954070003240c400084c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 589567239 1250 589565989 589566007
    0x9010e0106170a0f170f030105010912051f060b070b0609060619050901050f1201030201031503112e0f0f090e06090709120303061802030112110a030f0503 68
    0x4850240504500c119545101d240d0740d066541c0c1c3c10043d000244941d4000f440c18040101070038550604640c86501d0a40b91808070079200c186170402d209460000c1c252030000920781d0880c1082e41c2c8050340001c003030541c99802c1c0000d0724010a15861070001c03541e03601e50009001c40c03068007514010b81304007600c0e03080d41084030800c2001d00001d0405445200304104010001c40640001070808056092960300c400f003190040c1c4190241d0a000003240d00001000c5034000e00011049060340d00c00d803030800c40318140058001501c011400018424682c007a040340081c0b400da8040d0440d00101144820314464000e00308000008044501c400f0410400005240c43c0d0050442000c8104c60320b070189c0c21524013a030907007103e100940721038091224900490a41481805918060400d001464010038014034004000300150310800c02013440c8901c11100c070008074003c40c1e0403940050b150300310046094580301c011141c900e5643c2d9225205e04000400240c190300f030310300c86c41d0290700596214a182 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 589568345 1106 589567239 589567241
    0x10f0b031602030706051302090718061805190311030a0f0312200a1716200d0309061505060319060825060201060308070809031509010e01 61
    0x410100161f0307003442c002094840d8400e88183c4940d0b6650302c8100e5040350010201401c0708006c840030406c003803041241083d81031140520380c0c40195114005440d0baa07900b0180345c0000318896081007840340c00c1d2246605032009070b0141c00c01c041242e03102007210b80307140720050604c400082e40c8101c801d96980104a40003107991006402c0c101c80020100c00e40100c491030340000d25551035005503c0080c94000e004100c1e5640090b03070900302d15000c2d602094003080c0c0407d25240d5071414096010100580078031001541c82c00105a1214180f001c01e4580c007860060b566a070b8504100a01d48a81c5c08590344441d001c004003084910b54000c2c1c074060116940402c0d228401c0e0100000d80301c48003a401c1b901a074801070484109983e94401b40d00740e486921000c0c005020500403540400c91000040c402072400800365014100210032019005000f60f500c02040e80d940e010180210340c003 = true := by decide +kernel

theorem cover : BRFrame.Cov 589388489 589568345 := by
  have h0 := BRFrame.cov_init 589388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 589388489 ≤ n) (h2 : n < 589568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
