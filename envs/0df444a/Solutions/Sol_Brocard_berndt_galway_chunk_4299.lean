-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4299
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:09:51.131016+00:00
-- url     : https://prove2.me/submissions/72afdd6b-0aec-4aaa-a3d1-35be739c0266

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 773021582 ≤ n < 773201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 773022832 1250 773021582 773021591
    0x1d03060709080c0105130e09031b070f120201020c01050c0a0b0406050403020c0a3501090c050406090b06090910080a030507020103050711030711121b0405010e0121030c15 75
    0x11886051140c0f212920341000020803203d529009485400c030101c850320558907509a0b00c80c0007550071070154001d01045000071514140c2c22080018000d010380743c0d52480400d0785a41d946105000a0b0308080c0280176801202031040c4540c0114003410080c1c0c2c1100584550b0462548c1e107011005046504075049a501c006000c00c0c158104524040034000703070317001c03613540d070422208041035200a0000511070314200701450012280c10200b801c2c500c00385000b0b00a000c3e582c80c1088060b440d074040c290159142070000074000e1402e01a0360030003800504194544038609050000d1001f00400881c100494151300142c0c9000030072403512028000d60741c954440001c0d100040684102400d00d00810032000c0340030207142c201208a8034016401040e400320081e441001c28811071a80301003c0041c0039109060780100d01c0461100c5c6240c40c01c0300d081150341c0c1c0320554501001c07001e00a0003004400c4203001c4c0c0d560b00200c800511440c1c0a8200b00c0220305044c1c6e41e001500d81108400e40325280c46 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 773024082 1250 773022832 773022839
    0x100201060905090304030507090b1f0806040515010c200d0c14011d010503070e130c110a080a050d0209150c06091222030b2701060311011d03060709 65
    0x303803180c540c10883c40c40c003551070249561a1507030342d02c00074091903021540d2a0042501e40c3e13242c0282500d120701c4405035944c1c51910a0004d00801c074100d901c50701450508000550341c00500c032185404c03c074143c40d07000350302e52991103a91540404054001c207460f007100e01e2035003a5079070381082079490340302e40c8a440301c2a0900a0342c3c81c440155141040c10b00c01a1082500600d000040f1280a1030080ca006500c0c0d560b001000c8800412110700d0301d801203454084280c940b06207401c40d5240041540302e217070361010b1900602da604c601000001d01071540501100d000b080c07160004107510713102208007506100c4c00000141030642d00480d004051480000c00300b4441c0c00c1070040583c0148a54080c1c44902c941e1050601184030703059403041d400f000c600d00315030307204000c01844025503000003c440f261b14002805201c00c01900404c01c0b00804a018030030000201400340301c0a49501a00000c0c00d02902c00056030fa4180720346507240f6500026900280340d460070045244248076940e540344a2525 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 773025332 1250 773024082 773024099
    0x60609050103030908010b09060f0315010b0a2d031d0f010b0103060b210a0f020f0c070b040803040b160f060b010e010e06091201110a110d0906020d11070510020106 72
    0x404c0e03400461281d0420070f000f03455954180000b030b4440000c0d513540d81c40303101d0400080c3c00c12041d10001c49907014a4070000c40c0002e52400501582000da1311044010450050b902500b02d40762a95869203a81100003000c80ca48240c03c035084109004100314008003507a44014148001c10069010030784d501e5001e040f8030341c0d0600030b0900810805415074901900040d0010301c2d5200000c26011550304440030580701c0c00d455000c0c0c0ca1003a85a00304544900e80703010039900726030208003124560b05c1901c0000c5626140c42007100c0c202e0714000000c0d49000d241c070003800e4540d0030440020a07070400600342c0a0204125180f0748001034440d9000050301044c2100141030b800781d41e0103160420100015411450329071100f02d5031421401c56413904401810380c4a54050a40840c4002c0e801e031000c130700c2c41c3d0303100d0708681c2d41c5a506009a0a0381c60f454480041240d00d441c0700c1c8a07070342c0140e1085641c0201507006504949031041e25100350f98030a5103480102e00810b04484103500180e56541c8100030840 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 773026582 1250 773025332 773025347
    0x402090a0f0b120f06030c040908220312030b0616021f03020a02060718140d0c0e04050606010f08010e0402152d1905160c030311060601020a020907050f0706060905010303 75
    0x8186504c12099814008082680c03401ca00354984d0003607950300320380002c0c80f421109071440030080c00d0180740380f100800d0150f9030f0500d640c481164140ca9070918080258000e006500e4100c1c4e003d4034890410a60046000b195400c8807400e903045541c520244800c0e989082c80c0440340d40840d00e0160340e680350100024a00711005203a4401c101200c80c0c441c45d484124589981110840301c81c11800c03111140004040244e04503004200d11040c1400180c88032280d01c01900c2140a88180e50550707440c2d03001034461005007510140011042001071003107017240480c0680090000d030400711800761108108e0280e5110038042c0c101648441c0c1c4c507510031210240c10000794a203000c040d500b0000d40e02a856403240240101100303220004c90034598104250301001c114a8000088a05080d5a8100030307040303003070643c02801c40303018180c005011035000003508140345501070260f1849680d45102243c480d0072006052380302440400c00304010030941d000b00d001910581e9030004d1154074514015002e10b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 773027832 1250 773026582 773026591
    0x1b081e07080711090f0c0f1e030115170103170705032205031612110102100c030b040b240a050904060305061806070f14070b07030f11070507050402090a0f0b12 70
    0x9903042003042c01b800d82000c1d602020140c42d012900c40d60403448005058000e0300c0c509491110110001440440b00600c1941241c3d07552502c980c0001641d40c3c40e09030110900014200d64050441c500904c120000103064440c01002600d0400030710104405c40c200c440c1c0d80807484410581c105014900d814000500e500350340c0043e1041017454400115000000e8500141101b4510b05880101d44d00030b214910411074143c0d410400c0000381c0e84054018204201158060303490309810950600349208000c01e510700c0c1d0303034400860700841d44031519a580a0552901003190138850020a500c60380500c0740074504c15405800d107882c0c136003d84401c103801e90390ba45e000c03944031000340040070f500b0000303480c4100410b10300b0260721440107560814600c10480020711000703400c8204501c4030340c503a0081002c21b001940501040c035010301c0d00c58540c060248042d240da00004030400030b615140d0700400500001400300e468840e030320100581510103561050740b00d074800144030342805511540c0d15602c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 773029082 1250 773027832 773027851
    0xf051921020711040504060b03060901020d06060503060609042d0f0f090c2c0405010212060a0b04051c0204051312022103090a0519031b081e0708071109 67
    0x100095901c2e43c1d48074071844424640540d0f90740d40800c0502ca600d400c0204012405000c8855904150003101d000390301214070420f07140d18011001c115a48603204590280e00010807060a04649000b044002c18101200c004603050b08614440003c007564480441c200500000090b02d80304c000003803042d24550261090000d1416940307100040c01f900a220a6840c50010040072658449881d00b40744003c5001020301450b543c20842041415002021084d031f8850590110392503000502c80e0008441c000c2d02ca8103201448140b01c0b5080c14014080c00c03c1c0c580100c0404460243c000c1030440b081034441c2050381e005d14841c0020722564580c1c05440400b20b2000f4946100400d880030301c43c40c0001c890b03081803d800401701e000c0130000c02004450a410405a84000c408200707490020f402189088010031140c0d000201c01c1c0b03044040b002e103071981101301d4901d0909086210102a144803110b850741920510004010078140d0000c1c00e022441940c506014005c26010440302c01c42c02441801c1e03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 773030332 1250 773029082 773029087
    0x1140108070824041202070b0d0e0c0d030504091104090e07030209280c02010b03070602070612050906010b0313050a030309060e010524010e040912031401080d0f05192102 75
    0x3580c1c20991003140e119801443d0020a40f480c83c40480c103080c00c580c0854000400440c9c8030180b94190351100b06503c1c2c0c00012500201040f805100300b9090136040540459428002001031002c0381d08444514a01200f0b258a055120201c1108841d400310012400340d1107400b09000718100180f1031500641948211810407000c010030b980c50036041d013590301110b6180c24661525034000d421494004000500b524203243e141d1350b000b580c40065224110020b0241201800441160310459021f0981540a80496800d00504400591001d400b103080d0b8410180400c01188084c840810101d20a42d4080341c8120036081140913102c900c5426491a40342105019201c4181540c0191441ea03070030041c01e0140003a0010f882072841d00c2d20b80c03074000d07007032130700400c02c0001c2c10a030803c0220b41600e0410031000700c0040130362500400d0040d00207076401240d82a41c0b05004401011040140c2d02c2c0017440c1034001c84079000c0c0d03400c00001910214105c4624030515980ea003020020007040c2040450 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 773031582 1250 773030332 773030383
    0x1e0e0c130507090e1e310609021e040506041112060303040b0706020909010b2715131a04030309270e060a1119030b190b2101060903060e011401080708 66
    0x86c00700b80d031102145403008100d124401000b6003a000307000300300e80023054040f4080c034240040010011501100c3d206130300d4100007403018034051251102c80c0d040182e506040080068031080c040001501d420380c5403000780000039980c0b001e0300041c01820310500303001d43c5075246881170050703005060f00900e5001d003041c040341e248012100040b02c40d914009100d0f60003204104c0c003181002e0520724410803c08400500d800c040c40e14000b030071040340d03c1c06c04c80d00340d488184241510f040c00b032800000c0c009030203024200311003890300048042c00482a041c4001108200144000310b800240100310141c00420411500301801c1c89840c3c8003087c41030080345803060740c2d01001594148040c1407820f0640c1c5407a030924644845a4a100c0840940001c140e801e858070045500c0d6000441c0e440c660201c400d4070380c1c1d03101242e103864034100c070500d40360442514103595a10000e00071521108059650340d11611310500c244521550090040f07901924982d81807000302420600017603a1460018003103102407 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 773032832 1250 773031582 773031631
    0x181202010f1805030102040803091c02100f050d060909021c0b0a02130302030106080303180a0f0611090306070e010314092805011e0e0c130507090e1e 66
    0x405007001807415001c00007941103090360303207409500001e03050340c4042000303e94007500100404c4254002c035880d150904a02c8140803411040310b100a42224490f6182a0000d00a407003000c06c04842d414418100090060038004031036465014160840e1940300040550070a650010340190044003201d50888207a110002400006004079a440d503001a00c0b1781504140c20310000a10350040080c040c03982d80c2c007450380d500e0300151010020044444107902022400181d61040d00c1c6e40469209080750803612600f00a1541c1103060209000421070884255010300105110748056200d00841c004460001000c4980380080310210301c810030288414030070001244410b860000c0c22000c109078000b003c0088080410200804945c00c100b400700005540b1101c6641c16211480308206000b0304200c5d260baa90207480110741c02c00c60800078811449100d80040354007071458200310640399681c2c000f0000c1c05200701c40b0103007015103801d4801c3c0798480700071550317421090134186424019030500c0c90b0b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 773034082 1250 773032832 773032847
    0xb04111303031b0b040803010504060503030c0c0405060d15060e070e010914041e0603020f040b0612150a0303021e0703080a18181505010f05160204180318120201 71
    0x26080c8103155040f03402510101c040ca002040e8804120800340c242807030714003c2d0ba0401e0196034811410030744041100d0600100313032460030b0300074001098030b15844000c0c03000405026198503001000f1380d01c25008290400c0064050303101d110400a966864010003d00c00b41d000340a0307004008803103240d000580e17031000388003080c0d1b40c00c1c20750701000895039400980103260101c06905e5039031010443c2400718a0030340c0020200c81c001d40d401003188540d03108000403500766484582c0e00c01401e105080100b0840000c2590015411800b0b0907000795000006a042d1404c1d401100140c1c8400040141c4241500400200c00410350003040f00c103041d9585d84208ac05044220070800c5407850942c01c02041c030310301130070040c070b44480c0c01e188000c4400795800c082c00c600b6911201c04c41c0401000202d5510498a002400001da0b50300c43c2000d4041c40020b109065914050b41e016440c1c050074041510b5880403240c02c01d100c0d03100e40ca21180305000605180246500c2030034540d1001260f8000f50360007151 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 773035332 1250 773034082 773034089
    0xb0c01060f08150a140702070f0b1201170c130614040501060e1512040c0905070f083403050906091c0c051f05091612080a02100509010b041113 63
    0x10f000c0300e544030b41c8000300900606070b43d80042c2440c48140118640c01142d52030555030400034001d103031505c070721611299100e0103401c03054180c04000108080048568100065040c000590701f0070450400003030146114418000300342a600d444c00c000c0c4480340007a20880100569040c8206e41c90310740040c0000200705495802a550b1385210000c5051000c2250a40400d0b201021070390b080074149503903000114041c01100314036140208070410300a0582c00c0902c5150f507034140303507a5a04c008086402c0d12504100c86022403c0383c0c491400c00e0689407400a41d03e0f10703640000d180ca0464481458810060482211a0400405401c1c0c5900e0421240100360860800d214021031078500249440c014040808000300700150340e00c2075000c41d03080280100914021514821101641c480c0e84003458412407031411a514480800194404003401c1200c1c45030041d5109440c1c00712010056410840b0a9482a5500d44d018002407515220325820410496482c42c00e00c00e10902c1e10124411501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 773036582 1250 773035332 773035363
    0x312041401050403030b0117160f0309080325090806040305360a05010905030a02040c05120108160b0a200f0a050102180312040902090f06040b0c01060f08 68
    0x40014140444461a9008200410001c10243c506410300500520544085600040203039003040c0c5d02d1112400c40c0c4e4050351040031807a850480402054030f0080007106020305054442a1000203e1004009548103221100c1550200511604048416003200200740c082c03140000b020b01c20b00781c0005a050b0b01681c9420910307a580b0031391494402c0030310b0801e255021021003051180c0300d0403e05c0001d03204001d017900c002c40c08603266401512540c0c80c1c0d01805405134440c45c0c480001d071600b60084c0550306202d04107640782100e900e107440c0500109810001c0c1980c003044040c108414507010140040c02100c5d8083d0900c2c00d44000188140900f400008024004c0f20710f13400d40800034007660311107c0c81c0100312074000c44c149c030b04a8040d400100480000c1b0f04129895482c1e4100417482000c0750544035441458641030440c010001d4200502c2d803500810040341c80190b54954400034000382070b0364a001074442c040c046c405800e481d41500601440c0301001c408001c89a800242a04000b5008 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 773037832 1250 773036582 773036617
    0x230406121104030f0827010e0402030a060e100312050f0d20180f0301050112031d031002030108061807090917070c06091a0901110a050a1b080c0303 65
    0x14103007626a0007103070005010454241d042c282000b091000900c8003080200d1000403008018941d106134200c00c450007030110b41007441d001400e1425500071903110440900000782c02d81c03103540074404940c046507003458545041200340280300404641c03681082203490800e2504a00011080083c02003039220102152070b41404225502c1407045071024041514407291581400c08000c0070001140c0109401240c3e00246442c0d142810301480c2d0581d00c401c040301030784181c155070480e01d0f0f00c0001d41c201a01c00c0b80c026080490381c2e09025010702e001c85a6001750312541030505080c100b58020b0042210600c544c020380e03d003041c02040311404c440308240300080050b030a0400a840c28540300340e40e074540500007000020002c14075407040a5440c00d50f284070761551202f203494048040701d00340c03501004d000c2c0b00b903664030341c890344050252010560658600503c15560740c0e01e8203e2040342114040c1c01d424100e481020440d44003001440000c004080b03003041e41c5c1c0826100e1164540c50100c1c0c65030f0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 773039082 1250 773037832 773037851
    0x190305030406140901150b0c12090a0b0705010b09060108040b0a0518030f120f0403050426030304050d3005060d080c0703050c040203012601180323040612 68
    0xd502070203c0da4850302d43c3c82e0440c5043c4000f580204482c0d040300d000181e80036000300700000d1150550b00102c003a100200400c103030342811240581c0240400c140d00005028010401140c00c2003d8006544100004140d154000c030403c04030703103001002103040100c0707601000080f503603400c175540c0c1000b54040b0001d0320341c071901082d00c0c5407103890701c4004840c07000184680141c1c03840d10003490004140d5200d448a91503030304500e002444180ca019000500903c0140301625041980c41550b1008800c0d11241c210700ca40124203507041280c00b944d15400c1891080341d00e5400c010a02c4014121246804151500e454066901c80c81c246003c0d107001da981002842070785403101d540b00300c0c98005000030b0b1500a100702c0240e41d050a0300046503240220700347e03a101820140240c03411707070b0519090410004070f610316160311a10310a041016564032044d1070301081903010080e403a4039004e0369906040301c0110500b21030440d40b4081a682d2084c08200402009500c04400c820085c103841c008601c0f6040d = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 773040332 1250 773039082 773039093
    0x60e071b030201061508040209070908071802070c09091b153c030e01090f06020307090f120303050603060907050d0c0503010c170603010b010203160c03080d0902030f1903050304 78
    0x407542069001307806001742004c4c29600072100354442ca200301d40138415580c80c0c1000329844421886039858992100805104009400030485c00d130a5843c4e00050030b0070f45030346503e080d0280035071140c0001b0b60b41b15141d1090008103010400b03940e8a0440c800d016a24000c40e5962801e41c0d9003d41c405c01c240c0201d0306500601c1d0040651008040712842e800304440028410220b03c4c03500303c100046460b01e081e038030400b50180035642c1429000103968401c1125521054040c0d0700040c241d50810020708804140c143c44074000c00040d14411051156403000c620f00601144c0c0c018207460321136813045041001c1c20b040003542000f40c8005655828040c031480c13130060040d01d03960304200c0c0d140d420151907285241c0d1001c01810689800c1c00d2580c0c450f1924401e0500301e420b403003c0c450058000f00f00705078404281110303840095100380e509400d0207660340c40e6038403150485c4001c41c0f581520b520034002986010047c46c035200741408003500b0864001c01c0383c43d0a00900c00001410f0150100010382400b8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 773041582 1250 773040332 773040341
    0x14070609020a0308092b061a030109030e0f180406020f0f0a02010920031216061d060106111c03092003060109090503041806030c0605090103060e071b030201 69
    0x607030150103107604035200c0c42c10b440240c002c521410b000c3e42c8071a9180300d40000748040da03441c1035810740c101d0790441e52a4076058040c0c030240490b240a4011702c00c000e6400e8034241f09903000756000f580c41700180060300301004009038003407011a2040d40d5011010360f0245845031102d40040e448a40169a08a1818121114001e2014442c0324100100308080701d1901034100c80c400c3c80c8114a22145404c00f62103929500350000420b80d010750000e0001f0201103000310042c04c40c40c10141280c0844030f5942c0d03480003a50700348868110000141c1d1a2008040410800f60380500341d60300b045e4081c000211111a5612117500d15045146001e02482c0000c1e4081da20070601290000110300c5a80b0030003d6200b10307004c0d800746060107841008000602c44c0324a100392921254404061440e2030720344035010903001c05403584c43d000b15a540300000000783d90b04044400809aa40301c0320380360208903001500b00c1b8070a50080074030a0412040210550f0722000032046142402003c1105c0517072418200d0040 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 773042832 1250 773041582 773041601
    0x60114030c04321b0c060402040504140706180b0c190c05060c0a02031c05070b041104051008070504090807030c060e1207110f010801170a05120a031506140706 70
    0x35180f03c40020009000718015102e00765003001450480d403881600c0d41d8a100f00c0013018550b411030307070115005103043c2d082107802c1070052440a0050009080260404040380c5c40764000c01c00c1480b04081c2c3d0781040c030740c2c0802007498085103403c20000191054442d451240303a14100c1b071100d42903070200160b41c140b5401620020705004c1d190f00810555607a5000c0b00c080980c030074414209240000c040c04d1040525039900c0703540b183c0c18015a0f542e1038140000180048443e1410142046115180e40c8501445920a0300c203d0f5001071805505c5820103000d40c224502446c2003092000c0441c811104580229515107424100304556003000f10092808064200b11801032041c0b559803800c10130098aa0f1a015001304070303c9a40c1c003c00c001c00000c01e4050b02d40403444844c010071041080307030f11080100a401c000e942102c0c4560707403602d0a107403d012011491500108000803055450711401c0520052003509507030440c14040003a00c2c04207194852241c180c0b0014440d01004920340011108 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 773044082 1250 773042832 773042891
    0xa020108041703011d13030518130509010516050306032109030a06050106020c0406140904050f0708060f161e03060506040821070f1709030d11060114030c04 69
    0x1a540c462800d090f0030310700403170245d943c2da06050200fa0078140e401c004611082c0d1540780c07540303486003580d000071610241141da01d600c003808041010486c0018020544142c402200000340ca2508103041c1c0700c40085c2c0c001110800009004005a40d100040e00c1860350400d1140601a0400c40c24040c4e803d01c180740d44d10340c140c05403441e1001008056085039040e00c2040d0291214840008144001c40b8024480c0300c00100c401942e16040e03050120060390441d001d02c060f1030306014001c0c22a80380c4490740c0d0002c4210360142d81000082008031b5142c50304102002d060a10402070901d008080c1140a0400c424640d1300800655145000f40d0240c1b008010240496803071746d81d10404282c4540d08a80046014034080c1c0101e4112a9000111400c5581c80b4071183e1f2017107216151412192140c0003901607000c1c0401c150a0035503020043d9140c807220b16991040002000040d280c00c010040c0e000c3c5810907108640b0380d810340c0e03000c030342005810003c2d10000744c41c90320003210022003410f4000d000d10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 773045332 1250 773044082 773044087
    0x1030f060203182a191e120b070905120c01080606090a03080417070303020d05030a06090203040b460f060806071b030e0f0427021903050a0201080417 66
    0x400082e18802d4402e801e9449500410302c9030210103105101c100b1403507200c141040b843d000d00c1326010b0000c8a00e6425800c40c43e501006031940240c000060541f00c1c10340e9400d4900c82040381055100c49072101400701603030040d41048480100c02d5484140c80c65960600030004005043ca44452041d134800c0c1c00010070901a8640e04c5c144412103601a000d01211540a5060300c200500f0000c0d020701229410b42c003d084003101101d089038160400342c00e4104032501c903000040c860210f400618040c40c010a25002c0e641016060030400d204004540b1551740703444c00050000745405683d40707500d02e10590030507844411586019006014013400e6601340e0340f9011700403c2049000038120300c1000143c03100100d41070014031550b11007540c441c000740052b40e41c400c0c02d1000d0901c41c140300301200001e800400c030546101050001c11141e28401d1540f020100e802505518181e030003201d401c0108089544001d080d41c881980b60b9146920290600a60001107010004030811079903c01449170500c64 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 773046582 1250 773045332 773045353
    0xb0a05061b0a08030c0a080105030f03030f07020c030a03030507020c011103040506070311160503240a0902010507120e0f0402120103060207210e010f020115060e01091d06040e030301030f06020318 86
    0x40307a01b14080c880005003e241c00030a01d8140040c1d0840c03038074803000040d0304540d01c50084816410300180300b007086010308500103804e600d007004020f903443c0c42a200840c41e840c154000a24000040385654100a100f4102c26628040403040780c003520821f41d5650341c1d50718141015540d41d4a1140d08001a100f50b080050131034030007020300c000b40c030f00890941e01005c03024030a02c0c0c40c11980350445104402d841c00400c1c41c80c11103500c40380b401071060401c60308100c0741c0e0320f410400703240c50440b40700482c01c0c52194442c640380c505404c103640d0300101c604601704840461200840e80050000400c596400035290050006054611256600728165a070403041d049000400026003005030901281c0b68058680e030450044c002d0f414a98150381c401c000482c83c1850464104280340a414144038100d030001c207008071503100b810b0b1185a0744183c0d8105050503420700045031313030a50b4600c0d000c0d0020300052002400c100d9490011941000300941c590711a50308400150b215118040b20b180700b440b2000303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 773047832 1250 773046582 773046601
    0x130e01091b0306110c06070309170d06060813050703150b0a1508150117101a07020f010c0302061803160f050705030615011103160c090b0a05061b0a0803 67
    0x51007a00e03c141010300040d40248165901c6009030700e040c4686420000c0012441d07842544001e044a0180070324130342078034900d03210700da0700e502661001180c152100400e00403940c11001498005000c1d0202c00102c1d6440c2d11800e03120025400005c1c140c1d4001060384205920035000f1070010b0038011b112071401c1b5030720821400075000350200600410044000a041c0300c5000d6035803014880103031101c403a00a47c00f1320f03000001d14000c00c000b855418500f4042407407890743c1c010b4010701c01a1949140d940d84140104a8803035001c03000c840c1004100760300100001e0340401c050b6004142e00c800410000700e8204103c0c114021501c014644000807100c01c8148289003404400d10350290043d508490f41b20301c14151038060448103108410b00003641c20a055209200ca050314144600c1941d0a0143e03680803c0d10b45c10058409441d1285036040c1445040754611034000b060b0011039076031210710714190106803d0300480030300c529500004000041109020b004911240764801c0c44260359203484000f2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 773049082 1250 773047832 773047883
    0x80a0810080307111212070606120f02040207021f0e0102190c0e0a0e150f0612120a12060305060603150f01051e150408070807050612091e01060e0a0b130e0109 70
    0x70340d5045e027004400200c00d00d40410405401e84c018071a0781c0000041d0302448040d50000230120307080b054402e030151006044109944400c0a903941d0098900ca2090009107070007015448018a160000180d400041110028204a490210720045103656094280d40200b002c02c45c0301c00c880c002d1487c0036804002c50814288100c10303400c85420b080c2c48903818000794004041a24400b640f10b00c7c45404149410f00290032240c11310300d010700f80b010007400107105851940e8400c407025440740052000500d0b06000304910100104c04002e5140703811412822100d070184903150143c1e0501c0030103105449104010314001e03030040c101259901d1200305a01c030551103031140124a014501c2d02051811000c10305c581103420003440c05041092070024104102000b0f0400c5240d4840d5007040558042c2c02240c0c0d1b6a9040ca10000241d801d14140f6403d14048004095690b00d80c9000360130078450fa500c04000c2138400303259000243d1000d400381514010000301e0030103489009006103041070100404034 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 773050332 1250 773049082 773049097
    0x17040504062301230d02031e10031b170601031b031a0a1b030c030f0b0315040602091c020f060703140a050f0304080a0810080307111212 60
    0x40400400c0d41c1e950358500c80c00740c0410400360146400b00419100d6100340c00500140241444103001203241c2006000c5036032051140400481d000b000300710b00f10849007541c0c80005c0d40c490342640d4914001030102e04504003804020011002c6182c039a160035400a201c80c09003d0750444c458480a814204a94079102480221006168040b0b002e41c081c11000c07504003103079030091078a100c1c5491308c2c03106400e0b07642c001c0c100522180ea40d18200340c1f259030280741402c0c00e030391604c0016040d504858014251540300d0008502c00d0700340004005940c0300003910100c1501d4001e402071490300d075803800c3d50103407198200482d84242e14030700100c6800554030b2902503d510888800803110742c04000e0201174001c0c0724015010035054803c00045440c0c0c1002000035001526013145040c81c1160007500700d030800c0d9810f8031100e102042c1c4150194000b034659400c503403503200c2c52550616081444d5541c6c401c6080046c110302980502810603203950342c3e01e1400d500b51005840c44a1070b2400040d0003070b0444031 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 773051582 1250 773050332 773050339
    0x3020606030f0f0d050717030f1e0103080304140a0b070203040608101401210501121509150c090308040e041205090102071512110307030e0318040903020703170405 72
    0xa031060b0751035030000b501c0c8100c50307680b00034042e00307120941c01303850f1074014400c1504c4c046900c02c4c080103110300e480025480368802d81c4c61500c690500d98140c80250404001c0c0840403003500f40140046040c0c2420340c3c2c2d003d0b85c0018042400c100a035050b0f42040180304c3c0043c0045445824041483c0c1c0201c060001e907800f6641c1c100d09903030380d00c0705d0740d884226510402940b4640c94031180003075441400c0c06054a0000040c401c914050101c149080782c40990004107011b8171100e00408010648601a002c403100c5241403243c00c1041e103400c4d04075010f6508505c0480c1da41c6541c0030b4000e00402c40c0c00000c2d40c0201090391190b6680c0144c180c01441150308441d4804c1481515407444c0c010b0090b40c00000041c0e00401340241000d0800202849605508042c04020458200040814000d0b01e20f11035450b10303036645905080c2e00c080d00755078060504850942051040300044500c40304a403042110803a00862901886c0c00d0981c18201c843c7c0014001c01703541c000d05d0354a661a500240304645056 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 773052832 1250 773051582 773051593
    0x309020d060507110118021002160e060f010c02030d11010e06011203091203080a020a034d18220b0306070e22110c100b0109050604060807020a08070302060603 70
    0xd01d98601b00e460282e00d9540380c000c40d41603000076007418040d1010210309401190a10030541d2140c1c03824880f60703409440d60410303800c00c01240d820089d05042580788207007002815001c06a0019454403800c804010030045050010441e5040940060000c0701d0514159406c0d96118003010300100544901139010030304c200800242c800298040c00d04d01c5825a80d0044070340c40c0d048040001c1c2d40004602802c068450204100800c9560110800c3c824543c0d139640c40c1e055000c140e0550003100c0d40d590300f05054014001c40007208018111050408403540410101406000203505403402c40d150307404907050b10707001d210034220030790003902c0d03d140c21402c94660f69034089040341e00f60082e1207030940144d0350b041860f09013800d800d00d41524090300791021a24841800c008480b581100c50844003550118000707040305406171180c1030060f1030a02c0d00c0702d001402c0c000425058071491151004120300709000600f014420f0003882c03203c45c4d00020301603a429044c14020b580f030300b003550303400c1c0b1030300a6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 773054082 1250 773052832 773052857
    0x1009050307061a090a020306040f1109040501060f2106082406040225020a0312090608100819050307060207081810120e030c070305060711011104050f010309020d060507 74
    0x1010081c030003030000b8084c040564603840c50300085c0d0805081d4940080c0c84103c20040b00ea00e901561304008a0390b2640f076240e0250300200300c290796040c3e0098051000d01c0e085ca41031694020001d03002d819003060341d540d00da10740621002c0241410741c000082401090100b80c9000151001a020f10451750202881900c80340100412441003484032000e02083c20b040910001039490035404c040c3c00180318900481d1340342c9643e681c50f03c4038000398000a440c10300c28002240c028468035000044140c01003190342c20010070942d074280c8100c0c0311804201314500c1c401008010011241c1c038079407004042d91161641d141074141500501c520b450495098000d80072681000e55810200d64115130303500d14412411002800200301502062226004c00c020074912220308006610045100c3c5004003800d02c0c041c0c0004000c9413075010582c17401c1c1d040001c03204003204500700351015501f04903580d4030000d03800070043c3c006101806009401c804510700c4041409410380c4850712490583c0c5039140210030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 773055332 1250 773054082 773054111
    0xb0f0a11010c0503062806020321090d140f0a1e0e0109050f0a03080c060105041404030206010e07120f3606020a0309020306160906050f030a0905100905030706 70
    0x182c0720800720015105100282891520400400046118001d105812841d07609071052003a10398104901503400040c2054441030860740c8502010305441d12034100d800c00160300d03611010403201440c10403007480840040c2650207421150440c95840c14581c0d80c14070058080d090002c01d4601d11030100104001030040c2d800b82c02c0900740d0003c140c3d03400142d181820100802105019240358102401290110020340c40d000200641c174860740c014491985003070200001c0d0340a4500004001d07071001c0c18070000a40001d4220b0650b0301410340343e80703155101c01c4104c0f0b0380d040f01104800c982d400e000703180c81c3d800c02a5010900b04181c60921281c3d55003110142d010401000d800c03210b503100600b207440040740c4181d010788a680b01070320380450816841d0300000e2801106980b01c82c04196940243c084050300049554002c1201f800c2040c02d1080c03183d1034070ba203804001c0c4a0400175494110210401005000c4440e0b10052444208004a66420050790300d0b08500d60442c0c0e00c5d4585503042c0d0b801d54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 773056582 1250 773055332 773055341
    0x302040507170604150f060503040605070507020d03051e030a1d2e090209010305030a1d18040212070f050906061305010c08040807090203040b1e1f0b0f0a1101 70
    0x4903091410003031503c6030f609010003007061402440c143d450400002c0744041c1d9040d0b50000410442d50f80c00e03201d00b4207050880c212a0098144000c0c468108144001611500d0203207544640500b070081e01c400000d55140c5100000c030041c1d40f40e8007000000c01c901c82c4080d50101030303c45103c18080000c0c00c08208421740e03402907a0f51807181120b1400d41c40110050312140050f070380501b600046040c03003450340131502840d000c0e081107030541c00224006c030100794801c81c8942c1c056505404c3c0c854000060021424851004000b000182c0f00d40000400355250f1000f6680c054000004903030400b42d0310301c02d11004030f1143c000c8038441c3c41681c011844a01d804016106901a207201c00410213240500540f0180c0001000700c800910070b000000380494180300e100e005004c10900941e1307900e00b51400c41403e8500404101c2000c0d1006c080001401c1e80c1040c1aa014407042807410452401010b2a0301803c980d0340300f1400e101c000903c10242414030806401145c3c0651a00035094000c0c0410754240c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 773057832 1250 773056582 773056607
    0xf0c191a061f0e2e02010c0c02060a020f12030601170903033d03030801090504120e03010b0405130b07170606070606080604060606080108011e11220302040507 70
    0x10861561644020b420700c00240106860b400c0100a14407208086002c190b1640c00182c0b1031105002035040f11844e540d80c800356101d207840204482d200800010b030a440d12030078083d019502c08100030500303d00802400640051900031504610305807082080940e1048404c20300082081c940d00d007051714051112401040c0c0703074010710b0541d039485444c000d56000359510a500c1d0050180c01101c0310044030307500050140c502605210980c114200030302007031070681c4140702203440d060030080480e05100c3c002c80c07400712a1400f1415031403d20300013070241841d030f0141d07070303100385403100b8010f94810b1910b0900941d440b411407880c55135075201c01a81e011030b42d000120150a0b14000081403454a0303030090071010321503540000c2030f40d251404a0305d42a4210760445400c8d070f0700d15052011a400c90102401840220001d0000d80e1010910b074501040d080d18190103161180c500d030345002c601e40203882107044a440c5c0283c000000039429580003d503484140d00603846c00e40030030701c030a04c1f8400d8898203 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 773059082 1250 773057832 773057839
    0xc010f05091e120109111f12111602131401030f0201020a061d07050f030712061b050a0f05041202010503041a160e04140c0f0c191a06 59
    0x308038030308040c080701d450441110344141d41c090344001820fa442c1d400241c0030355540e000020707814989150a0b02c104005050151040301c0c0c04a0700303080c545444015a403008420b00d030100c501f0060f8003006020b44401640c8e40c603d1100415891a200c0017004618030702d5000711240950a030f10818030b0400c41e40d00c540c4d06061541403c0040c4049041018840180c070320610440d0541b1003503407220b000715400e0b401030300010300201c00d040c00768881c1008034002800d401c85038429400711040002c0d0359004184640301c03041d0103540c0000240316407071f8000c1d200d400350301c0366600258462480060140c2d10045d41d201c0402d0b0303043d1b5a1700c502442002035409031480c0c00500d1901040f550010344050f04020402c490710a4105110100000603d00143c007920540040030300361808000003402c1410351001460007a031802180003600b40c81c1c84041d54004150380c040c40e58410100303107441403031301c1100000600c61241001c40c458101d0344640e0f82d60103034000d25445028443e2500074061817441034900303590 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 773060332 1250 773059082 773059087
    0x5010515070803070203070f0c052e111f0c0906050c0727090501050105010908031201090203040302031605070501030b0f0a140103090516030c1a030c07020a0e040605090c010f05 78
    0x94082c400441e0404154011242041100d9942182c1e022001c1412204425010000c100710b0521440110b20b0f40603e000a882000c0c50740010208542d03884c0c3c0d08410021480030380304502c0c0b414488906410740045409134007110340c010440c0601042c0c00b0410001e0760304000000d204e07214409481d00042d594003c1c0107018549034090204001240281e02c0c000016000d03c15070805602c29480f00c41e111b12300103c2d00e9032504002520300041ea0303001580302c0e00204281c64a44203a000c1042c11b50f03102000068503512581802c81c030b940641c00f40710354461000d40f0410180100080d01c413080b220240d0302402048035070401d00c040c0c0c600c0e544d042b039040301500c2030502c40108460310100c050001850009040070b180e0316514504000c0003a1150328082c01641481031020308101000505603040c5404100c12070075450b100903101c01401140200c2020a203041107555000c0110010520154815036504190900100a110a8403058290b00c03848201c2e0030554000c0c007070032111500ca6220b150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 773061582 1250 773060332 773060347
    0x20307150b01050906030f040c08010905060f07051b100f0b030307060b121506150a080408070201090b0d0f14010807031509020d0b04050c190b0a0905040f0b01020105010515 76
    0x1001c1c200c1101c80750705001060000744c0c0c0e141c8403440a0f43c428000da42c551a041c2c10700d0b09150200400700d81141065904000200b00030400014690780c0207540d01f480796030aa40c864404484901400e4190740b62100d45150300c5140300c41c0003900c42c2845100d4181000702c0d90361102c03070070111502c186456400d03400a02c00c050100e603842d44410203e400180404000003462164142001740d2105013445a40070001400580e040401c68100091548803080345400343d40e05003d4a10580200024002a000640d40045911548155009105400101c3d4482241942e184084c1000030080f40c001c6281c0501f001080c0c0c510501a4101d030014000780c214681151280300f00c00c042d0070300d450320450320b032500900140c80c0c0c0c8548529490240402107560b041514149050441101d40c807441294807132010030151441d081104115019042d40d00d9403042000c405845031441c070341c401940305151244000d00104990008208003900340c0c001c1105c2ea0300c0f40d04101285c803500900041400c024032414 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 773062832 1250 773061582 773061623
    0x507030903080c0c13090512070b18010b0604150e01140f0f0c03030a0606200304061115101802040b03060118030b04111206251b061a01020307 63
    0x40c000100c419041d1107103455144c1c041010b00c03402900c00300a0b5503840110b0024800240001ca00c9010f03000c11183c03405600c0d0b15400442d000207031511060101c0358002c2038a6190960000d00c002201404058403260394800d0040800c00c4090710001103004a00d03c100d80e58800c40883c0d440480b000312290600380d00e120340c00025045019000c0c0c03500d01c104401030105604002461281c4c0310804c000c00c001d810701200034140ca48007208243c214881d001c142c030403064048292003d450086c0b40c0030316180c0ca100d010ba0300c2e2240740070058031621081d600f8454079040414000307040c0d4010502414111100444140c1203105a100fa00d500d443d040c0040b0703a03558407509805507100c01e8a02070414003078503030700c5050b40660282c8080321000c80c141301c1c000d42400e00300c0400b0441e1810b800034143c180b8150443d1107038020000c10720750b02813100184d8125090300030a1031068800c0109a594519601441c01c0c40c018041c00f00910750060050082148940c80001115902544001d02031840c59034070006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 773064082 1250 773062832 773062837
    0xa06180c092c0f060c0a0201060807060219020f060a0201050114010f2a0b01060519140702040b03072d050d12030504050c100e0f0a061d120a0309090507050703090308 73
    0xd000b1903000c0c00f01c0c40041101c08005460242c12280c0e132156517000411806400c544043d8000c0ca004d8020f0741c401c10400f900403036146103214a006410705415000d00c00110015904407003107502880c080340002140342c0c150b010364161592201180d07a1801c0c10001500d10540604092001034454a9400c0c41c2c00c502c607440c0400081000148546900c03541d03200b0b496420260442d8000581c041045c020b1a50901200d5001a40f1810411405916020410000d100e50f03038001c0c0c0500c0c2c580b50500b20a40303007000081c004081d524024031500c146005c04c00002c501000791028100407584011405142c03444548030542d0740a054554403840880007a0080c00e0005c005548500a03c102104591100c2c1000e154541032542d401407442903081c1001440412080d1050184405c0301d011b00c00141c208100e03a00c503992015985048150000002d0b654000420714200580240c00c2d000e020550064041c80c150b07011030700c0a02c45a070354000c1c21502405070401c0503000a606030000c1001c5480c8000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 773065332 1250 773064082 773064161
    0x100605040515220303020d020c0a0e0c1c060603150b0c07120303060302210d090e07050714070909120f081302030f06071e0804020d140a06180c09 64
    0x100c40d0152400241400f01c074000ca40e01c242e0250700310071103081070280e041c000b144d5081011180000c0c0c0f80d05041c16241e011800800c501c00701400001d45000c0f51300e48128032101610014420700009890b000018081c00c1c3c0f074915101e800440290210f40460210265001c0c0000c407c000e1036128a017a18040e50f001d6941426801e00d56594000300140e243c105c1c2c0b2903100300c88903507a0310040da035003601e051401e0354076106041000748900040c000d452004034480c0d0807500502c5c1c200d49651083c00c01400f0840000000c3d0058418020006010802c581195018a0203403181d05030941216105172a080b0082c103600700058030f2100011a8080080801c0d030505002404031505500c02c00742081c60700c007003650200080f800c6807580000f80f0050909081c078690a500c1c14001904040e800b041c01034034080c000805d50a0890002054860200006d00c8095040281402a0f841203001b074208017101d00c50a4600351101f0130007085100c0a07004400c0c0c00b10a000039070a0001281e0310100e40e001c41e50700c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 773066582 1250 773065332 773065357
    0x51b04021905031816060806060307020d050c030c070807060324050d0606091e0b15120a2406080a0b13090204020d1a03071401090303030b031014100605040515 70
    0x8594016a404020800f141d00f2045d04403040681405000b60540308020003e80c81141c0404c10010010381c04240d0034040b00742400c1c5240c0b01c48201000a0450003843c4046c152485040c030002901c05000603443e04032a081e0302c0401460792080d400030180c0e1005910b84880707900301d40f410001d41c2000d100e44100c03907000e0680081c00d540c5030640d040564a05020301280140a201301c082a000c141c41941c1d40040d00301c0b59400c072078580c0c241484460040780288070070801d000740000d000700965081200380e6036a03000004d54a510711300804010341d543d8002d0200040303501d00014035043c42441140d071007940c02402c210104a0702d01c420005414052000c80c1c015400b80000c0450322000c1c02080442c0c100038a4800303c600c0580c0a1500d000d800b0707440003c01d42c4403d103e040c1e403030740c00040c500180d80c2c2501c1c000c20601c42c450042032038810018444a4110300e070030711100c81050b07070300345543c00740c0a60b080800b401691035404070340b180075078010f040d40b080744220100600401000144048078080 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 773067832 1250 773066582 773066611
    0x20c030a08093d05010f050d0804030b010f030c081501030f03030605060d2702060304030f021606090303020610060e06090f0d0503030108190f0212030c0a051b0402190503 75
    0x5030088600e80c00d020300350185903c0e40d00046001c001c0c0310719481e010003105880401c01507141c10070544984605105045c000c002d442c000b4400e11880c441194042c5810140032880d41d41d43c1d0344e10583d401000d100031348046440e402e01082d0440b000c1080550800c8090400d0b020781d0031502c80700d20b000c0d030b104412414181e43d90800900c503200c96001d050141044440000c144c40300d40e0402070004091014000c90b4200c1011000c01655168192a007250300f6140ca480403000c0c040c4145d01c1c1ca0020701001620b080103100001d55668045031b55010340c3c1c03107942a10341c16200c2403211242c0043c68010100421007004402040c0c0c14443c000d0308020100030b02215460041401040c150088040195103a03000000180200711041269240b018007140d80035214070110340765001c801c85c0c0c60300000c4c4106000c1c4d00420304403c0410a40c1c40784050070080c0c074506889807608070f0b9a2074030034650b0403000b007002c12122030924241c400c0c1c2c0c01c000e11021500162420560080320168402070656424600c331 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 773069082 1250 773067832 773067853
    0xf1602041a1315271a1201021905070f080c010209121902060307092d0b040b041208040302040c0206041704060c12021e01141005100e03031c140109020c030a0809 71
    0x140a40241a00c950b2481810009001c0900414030405162400e99032300401c00340020342c218050702c40e42030100d45040c54441180d4501003400602e052000b910140020461114114042d4002c1a60304800c540d244045040c14501c0740d103406501e541000200c4503071150700d0250900b06c00035a40541c0c28544800c4040c0c945414400c0e005580020b04e00000030740c40020141300d11100c171030b0b01030481080100e0500749495170880c0c01e4443e9000c2c945500410405401c10010b61fa41560083c650007001400710311a0303c8e030300035501e2004541c1621580702201c010040f2014007002ca0782034401d29074440d1b00000c1181c44180f490460070500c00304520881c40e0310b4890000d96100b0103c05a03d000001c101211070302d0306e130f9a0f52080604405558241400c0c100030555481b00070164007441404c00e80c01810405000034214082d154209050944002e500c058400d510f602421000c070a14003a0701070359880e00300c2c0c581240503d000011030743d4410018148098080c25203641d00c0743d6040221451204e4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 773070332 1250 773069082 773069159
    0x608010f0501023f04050307080304210c0b07030c0204052505160b0405060411010206130b0a1e062c010333020421080f1602041a1315 59
    0x60506591342c02440030a00303011914040c402d40006181c213000450a181c1008031480402c207448c020400540d000d4060b00c810401e50490440c028180d0780720a41c0c0319841418050b250351440362040340b04601d8200001d40301c80410400108900c007000000c0400c1108038800d80d5150320904400c000b0103414140c41001590461860f071003688900e024200e41e040c28500940c1401c3d95044441c159081501003103940d0300c0410307042e02c902d07402480a911a40364000000014803018491000800644805071a240c040340c20000481c0c5084d030902490030515014000a1a034845c52066a8241d010040000c1a100802c02c12503010078401c0030300000385001204403003001f00c5170490b0741d941c000c1002c00c27028448111106030312040740100d042c580d0040e0b60b2003402d1310858480101100001c500007601440d4561440034181d8040c1040041d000240982254100740002d1148640600402043c400050340502240001803e294040681c146181100a00592600000d981580b5622480341e81e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 773071582 1250 773070332 773070433
    0x327080d0203071e02310510060e0405041a06061c0c0801050111120f040506070506062b020f06090303070303050612010c12020c0102091003060608010f050102 70
    0x40c800d400555661440386081410382030420f607442d00b0101c03411400000346e1200c52800c0c0034100a148134410010784004c01003c0d400f80500c1e854589450101000044890b05820506680b626240c050b0200102030400003500c108890044c0321810460303500000034000051160000e0000346500d083c40c101814207030340d0300c480c07605810744552a01e2440e9000c3d83c00030a05409000c5c03c1c030705801e688001104066032071644140b4510309000018401c0c1c83e03010007200752000341c1001440950390701058142959100d40a580c03083c0308511880d00e09484503000ca100e21a490625140206451495020003100c1030642002d036030003840410000d80159418401814020320903200050f5504002c2c05000e503641c035a4003c4025030b071400140300301007a00549010313400440058056a1418003680507406801000401c54000c02c00c141c0e6030403480c5e056007041c2c041c1c801d40d43d18000d55a03038900125100090034482d05004da0000d0080003070b88150f441000850225080b507160039190350781d03c0e040303101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 773072832 1250 773071582 773071603
    0x403050301030210050c0a030f0905030f01050117031315020a020405010b0c01060b03150409140d110d050403020604060810211b0501021e010f0204090f0e0a032708 72
    0x18a00100500c02c51070240d81c09500c4018918080d03051100c0c1422503541e44109060103020b101003040170514103442014044045c1c200030381960100314100340388038040c1c2028090504600c040031541c90290744004191a4050ba00d052440c046c00e00d00003807441c040c416002d9000443c024146070742d015860f2402814000c2540c03401c1c4555075030b009200c060844440b60000e203031150040081c0615500c400d141c0c25901032007180c001030840c25074581f0100100d000b05004049000c2c001c0c246070746507080209564402c1c0800103551072040460400c88040c800d0303020084d03001c0424081407000611611450790301c85031600413074454544401c080800324280945040202d8880c403030640401c0200b280240c44d000c103d00008240c641002e001035254508181c406001ea281d440480c1e0b4424001d40001c0000015503104541c0c841d190f4104c00d002c0c0c06001d0304c500886080549142d42c01e540010511011a0980d4030a4032162200d00c1340960f4035031044500ba0a410000c2010406072001d20212288 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 773074082 1250 773072832 773072837
    0x70504051905060f011e110114101415030a02090409050309040c0908060109020a21230708010e27010b1215010306020a031d060105031e2d060403 64
    0x4600c22024600151200245894001c940100c43c500c0640d8200d41845030381c880840070803090110b0500c0c200c46480001d00014440e608045401c00c110b201d0527074041c0a0b503010a101e0003001e03100c0329000180740035100303030301c3d00089200010011f04020303802454022130b03078030009440c0c60b000d0b00008041e90703103081d016100c0307420004070849a881c1c5407060300380807030b01810b04141440c075001103075440b80c038144030740c214844e000601c0070340d194850014480c906880042c10803041081009040040006c0d08084007c449a02414640c0034560075071184143c1c05581c82c181607a08180074029119000340010145d6501c02507100540e250b420300b10b0b49200d9901c1c000080c081000030800250017001e1003125105d8210a0464554818020f40c150559801c043d016955441e076450403001001000b0480380c09007404000c800407500c0101e80f05040350300c203c04403034030142d8034107000355801d1000c00f51080980c000b442c0d0a0000401d090082e6107543c801500710007611801101c1802d0407030441d1304500 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 773075332 1250 773074082 773074111
    0xc26100902123705120d061802131208090f060910110115051e1807121103012303031b0601091a0d080c0a0602040b0a11010c0c1407050405 61
    0x1114400303c801c030510718032121044019051075100c2d1912000c8032680c180c001d50300040c09902c5941181c01050041c101000340742c1821400300300b144000d40200c1001404115010400120b06421040d24104290003620a901d040880030400190002d00e0041d2500000244085203d654035040c2808014042c0e464403010701c5c40039802d8600312082c00000890740702e1001c40a2044d80c484103210f0000d00c40c007200d240d1041c0340b600c000441c0303080381c1582d28122000b01c504101d14107a102c3c492a400b001414000d101d60003a149080703c40c0d0009008440714056504205512200955003000c10340701c000e010b40b40341c10f5580b1012109007480310b0414425500c8a001001601e42c1c611032240311a506044403500c003040b81c4000740050b02042c0c005040c00300d011403141909a010b0108804090b40650215a21a034980c0410126000340903040081031410480c03010101c410300600700301400c1035448c8580c00c600d40e070b100d40d08800c0c030403040720843c070540c0710114450f1958465203029031003914495a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 773076582 1250 773075332 773075383
    0xd020c090a0f09150608062a0a0207080a03030b03010b010e0928050109050601081815060f040603110f1219030c05060403090f080d0e041113030c2610090212 69
    0x340740882c0a089110b501c284211510040042342c98040e02010011010541d1211002c0c0704902d0b061094000100c079000b0803094400305a010303486002d21010640081c4a00c0325004015246480250252a0408050000980c54500502c2e5006140c024000c2e030500b0340e5003040c220411200709030001c00010303540c0e1091103050740e00300203003c2d8400030032144040b08070a14240030b0707158030300c44c43c952a80c4840040400e03019031358500c0800340410003410400801e962810103800c00c255800030907014004607622628282046038900d48503c4181d001000740c80d001580342110ba4521803415010055110403420010310140003d60056000e03030703101c00150342080121f0f910084540d003c2c00300d65200d11505031840b0381140b541041c0180885c1c0000e880600c0010300c18003449403c44094006210311408420064909410000d803106032010564941d601c003401c008421488036204202c1e4403131003903100d0204081d00a5a4000e1028019400c04141c40107143c0c40e00c00b401c918643c1c01041c1802c0c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 773077832 1250 773076582 773076599
    0xd0e042a021515040b0f3007050a0302060717040e04020f0405010509040f0203100f02030901140108060109020f0d0606030c02150712020f040b03180d020c090a0f091506 74
    0x703004009107045466498140040512240207407120343e41d004644910041c90310340d44000d14112503079006843d85134640b8841c1c1c0c15003500da0502c80c0780a80e030100d800003914a418005621415104050000702e401c60650b009c100341604501c000711500200c45600050454a80b0003810040007404854180c41c01e0a20410607449481a1320501a6150900400c002e68510241a03000380c2c00c0400701c8001e0b5a82d00202e0700f02500b0300c142c1e10300070b8202802256401030560044d4070803803400d802041810760090041145100a2080c0d10882d8000001807090800540c014058003400840c42407034081c19100c0d1205071015580004081382d540c05140105940510104180320f804032220f00b02da2074505000740416010280809120b5804201170090b0807048044a01900c0d8140c0c401b500c900d009400000100310303010058159009000003400124000680c1d41c0486d04002c11999841d03562219402c01001803a2615100940b2405024085100c840540b10341081c003400c003295050030040382 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 773079082 1250 773077832 773077843
    0x307030201061a09060304031101060f0e01091104050618101706090709060c081213030f080f042a14040e12031f0e0a0c200d0e042a02 59
    0x1c11002c0142e00105822104400719551484105d030200c0d12a156828201d407555109107903140306619007000891213030030741c0e8042e0b011201d075441c00d001ba03a86c031107400406403003088004c0784d542c6078240070a0000c0c2c0750080142081c1000041602035803000200001c6c0c91402083d82c0d01c0c007103031034510301000e44c2524204103a44518191084445070401c4c000c0142040c42034800d800030000c0c001005020444140b00300d40f815286a10410142e0a0030b034048070100400300000c90101e10482c1605c072041d03001d09003540c4030399241c003a40c41c80e6946079251654134040403030907459100c58a408401d00f0350901c000400103446021004482891000c2c140b104491104480300502c1d0321480c0d48022400e45c8400f00c0b0340c07103619000f0000e45014040c1417024403441c10b40011064031403040401c004980c15a00c00820ba003a5583d481800d0780c02180c0c5020398028401443c8031075001031150190312030085a9010100b040030b40000740f80305c500e00054100c5004130400e00549882400000c0c05070307504210 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 773080332 1250 773079082 773079089
    0x100516090b0a08060f010c150501082406150c0d031a041523030f01050a060e010b030402100e0a090902040509030306090f070504091103070f09050120010609020a02030703020106 78
    0x4141c0c0c0707007826080000d0b0684000915140c85400c600c100842264807440e416804541d000f20404541145100d915001e4a000d0048180e40e01c43d40c08074881c440d070045006a020300151031041126242c0c14184100c1c0301c0000030300760f417144040103454071900041000c80c0c025000d60b41c001401c4561076202801000e04c240b410361050381007241500002c40c8842c660011109074116507028081000c2c0040d5040c46141d0401e175040c01002404442c02d41c040d0003803072040800c1c03001040a5520b50441d80c841d40020b010380c84101c0402c0c00020f0060600c03401001c9805c10318101200800c010340d002810404603a00155040e1742c0305c02c071650460800c0e00510ba0480012001745003103142600200318120001005003220807419000b1031450343c09075088034060468100107103e0303e15068102485944241c41c4640000d400c800020381c482c0c802d12114041e680142c1d10030181a41600010200d2078203d040740d51907560b22040080c05509520050500302c00c542c002c1d40d190750700790034060f08480700da90 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 773081582 1250 773080332 773080349
    0x4020310050d26030f0901020f0d05040309050307060f03050c18060703030209030d09030b0603150a2c0d080a020a0909050705130801020d0b0103020c070e0910051609 73
    0x288680c440300600e1010540d20700781c0e54801507000500b0807100d03210380726580c0081800c405100b890745803e0100158440d50442c8603000d010380ba02c021040c00c0340b040b01e01c40b02900c00b042c071900c040d081e482d81100350040c0c0030381740070190345403100c000030b0074452581e1040e40030400180c2c0e1004666014000c0c10340c000084070b0802d043c100d00403a2090703a40d0458181510407640081c040c400c042c081c0d41a22410715014040b1400d1a101500290242c24580010707114112180c000401c9441c0005421000f45441102c00d9966150155860082c1507580000034244030308c000c4000c201884905812000c802807802030140030b88445010700703c444054080d001c101e00400c86004e61a402401800483c1e00110780040c040c0e50f241001c540901440240ba00c040410103c0010200c0c0150090280200000781c2080f864000400642c2248500d02071042c40340c000003001c010000c080402c141c0e024141c9403c2e07d50802c403c03449a4100d40048800510b0030800a60007004243d12859441c054107502 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 773082832 1250 773081582 773081587
    0x402060d02070213020c0c240c07090212071202031e09030705010f05040c050d0309050d150203090d1404180b04060509040317070503090a1202010609020c0705030c092202030a0804060e0f0402 84
    0xc40d0b01044010200799903020341c000041c003589d8808042012900500159004540724203c42007001100b071030aa0700309000580d580303034140e144560703482264060150800100e0303d451301400d10041000c00182000c03920301003800940c020030403e0103210f00380000b000b0f0004452a00303103010300301d1100a8000134000c4403102020307000a0b80141c2c001c01601c0d0b0440b0040c0710355500d480d1182c150124000300403041e50002c400c3c00354185002a070440e002009407203549400c00150310401ca1800380d2b01c1030b041d0041801d00b40d14900c03c80d07507022000c00070002e040414080d44650200d10029410796044001402a42c1154440846044000d4000d1001e150a500e18181080c2d4159510441030018041e02c40030400c041d00203000350b008a005003640300c020354507a2141c844c0c071520303a0614840e0364042d00070000340820300c1c600501410720609400300910406400c0b0206401d00403500101280c0611442c5a41c2c400b00d0441c60190000303090a43d2252420100d0341c0030b000142001341600e034000ea006 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 773084082 1250 773082832 773082859
    0x80d050918040b040f0809042d0e031b030c0a0f0c1a070210020f070f1d010312080403090905180f0109110d0302070504020301030302030c070b0c03030402060d02070213020c0c 77
    0x1490080b035082500140f003e1709a0545003480d41040c8145240b442d800313403500c2459042401c14451b0072000301c00900000d080c60a540c0d0752582a079812040195894200b0040350000c006043e600030784a100c45400c40742070514034032585240910340802a03404040407803900f81041841ca998401a100c009071100400421490341d0701c2030301904000911800b24240030381800c134801c000c04004041c040e400c0340c1e244c40e0380f40c212014001c143d005201030ba104010701425030b100c4001c5842c0c1283ea203c0790100e22680900000c8402c18800351044080080c0407100180c2c2403418060180a06218124220a0f491a000c00c502e0500c01250301803561b4102400d8001261000300144400c10050301c040c107900e000b500d000c03810308101c0e411103684644081b00100a040d4008040d0800d4000c040c2161001611052200024003c103010710ba416481080083c2c0103050840280c0750903454410003606002459001518034400007403403400840d40070036281301940c400c05c0440e0f610501650784402c1e4211 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 773085332 1250 773084082 773084093
    0x5040e07030e0a0209070e040b03120f210103061a1e04020306150d09050601120c18111908100e010e0c09030a0b060a05041e09020109080d05091804 65
    0x50040c03500c0c0500d503a440007218500d100340407050b02540e0003829400e4a1800e01070182c08140da601c0014025440c1003a201c041e4200001d08420000000c80ba040c00c0020b110b090b25125881910f600d424101a4580e031030f000400c07070308580e0196100e000d0126258800c041c42510380000e41d811940310350120740c16091800c6003282c070641560402e80340540d89a07540c40108005440c800c1c0e0740318081200280381c0100d680903a00c000c600c2031090086c3c941999a90840c03d01c03079400e03654050700380d1038007180c01c004a040f8410400e9124460044c0440e07000380300352880c0d840c0e81102e07003800c68040350f41010034172881d4030070350f626030080c2c64404100247d402c19815043d5400140600780400c02d4a6001c41c404403440010382d110381500800f00c5854100340c0c03038610414481030f02c00c00c0c0640040c801c040b40500d09405030031281090060300c1c0c0348204a0702c07038200250a045000382d06011806c500410201d03400d0001210031402031316141e03074034000401803001414100e00444805d4200800740000a003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 773086582 1250 773085332 773085359
    0x1180e0a380f0607060204170a050325020604080607021606020a03180b030408071208040b070c1703010f0f08030405010e101407060609050603011a010507030306330504 74
    0x411a205100c46001d0081590058031264195101074003145280c02c010480d001801a500365007070540409078100c0d4040d50741c5072a110010119041840220f00c1041c07000d4420b442c1481e0700e00480103441480e0045910707580290040d0b138640c0c00841c10000da003601040800f02611607803400302c1d2580d143c018000d44a046482006003041501e400b40f10402c10f01d40c8960010b021030460407590703400d0030300e0b10008642c041001101c5024085002800060081c50740758441d9403c1040c031191955620406c0740c101d40d0105040b0b40c03d03d441881d9012010414010314080c18400044c805100e0918246440c4c1c06143c0d44124200c4c1d108220500c40e60368054040c1d494542c0981d031200340000c540c0420750303901c188900d6400c142c1030003080740d1040c840315400a90480351240b030300700017039101c0c4004c0c54240d4100342204100760031080040c408552040c0300402d64140a4600040d1240c0c55010a10110401d2208041c11200010152007000040c42e89180c40d07810a00300075182c50300e403c01c00640341 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 773087832 1250 773086582 773086661
    0xf1a040507080903031617151008100909061d0f010605060906040b03060a0b0c390f0103020d050420090108060610030908120a1503020303071101180e0a 67
    0xb101c40100d40c6c51080d0003291380d0b40003281140045091860a038080b01442d1284001d410710492881104412490003542c440f4001d500742c00d200c8541c1c604040c0500003401c000071007101c4240e550030b02d0f0000302d608100fa42101e4140700011309600224680f580e803e5800703a8000600c80d4104004550003039860600f103c0480320421103082e202d5480a000680344050303503000d540c2c03501c0c000a00401e000030100d149007450408044507582400304100242081000ca0b03440c001c0b000000d40c18851a160199000c00f11900500d4050300d408600002e0400350b540aa8041b46c8602081c036209902042034008a402c03014240d483d80120361510b015a40d9030000900144d005490009084048030311070703046405902e4220a00035501d868080120201c1c58044070050480c51400201400d880389208001040ba90020300540c1400801c6c1c803006001e10b000e00105061003540f4050344000864400c201005001c5d44000482074a8a00d0340102590043d000e07040e2403503034032540181150b00888144410703 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 773089082 1250 773087832 773087851
    0x261b0901090e1b0a0b031305010516020a17040b120105130e1903090b03010b0a020106061103120a0213060f0f020d1d03011104230a0302010507020d060f1a04050708090303 75
    0x280302c0d100469406000c80c4c05c1101545000010040149811035044e0080e074400ea00800140d642c0340e5641c515001d1803109500181c025454190124400c00008015095000b66040c60300c0d998000100565025041c41c01c030026403200100031074a001e40090124092540c0c5c24064405503921082e250140b0302c02c0c8840c613404d111484014940700d0b020a034003504820700030b039070380b0350310740c04160855008084420019801c003100422590b100300900c1c800c3c14031580c01182450f032002072403580304200034459242c0b81d40c280b05035091901c0c1c0c4020240204282c1d19441001e1a8644004201c0c00400c02c4400c195030003410359000f0300c2d87c4410100d42078008541c014000a00400020340035041e550810310f809034020030003084c0c030740c8940c0d80c1e030b0802d120341c11400c055010b20809000d41c004691001901040c4188003040160034492240c000c42403240000041c0e8030726000d59681216641d0b00b404600c40b025096900351070520f4403070a0b803c59a1410400454070f0030031140340d80c9100007070640c1071 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 773090332 1250 773089082 773089123
    0x4020607031e11011a0901090b040b0d0602090312040b1608070b07020715210504050a05030c010507030b040e07050114071e03090b13261b0901090e 65
    0xc0c54480c40c0d00c41007580400803100482c1181c0340c0010204030a001000b078070703035280002d1000100001c2c2500718280d0f00141c00c0d600310b60310384400c1d41c0003851001c0260313400613164038080582d952400d0034910300c42d1265000507110700c410800c0c5894403440b9002c60422102c1040700344103554080003568140d60720080d02407080703411407600c5041c1c0c3c0520400240f5070350038070b418484980d0300458001c3c00c0e180c42c42e01811a41914010489050510380b04140d00c540e05020001011000c9412032613000d03003d0400c8a4a1028076540c0c00d00c1c0d0b41c050710300218540d41d0b0702d01340048140d144c0141c1c2c0d00e280e01107a0502c032070110440a561202441d02c202414081b840b2032901c14084844299060f05410580d07141200f540c900359207606181035602100020f10038400030071f40400e58402d40e143c41940e805003001e41d6040c25141c0e452624565000c0c0e0040c00d982d80d080480706402c1151440b4111224000c2e00005842e4042c802140c6041e000120058140b518a00c1020717000036407400510440d107083c2c00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 773091582 1250 773090332 773090347
    0x1404020724090311191e0b07020105150f01020d0806040b040e0a12020f070308130f0902130906140411070c1d10050f0103020a020708010f0606180509040206 69
    0x190031001e12900800764016202140480d522940c4001e4245000341c5412005401c00707180c1c0d507103401d100d1003220403002c48210030901050380e4100c10241c900c076a0480c404004804d460343c001c036030421105000187c3d100c1040105000000345410003a4106640300040d070000d4030000f0751101075540204040100200008055030783d640c04c000c6008902400030082d01164007496030b107941040005032520061410026012031002628503038000800e00034081407415070b960600303150710042000c1801c1c0c5130f890340442c52480480e4582e004100044005913030307039034200705807001c45c0315a404500743c245012400c00c41c80703d651000c0c00c0c58150450f0700061000710078800c0700460013652005000e0304184070000c90f40c2121043d80d0380901a1040d252817040d0340f0820b14200c1c140391402020742201c90204510441c1d4000c0e00038000d540031034019103050355111001da42c21140c00c01c090002854030b40d0f90800c81160044030003103280b03c00e8420010070318100404103140e480003404c0240241000503021 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 773092832 1250 773091582 773091593
    0x30903032a0a230c070e010b0c030703080a0e1b0102240a0b01030204170d110d050403020f030c100f112a06040902030c0706061d04060e0c061606060506030114040207 73
    0x1103100180340c083c103916101507210035540e50016015026841c82064008551a41d100d4182d81c1c8540625000714646200d41e0741c03c81c0c641d00042c00f002c151a44403a03440071400d006000f5040c15a814280c007464103e44280028070b440301c1c2e10101a4440c80d00411002c6032107005515952140c81d0000c00b081000510700120002c1c03086a00031a10030240b00d450a1084a01154a000c10b0185a0b01c000c98038001c5500941c448159920070320224500f00020001814800c000c03c806c3c480040686011003110b0b4081071489909185c07450000d0420280400e0850b000600d41041100c2c0c58024007100b11501811100302035150500c10207050005104549540c0351802c450140c5201d0300c081d5200d04100103610041c2c1c121100c00c840c42d504044000c07d0040b261160550201f18800500c40144c03188d4469200034400000c6d1860305019510172003c1c6030b01c407400100844030004052120f07a06d16800c103502100c0782c0b0b400c01403041d43c041004200f160080c41200755074560803540140c0c0e4880ca403825 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 773094082 1250 773092832 773092877
    0x516060c12021209070f060f0e0406080a0302060708100303020a17190305011401050327010b06071a06090f1803270f060a1211040b030903032a0a 64
    0x56003034882c0001000c2c1c11105211207114051400f00040318182500d661094a03850070502070400080c5281102d582c9041c403941035103400c1440508000340d02503c5072a083c0c00e058203442d080d00507034003079418000d01070752100000f5440490011204410341c117683e0003e44460070540090440c000700300b6100c20a281c940115002d110740b06200703200e0710003101c00240180c00d09202d81110001c0000c40321400f5401f4108072031080004502880b21502c5440c1402280c5507240e000c1450303996140e10a0900b501c3e00c900410131140507113072241c0e0f8003c0c0c0722510f0701444401000140201660801e0041200d1485100d03500200e1414240042c0ca64007246203185014241031800899414900c0180410b000300c40c2d512641c4041d20342c410103401c00070511100d84100f4040c40c00003001c1c00403c244c5203110754402d102c80c1c0301c5281000c0c58565120f05100d04c1d5001a2040c0c04203400c00010322009040e08462011005000700c1000b104c80c0a0300712142250043d0354400d81804056203000d813511a00000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 773095332 1250 773094082 773094107
    0x20d080105031509010e071d0a0c082422050112050325020a0e04051b030c010e03100203070801081e1b011b081803190f051e0309100516060c 62
    0x7c079280c259580041021030810b10306000480d01460011980d001454002e042a2032030685800748191900c4c0f00010702c5003280441c1101d8401c0100400700544d03102c0300d802e07102c440c10f9500380b18800b05101810b001c40d503042c0d01104441510f8078113000050000b0045da803110ec600162912810302c8610260107070b09018000952080d1f01c004c1c04980200b00ca404c0700c0c0240c0c001c1044961020040a2040080401e160025803503480420b40400303540c480c55805269140c041c0c01d858a1840d01e000c0401a600143c8074500403560080040c8250902080800100102020001e500000392744000e6180c08103170480c00100c4110704003100207640500550882104440c42101200c00c850038640b52035003000d0344070071419030414210603481c9400114041114110414001009a0f0313a40d0410b03240d0707112200b228280202034010a13144800d140310540251444080c598403502c64040108100150030448140507040c03004a0407100c1003480289401d6001b0300005402005040a4501480c6000c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 773096582 1250 773095332 773095361
    0x9030501050c07150b0109142403060102240a0f0b030a03030b090702011e1a10020109020406120809041e151403030c03340f03020d08010503150901 65
    0x2402411401e00000308030f200d00a40380d1224040c43c02c1c9090042d655440c0e44640081c2405605108512020a0044800e14001d000b21846201ca81c0903a9441030580c048403154540031080092a58050090600340820f81d00b00c07041c1ca00c5980c50345043c0460250162045507651601310b55020b03a90360110316046c00c02401c1f0744483d1514900140a01300c0e10440901806001c000b00b00d002e401400394120843c94100700d00000a0403000e610018000740c1e0043c18070203d064141c170015103540d0a000e40a484c0c99002107480d0095006210581d1340581c44030308407501951464010481440645850b550101c402190501c9001c4880c1401403000241450862400066420340588486101708440814540445130302c0c041c010151640508800c41866810410080440c60403084103e2030300f00d84074030444521600c1c903130090601c6010450031a4510b814141d90f405054041000342c002d1203036441c100002e581004040398680c0036994210b80030819101c086600064207400600807160301e40c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 773097832 1250 773096582 773096591
    0x702130212060a0b0a05040e040f021206100f0509011509091e0b0607030c120c051f240b0a031d0303010f0603090b16050706060b0d0606030b0307030f0309030501 71
    0x50020040400c000d0b54241d11810f040c3d000003603051984001d0340d03480303003441d201d042c141450700c1d591400240700207000311000e143d03280c49080144d480e8646405800e02a500610b101d142019503804906001c0d0400f07600644800c2d0204400c0e510510a241035031030030308144401c00301c00c41c01910700000c035401001e021420242000d01c50156000b00d000112003100091008407404014005103108480300a80043d030308081d1307100030801c0440e000d00302d1138081c501002400b40e2511498241124041540c4044c22042040401341d0003602440e824945046510800b04140c4072255407996558403074200568008608098514003a6200b5582d2100e61804d001490304100c40d5940c0700c1d80300740603000503184038000100301d8901c03d116050a05520000c03200b11500d41507110704101a03004e03071030000c100c020003c1c00000b81d101d008900007040103c01843d00c86955103840c03826103a0b240c02041c1094640425410700d41d90002d4108111b0340c105516a40e050b4250070b04031981074a58001500d59801d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 773099082 1250 773097832 773097847
    0x417070503191211041d04020d12030f0e0c01230903030c0c040c0f080609060d151a0f090a05060a0f0b041a0f03040b0601021f050405061e07030207021302 68
    0x1d00c507450f01a981001044446000010381056010380e00400c080304403064940348013110803109840d00a40014508080150180d4490081c007220901000000e034403203800c090f800c0124040c8040d1142d02c0e5015110074901030000804124242c8892500c0c1c0601400080000ca4034404580481802400383d0f03a48215510015a07541034040300c0900030b511703012070600402d10460f1030780340c03880b01c544d2119180d1b22408204403502c4409041a6030042c0504d00b20b40000303102c82e12078580681c07600c00101e030724901900d207008017404141085004840c01c00e5001081d1b580e17038000d19400005400d00081c03c0e103813200441d480d125680c10030182c0402100012a1210450300a80100c4045280c0b143c0d8040e04900080b0722401040c0203010030102c02c1c400b20340010480c3c109942e2002041c07040303841d40c00c4481001e00c082e12080700000e05151b40e4034188403d008091144951000f40110080d40710556280718a01c0d010009100c0342c105a03020074a50704541c0c41a02c01c1d04001c030000810b6480702903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 773100332 1250 773099082 773099087
    0x9071704050d1214190e240c030601090306020901122901020d0e010c0c120f060608011b1d04021303060b060a080f04170a03050703050a0e030a140903100b100206041707050319 77
    0x7e10321011070000e11141c000401c0750981c803080300d20400043c0c0d204105a40707181d94000c0130b90040424203050203180e960f056410030b0a480703034500c0101c071454600e654400c420746065801c006000050b04542080079000390040e00440c54400c01e09003841c03c0312550155041c82d44402410760442180001c00e800c00e00203000c0044048400c05020700010050250340381c0709076013240c02900e81c141807105a80401d0840c035000e080b0902d101d1200540d00038004124000285c202c0e406161011954000054203200b844241d104081010b10300b0340c0c0661400d440494050098440104000d02d0090b0b200e0001d03082111018107095034400102c50142c5a0000610180182808941c401e001038a020300084042e00c00d800764030000300d0244091881c003801910300715420244900b84008100f001c000d800015207042248490a0b90750100004026100000b000441c42c140100744086512050034040803803510140d5244d01035040000303aa036114a4605903095010b482903007442c074001510080e01094 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 773101582 1250 773100332 773100373
    0x40f0903050901080a1b051b0a0c08010c0302040308030a0e0f0604080d1802150915040b1206010503091005130f0b1909050c09071704050d1214190e 65
    0xb00c0903204d000a5580c1d040b95070b41219405e2061600b400f4644042c4110540a200240584002540540c600a810340c1c0c206140408514040f54850f0728441d040001d40f200b0700c0381d1507815940b40b800750302d002d1a6854001417400301914110546640300c8030240f0160007002a0101318410100307071001442c003802d110720141c10030b14030300f51103601b0f15501180440785400c0340c0c3e0040e5401800204540352049406030103030880c28180340c1000011940741c0300300a0b1140a00002c20310324000325070752000c1d22001007041d10040d05080c1800030034002c2c0f04210102240ca810000904000024650790b01252406540442e403005858000180407610a1116407002d01d8030030002c6243c4280c01081d20702c0d0002c122061000042c24503003002081940600e092400c483d000704030b920700304844140c0c1c0106d010341f0f00d0050301c040f100d0380c1c0400d008452803034100300b100e103224802c100304111000402c01500090344000b000c0c0b5034510401c8040e009040d103140e020052642c3c01c0002c50b0140100c880c00c01e071266 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 773102832 1250 773101582 773101597
    0x6041502090d080903120c0d0807090f0905011e050307030305090126070201050c1c090c0f08070f050612280e0102040501021006081203040821010501120920040f090305 74
    0xe000700c910207103203800e1b00b00840d107250000310001c00452460301c07812104400080e28140402941c840c0000e00d034072020344020301800d2441400201ca52500901250380701c0840900e41c000340c140b00081010b50f030013060041c100d0b501424040ea03512005030040351030310311004c0007000804000c280940c1100c1c3c0f0b01c0205220300d103940c002300300e503884109003260f0340d01460007505556040200c0c41d0b07000482ca034100c0003140344203803202d642c0162100d0302440195100d8225120a620205003042000c1e00b8609010003803d0a0702d00d03515102d5012030400c3c0300100102140156003808844c103c0484150401c00c016004221040007618215000036002c1e62061182a006125072092911000740c90303c0b45204a07405074000304841003801c0500841a04018410741d0303124010f0107482c00e130881070b04011446502503152085150306040004d01031584000840e03160524100c2c2446c002054902c50f0306070640d03920358544004148a0003c0d01601082946110040c02e10040c541055044405418036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 773104082 1250 773102832 773102839
    0x41e05010f0201060e0a151a1e0304020a03140307050f071409010503070e040f0b0f0103020a06020a0b06011b140a1a1b0904060e070207030c08030a0206041502090d0809 74
    0x11204080100c1c203981481c05242c6402c0aa200420044041907010110b4000145800b211807540c0c1e962340c244030340ca801c0079050008030006605003400d11a0030f194007000701c14a02c06081d030615401280c00410103000090003125101c200b485506801c10581d504c20380d0290460345021060201c484e00d5441c00e00c941014403410030466055440c006400c01d0680d80040c3c010304100746460a00c80c0d0303090018100b51204000307480d5180101d1003100001e03100c0e20b81c1c08020b0615501d1841404500b04081c0d111000b15000000240b0010b0f034943d0749140c1000e024a0440380c58113682d104091108000e2900402c030407241003462960003004195900481e000b4a105903c80c2c80742c0543c0315020400722040303543c000c160a0f56010180f861005865070000142002507e5a1200103140d07062400340c03412400750380013541c00c10411440c201b100001d0903046000c3c504010a514001e507641201030002403181140c1e028a8050b400f681e41601d100b440005d00b5040700220030b00b0060042d074880c0110034003 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 773105332 1250 773104082 773104097
    0x281e0303060618081b0a0f08070303090e0402030d180902270d120f0c060603080c280b13060617010b030c0f0405131403180d020f060f041e0501 63
    0x1d0403040c010034030300b00c134088006004920890150044584c28902c0c01683c000c0401402184e01020020203102829a000090004c50f05504025250014951041c3c81c1140072004200058a022404541c20b1605082c1400d1100450355040003503030440e0844601c09202041c1812007007101d4050342ea03c45034200c0b40d25480366518041c0442f05003400c4000d0840050390648403040d03481000c0d9481805102e1a00900e03000b880c0c1e540405640e115401558011b2010417661000f42040c0034640d410104291440300400482c05480071301240600040c244425038400030f50342c42143e00241e00c0e03882d80000c003008190b807948a1400105507205407460341d0340c40c00c5580e030403508001654001d1a100104150342d1200c000d41000040d05000b45201c0540600400c4a0000303141080d945661050b524040c40d1500d00300c0c08c11a14285010814603c11540f0340308500158490303d002ca18945016601071383e890039082c0894031903202d25400344c03820040c4182440c50340031860200700d00f0340d00b09a94002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 773106582 1250 773105332 773105357
    0xa05030d0c030e121b030d06060c0605070c050c041e020d1b111203070e0310061a030c03070c0c1a0301030b070512060402160c1412281e03030606 64
    0x958134280c040d03030300780340c0038003005103110b4880340c1c2100c811725010490480380340465a107480340c00d84d03445034480c030003007114181c0210400100740103035980200c00e45060070b0100e0103601e070141e0307401c2d10610060181c0c0c1e6038040600c128007000361035101d00348090380079590b0786084210840109082c2004c0c40280221841c030f240c4180c400c1c480940841d100d00010071005940c18000211076101810f01014031104511031820341e00d0601141c00040f040c420006400b6191208010600d02e15440c1015800c0e02002048030360800041520381001e02481c012002e01c15500c2c3c6010340d400b464000c1004170701040c0201e48051074030401541a80d01c110020440f50312200d01c103460b98042d911607228010745900001d1441d003055405010070440a210349000d4042e103440d051803c0115411081014001030220085800c1c9140309a194242c05002020340092441d001c0c60b680c0d030030285046100c43e00360304001c02d10408111400c00355411084041c3c80d22040c1c500a4018011032084030085103040c541c03030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 773107832 1250 773106582 773106611
    0x7020607050d030c021b101b0b0f01050a030b0a1107020307080601031a0103050c0f13060e1531020d020c0105150102060108030906031f12211409030a05030d0c03 71
    0x10b58104171210508290300e82a0810043c03007d00d1601078108203a5043e08800d00104000c0030030a0350055554007180c2c2002a608541681c050700224000ca04100342040040d501c210626031285002d00e000580180ca0300e0a400c80d403046a00195141c445c540b800b013801e090110b0080d040364400c1c0c4c682ca65001300e0341c0c0c0c0100c00e0b00e0709100250207030b000021000d115080101c000405c0c80c0c0001c00c154481501145190b080300c0340d41c0c00c003403101d0482d24204450910703140c0c071008544804450300445c108401503882e80e040688d000d801c4417104506140020522940c043d00c102e050b85d1041507465007609001035000f003000300c84a8803a02c4491402c032040c0d50000c60214140c518103805503150810040901c0440e60002d00150703130301034014641c011201c802c070402d000a419001d00401d130000c000e003452240a01d22108502070400012207180d8280c2e009046100003034604443d55485100b10400a801d040d1098406011808001014102e00074198426128010540c9082104406c0c04000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 773109082 1250 773107832 773107843
    0x7060f2307060921020d0e06121609091109130c0e1909090507031b150e030f10020c0f0102250f140318010503070e1507020607050d030c02 61
    0xc900c6900303810422480814080c1d041200060b018060240240141c141e4001d20030408130002c00c01a0491740c00721610540c00a04140002d008480c0745080012010307003000c140201401c3c01002c09480002c071010702e8000c054200042c040c9150400c0000f5448074184656400380724031920503a0b50100381e81d240c02c1c0901c640046420301d0f0792211070070a4030006011060000492070001500130200004404100c2d000d10104540b0a0b0040e00c210340c5149000761410351044c01c064020704002905228005c51100c411052900e9072400980703081d1200003090070250b0400080c00540141811868440100d07001864044102d104130b65400420020403801c0b401520911448484c032046400c10a1031080f414514880c012400201109181c4c1c1d03034034100d0b401c100d9058045070808034410011444088054040701e0080c01d00718614603000c4030040c0300884d5505418801c4002d032062102761031410b0282c0740b007030342d0241c44240d454615090076556400f0f0040c81d0400070381000024189144013240 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 773110332 1250 773109082 773109137
    0x1060f141201060807111009022b0f1401020d05100902040303141b2410060c020405090c060a050c01061202090103060e010f020703030e07050603160810030507060f 72
    0x81c552956400c1c1a01200c2c0140080e1a18007007004013030101c0054501400707106d00c00c3c6070030003000031000503510520000180100c00e44840d00c421002c41c8010302e602d00da200070303032a900c407800000600e19890800d40002040145e540c02e50310110b140d225420099001c1802003914a07001c1011a50750349140059101d2800000d0002e11703050340254400890101a090310442003070902d81215902103043e140c041000d060302250180170306c1e83d0084c01c2110f016550880052040071a95505200003e4000d00032508024084c0303560742e0008003130034010b00107404035203002003225513604501e050040054200358140016546480c0c00052003120f0580b02c00302c420380c040c0228038141c0c40c603247c035030090902040c0c84183d5500c440d40300e02020580d10003000f5542c82918000307881500324034440e290103119002140500000c1080c001102c2c0280240030740841c052070301203141c3e541c10300780005050f0079901c0202280300e07000001c03a406801c41c48003441c175540c5076501816036004081024684a9001c0c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 773111582 1250 773110332 773110357
    0x230603121606090807050a1109060a05060703170c04061e0c08070f0605040f060b0102121801020c060c1f0203041a0a090b0f010821040e1009020301060f14 68
    0x840c1100490651064960307050041d000001c2150854541c0c2c10780f035200c4078088400f500000780300d004014451402d01b60912050760040d040b80391003008500c08081c98061207200d0b100c0403807030008040c07050130100800c1d1850545290301c2d040c24030440c20560061302940010a1421003070903440c060506640000c19078545e02c1c005080c2003030b2240011036128000a40344860881030070300102d8954018a030240b44964a0a203008009081540407110801708050440d008084e0480800c86c07400e080d103c00c4404000d040d0082c40305200141e11707010422018a4024501065070030340d10308042030040d0074500d541c2e64004c031181c0c109050000ca22046400074903014242c55400d41d140030704403100340e005030500000100c0e03000079103544000030011100304102142980050040d83e03400d01076140b0700e82158010345000d6980386d0303480b0751500590196038042590380000034001c9012455500003400c841070304541d41d507142e0b640200400e01d03140d20b81011481a968240d1090684803c50b1001d00350b44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 773112832 1250 773111582 773111587
    0x91f031a0d050726010c020309010f0e01080103060e0a0609080a020c010903081903021209160f0b070f0204020403120c1209060c06110f0406090807060903121b0623060312 75
    0x80b2240b44c0c0b101c200001181c0700702e444100c0e03a0303000c802d02c03c6e4210f80c5500e4008584809182c000140b500341d0020300a010000c03031290042e9142d800160032410349500000c04038002001c0a140b900c0c1c04507009000c1c10541c1890016030610a58200802e1010065425039102d090b1000c0191a06c042c5480000c12101e0100940c001c010b032810040c0c92104540d1802616007000341e41c114002d00c009031500000c5801404160140e101d03210781400081042d600700c00401481d1509554060089840103403050030324400e9001196210740c111800383d94819020050034440034ec0c000d00c13888080408444074100075003400c44003400303244e820088506640e91414225026590782d8050002200c40903420082481544030001d140c00c045c20107015580c4d04c0c1010b091502e0f400500d850210360007041440100082071000c2492244400f441d80c0c00f9041c0211150a000070411032201800360103040d40d40f0304000368203e0f640e118401d10501c0540c0d04480420340b90107040503101e0841035403402000300f04 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 773114082 1250 773112832 773112839
    0x1504050a0605070609020d141006050109031106070c06120605092523180a03030f050a021f0c1e1b020d06020a020102030117010204050d0305091f031a0d0507 69
    0x1600103040030b130b2145601090040e0b050380891510070071b81a04907081015810600f4800b00e0810019640003007034035092000c2442c0400283c1100380c107000140602e5644180d0130740d25100c3c0340854581e180d000d020400c1d21a907400f001004040b040382e41c07801e5107041000004070b615207041d943d40180369011100e0743e0340d100d211400f098443d0f0307a0a0f034014055044440c0c2c1040c1d1a00e260049412440c40c1001d9590001078070f03a00041303041e5061103214030142c100500201e540601620501407441c00d24130741d01c11003603001703a00d401f944510a446030801a03224180c45c214a400c8002005041c0d00ca02c0007448019020565035a901017128000860a495400e14200d65600d0055000e0018284100c40d090580391441681e00000e51070001d42e4001004002818410301800c10180c1004002c50a080c2020001901108584006420010041003405541d65643c21035003d000e04140c0003403504c4000d00e009800380580324000300690182803808100c0c1e0400d503d041c01c0b4190700401030301d0151308 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 773115332 1250 773114082 773114087
    0x301181a09090c031203090d020708151b0301030f211e05040e040503030f01171c030e01020d0b0405060d0f0816020307090516140d0c0302160605061504050a06 70
    0x40090341c8a03c41c445816030075032814007800242c0440d0380c08060b13403850229401440c050720180c8500443d80081c03001c0140c1c00c800300310807403500f402007141c00640c2c03a141744844005400f05171440c0600400000002003022404054620510a81c0820810302180c101d54140c030004880407004501103d54900344008620031940b41c9084900305141000d4480209200c1e88604480481d859440002444401c2444c0303444a4010880111081c4055450321881c940b6145c106111440480da800110303403d950194010aa0000445000315201d148600301407000d0411103030400d001c3c03454040840e200d0700b846403190502c0c0750081c08031400c07030301c0fa60b44602c0350b54042c0c48000b1a24651070002c9006940038001306005000c24180465603041034800402d0a40d00625000c09002c081d0341c0f010803d208000071b0b99500070308504e0004d20600800300940291090f141c00d07040ca13068980e4034504005032984602d015501c20713915040001c0c400c8036804190701c03c5001e1917a12501c80d8804020242c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 773116582 1250 773115332 773115349
    0xd1502210c1215010c12180f0f0f180509070302150a140405010e091005090103081206040c080a0b1302210a0605180a14010902030105041401290705030a02030301181a 73
    0x85840c040d02c0c107050240764400e42c210b5607000301d2301900081e2010000e40c0090018140600451554120000e01d000e0b1610303410070926008900050311100001e42188090055800840e0040d1102051014020000555902c02c02c00f540114449008400c4407044e04400d0314140c07003041e1a0f0751444840c017400c015a00e50003d082c040807841e140340204250701c0320310b0014021482814460303202d4286058400c330120005150301d004a241260003244594458281c541240582900140c0c003000f480100741d12141402e521510305000161074000d138155000c80c110740c000c18078110f900580300c98180d20700f92640e600c42d2540c4566440c0740307290301c0000b0321030050300010550b0000512149502580440310f200764003120009602000401250402e402207100241076160390504943c10150f1281c240b0046031042c8614884500c94880c1d0750550320b0880e005150043c040b41e884800284000b981c030751090145000328100c80d4848141e00d00d030780c05040035100203a0724845407609850705000741030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 773117832 1250 773116582 773116613
    0x5100501110304090c09030309061416140a080406030e031201060e0616030c060501050d02030d0e0315010f06020c1504140a05061207030b0d1502210c1215010c 70
    0x140810072001079055154410890440100d486c1c85103e2803650030060041c03172440c3d00c20824000c4101c8040c6104a1407412074280c0764181d90004055207041c140034401c0b22609400d0074651044ca0980c505000c1c0c11400b0b4022a01c403640d082c040540d481405039100d0250110000310200c0440041c0286801804035a0030000b0251001d41031840ba41c0c00c103d00d0f0b190014050340824030a2012400340110743c05194050302c0c06859049281030140d02103555008852840e004100314990700040c0f42d613090085c0198a5041d401c03c00302940c46455074035a140e0f4522419015105607655928107092004135a80e401608810aa0615160400450b10410070131055940403251140c00704490351810058110b42c8003217409099a480c000b6006400c0704e02c1310801c140704440610004002440c40740c018103810380c24490168450782130b40b81001030605001c07800b40f5041c43c0a03080002c5d011a4801a002c407a0700101c009110380c541040c0507003002e0345107039041c0c000b52085d20300c480881c5a5407100e035003e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 773119082 1250 773117832 773117867
    0x706090203030d06140f06030f150907210c320c1605040b03071e0e090120180103020d0609290d0209070806010903050303090a0311010b09060d050c060a030203091005100501 76
    0x1611000b000040012f041220900f01140b60310306c1000f100230790051042a05440780404000a80f80c048008d0060f030020000d440c10440d505500014401c201c034040304c40ad40c12945032a44426104503070300e89807480b1078421462000c860200143d81d207010b020303000d4040e9000c0d019001e1207052502d941018245d00c00035180c0a0103000380010524101001c0d148901020b40c000101d003115031004500705101a034401c4020441400080242c1d004102510719540d400d090050362001c10279103800160649900854035a840c02440c0700749100c035070300c11075090603075a100c4045201c1420b040081084025001a40000c0038900146541d40283d00e0280c00c600141004100c050740c076a2180d2550740100d840c901c0b00d801502d5810f04044e00881513421035007152009105400c0e90f00c004c203691f1000240104d00c9040c0402906060000600c205003032039030054611a6a81c1f48420058060740c41610000300a200750101c1102010715807003041e01031201c80d0079a807805031030540111707601c920650070000c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 773120332 1250 773119082 773119111
    0x10e15070b160e030604020604090c030f0c030e0d0914090c070c0303031d070308120c1b1509010e060a05090312040b27030409020706090203030d06140f06030f 70
    0x42000300190381d1141d101c00e080500004030380440140f1110b5142c0e03001d8000d5000b80d00b884016654007060710143c4026481c000f9080003044000c5001d015000e00c4019014585203043d00069816044103450001c950308a03851900a0340307084468080f5489008c2d050b554065502d49245881c011868220102030b044906001007900c070b00031041c000c1da00c1100400c1e541d01c03001c24050304150b0780c001c418454070701a001c91481e45c1c9440c070051180c608149142c0400302c00044560142e5825119000c481c00c500b0740a0310071003d02e013551074000300f110451400d80c00e00098103101d014000c060482004102030072460f1101303240035005c0e10005c0c2560203075010134450f19006084030300195200c0ca001c1c403401d9185040c81078550381d0f00d1758003611800040322200e80c000000d443c00021102101d000c81d00040e92840c860400c8002007a0aa0009505010000d042004180d03180c00c8074041d01c02d9040c22000d1070b14140208040400101001034000c00b0900004890582d06007405500486d103800685 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 773121582 1250 773120332 773120347
    0x906090d0218151206010e0c071203020406020610180506060c030d0b1e0307121a0702010f06170d08130501140f1501170709050a08070e1005010e15 65
    0x107040b22480c0881503120039400c0c0400500200600308651040020b54880207540c0b007524501d92100300501550384a4800e000104800c0a035540440c0d0100d03400c040002440640980001d0180d4010b00c5202e00520a981c080b5094880c5142c0b0841102d14200010480751300d44c5401d00c02507c4010851035016009020790b11040c24140001c1c078400c2040900040c002d11030ba01040090b58104100c0c20300801030052481640d00c3c00101d80e0250307070100719180c206004a107814811000d0100004120308042c50906c071500e50150010300300410b4840007401043c0e1100300300350001039070b903000716440c0e48a03080341d68130b43d402030710241d41080c2d64415140c450842511500d0130b45008222032a00f4400d958100074082109141d0103801000401d445c55420160100007400c107903c6035107400c1809901408504810b0041c54214020709020340003034120366903400c50a0b2200304911520848003100000110f00b1500200f0000c1560030503140c461035500b0010502c100a035510300344400381a820420315 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 773122832 1250 773121582 773121589
    0x3072601111b0709022b0b040213080609060403140705010f11130806090604080306011101050c0301050a0812030c0a02070b0f03010f1202030c010807090b04030b0106031508030906090d02 82
    0x804200410782d0200a41045042c10745260840980c019000c10b8410300600b141c001031540010051142c2d2400604d14200d002e000320000c01504090135806403000401240c141c03055983c03030003242c403c942510100d680d038640703441c0c0f01c0d80111030081c005081480c14210b01003041016100840c055000041e42c4030b40a0401c104546025219220000c00030070405904180c00d403900000d4240840a0300a03401d0000c80255103d1004d800248000c0021000540c5a48030701d210400302441c0c0e000a00c40e03414100c16214442d8403e01400e4060b0001c030001103008800003030a0300e0031142d01c0301c203a455984ea90110b1041500316400c0f0344214000c8550004000860401500101c03205403031180e034a514204005610310303665403101080c459007896103405a42c0219080050500c2070074683d07000e5540d0042103030a840380b6081443c14080118001c0300380105000345905071092600c040010714842907000d94174242c90f104040a030341c8100138214160034000050000f00e500a00b243d600e40c100e50740003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 773124082 1250 773122832 773122837
    0xf170409060308030117030a020d030b1203030415110901080103021507080a05030106090501090602151017100b04050f0a022a01020c0615010c1e060c0c0309050307260111 75
    0x1c1e03e141c4000300042c88440310069041500100e1900150b1070020f50710800f071f4851150300040c8052581d207818007602c540321340c031308031404070702013404c1d41d40da40390a00c0d107565890300c1000088200d5143c00f8100907854120f004550b00c0e510161104080c5d44e20710703400c02c6403940043c0d814103c0c11740148a002d000900724006440e80f180745440e00c645035810800018990000380d4003084c108440c8840070006207801003001120201e00c6a50700000d40e0301c014144c610516203a102d440d9102c100d40580403814804250400740f00c041407000d000109120f02040103071107040c3c41c580e0b0b04a00311700c08202e02d017010381d00410956208080500100c43c0c1900c0d0b900c44441e00e2031002280d42d400044911085009010041d4031080c0052448500025080000d1903456aa41c004001d44003a141c45000c80d0040d41d2943c4480782c2c0312406000c1070490100060400b14105421004a00182004505403601040c80010303075a07010304c0c1d0004001100905030324404d03035088400940d541e542800c05c020046800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 773125332 1250 773124082 773124089
    0x100b090d240203162304061d090c040303170106080105270412081b090402070c05030a0602040503120a051801031404050105150102161401051c1d06040f17040906 71
    0xc254829151009000e00356400300420003000b81d0180b41c240d1750a4000c0d5080d0380513101c00b490320200b114217054070341010411918100e0380c00300d60b0804108814050b20024000d9034800c0d0354540300b040501e408900f000ca000c0c055040401c0751a8014003143c100011480c1c4640c03074240343d400d0416442071070030300e5104090b14292142014400d51300800f5400c000800d400030344411130789283e5400c051501c03505001d801074062207150000380c62014000c0c2444180080d22008044c1d03000b0507a0f910b4a6402540b0603ca00c40c040d02420699180314503245046d589114803603110340349455500c808032800ca42c070340001141803550781c0f10f05070a504280b1003801c0c030941c81140000340340c3c20810702c52006480714032461811540000c90641d90030700d4400030041160001c1d01707e540d01003000401a1021700550f0342950300501100e0315500064026080b55070135412400040c04d41807000d0309840c3d154542214007a0081492685810008141e00f0004641008a855403401c240d11102448242c8601c0d50 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 773126582 1250 773125332 773125351
    0x210204030c1412070e06062505010c230304081912060f06090b0a02071815090504023a03080a1a01170c0405060c0303100b090d240203 59
    0x102070003800203100d00700005400468021041d50b2041c00320b103684e0a018090043e421070810301083d4591214800e48501e05d50b2040080341055040d038451107502030030001a1020342c02c01030070000c40e074064400d0145903940701c80c244464140a840e00c08140e480504201d4401d0001c000c035107002400c504501c0c400a61a903124160704d0407032103c240a43d000780d00140a0041c41403000c00540740c1004410080340c140e03080380c90300c40c0080b02007070341490310650086441c3c0c166840c8003601031131241e1000c6891000c803200720722400e459481072070441e202214000d4109401c022041050341c1c013030060f5040c81d01001d011401081c00c284450780451526030007140414120070622841640074040c4112007000b2074a45c21844100c00300003000c80300c240c0e920040d0542e021022450707481891046601411014141139907a040018100790341f60720072520400701c1c0d180404041a20000503085588800004100c6c0c5803d6003280c030f071030055800700074190b4281c00c1210043c95502145001944c4501c8150 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 773127832 1250 773126582 773126603
    0xc0e1302040509030a020c010c020f100203120c0316031d0318030601050904081207031506110105060307240507021f170c03071407061505030106080c0a0621020403 72
    0x14030500041c1c1d28041c0c010801d1360018410104200da0026500b400c800302443e084000b443c880c0042981041240c4410740c01043c000b0004e444590000300511404400d0401101e40342c2d80c41130001600d02040ea041c052450131048071b050020b01c641c210351001842c00f010482101011804030b85154004807402944590000e203080c094941031011600620066804440e585015130fa500900d01c1400c0720484003a40c4200410500d6219601c02c91101030b1072105205c07113903100c1c03030040c04801d10100011215804e1800042180c00e02151200840700843c002da031070318148040c8501054440e20103c002c1140500c1014056907501200110358a80c180b05030f940c40b2180c840007000755202d060f6180d2915002824040784051442c04c5035440b980e1440c05645103404d920030b045a500c523205c80074280f036051910b00c55450b03030030300c1041c0111403040340200080c69950981d10344581314041c1a171351000c1d143c841004441c0c05010781c106041116244010051407030042d080407604590819599029003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 773129082 1250 773127832 773127871
    0x12140603120304081e1201030605180c010207030201030c030b0423070203120118020409050a060e100e0a0b0f100f0207091b1409030304030318060f1403040c0e 70
    0x60040140d01c018801c0554518034203500d414089100710703113160b8130819071925400f4174441c18000751081e09203024001182c6580d41d0030309178050407056a0461f46a00146007400d030000c4005044294a07206801400c5032501c1d580065004080864012043c1500c400340001c550303a4512600704000b01619051460b40c0385000d2030b60035030000400310400d540c020400d02a0a0f496600c07103504541d500b07a44810322203e10070381c85c00a80115480402d08074244418400d0340111600300d08207444114411201d15620b40201ca0203a50b02440744c180290105800300740c9406281d00030010f028030141010000c281290041413100f40322038090b00015982c00045601e095060207103400800041d07000707004001c061010f54a812540c101c052051007050b1132a4054038881034142d40200500a055076102c5980b4100a49214040c4000c0960301c0e0754a00041915806110500c0700201c5517540c40e000403030310842102c00755101900c10340b2000e40d42080069440e01c0c03501118403c41f030412085814024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 773130332 1250 773129082 773129089
    0x5030c04090206130b03180f07090b0402070b0a1e0c170603010e0a1b140f04090302070b030c040914131e051b040c11121b01020d020403030f050c060c0307121406 71
    0x3120102c4291a041023103404040400002c1240c16694080c000048490041000400034800c034000246154510001c001605020746d0001c00317510710b00311043d00c4a1840e04450b5045038107143c8144081200040c8110003543c03040b240b56400403001c2c0000030706283c1018160720300418840e045070a4002120150944003400031a980200340e00003003000a13400290003e490244804646030086030343d011040305041c820082340e801060944101740ea24180b010628060354003078025501400d040900c0301d1400c1040200c0c2c103103c0d020034030b03500e40600c82e1540c42404101e81e4008030f44001c040f1aa000c4003080040c440807102d551707404047d11a480d000000d000680d0303508981e82060082c84203c52403800e01c0819400007001f000d1032140c2c2c0d0781d802209508501540b0f00c40a034510b602c00b194409400825074010020780c0d0103034603100c802c501011404c131040c1c410b00c8615036554000c2408034240780202000703140c01c03240908020121001c07400c2110215102d200600c000c1940700d0302031104504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 773131582 1250 773130332 773130361
    0xa05010c0908012307031503030509122a010203040e0a0f051602100c030207080c06071403010f0b0906090d060603120c0302070b16020907080a1505030c04090206130b03 74
    0x100710020300c1803450340d801441801200920160590a400f80040c1c0d0061003030b80700028100c0c030101107c40041e16420001e250ba000340324501d01924880140b110030000000c4e54103030815483d49222415184074860082081a5000c400c1c194071080c40b0108051f4182c4c0c40729071240188400000f071950400e0109420303510060700d203c050320345034112601090380c080f4481d50740c14080c03500030034082101c3c0421030080c40703000070103003048801044d00130324018041680c5000c0c1c403903070f606c0454800407088440c000b48420301c50786083c0070005408210312000c00d80905140100104103504003074002000c5000b16805540896440b070f41d0381d8050081007203038201304c4000001450000031058440e03901954403840c1c0d00030074206040100700f48400d589140c000b400401d80c00b900c0c46049041c0403801910a10041e9401c4204900744410300100c094005451421100000c1c001c0181d6541501444006d200c6044241d0b0032010410407518140c0c81103d40c200102074103441c05640e032030144100381149 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 773132832 1250 773131582 773131589
    0x9041d030a031e0e10090311070608010e010b03060d030c030e090a0504030908030a0f030e0c03240a0c0801230402031501021002070c050108090304031e110405010e070309060e0a05010c09 82
    0x1d41c0381210312500da804c00510000000580000040c12286074201a5000f1a480500451503c0b4406003c11110360182169040301c6009a41e00150f03602c138001c0444601045a00541001808c000740020910500b0300d00c28080c000c0c00c04609040c2c00340089084060100d4040311502e1b25401480205507108004c40d0040412401946c2002c030300c4407006100d007170305800c0141050b4880d000e8401c070040c28000c1c04000d02004040f0b48a40c0c01540e07105844100c000019913032460020700203405407080d801500c0a072903499440900c241c0c00c1040f4044000b0b000b0050041189440340007545a07101c920045000d01814440280d411580d0700009141031100401151014014420140003c800b0a1503030140e400909041c1030744d64456145514501039a070024043c0110380d1b85046c42055001c034079443d1640112007540e8128100340601003542d000f8441c10803268400000203812611039804803600ba4413408004c200b82c2102840b5500d801415102690265580c01c1003001c603540018190009 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 773134082 1250 773132832 773132891
    0x218090f0105061305060c0604020916021c0221190c0818130606172805181b120a080412210e15040b09041d030a03 51
    0x91405454449031403806100320b0380200008070300c454a481901312500d002d040d001e4a1152505411018180d94000c181d80aa011749c000d01c000ca29502009840e00c11050000c0c3c0040024040401114801c0c4000e4400ca00440c0103000e000b0621380350031101c0c8056182c3c1d00c1002500c2d003180005100241c000f0050403002e004907036840340000f070003d50581d6407110785035841c2c007007503140900820044c5030a0b68100c850141fa10704003040ca00e80020004080003100c08101401f0340d00c01143d40581004400d14000441045e8a4414954026080a5801510a59000200b80711941c0c0301d0310b01407281022003c8904078030a4241e40742820000c100e609641040244900100360316544014491805074190307101520f076082c400c2c0150200349400d06d4404401060402c000c0b542d008009180c444981d40c800c00d0030004200c0d03010000015501030b02e041543e034910b801c0c0300f003080000410b44001103ca01c0b1000c211505660201400501100310305a01c1c0824260f8060000390407001914895610 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 773135332 1250 773134082 773134099
    0x19030f0f0b01060e0a030b060103061d0406290d03121e05070306150f1407060504020910060e0906030a08040e01030312050c0412061508030703031812080c0d0f0218 72
    0xb145e0345101440d41146e8004070103000075103480300101c014040c10380006194504209000b1081d1460101542c030440c0155400c12200301e50b0490801c03c81030b68172501914044804034408903241000429034075074400d0910130320081d02030b291079040d1440d020005071801956140c0e610841141d000e99a40400f161800b00070413414034a4500200480c9000442001006104441114051001d45010728003e02042e03480d01118a40322000c0c1108a808902660396803000c641048500c04100c0203a903400d8850804030016001800b08841e0000c105541c51b22804c0c0d4010081500e01d001031000c1e040c0c901c0000750b150b056040280102200003552219507151108014154500318281c80c141e0b00e5204250b495010b06040c8170003c0d1051050308214061140d0b000100501d000004200306032080e00c00b071040130105140d4403400100303618040c0c28070701d110b0a12000144070f801e140340d00101c1c0020003420310b1900c2071814200c42c1c0051311f502441e0342c006140da00b65403c007004200e200004130351004 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 773136582 1250 773135332 773135357
    0xc1214040515150a09021801090506030a020f122508070f030b040906051f0e1504020f070506072606010e13092405220219030f0f0b0106 60
    0x30b03a108000103900044001c41000301c0c0206545180d0004407080041001803c0307500c90140c00020361110401202840382a02c6100c01540a00092011504014600c07400d5a48180900c0d0295201d0100c102d81c0660401c0000d18a43d0441415801080426511030020864030b11010024920910050a1040540400c40d85d039602c40044c08440d42a4503000c200d280701900400c3c042c1c000c2880080c03046050108000d50706054242000a4103130368107500d04207640e107244c081c40210090fa201e01181455600f842e0090401d03030003c250900800b00d40500d020420f440f200c1c14401d095882e08009113070340302400c804400d00c1500c10003403d455180340f079040c00c0410019002000d040d40450041004108020110340180c1c0309545454028403000034580582d21041c912401030400c8001c007610f00000b01d000004400d10740b41100d1507400001f40036441d40d408110706c408070201c810303031410100710300440069403282c85000074074030807010210400c0052601c004e851038160004070402c5484103404 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 773137832 1250 773136582 773136593
    0x110c03030406090201051207120b060a020c06030402060f0705030309061042030905160e0a020306030316060506041a0d06020c070e04050d080c0906190e03010c121404 73
    0x101d801980c005000914040c003480161064020305000307144d0700000e1020000100e400c180409035281081d002000111081810088207014044403200103910100c218802414008010f6030003a0005003480c0c1002c0030030310307038000d00d41c000314003260a6003010050211000041180a400110b80208401c0c000d08180000040c1c44a00c0401c003010030f841c60b405080016402d00304c3c640d00d0013031490010f881480d200090007510707a00808880324414031002c0b00160410080140036607010009510b100c2e03c1d40c500c0c001c040d40015240550500042113032407a81120700980b040e403940b04640115592070008100412540000e0000c001c0100408802d8140d0340c5083c00b450000c0c1e1700100c0141c81c0e005190300d10740f07080000d42100006036524418403003405000110f100c200381455a03841244da680303500701e80d524083c80b00c1c42500400207114000305400840414010600a4038003001c211098000203400e42e8410469840480d410381d400c04000e590900881800c0140c60800001500f0590b03510b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 773139082 1250 773137832 773137837
    0xb0c04032108220f11060406020a1401020a050a0503040501230609090c01050901051612270b0403020103021809010e150a0509040825051b0f0d061e1806110c03 70
    0x1400d2142c1c0362611800c20810003a1004946005491180c07036945500b4069500c5140d01cac8243e42d80c140440214141202c140221181600d05640305030030028070050540e880d410250080b51595222a00b081d10f105403d8501c1d8082d000e541080350890070800244440d12a0141c0940c410703070455a2900103c0c3d0300b220864070804400c0c607110703541e444c3e59040c40c06000e8420700000d0820110501c090001c5a115100c640c0d4034103965800355103550240000c40720203e4138414400400010311042000d90300079806002e90483c000c0340a210345008d28005064080c090700689a80200a800d1121a409440340c00c405464280d0b0503580d02030410000803082e460080008103030440001d520307200101c1442825000600705000da5105000c986880d90b1203603a207a03507028909c00c170149407200524085015940402c03010344180010310300e035106c51000e02412010400c070000c451340d8050007603581c1c0c0701e24a48030b0307400641301d254082d0780e15000c0e080d02c0e085052200c4441d414090520459004000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 773140332 1250 773139082 773139151
    0x602010e0d052a0c03150f0c090a150207031713051201090b0103080c0114071e050c100b0913080d0c021527070f030b0c04032108 57
    0x81c402e449210301d0100340d208407000110140c41610458200d078811100013004502e89038100e090b00c0d0785001c01c048002008500302d1360b40010300076036404911241101c0009181300d44014200c1800d103900c88444200c4446000c104000581c0503180c01c00c14001d5410450216440321102c452406080200c00305101050f40186d40c0b01c0c1c0020707000080d8100b0254006408258001880540340d079481c2030803d441c0d0001203c0950340c0d401c0060b6154805203c10305540308031103545640341a030304071b18010138580740c00364a2802400010030400d8a04001000002c60341e0121b000b02150760404e003414004507a0000d00000300361840802c5050010703070040140e840801e92604005040708103590224600042103640324030618040c010b002281c1c550001d0300c280c0e610103492a12541c000b09580d00e1360340d40c2a205066400200c094140002482d0568564010301140c403403900306034407030315207032010504c03901c82d040c0401080e9250075940340c114108991200c007048481c0a20350000f20f501201054009 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 773141582 1250 773140332 773140337
    0x80c1503070e0f030106030f080d0f140f06010215190f020408030a05070503040308030403050c1b01082d1003050709090309060311070c0311040612020319020a0b0d05100602010e0d 79
    0x80c0300c3e45154a0035070062001b0354111030f50741a00c40300c90034062070990006020750143d904040c20001ca01c1d81d42d008051584011005014191752515a50001c010002c6d29560441c020301028801600001400034042c00303940702c0b4081012a02c11800045952410031a042140103000c2007081107404025600355441500703119544180904d04107003584217580004150b40c00100503c800d240d80100908441c2d801c201c210799404035070152100e444000310000500143c00180061032050714139003c01c1180d80305203950f804084c0340186000e8603200888413400f1440a444007081484801c0100100410440717108001000142d2001030402042d4000e41007031503183e040240403408000c3c101e5290b290403041c4e951507662685811f074070070702c2c0e20340140707110318200000483d403408211001240d50354014000c0400d64002c071031440900c114101c00f80d07032100d900100000c010204000420440000401c00513191402901e1036503465202e41100045a1500728610700701e07600050034040d2001c0d42e0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 773142832 1250 773141582 773141599
    0x1020703110d030c14030301170604020a0308090402090a09091b06020a03080c0405190906141c1110030204030512030c180307090e0102030f151c05010f0501080c1503070e 75
    0x1d0a05444000800f80010400c0100c1d8010f603075005c03808800380d4162070b003105c52031070785050b600240d50b9580c400340d5010350b01042c3d0503c20000150030074000c284128014001504010080001642a280310ba019002e400d40324880041042040f8111941603c076540d0300140490500351b0003590380541017802410320500c1c83c040380894050a064800810700208000181c048204a403880b203001845101d200d00d050440203d0200d12208403400341c520050022448100308508001500080700c1040e968032610307403c0e0005a4a40054072501d40800344c0307016a965103145442c030314000d51503c50a103421014801d2143c1030f0b400b201110040c91280c00c0e1030b44c00e145541c000030b041403010741c040e90119150040080c90780e1419006140314035001e4008000d90b6880c2e00c00413506180c01c4500f113a0082d40d0038420321500c0b06260a0035070701380c0a50b00020b08081203141500c00c0300c0d42030704484000d81c0280b24105c01482c3c1a05240300300416030305030340d045092456002d4156030540d4151441018030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 773144082 1250 773142832 773142859
    0x6060f0d150906060f08090f0c0d061b11060709030803060d060e06070210060503010203040503041e0302090f090c0d0503180102030f0424030b15070303090c06020f0c0102070311 78
    0x3003400709809018080c104121450f03981801a040c02c81d001c407000c0100d100c100015080d1880030600d100a9070980021303204100b417401c10414050001142100d2090342c031540120400c0c50a583d002c00e1250035200e0004c0204841c06480c40c0580c020080010007000103c14000500c580040d40e40102055845002030b04031403034441d01411940c40c40c1c0c0b80c00d100c0e000801c02659800030f1706030641d4403070510822400b900c403c14103080c0d220482e4094281e034400c21040094400504988106100312102c0d101015140da0000318220001c1c0c42c0146204484802d005010b001840703100c2d58080100c035082c0c40405550f0790141c803805403081c0c184114030800c4260869900a00495a2540504080c4c0340d0b07031916079400018554504a8a1030768000303c002c04098540030788101b09441c00002c01d55102c0700801000180b0781e44c003490080303007015120f81143c030000f0321592030403000d00070a401804000d0b10701100d41d45000e180c001014115030207400f040020540580103010751240640710904080e10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 773145332 1250 773144082 773144111
    0x303200f010c030209011211030c030403051b07140301150b0c0f06090f1c0c060b1c0506040302011503321e060a0c020d0e040b0a0803090906060f0d 65
    0x505a03420455400c0c6286810942d0b0300d03034010410350310300340c8681c411045010f0074402110b200da01c05044864040004c0780411114401a5034018800d1a14615051000c2d074022041585490b68102c9a8000103050142800005035481070040c290003c200015400315170000c03000c5503108070011303800b00140010f4040014040b24200c895801c04581d00c5041c500c8103181d4036443c0c20205022406900c501c8000d20b5038240503418100c01940d101c002c070f2801500e428000300812800c0d0b652000640d28101031502180114821041c000c030058a00c070324080c1000b0703003598510142502110754410f0f007032002991664100140c00188080d0580481c01c01d441d407000f401c03000f008104584a8004411407250110341540342280c0000192a00b40d00c5404c900400d17202d540d005100943c000d00c0c2082c1049201d425a21114000204040344484542c4007003004503400e40c2140143c1d400c000354040ca0360501c2104150803003801d60340c0b14900403508410134118000e1811004020743c443d03050144458 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 773146582 1250 773145332 773145343
    0x7030c120b12070f0905060409020306070315210506010509010f03141005180c150307110c09151c030804020607060906050c0d0b0f030c060703030e0318150301030320 73
    0x2000448031610b4850210340c8518810348185c40d4068105000994503082c031f8007440c080564003400801c129241c20b1019000b030010308002c01d4420000030030000754021000c8a003d069012035004440c010b500e810824100207050700900e0080341c607400100190175558002d00100d0340c1110201c0190341d00700c00d0361070501001202c0700d51010304103030034000c2042ea204410715071000204122510900410b091000341c41504a501017602001e10015049d94056480c00402c0e0701040207860314441d00d00b00194690310150b070940020780d09a00140c6050500540c0c0da041074070380038600010701c1b485a400425507440100001e006d41404600d40040043c2c6400c031113001c56112000344840d140804004002d5003150501101940c1812050581800c099904852039400900030340821492401400107541c41900218201513a800040f01009401c1c005820100e0b00100c01900308a540000c2290b07400300014040c48450041004000113600044940d02e001c00030001d100303e0302007180e030140c10031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 773147832 1250 773146582 773146609
    0x6140d0f0504030203040e0f0c090d02040b120313170303070f11071206060e090a08031306150609051206280c09061236140c0907030c120b 61
    0x50074075091104040d00400684282d0301003002502c1e11f66644510740505040540720103440010402400030f07541460a802e0401600140000c15101030403004202002c154002e102016000842c540941e64001c000042c01031501d02280c88500c903031807010b2903e81c0300240400061150300514280d21034028480d440c0d8044403079064507d00380c0c0c0e8175010038919603e0030342240c1c81c5140007000300341705030425009401203603031344001c05551840d90b03911015648090490101c00011000c1f1100080e2280900c00d00800c5407940071201300d02d44071014101c555590022445042450103680140c240081d01c00d51145c408401c401403501102c041c0519030707605881c0c04228a06040c6071101568106280e04c0440b130459030b61000344605014454111030190380207070542084a803004c10f1001d10b41c9050500b50000c0070108855034540d03607038445030000c088810805504080e4110b081ea1a00315100341e800501800c051090500101c802040441c1140c1e82030f0500b07581c1c070140341254440980d403640701e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 773149082 1250 773147832 773147861
    0x7150f0b0a081c091e031b03050d0c0303020f04140306010911030708040804050607061d010e0a02060315190303120b010f050304230a020f0d020904032a0b0601120606140d 75
    0x48505503204c005d4000e0a00003903540d9088050046034030451b5042000c1200d4100004d0042d141000c2c004549241103401b05804240c0c080c8800c0803210801e5005200500c0c510403040e021491020505040c82030580c41f0004161401150700c8084410700102ca501c00e800d4a01301200350b51740c0c50000e00d107020320303007000e500100c021402c04100f005561080072180340c02001030900c00b1021841500b40c80185c40c0748100b5405c440c5060005042840207180c20448201103040781481020108140c1034140010027407004091004006164106110090181c9130703000c103000520000d40064003c1d001d40d00003208000d800000079050000c0c00b114080139078200b02e00040c0090717400d05891b60358650400103920230307410104241c10301d181c1140c1076144107134081c0052a0300e075100c1d24140d5242d040465400f1b4a12140008e180540c941d81c0855049580b08440d41c194a0604000042500303d00d0342c90314405920b0102d0902801c4e4104a22240c84102440307a140e44030a01d55a10002d00381c2c4014441e0b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 773150332 1250 773149082 773149109
    0x50c0315090405121c051024030b1504030c17031204030201140702010b01021002040e011202010903080c0a03030509030909040803090703020d0b0a2f0702010507150f0b0a081c09 78
    0xa84e000384c1030ba403203001c0c100395421b0042d62038450311070560b00d0280c4141d2805c0b421303e0b00452401c41340d00952944242c1e042c10002800314074000030503040062240000710640001074140108640350400b400600024002e41c050303020a000c078036540b44661034a81501d001e00c04000741c1054800d41044400c4c100345c03012403c180c1007081c0040d010382045010170340940511580740c06800040e1081e64110b962691100285920b071405400700c070064901c0583c104a1406c0020000c2820080100000544d41001f4a64000d40d41402030842c0c1028148840d550001c001c0c07440c0396507490a520780c0041e0040c0c21155240c4500b80c0940c5001200d0340020340210304558007034140b140000e081c5124505d1640c092100d041580e0001d00307142c954004040350100c100c04590300083c881c0000e0aa1030b4418100f035846c060032600c0e9410f40380700e80c400000149446400c1c165150b1001e009a400b000340a44aa00c101410040e5660f2111440c0550b01000100680c00840240c0b103491500000d01c141c001140 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 773151582 1250 773150332 773150347
    0x203040504050621070f05121507091706090c0105071104051f0605030a0f090215030406060f080c100f1b0819110c03060105060901050c150106020a030201050c031509040512 76
    0x2a00e417000341c4036072001032500d810001104d08040c070441d04040001d801405088200c411030030001040900341c0c2041100c40030001c100801e5441e074807141040c2040091140389050405680341c01c444071100ca04105052241c034001409070042c0000c0594200d401190302d6482c0015001070300211a0044002d0820050000f44079801c07600840c0500492001449040010301400d000d807164802d0081d0030501300315041100d90180009550403512070320000c202140c0d58500104c84c1c80d840e41180c040d0780c00031191007043e4581000c0c0000840c0407424648568a44228090421160504880e410b01d10030f01c02c0404201c8554103c030050081e051014059208c1034030028221071002070101c05910402c007920340c940c94001485412568000d100c0b9180c000f11000441d5160484000d0592030700c107048000e4240082050700b07501802486c0d0081607000342601b03009003545c10141070040c0410081090103645c0e03101d900004050141034a201c04035032540d10f85a03103400002605690080404610030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 773152832 1250 773151582 773151649
    0x519180b0c1e03040302010518060304061b0809100b120106030501051803040b0d1e061419120602070302070306060303031e020a27180204030b070f02030405040506 72
    0x400d90035010701c007210000d80b01c142680b541400128000364160340144400c000545c070030001800403010708030130049010428004641983c0003030318101c9030307152210364103940c2e043d841460381a261110f02d0400124104046040d0703d845440c03210180107034550a40504544604a06801c0b01c1041d500810049a40c1c0c20300a000f413000380e505203401c200007503817081031100000550b0140d80040e020145024401c28404004214101284440610a00c401320000b0182e1103070b00024442c020711088200c01c20810003400c0205800100c00e41200507105124102d084040c102e80168401c60041c1d48611a0409903d0300225a000506840c1042804030815525400070800d170003005442c00860100b0b03040c50401d9000f0358060700c1c0003d07102104d006908070004821600e2281c1050010340803602c610201244088203084002a00d4002070700f002008803142c612503200b900351400002410003400e00070348a126610816118503111004100b00303644601d90b0302280d4040740030303054003401b00143c3c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 773154082 1250 773152832 773152837
    0x60318022d101b0c05120a15060e01030f05030f0316030b0603040203060609060402040b070302011a0109050d03030905031303060b0406050604051305130506131709010519180b 77
    0xd02903003515108500380c1420030a0021805241980300c01c50240c5100c60310f040381c51045182a500e4003440d100010304c0d611880210810100e44d84054411f114050a164402e5801401c1d040081450107004001180c90612824156035010008055848190400394911301860740c440c0c00070100041803181d4008002c80c008c02920294030103001c03890000d02008468041140e0207501904007000003002c51601c60b01d0706911500c0240018103254440c3d81080d4076030413107082140542e64030010b201c245406081c401c40815402d10303004404909100100380d000c1d080700c00c020207054032644940100301c8240b043ea81c5422032459001031003980d170b0425802508109038900c3c00b0324940313580400c083c1000800c07102914005007078425103008507030101008100003001140c0d001440d41600e8006007003403141c140100200461072071005003d0030700c1c1440203806803d19030103800400c00340500da42c010090350100c0dd0710782020020b108800700d00f0b84440783c404401e04c0c0040e446401c0840e240c07113900c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 773155332 1250 773154082 773154139
    0x6090f1407031515051207090203010b1225050705010f05150907110304050f0102070503030f12070509030d12090b090607020c0316050409170c030d0e061006031802 72
    0x2c07a8068110308140f507000301c03100140c0c0d1340e941031840b081c1840a410310f440e01d16046e080d600100c0d61200d07a50b040c40c0d0126003080e004141c040c07400003078460780440c0c2d00c210b894005070310820707154078001c95408852445204c0614070b401e005021403801c060000a61110031100541c180a00030703071501440702805102d080e8401c0e0310642e000390120714824850a02d5002d07000044000303502d071509000420552100e41e50b00c042c1184103034000402e66840500240c000c450200021645618001c121502040301c010715510400c4404d0000909c25a40028451040000c5007088800814400c0410024021041c0d01402c0d001c07071402072000c00c000002d940345c41403c1c0f030b900350b841c80700c5076204143e2140d001a400f80c4000600031814009440c2c00e41c03041c0c0ca0345104000988100307501c2c40c00072250340c00c004110155508081071048000785540280c0216100c40000f40c503192403d1005000c0c40c50260140000b015615407030341d0001a41400300c2555190010b1142c52000d5902280b2024800309a0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 773156582 1250 773155332 773155343
    0x50a060e030a060b012d270608060607080d02091002030705030904020f0d0c080a0605030a0b04150e0a08130b4308040503010605030a05060a050c070609030519080c0706090f140703 79
    0x3c43c0d441c0c41f00d620320489501c0745040005056030700d1404804581e50100a852a40d00c520204411000038241c0c100901082503a03d03800341e203c0700c00f0802c1141c5014110414011354000304100d0002800100444010f0102100c0042e25044410301c40310180c05905080740c41c9518044035202c21035000b8081070f01c2184080070900005844901f40360322490030820043c0343c041e81300c1c0841c00045403a29141c012302c82012000501940d0445e2152500202120546821344c0000350040b002d0310000c60b41029011fa841e200d0325020044440e03149040c0421346d090b044c1030000c04003010b2241e02c0760107120614034507106210309068a080c460b540d94014428030f07105c1c1d03107480700020301c0e410049144600940c00001821103640c884017044058000103080218403002040741800245140c4074030418203009541d032540b244100203405694108140040090040a10030004c1381c0700042c0c201c034865540003d0101d02680c952070708910b100c40d031040c024038010900300801c3c110540023818004403400345 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 773157832 1250 773156582 773156597
    0x81c0309151a04020c100e0a0f150501080c09041401060306240504140412030b060d06080c0307032114070501050907090b0d030c081210050a060e030a060b012d 70
    0x90b0104000c0344210800148142c200040810900312554065a40c0c0e1001c142a05c403042c506581c1d9006449000c075084803200311204030441002124400d0034098600c08000385403c0092800040041400820060042001c900c001404540a4010030001c6500034001c0c4940f402c10705000d120b00ca240b00340d1443c004d001c42c400040078170f040d0040c0510400d480044404c55261174458050b0b007000b0141c000103060f2160140301e4503407036184c01000340d4230140c000001c20608004101d41045044030380da900c00c0d030000311305101140791b02c0e03244c1210311500c0d03184003814540684103031000c0c0d0128041103411100031079448140401900010f200d0314aa000355140390b85c403409042c04032228602d2054009a08000040000f80211100501d9a009031a00350406406090200c4610400c486035500c0c482001e804200134200311001c2c0c4050000c0b4100780f4110607a042c0030039940c044101000d040d82f03456007024402c85c5d000d19824090891201c41051403e40d990780c10303241c45c0602003036020020301407 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 773159082 1250 773157832 773157881
    0x16080303062407350304061b09051014030103050703020a0501020a0f021003110a0306050405130201080c0901090512010c080f010b1602041523060301081c030915 71
    0x1102e41c45240e901d000340c4850a04a00e43c07584c00544072050201c0c09140f09070289840e603610039040140c2c40040b00580955a0b00c1c051514106603020005030394050701c0d00d4104042034903000750450003a1001a150250b0790301808070700f140d04110341d100183d0090800030010081c0400440c0b0402501d0007921188551503443c401241d03182c1800c8001f4100042c030090040040c036090b2540c02603c0018940445c40d42e4800400c07082580c048814440801c0d5140000c001c541080c1c081c03941d0200c00b049440000c1905500003801c407040c000c0141008010004031201030340c0c00b50103410050a0003506010003550789100d168000c01210030040081024030001810660301c00000394103030351104c1041400c022041709400254201010100d038007503201c1107102030503030b401680d0400419402d0b001c415801e0a60b00c91210069400c00400d0040030200010f0001410000351014191010002541071102000303044004001c801001441c0d800c040c04c04c00d20400954002d0b900c5c00d1420a400f40d01400d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 773160332 1250 773159082 773159119
    0x1200d140d0908040305010515060f0703170106120605031c030e01110a0503010305060615040302040915320709060f0c02060414190e06041d0d050307122703021608030306 75
    0x5202c1409c6034000010040003081e20b43e4a0003906070b4034464106800d040ca607030130118401da042600709000041700c0c28000001003060303004e014001e10081c3c0107002c00018180403100c4000240310500145915100c4200c11900c003540041c121212000003152685078902008021707900a10041d22144a07600115405191148024044003d10f0302c005180502c2d55007400050140700038142c801200f12113603800111000e000300e242200070030404039042c0010310070300351440100040400180d01c0c017608005180e41c12001040c1512114100f6a00c0c42581c2c0c1402c03154020943e800030341140300410002072901151221a5003403034122401040074401c1036503030940c01103034070651110740c5e44040030641e0307402c0139805240c841d40f42c2807800c607450a03460f500510784015545a04000f41c400820030041d540d100195003c0c1d2050345900784510400d504101d590418001c1c1c2c483c042098065860b401c26008000450100d000100c0f04140c080d03442048a450390411a06140110005820031041d0740 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 773161582 1250 773160332 773160361
    0x1b1b0a14010206040f06180501150905011d0910020a0e010305070e130c1b11041d06010302040f0209090907180908120606090306090c01200d140d09080403050105 71
    0xa2041e40107043d580e0303880d03c40c400da400b040d200a48a803566207400c074070510703007550b50611f90174051340002c030314642924442c065250407540f0001c10f0350300e40307070060000a01d10802240300c03019426008005403a000107041c1000185e4011740303045440098180c2019422a041c0c00303490303d090300d08000d207a444c0102928a0924003540d5030748150860030101500e28070b68070004000216152040085005800c107601c0e0344515a03065230000c20840c881e00303291a0134051500d008641c041710003806400b010060780d5926040c00028815600e0f0804c3e250021000e03415108e0301070004017100322034148220020340325a03050117031311100c8a4081204001c08618003491080c0c651100d0b54500c2c0241442404104440241445501035420030020303281d80e808000c807038024035004000d04055451071001420481e503010310a090b00c441c0120354850010b020600b009031103d18201030010743c0d0b0704c02001c2e181b846441c0071110710038640110401400070f020054130a40340f14130002c1007a903d40600c041d0010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 773162832 1250 773161582 773161619
    0x203070b030f0f25020615010e032a04050115020f0115051c1a090d0f08151504230a050325181b0906080c1b1b0a 50
    0x84a0381d5010035070701d4080003d42070740004580303200e54441c00d142240b50300c610308020001d40143d00540c1800014850088201c80c1c164090a261000f582e0000101340c840030002000c0c040702c2e4002c102c1c1a003481141c00c06846000b80140100420760b11000321070b0700010104900c50040c420304e50302d180790f01c1c0c05104070003403000080c130b209950520741000c00041c078400d8801090b10400320310700840018002107440045140200c652102c0b80307001d0f0544c5181003a048180c508000028828802481d008988103070010300c2c10320b008040740104004128042d80311600103200388400200012908001410803c13402d010070002035005112034100808041c81c1d00440f039040d0030105000c030014080400110540c042c032504142c0c440d43e44c0c1c050031a0b0700b01e814180e00049449034660b240c5000201803a00190a4a09184245030f0409130300031f00b030700da0081c80d518125200190384101d1100b514085900016203008940d48c480d05107810036102c10128003400c0c06800001004a6040d0070960a418a07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 773164082 1250 773162832 773162851
    0xc0d15031104180501050a0902330c0f0d030b0f010302090306060108060118090516030e070603050c0405091003170c0616050d15240804080a050f070303090203070b03 73
    0x180000401048010403c00100c50306040790309503c200011804c4c00340c9403047e00b4408000071a0241d90040c0300d4a16000a03202138102588a08030340e0030080450004449582001400d4450b861220024a020300d2603517949120b1240c0c0c0110b900e82e542c50780094504039403e4500303506000d2110300640590040805181d81760300710000156081d442104107940c0204145440d40351120700034513248000b052030300308540c01602c5508000103c130200d22207004071900c07481d08203c2040c844000c00c0e2200030500400d010141c45e0004910122010816500985030080841132181401090f000d409101440204e407a031350314810000d5040450360a07102c0b0b04070310070050300443e66040d000000000c00000c4013010700000b40460720190403148191043c542c2d1000c41c110080c0e0803e00342001d48003003803921219848400d8081a100c9500c044087d40103036004031940d4540b040041c0a4a50f405822804101c208002c104002032540c10b420800700c4078002c0c0d0a544000b9101c2ca44080944001c4070043e56 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 773165332 1250 773164082 773164103
    0x20309030c0904020d08031f120816140102040f180e07060c081303030804110609010c08070212010e07090f020405010918090512121302010206060d1103060c0d1503 72
    0x745402d001c058942d01c41d10061061089000035a40c400c0789400945207004001d4640c1c003184442c01520b20000080c080c03031034503404071000700e50b00e651251251003041130748810301d01e10383d10030001d043d2201e40103176900000079503e0303549500012179054110b204045171224140745505803103410b0f20541c01c02c4002d90014040c15400d00005a4036415085021106145e040100003001c61040d41a02d000c1c5209503100200c070f05190814a070100c1804488610034002082340f0f031b42980e0802d00780d0001075409180b8945800c078a0002480103c0440381c004815402d1200382c44000d40081011003c0e941020401c00540d81d0321030300e00041740503500a940c00304044103401e01100b620030783c46170380300c080000010543e01c015584250824110000b03062020001003030801d42e80015101c195400304007140412201c2206400003561254082c080b24064141c02089a00b4410440c042c5030b0788680c00b40c219242c0d030404040780030607584400506003400d440c203231180142034101e0b0726030411070390040c035542e2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 773166582 1250 773165332 773165353
    0x20a0b0c0c0a180c03050f01060f0512040f0b0903040f061b020a1401091d16020a05060f270706120221010812030708040b060a080307120f02030903 65
    0x100651105a030109544076010744070303460303a65514215000e04003000c144203074400c030601c8020640d8401c0820809141c10079007000344141c0f071002c030380781120100c1c500071a0000e00200c06903664400c0c1d46181c10186841c808004c1401781002552245600c206410005a030b280e0350256224080e90050400c96810510101300031031249981d0859041d400200c074145440603400602071400b43c0e071058112240c0e5030b844000560b0400c050380020444042191181d0303840701c90300ca803c60002480c4c40512440e120281840034804c111405580780d0020448074181030072145902070800850b89590401c03070010044c6455121800702d10798140b000002065010304114080d20b4405210900c00c80c0d403907082c44003a900c03035111003916035503000800407000380d5414140340b141081d20141504000c41010401e04c000302c0d500403040c83d8003a4103d030050049031552030000c6c00103d2594444a250704c400310f402020f100d0300c042d2011003030040b0b4943e08510305280c40c0c180c0c4c8902603071002d00e80c980c100391300b41c9 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 773167832 1250 773166582 773166599
    0x81609030609020f030d0e0102010f1e1d0a03090302100306260f1006170f1b030102040e0c0327030a11120304080706060503061308070f12030f18020a 66
    0x1400c0b0b10740700501c2d6440c070424040102c0d26201320261144002004450b0a000558080c0320780850b84802c500284204544450f80341000c18000302c451000c503954146200380c40d2030130840c03035174101440c0060320034030300450800a12120941c0411391081c2d400d600c181e894a4020300c18102199465061719041c0482516001c0c4401100b01031001ca0340103071022500d0f0603d00384900901e034500740d1f4000038040e00300410442e088043e0005100395612a03410442c070204001003080782a00106184c01c42c100c0d0000c00b19019000d03d901c44040343e84400c050228140742040950300c0b480c142c000301802038549000104a46107000b00c03040445d003003042041600d510610301d407804029814101c644980030600040425031007181c00360f0350005c011442c24100082d90040c0001060220b00038217a0f07080c140c80182030358102900c02040001d002905208001101d035554140c103070011131034039801541c3c0c3c40240103440d1018503e1881450407020009460790f8541080655030040c0480c0718a50815554 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 773169082 1250 773167832 773167841
    0x140f0a030311153103050f07030908030409091a0f011509030c0b0a020f07080606060705010e0a0c08101a10021f02071509030c0201030c051209010204060816090306 72
    0x7026008080c0d0386a010a43c08100c0350003505000b040280c112071000b00103150220160707003040741e4132221101c1e0010030b0703100b816039500520388400541d40f001d4510342550304108a80c03082c2058003000c00c00044015540d440480d019020340000c4c040d2424840b5280301340d00040740d0040240c02440c00510042021350552604207819003031070190107131203845e000140101948603000007030001402d00c03001c036070500c8220780f0003452400900c0c0d828180250a40c075078500920103401203001040c142c06201e02500214007100c204020f444204071181450f034011607242c002c2405070700c101c1e2800f9058404c0b52090b4070503030340c46030032264440b038a060070003144007800e40d40c0404600c1014440c000750050522941011032003a02c005030f95003032920344251140c0580e20030385483c5251910600204c0d4214030078a07401a824600014001e880990a0b0b880d400b6541100c08003104640c208464110705500510603990f0f2901c40d0f44850785d42d03401e0140c100703400c091a040090312640c000c10000d0b445400 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 773170332 1250 773169082 773169107
    0x9110127140d06020f030108190314030703091a090c010219140c1e030114010b0901121814060901020906040b0307121407090f081b060c01060f140f0a0303 68
    0x42c82450740b02903103403071040c0e030003000d942004000000010003080c0d004100c503000c180d46504060056900644001d400b080d00021501081c0d24000005140e4901c00d50012500c59488440c121106010304c00d40d940d995000c546c2d404061054001100c1298000a980e034110310003d480d1071489038499550020341146003400c403003a441840780c0c52813a60340701354000407240b04102000c03181410400405080d075080d01102584500c0c0d030001131055003440400c41e01204000c2c01c00040703024204d00c00000130f16101d4025201ca160200410b0100f100203e5807001003e145801c0b6107158498181d81400c0780306104189501c0b1b00104001c10059181c0e8001d5544400300f81015454144101c1c124426940904000b03200072009104001c40c007604580c20a003e030034100c401039419410110f10654404400f032145151170f40f1843c040220340c0d502c10466020041441c0240300700d44c1d4034100d56890f010140039920003034100c40000d030181d081c0b001d20984a040028582d5038850f00d1a101950804084d11 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 773171582 1250 773170332 773170339
    0x2010204150c0204020f0c0d0311030601050a0f090302030f0c031209060a12020f0f0c0d0f02030a1107050612090d02120909090a2307060509030a1b090911012714 71
    0x107043d011b50005002d0300c44618030b04040e18a6074251071000f41112103071815402c00c00030500174089039903403100a40d01902c96034142181c0d4180b5502095a11000c50ba00082d030600c15868842c21525000c10401e01a400640841c2d200308034400441e00da40c0035124010340c10150500a00e50030350b00c500114044481c0b1950014600300d01e8045203101c40d4480d0760000050080081c1c3c01041610030403060b200001c980c5400042040f00c071000946907c40c045143c4100301085600a14508040c4184030007020010712090307a525a081f000d4410b040d0407641480980030b146000038105001295441b003a826124481d490950310304108260341a0240601d1320038885c2501841c0000c2890355050b503003030010510202c0e1010181e60982c540141500080f00304034040c8944a000c0d00c000607910f40c856030000e45c0510b13076551302c80d15100600459110260711810a0a110103201d0600b01400d511002070340d58452080c10300942ca22804071103c0410071a5210f031404001f01d0252208605034040c008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 773172832 1250 773171582 773171587
    0x30105220c180219050309070506030a14010311010818064b0a15050d0201030b090f220210200f03040806010e190509030912010c0f02010204150c020402 67
    0x1003410b515400c04030003107240034a60010b103603d00840450400c102d4240e0340d18001d4503510b014615151940200d204580c0140300c01310100e0704040490b081089810101c4185e40c0540d0703501c1c00c0031002e03c000d400005021400304030200b108507090300584580d400f01d1100510301d40e2590704547d6110081925004241c00b40400306030005000040d000c0c104001c4004003081045500f01c0c1c070f2501d1400507201c44400340c81c1c608184850b0600c4c02c20342089071002c80300460310040d41d000581c058148141c440e40d12609003030401441d482d40107401c1e130203891503d051a031115110300800d04103a0a4440c003942c03000880d50305424503407040964490091107050700e440d80540c1005140d16141c40c070103490305543c002003001d03c144042000120700401c48040c14032401e041103038483c2161034820b980008027a0312031700002c10b501400c01c2218081e0a000e0245040c08800c016028000d0800c001044001074542c054003507050320500a44040d54403042000f12007400100c1c0680da044116402260402c1e008d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 773174082 1250 773172832 773172839
    0x140d24050c0304060c020619090213140405010b090c0d090516060906020c33070c030804090b0910050d050c040c030c1b080708031e0123030105220c 65
    0x1034021507000d10010a03080e5260b0815280507010744203940040b10466101d8001c004145036818414455001502c0001903114200d0001c600010342d41b80b80308400b03c0c1450740e48843e0042c0e013104c0901c83e6010300000c01269900d40204a11500107503209070b0000130901100d0015001a84030241d510305c03400450f0070000300c11040503d0f690140c0e0100b404a040c8100c10416550148028000504219003048040c05121820410307c2e4050000314050302c2d83c1c100c0e18442d5024401126910340c2c006400c48a003a5880c50404090360180c09600c6500781000c03110f052504008510b94024080c4003030b1208103e051405015044079544c105440328031a0821104540c0c840b03201c0c0c01c0a2883c5a82c020403051610709020b00300c4a450580d2005440e41d603082c602c0420030050603260f1055104098590780d071581c10a064035207040c40a00c0480d0308020700006010b000e00b00c001c0c3c1c40250300c03060350031039007003c50308150880d03c0854540c150510140d940e00c1841d0701c006800580c061013503000e0580ea0380c5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 773175332 1250 773174082 773174153
    0x6060d060515090924060a06050a0215130606080a03081810050907060306060216030816060c0903060f0b06120703140405060403172203021c050d0501140d 68
    0xa94141800c2d4110340b40d1600c0d00345c1c1409501450202580c2e0106041c03d025001c185281014414801080f1000c1100b032801c510a0000e4008002140881302e00c0b4100ba0b000700d012240303814800c90b8840d00c0c01c030000415041c0411040d1900360140c0b904141540c07401c05641c0b407511210819603072400b5520382c55003540480d00c0303810b00802d008001060224280500542220b07010340210056504c00d00d4800304d05400000d445060b42d51040519494040c10844200e0920007603030010641c034280514080b21541c00b8041c44204c90040704284840c1d001100d8441c1166010b00708641c204404004410400c0304030852641c00a500345030001e0f05030b1100851000d903100680d0101c403143c00c0a001e00042c03503448a501c030165403240460b9038090920311202c2184070300d04001071742e0034008402c80c8024075000380f0042441c040c8150241010720845800100241e1200007019401850100085296441d00e402840c0044c0302070040314411800742c4491646030b440c400401041400440400c41107003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 773176582 1250 773175332 773175349
    0x10908010c03150608060603180c0604120620040608042315072c13020f090111010207050703080313020a23030a020a060c1a09031b06060d060515 64
    0x100c01d80d4000400418200c401c1148640e198060000c001e580710a0120a660704011260001e00592821202c1e02d02c0f00011410040744144080d1f001101050008050422400220806214044c200403040c200d2040300d04904038283c3d034a1583c1002d100512440c1d0044e081107800038000c401d403441d0102d000f148194680d100d1710315003003190040f4048604081241034079907008092420a060042c06058110300628031103294a851010040008043c681350031164542150f20100c06550f510103001c01c0c0103d80e80880d803103130f0014643d03001d46e04604106100740c0d51046e81c0f00010345545486c54694050940000d4007820030401d024001000583e101c512004c001c150300e1008042c18009100061a0390300c0100700716020790007c110303000050741c0c1c031004070f0705031a070350f0030921008401801d214079006100340501c00886015424010034a40010141030702c2c400741c400f19510692160400c5880302000e94465801202204140c000940b4507081903a22008036080101e46446003070001d0040c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 773177832 1250 773176582 773176601
    0x31902010f32010506120402062106030c122e020705280b06120c030304090b09011e0b1c0f050103030305090703033905101b1d01090801 60
    0x101c019520702501e102110303011090b04110b20140300b84642c03410307000c1401846601407111484071402c001908555601040da661303652036003030003108034036451300d41607001c442034501d10301c82e00c00d0300c508200910b0310820743c80080c02460040d08100011407050001a6004550350f10380170f603015488024074a45201a240480c090002451030180d928440080f255110304a2002c001d80f202c0503a002c0f81ca0101840d821110941d060200581940d0505040c082d060812540c075000015001407442d50a4025038a9800c0c111464941d60343d80c1e20881035005240c5100b10007c1d042440104003021028014104107a208008000031006c590000c2041b00c0c281c07407000200c2a0703030f40018400c0c1a031604c5500d88c400d01100040200906644000d44101003240011100344410f907181568814190700000603144c180c04004260465403a00e40d4448824062405205150402c0e240b16039940d403082070f04018954640005403482140c2c1d9004031920100300905100d44083e0014400409208000c520b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 773179082 1250 773177832 773177861
    0x1140328290703050a0902010c0308040c09020d0501050a080f280b0a050f07030e0c13020d0207050a12020102030103021c020117100906050a06020327100c1202010c02031902010f 78
    0x214079002d50040e08407034002d04502c00c541d10301400c00c00140d03003200058501d680c060600300c10942c0c0350b260884100009411145480c0c0c0045040c610035001508498140da804483c180002d68403903504e40c2c3d684200742c01300d48140c0d00c50890302c9885040c085400710104d4401c0e46050b0083c0035511048600d010603a0755010f500d03900c0c03003084003210310401215000225890240700030280c0d04040350340c403040421010701c42e8091a60658440d081903046038540c2c00c43c00e07003e548444050a10540b5003a44000c00d07210040302c80e2422140c548180b0031241a00d90050034440d5120402540b020f47e842c0d1440d00700d040c0320000701c01c030f0301482140340d009108026035802003540318100401d00741a1000381d88070600608200e1014000c054011040c0d84840310758062030306200c1016951004202c821401d001c0c0c10100d901c44841640c0e81c0712031074101d038500902e8030305201840104121f088960488555005820501c02003015148401e0203054482c028400800d49460520003035003220b6540512510 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 773180332 1250 773179082 773179163
    0x4050f06030105160f050c030714010c090e012301050c1b0f0406030507120c0f0620190b0a090204110d0c05130b070317070801140328 59
    0x640d85400d000312984003c1800e010154859082c0011304031500303000c052001e110001c10908101c60080007603a440540040b07001c002844c24101c228020411441420300141110001043d180360240400381266030b004080300c4507151400c219a504441c400030141007000401c0000902c2c1010071004d205060303941e03242c45403910f40004015800c161042c3c028003a0342800002c002298002c0342d03103000c84004174001642c10120740351a50b00d03490aa04103c034244030f0340a0120b0002e0b4015074040e2268283c241d00034542246a5140c0c4d50b40d0040c032090400b003200c010025000821510107140c0025004038041003d00d11035000030183c0c0c400d030000d4038600c42d0101c0c00e21004006401244650412070030a10701d440c031610b1440c0c1c0c900d0700c0307401082180d007000a801c00405100d040b0310950f0fa16088044421420b1050006000303410a110b0a11440b43d5014030308036500d00810040c0d0030559058102704580d00311030082d919000c5803076081c0c625003450f1248103030b8282404011054144420720290 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 773181582 1250 773180332 773180341
    0x1002031003140d1d06070b04030908030d0204060f0e0d060b0f03031b19050714030a06020a0c15290a050d0819080c041211040c020c01321804050f 64
    0x7050a030480000c003010f01c0304d420340154076482d90710403500c042c1e401010000c0340303503505c3c141034a0900d2168000c40b001e120005610ba8016001d40c05001910920350300c4122500408808841c07980ca2001c0541d1b100040c543c2d6031001400035441076000720b0000c0c00070803440a500000074155000340c041c1817003100f10114814176010042c000c11a0354480c4100039250910a40c403502d584610b1030158441240c0c21844e59850b960301001090005c03507102d481995201c42d4802e004000c2584100112807040030004078040d0004280a00c80540d541400e86000c0540c000d00743d480402e41010107142c05c03030380d446004523281c2c4400308121a91070040b0116595510000701c1004080d900c501c0060800020344280081c1000020449044445170344004407c2366050510300b4000110840559000f894601d105001c55008200c0703001560003600e4110100800000810301e0010315030b101016080108511095204510302420303442080060344100065500b001c50b048032800d1700c035880841e01400411 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 773182832 1250 773181582 773181587
    0x40302010b09042f150c01140c12070215010609031b0311100509040911120d0804060902040b041b02121c20030a020d0b03011a040b030f0a08070302010c0f021002031003140d 76
    0x4840843c81d005e140d548c91404100080715801405850030101c0c0030752000c612003074405c00c010600440380d03443e11000c65a480401805000c00c5100032600d800d21030402d24120b41041c005e802c100e030f41120800d000040b01000704801d010030780400c0d6080c403000b4400b590701500d4030720038842c000b4803a03002060b031440800308105542d000000e0b8440c556228070301c41030307200d580500525002a800100410791580740d00c00100503011482ca401d0700645021809603400d0710445d849005450380c0c0c1c09548034030100080b8111a8403030307004001903c00c50745080c092074074007a60010f404c2034240300c0342580300043d01c803600d041c3d9401503a001000300d0700400d00c84050402e910810071101400c800800040d00c211200b0381d00d112501c1980f520540d0796040513000ba4500f8400d00d03102451540694840000e075142140c002c1d04208410350040d80b8001c10703103034058060a80c40000f491903070020407200d80001c003000083c3d4001090940c540398500b40000c00560707a178a24003000101d4901a040f5482c2c0750170300 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 773184082 1250 773182832 773182841
    0x30b010e0f0c0406050f0f070602070b060f0d02030604110a03080a020c01020c010306080a020108090f030c03070b010531021b030a0f141629040302010b09042f150c01 73
    0x81281c2d209042104110060b00a42140c0801c0c12040140d03840d81040301911000e80155031002d06903c5c00052020100035044031024443c2c5800c0f20f00702c005030150380c2441108504400021341581c441c0022501242038040740c950b02040c020300c2a0000ca0b185c5e40d54007210703045040420b025a0001000428540c1c05110b001c0b14040d00381f0781003180d6450090341702c0c0d803802400d8000e03042c4043c0101043c0c0445081c0102488201150103c0759508001060325a41c0da1020f00183c0c0d80d58554800411a450814203600000080400c0c010300e038090000440b0010361066110003200d80e081102400050382c00206520303e01c5240c1c069625500751035005080b60010002c00c804002025085440c040280c4080c0d80d02c085410088001040c0c60707240003c0c0034212601e41281711000c0c004540c00f40c010540e10507125502c00e50007480300b15041424842c103c082510000c200600c1c3c444140b03860800a060812410850000103282e90307030b40004500f000c0c1a0f080300300c000480014811141c0e0f00240203 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 773185332 1250 773184082 773184091
    0x91b1e1f090f090507090e060f0603131a131b030506040f031106071b051002120105120f0a110f130609270b04032601031118150a030b010e0f 62
    0xf0280302d00e14150100600c0d030916401080c00c01540d01000ca006600c80003101310001c0f0015114540e681071400240c2810182100100c1e2985043c0c551440c00c0310340d41d611580640e00c850100c4510303a0a568940501c414100e130b04006000324941c1c004041002044214004c6004032030211107107506050080940c800010280050350240707007070160032580812500103e0300c104880c5003400420749089410051401000d15000e4000b061032100d825141d0840b46c12244111100083ea020700402d55440c4c001500c0c2050540d04810b027010080b84185103024014607004004000d6801e581c00040d19904035940744940b15983d450051008015a201c0c0a03090701654090038120310a07166108841d0300340760001000141c1400100c1c1c00c050246500300718091000440042d000306100c40304004040074441911080d4101d40e4204c1715007080540641014600c02d50b1800e030380c0d941d40070b8040e2401e0100c0c2254110324800000004107011404a90103400e641170008010300303051b00c103044880350150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 773186582 1250 773185332 773185349
    0x8060411070f022206300507050607140a0f0c050d0209040602070c0f090b0411030105010e1207080d05120105090705070b0a061a03091b1e1f090f 64
    0x2040307070003041c404502040e407070b42c2c116110a040c2044158400b02500c031100c1a03202c0c03905081c030115003040482c071500742804000c1c242128150300840f01c1000c0c59070001026215820180b8180700074107002004083e900d008110345c0c011041c50764205881c00210010940300c2d008070b110b98030200040c01000400503c006c4803101c1c40c541403500010400750002c3c1c001841c1075800220360341001500400c3d40018040700c401112066600c203d0b0350040d00082c12014420340c60f02048407021100300d41564142c840682d82c1d0340c1090702200500c00d80c0e00c1a80040d1045128250000905600c100b04544601c0380300c0c0c3c0e800e0b464440100341441c16101c180c00c2280305043c488100550703036034044c0554609540047d001d03241525945100c50080039190001452440c080004c2c440001c41d0740015400307085000100c501d043e07144103116900380f2003800100da01000d040d08881030000f9681455100c50402080c1c0e00d03010303415100400c1409101c08000000c6604000204446000b54204100414009 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 773187832 1250 773186582 773186587
    0x3090a09020a14030612060103030f1103040609030303090204090c27020f0f210a09050c0301050108120c1e071d0c0306010804030e090a0f06060504030f030813050d08060411 76
    0x2090064240c0c55001c3c01a018444080001051582d41c2022158800111001d0310a156160b0038020000503d1402e8100400c0074a4844040c1c00f4001041360100c501664524151900307647d2300b10090a0091001d82e07000307840f0403a2501081480325510002d0101c2c0b80045207110805e0a1080565290802c4140e4144140018031454030014200c51050201e440c2c1c683da40c114800a08403140420a842ca00c0c064061003003040c0384455a100780070700703405207040751344070080182018280c034424002c3e000550400384581d6580d650540180100c010380c50306661620213906010b0124246401c0c0445040e4800f001c1000324041e807102c10001e2490501040700c031031810160f054480d200160540f03040011020014003410f2140c290440083c0d4010400c50700341c205604030001506a180909000c0c0d803038098001402806401201d0440750700440140308810547c80503903a4100c010241864410700f0b04c42000005c03410f105168030034000d62603020f0241003003801c0c0821070307501038403011149004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 773189082 1250 773187832 773187847
    0x21837060506040e1f09020f0d0509010c09090c200c1c1a04020604050d14010e070f09020a020c033403020f090411030712150204060f08040f021203090a0902 69
    0x240711204d0b52140f8903040c0a040e9841e0040c40031981400da0b80110212840030408806826202004140e840e10b001028003081d1642e03c401400c98684613004070100300141410071071281075030083e40010300142440c20400e901c840030007603038000d0100d1003d21504100c01a9a0781d181070422204014994016003d850b0700303556803c40310041180680480c8090040000c0c11982d400040300c01616000d800d201d440151854201c0703101c0c00c0140030400550910541c0c0003480c0000075000c0c00c945103107201160365450300a441009501040d4200114081d0b0b1140b0310f40354030104002095491002c4850101303e4a010140c80319019160300341c510f200348000c040002d0798072620740e2460000100c4940308241c8a80c500902c060440a17007640d01405a1000060910a50003c402c0010f0107040c04a8010300607009440403441180214004910842104980b4a100312216a4401d102d44402c81c41420035030000f5044212441c0f210316a030340b00242c000d505081c0100100010301c02100b055060442 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 773190332 1250 773189082 773189099
    0x15020c1e1204050d030c020a0b0f0c0c060c0c040b120601120303110a0e0402030a0b040e1005010909030219052b0f020106050604050d02060d1119050702183706050604 73
    0x11030030406801c01014501b603c05656030f000607200100040b41d00d032543c0700b101e1150f06101c0c0d0015020100e0324023503012601d80f2800e1041c21100440c4901c8060100c2282407800c01c070041400f220f540c0c0c0c21900d40300b9450201c0b0401c201a60203880001c25180842c070051400405940c0000310094025400340280b0040540001c2c0b025003e900031600581c6a940d010700c0e190080401403401503203e0705100c6840c203407078800310314507205c1015114184a141e0b00c80301e2035010396840030310040050b40010303e40d60841d05222000858031b4810020780302031900710015800703a100e00c202060f207091004140c1c07003059a00220b1011005049000038410b0310728160000b42c3c140100e1003028007036004c0000700030455640000b16010000c141908211030b80200c6680c0f1410f8020310346038a0041100e1003009950380c0940c098814842d4004c1c1203d420700c02c030100190581e600506101411003401e2541c2c0c1c2351201c52200451150400440c480002000a00100a17100a0b038855405040f0811050000b080c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 773191582 1250 773190332 773190349
    0x2120403052d0912030c0106090221040b0402040507110d03050a14100306051512010e0c12030a030c03090f210c0302031b0a0b090102030105191215020c1e120405 71
    0x5904841c004d00398400100002e08500c110032402c501e42d4a081c1000c030700e41049034041c040f650341c00c05402c0d150b40340c20310040d16020001c2d94050710030581840060014130381504802d90203251841d250030200c81240081d89860503000c4214080394403a0100000c029040c80380700d45841004ea00603109080540b000448801c580c00040c14040c0c0319000626181800881e4034030044000d454010300c0049008418000c0c03102600c901c415001f80c083c402c00d18609004805449460b08001e1440c0188408054000740710303502d204814540c80b00b41340c1c000705d07070315244900e00c0c00d0007003482c2050f10311488000050810502d0070382c810b01076028032550100c2d07400400d0ba49540c80ea00b0884071100401c40410f03260000e10324006125001c60000c00c031b10008190007840c12110282d940309412582400030031900805c03402140100b048800d644404200300003c80302107001c00490052802c00300c801a141001c04d0080c078101000544542c400c40503401700204070301040c01800c15400c0c5410000001c8400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 773192832 1250 773191582 773191597
    0x504082107141c0918021e07020a05060d0b0a1a04030b060a030f1b060f0806010c030e150912030304020a030f05010e060f0402181005010302070602120403052d 70
    0x4901100082d542000300300040e1400d10129104a010720009450060400c1306a001e000396001e5608002c480140b00d40c000c0e209070303404201680e1140307801c50340c4007410703600540010381e40324a0040300018184c8580e4014040b440d10550042070210b0b14405001c01074003540e100a04801e00c001e11048201c4110f81039400b41c9500644422072034a0b40da0000e000d652a036040601100c00b14201c030700c104461200007207144800c5c4443c0e5400035581e48010707508004044140001b04580d000041c040d03610500f20303440380c60f202c0d08000083e250039a0102e040d4008051105954103400109a0703410701d00000c50440400a04009516510300f03a4045150750703204c2c2c4070080400490300614002c01400703400204040017480200d6400d460888a20510310301c00341c0c1e05074010000b071001941c03480440c42016210b048840c0d030611641d0b1815004400a5001c030205542c819824041d00d0880100c2c25400f6000758043c0d075801e600ca14000301484807028000900f0074010301003034700100403030400d0720135203411 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 773194082 1250 773192832 773192843
    0x80c0a0609150203070b100501020d0206090a0b07120c081f0302130c1202180f0108270c04020c031e0301140f0a2d09061a0a02030403120504082107 65
    0x1c0c0003404020391031801008170050004c041001008542c09207000204c00310f41c000da0072034616650940d001d0742ca890042d165448184c001c1d8040c2400314140f124110b400c401589851041210f84501031070895405104800008a640d014004401d800c10324130251441c05040e0003207100d25660001d602c880c20701c0d40641070f1507124040c09801310b00030a13020740c00405815056580e07513500301031040507420003443c10f441001c00544500340e5510a41c038042c402c0c904880d05140300207080426549003418041d6601c03440c4900007041d002c40d2910b001401030510840011038651500401c009410143c40d1549007c003841031004009422040c8002c068000b4240c0f8503800901c5040302295000940e0303000040310003c10030701c0d4803401090310100d41d48460540c42010740c0c01c0d00c5800c3c0c4015518030f88105081a46490300301107240122200074450401603004680c500781d40c13651a2003412260500ca6004140301090410010400307100c0c94070300b400704e0701c002442080e00b00c0c01c40c00c00e4020504007900 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 773195332 1250 773194082 773194109
    0x501020c04200309060708220b06030309120c040b030114070807120504030203030702010b01020f0c13060e07120b010201061a1605032a0f031b1005010906080c0a0609 73
    0x318141d4042e00340c0c5502034543c2d03914242c049990340300b805584080014050b1400a4a64000b440c044a0481503011004011051a495012038944040c00d400d44c540000c100e903041c1696040380781c540001054002d010345134080400c00003100c44561031940240d0400c846c04034000c81c81401d040e802102410a51050303140d5190403100790340e004403c90720251504003032106251f000006036209011980c001c3c023007807001400480e224040d82d6903012159000340d03d0b0f18523601e41064240c5ea40c000ca0b800c0055203a68030740c60f00c1400d010135140100425103090784040c95030810f0042c14900340b002c4c0000e11046180001c0e00340c01131722109640705640004200000b5851041c1e41c04a0740e141c0010440703494410741340d602004403101915165548540c1c1280045050002c6030340c0d810007650800ad14100203c01403051070950b1400f01c6c0c00c0040c020b0780151140440740c0d10850f0b01a00d5400b50009105042149151501001d410350340e100f20070001082220550213417515003a070720410507550 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 773196582 1250 773195332 773195351
    0x601020d120b03070b07051605060301180f23090102071101080613060305031b06061c0f0b0708060a2111030102070c03060b030d050703050d0b150304050a060c05040501020c04 77
    0x10042c0a45060168140141c020016440711208081c02c3c0c424000e40981c3e45400b01c1d03412143c1400e54510489810801c2071004200c140d0940504041e021100b0401180c1d612442c40150300311682004401d901c0304406e4034036800704446007482e80e4042510700c021890800240c43d0180a1415242990b0403c198000058455210034a080d047c0300600c80c1c1c288503a039120b10300309459400c100484c4072000f19007040c1100312800000c4090290700c020b0420a840c442441009980c040754401c02d88502c0441040b8200145194480d0361050803540d54800140c10400d08224120050b42e006640c0301030202c2c007043c41d01e0002c1140225003a802a00c1c00009141400403901a01402174091301d0480c0b403c00010034403105800107461300004030240c0381622000d50050341e140c0140c0501a00041045c444118070185e00d40c440c56201030020145803101c00790740e20602c0c283d07204442c1102d00d27810696611041003094012140e4001003800d20b1400c3c18207000c0000d65410490000b80d01c02d540b100d1240 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 773197832 1250 773196582 773196617
    0xf0d0203180f04020a0e041a0d02060703110717010f0e0c10031b030b040b03070305100213270605010e151804020c0d17040f152a11060601020d 63
    0x24102100b0150095484681c0c41320050207441c060740c030381c41c0602e04103400404c1500102a610091810080c80c90b100720081c2d400307105458000038012004d120700b8036150500203400f00091030041005001074200500c80c11441405c1d039410704190100682041c213110242100800d44d441d40c1c0205544001200400c440110060101c680c0442c0d582c108907181d8007010350b0315400800a10009560078000a002d0000b410b503980c0e06484080d1082d000031b442c0040415540c2c00800490101c004540580c64940040485040720440e0508d2413400400b005a20004032b07020342001081c007400c002024006c0c603004102c1051440ca0341210161b800940c1c0954040e01c40d501d00781803803000c1d104540351990030425544e100c078451910408200303004122030301e4030990004903126075441901607500c1c179103980d520169002d0580c800706585480307513807001e06074020f240c2d02c02c5a5464050700303200140400c2c0010f041d610140035201400e801040030051641d0300003400d030700010300d5840c03c00e40f03940c52403404 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 773199082 1250 773197832 773197849
    0x2160f11060a0c110a1409090a060f14090d0e060906070507060c050609030a020706210f05062d011b12090303090b07050705060306040204120b01080f0d020318 70
    0x149540940085000303080030707034400307040000f09202d402500400401101042000707020b5110303000c600c1c54000180b080604007102096044092242202c40c0c40500d603850809803442101c0e4441c5441d65404c0390210074080c001420341000c072002c082e0002501c11400100711b19030a001990040388001000040780c1c440c6411211a15044000d4606450b1600d00040284c0503200064420b4410b040216040e14404400c40d884003030507800501049282c00001e031a01030010303100551001c0d0005205125109038003c020400b0803050000a41d0300e800d604128860b180d54580101c41040c2c403e455441550000490841d51804d0a140040c160b452491071240c82d0130001c02007040d002000c08100300e91b000011242524800d0b12000e041c03a4a42011500e0f50196003009461030740b1a410411036814004011500301401410162a150300c1d0a41c4080040d40f4030001c1300d0049007480100300018090020b401c0d4442c3e004040c00c41c0c083e607254002c3d501c0c00b85101182c4110541c0c01c80640c41d5907601d01 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 773200332 1250 773199082 773199113
    0x14030d03020a0c020604030f060b12190c38040501050d09060e030a21050903220801090309080d090e1501050702120c0103060e0702070608220f060f02160f 68
    0x1517564881e180e11f40341c0890510004229842420000410420f02d0a076503802d003421080c400800821600034014614110060070136190f03100505408129549600302d03142c541500030b0743c0100b07110001024030708001c40d03024207400c40c0c050a000030300a5a80c010100c400f1a2105c0740080340c034854604202c002401c00540e451070718480003030840015a004a4540c900301c200580780700c1c0d840c103900070020a03540d0440d586081a0020052104203030742d10340e80701c286c0e140000e100c0c10308242c0b1280328908440e41c000c1d0030760110318401c4040245940030081426810f681d407400d100c046151008050070560084c0c151060b00000310039a90b200e0348900103403402107800400d40306054582c04042c94846001ca01c4007070009043c03000c08104410303181d81e194000c8030294020103240c1d1800d10200c540d440040c180c0d8095080c21030075622014801000c0e809090b001d041e0020200000b460a5400c440045420000c03445c010f12610850b5040c0e40e064403000d64029035801410846441c1004800c042c600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 773201438 1106 773200332 773200339
    0x50105030105060a12060b0408160501020604080f0d1406180405062e08030325020c040903030f1a0a08030c0303070f1701080c090114030d03020a0c02 66
    0x30b0400d04c02918040454802c210034440030344480707902c81990311034081800c3c00200310a1000311403079807402c1c030019946860000043d442d0f80000300043c0c00b15078082505c148141d005d404603240d161030b500c41005902d2600c03203004640035080e00c02c3c6010354000c811a5030b404c89040042405650403000400302a42c0e4050300e0140780003c20107071704c0329070001d03556030a11041008500000e02952805942c491030007000d11240740d507010a01c22401d6800704c0c00030052940205005800c031100b9034000c10900b0090805130040c204041140a080e840c00798034000b8583e207210000da1405c4126203a012a5075201c15242d62401412410500e40d0001c102180c0124010b844d68851890703903040241c4484045003031204548401d80c0103a140d40c100d21b0002c0741e12710b840c241c224003400b802004032907136442078404640e1310000c10521000f03055001400040f05401041d01e04e401c0b55008 = true := by decide +kernel

theorem cover : BRFrame.Cov 773021582 773201438 := by
  have h0 := BRFrame.cov_init 773021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 773021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 773021582 ≤ n) (h2 : n < 773201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
