-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0311
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:07:40.266331+00:00
-- url     : https://prove2.me/submissions/320d712f-1a0f-4346-b128-8093fc5b5769

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 55755399 ≤ n < 55935255 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 55756649 1250 55755399 55755407
    0x40609062102010f1b050d030b03061e0420030f0601090b060304021503090a140610060203161e0b090a05071505070602071a1008010b060405130903030204080d0809070501 75
    0xd4000380050300c95103015030b550b407041401d020b403c207150700a00100641c964446d031a01d40340103000741c0802d842d6004040a403600f8044a54031803660040c420310b2141e140c0901c101c0c0c40000300008c10400c6642006440040c611020306034041d0044c1c103c0740b400c1180c94410f65074040900c03d140c0980d04003440e448035410f094090380e02465002c0d201c5072030001007a00d41d001581000b40b80100034451444100045044040d0540c2413110040142c0310500381181c40c801400015000b580542d403042001c883c48083d4440c180711101c3d0090080760340600b030382ca040305c0f44500c103007005042d005918060054442001c9100e91800e03110b042111641ea558002a042d80310b000c00b00340b000f189043c0024000310340c50350001c1002901c43c2500861001e110402280400d000380c6040705405103654007441002001d108441c01100c007224200e041518040000e44400a014801110170b41c884c290081014040e4064502800101069618070095075a00030030418044034008120700c280c020010f065402 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 55757899 1250 55756649 55756709
    0x7020303071b1d0103060e0f03040603060f05010c03020c090a020d0e060a0e0c0904060e0307020d08030a050a110702130b1008040b010e0106080c0307091a0406020f0706051204050102040504060906 86
    0x83c016030411560328680380d80300144060000300b50503002d21b0803020605d171814801800139040310b41340000c2180c10034485000d840d409030001070603c1030000b00b5034082500025031003007410040354001440e544224065010f0700818030243d1000d07044c02c00e141142c14020400501c41e0394003c0003044400c403001c2005a0f907000c6e10095581003036140c400306010031032940000851b4083d070b800300ca2800c0115800310b4181018aa42580c0304040802400700420b12405000d421401486003070200b0414013260458510030010000d200b0502040300c1c14123403103160813510f03640000804035140c200305490044e2840c041150120341112071840041062184410664140c802030380d14031301c40e6941d985190b8015800030340104244112148001001560344815042544e28001016191454000041d10381b103c014502e091300e400646080c040280d10505036051410484000c2c1410748940c05c0032030080c400d070740001e904242403003001f241400160304004c0483d41010200030018200945854501030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 55759149 1250 55757899 55757939
    0x2041802070201050f0703052203060e06010806061002071a090111030304150f1b030c030606171303110303130b0703090b01090209060409291c0308070507020303071b 73
    0x140c18490b80040d1705404003d442600d21030f0504138940807100b124074104d0b00c074140c22802450410ba00c11300c00c20240d030055540d400383c030600a15840d410310311015118070000b020603000c1c82c40c0c2c00c1a00061072003081528010000c2120001c0012645100070580d5130000960380e000c9110300c04811400c0c1d200004903840740e5041803204a0084050382c641014010100c0c40748c214980380c0c0d000e0042c1e1400351100840c40c401c0c5440015645450000250646040d40c1c000400c1c05500c100021541503880c01c6035074044003500c00820f2400c050b207400d403031194071042d07200316520011040001d1440e01c1c3e0100e43c2c0141c040d81001e0090382d56620f044056400c013803c014142209000108050107580e0082c000d90080280500e04050b16144027008951075544104c00c0110302d00d4100300d824442c01100c548586090782ea81d0b4051184802080034090103a4004003046003400000300920701c16000e9602c1035030f004050303a5480c04582404a4110b42d00200c1d0b46a41d0503c0030001501c0e0001081c15442ca1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 55760399 1250 55759149 55759157
    0x10503010312030525032403170f040807030308060112060602030702040b0f030a0602090901050603010617060102070b03010608090f030306150c070f08060709080d080f060d05010f02041802070201 86
    0x20000140c00c6014150151000700000a411085c0440c000c952418968031045544d000401d22180c821607030000009003c0400510705074501070003c284c00f055010400d1094107417075660780e030a40c01c008155105a520036510780c000d401000c02051f81c08003010340148800d0b07844070381c4182d030a03100c8000c86541d4451080581d0007002880c0c01820b01360000b0072140c20091200c2401c1c0a00ca02203801d140350302c0c4088809036400103030707a2114a00080c080f405001c05481840c00c40d07040800103411250702284003c1da0103902030004007035a00c204140030190001e8210309407a569030b2400680400000d80f41e01400b8020002440e80d00361001094070310500e001404030300c01d107403d0070713800003e58480040a14a805070703050220b80800c00d40d8150000b4610782e8000e1074030f032402090013081c03021640c212408035002140103110940c1c0c000c074465000161020000700d6511000300240100d034603500010515400e2241c0c0201c16074290b40070303008035980d400381c0c10011550444004100e200b02c00c2d009000c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 55761649 1250 55760399 55760423
    0x9030306090f0421031e09020d08030a09123c03021305030105010f0e01080601030f060c0c14010209011404030b010e0c13090504060606030213030b06180405010e0c0105030103 77
    0x1e000c218002d40240c002c0d1803441c20001c14030240704040a1600c03840c80443c0c6c4440d030b810031140a0450072000880780c00b908208070050b941c00202e14000040001d0303c0c0c06008000f0070b4480c0140c1c0d00c1a2400b41d802140c0c141000210580a4075000c02c4150ba001e03118410300c05081200074045211210009c00c02141e009001010003c0d40250001901c0814003030288e00c0101d41e03a1400d100e124080c00350328050700d410274a0200908011030050300b003048036420640040001031500090380c0c04a59200d100031602c0c015082d81215201c0c13114001401501a54864244400044d401042a19000e0380c840048480c0d10f24500e440e8811444010b05555000700100314440d41c001c0c803a43c205048240c200d10703003c9840c0e44113500045503046510000c0d81c440c140810801d6511660700280300302e04042d030038600b141c0c0421000001e58480500380c485184002200e65a43c40310a009805520000309042c0c00c0c5030401030300a00054040010038030660058859541c000d030180c07070490f9446201c1e2000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 55762899 1250 55761649 55761661
    0x3070206010b0a05040503010e0601090c02120a0302070f0602070b090609010c050d0e0a020303042d030503090d06150801020c0d0203070b071404090c05030601080105040216110d020a0f09050903030609 88
    0xb568403c814103402c0040610012030725603000c0c001c4080b0382c610280100043d504000e0400c00b200d0b8110300c81410341d0702a001c904545051071081d103000102504005840e03071014141a808211701c298000c040c14030009200b400c1000d00f035000e82c010141c00b030440d4607690314401420b00300e846091080000c1201404010b800740b800c0e402503030600e110b000940e5071998132a400320b4550b401a4100d8545c01102406103903001580c00c0e0703038084220011000d000e45500d180c69003600c03071043d9880580103644460403001070003019084180107450130b65000030f005580c2c05005000b50030901810180b401100200700b0704920002c16205403d411445801d03c94036074880c00e0b140211084c4241c200e40205001c0054000d81a21405800c40e8054403500da4034501078000400c0560705800a6201d9131041c42682c0022400c441c41810b9168058074480c103800d001c40009a50300395402d802540000c4205000c140040042c01c14800c1306c01543d01400591100300c4255145d0104982e22500320440e8400111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 55764149 1250 55762899 55762919
    0xd060f0f0306050c0d05040b0a0c1b0212120d0c02011a01091503090b040b010503060603120d020a0306330509091518010609050a09060f060c150515040608030307020601 74
    0x140140070035841303910b000046003c000540c2d07004c580541c1c1d500344070403c1018020082c041c4e01d04a880030302d0b0440d1880f010b0041485e20b0404141c01131b0145584a0024000c1d140c100514074002004601c400d032245041c80c80704016103090b250102c015400c102403d402e041e982004030703908410584401c1c900c0d605003c050080c1c4204050700600b016143c00088010940c2c1c02d032400e02441c0640300d000059030410703042c10f05c0d028001d0050340c0250701c5907205040b500c02601c1524030441c614800940c0e00c00d0769400850140c00350b50070180c220366400340e04000074102c261852105048408442d6920b4941d0710707090315240101d49141342c22000c61800a02110038070700460000030702c02020f1945100e040c1c43c2c00407030250260024404103450020600403031802c40210b90003001e000310184903441c14008071807081c03044c51040001b849900c3e18280308101c0c1003205d075001e03081801c10811030740c40c1c44e652002c004520085078a000c2c0340f070090003142c1000e000c002c5920502554000308050b07460100148 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 55765399 1250 55764149 55764151
    0x3030f060105071e03030b090601020303160e040b0604090c02070501080705120c040e0a0609050c0c15060f03060403120b0d051b0f03030c07170c0a031b090f020d060f0f030605 77
    0xe500c01381111251044411508503030032180c1c0682e070006262403a050074040040005050181076620600401040400401c6c14068000702c518000b0622001d440208010388014030910740c2c40a400324009c0f81c25405130b88403100e4600c0075800c6907041c2d5a03980040d103402c2ea05440d40d90004004020401c41d00c1c281505460b00a2002c1c0c10051416903030715003010680e8425250005000c1c0c0b0303000304003c0c50b00b160040d117400c0810f144c40e840c600f01c0c0b020107140d80c03040c0c981c01d00b41042200800040565035000d06034041180094161481c614062500420161144080c0d07001ca5240c2400756106051088000380c15a40c080020500c4041d40c4503411095a095162140c1c070059109000e00c2e69101440a0180c0c107504400502840c1c2c20840c64000804003065000203603440703909003c00035910b20400c1402c50380c21004034004e00c003046401c1003050007e034020804030307400c0c0130540f2910781566000302680712501104020654071807141c1600090284513a503441030441c0340a00215656034442 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 55766649 1250 55765399 55765403
    0x604031b05090403020d0f03020906091908010212010602010c260a0603020301110901080105060f0306010503130605040f031205070801090b0f13021b01020702011d01020316080901090803030f06010507 88
    0x34400540e03104009000100e04440490068000b408500d0b901340c0c00c09200e4008400b0340c00e0540c03e003800c400200c0c0c158040c2400c00b5209049169000001c044420543d034003a0503490f00955982860001004400c0d40c00c1c4560001980380c8003d0030400c03882072102000066088a2001400c1912100142c645070040c2c94400042c0e5138141c0040140d800f44030340c40042c00d0303886000b922000341038005400400e0592042d40592002c0160380703010000907084980c409800d0074a17980301d807503e0400060f8803034100350082c1902e01d01024007090221024190800070700c01e07a5104400d01ca603a001005564040d5501008a004907005100480e03264000051610000c2d01e040d0560404600280715805030003d51076459600242002004030130065050089031110b00039890044950700080c038101c626140326102d50700f041480340450f84240100c1301030300c10a40400c3c910040b94144075180354480350406000c00d024860004244002100740e0348a0b500303800400d82c081d03030b03010015500395021b0902 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 55767899 1250 55766649 55766693
    0x8030a0b0d20061603050a1b0f02040f09030903021e040218010207051c08030a02040b0315100f0c1e05030310140402070f020d020a08030d05061e060403 67
    0x40c0565100c079040508014014100340001d1012214141d0406000c440741c02c0c000e1200f0003070180c002188042114451350f0600d4100d5403420800f03c01c03144074503505003901c5401e0b182181203046c0b049103115141040c0c001c1b1001c00c85800303511403031011154441c000070080307131a0200c10005458504420f4100c2d0b0121a4440c0d044449000040d080b6070000c0c1030038441c0d84a82d6070310079195a042100d00040d00c0b05591103100500d0490509640801c940f00060a07090000002a0680d2058040e0350060011750052038590600000c610401c0c0070040c222030007205070302ca444610078411060151002d0140c1c403000c0307540031140c0310827095010048040e03001882c030800303080c0045d204000840c4210a40c0d00c1c03c4078441d041440c481c003540c01d82e450052081e0b00520440d00407030303500c070803012400754100c130f10fa21400700f5440400c21408155102d403c550101190600800c000c64015134030a12044806000e01d00036030750314961500c06141e88a4022209100501c00140c400030f21080d04003203120 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 55769149 1250 55767899 55767911
    0x5060906040519022a0703020619030213080a0302010b012606040b060c061602010219050a020109020316090b060a0c020d080405030111071b08061504020c030f04030c1406030408030a 80
    0x141e41e6090ba0f1180d40f40704006041002c541881c410f051240c00505c000c00c8000e4150180355400040082c025150b20792035160039000007103480da0107070b4102c0f101c1d1036031404102c0110f684c03104440d4031040d00300d03002e5002d542400701030481e0351b00c03070050402c0042d060003605440d00c02001504079200001466a500030b9544c20440446035100700117409074401c0304000700402e02d001640041c1e0b1f000e404004c54156801440740098031048010401c0c0c2c0145a13140090322145034140072809458110800f03034040c007812001200700342281d003c1ca000d5445201080c8031b0485408180545403051050220004001e102204014609200c242c101c2c1030142c0c0c425810036448400180c00c54001c090750300f500c4c03a00010140100f05022424100c070517a41d0350442c00480ca4480103136228100102440c604640a00000005030b6071507060318074040000040725142c0c0b4810244105d950700034041030320790341014400003e03402c801081c41007040300302801d260308640311175442c0a840e030006402d81007e13030b803036079 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 55770399 1250 55769149 55769191
    0x190504030b010b0309070602010b0f0904030216032a0e060906060408030406020102190c0203070e0a0e060108070306060e0103050307030e12010207060504020103060518010312030e0319080a050609060405 89
    0x70141406490103000c010b5590404031220391a100080d0f20581c15641403004d192011f030b44070003030245035603001e4451119554a52400328205043c14100225660a11394040248195220002180320100a410030750f0000840c1d1303c41650102c1c4038440c440118100041c3d46420075000342074111602070180c50409031100701543c1560455040640143e44c0070a40503404040001084003410940c00c00c0040c2c0700e01a00440e0711021700380200004109440c0115058201d40c0c2d1150040d06400740c10355449585800000742c89024910056510170300303010001c180d94903507100e81c0d812694071030021854403040342d609540c0ca040c01d0b84019070004a0084c0c8424040c428001031100c18812000000c2074500f0344000b404403a241c0e00540d0003480521141c1e2020b6840c00401d5054940181503201c0d0003030710903000c8020f080c0f40c0300040d6140c000807418540d41c03200210f40320380440f119204e00c600d6645401e100300c00c41e0003c031010f80e40180701030b0100320181019442150040c00304e8102d40200e210780 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 55771649 1250 55770399 55770413
    0x3010518071703160803040312180212030c010906060e06040c20070302040603110928020304021c03020a0309090c0917100204060903020901090c080705030a060e04080403210519050403 81
    0xc400117841105000040008156004080340b401540c102410820501401c42e00b01c1c58030700f00c14000340640c0103e02c240c0c40e0040204183c1e400c0a032108002d0000d10401e1905001515491040d200d41c0301844011402601c0d15008450707a06846584908189070104c501d09491080c510740c3c07404134011282c010025032581c3c01094040c50041c0c100c03541d8130440409011035000000c2149007030009030281c00e0184d0b000240004070001c2c40d503002503101e440303600009240c140c2d5019040c003220908181001050340108044080501a03250310603455503881048060702e0103840744000044110f141400441c0801801344441c141c441d00712801701c2038401c5180704a074000e4000700c02041c4840810411464140c903100d014080040e01408083e64210010308480c9001d014002800008000208010030a41c010070052410628615450400b07080c0000260306c207000076500f0725a5041028400303025080103446076003a035503c41d8030b01580c03900c4c400203800d08505a24100310b03082000001161003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 55772899 1250 55771649 55771687
    0x10e1c060507110606040c09051009090c030b1302031b030702100c090512010204050a0b210103030807110c0307060311090409120201060501080705180f040f0b03010518071703 77
    0x151946091144540140d13813030031300001c00706072050342007484c4940c00f6544810303041d00300d80080d01d2200c605640200c054070038902c0342c1c1008014a01c0c01e03100e505079a0345a000004007040a440c05408030307d0141e003c00a034401122126a409010015407013141c895200079030344940c0c10707c151010f4801c031040b0301c2c1c195216801c0010004034016400d000034549851580100c0100344001c525003881c003404101442c0d003610910712002d20100e440f4000c001076004081c607020003260828040d60b102d2801074440c10b001d4910900007080400341ba0700c0d18500040614003c00014000c161781d5140140817030140c00160070700c0350002030a0106000365141d80c001d031040d5910420b088400d400003c0e0000b42120290781c40581004000303403d01a10503000790485105054145000e40464007000c00b142c022004884c1007070308a45070840c24190b004169010044800e4120000e1006072105845605800c80c6507030b1084041d00039450411801184080e00758001c288003041e44e0500b1111011440c1901e1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 55774149 1250 55772899 55772911
    0x20d020301050f06030706050a120203040203030c06011d0c0301030503070b04060b1002030712030203240613060e0a0503010626070f06050307020f0118020607032a03090503010506010e1c0605 84
    0x703408010f101e031505e818041c0030041d01c22407408a0401b0703c68503005042880b40003611032407a9000000c0360079520144211000c901c8804201d0ba001d5a68542c510a81d01a84201e2a001081d03000420001055501140e0407a600007000b94184800c6440d0301c0c81c00c02c80a4800c0710302c55510244140ca03a21115010882004d203031b0090342d110040c50521f01c0001e14150900c0c401c0610400c10403080811003007814030040640540d400c000a040d4012500901c00c445142c40880d44890002409607845440da02010300e059440c00c1a4984d610103041c00c0c0e0366540140703a00c40c0041c815248290a8040002c500c0300b40701d40484000782e0780c4002c0b25034410042d07044000041c400008001c0010b030101710002c21f03c45481c0003007010601d8480506112040d50000070b1140000058600c207040c0704480a81d15040d40011040b007904030182e0313910345892000000ca0125000e10310019aa1406100e0b980c46a18180c46613145610004100078180c44003a4110400c44903940110f00802d84901c941c40c4100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 55775399 1250 55774149 55774171
    0x60605070230030a02060606030601090608040611040b0405031507080109020c070f06030e0609070605042303010e0d032d020717030903030f090319081305030d09021c05030405010c020d02030105 85
    0x313444000003801c0190003080180102030410a10546990181070706c0300b201d01c0c1d03203050721064656103480c03005414490310688040d0800300c1d000c144025440010402c41b071084040f113100c0c0c01c0a14a05000d40022185003010520250040105d2581c40d002000300e4021001a920307642e07100c0410100494040e001180020b0303407444141c42c0d0413020096160840d94500c002e041c09450148010940e00c0343e4010200080046613600d08a0181000703a40b24000d0014020b000b1b8500079441580d580642008950000b41407000d000f4000c01c0c1e041550711b0300ca21200c5034030703a002c2500c1c0b4480301950006008650100301e400c50b00e807032840f01e00059030040301a400a1a0f403401d00003903048101e02c006d04105011b030002c01144030282007c01c400b5141e8a0f581c105900b0507501c02a52540118020b000940b26000000b18403000810b69440ba6010b20700c03c69918000c1401a00b03004d001025881000785954001c0001340f19542c000c03428800840c3c80103001e088500010790202e401e440c0d050301d03050546 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 55776649 1250 55775399 55775407
    0x30602030a0b03060c0403060b01030e0f0d030f0c2f060c180a0b03070f0905030a0311160b07060f060b0d050403020c04020a02030a080613060e07080106020106060507023003 76
    0xe810707a01030201e000a040f4000c0c080c41c201400403060754852880f0003004240d490010700051303402074224800311401d0800b954102211300303a0760342e118601c0c0c1c402500000e01e0400480d0101d0702901c1242c1c00303001c20366500d195200103108045040354241e040200004181d89140d007803072900b04040c5206050340c641540e2902c1400c0c4a04840e50020701c0050b2140a040000340402004001920fa210419140c242400001c4020594005c40c0e150061034050044610000516401100014640e480700c4102e0b4115100070603002d0103051140035a66041c2c070104159800b04015070040b01003402e4801c00002c002c1c0e55001c01d002254002c0f143d0b00821500c400402041c19010702000441000507501940750061406009459201b10920302d000e2090000100f2410f450f0a40301c0801c065401070100800340d00c0b05000e030002c0c0d1044414000060900c400411801e00c103000300c9049510a4542505100b400e50070808035140049012070001e0300690000d540541040d12854001b600b20069695 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 55777899 1250 55776649 55776661
    0x304080706110c030703020d020904021807021501050405090307021e0d030e120115051009080a0f0c0f050a090b040b03120d0b0904020f0409051002030103120801080105160806010c0203010603060203 87
    0x2403481c842e83e218401c3d00110810070260b200d200c4003100b01360b412102c4011907602c520008580c0c4510111030801c0b126900c0802114580005130404607140a00e10b6052680e600d50812003a40c0c422181e14129400900580e001070603d2500254a20132100300484a07500b0000443c1c3e0250071280c05a0000b614940c09610314202040380c203c808003805c009122071613190300301303081104c0c45106007800341d00560031807400b0314404d0100740d0103043c0c2d038025100d01000340d0030021086070030070ba13064404003690580040e220701c520740243c080702e0018040b400d081d4039100f4403c000340704040d1610780141c0c03113080600d501ea4041c041113400350b011b1102140ca400904407542e048030f4803050035902411009091101507074070404002001141200d000c2985401843e00d00e0900b244041d4285081d40044004400c0092110341e011103000945c0d10b4080580e0707603485035800d0b00d10595020a441c031007900c45c04e52061040c814a98001c0041c10103940b000c00d0750f03000c2400c40f0920390094840650100c28851 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 55779149 1250 55777899 55777903
    0x2030f01050c0324100e010203090910030209010b0301150f0311130602010501080c0616080405060f0301030204051b091002190b06030d02010e1038101e11030408070611 74
    0x2450444803e4000100182c4002080f14a10101440c00c28440d5803011406c0681c4204122450000017400400365800c1000b41f20180b8942e0f4002244103543e9200040743d81007406c2c007641e0485007d040c0c082a10180100d0944103261403210090400d612400066540300c220300050098144c1c54620a010f240b1304000242100c0c03046e08104c01d02c0c0c101d1084480643c0e82d103016900819240940100c24842078640401c0a1086911550b003002d004950001d0000d10035001e54120f9000342c81c280055620104642c12400c0b90124070b11101d8001c1c4103c04603400e0005083e15441561f00480c0c286460350300d802900440320350f00840d80400320b10700b0080e450809010005101c1c2c600e000030701810b413000040d81d46480b141014001d403207594003080c0116021056035810201240e41880064606101c0786a000486540c2d030305001740c9a0f0750782c03206400e00c50b041a04403810a145448003103015003104454951180c40c101c11548002d00c0003080c0300d5402d01c1543c000300304e03a845289481601f030818034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 55780399 1250 55779149 55779181
    0x31505070306060509011206050306090a1101020a0c03060b01020c060c0106060921030f0c0f030302040801051302030c010e01030207060509071d0702060f060105130f05010e0f1c02030f01050c03 85
    0x101070070b041d010840a60000240d58001400742011841500701d4807034840180115808076a05109010510214800c0400c41004071805038078400030743c5240b04010380c0c0c2e44901810041149102c40d1041001c104540d000315040401403040c1d4240e11b105000250701d940100e08000400d95580301c0400c0301540017a01003004100b070100140039006031540c8868810014040541482810045140c91070712920607940d480b948207450510603180390030f00500a42150042d90000c0d8a041c02141c1c100303540900511201c1e82c010b00819901c00050700442d410300d9400150782c1450b400388000c1c1c0024095006041c480d05070300008003200c51401c5070504032403060949410b080c100500a00c0749066001c51150780c0181995911405a154a40101d0741c0f0301c00c80d0718a4280c505181804210440316003200c0c41221026651100002d007034100b0813401101103504158040542e4821400104408594199190009055a03040340300c00680509403201142c26080c064000400c006151450443c42 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 55781649 1250 55780399 55780411
    0x708010e0a030806010c0b0109092a09020a0311041701060b1801030c2001051f120f02041506080405060705040e0f0402040e07080604020301060509091203090c040204031505 76
    0x921268a03500304058491180040c06400c2241510000b92140d008002c08941d0913801101440ca03036030340700c0c0440010401610225441d07060030382d00c0400c2c0c88903c41907000da05d09803000700740c18900d0f16410100a40c803c0800307100381034503004150320f04142d9001410042402e02034030039a25440720200c900315100d40e0007801c103003038061101400741c2448181c0014580e5007801d00052811136420140c488020045407003148a016203120142c840381034000e036004401854100164191101d00c0e02c60060890281e000040381000da44004114100e4600c12407600180000900481c455980000c83c0c0f40c2d81c203c81d002c45d070340c1820710041100c108030f255441041450100d0400d810140b500d0344010307028084006000c00c24000c5010340d0340311780c05100d4912880c41200c3c501c0e507a9801d407640340c80c000c0724240d00c65441d0420001c0c40f82050700c50684903416081c0a8822800181c0ca01504c03070300044e14030021403143c080301180a44451000304041c40c09110680d83d901003141c0d0141c02d17580000c000c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 55782899 1250 55781649 55781651
    0x709082517010905010513150902150a050a090b0307050a140906120103030810030c140310020c0c032103010611010b040603081c090c09020a0e030601030b0105011404050102190807150e070801 84
    0x5030301140d0900303006231440304103030380c085450300340c5000140e804050311600802c1d4020014040503900d0f0850000c100ba0511768842110f615503420030601c0d2400101c0f442e0010482c10441c0d00000c82c41404420110000d8a10060402c1108e43c0458650380201401020202c030020060044c550400103255012102a503a600d001d411507440203100217491003407080304408200000e0407943e0603c241c805551140104640300c00c580110250b0b80c600482c0074034080e01480100a1a01501442400c003542021b07101d54590303481c00d54200c0d82c03130600300c0c4029955561070b0084580d550b198010140214090200d00b5107c0304100309110441050412101e070161400743c1842c001340102d91401c084800c111350068a60b002e0420507501d0341c468024081d414091440040204059030703103194165042070341c1d880900c6031700c644510301502c9203025140c0940d025511a8801c0361442c40202c009038442e0315914288034103640c46074810315480c0c0d29a49415110303059000c00340c400b044124014088440 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 55784149 1250 55782899 55782931
    0xa0f03090b07030f080903070b10150203090d0b040c0305030c030306040f020c062d0906010602010506030d170604020712020d0201150f03020409080c1b01030507090825170109050105 80
    0xd070241459100000004c00d10000320b00180c0f21513018030507508080c0e04049150580c0c900000e04c021300006c14010840c030400814106444d0510000c140d0b41540e8000d0880c0020003410340716000c14500050080f03c00518200d03003c000a1802e00142100c002680002e6441c6c2c1800001c02c026503c0c6240814212881404011b0095800151081d0050304502c88030310280002c3e0544165200302c6000020015244810b1000d4800001606812114940d00801094403800c08154407541048001c00024081608159941d0740002040b604418028001403401e07060b50741c0c0d06400c22180d020301015800c69818600d400b6020301444d403850501030701c5000305600b03280340d0000d074160034000640a1907854403150100305080b822034907402400811191f101d02002c000011201d0704200c510700090502c004942c190b4010607a00d400d46280da00076100b00c0c400380d07403014080c0102d00d08110000003c90000a00c0c00030f940c4100f044880d03220700200314038178641401c900755007001c0c01c3e410810700c03a51 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 55785399 1250 55784149 55784153
    0x1211190207260a033e070b040b0d020f07230d020708030f0c03210103060b090c04061209060509210313021201060503011e1a01020606040f06080a0f03090b07 69
    0x4991951070950604050300e507080c1402c1d89495002010701201c0c040c0e6000521700c0703003c1c82c286a03201ca01000d017004496025885407040d656034099446271441000050080c9800304061b6000b030514901101640c6040c49070300c2e103e001407108007102503801030502500b000720b0340c001804000300e407595500060400384d192408103507881c412081d134a40309031000b145a041034403050044409042c66054111051040e56048035081c03103080c44105c0b01c4a01d461200042c9080040c4011b204407a18840d2a051525140043e039913502d2803a2048071156481005000180c0b40303104290141001b040280810103000d21443c04d200740c208403000c00c0301e9051040088002c4000109a40c459056803031207800341c03903000080e026081c00e400c820340c19401c000118801c25100b010b641254a0041420b10001031407001c401140c6003640405401030300f0480015503241042d4001d2304011641e01e10005006540701c4d04c0b0350500040035811100c007aa035040ba18149540700d40d03440040c0010f0240350785001515 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 55786649 1250 55785399 55785403
    0x9010305062b030c02061201050a060c0f02013c030e0c0307060e060d05070f0f17040b061309050105060f030d0804020d150e01090203011506121119020726 68
    0x340010749036024981d80721402c0521131614009456405807503a900c510820039184584070090003054003c0c0c10641000862030310075041041c000c0d80003401110a14019001100c0c090394107469011540b569401d046e0380e654580802d054441c4441002c103a810509440050660b03007070180110450b400200401341503600408d0350340c219040b90501800020b0004d000c00c209000340e4031500c81d507924020801000c40e801108603103e110346562a4002d030380144005039884c00810b0884015401d0307810003d80024140b0500b150404001814414404c960000e441c003a42d503840d80464880c0d45400600100d400c1c05001040014001c4010b0400c0d8001c01800421000000704060b00c01d400507104041400301c3c00458a4a20070120b00900460381e9a091441c00792407510001ca01942c6000d080c03401000c8400e1400d0103680c003595400000b01111264074010f002c2c00d91100c640c110040142074285990300020300800c41c3c058019250306841d10228540d110b02c8180c440c2c400c40f25940c4042c03118800 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 55787899 1250 55786649 55786699
    0x314040b1f050d030e0a0609210f0b090d090902040305210c01150e060301200a03020d091227050d0c0801060608010f0807030317042d05190c031221020901030506 71
    0x503080c0c003c09c0340685401d001d0143c00c2921070143c5100c0f0300384203001d802440414005203440b41350702c42141940e078840f0518101e101d01c0c07001811a8100345858031180e801c2003001e5828800c1c80740181d040ca1402d0005600710340c9101034489c85421140740411011010505903980b002085008000380c5c04074208451503c403601600700c010a800181103036a16000344c1c152038001d446008108408102d0740340400145103200c00500108062140789620303131009500d10940f100c40e482542e51018581006d03c407030280261400c413070502c040c0a020407808401d1003030400400c8543d4480c3c000d5450812000885905500491441d80205030244040f0790403850b00e00704804044400089075031981405042510089030311110a000c007090b903402c00c5144600d207158540920150b5000000455011280211030040181903000c040001c1010a54200610403540c82e241010300710b00440920170920f020b51401d582d60f000d0741c04070711907503596450f01c1929482081914603040c0120000724070505050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 55789149 1250 55787899 55787939
    0x403050601060c14160612050603190204020409020c060402100201020a05040b0c192003010608070501141201031a07081902030a091a070314040b1f050d030e0a0609 72
    0x700150a210811025408007284258003c0035581071752000e400201c08000c00b4407480c000150304054032440301569200303860080740020000c040001e50b010300300e140381321042c0060364455402d1200250103075150005100140f580d001502c2c0354038092042100c0c0f24031302c3c5640411684140444000640c00600700e5042e10308880a2603128200180300300d103040c4041e04461410140e080c090810042c102800714048140f046040100c08480c0301414200d50003440b8101031a0b024941c02c00144d4002e40c0180d928003074886c6903520f8401003c1c022140c200d0281d00c2281d9416a100b880f480c022043e810981d0445018038102d034903410319862806180002ca000541e20716800404a040410b01d0741c00401d4056100300c004105036100d049080c0e00d400c0840d03001c804a4149242084c0300b1181000b43c510440c2d03c1500c10b400340d154010340841c0c2d22440040c01c0060761006002061565594456807860341c400e90394400c1d06110307142403041e5801c05610540c10b0100303072801402440348080c0181d815003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 55790399 1250 55789149 55789157
    0x8011703090603060604090f1d030a050f090a030b040b060307061b120912080309070f15051e030a0f14070c060f0f0e03130e04020a03020913020604090b0411040305060106 75
    0x140740c00d0700090440c80703035500c009455464100140f40c2c2029a800007010400789802e0390314405411284c20b9162f11420808000040040142c00003c03c1ca09014066410700a0903025036030340c07641c0c1d03003006000042d1400d503044032849041140384d2030708011030702c0944940e1500388988507041504100307400007094010120202583c4058203148600d5480004201d1082941c0500d4954104244030307903c180d50301c44040c0114040403a0b03804044800702c00b101c1100341100404c030140b030400c5030703641c1001345188440c0d451614456001e00c0144007450264580d1940000c3d00340964881c142107950100102514030720840401001d1908450b000d480c09811081c040350000d01200420000d02c0364042c96041c041c60403e001054800020103840c400c01c2607040000802d0b11101817003500c4804030f4001394003040001d810f0005092070310700345030450f03180c0e60101130000044c1d00050098110707400105400742c0d6000014114501802841b0b42d0300b00c4400311364a00740c255241e81e42c035103405010b20f078248 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 55791649 1250 55790399 55790401
    0x2070b130201020a05030f0c1606020312150d12020c0102070303140706110415021527150405010b1908070603150801020c010917120103060b06070807050109020108011703090603 78
    0x5a4002c1c00380350080c560010590b0391fa42007215a401d155048a00c8003096441113502c04003007020240e4504050310381e070380c00a504254031141c0d04100030300000c10510380801c03d1a81c088490710b40001c3c19440da44030310b40f421540c20415000924010002111904540c0f0411042001c00d400c44a19240862030704400380d510340440c10443e008c1d204205005030203100019000030306074899403500180101c960b09039900001018100e124a20f0190340c41464080c2c1a0000888020000420701c3c5ca40c099000380c51044120840201c441c0388221019100c0f40d440e000c0e204070b0fa160622003041010300720782ea25440641040c2449079500c0c800e0080fa020b042c1d8a00316106d501078809991030013051514021f543d500d01d00c3c9400c42c044c061098040b640118180811030242c261070041d660102e50889140419038070750f07110b42c8060301144181d03603003100c400c03c034507004950300000a00f001405440040341c43c0c8090b2000400508050744002980e0030050075000710b03540080200c8000340d03405c403405500d0b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 55792899 1250 55791649 55791653
    0x11a060a0c020a0b0a0201140912090a050d0308060f01020109150b040b100c17090d060b01030f1107110d030519093201110706050d0f020319050a02070b13 68
    0x62641e055001039403041101d080043c000300c15500900d041800b82c2d0080c03100a590881b40d190b0340c902950300c0034850304543d0748407030040c0c0c0c4040644240300c40140030000c29a0381d040810880d03044158180d0020782c000c0104026810b200c00218130b5583c00784001c10051059848100c7c042200e900d00b41c0e451900c0d6141508180d4540e004511140001010340e1624195280081c0078007c03044811501d1455540050034100b044105980c1900c0014200d1103041585a03101001425180d0001341455501d40500b4054030041c070503481004a440c081e9580c0b4281d03401c0c4000007150300d4125521500c0362400c0703980000c0d03003e0160b803642c0d1054406040d0290001c10309a6a00059412240c0b01d00c40b46091400304c900d04440090071103025842d031100e0110010011114400c060052007601e82c041342040014621500c002d00410780c041e000003a00e0764600d02c2d40310590b8000d50311aa080244d07424140c030350002074800c00350080d214400071868000d0980e161070030000010000d11066941d1004001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 55794149 1250 55792899 55792907
    0x310050a0609180507090b06070605040302010e0102030705040509010f050123040e04030c02010e030a030f0f0e0409110a06080114010f1815020d02060f0f040f062309011a060a 77
    0x1601c02c001e4203002c030b491401000c0b2110030102d0f400761030603c203000000840b1480c80c403403074001ea003014203240e00d446032a4481c40064900078100f20110340d030310509080c1040c1e00388041c44c0545a03035901c0550f0707240340c541000014041a0800c101c0040482000c220303d80c2c00c203900004000c84600b0742d082001e20f50703074030341460300442d0305c8100c404101d0307800c101c00c056201101483c3e4034400d0720f0b551030700c8900d80141903440d0300070704004022601ea035100e1100c1c85c0c050544111110014503280c5000032104000c501602c0f03450100b2034104000711041604c0b840c0036111100601014a0008180d41c5007201d000001018051018144005480301010070791050300454010b900345140317144860303900d041040f00841c2c2d0000740d60046c09035040d14400b10713101113486806502a0f824400a68846400d46120360002410448203a0640e0719410300207102d50049004a203d006221502c2500302d505200401c00d008004070b81c140d14040742c241500350201000c042810080d258a40c455100b404266 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 55795399 1250 55794149 55794161
    0xc020a080703030501150f0c02060c0106030203070902130605070c0e040f081602040b0d0804090e0309030609060a0b010302091012020d140a1104050a0b070c0b030108030307020c010207050310050a 86
    0x1811420300018904103140e0075420150407200d4425800400d40f2000c039088480300a80c50a00001445980e5081d0161500c080038204a211031000007412907920350000c0e1502109500c001d90a640200d03040381030840300c0fa00b18004000e1400c21520301595503032038602450403402a12803801122010909020791903807101c42c280d07072003611907035030b00365009003202c0603400b0410491241d4281400e0480ae030078001009500d0790750190044c0d050a00740444a000340111260125252209011414565400300303c0c480c01080040c0180940d82822402c07130301a110401c100505041c0100144040c41d2613644a01204580340d18000c1000344202035804060b1040240f00301c0b070681010708a1240511081415005411022040025641c03c0c808d010f1140610311400345c0c000d0b00741e4420880140113070024075030b4511505540e110580c4034009894540c00c20b8100000d04c0d40b020041111094040194040c1c240b02400203000c00c81c904000030386d03200c94041000c400c01c0e850380086444510309820034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 55796649 1250 55795399 55795403
    0x80a0509120307060501051504030b181608010e03031306020c10060b0d24051309060501090615020114060f03070806090105071b020a03122c190506040302040c020a 72
    0x114507001a5410010ba49400011040c0c90141c540700001485160844403010309058040382181081e00d140c0300c440d4000c1c00106541d241c055611200703096400140300c0e4001c0c40410040e80d102e01b50818050b2400c60340b4030f00304d80310280d00400601807051040b170f0003c01d030140c3c41280035070784542e29070003036041004492224045a003440b00c04541081a6405441ca540001a0801406405400c400750506907001c035480c075030f041e145d014056420100c035942c503003131001c043c085060040d0741e480400319a000d0b80558840d07603907170406100c4000440011406080d4910080c000c1d02a80c06080c0c1801d000544081d11800101e00c9246841d10148291030007000014203640c56071030000c1c0440d020f4039007211030324009203603070b0602c100b09440ca0442c41d2800350041c010f005502d007150341706064540e0602824007408604c2010b0700c1e040400785580d1441e59802c03000604040a100c00340840411248443c034100c0d40e01d0310052016440c0c0700259001c50303404030340104070300c5e0340d01d40d090f41003591241c80 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 55797899 1250 55796649 55796659
    0xb03060c0418111204080f070507050103060506130e0912030c09041b0203030a0f02040e070c0308090118120c0c0905070f0806030a030804150c0e09011d04080a0509 72
    0x41065000c00c80015208880c00500c0c45540c0e071040440c000201c60050359001c4100d03d0600105919040311181c640d071142c800c40c503452609155981100079504000d9040300e181e80025000c1c442e13035a060003042c0040600303440c80c07424848500f07030124000c41180604115400d090000521540e000c005040480801180c416a40d040041c00c0b0091540600360582c001d6007080030748140c4028108001d8203954056000d5415501c43c800e00740080d0004607003004265800f480045000b00e1500c10180c003a96187d110440d03440450718024102a000600462a036403401151307a0341c0410580501e100c01d91b102c0c5102040c0700387c12405032164540780c2d1f0041c3c006241c0000100c2d65031510f51086014a142d5107030300a20b8030000070221403d80701151165056048101c5002c0003a01400ea02600a407003020103403032491142004030102c803846a408000107880c178042d6011414260a120b0150890843c5096804a003900782d078400c0b0300c003800040c030043d40040c035000103134890f03800c1d110301c8100141 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 55799149 1250 55797899 55797901
    0x11040e1c080103021e03060703180c0b030906010f0812070203011404050f0c040507090b071a090321010501140318060c040501020f0708060a11040806130b090102041202040f0b0306 79
    0x1005102041c02d020890042030281048080ca00200c10307281c2014900a0041450360b8410038200c0181008002c25a200006540800d00007032542041d1405001c0515044d6120314009244500e4800e0603407014100d22040401400341c444041104550a03480200c00d41d550703d458808603004000c08805108880034410a12007088404a0b0100000c00b0a41c100c0d8404400c0c84100411a6010340d20380020400108040010440075006806600e0203880401100a40d480314026450300c115405200b0b500006a403a100d00d500c4889111066009400f01f4001d604060020788041d1402e8520380301d0110101c0018494441415540036401240d42911a41d040c2581000602c2e0003c0c09514098054100301400a030300010310a011580c881e401030000c1d0b1900342d0b8040081c0100d1000010000040202060040d02045001d006946910407201543c8940c100580041c0024101d00d10b184d00400c8100a540f500c45811075030160120b60001d040e48404018400030183c05403e19014001c0d18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 55800399 1250 55799149 55799203
    0x501051c09060c110303090c090606090a0305030d0e0c0904060b06070602070b070f02031201060818011803170f0f0c0d0e0f0709112a03070507150c11040e 68
    0x9080f100345404181c03207103402c140d072052605441c0e0004035800701c0d4685c4901e8682c0c46500d1b00031142030704124082c020301c0c0f0b0020b4040100340a11002d070002e40f03403588000380700680c468142c4904401840d00d0800703010030071001b40c005105803c002d44041c1c43c2e030fa00e8002d4030300f45070b4640b022210010b80c8200c00b156201d025180560000504550240120b203012400742005400841121038201c0e0000421440da03003484010380c0c284902401c2541140c800e908501c505440901c2002c0a003040141c0c0080440b1207843c0041642800c020751004042c082c40c00d0143d61000707800c1c07030f9410440540300300c421607a0b42041076016016004442c032109052040c450000940468541621002c08041d14181a1982001801c0d01c90090021000d480100036012081140c040540d4002c80c03c40640700a00344100c40151454114400c113803100d4200d0002000b188400c40008400f00072103042050540b48961030f208500d51808000038012034403200d82c50b0324a8400c1c800030354007503800600082085060 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 55801649 1250 55800399 55800401
    0xc010204050a0f06080114131109060c160503070b04060311160305030a050105090613110c0111040603050124030c0315060c050c090906060d050a080a08042003070501051c0906 77
    0x3c1d2182401281092002007404101d106012070388582c0a080c0900103e01141c0c0c0d60020a44407040e805a450140494071817a5602c000510908210200078041514441400c8002440b5640414884e40c0020300400c020540d54003520201c03031090500143d41080d0500e52080e03031203890709060001f01018000c1c8101500400514011183c980d41040160380f0740050106041d01a00d01c0c0c0e900020b041719012900e02150481c03260210205541814070643d00d10311420745120301c10070890b07100045000d000300b0364184030340350050845000b00c1f40c0c3ca101d002d8892031088110080c04c0105500c801d2400d60280c042e0b08a440e60040880c184560141c1d41d81300103001d100c54203811031f6580541d0859a506290a41499010301c8421000e0840c0e5201c1d20100429048003120884d0740c1c4c0110344600c40806c0c20313600a0b042c241e546440304215842c1030710305411544e00458a000103c50000d860700040d447c0010b0035000d882d401c0c00c0c61542c90080d9000420f0100400c540c014089080040c0c080c00c00a807 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 55802899 1250 55801649 55801679
    0x506010b04061e0212070206090303120613020a080411010c12030209030106061d09041401090f030e030a0b0f0705120405010e010c0528120c0903021005040b0d020c010204050a 77
    0x26036500c90001001ca8510107140400c3c0340c00c0c0000603031210549000c000482c1c8010014140300030301c05490040c02c440401d0039900404000c44c0c020000c40300b007145604108200b1544902807036000c602e4803600c0d0001820220000d0400350101001c00e00851561b4001d01c180205950410900f2268281d9510020080e610014041c0e01a5007002d6000480d14010201c000e2a04051003201c0251800c60342481102c8100030001e65071036140f1080d40941c2c65080c890a40c0450040c200e9034268407981c1405000140300c2c00b0070794042d07408040350001182050760b440f038108081d01c112030301c00c1e01c4010080700c0034018a0b40e58541114440140030401c1015484802d02c0c0050302c1c000e0001c0f5144e004203130340038000c0c1c00c035800c100130b8450801c0d20088044141c0000d40f201a05002c00d0742c40f41c4d2089081280c205043c000c0101d0707150401442035191a001c04003c1d1141c61419900d07040c20460290403a009111048011a07000305030250f09000030b4055401403e400390162124030b0f580c0c03a418081c40c2c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 55804149 1250 55802899 55802909
    0x50406090614040c0b04060e060304021801030506070e060a020a06050405011b020c0405010e0606030a0b240702041125050a0f0515070201020301060c0b06040605061303021e030703030810030506010b04 88
    0x1e111130002054800407007514211382c09502c9802039043c02005004c159800140200e070f12a0f4003404055a59006020701030196000c0c0e80100441d291000002c1c0c0740c0d05014a480307203d2082440034000703860740010b11a00c411740c44000800e00d0b0b11a0b151450150a503400c0700c140342020308c0c48211043e0340c000780e00380c030301a001c40d0148807030303641e8082280f0051416540150020810000a12000c517690816500c0e110041c0c901c11990100c202c0c3c04401102c281404d503c00940010f14000350b00c3d040c01481085400d01e80000c0c6000d00a505181c0404000513076002c2d52211a03807058144801417000da006030360005500c2e61905100e24000c0e85504154512207030301c0d10a4004521541d20510940341654842e496030740e0f179998039032544100d0b074030010003981d071180c1c842601042d141c4524003c1e141d0300d412100070180035070840c41045041d138188108081503180701c21044201d903900190306021a501420141050b0700c501c995807011007526000506075118082c0002200c50018000b0710441e2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 55805399 1250 55804149 55804163
    0x4020301060e04050a06050d021216090c030e0705060a0c020d0606080102030405060907050904060905010b13021801020a0c03080c0307080f040905060303090a090203150a0f030605070c0c0905040609061404 90
    0x545d80300c1c0d121080350050b000711034000c000509507600500349021072000e980c00030301c00c0724441506104021148002a0481c544540c0c942c14044182074050161782405201c100181c24001e0500b80800e8003406941d131070390200084038804109548415051000440e0003510500443e9214002c06010b0b600c00d5808031158440c0d02c00140c1811408144541500c90042242c03a20b5251503c822002e4505010162055581c80460b100c2030f5482d164501e4461348446005038840c44045440300030300c2c10720b2107254150b4210000e0180043c215048040c00e0740c1c0e0000159845000411501e49140101140144903040000f00c0c5c074800a4813102501c2125110901800155103040030f160301c81c0602180c1c0b5401c068039180c14030110700c86402641d400090b504a50074180d07d00c6000404000c900e6106108240f14a02c0074414400c81d4010154040c65908010360f0755a050341d190070001a09204a00d50303d075075180031408014403600400304043e00a5014010782180c8910466061401d40d002c82e05c00c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 55806649 1250 55805399 55805401
    0x9130b360303060922020609040e0a1a0a0c0806061b03030a0b030601050a03020102060a0b0316061205010608010b040e130204020d02090f040c0c0f0c030506040c06030608120a0309060b04020301060e0405 89
    0x801206603a017071500006140424070100c01d5401d2004640051040c07540c0315458452658040f1010000c3c001c0050050850204102c5501c0d2046529100030304440105c0c0e040c40c07549101d050b0064089508024103a4186a0318001ca0003401d0340403020342000521790100109214291042da08800c0760840c2c00c9040d40c0a41e66600304106461009101c0240542c005000240c55002c0c50303444000003200150070b6030101e1424020802c0b0790a00b9030407820120f52038645030800f604282c403684d409440981002016541420b0401a0902039031103520390400348000040e21141003c5038580256501a1056459400e07012041c0069000030b04528044c00c0b034482c01c10428507250003840300840498840040920031625104112144c0f070109072010480c04000000182003080703e039100b41e00800c100c9040a0804000405441c21a806503355074441c00440121032441d00440718224802c3c00c2c0061070441c140b034004060031120f0001903010b44040000100c0d15005925409134000c02c840070015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 55807899 1250 55806649 55806661
    0xa060c020c130209030f060a021201051e0d0305040b2719050d0501020702030d030203060102240f150a060809010b0405040b04030f2a0209130b3603030609 68
    0x15503030078050501e900c1101c54404400703098a80d8014860000041e06940d440801c440440780b03880300565010b9100e96001032450a58200d4034021800f52104945440b14044003010101c1d00081210a8911505c1c00c070240008160041080f94010556455040d80380c03600002c0304404001c00124105001402044a84103441c5ca0a55410183c000b840d600200500b8030003440300710160144225244c3d1340c200300c0740000d43d5082001d428100c20543d4056034030314141f0b00090030081070080076a001e500709052005600061401c580e4420001804841c00b03564051001718034883c0c01208a420450824011603625485101d1903c1500c5040c0207001c0c0089030820b02084600c2120080e000e409c0010204000911480507403404a84c0361070181c2291001041400000c41d0030f04000c0150b1002044038001c5013010300f03129601950b40d00003650110200d071210b001c1410014410f10000b400030002d00c00d50390300480980010b0140d182100400f010642d47d9582c0ea03401692103a104192081c00204 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 55809149 1250 55807899 55807903
    0x1e160f0f03200d030e010605040203010e06030d0804110d0606030b090d110a0c0b0c0321010e0c09060703080702030c10060509060307032001090b0d0c0305070f0f05070c0e01080a060c02 81
    0x7695003000d0014500d550f02d1403c02c40003442c0e4076000c6100c0c0e540341ca40000302c3e0394507400614080d00381e00305600842d003092000c16143c5034285a004081c0103c0108000101e2a030550b42040360900b1b5604d90100b182c9481c0600c014506600014422129a0140075283da00005c0c810703a041465161883c003140b00e9070400d591070b0f11442d00143f40003901e19092080110100160100c1d2240d0f008480c1480f070381d101140d00605111528084008880f4010050103103103075802500503410700d1080313207095054000300d80144650200a424000c1c4070f4040341e4003520170400c544201d82904181d8000e86106060800540090b02c00d9520460902c0086080c914020440c0c1c0c04581e0300c82030721400c003c0a400c003482ca111600c101c082c1031000c03001c00040c0070a40d0a0040c045608429400556203a02e5040a0115180a00581c2c00c000c5040d050078035282c1c105a1100501c0c409050451302c9840754039200440e4411798000b102c40070a401e0000810140000b01504000d03c1507001348151500000c0803030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 55810399 1250 55809149 55809197
    0x2010f0207050a03020607080d0e0d0207060f050409050709170c01080f010b03040b0901020403060204090621200609060c0c03120f120a140403021e031e160f0f03 71
    0x140c0c001c5483c0020801460f041e4014031a103440360110314102103008418100f00c0d00c20000c0100207400c032006030600240c1c18880c90028210703c1c2414a507902c0c58a4008003180207600460b0b00302c6a4031408500c0303080c001d40001d40140050615a0000701081203203544681c0340d41d18031070119003014089124400c00720b20003410307901c02214075401c9d59142e80712400c0da01c00140a42409541c00c000c08000700c2c0d0302c0c3c0020406803404110224600c0d1a00616401d824543c0120280d28851000d0032400140c40151164240b9002e100c1404000c84000000c4e900b40b06d401d030402d60040e40044c0c4110451008500f00304902422001e5074071a400540c2c42c0121803080e030a44c07244c500340400c400141c0402054201d0380140b800d290003d00c540c02c4851038100c142c401c0e541900581d0103580c1a800000314001611188030115000e0b40c2804a00d4040040004140c00031000040e4042201c084080c88070518248181d00602106030a1400f42014416006ca014041d000902d4090038031590b00d8041c443d02c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 55811649 1250 55810399 55810409
    0x150506030a150b03042d02030a0602090f0d0606060e01020604211707080f0106020309010207030f110a0f1806031101120204090e100b040c05030c03060d060f020702010f0207 76
    0x149140c1e1a10290001080c01007900e078401d11141c2d50204440f1200750103144524421031090f40e003010800c44d03410a0302c6d0448503007030308400e14841010060f2070102d4103d1a0503840384002d070312a5018000034140801d44507200da001030042c2030410070320402e90407a46c103d40303140e1284000c1d40014001243c80c1c0030200e40240490341444d01c1680364498049500b80344420620702074806d00c0781c030810300380303030b04016070340d0400040c124014000c0202401c01c40600405890004600c0c00481d1030010303448041070322001d049000481c2000050050640351500403403001003909146649510429041200c140101c641505045004200c040500d10907001501d405c148082c01101e030f00030044540500720300000b10502c1d001e12000455400714014051203403100000340c04d21042000c5070300c00725400d444105200e41d0801e011001d000d90407000300c0b9005444c541e0980e5896a5800c0807903c000751a01009042c186003045c4d0700741702c0342564040c08140340700740d82d04034030b0b0003908100720b940b000c41d8041c13 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 55812899 1250 55811649 55811659
    0x10f061d040803040204090b09061005060406022a0607051b01090308121305030c0a0201080a060b0f0d0b0919140105030613050a060e0606010f03050c040303110c0904060605041505 79
    0x46004203030042c0255a005100820102c2c2005080d0340e00b10110300c007039409607903e40c0002c0c144211109060207050240c1402d886543c1001e1074507400a5440c4948004042c40040103400c0001e1031040c11404112110060001a0707a46410719203143e0382c1d0000c10348281c1c0f070040760501800da984280c5200c1d0449400c180388606100c614070740c4c80c0403c080a41120702807640400744c0d10020300148007903d10b8001031000360135011060f0001401c039800003001242c62503d800c030140415540c400940c0c030300001201d071440d2120842440749006141200d0310b19070100b8404200301707900c0c8007004108012601034400780310300141c0c5102c903520241c00307000d4954580c1080002400404041f8080c0c82c2150241046442c0901540c40d01c40880c0d403400c1001c8943d4120b4420049a5600425100204482c601d003c03c454580301e0440e054a010760700005040202e10076403c51510402c10401c40103103001480c1c0c01302d03414185803100c003c06803482518010307070500c035441d520591031810240c00c651024003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 55814149 1250 55812899 55812901
    0x71707060e0310050c090f0f0d140a0b0103110a080a0b1906030b090106060f0216030f02040f14010f050604060509040203041b030302060a0614060715060b0c010f061d 73
    0x1015078014040400c0c440d09441410341080c8084000c0c0212030254240d00703442e130360b5056030b90188803660101002c81da000740180e40c1c4405050703d41025040303444c1d41249100080c0c3c9a0504114207080c1c0440340607002030001000071003402100359001c11400012204030004039545c3d45050788903109140d01401280002d00019400b03045100601d05a00c0320b6a00050170540325990004004400d0380c0310b9006030b640d41d5042c041241c0000110384210907600081c1101340e25801c00624464030703400700802c44100443c9150131034403940c0210303107410340e074010034071000c0b4241c110005c41c03032402d118981c2c0203e403a100019060401c2000c8070b0940300035940b000e14006c4010240400f950020b4011502c1101510405200440c084008005544207038041d000605014005009556aa410140f00300c0d0190f161494035656000071079404035441440c0100c0f0513400c40e5428003c7c60070780d01882140100162502d80f81d80c041d40240c2c41c0245030142002749a032038884c00c80140b020310007641003000d1518 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 55815399 1250 55814149 55814159
    0x50d020106171b010e040618230a1109060d0c0207050405091203060d02040612150b060712020709050106020d03050c0a080606070f050307080c011404080910020708031b071707 77
    0x201c60f880e80b0418104044400b500801281c2141e0543c1d102c660f94282580b00d00026031207071702504004140c0314020743c1885036030446990010038041c0c40110204e0f5034540710041d8064401c00e450307100ca8018503042c5c8440c980300d1040c01805440c0c82840042c000c4070b20100d41071a1910a19008804c414010030480c08140c15030b289640c4007910035a400301e28401074000507a41c0340035000141c10028002c1007940c0280c9407100c0350301c0058000280c2d05040c00d840c540161580002c0c2d030450343c1c000060340c151940041069041c02038640040312118203020020030500e0f00051403600070089550104029038400f12841810f0107040b0007600010490f402180303492604401400340f0b5070041c0f24000d280d412568460340385a01c0744404803240200030500c5103620000781300303450003901940500c921038a8151b462202d10f200d1405028401d2180008500035030b0f201300031800140c140e11084030341d11909039008240c0d0010b0030407010960b208541c0c01040404500c44981881046980101901800e00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 55816649 1250 55815399 55815433
    0x14040c02120306010f02120708090307080102070206090609060d05150f060301030507121505070804110904030206180102040506030406020d060510020703030518100c030207050a030b011719050d02010617 89
    0x805e1428110711441c2400c1140b48510030081202c50302c40d0880540e01d14215003410b05200c62540110031591041c01604003607222001100c01c151400c4405030703520804000010918001c04080c02d1409240c041003090703a080303170a0181030503031085a1000107030450504200540c072003400000c02582000310100a0081c860740c00c6140c0511030000e0700380980078001c02a040323a030115860b20000300c8180901060041003410a80d56203400d5070003070324600d81510081d642c0d42c07014000310b5540c14141d403030345500c000a5060300d028200c0101840d40c0c90820f410844080d400170a03c03541490302c0d202d4001460324040800351407a0f00706030050701d002461500d0951300358025100d1a100f038101c04490045d155940110891039a4050312641211007103410700900d441401c0c0c0000c3e00520f154081403002c640542c02107030455421765264001c02c00e10300c0c01d46003483c1941c0c4407004510039a16140c010440041045044461a903008001c81ea5580c000c0000c40640d0b28442d403820340100c812611103c4603 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 55817899 1250 55816649 55816667
    0xa09110904050a020d0b060108010f0602030313050708010c030204090509010506011709010213080604030306060201060b0d0e01110406050301030b06090609040206030411060309011e05091903020c040614040c0212030601 96
    0x440c2607643d01182034000c50b040703000c030034812640c0c1400c05081210540e0020301c10360240500c1124400510304244001e0360300e201c090119440c204180800d4410170008000c00d6001e40b130380c24000d001e0454406e4010700650000d00400c80315074200310005400440520400384907801c161342d10b407410502c0c0d0240c1d0300b8004001d0030046055408101d54100c40444001040c0140b164800030800c5140509008040b1603c1c2d030001411641026010003031480e2050999500f01c100150001d0202c0600b11000d004045207e030006410303401050010300d5582103000355049074001d0010b2800c2d0341d03816080048142003198103030b51000c020008078003d814001d015580c0544942c2d04900d98641342c1d130004000f50400c030b458910f2617444082d42111428000801c2d03070802c034010000c0c000c50130f190030410b4a90355a5500701d0a8010464100c20a01d88200000c044042024004009158070382d5208606000d5990a860095081911813401d03036100007401c003504081c1c8503019086440381e030011508640 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 55819149 1250 55817899 55817903
    0xb072103020910090501030c171b070b01081f1103130204020c0f0f07060201110a08220c050907081b0c07170601083d2a080a09110904 59
    0x903003404100c109440c0c0f01c0651283c0c3c500c03500e0f921030451600b400101034891030b030960300070000c40c1e00d65a200e030001c1d1304005070028001c06214942c42807001e14410240217101c006000c00c4049000082e03000804a40d50800e12000f69209902e0540c0b0f40113402620b04e02001e03044500800c000003070030102500d4840341d00500c001c0c40940b909e010844001d1a00e01d000c0f454031425001844c1042d14009c04024400041099000034041135048034840d607887e0040c3c083c0714003840310000008056410800000141041450500700030000c2c0b401d00240031041402407a0090308408080340b410340c064034007940324410100c18068540036200c51483c6680001c0d01da504684140140899a004210032402070030304040020140c1d0342c50102d1451a1a411007409800329096a603581c50301701c40e1502c650300700341c1d1101e64440c40690042403500200308442c5252820894032504856019415842c1209811640c0d103464003031321002c04900c115164007000901c0040800d00d40e001c5410301c40c2a40d640f20b4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 55820399 1250 55819149 55819151
    0x504030809040b011b030e12010b01140a03150b030702060f090a020d031107030602070c0f05010203030a0e0a0f03080f071b031202070c0b1207030207020906190305071805010b072103 80
    0x5c820300c2e401100b505002011008a0200e44859840e8207241001c04021400c500090002a143c02c00190080c840701d0203d0450460018490b10310310302a400220752101c1a6800c41a4290381d51204c0b40c45802c03d840460040c0141400308000c412810800c0d402051600040c029004c815801c00c20340c03200241d030480a00050345040c0450850a02100c0300941c051000941c1d030304038610b000c200985854100070b110f041c200c403041c000b40c0d9000003682d610502c032140c008ac1090310341c1c40d02407401c00021002001100c0300a0b107202010342c840c0c00749001c2c60b007a2071a000e0903113840c0415100456287c4012040d0f40f07c00201e000801d214103845030b1001c030304040052038810684c0740c158102d0078580090f459601c00081e040e40c1c804c0942c001d02e030302050500d4114104101940050803410018121070b106d00c0320024100c110140d0b0441140045070300500320345d46565100801c0543e4051103460030b81d52803a100000503001680c1c0121000c040e0700c40002c2100424001254014218000b0f50030101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 55821649 1250 55820399 55820417
    0x90105130e0601060207030c050406031e0602070f08091003090803070507080412060b150702060417101a0109060905100302160f060203060906011706090601050d0207060b09070504030809040b01 85
    0x20308410b200e064081c100541c0070704909070450402d644d481c03813180d1205020b07500c2c001c01040032039070b000c0c0343c800e42c0000c01c140300245001c00d051440290051400140084200d0880e920800c10360300e0052044100c2a0381311407090b00381c54401d40440c2c58404000c0d04001c010000a16014410401044114840d0711940c0c02e1644031900c00b158040584011500c0b965942504241440d05411a482c070481c401203e5141c034030a603001c10158040c074412154401c805024240211b80140300c101079405c0c9420b81008403050b4281400c45582011074001d01094108601148040c480c83e45002541c00c06400f241c00c03003840e52412030081d4092140e5081107901b843c50007000074248042c01e850079000c1c01e005a12030802c03104200740d1410141400e414011100403480301a240f0211681d44800b00301c890303040c00e07512017005030350904c02d40c0c0b040d54905100060020400150364460101c08805640c9a1220341d100801038940b88a58000a09112805c1c4010741a034500380d001010800c4042c5408204 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 55822899 1250 55821649 55821671
    0xa05040806010e09011b050405011211180a05060909040f03090302030a0501141501020d0806150c0109061107050304150e090103030302030a0507020102040f05090c21041101050301030209010513 85
    0x41401c00c1e0441180c058442c010311990346800d020fa0140c2c0c4042d80100140c0900b00c80010b0a00d20461040c2d030306120452000d10300c1404941d01c0081c4800a0105403a501c400c19461100e0625841300898072403011407402103514140501516112000a4032810b5a9103480e22015148120503800310200712403c200070005071414445070842034810000401e2010003442d44203d0f0311001400e6000c52a07464100d0412a0390006000c8a000c0403802d000545407100070100d103158000001e480e000110004a11206000540c000e07107142d8051001000b4071520002c2010191003001006803d40c1d1050106120a204030062501d014480e820805070501522003c103213202426030040e40030a601108005141d6958040c42d60f00c4491031000714030740350a210302c00d120f00300680210b6028010b4580001c24400503103040720202031802c0742c3c01180b800c000501c400444030440d001c5400c100d1407203800d1f09950141c41030b00d050b070340e00a10f510840c0e0300740820700036048000480c1810a17501c0b6421901 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 55824149 1250 55822899 55822903
    0x3031109040e03030f0609040c090c02010e0105090304062c1e030d0302030906070c03021b0a091503150203010503060c030901150816080a12050a020322030b0a1b03020a050408 77
    0x80c1640b0b48060f54903454007001440705d5100040c03046006031410010400018401000582076030440350001030400c0c900e03a001c07801011000901202ca61810040c8a04410000041c0c402c65403169180700b11744800100002941b11503001c2000d5110080e8012561890401031700345030394644050500d00c05d4800c4000a00e070401c89240705021950005c20f01c11041d00030b0282540c40030f450300b1f01c1711882640d81c1e0003d5880c20000c1c1e4a0a81c1e101c5400034a003a0b9864000c03520051110007828450360031102c2c10f260203c1c9e001e2008984000d9064800c4041030168000c2d00c1c12240d004003c1c04143d031b80c98204910a03030004040c41c41c1035680b031034501c08000c07110b201c0d0006403600c1401400d188000e0910118250190b8000102561207120b038031002071050724250900c04080d2919503140d00204800340d10b540182c40c103503099900300c2c028450720756000c40c010000b00c2f8003620301105580c551380e08140468070756450b8544000303e0040f400829901a4000746a000d000703140840ca03207544c1c2c418080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 55825399 1250 55824149 55824161
    0x1050103030e0405070206070206180f120a0908060103110d02010306170709060501030e030313020105040e0f0a0f09080702090c0912060f06041b080703110c06250207030303110904 79
    0x401082c01000885281d090910500380e202840707000030041800c0c07941001c1d64a034001400400443c00e48069100f0841c0180007000380e484020085400c0400706108410381c0ba0408041b890001c0d41d80c1000046d51580040c4940c100ca400541c0e014001c5034950500a0b200704068060f4140b607100c100015480102382d000b100e0042101c00130300700c0c40c3d003010318100c2981c80e01d5200e281050306000450141c0c0e04c01004484e0050014014140000c09910050304c903070143e60300c00564425101e0800c000da518240310b680c45400c0c600b00800c02d03003101282800c202d8040e508060120304042c00724a0040c205941010f030030501900040303040c110104001191000f000e20801c16a41004003403022014012400d02d03040390040324207201202c1c820071805d1100340c032004100200244a0042a8034134000d500c4190480d20b000c080e540d43c3c506544106583d28001d49404107000d001e1030780390b4801c41010380c0e04652910942d0207000f0301032460b10210b002e007446004240c04070108000310b43d0b180d595032003a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 55826649 1250 55825399 55825403
    0x2150a1815030e03090a05061b01020a0903060608070b04031103101b080604020405031c0c0c090b090a0606120b040e0d02010603020a090903090b0f0702030105151003060b04060c0201050c01050103 86
    0x2401d8240d9078a00040a640352a10328401651080c04940003d544020b0322500b40c640c2070b650709480c0ca0355100506100b40000031400190b51000400400f800d61150b80c040940b1300420050042c10f5850002954810281c45803090480e414481840040d2250b00d0501000600070200c60b4101078a1000f42d00700d800c81c005091060702120074005199401910ad40e501800860741141080d183c140807076281c0c40c0303080d00c03113a00312082e20081d070b0340d0ba004501071031249400c6059200200c1c4c4407800040101503915030036100e8800c0000245403504035008180689000c4c1d51014211000141031401802c071140e8460f07030203503ca00c1034002e8002c04100005603c24039500100c1c80301c0c03850045c8000c0d175800d5046118014101107203240829000140c80301240c102c500602e555030702c0c6099401da240030b0b11100079031550070300060180991580510440300c1038220741c82030702082c0d450003d40464659106040c00b128050004000e02d034007c286024002e401270400c580741c00a403030055800c643c401d03002 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 55827899 1250 55826649 55826669
    0x2030307020c09010815060d0807060b1f0e1009030602070b0a0606020f0c0910030218090d030204030302060412230717091c0c09020a0e0f040902150a18 67
    0x3041445541000b5031011804141c0d04800954185259079840b0344c04c026040d83c024600e10f02080164a404031504012030b0095019034961030070703141c20409400928801440390343da485020764810151400491018042e8990350b107410401c2d001e00000a032582c580c001402444000000414591f00052400502c50300c105e103941d01c0c0c0207686504840050700041c0441d80000021401d49400107100d0b000d001d42211f10070300c2582c41e841005c0d9030541940009403c4001c0300017000d01c010511158501a070618800c0d00c895001115089049001c0e0b4031003d8010b80c030031030204010402481000d0000190752402c20340040c111081070f01c1800c480500c0b400480400900b42050110219295640b10b0040003a103151200e4040060105040010703513aa00d406074070751120803c4518800c1000800036043d041d900c44030205405482c48086114060043701c00683e030144515061040c8541940d0007040e0140700344010a2800d4103400c255212814041d07412411100340c1103d07983e61000f40003501e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 55829149 1250 55827899 55827901
    0xc09120b040203070602030c0d1409040f0209041d0c040203040f0b04052104030b060f0f1005121008120f0d05010e06011205090619021207030e0d02070302030607030f0e0d020303 78
    0xb0505207003034041d0b4800001c40d04244054110032101040309038100d8198030305180000700e9170b00018202d00c00c50104940c010b150000d40000e031981d079005003c030351500301c40410900107107503001c3e01100c6052000003d550803130421a10180340550166810601070f0407a10440440fa9850070f105540c281c03030503141540000521038070078104900000709a900410701d0b500b0503146988030706400c400036100a00c600848180204a070729829054907204100034454010880d40c0303840a84242d00c11012400c10030a4036000540600700c6400300c1c1c0c11204008010050718148203000300503038000b4101104841007c00030b40c1012030300b0780502400fa0801c02c080154905041e03002418000702008284023443c20081000410030b00865090340c80102440902e0704180c2c0040850000d100d5110510821901a002d003d02c69600da40001446000303041154441c46044400740d0340c0704607030720000f54160301c26400074a000d8400e8000000f020181a03000ca00380d4550710200e0b0400198018200050748044 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 55830399 1250 55829149 55829153
    0xd0212040803010305100c0503150d0b0a02041e0e01050607020d14061905040b070806030304090e010c020d05130b07060608190b0105120a060504031b03170105060a120c09120b04 78
    0xc05006c4160307441c40d01c10050f036080200090014080201008049100d440c4525490344980c1c3c080146154000ca1a514920b0b000003403800a4009001d8200d00c140d82610b42c044882c5004410303002c2d0b6040c000041456032070401008040c0c0e204010480e00408030800520000300075590b11000681400d0240030707549400c074005074078011410300302203010303080905110100344a854616005282c07845c1c013030b44c0c80e6502c00200749903104a1f802940090714211a0900911042d40854103018680d82035440003d0706c1030003294640a1140c2c0d0100c18009001c0c10850342201d40300500b03600348510300c08240155102411030400c08121555550420758005160801c0091082d41c2d001d42001c440783c200d5401c1884a1340e5440100c00743c0100f1351595940883e040c1800317402c281580608049151680080c6481c00800f040312031112150b035102080c0010816240501c04d407040f6080c10f5a51108140c40700c45601b0180004200300b4060080004022842d503854074000c1035114020601a010740c1824 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 55831649 1250 55830399 55830403
    0x10b10080603330705130f0f090507051801021f021317120903010603020405040309060f03060b071e051e070801020f2a06040f061b020c060d0212040803010305 70
    0x41d110b600440260292054020ba501080c0b244550743c0c88000411250b4503800705031180d108065140c030000c1000d810000d14081d4800c0e40000750341c500c00703401c100103940340d2180040d02d0090381c03598080744040c00168005d519003002c060a0080510440e15070410520b5405048030090000280840d000214a65005842015080241407070000208400b0480000d0b40d110b4001d4600480c10301000503801c85165403d4104030302664004000b04560706192030090180003251082d080480c43c01c68101407528002c0c4940821100c0520140f80780c1180390741c1d840321665460160703100340e403412941040401c10801034000c00140503505015050320300c420b82031034200b1380cbd4040718441c2e00411044904540c40400d6403442007089110911021100c203042505003c0520030300c2d030070700c1040104400e101e00c19100c4c82d2850b01585040041c80022a00c8101e01980e000083c0090307400300150503018200359004101d060f00300c40c001030034031354050000c000c03c04055070140d0304c104000c00144180042 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 55832899 1250 55831649 55831663
    0x8150603010e09060624070309050901060503041b060c0f031101060611010e06100603020f0706020c10180f03050a02030c030706020c060603060403080f0618240109080a14010b10080603 81
    0x2110408080c0151b140d889881c82c2980c903004d14600400700d400810036014450b6030001e080010700d007601c0f41d80c45940040c869041201d0036aa010201025003458100d0107072440150380c9141d4694508110544495910844100045007000394114010041000070f00c9503001a00b0f0658400303072102e903140d01403825200305555402440d00800709218150801e9803452084030410306003d070722402d150803c1d07203a40c0540d60700500300c54000108140c2c0741401241491041c3d400340001c200302c5040111201c05600e42c094014101d103a015114400302c1e00a00142c005d401880c4100e91604000310116402c5422007101204c00e0f03500815505803055041c401c1c69030059042c0d00500561a1688004040242c0503000c0c00c0c24010f80c0010603941e4a910035100b140c00394420700300f034150400b1643c1420100314200a034495039144a54200c8030362240c49244200c401000040071800075640301c11500743c800d964400410740d0b80d10403100e00307912000b003281d074481100d4642d4040c41c40c0082c00e142c01c06107 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 55834149 1250 55832899 55832911
    0x4060501180c09211e150c05070b042306010302130c080112050a12050c0105090309030a02041a030a030203040e0f0115080405071a18060903030a08150603010e0906 72
    0x4101008011610751058081d8211188000349840345135924040301c0444100da04003602c1d080d500d2908016030546002082da4a51044450300401c0120308008400c403aa4504450001362041142c6004503081001242d0850302940440b400f4404501d0482141d1a204c01d440c240e03034000030300410039458092500300d12b078114a08103220000b4400402840c188050081c4402c101c1000c50001c103000040180443c0706610002c0720000d070fa080107016000f0340043d00a00f43c070351700b003c001890100020080e540400805001440301ca0a1a03081002400e01308a04003a0400310345020342c12660300b040700c241d915000780c002e159104d061480c3c460406400410704c0c0c4007004030900400c4641180c408d0300c400d05682d450281681d85032460414202086a07112a0401000c1c000f01d840c200c1c540c400805c030b0a11301540e0030745d030180720000340909401000201c640c50b400a111403400d06018508050344071502d5140700e03c60070b131303800e0020300c0341c0d042030700005040f1001c0c1d010031001840400c0780c0ca030480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 55835399 1250 55834149 55834151
    0x8010c09050312070c0b071b09050105030d020706020706120e01020a08061905010909020c0c04050108010204051e090406020a02030c0a06061518032a0305061b130306051801050406050118 82
    0x2004c50300c030703043c040c001441542c10314400010311805100802210320350b050a62000021031941c2d03260341c40d0240030207001e0544640038201c054000907000040c1e00701150340a8000d0300181d45840e50684142205264050b0340644582c8400640442071004145060707858075054154180103003030190a9519407501a03500c18000c505000307070ba802001c00d004450440c440981c0c0e9415203100f86040200b00c69010b0b800c1418800042006401034015000b03455040d11151035000302c400f00c2c003404000844910f50400c200c5004100031410f40d4000740108000350044030314112036602200c0c50406d40c4102511059921281844020b1042a400d01d0784001894181d81440329003410103101d60051000a10003640e0000c04241c0001c0011903d0a490b88808070414030b80d43e80c10103d0311008202c0d40e2801400448050401d03034090102510407003e0b200c20748031580ba08660f56503004250151410070b040a803500c00c0045e00d0400d01400b4443da00c01c54000c50036500d88600d00304e051036549004441c003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 55836649 1250 55835399 55835407
    0x3070605010f08060c0a03091e050f01020a05040311030f0a0606150503040201050909060a0b070804170303040f03030c1812050c09070e010c1104091b09060e04030305060a08010c09050312 82
    0xf842e00058601d8006942d00c0c041951100050001d40003004a44d40040c0030350f4104001800c080c4002c50700081443c050010f4403031a8401c0031416080344549695070b008a6000e100900209592040c80b5a00c2d5201400702e403402d00f4400c001519154408400311030f00c41e220740c401c1c410f0355502070700b00241080b5410294154200340d800645140607410b0300c00c0c003864150000505982d100a1400c0041070180e05050350b43d141424151113075031081c018403410013640349a0914003c3c00004a0740305581064056100c03400a40d021405010b10302c0c0410208105072011004001e0a103130108014200307d1010706100c0c0041c5009800c3c4403070710a8003485200700340e003001402e94000090200c1180c0900c0c2c80c10305960280341443d8071196051026401030701d8032541c6020000301b82030400d03030104034600c80414039689060301c00a86015010341a109503c2d440030400180c0250080c980080c0c004161082d4561904080d0703085840d03441c10607001882401003044941014401a10100c0d0415a01468 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 55837899 1250 55836649 55836659
    0xe010b031911030a05040609020603070309140d08010b07051203010f050310090201120c030e010504060203060a0e07090306020a110f16050a03081902030d0216030e01021c050f0d0e03070605010f 85
    0x1d003c001c060481c43c68803040003034204000d81d8001003940340d000704140d4803400d0400c0001c0013400d400c20112108803140042061501002030000380c0714640e030340d0b0081284c3c00d2881c620b0044d000100c045a942c8240c0001c01c1c034080601d009903020b41071004058980510340300815203400c0b107000034118031500d84001000941d0388011011352150100c1c1010859000d041c40c00c40003031000e0f111045180d480c4c201440100b03c243d130015401303043c00b01c640d410169200d600c1c031054a00103039030060200e42d60540420000752141c002d054086401c1c02d0002d00c1c0610005c58034242440305140c010140c0104500c02c4000421440c0c203406454160390b100802d03401d554800e8160310841d242c500c1000901c15070903402c140b007041260809002100c0554407913110301048068008981000c4000c120201154001d03544006411050300c1010f1180d529144c050050582d11503201508402c1c10348410441000540058010903611410f141c0045580c0c0800c0c1c14070104440040e04601054540c8040400c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 55839149 1250 55837899 55837931
    0x603020a08070e010e04090f0b0f01150305060a05061306030501090207021311160c0e0a0b0609010e0a080a03080108061005060a08150406090b03012a08040c0e010b0319 74
    0x54401014144071940c1100d283c01601c07041d030b002e0300301ca40c840e080441190030080c05402d00036085100d19801040c070348442c040c2121060003401049040721003031f00f031b10f13840740d201c2c1c2c1010341c0082018161000294403440031a440e03510122500000140c680300030024180d15100f1940104440c1c2c4045041040c1940098201762101c1c469260290b100c0c880c078040c8030305140c22295403540f01040750390001a5442c20101588280c0b203015000610000010031800301e0703000d090600d001c000c015a113044103040040d0390740d208480503140c02ca03900c0c2a020911400401220300018000d85900e0865850a0451032070f04030002c10000d1364040d010002c000782e85a072010b0318401c556605010034140d032240c3c600f600e00b8100b20241588507050100003e88a5050360100e40d6000781076000340a0f00c05c88a20300c070000f2146000010310b420110540c0d01100e489112460380251040e282681c08036500c49954558000a0b00102007000e4004217104400074400300404020aa0f90381c180813a03049120401 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 55840399 1250 55839149 55839151
    0x604050c0409050c09060319050f010e0f070c080a030e011107050d0818010c08040201030b09060604180b04050403090e010608040c050405040302010212010e3112020a0c060f090603020a08 82
    0x700542d500e0340d010908a40b980f00682d4140180500340c69240d2034121100f0200b040343d50089580c0516000c0803d42c0e03050001d5145040c2c07406143c024007184c503888174501d00e115006001e0b03020881105c40c2100066001001000b0005140d90046401c2141c0351a2070300715441200300403e1040e0400940001640109110000340124108401c40341d4545400320b0100042c00700340d00780f6518100c41540060740012685001341c0c000e0340c0400c500301004090240451065a50399803015043c4820802c00f012521611501c03100c500011426800355004501640c1056130300b1004a1a54403050040c105c2c960a00350043c5079a10f0701c06020704150719a00300d1840c0e03500503d030050381c403480000d05042c000d40403075401c00f020704440d00e404d694a0040d54811001a01d50140408514490711240759406a8480290119541d00d0300240030341d42e01c0f213404060200042095019205d02500400c01040c00c200042009848004070600c50032070040c5900240d80000c001d1503c144846130816611001c22 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 55841649 1250 55840399 55840409
    0x6030603020d082203060207060c020318130207020405010311100c080409090c080d02070501030501050604180b010e120102040501030507090806070f03021309150602070303020303040312021b0309090604050c04 92
    0x4240d40d4401c000e0f2138141a1400000151804100000001042419801001602d0082a01f08071903045003c0807a100d10540c0942c00441034900c034030004528000381708001c40103540800614165083d0301003415100f09134400d807110340214900390740300c0c200710365440c1c6101c0003450a106810f81070b5a034064070740294010003200d1980c50b001101000070b4100564041e029000881e050000000700c0203540d1700322801140d002034144000040c0030300b48481a50b00b5909861401c82108601c03e0f0381c1d000030700c2420080b41c100584d42e9220b280d43d48071101807800b66510306c000540d4580c14180051300340c8002501040400401002c2004034181c0440c607150012103514103038811a41c0c1c400b003100a40100d1003078082a1017945400140740c8166407014a011445000040880baa294000e0b41c85000920000d0b0168004100040001c5c0c0700e0801a45000b06a1800500b8604f0401d001001c1c10111803169205501c0080d0002852410045441c0d02c028115014051458540ba81c2c50701c500942c419 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 55842899 1250 55841649 55841663
    0x3010902030601140d020a020c150d0e100903050a030b0603060f040506130518101112070c05070b0a110703020307060e010207170303161b1101050702040f0203090706030603020d 78
    0x100301c15031310404041c05000d0b1800070142d103412540c40800002e50117400d900002d4440c003102c2800d01c0c10300e0480340510b1007040803e103003001c003040342d0140a8400300e0480501402403203c0c9101e61003240c030800108078066a80c95849660010b000390032500540d06040c450345040c000c002d00c03507680391003030007802106076008181501c0d800c000c28214018800b001d2806410101049a6889007200480041011504641c1c6d0b0410140c2c00004480189200800b158400c2000452001c100d1274031035042051840c02043c00c207050b8440d541010b2454020366400c0c0b4001808042456000600310100100c0b0307005010451b1655000075645c441303610442c001d00c1a103031410002a802440300f50024104108001c0035000340c112160740725442110110102c0f000c00300411042032040803038250480c0301c1c44648001264986170fa140300b80c0c05458071070400004000190058840307001d005950040603401684a0800c0074150341004800c3e0040e00030546040307010400350350b0300080d100c926500641b0b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 55844149 1250 55842899 55842901
    0x901050420101b0209091c050903030405040510181b0203090307142107051813020d02040204080d0903020307120c0504020904060b0f03090d0906020c01121e09260301090203 76
    0xc0720008003c0384050181d4007452110805c1480c60b000301c2d582145079402c442050054060300310a541c54003c0d44403086d05580309000030b10403800c255000b55003101444201400c00d503910443c0c1d40ca5000c10741100261540c0340c451080e031b01e41340104406014459400510f09000c80140400d55414462055410464814081d49210749807844280780c80b10040b030303022295280d00501556140c84620806005c0d181100d00140864090340522340904041041c1e2008038680c0e40805c54402c42e05242030341d000d9420000040c0c3d561081200403602c0c9080e0720f45440e03140c40c42c0109400c02e5050351207008003010011103a40018111003204c81070321022600145c0780c500d0030004c00d000303180d541c012902c03400d800255000c00c2c14210700918403a01c00b49040320390000c407240080314070f05003a1160b0405a40035664100943d80505500c0d20a0708050320001020510310008a944200102004500d140c0c5d82d02d40c0000e21200030300c13551140b4002c16000c0c1021981036002a6644014810444203076400700c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 55845399 1250 55844149 55844177
    0x1207080606090303043f031214010303020a0201080705030c040506031506130906050409020609040203250c0201020f0106121e0206120a0c140d020c0a0803090105042010 74
    0x150a030382c10450b0107400c4a4070303281c5400c02a007260044840c030000c803011060030030000004074410030009030501076504003400c0e41e566041d2a201541da8a07416060707200c001c802098114410030b036000f18003a43c010680c1d40c0c003500025003c404050646010800304000b044803400000003250100c6409441c0d21f179903a51221800c0d00c403440040c8031b00340c0c41980094010b40c45c480030b001e060b0541701101c0f0304121282d5108100000c4580110000713421040500110a95280940c090b680c0000041c0f03040880d405c6150906c01d00c1c5042c54012404503806603599800c1d035a04100802d10040b2480007000303040e05007008510741403500c5030002d102c229003075240c0e203114083c1e4400001007039001e4040364071041003056104028104880004485203404901d18910380300300b03e400c0c100c410150807d0b2803c101c03032420001039400b6030094100d521602070400000380342280154418079a83c00001403606291500044880c04c05006c0d68955088021224913a5204058003500d11014200b070302188800c5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 55846649 1250 55845399 55845409
    0x2071e020a2309010602070e13030801150c0203010c020d020f0102040f050603100905090109030e0303121b04050d06050906100f0b031905070905010207060201140a11040e040302010b0f010512070806 87
    0x8401d441d0f0b04509102c0000611a80010701ca5007603c40480c6070002650310321850803d200c0e0400809000236004500400200740112100b410f0500341c3c0ca05124040a01c0e00481c0c00d648110341c2c50001a40400205001e490341880150b880f80b062200a500d041d1801044084840705405954418807000000c40c490220043d21a0b0040c51000c40600c042e14101080c00d00a00080c581500810503002090b800c074a000300444240c0a290201483c0c4d54032444040d9140420700c0d8420020050f081101140a0f0b64280005541920800b800300b064a40b2800341c0d42013030b01c050245080c014000c1424004840410500d0055480c541a8280c03243e0f58421103034908541901100303600f500d860b0502c00c134540e02045200503920700b1307001c50300c15070b036241012401c0b5103203542e00140823101000820005903154120010b62046070002c2ca08258498240990362803003501e044002d40c0d55a09094000e05080b901da00444c942401c011b41008001200401000c80003000142041909000111613a4079 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 55847899 1250 55846649 55846709
    0x504080a02060d09120c111f030b1c0b040615030803040b10170a0210020f030414030a08130905010605090d02040905010e0709020406020f0a080a1107051302071e020a 73
    0x2105d100004088100262090341000c40070b80382d4402d180c0410b411402d0080c45140da04400140511280e000d1240440040c50b000b09456405028500c002241001c0385900781c840704c1c01603210446905040c50981304030f480881c00c24004000d507103000c1000c1200d040903a0703409a0055203141c0c3c50b599040302c100c6a280c41e41c02082101d182085108502c0400040d911a220310980c1c01203042c1c140350700e0036a41d88030340700d404102907882000140a4008640b11b21a0f42c5035004d0211202c0810039a80c08459401581c0180303840040050f0400440c081401158010301640c02c0252074102c103170020a044580050b0081c0c000c44d228101c40d802c000007580008500180d08003510416916254800080d60081c841c2a00611540440603080140800d13901402680f141205103483d039848002c0e47c142e00620210100c03809030500014880c0c030703025142d5481503005280140e13180c0c228900900c02101d40c180c440d0600d00302e0700c001c000585450001380b0950b0f048009159120a00c07a68442071494 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 55849149 1250 55847899 55847903
    0x60d0303020705030f04031b051e060c03030a0b100305060306071d040c08060f01090803120c04080709021b0303060a09110706150501080f040512031902070f120504080a02060d09 78
    0x204c00500488416004805441903922030031038141e02480310300d544486082c80d8080c082c2d00c4514030403400c4591651240c00c0807a00390161100c1d05005246c1d1b80c041c10350f0411601c001000780c0302d550b40b180618124590004a01c580c2c242008142000c901180d030b07400008002100380082d0a08050845584c88400004240c0050060011040d1840010b042c81020b448050013044180c036032803c5580140009000c0d00c028000840c106142a490540415800b902c81e82c002c500420010074482c42c180031000142400031009640e90f0716840300001c061a01c0016400d05400500503c410381d0741e80104c45c41183d0b0b400201140c0b40d21540070182151081581c0100820310b46444801b80c4144444000c081b10000d80322500541c2d1000300c1142c0e14042200c004005402603425220f500788a0009550810300c02041e64604082803000117080740c0c0a9041511070705181054101000350440e42082d94102d140780803410303c0d140c5116250390b002e0310503000f4032070500401d0841d0090415803050b41066 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 55850399 1250 55849149 55849153
    0xc03090105030402010e130b04180201020c0607020409050613020a0b18040f020c19020907090608070513050a080105090c240f090604031b061b03200303070504140f09060d0303020705 80
    0x40781003c2c90310000d04142c64410300850400300e442c1280d04000184ac424103070103030068805000402c04100707242d40b004108a03841540c4060407408250f080102c80e01c2030540031840c1c072034a8140c0c01008880f00740c0341c0c403000012608029210341d020120801600f2403205490209024a5180b11400030b409226a81c480382d1140c200e003070101c0c2043c0c00d40c07401c4160080d54194510b44643d4800c5036040000c0c091500403607030703541c0880d042500c6003000b000580400c0100c08142c503102c00018030b01c0d0400b9880406540e4503482071024003541400005074466003240c3d806c00002c410701104d60150a00e00313581c6541d80011800c040705c0740803502182c03640100200441c3e0348684910740b140070907200b6240303d400c2e8072004001003011400741e889100e00000703176110400d81c61815501100c046442800060683e41c80340a405080441000a50b002d0030301e81c1c80315525241882e401c07040c404225540d0500c5400c010348011980d40312081900c0e0024001e440780c0c05039548508054000e84910707940202a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 55851649 1250 55850399 55850419
    0xf090810060501120515011b0c06080412020c0306010504090309050303130611031204060b01020c10051b06010e040602030606070f0507050108150a0501030c1b061b050c03090105030402010e 83
    0x160310036034046001c1d60003d803146005440300e214110f040301c0c0101c4040c41b64180b0040b00080a60246240107400301d4070200100045106546d040b00340c60740c0d40c1c802c101041d005400e000420660b1006245524401d10041c050f034040480080d507240e1044c450741d401035568110307000916100f215088040c00010302100c0e074a001c0d400a462240c5064490710f0009900c0f4100c8501081c40482221101c8082400c1d5004ea0703211512240010896000490f043d031141e07044148244d15160303000303140707100140c031002e072608010b0601ca0074681d45440042c0c49608404014000031043e40501034116070003034401030326551982d0209000780305030003025101d00305480e08242005000510042511420380c0c501500e034590031003003c0c00c055039262040d071000c502c1605002c81d510a41c0601c580079032914051244000c244080c041c2c882812800366156510b07003030404004908a0005c01052036a4070f40640f600c00140c040e81d499000700d40c2c0304d03810400000003040540e8802c009984151070000c1c000028 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 55852899 1250 55851649 55851673
    0xe0708030405120f0d0302180d0c0306181a0405010915020408010c050f0a0f0306170606040b030c03030706090c05060a08070e0307060e0910030b0c0a030e1c0f0908 72
    0x500c1e0854450315104211a000c000e1060b0300109825138072a0f0201c004041000f080395096020b5081912842103000758203512402595a83c0e99040364103000d1808524442c1c11030501d0f00c1910280c03000c888d0701070544419140003604048d421401d0781c1d00203000600a44481c50201d014040440c00501b035051070305601860944a54003d1040342c2c0880020000401c500105030b54a01a031070140c605540d00f030111140c540e01450f900e8014500c98580001c2554a9040380c800c00148014103800c01d911010402615080522a80b074009000314010042010044002540d91045400050034039450b01510410400c19030020ba000d07000c02031406480c2d41c9030101c01400d60204555050000308035091116181c00c002c40d5090035103403195903000e22000104284081c0c5540035000d0903032030450f818001f01154045c0003a502400110403401d5507240c4000008080d07880e00700001425400210007140030b50208121400b42c0b0110f400c0c241840c00ea4200f043e5113964060313111341040e000740e802c034100f = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 55854149 1250 55852899 55852903
    0xf0c030305040809041b0824060a090503010f0b03010b061216020c03060a020a020610030c06051b1603020a0f0807050906030c0901080606010f02032508071e06050603150c09040e0708 80
    0x80311b1120303a07480f000141e80360340048960011b0b21604003c0440d06c4109407445080034001803661540707605110203040c0c1d42e0390119003100e44111000040c1e5030f5485814104c1c0c03400380128074040b9000c45059040c00071000b21000c5480c00a03025002d0b0002c0a403400c04114001e000139101248003d043e20000d01e4960704400196004c51002070060146000141310315107410121030942ea00718071017000080c02c00d403081d107059001900d0070591001c0710a91580c41e6408020418172054440350705c1d466580340d8810310800c0d20a9030010302d2040b9585a0520071580002030841c00c445c0e0444100c8001d0f224500031a00703103403100e014030760000c1044002091285000407074600800003a03035800c603820440781003240c907030090302d000c07000c042c60f081c024060220801c1d8001024070b0048000d68500891030ba15119254171200703004450203844601503040c009103208550f03011409402510100707411078030000d02d452004242c0000d1241c0883c5014080d12258000c10240302c250040312805900c50943d16 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 55855399 1250 55854149 55854191
    0x9050a050303150a0b03070c02060d0b0a0b120106080112110a0902030f010303020601060c030210050601020c030a0b190908030601030c030b03070f080f01150e0718090510060f0c03030504080904 85
    0x18007031100c1603000102c140c01d05e01128821001c5a0b2070060403241c40e42002a1a40444000600fa03a00d4250110007030340d82c0c41031500240740000c240c65541c16005541800064164850414018a10010020504102141c044071a40513040c141040000c42c009219582c003a082076010920100400c0950404c1e0f01074203058034041d40807240030383e0f603c0304c1c1203940390004500100140c010181c1c81c0212181e0f6000312b80c0050050056940c0c0440100100349030501c80641a9800c0c2e140e84180000c03034581c0d180c07200903004029420b00c00c0a4046d217034100b00c2d20001c1e007030a04040da40d080151440e842070b8003060050304014160741050355140c0c4003404e4a54640240425400340200b690881141446441c902150f03185081c0000d6180c9000c40d450000020900801e0003000385803142100c0313511504034007900c4507a4000a050400d050350900301c0303802d0f8204209008504035001c0b01542c10401c107101640d8585008100c176515403800c050540286181e003a0050700b8454910de402584110310 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 55856649 1250 55855399 55855441
    0x20d11010f050403110c040204060504030b0a060b03130b010e01060c03120e0d021b04050f0103031101090203061006180806150111010203042f060301090914060408130605040e0a09050a050303 84
    0x1b070f0b0400c044501004200d1286100c0c440c04284200001c00c00102c140f0400c035270002d921040081c00540d9020300680d5580111020402491342c0c0a079035042161118200707000d84031900e0700d208150306107900a012102c10b0f00000c0c0030303c5481100c01300851640d42111400140707804c1500c142818503600032b55074401800c00f40d020741061805014580c20644503040c8101e41c07820300703804540d02c0d64600340c440308142c0340c001f0010354881944902503101001103a02504112007464161498100002d01c4440440b91001c00c098070401c04014000c07001441581100b101c032042c514401c100c10050f54000c0e103602500200b035002004001c1800002c0000510317040742421501c81c20522a265201803040d0220b900358005801d10041c000c00c040c951000180310700c1901c0c1e10318440f8005510364940340b8200da0840e04410b001520782041c0402c410301800501e49801c20905007810b24091080384072000b0442801c1950395880c81c0103020040100c61021a009401d80e070781c4e41081c024120001c1544566 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 55857899 1250 55856649 55856653
    0x140c1509030c0d050d1b0804170304030c031b08010902130e0f010e0f010b03150f0a020d0e010606030e01090f0209070519050406090b030f3702030402040506030c01020d11010f05040311 81
    0xb110b03190a200c1b4a04150340c9622001c850300d824100084121922005441c1c95480c0c4010302002c000516862081e00145000364900c24031060410129200140180c002d0440d6074103014107100140c076041e400b0700400080f1040071650801e41d00401c5c2c64440c0303140c035803411036091445d0440e9803080400d48010740d0008200074070a5100a00c20b0550318101042c030410040d44400000d00076144a410f00750300300c1c09100300545049998105007050326031031007207108207035541c420410074540c151051070b8200710030400074091400c0740c0d12802d8220819071b070301a0141040100042400c2d11640842d90502c002c210010215020804002c110b1b80050048d1030200380310f507030080380500241041d2032040690303070355540c003955400003c00700c032414001c25251480f88240b88410b59140074000ba2a13007280c207100041c1c80c1d103081d00400060340d401400450007500f011070201d40c5664042030034254813080f41000c0e2280d2040104890050542c040070100d050300d030005000816a2052400b1182401386d82 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 55859149 1250 55857899 55857917
    0x2070602180603010302031e0118030509010201060515070609080903010509150603070e070c06060807061805040c0c020d080408060f01051201050105060412020111031303140c1509030c0d050d 84
    0x41c03042c0340c4003c0c00060345c141c0c014a01411090740390183d500c141c4240318004a0382030b182040c0c0c403a1605035400c0072000b1070000310700096a03513824401c4600038002103c200c60f4100440310032080038811404040c21054480c00650203101c460070841d400d405020300200081c0c500816081d440d0000316021010300260100890102d16002030803109481034941d54014985400c002901c003c0c0b15880100e92054481e20000340005081c00200010034107611480210004030340c41150071211900100e204910700b5141040c00c1e40d2101200c0e40080d4165003501d8130046d2810000707806d008981c42840c1d0340c4210010002d180da142c401003412250160b820108261601e410709083c0c410901945401c500700340030070000260900020048103006060251541e9003082e190f50440c0c0c400c000314800340c0e180d44000c20030002080000444e6000100180c9454454100040c281c41c1014401e038002d10030105003545079540521803daa43c510042c420310b0083c5207450560f848801490000c03001c00d1072a4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 55860399 1250 55859149 55859197
    0x70f090b0913080d0b2701090e01060e071b0503040b04030b070806030d270e0610090807030222020703030e160f1701060803030106020307050d170f0403050d02070602 73
    0x3681d076440c115803060f4028100344045411500a0400800180d4040b62035000340d005801c0f81c46202c2610301d2428903034030f441d6041c40000c070203a41106040c101d00c0e0b850028100000d1801001c4c4c25003054091030311910200760400594040505004080c00a0000050000c0e00d020b44800400c1103a10030155a210740c1d490642c10f07240c20000701c0d086501038029510f00801035100d10000740742e41d100d81510300c02411110b0300b81c19407580c49070844148404c550b01070219a00c0c05424002c403d403480d00d8480c05450506100e90b49503266440004c0c015042450050151031008403042c0c011401107008544410031030600601800540075035a0090160303151051494030b0b11003440341501c0720740458608413860b0002070307415014408103d00d0389550721000842d028200784015402090076600a684410180c2025410302449198201c184551700809609140d803440c14264440c0d0304141004040d03403581010744492040c1644850924070014845040060359401b41a41d03919a141c2e051080c1203079 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 55861649 1250 55860399 55860421
    0x1b060606041d041704121713090c0201020f03040803040605090c010203040626010806010305010e03030f0c160204022205270a06150c050606030627070f090b09 70
    0x80d026062039080c2c10007030302008620460829070010710a5000318052598518900c440f6000340d0014001c6402030901002406425a104407000c1804c643c0641750001a10241c00e042c180345c81400b141c241c86110010001d0700070740c1500d01090411404681c2da203458940f4800c03583c0111811502c040c50040420100a00004c083c810780c030068006600d09420900151181d402c0480b1111002c01c0c00940001c1f0001d090401c0390090902d030006015a504600d08542034641e00c0302d0000781e40e40705000300300b01c0030203480c406a0014100c00c0241e5440c0c00c0c003a408000c081c00010301030b4209000007820fa012a8000c00200f100c2d10310300401c080381c2c0c3d46400800c19040c0d10060020282c0c0b003410014003100074044401c0c0d4006c1c200c9000025910740d0742012401072101120014007140d1038003007520602000303001080d40943c2c101d02402051415102145504462a8821115850641c1c80f900c0360fa604002c0100a000040401420a9510652240901000c1c3d04d268001c000040114002d20700e0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 55862899 1250 55861649 55861657
    0x1080702120423030703030203031b030411060d021315020f0c15030606040807080a022106010b0d020f0c0a0c120b060405061804060504050c060f18040e031b060606 72
    0x2449a1035490726241080c26400c40780303072043e07003003403045807201c010116a801c1003240001d40c413a401a680b43d1500d080d007000584075030384495805200400c10040003400a44070510481c0003100e24a03202c0d00c0c02c0c0280d4009009480110703202c2201410085941c6030700700740031001d80106908407080a142003008a407a4400c107804690031505200d041e10802d90020040c65121030301415280c109035448042510340545680041c160307402150b40c1000b913003881407481082c1c15401741000000300146040d00c1e99084140318a1440300c00c046540d8107042c6c01c40d011200c1d00340401d0f440a465540150b4a1902c482da4000110344051342c806e4001000880c00340c043c0d040580001400c01d241c3e4809007400090300f0001c020366408000d40110701c60b0403861140d1580554080d00c000209481c051810518042415003080d1244009100d052200301c1d0a60850302c0a21030303504d1000d0100318100114015008a869039a4140004540e0a22580c091075001d00d4680724001103404039210101400b82502c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 55864149 1250 55862899 55862923
    0xe010504020f0604031e03050702090c120c0c0c0d11100503090f0f06070e0d080706050f100b070f1403071b0905130204021309020f040602060906220302150403030b01080702 76
    0x340d8082100c0300300240c4410246c4d4000e00f000f80c904510741c0c0c00160040003c031601352041501007000310740706490f4055070b540006003210b40d81c0f42c04030380325002ea030303c100c552074540c440d540c0b00410724208810664140c940240c040c008400f080f5800c04041c0c05600300700e88040c2c00d40314801c0103c4c0740c89800503100341c40c140014043c0145446001b4200c0d040810031200b00c0e0451030035522000054030010050070100d000302400181d50a00446070b039084980a00007203809a0321070000e11124034040e08882c5c0d0b5a601007886002181c507032406014205000c0242081400046008400d0003003103038009450b1b021400d502c445881d207601d6a801220029689522289070b01c00017a03005041940c018030400d041031150841c0e540d0758141c401c003a41d005000d00c82200702d0100e4108031b0039404003e51030b08154a43c014041c0d80c64552103600085c01c0074951012000c0300c40711030006060007440307414a0303c0762003052008075150904024001e00f0031701800a000640020015040920204a441400c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 55865399 1250 55864149 55864163
    0x15050423150d030809030c06010b07020f10050a030213032a060206040b060409031106010b0a032f030402130e06060906010216140f0d05010e2107060c030905010e010504020f060403 79
    0xb002c42e48007103408640007400140184010041400000b00401c2417500031b124100c04c184e034901c807610500454440681c50300c0d0040c5071069040104603002400d0784c4050700c1a1800586522200c10074020300002c44c0d001900003140c0001208024003c0c0800c0d0a9001d10041e004a83d84d80d00c00041341d490b403048401420680005000c214149803640210907080e000c0c0c5001c0d402c5400b899506400c019082e4809071903110f0000d110003103640c0600400e41d82080c0011b0181141144042d00302030321881d02d454050104001000404542c1e403600390544d08141c0241c10003111030712004899a50906a4046104200c290700003000d41d0710005052100a82c061440002c0500d0030108104410031000469840a880e40ca02c3c0080e03111801250313900750282001154180584032417a05220250086084080c1480d9403403200405000440703640551083d40042c440400b4403080700101a420001860b9508040080140c0300d41500306501640c000c680d0002002070780402c004681c4038038031005240e6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 55866649 1250 55865399 55865419
    0x304030b060105070311011406030d05090a030f031106040303060302130c020d1d18010312030605010512040203011404081e09130b0303040302040e0303010812040e010302041505042315 81
    0x82d4401c1000e400250301c6400c0460070080302030141400e41d900003007103d088600d244204040341c50100040f00e45038080e800d006251407820000b240140c0346c80e000c042c1211009891840c1010302c0b50b08210078041120007595800e040c90721b8000c014241c00c1c44240d210b00607449407000001c41138840c4100040d215001000384201101c0b00f030343c6e609901c0c0d8509911900281c908010380c6c40d060b6042d83c6260341090028800d6042d481c0c40c02c000c1014a2103003040510f09101480580d0f0090700b154210f40485901c0844e41d82c0d00d1000a0145c4901d21110044401a07000d200c01c100b603900c09003171074040104892a1080c481c3d00714041d280503000c2c5959111000c004500c01c401c40c03660001e2010100076040e2031520740c698011900361352100300c644045038400401000103150900403054042c410507110f40c9024a002c41d210b41c400b1041c007010b4815503403142d00c031410b211403c1030300e802000d01500510490190003031940301d0000103c0412143c120342c000050a961510111038080b80e0024001b00c1c43e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 55867899 1250 55866649 55866661
    0x2d0c090709050120030c010c030e0105070807110f0a0317070e06030622020f1b03040e010306020c03160506160e240d0f05041703040507091104030204020403080406110304030b 77
    0xe4121941d043d0214000f010313032541c484407401d100510044144000100d0741444031003005041f100c25400300764050f450042403050302c40e80315a0343c503088655441c1504100303040c40c0c4001d0400051049040403845480943d404160704407802104843c0704000c484400c2c1c0c4c507503006481d680c20400d016540254204006071561419080b603a060700ba0008102c0c010035035400c0e021040341d210060081018801051020f80d0170700340c0d400d807504100e080019500f02403804000e203408034010b000c002c224640101e450424400108256041c88104042c6120704036001e0030015210303103041c1d43c410381d145409555040720501452005280c10400780602d010700d02a4000030509110780004000542000c2000e6081004d490041d440050041174002a56007001c0c50801000402040d80d1240c082d030a00401011500c0482e40c00203c40c115000441c40070050000558544150780000354018030108011080c0252040900181c40441e203c161441f1401c03000181d07a4019884010001c400301c50010300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 55869149 1250 55867899 55867907
    0x601020616020f060a02130b0c0604020d1406070908010c020127020a0506030a06050102100504120c02030f030d0203161e03020904060b071a0f010501202d0c0907090501 74
    0xe54141180b064860400e0f1901420303080c85030944010a08580120300320007640882d0344000000c02c0f42e000082d00e041d0325081055141c4500800c080e110341c100c1c580410601c402e0341c429041c10102c45059a04c0381c0740401005e000c070070490143e407030550720b060480d403056801441503045009000c90794894440005c00a85149461014200d03080308a807240020305468050180d0300039000349501151031810980024076121a4840540e80541480244408118440e5042c04911003138030700140110f01754004a45000e090149903c0e41e48000602e120502000d0360155000c1c3c039103400d00312180c9400800c200c8240c504c02e65a1081c1c00f408001000701240240c3c000d008040010b000481c03920f0b518566000c56411450090b00c0400c2c0140a2150481000d80c519902007102c10b82ca40c225410301c400200045075903280040309940d01038501189940400116043d0b524801d4030158941055800e101080c407510b5a102261207010f41c810382078038003000d10500c90001555180300a0b450100116 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 55870399 1250 55869149 55869181
    0x3030e011410030f0c09090c0806090303040803150301092a0f0f0b0a09030215030a0f051b0c0c04020316020f010614091503070305071d010f0620070609060305010603020306010206 79
    0x201d10f0004201d00041c08001b5000390a80540a801c442c2c40c002e1601240a0402c4002401025981c000308204800542c0340701c29a0340224945030f12550103034100011034010042804060142c08907151510302c8120391491600d030032a1102d105805103541e1742825070000c0498001c80c05626400d510602400e003050300688000200361611203465a501c0e00492441840318a0006488000100b04812030185000b0b43d03100310540300c4200034030701d0040d490580b00c02c04a403082c0321388403000a2041e80380008100480c000c0c5c1005200315031301d0414128000042c1d045400f1140940540307107050320142c4d0184a820100d401804049800d041034030100301c1c180c1c100a08240208002c6921541c80c0d4804012100240d44100d004152243c240302c807540384445c0704141d160030015114010302403007943ca440c00044401e6414000e0f0b000c00c0000300e000c2442d605210340030b000d1040c03880010310383d40c0c8280c4940880e8010344003004145d0300c6007030403000da1200301c44a5025038400f40c0441c10110001c1c041c9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 55871649 1250 55870399 55870403
    0x10e070e180a080a080f0114013006080a0605010b030c04030b061c050705030105090a0323040e0f04110f090403210c022a030613020303040b030403030e011410030f 72
    0x103106100b100d0303a110005a00b2800301100040c0d132031381c200320b0b0240380320b0800d5000d42003008140c51800159000244681c0044928000400300d010029000180f41e0801c520080b481c3e8a05001c002e0300d130410700b42e40c1d056107103060740c0b650b08000c00001c00c0503001089074003c1191840492038117003546c903083d0b00070350050040c980100906658a06419010340950b641e180300328040c0c04202e1a0008260a48001400e0700340290080c8a00c00000703504808020b40d10615034050a12084a10103c40c100e0700443c4c1c09010409211000c01c0740c01c0044000b403034441c0b84100d5941d070a1540300c0007489041200d207080581c2154200d0042408680102039201108503030340080740d03080d50900d052a040c3d404020f0a080580d1040000300410320340c100100341030034003030b041407a90420608002507980102404a4868415101c02c040642d2020300c12140034203107082e07400303070b59040c14903000f4000d261052001a9139440e00310624010f2824440240c02139a070b010490009500b90b498a0304201140942 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 55872899 1250 55871649 55871653
    0x31506070b090a0309050a1d0c210103030311071709040f0609090209010504021306050a0203040f120b0901110315012d1103030705040603091505010f08010e070e18 72
    0x40001c9010568902c10801c040c050301c861501ca240192106980e80c0000c0d00c01c0c1d0b541d1005005840100c503142c49079940714011440c00d901c405031418030f944506400100e1000d00e60048184400850411038101c1c1e20030b680402c201c0381040807103000344c011104d00400c2600c1c00006e440f80011914003801068400410020702401742207618030132201c00f980b10407207154071000e8000652421051540c01080c0556045d0b1500390294100240c030b40390f6000d968148000401d04480e07151003002a28060302c4003100304480e1544809014088110f041e50441e246105400003c00c160b40600440c8245981690321906688a0102c1419020440b00c0fa0700e0400505480d459901c904155100b0061607251f002810f0341440030700000c01a1010f1034090000d9070040040c00700700c40d030110460b01280c40034503000402c500c0c2840c03c60005403000980c040701d02d00f09000800c03486100541038040300c0c074000003088003010405e62a80c4451403841400038110031280010318808410203156814094881 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 55874149 1250 55872899 55872907
    0x903010209040518010c030b0603060409051006080319050a080106120b0303030412080606070f0213020c1e0d091d09010914030901030623040e030c030d02130515031506 74
    0x8241240e8049407a08401000c9540c002182402841172005402c0300d440c090103030320000002704020340310141049026940e2000c00505200040c1700c6108129821201406070a0703540c8151a582c2d0480b2062001408140d03003804a103d004400310350b928550382d1500c1902e42e01e003d40646104150b101c00f08402c035201c900350a4a6502030000310312403403080001411000207001b0082c0707100350050005008800411071600403400352400040c61503030480d44d8036280400001c8032006409402c100c200c0c90f1190910380d0400308541001515940700c9481140e041c00003800048883c1042403084c1408812111010101030224110311507000c6810000400d05c0761285d03644c2e6a003e50564002400c0c4c0d08040b802040c03560341402944000c049010540e04807101c0b060036850704800c0c20144074031403941ea050020840c002170041e034500007101410380c1d803140c1003103010740081e500c40c070340d4140240d0225402040302d00c2c24482800412912203109400c2da40c42c90605d51003d41c0031042544e016100340 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 55875399 1250 55874149 55874167
    0xa06110c010204060c060c1112070201030f09060e10020406091206060308041d0604090309060305060a050910030506100803030613110403032001091203020915040305030a091707060509030102 84
    0x40014801131030141c1c2da1031150229424540c080b943d81001e81d1080001c25850f6440b10b1100091540038406c00c141c01d1952560240b00580003804241c80c0e5120a0f0f003000e2a203414003001f0381c021201c40810343e0940d0302c0403030034034200340032442030340103003404249000014407400249401d000302c941c0c4107a000041e000e07181d440300c600c10340055019125848404050700358402c0a29a1150000c500350f50521003c1c1156401030803008082c00760200b0036584500081300c0780d5403070458900519000d424029103003003580500c01c100000780410b5030a84201702c041026008508a180221180c01028508503240c81d030402c0346e03884641030620301094480d08010700c0c1035461001080114441e450341c00d0170800301c07240e4184e5100c00c864020b421342d25080341440030610400901503906007902d00180e441580c43e0003d80c141316000030302c29407140081404000c024000004000c42003454179840b106660f1050b20341c8009a8501c4040090b07004241c0c00c0140302e0059026140b20803005002504202e01c003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 55876649 1250 55875399 55875401
    0x30a080705071a0708030c0a201011090a1707090f050105010e090906010506031e0406090501050105090106020703031202040e070e01030b01030b15070203010608060c04050406050906030a06110c01 86
    0x35034800d50781030b04418000c0100c283d109940a45050103d101d5a0400c400383d2264038060200031702c213504880000840042c0c6d02c1c0b2401040044000031503501c61260540710341142e0310744400c0c40310030566140139205900c00c00d1903401e0340d038000030040c5821401c03070030001c40c510700300000c07821403215101d5031030b02140f26400b500079040b00c10180d56001401e58136040005040e0200c0f00e0740d1600960000040c00318044010070060b054903000c0e1039082ea2034960b8007003064078584002d501028150b1041c01d1204002203504038410032400750000340440d13601c035010840001001c0c17080c100560b1015008000181c06031304140032000c0c40c13520040c2401c3d81c07640000e002c44011030301d590009115814002c0151381620410000e46020301c1c0400000b407065002c030341e00036506103c03070034035160110780e5204540e400d40042d005040c040b000e451450901340f813000c4160704140299481641410008501410260242c80c0306400003030003000110402d0b29004020139402b8000c04c2100002c1105032036440342 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 55877899 1250 55876649 55876657
    0x11112010b21131208010e13050c060a0507150203010509010303080606071202030901030c0206060121090203070608160201090209220c12050709020c120f091503010806090c0105030a0b030a08 84
    0x1d540c1e050f6403820303807516211488181c0c0c0000402071260290050100151811189600c1042c559200c072000c00241000c51425503040c11041c1c0c0401d00140000950741d002d8043c0407c0c070311400051b054400c50246d080c090f40824000c090700402401e00400c0402c0c40b0303045481d00304001829061400300c0d5521a10f410984c1041c00e140940d100140701c107101c3d6031600c1910b0f80e040c20341c03015102c01d0070004002442000c100380941c030000b403600f00103000e821440d481140c0e0180d004088405136a076940d805400b80d0340c100c0344441075a00581c003d6001074018040c882e46958014203428023583c0310104146413941e4128408401c2001050f8000000c1c40840c0344000380024042c01c1c0505011440d040e850111180c224014490044c01155410800014080e916040324004642c0351200c41e2218011401013004141d480343e40d05c41c08109070340b6000007d605850105094484c0c0d503903000b420743da0318001240a90300040b000c000241c0d002c1d69550000c0f002080040503030b400100c50780c640c10340e103400c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 55879149 1250 55877899 55877911
    0x110d0308090f070302010905010e06190917071d04080c0604050102130807050609010c0516030303151509030204020318100501060201180308012106020d05060102011112010b21 77
    0x11242071001c03284041120558030001c040080c075003035007907500003048401c0342e102d441d060018090001c1c0b00340e46c1c0c02d010360703880e407003d210782e03e4080100103c020918851440348500611203044014440600450301c0c1c01030300d0000340e1180c95603800c800d018900c5100100142e444200c1404441d24082080c80450b01a600420015880351171034142c801e0300c910241e11240080d0b011040401c059240e510079030360f04143c00d003030882c15503100781012414511800c0213101d400c00c01c2c2c6004000c041c1c02d0f034040351812a124500340b032000e80b20028100782e800e42c80141c0e80412000801040140713810340055900001c001041d601d0401004e40310752030080b5940c580380702c441e110401485610360910a08100080303440a417180035945803809010500180504402e0000103484400c035294621000700456038822000c6584d911500309480007090155040d034015400d2001000c980c003480d07000d80d1023072003c0c185807059503441c18401e24010b910052100c40405001c2c0742404103004c3c44104144104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 55880399 1250 55879149 55879157
    0x7032a090923030414040b18040b01030b070302030c1e0c0d05030108060705070b04030c02180408031005060301050f090405010b04050c07151404231b010905030c0f0d110d03 76
    0x2c141410008400350401e90b80c980300c3d4014041000003400b42c2011240600080e20000350001011313000c22221511106446244d48040b0b061104024668003a14101c0703018046004842e02d034850304030b0980c0703c240d5418410b03901c06d015020003400d948c1c500d00802c0f540b8000c0145000c0c40002c00b1070600741103070246808200302100400286005102e0a64842214540607260001d10b555a000004000e40080c08114035503201008644540b102500d40100d010260004e40c40c141ca0324071602e0780101c4503243e90740f600704000034840c00c020007603a040e1900109a50346070284035040c4418854000e00c151341c40e40d02c034858100540c9441c8200341c040c1c4120300065030356903080c2c20a03096121895410a00c0c89161240c005c0300101c00f0802290071540c0001c042d044560180190115a288988010042d00030f21000040030300b24042180701410080e294184080da03a00d04050702d566420000b0b6400562155400055251480951280728071501d041c40d01c070300c0c052000ca9200703188403030128041 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 55881649 1250 55880399 55880423
    0x819061205070506090a0b031902040b1b06040206191806050702150306090a050403030b12061e090307081c0c0309032a0602030c0919050109060207032a0909 69
    0x111105220b00307009010180e901615000c040c0c1d010030411844d41c4110090030b1030101c04100e0407042c42d503203081010301e5640300b9900ca988440b00c41c01c103a80907500700541c80d45000e11031f00d01103d0100e42140300d617070001d09032410110308010440c402140f00001e94100445031003c0b0b10301f400d6400010010300411798444e03032506c40a1042c424400344250000c101303e40c00707108203c000c0d030b507c11000c1e9101c03041840204a50f2a20314050f8081c00f640c41d405684010514141161880300244092040c04030020f003a4400324081b00e001c10b0b580701640c21b2103841e00100400710209200382c1c0242000340064541b1030b0203e0801c0d007400d0071601750088080000e0348481000013413603030001c01d0b003921182085029900700742d018141d40d03031548504001041990003100240e5034021600964444020250400001201c400340c05600718400b805070502184616a010079000e1000035050180da600004c24400003003500e0000550803444208044116106480400c219215000d0071900c2c620407070b845600 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 55882899 1250 55881649 55881653
    0x140f090103110a0e1311010504050d030e031903050708130b0a080a05070f0c030e040f0603080c06010b070c06110307020d050f07080d0509040518010e0a06050601051908190612 77
    0x1001c400e076200e420b4482d1941d0500c00101120480c00c070002d86d0200a980c1c840f450040140ca19028540c031072036200d401e40c1c00190078503130401e140380c3c010b0f8000c030140c3d404110800c81c4e81c404243d02c464003038005a024084000003030220001440511380c0041c13451102586c40c0d130280865480001000000703299607041c00321060045c003800d500b14240c0e040540302e004441c640141140034800014040149156000c6465101ea51040c2c4000780100c0b402e11186072030741003c1c0c00b140d02c0b280110302144110400084d0740d004c00030960384144d030311204280905240803421100e08404401c4045540000c00c80c4800580c3c4003c6100543c030b01c10030240c0200303000e401006090003215480076889070003550f504018190301000316050300404850000d4203464000b241d19112051131007000c080d40c60030104d400700010000c3c2040358984600010b02440c1d40702001103a10b401010100a8103000d040b5074040c40d01d0040c20705d2a4403d5658000c01d03441144108170205903481d9500c4400d14600d10140142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 55884149 1250 55882899 55882909
    0x30105070c030f0e090a0911030618060f0f0408030406020405130603021e150a020f01020a02070e010609050604030204111612020c041a040203040f21120506010207140f09010311 78
    0x714895450404d100d074194204003081001c60010100000e442c2d44640b03807000c10550b100032050ba840040c2c11181c091401a080c203000d203000c1070700c1d80424814a00001c4041c048007070102d114008040c40c4c84801d454680c0ca03045603400c090411205941c00b8000400d05d40c9a41d0075a1080004506000c58aa4514018003600c2e490080300041808481d03000d0640320780b21940d5156050008a0550b650f0303a454510807402c001d100b80707011509500002d440d0024030390001d0f45206840000e0b2015140d030740d907000c4c00d44242e101c601c50036800040502c030030005850140e00c001090075800203c036103020240806c0380c183c6804200d041380d502c1c55040c000c59221b581041515500d200030b0b0340402019117074051084007050001c036001e00c03072900080003600304038201a8070b40c00b0769402a030085120116500310900e54850b07403c0c98000a84c90700b08441842841c0c003989000350780680103049514144070f840d078100440030011039004421003030050403135210036503013500030750096040b0180c4400303a9003007007 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 55885399 1250 55884149 55884167
    0x1205040311120c090a14010305010203010e131208070c080304060c0206010816051203040305071d131a04060219030b0405070504060f050c010906020c240106090b0904060302030105070c03 82
    0x42c001c02e0b14002d10305842c030000a1101ea050300495561481d96103003203000000e0200d00e224943ca90320040000800c010054000d141030700c94080320052aa07460b0440100304c0d04132a035016001102c1c0c8074415101c0c500480c03089800059501c1c0280c03803120640c5400c04207a0048e40d080b82c28a94440d03821459950520400b400f400d002030107460031221650010100940900400348076200300c18844e10002c1040045a001315480000d450170a941d455a680310441140191109030700e600b000a066070340000d040100d000e920401103008040f0a031200c080384040100304445081c1e081040341404030380d8846035044045290f0b40400c0550002082c0410307207001420050a216050000788075040c0c1041da621004283c0345011038031484c4c0d070a500b50160000c0c2c0d070040c0c0b01314400210041595000320303001035001100b4400d004a041c00700654001d100c002d11507080014105201402240d215100400d400000148049901500c1e500040d084840c1643c04102240310394400204041d0081030380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 55886649 1250 55885399 55885433
    0xf2601050c0403150e0a0b04060c140301060302090f1504050312090a17031c060501110d0801060f0507021e1c0201080403113c03040f050f030a12050403 67
    0x28445428030700840601030042c0d000c010884080084c1c01e000e410760075401003c0d08201402190000c0c40ca504128410003015102a10290704202d03002c41c015026441c1a02d840c1c46403052039246030710700b1204400a40005000b40e50100450049840507174030408006480c80c004294541d4807403402040510300b000d65400d00c0c1c03c850042c0f144c58502d540c3c07440c2610840340ca40840802406500c05032608521440d41e0058a6200094590b0305100d0303240e0103001501e000707883d041d8a54042c0101566951210404040080c1026005200d4144146544181d14110741011420700c4944e50000c0d5003400399000b1103038001c0201c00c101d00b4a140003110001d02c40d1000055402d9036100b900020b01c103510042000d0f091054013a04030f0540d8404202404240c0d05085000400344503d040c01040c2c0d00314034031504015005601004420341000c170440c0d007215120812241c209103000207204040c0011890b07180c0c1030141c0344080f404102030b4448030301e0801c1c02c1c0d551650750300e0079494021621540e100c04 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 55887899 1250 55886649 55886651
    0xe070f03020303091c08040e07031d060a1808071209060f020307021507050f0a0201030c09080a1101050f13080d0507110904060b030307110a0e061311040f2601 70
    0x10400168030044111000310b42c0c2a194402850000001d281c2c40e4051104000c0c12006d0004002406003c60003582c0d009024507a0140200070b12003696884036400b50071240e103141c0240740801c0a242039030f8030814010080d0200700c0407030030384c9440e6041250030908090782c62140780d450788454154041c1c4100040c1155082c07000114605c3c0c20025680d000d00c40009004007030300700d48080f040d400d842c1694075040d0300c60100c90449040004140d11b5044425040340401d0812550350030341341c02090407000b41e9542400921925000d40c68850034880700d1204241484800c00c040c0d4050f02400c1c008007404102a540780d0011071600400e01c2c9004074030541c0208121040c01042d001444110b5589000c041c02c0324004101d40300ca080540c010b000da95499a89880000749078810019400100d40b0421021a00205629a20728076910056411074405503c401803404204803000164004d81c002001c04040504158640b2414980411942c0003148800c0c0e13440030300c544250280089090791890140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 55889149 1250 55887899 55887929
    0x140303030c070b100f030501200f070609020d3014030711070e01080a030e030105040b0402010f090905010303110d140912030c0d0e100305040201050702010509030a0c06030e07 77
    0x700d200c000d4000c20b60010008041e410100c0c111003151608079001c1c0c080a80c442101316a01e00e0283e00074444601140103030101242c1c451a80c0314007400b950114110840c959207441c2c640e81d103210052052900403a8000d402d10700380d0000c0b07440f0303041441c4540d603560100400720043c1a0481c0c481c0d207201d00c140303040200c0009200308030300c2d4900c281c94020300d41c0d04201034030080000d10503041c10119048030134248100800026007400010704c0800c110f000345c5480569032510300605007038030b1085070003034250700344c0c00007260041d441f45241704c50f841d00e140380031184280c50303500300700c280c40085c2d00a40024100580c501e03010700c81400341040f6894141441404a0380300c0761520214028022028851442c0d0000344124000074400c8401e0301c41d11500b5218a403140c0740300940341201000106008021504d0440c3c807250184c4201c500590f0143c4641f414824194011143e603400000c080d1740500588901600286d407440000c2c01800e81920045404540392403d03e04e040300d070b544016036010400e4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 55890399 1250 55889149 55889161
    0x7021905030a08060f04050405100e030c0607051b0709050411060c0d0f0302070b0c0a02120304030c060515060d09020306061903020d060e1609060902030c1602040b0d08030114030303 80
    0x4482d0080020304000c0010369440780011070140ca0210075981150503c020481007000c00b195414099442440c03c010803a0010210307030340d901620030807501c1076001ca4042034071540504007401d4815114050250408540c420443c20010654800c203941c81c1c40c0d00502040080382900c0700240301c82070f81d4940c201304002c2d82c0d01e82d5642440f0108000c0c8103080b248000350781d1007034040302c96842d004a0606c510f0b0508102041d01c540c054205c00005005182c15120032518003401c07240a0307a0140d46d050030b0b29840703443d45002820064850b03e40703c0c00442d0070151a03100e110141c842c40c6004040014942d40500515041c18001811140b240c4886440b07100f21110414009003a48d070140c1e6200303400001840e00b00d0041400034003440031885603c0100030f071039524000e02c1d019a03030b9800c410b02880d551020719600b0390100341c400f99410001071007083d810106001c040507185000900204054040c1030109003445407820342503c164000000500901002502c980284a4150001d43c694a046 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 55891649 1250 55890399 55890403
    0x30f100203240d02241602190303050d02030703020403060c0503100b09010504170304090905030319020913020a020106030c090b04050903070308130302120a3204120302030d0f0507021905 82
    0x2c200074401c08989116101851510288440307065540550325920b1951946c04111940010130480c8200740c11181d01c01480805200c4000300e983c1511303028201038404403081c02a4200a0240c42015828080000814614020101e084070641c07541540d90410032410441441c55800c04140d200c0200b2826203c0d90b40304084400300c0320900b103042c0d821442452458254440c503400001d03858100041c2100b441030103c0151b020f0300d08000c98100c907000011036201680240002c942c0e010b003020007020041e5a41e500180340e41c4071603200008a0b541c680c0c0d0b404100d9112034200c1034a42d80c0d07581c151a12400c0a2180383e4010400000450400c40e041c2d03001403812030010011420000b5130101c0f001010300800540e49810380401000340c6810399894020500441420070481000040e401c01c81c88e542d540c51464110a00441c0682c9440c0c00e00d20a079000301726200c401c07011840100302114464415105030010500b071514041502e040c0300a0092030650351840b038503021286e0720f41c075100242c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 55892899 1250 55891649 55891669
    0x606030a0c090b040b12030307080915060603040f0b0c090312040338040b0f070e0a1a0408010603060902010e0a0f050d080d090302070305010c090501080a0506030f10020324 76
    0x10300d80c03003c0f50406154001c50302400c5c050418a42080761603004c0750041101001031807241c105540e80c400c140e9a50040d5503521103520106261025070744012a460f410120025039100d40100c89801c9030030305581d41c02c054000c1c1101d0640241c0404a00c404030341ca0123100701450f100d504520a41403034296241c240012504080c0440c0100141000400c50b207052104080d00e41c004100400032841d1904054030290f1048130000005003c070b01c0005d10a600560702d031189500042c1c000c40c0b590781440307045c2c040b10710742d110b01c03070641c40c1c06020000741240c0074000e540280d0710aa1001c40d4010681c4005040c0034070081c1281e100e9507010509000200750960740d0022980d0464141300301c00c100707007403180d800d2150290060001d401c101781501807640020302803085910900c020410001d100c1c40845021809004080c0006c07403802c04142c0c0c0442c1c54001c80e03000b5200070161038241c00305042042c81c0141054550425907004020001c840341c2080e0001d950900b02e04d100056044003c000403c0d030b1076 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 55894149 1250 55892899 55892909
    0x30e03040e040302010902030604080703140c0c090702030c0111070605090c010c0327061107080102030c0d0203040501240612020315130f0501090906051303020c211b030606030a0c 79
    0x448803000405142c402d41005101ba9006400d54102e8105410101c0050780085400d0300415940c0100f03900805d010170480f00300d6001280500448640700040150040b00a01036404511060145101106080c8940351240c5000e60b101c0d65075124514000007520401000348038990840b42c0103503e540d0b048511000786a62625040800c00b0207030081d0420301c901d0407001248030070001c40100303089402c20800e021000d0454201d81031700b5500d80d00c4c90300b41e12007100c030001c9800701400400c00c0c6c2e038540c1d0003942d0403c0c0b10390004280e5410f14001c0d5800700d4000840000d404100b454208542600320003442a01c00351700341300b0b516618000c410b0050302201c46d100d09000301e00ca6407282c542070205510a02c0c030025010424025940e468007a00c002d0129294180c2e401441c060209004407d40c0e90b030300c8030f21540350b000760070800c0d200803c2218140c064400c41c046850018200091000148003421b1002c42c000c034903404042080040c107250000050109000f540003066883c00b090341403000b041294 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 55895399 1250 55894149 55894169
    0x12030403090b13030c06120f05010522060506210702070302010206010b070311120901030c0503040b011505040801020a080a05010e2502070b0f03010312080c04051003090503030f0115030e0304 84
    0x8510070341408028043e69101030862005010007060f5564026560000f60494420078400540088a40740445400384601980300b00e60807500071081d841002440c140e56188103000038031a65400100305207a1013551101c194080000c034030700654a4800c40e0a421100324802481c1031410343e030010799201c006001c2c0148040022074031070b0030548201d00035042e814030001178030300d21407440c04120b46a42202c1d0009022a060454001c850b0f0301c41c0090b01e20450300b103500c00c040d03039191881d101c41e20701c8030072a09400c0010400c00840c040400f40018202508299034040c1e131841c180c0303902000c5501c1a000003101c2c0349030409100428204031071110402820000031140d0f9500064140e280401c0c0c1c0d40000c15418002c500050142c06107c081d504907806159900808580a2421100b414044a41c6017403440180424455414815401041e4440f54140050b03803036501d1b02d42901d580c008a0360807845501d00c1c00140100309a07048d42410149803800c3c00d00c44406017940c0c00e80c507401140510340040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 55896649 1250 55895399 55895407
    0x506041104091209031415130309030c060507050625030b0f210c060301080304060305100306020301120309050613050f0310020a1806021903051809090c0312030403090b 74
    0x1607950707902284426900c10010040c0c144080c0c0007403d5a0750a10060b9042d9016903240200c2100100d800ca41071180403001c44034950ba9410240a9058414410b9041210713941c0080001059050414081c0c002d94540d1515039402e403900d07030f1030a80c0060042c14059400c2d10f011b01c21300c1104c01510b03014029414007040700c0344094080307a080c048406c0096800700315000514001c9403403c01121480003d20b0549030125140e000b0f006103481b080c403556040e03900400c020007120388242d0000780c0184008500c25446d039542c0e11204141d0704280c02640c8030014551182c0105508120010000e00003620001d041c8840081504080300d200d200e00d0b1300510002ca007103400ea40e828404000d12032080715046480b148042c90003040d00109000c0303040000140c250100d6201e00000307180d802c60840710741040301008aa50110356582141514004400841b11144501c0e91003a00c10f0713100b00f42c4040108444a2200101485d1608542d4104417521040082c400440e80c00b01808064403101c0e1149a61 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 55897899 1250 55896649 55896683
    0x12150d02010e010c11150c0c03060606091201110304110f010c1e1104020c0114180318010c0f060c0e01030504080301030204020a050f040e01053606010509090c030105010912050604 79
    0x210001c042221741d805080d16000703003800800c6601030801c00600f0400c4488182c100d0007416660001a100d03207521200c203000d891001d143c0032125008a040a82c008a041140c16840102070b41041d1011103000c2e0f28042d52907a5414203100c140103900e02440c00400e044007548540304803209041d00034950300640300c018420300c940506500710503d00a00115920081c41d03030b08a00800c050494031703111280c3c00000c00c04c110540c094601510b002940514070f05003e007400c021101548404030b1b814084030240c4400418005448040719170f0141c1c60102c0c4140004600030154013942c0d0410f418540342030103100202d401d8a05903415258141d42c01a03840b124000251494090b040d8120f0394004000340104405c0f1854481d21b040381c0c820b80340101108442c0c214500700c9000821070b11200002203002c1101e280c5074040b45600150181440c17403806141102281e075002d81256040301c84000040100010f59003c19080c00801c0303e88030b01c07411615241e070340648400b4040d001910580e0711001c1e50300 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 55899149 1250 55897899 55897913
    0xc02010605060d050a060f0303020d0c0201030b060706050a0f060602070b03090a0b0405010902031c12271110020c061603030f050103240614090901060b12150d02010e010c 75
    0x500401082c850f150314402d4507000c003400d0308503a5468950304041d0005584011121400d0076a50b040c0c025040702c0b404560700707d40e45150036400b6410103403101e58080258a5010091040c00c0c0a4103010826150034100c207019614101621248546030040c204100d61b03000c507104003505c28031a5215540d84410712411b2800002c1c08000d0a40c14940050008210b0150701c0350f46010b10a4083c0d400e21001002d141c82c1307410070300382c401d408641c40c154441c082020a0b44100c4004014446281360212020380444e9481d0202c641240d00c0c075003c00b4202401c0c508000d1241241c0140d20041c1070240c50175002c0751841c0180c46503100e8249983e0114001c0502070b8002d445002c1d0010810030032076949003031401080031320300034036118418507500244c1c1e40350f070030b00880c010b0b903105040301e03100142d1302c206004c049000100340038010b5580360004194040d40318005d150b0074400310031480b079600307120b05c842c0750011f0010b440740e10407122038400c080140d810a40d1403100346424204003108400c1820246 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 55900399 1250 55899149 55899161
    0x914010c051509030c0d0c0c03060b12060a090302060c09240405040903050301060810030506130203031207090810020a02070509060418060204140406180c0c050703080318010b0d02040c0201 83
    0x10142d24410802c0381500f0000701522511002d04111404c03928082c4050707580302e070007100142102c10303004010b0010501c181c10011210401030454000d01c000000d01c1828058141c840c8000d25480302901014194100708050300058240c00d00e42c60403204800003038000c09100e0105c41d1440e0748000c0c410940000c2e100355002084050403e129108943c81d0050042e8424051600070941c03004c08200c112024139102401c0d00ea2000c0140840d84230f140f04810341c6220094100d80c541310801c2a185020b01d003071100d41c0140500d803245142207003405015400c1003818a04850014418461200303076690000300782044600c142c62182c4c00c0d4aa00300418045c284980a0413505020880c10b5001c110a0740e00900c00c907604a1104c6081c1c46901080100f81c2d8010721130600484010400c62400401d40d61007540501d8541c00c1401000c1000d5541d14202519540183c0e10200702208200c16410602d003c101034070420002000b1484103440010380d001c425201c00380c065596000441c0c1400d0007540f240c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 55901649 1250 55900399 55900423
    0x70f15291215090a14060601020703030e0604030213020703092c1305030307020c040c090308030610090806071e0306051c08040b040f03060e010504050607080604020702040c080709060914010c05 85
    0x80b10b0600d00740706807940d118071a400450340401c0b440e0801e12003440100e02d1500480059024010951039600d040703d000401c0c1800c180d10103c100000401a80e611034545d90813100e00101684881490401410001285d400b0381914038000c0840802c1041c054060f80e0040080010015151104150038030040300e00e035001040b83c0b02c000b0a00154a400141e00a4135180440702841202c100400840741c4958521000f482c07a1001d1011410301d00d8060041300b42116a4500083d2481d505ca0600f0700c1c1c15002c3d55080c0200b1000300f04040d80b0b80515911a21205a504052040d9460100400c13040c21108a80481400c40361340c0c40310410500744122401000304d40c034400e44840c0c0f80c4807076004001c29840b08480341480c0c810000043d800c18000e1502c256003050107040e5682c0c1e261415101c006004100c5580140d080010070b00503610f40c4111084903032159205102132030f000744003510304171300e40c0c0102c0e091200c0d002c0100842105054440c001803800c0c40c001800750443e2030720504e0000c12041e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 55902899 1250 55901649 55901683
    0x40f1a0d110306090114240f04032006161203140a0c02070e09030421050102030408030406050f040c09020904020c060c090112020f0a1103070f152912 66
    0x45001c5145481c0c001d1805420111080030b1180d9039207680709050041e043c082a0040300100101603008070605084080481217140c00e40b401c45120030102c460750268000315003034170019000c128540f940311410841c10798140e42480c0303094036401ea864501d841d146c000403d14003402c4d0740705040d030f44680c01000c8214400c04196865007002c48050025201e040313080401441000400203810040c4851140686540c030302035481d00e0705000d990a204003080a1400b5010b070307040344c40b000150003440110310030b81c0038040c1c03035480341098509403040c1c0760050f0000481c40600024400403e00c0383c4020000c6688101f40140e0703a150340300c04980039000365400b00c0007502401e0200070a0801950041220031000d03600c0a0741140400175200480c003030010b049048050600c0940320660060344110710b104086c1d400c8030304100d100d507a0500c9029548a040380c0341081442004540c0d5418040e0b82c41e5003100744002c42540c1c5c940b40380b0070b0241ea002c80703041c0d21600d040c0da6410120042800041350b02011041 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 55904149 1250 55902899 55902911
    0x3070b0306040b09040b0a0f0b130507140a050a0806030a030822050a050109140304150503131e021c051005040206070b010308030403020c0d020612220614070203040f1a0d 75
    0x100a1512801210346c0101c7c6d50030300543c421840110f02c191030346501d0050001642c2d1030369071903540050000400380e43c14040c1c105400e91520701d0300405401c44034500d070b88440d510501810020003000010f02402e00070303404050044c001035000080707242d11990b282004413222034141c01e0401b5042c140b0102910340d00800d810901400707810f40010300000e010740380ea10f820368503c4102d2a80c0348540d1051211b0032525005541e0030078400c0000395000724008070030390f524a086458403602701d0062480790b2485042981c4960460501d940e9080c038541c102d02d801d104841140e21047d481e055050741d40c044c2c41c0c1c1e8400c00901103655100079540304c0341d00f1824846156849140c041c819610a2740c0a80140c4640750f941c542502d03210035100e1900d0350107003280c3d0800e444820701626110002d13141140b190003412100e0840385001507100c150701d00500380420801c000c45a46800c4480c007034010f1381103400030841400741c4840f120f01c12046030a44685c07a540c0c3c20b00c00c14120428064101c0040000381450 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 55905399 1250 55904149 55904153
    0x1b06050402010e0a181122081504050d0f0c020a08160503010c141605070f0603060905010b09090402040b031c030e060c0306010c030314190b01081b070501060f09050405070605030603070b0306040b0904 88
    0x55094080d5a008c070300310f822164240d50840f0844104aa000704560f000b2080c110405100780340c0c825809011b428030b9120343d42c550380050108901c5412500c2d007648401c0c40e0402c5080030b044540000c02c4150020000146000b60090007a465506e0781c184207800020300562020307504013529005900030040e0b445a9031108480b0411150324480d800c0040e084c00c40129000002d440f403a41212001911079140c074680d0000d0000a02c0c4c010010b90740242d07600403940e0b582e2018000c081000000c030031605d441d048424000b4080f07565242450035241e1082c81041044c01100d002c0300d0300b18509081043c000b0b409440c040700640050060705030519040c9092003100b000001350800182034501c800d0018407080300046502070f600711600041442907016500305841e18500400c64580603100109a554998100341e880c41c1c82c60380701c850031550f07403000c00c000c0c48070501581018060740c0c602103113103081280029a8500a901030100d05010000108005680e03e9024922035200034046c5217142c0380ca4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 55906649 1250 55905399 55905457
    0x1e06070b0a0506150f07150f05010e160c0b040206070f06020424050c0a020405090102090a0e25020d05031e0403030f0b010201060302010804080a1b06050402010e0a1811 74
    0x6807002401001c600c0014134801c0032620a075240805008222424000d99803240d004003441d41e540f207482160348002d510f200030685c1c010359002c0c0c0240c035001d00300c5080c00f44010709004d020303200780c204202c4441003910000c2e42c2c3c0001c41d90095012501d03075458442e07904008088071007409004040358070014001500072030f00711000580101c0802ea4101ca40c14002e0243c44520910003540c215810903020500145041e0b408a50402c40040c0018140f01d0000040f03407800c01c8a070000100064032808014070050080b86100c01400452224903605164040103542c0d40148203000f41400400b2002504185c0c45920342d41c446d40541001c12600d0801d4140500105085003090107540e0030f24141c40c074194014020002120340c11b96078a24150348075125030940b504180b10b200c04100d04507925500c22840b04105011182c003d200c00a5181028030015000c41c0c3e8210106000b41101601000a11100c84185407042c21010000c641c000c00020811010b100310003800001900040b640003000c995 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 55907899 1250 55906649 55906651
    0x909070306060801170c0909011b0801050a1e090207021305040305030a24060507080c010501030b0f0603190f030201060b0a021609090c03020d030c061b0e010c021e06070b0a05 77
    0x106840d140c00c0759888074580082516041c845c034216030310034036a08070f990a118616580c0b08c4809400001e1138180c5104903024007114500e0034000418090040c06039150500301c0500401c942549407480101740c0c50560b03002c25451145c007148503070109410b425511052440e480b1101d8915040000b46040c0c41c2c058010780040d20201c09807450301c1240031030722880b01d00e0101e0f0300d40c06401c020701503450424100d960f544428012540c40d0818441401511000d00545010303601c075040e002501d01c1c01c1c02244924030030044c03041d40700b50310201100c01010080c150718140c00d42c001e505441880480e0605a016101c580c0c80040420b400107400302c02550701003441680c01c8142142c40d910b095031b85c40780d10305075000d002000e0116500407030100018035209a000c00551300c81d080121104103580c41c1ca43c111130a0f00d8445018448284409008540c0f0000141115a09003000c040207413458011450030494040c0494403c142c0004503c0035075203501c10359448550005105605280c802d0310300303002e000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 55909149 1250 55907899 55907909
    0xd0b070f080603060c0c0708070b04150203071e080c150a0e010e0309040c02070e10030c05271e100e0f0405150604020706020a11160e010306020c01020909070306 71
    0x803181041440d540d101e0507859000b060300070000c00c3d040d20f680c00542c00c40e9020380317a984910300c2000030000300c0480900505004085800c1319a40722458550706040701c1c18107200c8401150000c20040001642c842180454000c4088d00050242c00604c1c00d02410710032182d03441d48910543d00e06001502d4031202180c4205d040b0712041c04810340c0c94031070b18245c4150403071440341c68201f4000042e07107040a5011250789100c40c81241d144a41c0d4600c80320042905039240c1a590500d40c006205001010b02c0c01001807405580002c183c0700450b07201c100039245603010480ea640d44c0004150b2032a5048160400c401c0d03c0e180e00314950401c9005031004000900c101b0040c070103410001051000c03841696031182d904078000c1c1c1040d082002102c1301040b4001c0501d03511503800d11284021407060720240107074052903102da18007042c0344403440c0d14010239180581640440d06800b4401e1503800c20321076045a074441c90258951004240d030b940079019507100140c01040c9a41000322031a13040e0081c804823a = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 55910399 1250 55909149 55909157
    0x504081b040e0c09040611040f0303020c01140f0318030c0106090218030705091603150602010905010b0f0d0807150e030a080108030f0406080405070306060b090906030c010c0f08090d0b07 82
    0x2414480d040d0f20b448640700303850790008205001801003541c07a0454104071400c3c80c3c06500d8a602c0f9081c1c8036098a2542051f80164001c1a0102c25540c21420226015014482d0316040c85660380c3d40e00c00310700c0014008810521001d0720301c1c40e03682d81003003914840003486009100c896140e4055900a4008255602860260b00040304460034042101c80c2501d1014110a00702d81d80c2c0403520701942c3c0b07000041400c060b982c2151960004040301100040d00303495001140b0b40409040c0b890070b44040408941c80340b032228041d1a859503400400c45206a84595030940310451414170150b070328103640140e0002401c00c00c010744000000310080c41da507061522003011990701e4200d125a40d000c0c11382c040007000401c000502000d40201c00c0705500500c14402c40b200701c2c1c0c40c0e0760781c18260384c021750003840e80039000719204289240c80e104172603024505400509007068500002032010a0502d40035280c9546050200184980d01003144c10000014241c0034a80055182456440b02d08885031000a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 55911649 1250 55910399 55910411
    0x1030f06080312180d0e100f120903050f03180d090f0512031c02031e0405060109110c1606171006080702100e0f0c0d03050409020a0504081b04 63
    0x101440e10409080e920780900460038152086441c0480c164081c1c4544208807a1200e0280d032090100103806a40702d19a54a40c0e80c2540d0b0805c0c0a00e20411500140511454058454185903c01507110741c03944014004940c442c030a0506803440c1c4580c614480c2c02c440c00004000e000554500e00110b203103400c02c100c550a8010b90800c854030900c0703003d911021141c2003001c108514180020030600300c6224240da2521507401d01b52801501c0c0c0d07400c1c0d1304481e6004400c204408610030111420920541956866450195945616080140076000301103036581550a29000c80358251101a42240d040b1404800c4030258600c03050303075900c03e18000520005406848080c0e905119014205000d4000e000e2410400e041c2c1c1d41d034070000e02003011481042d200145180141c042d0342001d001c8440030f440c0c12140c03410481e082c089600341c41ca02070542c00c5021380020358010120350480d0008400140c8542104c01c0031a41d500c155401201d0a00c5000507062201000100501446208840030010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 55912899 1250 55911649 55911671
    0xb0708090f0a020d02040605041410120b0c0a0201090f05150a0207081b16180e010209010903140307020603010e0f07020705030c150c03030708041103060615090d050105090c0103 78
    0x681c910000c250701c60307070b0485416000181003503000340c00301038402071000c82d09036103403408502150b140c0440104400800000d00610001403581071014010a004480c1e03007e03035a0f16407640c80340c4003500c1c00a0f800e000143c1e080c2d4861003940000940c07035000308401d1501c0350710300307000d5036441d581580c140c0868215004500190317410301c204d69446901c00d1110b4102421440010f41d00020358503840c1440c0a41c500842d03803280440320036400f4040c15094404070443c4842154100c03038000c04005040d0b071040001c01150303070304018100100c03030740000c05165800406081ca410340c01050030007034002c080400045401808144807a00c11041c81c46080c9043d03036410801c036501c007014032415801d9080b40c4c1c411481401d0851903003c1c445114481c0c1854900d203c064246103900c111410350006140d1414002000b080c01c001900d60071085004140500f803a40c006001c0a242074a042d13409000000c41c2000c544401914069458000c0001c220615001d04925201e085118146000920b00103240349 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 55914149 1250 55912899 55912903
    0x90608040b0604020304030210050901061809020603190906051501080601020c0a090c0c080412260d0207060e0d020705150712030b010507082a0102090108041b030209040b070809 78
    0x1104a81000c1d2540098641e00203000c001d500262054045001d0000c014241c180d00f8011107004072820400020410300e080e500c0c290005121500404140c2401a00320140c2e944000342c0350444c103001444a55840c1d2503c4030401403c80d140c00400c0700f030500040007a1700071340c0442c2e81c03800f6100307894180d5107540d400012601e80201071180c1fa41700f41a0482400006201e030b101022a90312410408111255908d4500c115007255004030350070001d81d08580b01300b0840c0b4030881e109908040c100c00d050071104018a9203805001c41d21a40e0550226841060007215003250007444e480300c083e2600004008402526107100c5c0c00360a00072102002540ca8081107a422a5090fa0300a031410402e15051101240513003683c001685c10402d05224010114030700100030900da0964040681080721100402000052842d4000d44241d105100842903a604425102d5000c1d40c418644c00c6c079801980310070031542140c0e40029403c54844410001041900c61072580a180c0703546840e041a40d503201700740e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 55915399 1250 55914149 55914151
    0xf01051603030c021203090a12020304120b0c09060714190302060406050606070804090605030709060803070308060a08030703020a0218130f03050d022a01150303080a0603020a0e07090608 82
    0x12003508a0103011102092103648040510003261050f41e607074540303c0d16800910707002603071030940d103400602c00c41d0b040080800c44100c0560050000c0c50a161070040803005180e001a00500382c1143e403000600b8500c2140f046888002009040303e440315068108800e41448100e1400c0c3e1500c01c1c20504010103584480c200d00e0603506034020180ca80d0b840e03880300041d040150505400c0030b005d1001e0300c002402c1c42c0c007a00180040d4100011824500030406240c8841a0b00c01814185469003d1164140120858103213942509060041d5240c0c2404039500d20819885201c0900020900300300701075002c01c0c13801010b80200e0781074940128550004009400c2034541c00d002c0c0c0510585c2e4000102101440804a0b0107410507500382100b031900c4a080e40e20800d054134081501e80c030251010760742021403072180351500008000f19540f640f15491040e10b180009000d00c10f0600000e911099550040c0000d940d000e4141c1229907540c0c9054103078100140c80c0f00c0041804100d000c40c0e0741e44500741103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 55916649 1250 55915399 55915417
    0xd050a05130206160204050f040b010509040309031101120612020301150506090108090f0105070801030b092e06080a08120f060d080a0e0a15020d03020414010e0307090507030603020f0105 82
    0x8001c115003560030003070355a2044489000d21130554a0901c0561745900c41c86108120050000e800303881d140c9400032116005070840c5214130441b07000d000c0441c1e401114101660f5100441618910b01200140c801042401804c0c4607181401004114501c0b0720401c3d00b2510720030303802440000400319170030703c0300c410701e025007504400c0c01c2c00500d03440d40c8620410354001e0311000a95001a508132003c0c0d080d2070045074400041201c6900420401040119240d400700310b0902078001d00b1300c070b0001402c60300c000c800203400285203020700e8a00d0030f80c16840328001b00362240480d000d0018038074040f41daa8100d6020961440c0380540020510070070350090750721446008150009105099175082119000800640301300030b21043c10315081c0e121280948058082807050512420500c40d0091408112440540c200750051008001292050320000004c0c3c0302402d000c0340070315034040420329180307541d40451185424070080c0f140c803d070035034820429a80240d42510004140f000152003600c244068 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 55917899 1250 55916649 55916671
    0x91a0a0311060a0903151a0117010501080606040807030605010501020d020307080405040f0f050702010906051305070e06030307051504020a14010e0909030c100b0301140903040b030a020f0d020d050a05 88
    0x402022890b0503001030181007810700340340d2003890712502c50b050302803c0e52000524540da6500d04018814180c804085c1d12442442d098a0512001030b5000c8110740c1807055606222078407001c503030039135038000075207000e802d107841207614444c0d407400c1820207800c003842540d01502071440c11844072480441201c50300c540103800710380340500c0c00c018400245880440130f00c1e42981d07252000280d041c0c03070203203238000c017407c4c0c2c004030700381e581c508001040b01c0d400ba2071400030300e405616101c0013960100d540002c480d40382800100d1030b926040401c2c21441001b03402440d034042c210828803a03403d0188840d0045009540e00364603582c44440c0300107039991007440702d40130592000140c592803402d601030580c003c0d40c4006503420f05941883c1145003460440e4a40f04460712041c0c5414942000d00c1060001c0a680002000e00d040460840784c407481107006000840320000005000075550743c040b00e01202c0a0200d8583d83d480003568503000f074019144201c802e6082030003056030310655005103809007641c0c40c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 55919149 1250 55917899 55917923
    0x10303051c0b060d0b01020c010302030615031b040f080f0303011a0c07080609010b12010216020d0305120717070f0905100905030304030b04050f07080c09070c0507091a0a03 76
    0x803010a00d1201c81c0550400c4548450940129454040140801e00c00203031021441040280c00a0b060112580d00541014814400c021a80d42d030f100c11919000d00e005c4940d5681e40301d080080340391003e2041007040e40100081c0004000e80c26a164008641049094402184001940340c0e2280b2080c1300780e2400c410001c0080c0c030300e09054001031900512107001c40740d220380c0d40c168072410080200c84540340c0341d55883c0702c80d04a0034482e604900080404000f1807504400721070343c0c0300400c80074001a00640030b0448070b07810903004a003290346000041e00c80703035500e01c1c1c80400200768039440741510b00700704d1010001c2000e1600940c4d00c080031300095152011000d050005109441d03000b000e840007001905a80000e99880c28070080010318050380d003030591850141046407414560350b5140c0c005500c805000c220f041350208a07800800d8007218560b80540703640c24200c0b03007440783d03a002420502420b4000030f0400800c3e8801960102c850400214000603001044444401844080c000142c000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 55920399 1250 55919149 55919167
    0x9030504230405010605030610031112062d010e091003171b030703180806280c0e010207080705060304081b0604150b04051302040902060d022205010801030305 70
    0x180312128824a11a941201010141c0c006416a082a0310803000326000009000d010b05204400301201d4201c1e040034003500700d0303001030800a44691000c14450900c808085071b0070380e4400c818000b0040c040503030304043c800884484110038011407100343c0482c5a03080f44000c0c9040c07014041e48241c048ac1600e8100c40c0c1f56494204d0f43c000c0301d680c4a961034004100c02c0c00d40408420307206d40b0781ea101c0305c020350b1101c5143c81c0141c09120040440100c1c0385180340c0411828000050b4250722940c00b403010070021242c5003501d142c500ea0100500710190520b910b610603260310042980010b10240e0840303020555500466895020b03030b000c0c0580200c1c041001401282d47c5100505400881a1101d00c140c10b88994690070990240c0c0c04981c441407021400041c405140100b0103041021178040125040002e00d520107400240d400a0265072a00c040c0c80956864905951608070b103040203541c0d505200b80c130904854000c005100c034800414001090700d500c5034030f485041e2641912941d103011050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 55921649 1250 55920399 55920419
    0x608060f040b03030d020c06010513052701090c08030a030f060605040509180703030507141501120f0c12200906010503091c0906082a09060f041e060309030504 70
    0x810360b10b070f0f050f11003002000051500c520042102c0c50910025180301e50502c01040091543e05400651007420007081c00783d4501a030300210400340054214070a190400950745014041403580500710008514000820300b902000030816601c1d107650070403440d044036600c2e5040700e00301e008500c0018000c0c8014001420322041c0e00e0381105603d20b5074030100d12320f407010600d04100f68108800140c030114165080106e8200b00e102e4404505014150080001140c8803440405125001e41c022511510300c0500c03c019601c0104d05400c2404115000e4031000b141e0a4940406011144000740402c00c1760036182c03280314900016002002100c031501c0f1000111840e40001d001510603000d64040608010010b0100f010180c0480d201ca1a40c1442d000002d440c0c044014066a03c0f40720302c00882145006c00c0310f1502e003600d0030010f015241c103c00d00101e200b40c080c0003440900d000e000140803a40403109145902d400300c0c2c00400c0703c501c58655804500b6501c070a8030007004130780140414481d11600c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 55922899 1250 55921649 55921661
    0x9030506071d0301020d06170604050a17071202030c0c040203060306010302060f19020a06051e07180e0109060314030f0306090a090501090b0a051305100f200c070608060f04 76
    0x28403001c0b555148046400203089a200059000805543e1036040100f00c40070080d070380240e001d84001c2c1000e0b140c030392569a161400408010010000840c0100e07030f00403100b0507104010f82100300460003003510b540103956039200000e2100c0700e105441405003581f03030600840384121405800307040c859103140e00b0f025003504811007080d80c0d5401030001402c02c100040f10800c191049030f00808601400b070610380100c98010306202900784101500c1c40403896000c2c0701317a4002403d441c0818007080c0d9540d1700d076080d0081d5040482440125400060b0000d00b0342c000c80c080c3e90240d105040c1e4550300100960b942d03c07400000303085a080034400201c07240f4010070700d96444048502c004c501c40019648007801c441d0031043c111080c0000d134090141c840c4040c03181580c009200055000c0e90071319038803001d554806070440c8236002c540301d0002d02d4600f44143c0000c1102c810400d1001c1c45000c402e55503903659080f035000081c41d88111280065001e11901525008203006024072009911704001e05c005060707 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 55924149 1250 55922899 55922927
    0x608030d020a0c080a03050109150b090f0a090e070e1e0c0a02120403140d030506030c040b0a05090f070e01030b15030a090c15080610051b0a06020d0b01030c0903050607 74
    0x42c142c2c83c04004600b940e40107008508580c1c1e0005099810059000c0868052894080c1c5503108603000f4420009a042100c1090380300f140c02400007600d04000030003154071500110030903400c1490410000400161101c20303a80010802106590b888004c4803003410306100054141c0070314004140090b8800009000b071a0301407040e51280000d450f6804915809540f08440c6a0002c0000c420342550a01105100c3c0c22140f07400d10683c28200b00103559000c4a80f04c0d244030701d60b103826408050340c1d01040340004040150001460345001080b05424240031150000401c580c100c00c0300d403e40c4284075110310030b84020b003030b401c03200c3c410072049600390001410842c480755218801c03004200c40c3e55004d0000d0054454407850301261940041c00d00c20302500090041c00c0384c400782200c0c25000001d85046c01451410407400400b0021180c5c80e0a500f8100078017409d20018a50710580910b4001400f404002e0301c1c01e100c07020b01c40ca002c542c103851500c4098505d810120100f0f0034a0701c101d10320304001c6 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 55925399 1250 55924149 55924157
    0xc0d060e010218040b01080103150f0902030109050105250801030b07051b01020405030f07240909050f010e06010f0c0305030603100216020301060b040b030601050a11100617010608030d020a 83
    0x904044010700326072114150104994007580c0c0d00f0154a02800380c042140b00a203010070155146a0318151a0010712506c01c1d0440e0b150110000805040d0b8818020340e60010000d200d500b2a500303099008160545040b41d0050544403001825030785607503040f00013541a910201140e1850320f520401b164050090400c20a0810410060000c40d01046144070490345c00140d840c1e140c10105481e20203180d104002c150000c2c803040160400b460940360402c042528803104038900ca00040f6070810203600010072041c41d100030f026040398000d003900d042e11101200d24019403101c800640d0304844451240000a61403081000002d100b81c01464004102030120b6000309412043c210680e007081356403010700068101650b055180900541e4020035003a051a0325080c2401e030b42c05407a1100600e668180400041c100110354459131111007000401e10942c2c800208241040740030340014030400883c280800c8415030584010b1048604449101c0000d501d0400105c660b60084e4201c0e02d0344000b88 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 55926649 1250 55925399 55925411
    0x1602010905040905071e0b04090b04020c060703021207030506090a0b3010060302130b060909040f06050a0c090905060d0b0412020f0102090a0603090c09061403061501020c0d06 77
    0x75031501e0140003007441c4540c020b802941e0030164800c0d1096a00741202042c04840348040045012020849007521003178400801c18854540c0802c000c2c1c420b00c06a80c60902c512810810030680c10343c05024518501003400605850b440d008605646094034100e42c40080000031603400340d0142e002d800040c00c0a45168031000306034a843d6800302c1e10580c4003185207080d102e07515940c4000e12211010204404081001c0c50550300404e620030384925107101d1083c2e5401c0203204a40d90a020b0312410107008240702e84900d0320346094140045030540031100365081c9408251130b03420900506200355019603030312030130501e0b120990780505000b52815402080106c2c01c107000c12a00c100d1a48a54090110506003d0700d8010003032820f15850100c08803030344107000405080d6101c03840641141c009203800300d00100c81d0b04240c1d00918040c2c2c409044249040c5000a10000385054000c88940407010303a540d6960b4125184d107072034100010240180c202da005507183d484c2c0340da030b00310909000703034400174007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 55927899 1250 55926649 55926659
    0x80f030a06080d020f0c0d050304050907120203010b07050d0305011802070201090305060a02040f060806010503041218180605010c080306040c05130609180c080106050a030b0306190615020316020109 87
    0x103000303070000c0140040e003143e0f11018170000100700d0b010304094195040400610706480744c40c2c40303004a02501d8481c03525540407580540c440c401c0d00c017612029a0086580356556111141c00c0d9003d204111424050755041108603406445030a040360fa55142c29560001401c440302d0007035000c2e00f0308a0502c03140c5100800402c404020030707841030001c0300b00140d965042110b000321040171940807034100f021650030070070f03642da00106170b903003081c5c1c01a000002c0c1c101481c0252154801ca81c0c5890300c8a04601d00090303400d955159401d030002004504004403600e0f0401183d000c1003a26010701510000c102040050626900045008080b85001c0e030904003600d401e0740b130800b021780c02000003681e1001d05020402c036114418502441240d410401c1011550001c1c164002c14170441052010126828090702d010b41c01c00415040c0040a80d404c030301c1d0100c01000c09180230845088058585000400c464212016522003c5900d030021424201c4020140311b0030000040304034100148042e00189c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 55929149 1250 55927899 55927903
    0xb0904150f09080d0b09010605091e060705060103140c0d020f010c02060c0303010303020c1e040b01090902070507080618030f0702060d050a0e0f0601050120031201150f0507080f030a0608 82
    0x1880900c583c49050359103c40086050a0b900903200c0c0070710800000004008a540140450b110118140c0b400405d01969410000d062000003103a290803480000307144040140c045840c6050b42c3c40740320801c100d01c1c11070103101d9a807003050b2105034110114080340800b40c039048411404401c01403400104032101d650209425400c86100c070425648044010f004154051044072491041602c00407034618080210205843c580010719000303e40e2240c410800380d200e2003840e0040c0c08410000c0d5501c91040c50120307500c0405200f04991030045d40c0c08108120217401c1810a10b6480c00c0045041c007c0710710b030320603060b030000d441264080b03010001e182550300d00d40500c0e40308261995001400c0e4004400c2181000d8800c441300c0e003650400001842243e07000440300b001c21050b000d10f00a2070b0f0910000b9850740c4240c550041500703221100010780900d215480d02c58100c1070380e03100e0309611a42d00003600c0d24096000014001074041c0420b401848080300a5a03221030340714004940e480c5e40302e903528 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 55930399 1250 55929149 55929161
    0x17030d1a10020a05100b18070c02030303130212030a02030328110c0105150604060f021905010b030d02030f0d091a040c05011106010e01030305160b10030c06030b0904150f 75
    0x41c001d0b801c03100207041482028405180346641c90581804403000d01400a00f9003000114180302c81c014000c003050f429489059020401e0b1350280c03c5990300e0405a207844035045a401003240309000d000c0c84960600300c0801562a40042c0e60011400d64440d0b071210910300b05114800401900c1050324049036410354001c84a000c251181a1a40c5a0078080091300351071006241c000803600404c07413110719494002c11101110b01500d40740440310308982e012400c00300b1040c01444010310681c0d8140910030103610017101c01408404903598601002c90582c1c0324011030340c0300780888406001d00c201881e0a40c004502c0540b00308880d505070342003425a4018180199000d4500101d0000e090115580040030071a80c00f5401e0b00070021985407015500a480b01400300074108900420541c0c0482c400008018419a001803c6000381c900744ca0b0180700070a4a1006468550312640c002070150302138441d0100c040070281081d500395840752981a54940013243c2003d60f80c1e500c1c0304040032051244119 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 55931649 1250 55930399 55930429
    0x1b1203181516030f0b01090b090103110708030114090f0406051806040b0109050a09050705240a05120709032310110c010e071815090204030308060a17030d1a 69
    0x1554448015400501311460300c034110007040d00c3c0481e000256a00003100c4011100c80030308040c1e075100c948d00100c010707000c1842c108510401c00321b1910100910640514180c440d09101c54110307001c3d40c020032018100544416000841240c040703404225140c10581e8401c2440c55000420541c203400f86180c2001102d0941303102d40d040c0c00600540d9010f026094001920740400d10411100e80c07036483e00c0740014810349228007581d10318421282184041c940640140403001d42e1a441101d801802a601984041e45a201c18100096445001e0340c01d03581030f00e400c0f0720b0180401d011207042505400d20a0800c1d80c061281c510140b9040d90030303008060b1880300480b0740a44900201111030300f5603099626202c1980c103c08818003000c003001c0040c030b4911140b175001003082c091002212040080540194640c0d900018011091580085049000784019200e607101981e90700040c0414101c0440503940f507400801c5108040c4543d900528031100300b61100300f008000c1000025a15280c0e01720b2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 55932899 1250 55931649 55931671
    0x9050c0d06090201020105070509061b0106030812100f03080d05071202040f061403071e0e040204060309110306060a051002031b1c0302040e04200a09021b12031815 72
    0xa0b200310b580c203000e110342080d00c3d42030032820a42440002101d41c040d150341c0d07140039a0a49002c1d000f80301c0c25001000210b400c50f0340d40b0745d900101da0041100c510101c9a01c0c4401111420000b40e0040e11014982243c2e04030615604004180c91510003400c40540301c401003110706206100c6407800c6200a00080c030040074000380c812700d014005040040d8180c552040c0002c14001c018110360803015100d44140400c1550390040440312003951054554200943c01500c007240200e01e454240e8061003115006030007500e00502c0c11000c1542e121412110030b50402c401039001c002ca800c00c0ca82040022140740107590070203a04d010440001c40680740300714800e500c881c116003452038000480791b1400c0c201d440c05602d001e0404c68141545000500000c1c014441c0108080c4460042c0e000842c00060091510302050758a0303c00304041d402000d140c075000030f40f030348454284640019680d00c854a00d6044141160380c1c9904980034030300300566a11060280c01503000300b0041414000c1c0c031078007190340 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 55934149 1250 55932899 55932911
    0x15150b09040c0302070503030601080405073807020f010813060504210801030b0103030509060408060a15080d0804061d060c070606090902060d0f020d02040b04030b060901061209050c0d06 82
    0x410060701c0b07910240e07209261040042c0c00c04500b02000722680514282440a030546039850020f1501005901080303110303c030500c124040e4098000818411802c0882c03c502044c05818517901c58464110000d40c4200e04281814003940104031095007c085017030100320081c070f00e4a078142905c3e03003202d08648081c0110400d521003165140c00c280b81400303c1c42d00c4400c82d0304550700c0d4142c2d0f07101030101400f4030801044610756030ba02d485c110750141c40392000b42c56050802c0312041004d4003520410006088280c4804180d090000659445080c065521201c90b0346603a140c05004082090151307826045400040341d140c1d10405c082c0b8090103100d030003155503000a040c0881100c00c9508002c0c010ba0030444501c0260b40c81000303442148a0030040064403001d40103181000f0310a4207071382c5807000d0010800260581f4814068000c4900441e400002030b69008100079180509000304404a00601d0851101c0701076a4000a1010711990844000408040014281070040001110650b86030f01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 55935255 1106 55934149 55934167
    0x509040906020c0d080603011e02090406121a1501090302011d1005041d010510051e07080d1d1222060201090506010b0702030a15150b 59
    0x7541156540792440b10191030384000c003620408203454a0018509007018005c10189140c0892117030200801c00c8884402904849400c81c2c225a6442c0c01094100034920300403110742c0030700c2c9200c8a40c49411aa0042000020a00c9204000c0d500b405640c40e41c000038514142c990909000e2400400b40c001081c030580703071b130503a5a0302100c0101c07922140398016008106449850030b006640462806000080c164284075003038102c2d60100007d54030318410800b030002d5401c82d01a50b0004210f0901044441c1c029034401c0e06d055000060000311450b61f4803942d0480076005410401840021800c2034a81506402c3d09000c0200040d06000c4610f40350341d54813680c0d20050881184903254040207001b00314078001122944512000800d072040040c0a07601000d40c000c00174503034954a50f85d0005030864805401d0356a580307401172901a1601701001401030152501c1e45c2c0e480d44029 = true := by decide +kernel

theorem cover : BRFrame.Cov 55755399 55935255 := by
  have h0 := BRFrame.cov_init 55755399
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 55755399 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 55755399 ≤ n) (h2 : n < 55935255) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
